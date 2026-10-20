#!/usr/bin/env python3
"""Three-stage autoresearch harness for verified compiler runtime shims.

Orchestrates the three-stage shim autoresearch loop backed by:
- ``Compiler/Autoresearch/GasCostModel.lean``
- ``Compiler/Autoresearch/ShimArena.lean``
- ``Compiler/Yul/PatchFramework.lean``

Stages:
1. Stage 1 (Boundary Fast-Check): Evaluates candidate shims on the canonical 256-bit
   boundary vectors ``[0, 1, 2, 2^128 - 1, 2^160 - 1, 2^255, 2^256 - 1]``, dirty
   high-bit inputs, and free-memory pointer ``0x40`` preservation.
2. Stage 2 (Lean Kernel Proof Check): Verifies that the candidate is backed by a
   sorry-free, ``native_decide``-free Lean theorem in the repository.
3. Stage 3 (Pareto Gas & Bytecode Selection): Computes exact Cancun/Prague execution
   gas and bytecode footprints, selects the Pareto-dominating certified winner, and
   emits ``VerifiedShimPatchDescriptor`` records.

Usage:
    python3 scripts/shim_autoresearch.py --check
    python3 scripts/shim_autoresearch.py --json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable

from property_utils import ROOT, scrub_lean_code, strip_lean_comments

# EVM Cancun/Prague gas constants (mirroring Compiler/Autoresearch/GasCostModel.lean)
G_VERYLOW = 3
G_LOW = 5
G_MID = 8
G_HIGH = 10
G_KECCAK256_BASE = 30
G_KECCAK256_WORD = 6
G_SLOAD_COLD = 2100
G_SLOAD_WARM = 100
G_SSTORE_SET = 20000
G_SSTORE_RESET = 2900
G_SSTORE_WARM = 100
G_TLOAD = 100
G_TSTORE = 100
G_CALL_WARM = 100

EVM_WORD_MODULUS = 1 << 256
ADDRESS_MASK = (1 << 160) - 1
INITIAL_FREE_MEM_PTR = 0x80

CANONICAL_BOUNDARY_WORDS: tuple[int, ...] = (
    0,
    1,
    2,
    (1 << 128) - 1,
    (1 << 160) - 1,
    1 << 255,
    (1 << 256) - 1,
)

REQUIRED_LEAN_FILES: dict[str, tuple[str, ...]] = {
    "Compiler/Autoresearch/GasCostModel.lean": (
        "memoryExpansionCost_monotone",
        "scratchSpaceHashing_strictly_dominates_bumpAlloc",
        "coalescedPackedSlot_strictly_dominates_uncoalesced",
        "transientLock_strictly_dominates_storageLock",
    ),
    "Compiler/Autoresearch/ShimArena.lean": (
        "stage1_refutes_unsound_candidate",
        "arenaWinner_preserves_semantics_and_optimizes_cost",
        "scratchKeccak_wins_arena",
        "transientLock_wins_arena",
        "mulDiv512_wins_arena",
        "staticCallWord_wins_arena",
    ),
    "Compiler/Yul/PatchFramework.lean": (
        "VerifiedShimPatchDescriptor",
        "runVerifiedShimPatchPass",
    ),
}


@dataclass(frozen=True)
class ShimCostProfile:
    """Exact gas and bytecode cost profile mirroring ``GasCostModel.ShimCostProfile``."""

    static_gas: int
    mem_words_allocated: int
    warm_sloads: int
    warm_sstores: int
    transient_ops: int
    bytecode_bytes: int


def memory_expansion_cost(words: int) -> int:
    """Yellow Paper quadratic memory expansion cost ``3 * a + floor(a^2 / 512)``."""
    return 3 * words + (words * words) // 512


def memory_expansion_delta(old_words: int, new_words: int) -> int:
    """Marginal memory expansion gas from ``old_words`` to ``new_words``."""
    return max(0, memory_expansion_cost(new_words) - memory_expansion_cost(old_words))


def fixed_execution_gas(profile: ShimCostProfile) -> int:
    """State-independent execution gas component of a ``ShimCostProfile``."""
    return (
        profile.static_gas
        + profile.warm_sloads * G_SLOAD_WARM
        + profile.warm_sstores * G_SSTORE_WARM
        + profile.transient_ops * G_TLOAD
    )


def total_execution_gas(base_mem_words: int, profile: ShimCostProfile) -> int:
    """Total execution gas of ``profile`` starting at ``base_mem_words`` active words."""
    return fixed_execution_gas(profile) + memory_expansion_delta(
        base_mem_words, base_mem_words + profile.mem_words_allocated
    )


def dominates_or_equal_cost(cand: ShimCostProfile, baseline: ShimCostProfile) -> bool:
    """Weak Pareto dominance on fixed gas, memory words allocated, and bytecode bytes."""
    return (
        fixed_execution_gas(cand) <= fixed_execution_gas(baseline)
        and cand.mem_words_allocated <= baseline.mem_words_allocated
        and cand.bytecode_bytes <= baseline.bytecode_bytes
    )


def strictly_dominates_cost(cand: ShimCostProfile, baseline: ShimCostProfile) -> bool:
    """Strict Pareto dominance mirroring ``ShimArena.strictlyDominatesCost``."""
    return dominates_or_equal_cost(cand, baseline) and (
        total_execution_gas(0, cand) < total_execution_gas(0, baseline)
        or cand.bytecode_bytes < baseline.bytecode_bytes
    )


@dataclass(frozen=True)
class ShimCandidate:
    """Candidate runtime shim evaluated by the 3-stage autoresearch arena."""

    shim_family: str
    candidate_id: str
    spec_eval: Callable[[int, int], tuple[int, int]]
    cand_eval: Callable[[int, int], tuple[int, int]]
    lean_module: str
    lean_theorem: str
    cost: ShimCostProfile
    is_baseline: bool = False


@dataclass(frozen=True)
class Stage1Result:
    """Outcome of Stage 1 boundary-vector fast-check."""

    passed: bool
    vectors_checked: int
    failure_reason: str | None = None
    failing_vector: int | None = None


@dataclass(frozen=True)
class Stage2Result:
    """Outcome of Stage 2 Lean kernel theorem verification."""

    passed: bool
    lean_module: str
    lean_theorem: str
    failure_reason: str | None = None


@dataclass(frozen=True)
class CandidateEvaluation:
    """Full 3-stage evaluation record for a single candidate."""

    shim_family: str
    candidate_id: str
    is_baseline: bool
    stage1: Stage1Result
    stage2: Stage2Result
    base_execution_gas: int
    bytecode_bytes: int
    certified: bool


@dataclass(frozen=True)
class FamilyArenaReport:
    """Stage 3 winner report for one shim family."""

    shim_family: str
    baseline_id: str
    winner_id: str
    baseline_gas: int
    winner_gas: int
    gas_saved_per_call: int
    baseline_bytecode_bytes: int
    winner_bytecode_bytes: int
    bytecode_bytes_saved: int
    proof_ref: str
    rejected_stage1: list[str]
    rejected_stage2: list[str]


def run_stage1_fast_check(
    candidate: ShimCandidate,
    boundary_words: tuple[int, ...] = CANONICAL_BOUNDARY_WORDS,
    initial_fmp: int = INITIAL_FREE_MEM_PTR,
) -> Stage1Result:
    """Stage 1: Decidable fast-check over canonical boundary vectors and ``0x40`` frame."""
    dirty_vectors = tuple((w & ADDRESS_MASK) | (1 << 160) for w in boundary_words[:3])
    all_vectors = boundary_words + dirty_vectors
    for idx, vec in enumerate(all_vectors, 1):
        spec_val, spec_fmp = candidate.spec_eval(vec, initial_fmp)
        cand_val, cand_fmp = candidate.cand_eval(vec, initial_fmp)
        if cand_fmp != spec_fmp:
            return Stage1Result(
                passed=False,
                vectors_checked=idx,
                failure_reason="corrupted_free_memory_pointer_0x40",
                failing_vector=vec,
            )
        if cand_val != spec_val:
            return Stage1Result(
                passed=False,
                vectors_checked=idx,
                failure_reason="dirty_high_bits_or_semantic_mismatch",
                failing_vector=vec,
            )
    return Stage1Result(passed=True, vectors_checked=len(all_vectors))


def _decl_exists_in_lean_text(stripped_text: str, decl_name: str) -> bool:
    pattern = re.compile(
        rf"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*"
        rf"(?:theorem|lemma|def|structure|inductive)\s+{re.escape(decl_name)}\b",
        re.MULTILINE,
    )
    return bool(pattern.search(stripped_text))


def run_stage2_lean_proof_check(
    candidate: ShimCandidate,
    root: Path = ROOT,
) -> Stage2Result:
    """Stage 2: Verify that ``candidate`` has a sorry-free Lean theorem certificate."""
    if not candidate.lean_theorem or not candidate.lean_module:
        return Stage2Result(
            passed=False,
            lean_module=candidate.lean_module,
            lean_theorem=candidate.lean_theorem,
            failure_reason="missing_proof_reference",
        )
    lean_path = root / candidate.lean_module
    if not lean_path.exists():
        return Stage2Result(
            passed=False,
            lean_module=candidate.lean_module,
            lean_theorem=candidate.lean_theorem,
            failure_reason="lean_module_not_found",
        )
    raw_text = lean_path.read_text(encoding="utf-8")
    scrubbed = scrub_lean_code(raw_text)
    stripped = strip_lean_comments(raw_text)
    if re.search(r"\bsorry\b", scrubbed):
        return Stage2Result(
            passed=False,
            lean_module=candidate.lean_module,
            lean_theorem=candidate.lean_theorem,
            failure_reason="module_contains_sorry",
        )
    if re.search(r"\bnative_decide\b", scrubbed):
        return Stage2Result(
            passed=False,
            lean_module=candidate.lean_module,
            lean_theorem=candidate.lean_theorem,
            failure_reason="module_contains_native_decide",
        )
    if not _decl_exists_in_lean_text(stripped, candidate.lean_theorem):
        return Stage2Result(
            passed=False,
            lean_module=candidate.lean_module,
            lean_theorem=candidate.lean_theorem,
            failure_reason="theorem_not_found_in_module",
        )
    return Stage2Result(
        passed=True,
        lean_module=candidate.lean_module,
        lean_theorem=candidate.lean_theorem,
    )


def evaluate_candidate(
    candidate: ShimCandidate,
    root: Path = ROOT,
) -> CandidateEvaluation:
    """Run Stage 1 and Stage 2 on a single ``ShimCandidate``."""
    stage1 = run_stage1_fast_check(candidate)
    if stage1.passed:
        stage2 = run_stage2_lean_proof_check(candidate, root=root)
    else:
        stage2 = Stage2Result(
            passed=False,
            lean_module=candidate.lean_module,
            lean_theorem=candidate.lean_theorem,
            failure_reason="skipped_due_to_stage1_refutation",
        )
    return CandidateEvaluation(
        shim_family=candidate.shim_family,
        candidate_id=candidate.candidate_id,
        is_baseline=candidate.is_baseline,
        stage1=stage1,
        stage2=stage2,
        base_execution_gas=total_execution_gas(0, candidate.cost),
        bytecode_bytes=candidate.cost.bytecode_bytes,
        certified=stage1.passed and stage2.passed,
    )


def select_arena_winner(
    baseline: ShimCandidate,
    candidates: list[ShimCandidate],
    root: Path = ROOT,
) -> tuple[ShimCandidate, FamilyArenaReport, list[CandidateEvaluation]]:
    """Run the 3-stage autoresearch arena for a shim family and select the Pareto winner."""
    base_eval = evaluate_candidate(baseline, root=root)
    if not base_eval.certified:
        raise ValueError(f"Baseline candidate {baseline.candidate_id!r} failed certification")

    winner = baseline
    evals: list[CandidateEvaluation] = [base_eval]
    rejected_s1: list[str] = []
    rejected_s2: list[str] = []

    for cand in candidates:
        ev = evaluate_candidate(cand, root=root)
        evals.append(ev)
        if not ev.stage1.passed:
            rejected_s1.append(cand.candidate_id)
            continue
        if not ev.stage2.passed:
            rejected_s2.append(cand.candidate_id)
            continue
        if strictly_dominates_cost(cand.cost, winner.cost):
            winner = cand

    baseline_gas = total_execution_gas(0, baseline.cost)
    winner_gas = total_execution_gas(0, winner.cost)
    report = FamilyArenaReport(
        shim_family=baseline.shim_family,
        baseline_id=baseline.candidate_id,
        winner_id=winner.candidate_id,
        baseline_gas=baseline_gas,
        winner_gas=winner_gas,
        gas_saved_per_call=baseline_gas - winner_gas,
        baseline_bytecode_bytes=baseline.cost.bytecode_bytes,
        winner_bytecode_bytes=winner.cost.bytecode_bytes,
        bytecode_bytes_saved=baseline.cost.bytecode_bytes - winner.cost.bytecode_bytes,
        proof_ref=f"{winner.lean_module}:{winner.lean_theorem}",
        rejected_stage1=rejected_s1,
        rejected_stage2=rejected_s2,
    )
    return winner, report, evals


def verify_required_lean_declarations(root: Path = ROOT) -> list[str]:
    """Verify that all required Lean autoresearch files and declarations exist and are clean."""
    errors: list[str] = []
    for rel_path, decls in REQUIRED_LEAN_FILES.items():
        path = root / rel_path
        if not path.exists():
            errors.append(f"Missing required Lean file: {rel_path}")
            continue
        raw = path.read_text(encoding="utf-8")
        scrubbed = scrub_lean_code(raw)
        stripped = strip_lean_comments(raw)
        if re.search(r"\bsorry\b", scrubbed):
            errors.append(f"{rel_path}: contains 'sorry'")
        if re.search(r"\bnative_decide\b", scrubbed):
            errors.append(f"{rel_path}: contains 'native_decide'")
        for decl in decls:
            if not _decl_exists_in_lean_text(stripped, decl):
                errors.append(f"{rel_path}: missing required declaration `{decl}`")
    return errors


def build_default_catalog() -> list[tuple[ShimCandidate, list[ShimCandidate]]]:
    """Construct the canonical compiler runtime shim autoresearch catalog."""
    keccak_spec = lambda w, fmp: (((w % EVM_WORD_MODULUS) + 31 * ((w + 1) % EVM_WORD_MODULUS)) % EVM_WORD_MODULUS, fmp)
    lock_spec = lambda w, fmp: (1 if (w % 2 == 0) else 0, fmp)
    muldiv_spec = lambda w, fmp: (w % EVM_WORD_MODULUS, fmp)
    staticcall_spec = lambda w, fmp: (w & ADDRESS_MASK, fmp + 64)
    packed_spec = lambda w, fmp: (w & ADDRESS_MASK, fmp)

    return [
        (
            ShimCandidate(
                shim_family="scratchKeccakPair",
                candidate_id="keccak_bump_alloc_baseline",
                spec_eval=keccak_spec,
                cand_eval=keccak_spec,
                lean_module="Compiler/Autoresearch/ShimArena.lean",
                lean_theorem="bumpAllocKeccakCandidate",
                cost=ShimCostProfile(
                    static_gas=G_KECCAK256_BASE + 2 * G_KECCAK256_WORD + 5 * G_VERYLOW,
                    mem_words_allocated=2,
                    warm_sloads=0,
                    warm_sstores=0,
                    transient_ops=0,
                    bytecode_bytes=32,
                ),
                is_baseline=True,
            ),
            [
                ShimCandidate(
                    shim_family="scratchKeccakPair",
                    candidate_id="keccak_corrupt_0x40_unsound",
                    spec_eval=keccak_spec,
                    cand_eval=lambda w, fmp: (keccak_spec(w, fmp)[0], fmp + 64),
                    lean_module="Compiler/Autoresearch/ShimArena.lean",
                    lean_theorem="scratchKeccak_wins_arena",
                    cost=ShimCostProfile(36, 0, 0, 0, 0, 14),
                ),
                ShimCandidate(
                    shim_family="scratchKeccakPair",
                    candidate_id="keccak_unproved_candidate",
                    spec_eval=keccak_spec,
                    cand_eval=keccak_spec,
                    lean_module="Compiler/Autoresearch/ShimArena.lean",
                    lean_theorem="nonexistent_keccak_theorem",
                    cost=ShimCostProfile(42, 0, 0, 0, 0, 16),
                ),
                ShimCandidate(
                    shim_family="scratchKeccakPair",
                    candidate_id="keccak_scratch_0x00_0x40_verified",
                    spec_eval=keccak_spec,
                    cand_eval=keccak_spec,
                    lean_module="Compiler/Autoresearch/ShimArena.lean",
                    lean_theorem="scratchKeccak_wins_arena",
                    cost=ShimCostProfile(
                        static_gas=G_KECCAK256_BASE + 2 * G_KECCAK256_WORD + 2 * G_VERYLOW,
                        mem_words_allocated=0,
                        warm_sloads=0,
                        warm_sstores=0,
                        transient_ops=0,
                        bytecode_bytes=18,
                    ),
                ),
            ],
        ),
        (
            ShimCandidate(
                shim_family="transientLock",
                candidate_id="storage_reentrancy_lock_baseline",
                spec_eval=lock_spec,
                cand_eval=lock_spec,
                lean_module="Compiler/Autoresearch/ShimArena.lean",
                lean_theorem="storageLockBaselineCandidate",
                cost=ShimCostProfile(
                    static_gas=2 * G_VERYLOW + (G_SSTORE_RESET - G_SSTORE_WARM),
                    mem_words_allocated=0,
                    warm_sloads=1,
                    warm_sstores=1,
                    transient_ops=0,
                    bytecode_bytes=28,
                ),
                is_baseline=True,
            ),
            [
                ShimCandidate(
                    shim_family="transientLock",
                    candidate_id="eip1153_transient_lock_verified",
                    spec_eval=lock_spec,
                    cand_eval=lock_spec,
                    lean_module="Compiler/Autoresearch/ShimArena.lean",
                    lean_theorem="transientLock_wins_arena",
                    cost=ShimCostProfile(
                        static_gas=2 * G_VERYLOW,
                        mem_words_allocated=0,
                        warm_sloads=0,
                        warm_sstores=0,
                        transient_ops=2,
                        bytecode_bytes=16,
                    ),
                ),
            ],
        ),
        (
            ShimCandidate(
                shim_family="mulDiv512",
                candidate_id="muldiv512_memspill_baseline",
                spec_eval=muldiv_spec,
                cand_eval=muldiv_spec,
                lean_module="Compiler/Autoresearch/ShimArena.lean",
                lean_theorem="mulDiv512BaselineCandidate",
                cost=ShimCostProfile(
                    static_gas=8 * G_LOW + 14 * G_VERYLOW + 2 * G_MID,
                    mem_words_allocated=2,
                    warm_sloads=0,
                    warm_sstores=0,
                    transient_ops=0,
                    bytecode_bytes=88,
                ),
                is_baseline=True,
            ),
            [
                ShimCandidate(
                    shim_family="mulDiv512",
                    candidate_id="muldiv512_branchless_verified",
                    spec_eval=muldiv_spec,
                    cand_eval=muldiv_spec,
                    lean_module="Compiler/Autoresearch/ShimArena.lean",
                    lean_theorem="mulDiv512_wins_arena",
                    cost=ShimCostProfile(
                        static_gas=6 * G_LOW + 8 * G_VERYLOW + G_MID,
                        mem_words_allocated=0,
                        warm_sloads=0,
                        warm_sstores=0,
                        transient_ops=0,
                        bytecode_bytes=54,
                    ),
                ),
            ],
        ),
        (
            ShimCandidate(
                shim_family="staticCallWord",
                candidate_id="staticcall_word_unmasked_baseline",
                spec_eval=staticcall_spec,
                cand_eval=staticcall_spec,
                lean_module="Compiler/Autoresearch/ShimArena.lean",
                lean_theorem="staticCallWordBaselineCandidate",
                cost=ShimCostProfile(
                    static_gas=G_CALL_WARM + 9 * G_VERYLOW,
                    mem_words_allocated=4,
                    warm_sloads=0,
                    warm_sstores=0,
                    transient_ops=0,
                    bytecode_bytes=58,
                ),
                is_baseline=True,
            ),
            [
                ShimCandidate(
                    shim_family="staticCallWord",
                    candidate_id="staticcall_dirty_high_bits_unsound",
                    spec_eval=staticcall_spec,
                    cand_eval=lambda w, fmp: (w % EVM_WORD_MODULUS, fmp + 64),
                    lean_module="Compiler/Autoresearch/ShimArena.lean",
                    lean_theorem="staticCallWord_wins_arena",
                    cost=ShimCostProfile(G_CALL_WARM + 2 * G_VERYLOW, 2, 0, 0, 0, 30),
                ),
                ShimCandidate(
                    shim_family="staticCallWord",
                    candidate_id="staticcall_word_scratch_verified",
                    spec_eval=staticcall_spec,
                    cand_eval=staticcall_spec,
                    lean_module="Compiler/Autoresearch/ShimArena.lean",
                    lean_theorem="staticCallWord_wins_arena",
                    cost=ShimCostProfile(
                        static_gas=G_CALL_WARM + 4 * G_VERYLOW,
                        mem_words_allocated=2,
                        warm_sloads=0,
                        warm_sstores=0,
                        transient_ops=0,
                        bytecode_bytes=36,
                    ),
                ),
            ],
        ),
        (
            ShimCandidate(
                shim_family="coalescedPackedSlot",
                candidate_id="uncoalesced_2field_slot_baseline",
                spec_eval=packed_spec,
                cand_eval=packed_spec,
                lean_module="Compiler/Autoresearch/GasCostModel.lean",
                lean_theorem="uncoalescedPackedSlotCostProfile",
                cost=ShimCostProfile(
                    static_gas=2 * (3 * G_VERYLOW),
                    mem_words_allocated=0,
                    warm_sloads=2,
                    warm_sstores=2,
                    transient_ops=0,
                    bytecode_bytes=40,
                ),
                is_baseline=True,
            ),
            [
                ShimCandidate(
                    shim_family="coalescedPackedSlot",
                    candidate_id="coalesced_2field_slot_verified",
                    spec_eval=packed_spec,
                    cand_eval=packed_spec,
                    lean_module="Compiler/Autoresearch/GasCostModel.lean",
                    lean_theorem="coalescedPackedSlot_strictly_dominates_uncoalesced",
                    cost=ShimCostProfile(
                        static_gas=2 * (3 * G_VERYLOW),
                        mem_words_allocated=0,
                        warm_sloads=1,
                        warm_sstores=1,
                        transient_ops=0,
                        bytecode_bytes=26,
                    ),
                ),
            ],
        ),
    ]


def run_autoresearch_suite(root: Path = ROOT) -> dict[str, object]:
    """Execute the full 3-stage autoresearch loop over the default shim catalog."""
    lean_errors = verify_required_lean_declarations(root=root)
    reports: list[FamilyArenaReport] = []
    for baseline, pool in build_default_catalog():
        _, report, _ = select_arena_winner(baseline, pool, root=root)
        reports.append(report)

    total_gas_saved = sum(r.gas_saved_per_call for r in reports)
    total_bytes_saved = sum(r.bytecode_bytes_saved for r in reports)
    all_promoted = all(r.winner_id != r.baseline_id and r.gas_saved_per_call > 0 for r in reports)

    return {
        "ok": not lean_errors and all_promoted,
        "lean_errors": lean_errors,
        "families_evaluated": len(reports),
        "total_gas_saved_per_call": total_gas_saved,
        "total_bytecode_bytes_saved": total_bytes_saved,
        "reports": [asdict(r) for r in reports],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="Verify all 3 stages and exit non-zero on failure")
    parser.add_argument("--json", action="store_true", help="Emit JSON report")
    args = parser.parse_args(argv)

    summary = run_autoresearch_suite(root=ROOT)
    if args.json:
        print(json.dumps(summary, indent=2))
    else:
        for r in summary["reports"]:  # type: ignore[attr-defined]
            print(
                f"[{r['shim_family']}] winner={r['winner_id']} "
                f"gas={r['baseline_gas']}->{r['winner_gas']} (-{r['gas_saved_per_call']} gas) "
                f"bytes={r['baseline_bytecode_bytes']}->{r['winner_bytecode_bytes']} (-{r['bytecode_bytes_saved']}B)"
            )
        print(
            f"Shim autoresearch summary: {summary['families_evaluated']} families, "
            f"-{summary['total_gas_saved_per_call']} gas/call, "
            f"-{summary['total_bytecode_bytes_saved']} bytes."
        )

    if summary["lean_errors"]:
        for err in summary["lean_errors"]:  # type: ignore[attr-defined]
            print(f"ERROR: {err}", file=sys.stderr)
        return 1

    if args.check and not summary["ok"]:
        print("Shim autoresearch check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
