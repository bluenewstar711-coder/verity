#!/usr/bin/env python3
"""Unit tests for the three-stage shim autoresearch harness (`shim_autoresearch.py`)."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import shim_autoresearch as sa


class ShimAutoresearchStageTests(unittest.TestCase):
    """Test Stage 1 boundary refutation, Stage 2 kernel proof gating, and Stage 3 promotion."""

    def setUp(self) -> None:
        self.spec_eval = lambda w, fmp: (w & sa.ADDRESS_MASK, fmp)
        self.baseline = sa.ShimCandidate(
            shim_family="testFamily",
            candidate_id="baseline_cand",
            spec_eval=self.spec_eval,
            cand_eval=self.spec_eval,
            lean_module="Compiler/Autoresearch/ShimArena.lean",
            lean_theorem="scratchKeccak_wins_arena",
            cost=sa.ShimCostProfile(
                static_gas=60,
                mem_words_allocated=2,
                warm_sloads=1,
                warm_sstores=1,
                transient_ops=0,
                bytecode_bytes=40,
            ),
            is_baseline=True,
        )

    def test_stage1_rejects_corrupted_free_memory_pointer_0x40(self) -> None:
        corrupt_fmp = sa.ShimCandidate(
            shim_family="testFamily",
            candidate_id="corrupt_0x40",
            spec_eval=self.spec_eval,
            cand_eval=lambda w, fmp: (w & sa.ADDRESS_MASK, fmp + 0x40),
            lean_module="Compiler/Autoresearch/ShimArena.lean",
            lean_theorem="scratchKeccak_wins_arena",
            cost=sa.ShimCostProfile(30, 0, 0, 0, 0, 16),
        )
        res = sa.run_stage1_fast_check(corrupt_fmp)
        self.assertFalse(res.passed)
        self.assertEqual(res.failure_reason, "corrupted_free_memory_pointer_0x40")

    def test_stage1_rejects_dirty_high_bits(self) -> None:
        dirty_bits = sa.ShimCandidate(
            shim_family="testFamily",
            candidate_id="dirty_high_bits",
            spec_eval=self.spec_eval,
            cand_eval=lambda w, fmp: (w % sa.EVM_WORD_MODULUS, fmp),
            lean_module="Compiler/Autoresearch/ShimArena.lean",
            lean_theorem="scratchKeccak_wins_arena",
            cost=sa.ShimCostProfile(30, 0, 0, 0, 0, 16),
        )
        res = sa.run_stage1_fast_check(dirty_bits)
        self.assertFalse(res.passed)
        self.assertEqual(res.failure_reason, "dirty_high_bits_or_semantic_mismatch")

    def test_stage2_rejects_missing_or_unproved_theorem(self) -> None:
        unproved = sa.ShimCandidate(
            shim_family="testFamily",
            candidate_id="unproved_shim",
            spec_eval=self.spec_eval,
            cand_eval=self.spec_eval,
            lean_module="Compiler/Autoresearch/ShimArena.lean",
            lean_theorem="nonexistent_proof_witness",
            cost=sa.ShimCostProfile(30, 0, 0, 0, 0, 16),
        )
        res = sa.run_stage2_lean_proof_check(unproved)
        self.assertFalse(res.passed)
        self.assertEqual(res.failure_reason, "theorem_not_found_in_module")

    def test_stage2_rejects_module_with_sorry(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp_root = Path(tmpdir)
            mod_rel = "Compiler/Autoresearch/FakeShim.lean"
            mod_path = tmp_root / mod_rel
            mod_path.parent.mkdir(parents=True, exist_ok=True)
            mod_path.write_text(
                "theorem fake_shim_thm : True := by\n  sorry\n",
                encoding="utf-8",
            )
            cand = sa.ShimCandidate(
                shim_family="testFamily",
                candidate_id="sorry_shim",
                spec_eval=self.spec_eval,
                cand_eval=self.spec_eval,
                lean_module=mod_rel,
                lean_theorem="fake_shim_thm",
                cost=sa.ShimCostProfile(30, 0, 0, 0, 0, 16),
            )
            res = sa.run_stage2_lean_proof_check(cand, root=tmp_root)
            self.assertFalse(res.passed)
            self.assertEqual(res.failure_reason, "module_contains_sorry")

    def test_stage3_promotes_pareto_optimal_certified_candidate(self) -> None:
        unsound_s1 = sa.ShimCandidate(
            shim_family="testFamily",
            candidate_id="unsound_s1_cheap",
            spec_eval=self.spec_eval,
            cand_eval=lambda w, fmp: (w, fmp + 32),
            lean_module="Compiler/Autoresearch/ShimArena.lean",
            lean_theorem="scratchKeccak_wins_arena",
            cost=sa.ShimCostProfile(10, 0, 0, 0, 0, 8),
        )
        unproved_s2 = sa.ShimCandidate(
            shim_family="testFamily",
            candidate_id="unproved_s2_cheap",
            spec_eval=self.spec_eval,
            cand_eval=self.spec_eval,
            lean_module="Compiler/Autoresearch/ShimArena.lean",
            lean_theorem="missing_thm",
            cost=sa.ShimCostProfile(12, 0, 0, 0, 0, 10),
        )
        verified_winner = sa.ShimCandidate(
            shim_family="testFamily",
            candidate_id="verified_pareto_winner",
            spec_eval=self.spec_eval,
            cand_eval=self.spec_eval,
            lean_module="Compiler/Autoresearch/ShimArena.lean",
            lean_theorem="scratchKeccak_wins_arena",
            cost=sa.ShimCostProfile(
                static_gas=36,
                mem_words_allocated=0,
                warm_sloads=1,
                warm_sstores=1,
                transient_ops=0,
                bytecode_bytes=22,
            ),
        )
        winner, report, _ = sa.select_arena_winner(
            self.baseline,
            [unsound_s1, unproved_s2, verified_winner],
        )
        self.assertEqual(winner.candidate_id, "verified_pareto_winner")
        self.assertEqual(report.rejected_stage1, ["unsound_s1_cheap"])
        self.assertEqual(report.rejected_stage2, ["unproved_s2_cheap"])
        self.assertGreater(report.gas_saved_per_call, 0)
        self.assertGreater(report.bytecode_bytes_saved, 0)

    def test_cli_check_and_json_mode(self) -> None:
        self.assertEqual(sa.main(["--check"]), 0)
        summary = sa.run_autoresearch_suite()
        self.assertTrue(summary["ok"])
        encoded = json.dumps(summary)
        decoded = json.loads(encoded)
        self.assertEqual(decoded["families_evaluated"], 5)
        self.assertGreater(decoded["total_gas_saved_per_call"], 3000)


if __name__ == "__main__":
    unittest.main()
