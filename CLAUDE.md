# Agent Guide for Verity (`AGENTS.md` / `CLAUDE.md`)

Both `AGENTS.md` and `CLAUDE.md` are authoritative for all coding agents (`claudecode`, `codex`, `opencode`) working on `verity`. Keep them synchronized whenever agent workflows or conventions evolve.

---

## 1. Non-Negotiables & Hard Rules

1. **Zero ProofShortcuts**:
   - **No `sorry`**, **no new project `axiom`s**, and **no `native_decide`** in compiler, importer, or proof modules (enforced by `scripts/check_lean_hygiene.py` and `scripts/check_axioms.py`).
   - No `#eval`, `#check`, or `#print` left in proof files.
   - Proofs must stay **under 30 lines** (over 50 fails `scripts/check_proof_length.py`). Decompose long proofs into small helper lemmas.
2. **Never Weaken Checks or Goldens**:
   - Never weaken a lint, boundary check, golden model (`model.golden`), or mutation test to make CI green.
   - Any change to `model.golden`, `docs/TRUST_ASSUMPTIONS.md`, or `docs/AXIOMS.md` must be justified in the PR description and kept synchronized in the same commit.
3. **100% Construct-Generic Design (Zero Benchmark Coupling)**:
   - Every compiler pass (`Compiler/`), Solidity importer feature (`Compiler/SolidityImport/`), standard library module (`Verity/Stdlib/`), proof (`Compiler/Proofs/`), and smoke/differential fixture (`Contracts/SolidityImportSmoke/`, `scripts/solidity_differential/`) **must be 100% generic and named after the Solidity/EVM language construct**.
   - **Never** hardcode benchmark-specific contract names (`Midnight`, `Market`, `Offer`), library names, or struct/function identifiers (`popFront`, `popBack`, `_begin`, `_end`, `value`, `wExp` domain constants) inside `verity`.
   - External benchmark contracts (such as Morpho Midnight, Uniswap, OpenZeppelin, Pareto) belong **only** in `scripts/solidity_import_corpus/manifest.json` (to prioritize which generic Solidity constructs to implement next) or in their own downstream verification repositories (e.g., `morpho-midnight-verity`).
4. **Required Pre-Merge Gates (Run on the Exact PR Head)**:
   ```bash
   if [ -d /var/lib/sandboxed-node/caches ]; then
     export PATH="/var/lib/sandboxed-node/caches/elan/bin:$PATH"
     export TURBO_LEAN_HOME="/var/lib/sandboxed-node/caches/turbo-lean"
   else
     export TURBO_LEAN_HOME="${TURBO_LEAN_HOME:-$HOME/.cache/turbo-lean}"
   fi
   export LEAN_NUM_THREADS=$(nproc)
   turbo-lean pr-verify --base origin/main --json
   turbo-lean pr-verify --base origin/main --project-dir . --receipt .lake/turbo-receipt.json
   turbo-lean verify-receipt .lake/turbo-receipt.json
   python3 scripts/check_proof_length.py
   make check
   python3 scripts/solidity_import_mutations.py
   # Plus smoke + loss + programs differential campaigns & PrintAxioms check:
   python3 scripts/generate_print_axioms.py --check
   ```
   Never claim completion without passing evidence on the exact commit SHA.

---

## 2. Turbo-Lean Season 5 (`0be49df`) + `lean-native v0.3.0` (`375a5ae`) Productivity Protocol (Mandatory for All Lean Edits)

Because each agent shell tool call runs in a fresh subshell, running `lake build <TargetFile>` or `lake env repl` in an edit loop wastes 2–10 minutes per edit re-loading `.olean` imports and bloats RAM (8–16 GiB RSS per worktree).

**Every Lean agent MUST exclusively use `turbo-lean` and its persistent in-memory Zygote REPL daemon (`TurboLean.ZygoteWorker` + `lean-native-core`), NEVER raw `lake build`, `lake env lean`, or `lake env repl` in edit loops:**

### Rule 1 — Mandatory Shared CAS & Persistent Worker Environment
On `sandboxed-node` hosts, always export `TURBO_LEAN_HOME=/var/lib/sandboxed-node/caches/turbo-lean` and `PATH="/var/lib/sandboxed-node/caches/elan/bin:$PATH"` (falling back to `${TURBO_LEAN_HOME:-$HOME/.cache/turbo-lean}` on standard local machines) in every shell invocation so all agents and worktrees share the two-level `InterfaceCAS` and `TheoremProofCAS`, the `/dev/shm` `cone_env_hash` dependency-cone cache, and the persistent `ZygoteWorker` + `lean-native-core` JSON-RPC worker (`0.07 ms/req`, `13,973 req/s`):
```bash
if [ -d /var/lib/sandboxed-node/caches ]; then
  export PATH="/var/lib/sandboxed-node/caches/elan/bin:$PATH"
  export TURBO_LEAN_HOME="/var/lib/sandboxed-node/caches/turbo-lean"
else
  export TURBO_LEAN_HOME="${TURBO_LEAN_HOME:-$HOME/.cache/turbo-lean}"
fi
```

### Rule 2 — Mandatory Fail-Fast Pre-Proof Gate with `fast-check`
Before spending any time writing tactics for a new auxiliary lemma (`theorem` / `private theorem` over `Uint256`, `BitVec`, offsets, masks, memory/calldata bounds, or state invariants), agents **MUST** first write the lemma statement with `:= by sorry` and run:
```bash
turbo-lean fast-check --transpile-lean Path/To/File.lean --decl <lemma_name>
```
**Why this is mandatory**: Empirical telemetry shows that ~30–40% of LLM proof time is wasted attempting to prove a false helper lemma missing an overflow (`offset + 32 <= 2^256`), alignment, or slot-disjointness precondition. `fast-check` (backed by `lean-native v0.3.0` equality constraint propagation, LLVM 18 SIMD `i256`/`i512`, and NVIDIA PTX 8.0 `sm_90`) falsifies untrue lemmas and produces a certified counterexample (`certifyCounterexample_no_false_positive`) in `0.1 ms - 4 ms`.

### Rule 3 — Incremental Declaration Checking & Interface Hash Preservation
`turbo-lean check` automatically starts/reuses the persistent `TurboLean.ZygoteWorker` REPL daemon on the host (`Shared_Clean` `.olean` memory across workers, `0 ms` re-import overhead), computes the declaration's BLAKE3 dependency cone (`cone_env_hash`), and checks only the target declaration (`~18–45 ms`, or `~4 ms` on warm CAS hit). Use `--disallow-statement-changes --json` during proof decomposition/refactoring so `.olean` interfaces never invalidate downstream dependents:
```bash
# Enforce zero statement drift during proof decomposition/refactoring:
turbo-lean check Path/To/File.lean --decl <theorem_name> --disallow-statement-changes --json

# Check a single theorem or definition interactively:
turbo-lean check Path/To/Target.lean --decl <theorem_name> --project-dir .

# Check all uncached theorem shards in a file in parallel:
turbo-lean check Path/To/Target.lean --parallel-shards --project-dir .
```

### Rule 4 — Pre-PR Verification & In-Kernel Axiom Gate (`< 1 s`)
Before opening or updating a PR, run `turbo-lean pr-verify --base origin/main --json` (which verifies all modified theorem shards against `origin/main` and runs the in-kernel `collectAxioms` gate inside `ZygoteWorker` in `< 1 s`, preventing any macro or transitive `sorryAx` bypass) alongside `python3 scripts/check_proof_length.py`:
```bash
turbo-lean pr-verify --base origin/main --json
turbo-lean pr-verify --base origin/main --project-dir . --receipt .lake/turbo-receipt.json
turbo-lean verify-receipt .lake/turbo-receipt.json
python3 scripts/check_proof_length.py
```

### Step 5 — Rebuild `.olean` interfaces ONLY when module signatures/imports change
When you add or change a public `def`, `structure`, `inductive`, or theorem statement imported by downstream modules, run `turbo-lean build` (which wraps Lake with CAS caching and seeds theorem shards):
```bash
export LEAN_NUM_THREADS=$(nproc)
turbo-lean build --seed-shards --project-dir .
```
Note: `scripts/lean_repl_daemon.py check --file F --decl D` is retained only as a compatibility shim that delegates to `turbo-lean check F --decl D --project-dir .`. Always invoke `turbo-lean` directly.

---

## 3. Agent Speed & Efficiency: What To Do vs. What To Avoid

### DO (Fast & Reliable)
- **Always configure `TURBO_LEAN_HOME` (`/var/lib/sandboxed-node/caches/turbo-lean` on fleet nodes or `${TURBO_LEAN_HOME:-$HOME/.cache/turbo-lean}` locally) and `/var/lib/sandboxed-node/caches/elan/bin` in `PATH`** so all subagents share the warm `InterfaceCAS` and `TheoremProofCAS`.
- **Always run `turbo-lean fast-check --transpile-lean <File.lean> --decl <lemma_name>`** on every new helper lemma (`:= by sorry`) before writing tactics (`0.1 ms - 4 ms` via `lean-native-core`).
- **Always use `turbo-lean check <File.lean> --decl <name> --disallow-statement-changes --json`** during proof refactoring and `--project-dir .` for interactive edits (`~18–45 ms` via the persistent Zygote REPL daemon, `~4 ms` on warm CAS hit).
- **Always use `turbo-lean pr-verify --base origin/main --json` + `python3 scripts/check_proof_length.py`** to validate PR diffs and in-kernel `collectAxioms` before committing/pushing.
- **Reuse local `.lake` build caches on worker nodes**: In a fresh workspace clone, run `scripts/ci_local_persistence.sh restore-lean` or copy/hardlink an existing `/var/lib/sandboxed-node/*/verity/.lake` cache before running `turbo-lean`.
- **Search existing lemmas first** (`git grep`) before proving arithmetic, bitvector, memory, or storage frame properties from scratch.
- **Test single fixtures/mutants during development** (e.g., `python3 scripts/solidity_import_mutations.py --task <name>`) and use `--jobs auto` (or `--shard I/N --jobs auto`) for full campaigns.
- **Check zero Lean warning regressions before pushing**: Prefix intentionally unused proof hypotheses with `_` (e.g. `_aligned`) and verify `python3 scripts/check_lean_warning_regression.py --log lake-build.log`.
- **Keep PRs small and single-purpose**: one Solidity construct family, one proof refactoring slice, or one CI/harness instrument per PR. Stage files explicitly (`git add <paths>`), never `git add -A`.

### AVOID (Slow & Error-Prone Anti-Patterns Observed in Subagents)
- **NEVER run raw `lake build`, `lake env lean`, or `lake env repl` in an edit loop**. Every agent is monitored for rogue `lean`/`lake`/`repl` processes not spawned by `turbo-lean`.
- **NEVER attempt to prove a new arithmetic/word/memory helper lemma without first running `turbo-lean fast-check --transpile-lean`**.
- **NEVER poll background builds with `sleep 60` / `sleep 240` loops**. Debug tactics exclusively with `turbo-lean check <File.lean> --decl <name> --project-dir .`.
- **NEVER run serial unsharded 293-mutant loops or two concurrent full mutation campaigns on the same host** (each mutant rebuilds `Import.lean` using ~2.7 GiB RAM; running two full suites concurrently starves CPU/RAM and hits 600s timeouts).
- **NEVER rely on `cd` persisting across separate `Bash` tool calls** (each tool call resets `cwd` to the workspace root; always pass `--project-dir` / `-C <dir>` or chain `cd <dir> && ...` in the same command).
- **NEVER leave scratch notes or status files** (`PROGRESS.md`, `NOTES.md`, `TODO.md`, `.bak` files) in the git worktree, and never stage borrowed helper scripts (`git add -A`) into unrelated feature PRs.
- **NEVER write monolithic tactic scripts (>30 lines)** or unconstrained `simp` calls over huge definitions; they cause `maxHeartbeats` timeouts and brittle proofs.
- **NEVER drop work silently during rebases/merges**: inspect both sides of every conflict, keep every improvement, and fold duplicate PRs explicitly before closing.

---

## 4. Mathlib4 Code Style & Naming Conventions

All new and refactored Lean code in `Verity/` and `Compiler/` must adhere to **Mathlib4** conventions:

1. **Naming Conventions**:
   - **`UpperCamelCase`** for types, structures, inductive types, typeclasses, and named `Prop` predicates (e.g., `CompilationModel`, `ContractState`, `SupportedStmtList`, `MemoryCoherent`).
   - **`lowerCamelCase`** for functions, definitions returning data/terms, local variables, and parameters (e.g., `evalExpr`, `compileStmt`, `execIRStmt`, `byteMemory`).
   - **`snake_case`** for theorems and lemmas (terms of `Prop`), named descriptively after their conclusion and key hypotheses using standard Mathlib connectors:
     - Connectors: `_of_`, `_iff`, `_eq`, `_ne`, `_lt`, `_le`, `_zero`, `_add`, `_sub`, `_mul`, `_append`, `_mem`, `_get`, `_set`, `_none`, `_some`.
     - Example: `exec_stmt_mstore_eq_of_memory_coherent`, `read_word_write_word_ne`, `decode_uint256_encode_uint256`.
2. **Formatting & Structure**:
   - **Indentation**: 2 spaces; never use tabs.
   - **Line length**: Maximum 100 characters per line.
   - **Declaration headers**: Keep `:= by` on the end of the declaration header line (or after the return type line for multi-line signatures), with the tactic block indented by 2 spaces.
   - **Structured Proof Focusing (`· `)**: Always use middle-dot (`· `) focusing for multi-goal branches (`rcases`, `induction`, `constructor`, `by_cases`), indented consistently. Avoid unstructured multi-goal tactic sequences.
   - **Explicit `have` steps**: State intermediate proof obligations with explicit types (`have hSlot : slot < 2^256 := by ...`) to keep elaboration fast and error messages local.
   - **Docstrings**: Document every public definition, structure, and key theorem with `/-- ... -/`.

---

## 5. Abstractions for Maintainability, Reliability & Proof Performance

When writing or refactoring compiler passes, specifications (`Denote`), and proofs (`Compiler/Proofs/`):

1. **Good Simp Normal Forms & Abstraction Barriers**:
   - Establish small, orthogonal `@[simp]` lemmas for projections, state reads-over-writes, and constructor inversions (`@[simp] theorem get_set_self`, `@[simp] theorem get_set_ne`).
   - Do **not** unfold large recursive evaluators (`evalExpr`, `execStmt`, `lowerCall`) directly with `simp` in downstream proofs. Instead, prove dedicated unfolding/step equations (`exec_stmt_assign`, `exec_stmt_mstore`, `lower_call_static`) and keep implementation internals behind clean API lemmas (or `irreducible` barriers where appropriate).
2. **Compositional State & Frame Lenses**:
   - Express state transitions and invariants via reusable frame/lens predicates (e.g., storage-only updates preserve `memory`, `byteMemory`, `calldata`, `events`, and `sender`; memory-only updates preserve `storage` and `transientStorage`) rather than repeating field-by-field record destruction in every statement proof.
   - `Compiler/Proofs/StateLenses.lean` provides `StorageWordsFrame` (with `refl`/`trans`) plus `@[simp]` projection lenses (`memory_writeUintSlots`, `events_writeAddressFieldSlots`, …) and storage-channel lenses (`transientStorage_writeUintSlots`, `storage_writeTransientTargets`, …) for the source-semantics storage writers; extend it (prove the writer's `StorageWordsFrame` once, derive the lenses) instead of unfolding a writer to read an untouched field.
   - `Compiler/Proofs/Frames.lean` provides `execStmt_*_continue_inv` inversions and `ownedEq_*_of_disjoint` resource lenses; use them instead of `rw [show execStmt … = (match …) from rfl]` + `cases` in statement proofs.
3. **Modular File Decomposition (Avoid Monoliths)**:
   - Split oversized files (`Import.lean`, `Stmt.lean`, `SourceSemantics.lean`, etc.) by construct family or semantic layer with minimal `import` dependencies. Smaller modules reduce `.olean` load times in `turbo-lean`, enable parallel shard verification, and isolate proof maintenance.
4. **Heartbeat Hygiene (Zero `maxHeartbeats` Escalation)**:
   - Never paper over slow elaboration by raising `set_option maxHeartbeats`. If a lemma exceeds default heartbeats:
     1. Replace unconstrained `simp` with `simp only [...]` or `rw [...]`.
     2. Extract complex sub-expressions into `let` / `have` bindings with explicit types.
     3. Split case analyses into standalone helper lemmas (<30 lines each).

---

## 6. Core Commands & Reference Docs

```bash
if [ -d /var/lib/sandboxed-node/caches ]; then
  export PATH="/var/lib/sandboxed-node/caches/elan/bin:$PATH"
  export TURBO_LEAN_HOME="/var/lib/sandboxed-node/caches/turbo-lean"
else
  export TURBO_LEAN_HOME="${TURBO_LEAN_HOME:-$HOME/.cache/turbo-lean}"
fi
export LEAN_NUM_THREADS=$(nproc)
turbo-lean fast-check --transpile-lean F.lean --decl NAME                 # 0.1-4ms SIMD/PTX counterexample gate
turbo-lean check F.lean --decl NAME --disallow-statement-changes --json   # ~18-45ms Zygote REPL check (0 interface drift)
turbo-lean check F.lean --parallel-shards --project-dir .                 # Parallel file shard sweep
turbo-lean pr-verify --base origin/main --json                            # <1s incremental PR + in-kernel collectAxioms gate
python3 scripts/check_proof_length.py                                     # Verify all proofs <= 50 lines
turbo-lean build --seed-shards --project-dir .                            # Full CAS build when interfaces change
make check                                                                # Run local CI-equivalent validation
make test-python                                                          # Run Python unit tests
make test-foundry                                                         # Run Foundry differential tests
```

- Project overview and review order: [README.md](README.md)
- Contribution conventions: [CONTRIBUTING.md](CONTRIBUTING.md)
- Roadmap: [docs/ROADMAP.md](docs/ROADMAP.md)
- Telemetry & `turbo-lean` benchmarks: [docs/TELEMETRY_AND_TURBO_LEAN_BENCHMARKS.md](docs/TELEMETRY_AND_TURBO_LEAN_BENCHMARKS.md)
- Solidity import guide & per-family checklist: [docs/SOLIDITY_IMPORT.md](docs/SOLIDITY_IMPORT.md)
- Trust assumptions & axioms: [docs/TRUST_ASSUMPTIONS.md](docs/TRUST_ASSUMPTIONS.md), [docs/AXIOMS.md](docs/AXIOMS.md)
