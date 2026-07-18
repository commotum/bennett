# 8-CHECKPOINTS

**Status:** Completed.

## Current Facts

- Bennett's segmented-history paragraph is formalized independently of the
  concrete three-tape simulator.  A checkpoint is an arbitrary complete state
  containing every control, tape, head, and phase component needed to restart.
- `recordedSegmentStage` realizes one irreversible segment with a
  `HistoryRecorder`: it loads `⟨checkpoint, []⟩`, runs an exact recorded
  iterate, copies the terminal checkpoint, reverses the iterate, and restores
  the caller's scratch baseline.  It erases every primary-history record it
  generated; the supplied baseline itself need not have empty history.
- `ChainState` retains the permanent original checkpoint, the live current
  checkpoint, a completed-segment index, and newest-first intermediate dumps.
  Its globally inverse `forward`/`backward` steps omit a duplicate first dump
  because the permanent original already determines that predecessor.
- `Plan.segmentSteps` maps declared block lengths to exact source-step
  iterates.  A source run whose length is the sum of those blocks induces a
  complete checkpoint chain and a full compute-copy-cleanup endpoint.
- For `v` source steps and `n > 0` segments, a constructive integer plan bounds
  every segment by `v ⌈/⌉ n`; the bound is not uniformly `v / n` unless
  divisibility is assumed.
- Retaining the permanent original input and final output leaves `n - 1`
  intermediate restart dumps, not `n` temporary dumps.
- If every restart dump occupies `s` cells, the exact discrete temporary-cell
  budget used in this stage is
  `v ⌈/⌉ n + (n - 1) * s`.  It counts the largest reusable primary
  history plus accumulated intermediate dumps; it excludes permanent
  input/output and ordinary live work storage.
- A restart dump must determine every component needed to resume a segment,
  including control, work data, head positions, and any phase tag.  The
  abstract construction therefore stores an entire caller-selected checkpoint
  state rather than pretending that tape contents alone always suffice.
- The paper's `v/n + n*s` and `2*sqrt(v*s)` are continuous relaxations with a
  different dump-count convention.  `paperRoundedCells` is exactly one dump
  of `s` cells above the formal discrete budget when `n > 0`.
- The ideal segmented time is four source-level passes.  `checkpointTime`
  adds the explicit parameterized charge for writing, reading, and erasing
  intermediate dumps; no concrete dump protocol is inferred from semantics.
- `balancedSegments` gives a positive ceiling-square-root choice and a proved
  near-balanced upper bound, not an exact minimizer of the discrete objective.
  The positive-real AM--GM lower bound and equality at the square-root ratio
  are proved separately for the paper's continuous expression.
- The nested logarithmic-space/quadratic-time sentence proposes no complete
  schedule or invariant and will remain classified as speculative.

## Updated Assumptions

- Model one completed segment as a partial macro-step on a full checkpoint
  state.  `recordedSegmentStage_apply_of_run` supplies a checked local
  history-recording realization when a `HistoryRecorder` is available; the
  higher-level checkpoint chain remains reusable for other segment
  implementations.
- Record the input checkpoint of each segment as recovery information and
  validate it when running backward.  The permanent initial checkpoint is
  accounted separately from the `n - 1` temporary intermediate checkpoints.
- Keep semantic reversibility independent of byte/cell size.  Resource theorems
  take a declared dump-cell cost rather than deriving finite storage from an
  arbitrary Lean type.
- Count original source-step executions separately from target-machine
  quadruples.  The ideal high-level cleanup makes four source-level passes;
  restart-dump I/O is an explicit additive parameter.
- Use a constructive bounded integer partition to justify the `v ⌈/⌉ n`
  maximum-segment budget.  Do not infer a realizable segmentation from the
  scalar inequality alone.

## Big Picture Objective

Formalize the sound finite checkpointing principle and a discrete cost model,
then state exactly how they relate to Bennett's continuous and speculative
claims without entangling them with Table 1.

## Detailed Implementation Plan

- Define a full checkpoint state, a restart-dump recorder for an arbitrary
  deterministic partial segment macro-step, and its checked predecessor
  recovery operation.
- Prove single-step and finite-run inverse laws, exact dump-stack growth, and a
  higher-level compute-copy-uncompute theorem that returns to the initial
  checkpoint and erases every intermediate dump while retaining a copied final
  observation.
- Define finite integer segment plans with total length `v`, positive segment
  count, and maximum length at most `v ⌈/⌉ n`; construct such a plan.
- Define primary-history capacity, intermediate-dump count, temporary-cell
  budget, ideal four-pass time, and additive dump-I/O cost.
- Define a positive integer square-root rounding and prove a near-balanced
  bound.  State the continuous `2*sqrt(v*s)` optimization separately if it can
  be proved without conflating it with the discrete construction.
- Add executable small examples covering zero steps, one segment, uneven
  division, invalid forged dumps, and exact reverse cleanup.
- Export only stable checkpoint semantics and costs; keep probes and axiom
  prints in an audit leaf.

## Build Structure

- `formal/Bennett/Checkpoint/Core.lean`: checkpoint/dump state, executable
  partial inverse, finite execution, and cleanup theorem.
- `formal/Bennett/Checkpoint/Cost.lean`: integer segmentation witnesses,
  storage/time definitions, and rounding bounds.
- `formal/Bennett/Checkpoint/Plan.lean`: exact-iterate segment tables and the
  bridge from a source run or `SegmentPlan` to checkpoint completion and
  compute-copy-cleanup.
- `formal/Bennett/Checkpoint/API.lean`: thin stable re-export.
- `formal/Bennett/Checkpoint/Audit.lean`: executable edge cases, claim
  diagnostics, and principal axiom audits.
- `formal/Bennett.lean`: root re-export only after focused builds are stable.

Focused builds:

```text
cd formal && lake build Bennett.Checkpoint.Core
cd formal && lake build Bennett.Checkpoint.Cost
cd formal && lake build Bennett.Checkpoint.Plan
cd formal && lake build Bennett.Checkpoint.Audit Bennett.Checkpoint.API Bennett
```

## Boundary Checks

- Do not identify a partial segment function with a reversible step unless the
  stored checkpoint and backward validation prove a two-sided partial inverse.
- Do not count only tape symbols when control/head/phase data are necessary to
  restart.
- Do not count the permanent original input as an intermediate dump.
- Do not replace `v ⌈/⌉ n` by `v / n` without a divisibility hypothesis.
- Do not report a storage budget as total space; live work and permanent output
  are separate measures.
- Do not hide restart-dump I/O inside an asserted exact doubled-time theorem.
- Do not export a logarithmic-space theorem without an explicit nested
  checkpoint construction and proof.

## Completion Requirements

- The restart-dump transition and its backward transition have checked converse
  graphs, and finite cleanup restores the initial checkpoint and empty
  temporary dump stack.
- The reusable copy/uncompute theorem preserves the final observation while
  erasing higher-level history under explicit blank/copy assumptions.
- A constructed integer segmentation proves its length, total, and
  `v ⌈/⌉ n` per-segment bound for `n > 0`.
- Storage formulas distinguish primary history, intermediate dumps, permanent
  data, and live work; time formulas expose dump I/O.
- The rounded square-root theorem has explicit positivity and integer-rounding
  assumptions, while the continuous paper formula is separately classified.
- Nested checkpointing remains documented as unresolved/speculative unless a
  complete construction is added.
- Focused/API/root builds, forbidden-shortcut and line-length scans,
  `git diff --check`, examples, and principal axiom audits pass.

## Stage Results

- `stage` is a generic load--compute--copy--uncompute--unload `PEquiv`.
  `stage_apply_of_segment` and `stage_symm_cleanup_of_segment` prove exact
  scratch cleanup.  `recordedSegmentStage_apply_of_run` instantiates it with
  `recordedEquivAt`; all primary-history records generated by that segment are
  erased and the caller's complete scratch baseline is restored.
- `forward` and `backward` have converse graphs globally
  (`Checkpoint.areInverses`), including validation of the source checkpoint
  before a dump is removed.  `run_from_initial_shape` proves that after `n`
  successful segments the original is unchanged, `completed = n`, and the
  intermediate dump stack has length exactly `n - 1`.
- `cleanup_of_completes` reverses a full list to `ChainState.initial`.
  `computeCopyCleanup_initial_of_completes` retains the permanent input and a
  copied observation while restoring the complete initial chain state and
  erasing every higher-level dump.  The macro is a global `PEquiv` and uses no
  hidden halt guard.
- `Plan.segmentSteps` maps each block length to `PartialStep.iterate`.
  `exists_completes_segmentSteps_with_dump_count` and
  `exists_completes_segmentPlan_with_dump_count` bridge exact source runs to
  full chains with the proved `n - 1` dump count.
  `computeCopyCleanup_segmentPlan_apply_of_run` supplies the corresponding
  plan-driven retained-input/copied-output endpoint.
- `Cost.SegmentPlan` is a constructive integer partition.  For every positive
  segment count, `exists_segmentPlan` gives exactly that many lengths, total
  `v`, and per-block bound `v ⌈/⌉ n`; `exists_positive_segmentPlan` also
  makes every block nonempty when `n ≤ v`.
- `temporaryCells_eq` verifies the exact declared temporary budget
  `v ⌈/⌉ n + (n - 1) * s`.  For `n > 0`,
  `paperRoundedCells_eq_temporaryCells_add_dumpCells` proves the paper-rounded
  `v ⌈/⌉ n + n*s` convention is exactly one `s`-cell dump higher.
  Permanent input/output, ordinary live state, and physical dump allocation
  remain outside this temporary budget.
- `checkpointTime_eq_two_unsegmented_add_dumpIO` makes the four ideal
  source-level passes and additive dump-I/O charge explicit;
  `checkpointTime_ignoring_dumpIO` recovers exact doubling only when that
  charge is set to zero.
- `temporaryCells_balanced_le` and
  `temporaryCells_balanced_le_two_blocks` prove bounds for the positive
  ceiling-square-root choice `balancedSegments`.  They do not claim it is the
  exact minimizer of the rounded discrete formula.
  `paperContinuousCells_lower_bound` proves the positive-real AM--GM lower
  bound, and `paperContinuousCells_at_sqrt_ratio` proves equality at the
  positive square-root ratio.
- No nested checkpoint schedule, logarithmic-space theorem, or quadratic-time
  theorem is exported.  The paper gives no invariant or complete construction
  for that sentence.  Concrete dump placement and target-level dump-I/O remain
  caller-supplied rather than consequences of the abstract semantics.
- The focused `Checkpoint.Core`, `Checkpoint.Cost`, `Checkpoint.Plan`, and
  `Checkpoint.Audit` builds pass; `Checkpoint.API` and the root `Bennett` build
  also pass.  Audit examples cover uneven plans, the `n` versus `n-1` dump
  distinction, explicit dump I/O, forged-dump rejection, local recorded
  cleanup, full-chain cleanup, and the Plan bridges.  Principal declarations
  use only the standard `propext`, `Classical.choice`, and `Quot.sound` subset
  appropriate to their proofs; there are no proof holes or project-specific
  axioms.  The final whole-project release audit remains Stage 9 work.
