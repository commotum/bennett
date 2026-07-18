# 8-CHECKPOINTS

**Status:** In progress.

## Current Facts

- Bennett's segmented-history paragraph is independent of the concrete
  three-tape simulator.  It treats a complete restart dump as one higher-level
  recovery record and reuses the primary history between segments.
- For `v` source steps and `n > 0` segments, the longest balanced segment is
  `v ⌈/⌉ n`; it is not uniformly `v / n` unless divisibility is assumed.
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
  different dump-count convention.  Its doubled-time claim explicitly omits
  dump reads and writes.
- The nested logarithmic-space/quadratic-time sentence proposes no complete
  schedule or invariant and will remain classified as speculative.

## Updated Assumptions

- Model one completed segment as a deterministic partial macro-step on a full
  checkpoint state.  Its internal primary history is assumed to have already
  been computed and erased; the checkpoint layer proves only higher-level dump
  recording and cleanup.
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
- `formal/Bennett/Checkpoint/API.lean`: thin stable re-export.
- `formal/Bennett/Checkpoint/Audit.lean`: executable edge cases, claim
  diagnostics, and principal axiom audits.
- `formal/Bennett.lean`: root re-export only after focused builds are stable.

Focused builds:

```text
cd formal && lake build Bennett.Checkpoint.Core
cd formal && lake build Bennett.Checkpoint.Cost
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

Pending implementation and audit.
