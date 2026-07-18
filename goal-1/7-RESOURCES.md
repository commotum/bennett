# 7-RESOURCES

**Status:** Completed.

## Current Facts

- Stage 6 already proves syntax cardinalities `2f+2N+4` controls,
  `4N+2z+3` rules, and full tape-alphabet sizes `(z,N+1,z)` by counting the
  constructed carriers, not by reading them from the semantic theorem.
- A source run of `v` transitions producing a word of length `λ` has an exact
  target schedule of `2v + (4λ+5) + 2v = 4v+4λ+5` quadruples.
- `ExecutionTrace` counts successful transitions, retains both endpoints, and
  distinguishes visited, ever-nonblank, footprint, peak-nonblank, and
  peak-active positions.
- The canonical physical history trace for `v` records has visited set and
  footprint `Icc (-1) (v-1)`, each of cardinality `v+1`; exactly `Ico 0 v`
  is ever nonblank, and the peak number of nonblank cells is `v`.
- The copy sweep visits the closed interval `Icc (-1) λ` on both work and
  output.  Their copy-phase footprint has cardinality `λ+2`, their
  ever-nonblank set is `Ico 0 λ`, and their peak nonblank/active counts are
  `λ` and `λ+1`.  When `λ=0`, the footprint still has the two delimiter
  cells while the peak counts are `0` and `1`.
- The complete target work-head visited set is the raw source head-visited set
  union `Icc (-1) λ`.  This is not generally a one-cell extension because
  the source need not have scanned every final-output data cell.
- The complete target work ever-nonblank set is exactly the source trace's
  ever-nonblank set.  Its footprint is therefore exactly the source footprint
  union `Icc (-1) λ`; standard endpoints simplify this to insertion of only
  the right delimiter `λ` into the source footprint.
- If `s` means the cardinality of the source footprint, the complete target
  work footprint is exactly `s` when `λ` already belongs to that footprint
  and exactly `s+1` otherwise.  Bennett does not define `s`, so this conditional
  dichotomy replaces the paper's unqualified tape-1 equality.

## Updated Assumptions

- State resource theorems against an explicit source `ExecutionTrace` whenever
  a set of visited work positions is required; endpoint-only `Runs` evidence
  cannot reconstruct intermediate head positions.
- Use the explicit constructor-tag schedule to derive resource traces.  A
  semantic `Runs` theorem alone determines transition count and endpoints, not
  the intermediate resource profile.
- Treat source work usage as a supplied measured trace rather than imposing a
  separate bound convention.  Bennett's scalar `s` statement is interpreted
  only after defining `s` as the source-footprint cardinality and stating
  whether that footprint contains the final right delimiter.
- Count an execution with `k` transitions as `k+1` trace states.  A failed halt
  query is not a transition and adds no trace state.
- Keep permanent output, temporary history, and source work storage separate;
  do not add incompatible metrics into one unnamed “space” number.

## Big Picture Objective

Derive the concrete Table 1 syntax, time, and tape-resource formulas from its
finite carriers and explicit execution schedule, and replace the paper's
ambiguous tape-1 equality with the strongest exact measured result.

## Detailed Implementation Plan

- Package execution of an explicit quadruple schedule as a nonempty
  `ExecutionTrace` and prove its state/transition-count/append laws.
- Prove the copy loop's exact work/output visited set `Icc (-1) λ`, cardinality
  `λ+2`, constant history head, transition count `4λ+5`, and `4λ+6` trace states.
- Prove the forward/reverse history-head path and exact full history visited set
  of cardinality `v+1`; separately prove peak nonblank history `v` and cleanup
  to zero.
- Relate a source execution trace to forward and reverse target work-head paths,
  then compose copy to obtain the exact union of source visited positions with
  `Tape.delimiterTraversal output`.
- Derive output visited/nonblank/permanent-space facts and the corresponding
  empty-output edge case.
- State conditional corollaries explaining precisely when Bennett's work-tape
  number is `s`, when only an `s+1` upper bound follows, and why neither follows
  from an undefined `s` alone.
- Collect the verified syntax/time/space facts in reusable resource proof
  leaves and export them through the simulator API.

## Build Structure

- `formal/Bennett/Turing/Simulator/Resource.lean`: explicit schedule traces,
  exact copy-phase costs, and the canonical physical history geometry.
- `formal/Bennett/Turing/Simulator/WorkResource.lean`: raw source and target
  head paths, explicit full schedules, transition counts, and exact head-visit
  unions.
- `formal/Bennett/Turing/Simulator/WorkSupport.lean`: preservation of work
  support and the exact full-trace footprint and `s`/`s+1` dichotomy.
- `formal/Bennett/Turing/Simulator/Audit.lean`: executable edge cases and
  principal axiom audits without burdening the public proof leaves.
- `formal/Bennett/Turing/Simulator/API.lean`: thin public resource re-export.

## Boundary Checks

- Do not infer a visited set from endpoints or transition count.
- Do not identify visited blanks with nonblank support.
- Do not omit the initial left-delimiter cell or the scanned right delimiter.
- Do not count the final failed halting lookup as a target transition.
- Do not use list length as distinct-cell count without proving the head path
  and converting it to a finite set.
- Do not report tape 1 as exactly `s` until `s` has a formal definition or an
  explicit equality premise.
- Do not fold the permanent output into “temporary workspace.”

## Completion Requirements

- All state/rule/alphabet/time formulas are kernel-checked against constructed
  syntax and schedules.
- Exact copy and history visited-cell formulas include `λ=0` and minimal-run
  edge cases.
- The complete work-tape visited set is stated as an exact union with the source
  trace, with honest conditional `s`/`s+1` corollaries.
- Nonblank, active, permanent, and temporary quantities are either proved
  separately or explicitly recorded as unresolved with a precise obligation.
- Focused/API/root/full builds, proof-hole/shortcut/whitespace scans, and axiom
  audits pass; conventions, traceability, and `C-005` are updated.

## Stage Results

- `Quadruple.executionTrace` packages an explicit rule schedule as a nonempty
  trace with exactly one more state than transitions.  The constructed full
  schedule has `2v` forward, `4λ+5` copy, and `2v` reverse rules, hence exact
  target time `4v+4λ+5` and `4v+4λ+6` trace states.
- `Simulator.Copy.Resource` proves that work and output heads each visit
  `Tape.delimiterTraversal output = Icc (-1) λ`, of cardinality `λ+2`.
  For both tapes the copy trace ever-nonblank set is `Ico 0 λ`, the footprint
  is `Icc (-1) λ`, maximum nonblank cells is `λ`, and maximum active cells
  is `λ+1`.  The history head is stationary and has visited-cardinality one
  during copying.  `copyTrace_empty_data_cost` checks the `λ=0` edge case.
- `Simulator.HistorySpace.concreteTrace_history_cost` proves the canonical
  physical history trace has visited set and footprint `Icc (-1) (v-1)` with
  cardinality `v+1`, ever-nonblank set `Ico 0 v`, and peak nonblank count `v`.
  Geometry lemmas identify these shapes with the actual forward, intermediate,
  copy, and reverse configurations; the history result is not inferred from
  transition count alone.
- `Simulator.Resource.exists_fullRules_scheduled_of_computesIn` extracts the
  chronological intrinsic rule IDs from a standard computation and produces
  an exact full Table 1 schedule using only constructed table rules.
  `fullTrace_work_visitedPositions` proves the target work-head visited set is
  the source head-visited set union `Icc (-1) λ`; the output-head visited set
  is exactly `Icc (-1) λ`.
- `Simulator.Resource.WorkSupport.fullTrace_work_everNonblankPositions` proves
  that the full target creates no new nonblank work position.
  `fullTrace_work_footprintPositions` then gives source footprint union
  `Icc (-1) λ`, and `fullTrace_work_footprintPositions_eq_insert_right`
  simplifies it to insertion of only `λ`.  The two footprint-card theorems
  prove exact `s` versus `s+1` according as that delimiter was already present.
- The paper's `v+1` and `λ+2` are verified as distinct-cell
  visited/footprint counts, not as simultaneous nonblank allocation.  Permanent
  output contains `λ` nonblank cells; peak nonblank history is `v`.
  Whole-run peak-active formulas are intentionally not substituted for these
  metrics: an additional theorem would need to calculate the live
  per-configuration active sets rather than merely their union.
- All exact formulas come from finite syntax or explicit schedules and include
  endpoint blanks.  No space result is inferred from semantic correctness.
  The Stage 7 proof leaves build without proof holes or project axioms; the
  principal audits use only `propext`, `Classical.choice`, and `Quot.sound`.
