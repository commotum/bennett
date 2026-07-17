# 7-RESOURCES

**Status:** In progress.

## Current Facts

- Stage 6 already proves syntax cardinalities `2f+2N+4` controls,
  `4N+2z+3` rules, and full tape-alphabet sizes `(z,N+1,z)` by counting the
  constructed carriers, not by reading them from the semantic theorem.
- A source run of `v` transitions producing a word of length `λ` has an exact
  target schedule of `2v + (4λ+5) + 2v = 4v+4λ+5` quadruples.
- `ExecutionTrace` counts successful transitions, retains both endpoints, and
  distinguishes visited, ever-nonblank, footprint, peak-nonblank, and
  peak-active positions.
- The physical history encoding of a `v`-record stack occupies nonblank cells
  `0,…,v-1`, has head `v-1`, and starts/finishes blank at head `-1`.
- The copy sweep visits the closed interval `[-1,λ]` on both work and output,
  including two distinct delimiter cells even when `λ=0`.
- Bennett never defines tape 1's `s`.  The construction's exact visited set is
  expected to be the source-run work-head set union `[-1,λ]`; it equals a bare
  source parameter `s` only when that parameter already includes the complete
  final-output delimiter traversal.

## Updated Assumptions

- State resource theorems against an explicit source `ExecutionTrace` whenever
  a set of visited work positions is required; endpoint-only `Runs` evidence
  cannot reconstruct intermediate head positions.
- Use the explicit constructor-tag schedule to derive resource traces.  A
  semantic `Runs` theorem alone determines transition count and endpoints, not
  the intermediate resource profile.
- Treat source work usage as a supplied measured trace rather than imposing a
  separate bound convention.  Derive Bennett's `s` statement only as a
  corollary under the exact inclusion/equality premise it needs.
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
- Collect the verified syntax/time/space facts in a reusable resource
  certificate and export it through the simulator API.

## No-Cheating Checks

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

Pending focused integration and audit.
