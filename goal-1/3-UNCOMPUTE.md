# 3-UNCOMPUTE

**Status:** Completed on 2026-07-17.

## Current Facts

- Stage 2 provides executable `PartialStep`, exact finite runs, two-way
  termination correspondence, and `HistoryRecorder` lifted as a mathlib
  `PEquiv` with exact cleanup.
- Mathlib `PEquiv.trans` composes partial bijections sequentially and is the
  appropriate semantic macro layer.  It does not by itself prove that the union
  of three concrete machine rule families has disjoint domains/ranges.
- The paper's copy stage retains its source and only writes a known blank target;
  its reverse accepts an equal source/target pair and restores the target blank.
- A useful output observer can be any function from a terminal work state to
  classical output data; copying arbitrary machine configurations is unnecessary.

## Updated Assumptions

- A generic blank-target copy over data `β` requires a distinguished `blank : β`
  and executable equality.  Its forward domain is exactly `(value, blank)` and
  inverse domain exactly `(value, value)`.
- An observed-copy lift retains an arbitrary work state `w` and copies only
  `observe w`; this is injective because `w` remains present.
- The reusable compute-copy-uncompute macro for an exact count `n` is the
  sequential `PEquiv` composition: recorded forward iteration, terminal-state
  guard, observed blank-target copy, then recorded backward iteration.
- A dynamic concrete machine will discover halting operationally in Stage 6.
  At this abstract stage, quantify over exact `n` and prove existence over `n`
  equivalent to source termination; do not count the macro as one target step.

## Big Picture Objective

Formalize reversible copying and compute-copy-uncompute independently of Turing
syntax, proving exact input/output/history behavior and the necessary blank and
halting preconditions.

## Detailed Implementation Plan

- Define blank-target copy/uncopy as a mathlib `PEquiv`, with exact forward and
  inverse domain/pre/postcondition theorems.
- Lift observed copying to retain arbitrary work state while copying only its
  classical output observation.
- Prove unrestricted destructive overwrite is noninjective and cannot have a
  partial inverse when the target type has two distinct values.
- Define generic lifts of partial equivalences through an untouched product
  register and an executable terminal-state guard.
- Compose `n` recorded forward steps, the halt guard, observed copy, and `n`
  recorded backward steps as a reusable `computeCopyUncompute` partial
  equivalence.
- Prove success from `(before, initialHistory, blank)` iff the source halts after
  exactly `n` steps; prove the exact final state retains `before`, restores the
  identical initial history, and contains `observe terminal`.
- Prove existence of a successful macro over some `n` iff source termination.
- Add an executable example using Stage 2 list-head erasure.

## Build Structure

- `formal/Bennett/Copy/Core.lean`: low-dependency blank/observed copy `PEquiv`
  and exact domain laws.
- `formal/Bennett/Copy/Audit.lean`: destructive-overwrite no-go theorems.
- `formal/Bennett/Copy/API.lean`: stable copy re-export.
- `formal/Bennett/Uncompute/Core.lean`: product lift, halt guard, and semantic
  compute-copy-uncompute `PEquiv` definition.
- `formal/Bennett/Uncompute/Correctness.lean`: exact pre/postcondition and
  halting/termination equivalences.
- `formal/Bennett/Uncompute/Audit.lean`: executable example and axiom audit.
- `formal/Bennett/Uncompute/API.lean`: stable uncompute re-export.
- The public root imports `Copy.API` and `Uncompute.API`; neither API imports
  diagnostic audit leaves.

## No-Cheating Checks

- Do not define copy as unrestricted overwrite and then call it reversible.
- Do not omit target blankness/equality or source retention from theorem
  signatures.
- Do not copy the whole work configuration when only observed output is needed.
- Do not use a source predecessor snapshot or the reference computation as
  hidden runtime state.
- Do not claim the composed semantic macro proves concrete stage-rule
  non-overlap or an exact machine transition count.
- Do not infer source halting merely from completing `n` forward transitions;
  the terminal guard must check the next source step is undefined.
- Keep audits out of the public API and scan for proof holes/new axioms.

## Completion Requirements

- Blank copy and uncopy are a proved `PEquiv` with exact domain/pre/postconditions.
- Destructive overwrite is proved noninjective and incapable of a graph inverse
  for any data type with two distinct target values.
- The compute-copy-uncompute result is a `PEquiv`, hence globally reversible as
  a semantic macro.
- Exact correctness proves input and arbitrary initial-history preservation,
  observed output production, and temporary-history cleanup.
- Exact-count success is equivalent to `HaltsIn n`; existential success is
  equivalent to `Terminates`.
- Executable examples and principal axiom audits pass.
- Focused, API, root, and full builds plus hole/shortcut/whitespace/diff scans
  pass and are recorded below.

## Stage Results

- Added `Bennett.Copy.Core` with executable `blankForward`/`blankBackward`,
  `blankEquiv`, retained-work `observedEquiv`, and exact forward/inverse domain
  laws.  Copying is explicitly partial on the known-blank/equal-copy invariants.
- Proved `Copy.injective_of_reversible_outputOnly`: a globally reversible
  fixed-ancilla output-only realization forces the computed function to be
  injective.  This formalizes why general reversible computation retains input
  or equivalent recovery information.
- Added diagnostic `Bennett.Copy.Audit`: destructive overwrite is noninjective,
  its successful graph is not reversible on any target type with two distinct
  values, and it has no graph inverse.
- Added `Bennett.Uncompute.Core` with `liftRight`, executable halt guards,
  fixed-length `recordedEquivAt`, and `computeCopyUncompute`.  The construction
  is the semantic composition `Fₙ ; haltGuard ; observedCopy ; Fₙ⁻¹` packaged as
  a mathlib `PEquiv`.
- Added `Bennett.Uncompute.Correctness`.  Principal results are:
  - `exists_stages_of_run`, exposing `n` forward steps, history growth by `n`,
    the halt check, one successful copy, and `n` backward cleanup steps;
  - `computeCopyUncompute_apply_of_run_halted`, restoring the exact input and
    arbitrary initial-history suffix while leaving `observe after`;
  - `computeCopyUncompute_symm_apply_of_run_halted`, verifying/removing the
    copied observation and restoring the target blank;
  - `computeCopyUncompute_succeeds_iff_blank_and_haltsIn`, making target
    blankness and exact halting necessary and sufficient;
  - `computeCopyUncompute_eq_some_iff`, the exact retained-input/output/history
    characterization;
  - `exists_computeCopyUncompute_iff_terminates`, the two-way existential
    halting correspondence; and
  - `computeCopyUncompute_reversible`, global reversibility of the semantic
    entry-to-exit macro.
- Added stable `Copy.API` and `Uncompute.API` leaves and re-exported both from
  `Bennett.lean`; diagnostic leaves remain outside the public import graph.
- Added executable list-head-erasure examples.  They compute, copy a terminal
  observation, restore the source/history, run the inverse, reject a nonblank
  target, and reject an invalid inverse output by kernel reduction (`rfl`).
- Scope boundary: the exact count `n` is external.  Existence over `n` is a
  logical termination equivalence, not an executable search.  `PEquiv.trans`
  proves sequential macro composition, not non-overlap of a concrete union of
  phase rules.  No target transition, state, rule, or tape-space count is
  inferred.  Autonomous scheduling and Table 1 junction proofs remain Stage 6.
- Arbitrary initial-history suffix preservation relies on reversing exactly
  `n` steps.  A future autonomous reverse phase needs an empty history,
  baseline marker, or an independently proved backward boundary.
- Verification passed:

  ```text
  lake build Bennett.Copy.Core
  lake build Bennett.Copy.Audit
  lake build Bennett.Copy.API
  lake build Bennett.Uncompute.Core
  lake build Bennett.Uncompute.Correctness
  lake build Bennett.Uncompute.Audit
  lake build Bennett.Uncompute.API
  lake build Bennett
  lake build
  ```

- Principal axiom audit reports only Lean/mathlib foundations.  Copy partial
  equivalences use `[propext]`; endpoint and macro-reversibility results use
  `[propext, Quot.sound]`; exact-result/termination characterizations also use
  `Classical.choice` through the mathlib `PEquiv.ofSet` guard surface.  No
  project-specific axiom, `sorry`, or `admit` was introduced.
