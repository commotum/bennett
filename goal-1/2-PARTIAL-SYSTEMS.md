# 2-PARTIAL-SYSTEMS

## Current Facts

- Stage 1 pinned Lean 4.31.0/mathlib and the root build succeeds.
- `Mathlib.Data.PFun` is available, but its dependent-domain representation has
  been checked and is not preferable for executable one-step semantics.
- Mathlib `PEquiv` exactly provides the executable partial-bijection bundle, and
  `StateTransition.Reaches`/`eval` provide reachability and potentially divergent
  whole-computation semantics.
- Bennett's pairwise rule-domain/range non-overlap is a syntactic unique-rule
  discipline stronger than extensional successor/predecessor uniqueness.
- Table 1's rule index suffices because each local Turing rule is injective.  An
  arbitrary deterministic transition needs an explicit predecessor-recovery
  interface and may need to record the whole predecessor.
- The concrete Table 1 phase changes `A₁` to `C₁`; an abstract history theorem
  may still restore its single underlying state carrier literally.

## Updated Assumptions

- Use `PartialStep α := α → Option α` as the executable primary interface.
  It makes successor determinism structural and preserves computation.
- Define semantic reversibility as predecessor uniqueness, globally and on a
  specified set, rather than `Function.Injective step` (which would incorrectly
  require all halted states mapping to `none` to be equal).
- Represent exact finite execution by an iterated partial step and a proposition
  `Runs step n start finish`; prove its connection to reachability and halting.
- `HistoryRecorder` provides a single-pass `stepWithRecord`, its projection to
  the source step, a partial recovery function, and both graph directions.  The
  second recovery law rejects forged/noncanonical records and is needed for the
  backward-then-forward inverse law.
- Store newest records at the head of a `List`, making reverse execution a stack
  pop.  One forward source transition adds exactly one record.

## Big Picture Objective

Implement and prove the model-independent foundation: deterministic partial
steps, exact runs and halting, global/restricted reversibility, a recorded
history lift with a genuine partial inverse, and exact multi-step cleanup.

## Detailed Implementation Plan

- Add semantic core definitions for partial steps, their graph relation,
  halting, successor determinism, predecessor uniqueness, and partial inverses.
- Add executable iteration, exact runs, reachability, halting-in/termination,
  composition/determinacy lemmas, and iteration of inverse steps.
- Define history recovery schemes, recorded configurations, forward/backward
  steps, and both single-step inverse laws.
- Prove source-run projection/lifting, one-record-per-step length, exact reverse
  cleanup after any finite forward run, and two-way halting/termination
  correspondence.
- Add a finite executable example with an irreversible source transition and a
  small record type, plus negative results showing the unrecorded source is not
  reversible and forged history cannot run backward.
- Export only stable semantic/history APIs; keep examples and no-go diagnostics
  in an audit leaf.

## Build Structure

- `formal/Bennett/Transition/Core.lean`: low-dependency semantic definitions and
  one-step lemmas.
- `formal/Bennett/Transition/Run.lean`: executable iteration, finite runs,
  halting, and generic multi-step inverse proofs.
- `formal/Bennett/Transition/Reachability.lean`: heavier proof leaf bridging
  exact runs to mathlib `StateTransition.Reaches` and `eval`.
- `formal/Bennett/Transition/API.lean`: thin stable transition re-export.
- `formal/Bennett/History/Core.lean`: recovery interface and one-step recorded
  forward/backward construction.
- `formal/Bennett/History/Run.lean`: projection, length, cleanup, and halting
  equivalence theorems.
- `formal/Bennett/History/Audit.lean`: executable and negative examples only.
- `formal/Bennett/History/API.lean`: thin stable history re-export.
- `formal/Bennett.lean`: add only the two stable API imports after focused leaves
  pass; internal leaves never import the root.
- Focused builds: each `Core` then `Run`, followed by `Bennett.History.Audit`.
- Adjacent builds: `Bennett.Transition.API`, `Bennett.History.API`, and `Bennett`.

## No-Cheating Checks

- Do not define reversibility as injectivity of the `Option`-valued step; multiple
  halted states are legitimate.
- Do not assume rule non-overlap is necessary for extensional determinism.
- Do not hide a predecessor snapshot inside the generic API.  Recovery data is
  an explicit type/assumption; any snapshot instance is labeled as a fallback.
- Do not prove only forward-after-backward or backward-after-forward: the
  recorded steps must satisfy both graph directions.
- Do not prove cleanup only up to projection: the abstract theorem must recover
  the exact initial state and exact initial history list.
- Do not export audit examples or diagnostics through the public root.
- Scan for `sorry`, `admit`, project axioms, and physical-model vocabulary.

## Completion Requirements

- Every planned module compiles without proof holes or new axioms.
- The step graph is deterministically single-successor by construction, while
  global and set-restricted predecessor uniqueness are separate definitions.
- Generic partial inverses reverse every exact finite run.
- Recorded forward/backward steps are proved partial inverses in both directions.
- Any `n`-step recorded forward run adds exactly `n` records, and running the
  backward step `n` times restores the exact starting configuration/history.
- Source and recorded execution have same-step run and halting/termination
  equivalences in both directions.
- Audit examples evaluate and prove the source can be irreversible while the
  recorded lift is reversible.
- Focused, API, root, and full builds pass; proof-hole/shortcut/whitespace scans
  and `git diff --check` pass; principal axiom audits are recorded.

## Stage Results

- **Runtime semantics:** added `PartialStep`, successful `Graph`/`GraphOn`,
  `Enabled`, `Halted`, structural `Deterministic`, `ReversibleOn`, and global
  `Reversible` in `Bennett.Transition.Core`.
- **Standard bridges:** proved successor determinism as `Relator.RightUnique`,
  restricted/global reversibility as `Relator.LeftUnique`, and used mathlib
  `PEquiv` as `PartialStep.InversePair` instead of duplicating a partial-bijection
  structure.
- **Exact execution:** added executable `iterate`, exact `Runs`, `HaltsIn`,
  `Terminates`, `RunsForever`, composition/determinacy lemmas, and the theorem
  that any graph inverse reverses every exact `n`-step run.
- **Mathlib integration:** `ReachableFrom` is mathlib
  `StateTransition.Reaches`; `reachable_iff_exists_runs` bridges exact counts;
  `terminates_iff_eval_dom` and `mem_eval_iff` connect to the `Part`-valued
  evaluator.  This heavier import is isolated in `Transition.Reachability`.
- **History abstraction:** `HistoryRecorder` exposes `stepWithRecord`,
  `forget_record`, partial `recover`, and both generated/sound recovery laws.
  Its lifted `forward`/`backward` steps have converse graphs globally and package
  as a mathlib `PEquiv`; malformed histories are outside the backward domain.
- **Run theorems:** `iterate_forward_current` proves exact source projection;
  `exists_forward_run_iff` proves same-count lifting in both directions;
  `history_length_of_run` proves one record per source step; `reverse_run` and
  `trace_cleanup` restore the exact starting state and arbitrary starting history
  suffix; `forward_haltsIn_iff`, `forward_terminates_iff`, and
  `forward_runsForever_iff` prove two-way behavior correspondence.
- **Executable audit:** list-head erasure maps both `[false]` and `[true]` to
  `[]`, so `popStep_not_reversible` proves the source is globally irreversible.
  `popRecorder` stores only the discarded bit, its lift is globally reversible,
  two forward/backward steps evaluate exactly, and an invalid `none` record is
  rejected.  The audit leaf is not imported by either public API.
- **Focused builds:** `Bennett.Transition.Core`, `Transition.Run`,
  `Transition.Reachability`, `History.Core`, `History.Run`, and `History.Audit`
  all succeeded.  The final representative counts were 401 jobs for the narrow
  exact-run leaf, 659 for the mathlib reachability bridge, 542 for history runs,
  and 543 for the executable audit.
- **Public builds:** `Bennett.Transition.API`, `Bennett.History.API`, the root
  `Bennett`, and default `lake build` all succeeded; the default/root graph built
  665 jobs.
- **Axiom audit:** principal inverse, cleanup, termination, and recorded
  reversibility theorems use only Lean/mathlib foundations: `propext` and, for
  list/iteration results, `Quot.sound`.  No project axiom appears.
- **Scans:** no `sorry`, `admit`, axiom declaration, physical vocabulary, public
  import of `History.Audit`, or trailing whitespace was found; `git diff --check`
  passed.
- **Plan fold-back:** Stage 2 is complete.  Stage 3 can use the established
  `PEquiv`/exact-run layer to state copying as a partial bijection on a blank
  target and compose compute-copy-uncompute with explicit phase separation.
