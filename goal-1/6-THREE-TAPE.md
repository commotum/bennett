# 6-THREE-TAPE

**Status:** Completed.

## Current Facts

- Stage 5's heterogeneous target configuration is essential here: work and
  output tapes carry source symbols, while history carries intrinsic source rule
  IDs.  Their full alphabets therefore have cardinalities `z`, `z`, and `N+1`
  when the source nonblank alphabet has cardinality `z-1`.
- A forward source step must be represented by two target rules out of phase on
  the work and history tapes.  The upper rule rewrites work while advancing
  history; the lower rule moves work while writing the rule ID on history.
- Pure fresh-state splitting is not range-disjoint when source rules merge.
  The lower rule's history-ID write is the proved mechanism that separates
  those ranges (`C-012`).
- Standard source words have work head `-1`.  To make Bennett's first history
  write occur at cell `0`, the blank history starts with head `-1`; a
  newest-first abstract history list is stored physically in reverse order from
  left to right, with its head on the newest/rightmost record.
- Table 1's copy loop supports `λ=0`: link, move to the coincident right
  delimiter, switch direction, move back, and exit takes five transitions.
  No nonempty-output premise should be introduced unless Lean exposes another
  obligation.
- Initial control is an `A`-phase copy of the source start; final control is a
  distinct `C`-phase copy.  Cleanup is exact on tapes/heads and through a
  phase-forgetting control projection, not raw whole-configuration equality.

## Updated Assumptions

- Use exactly three typed tape roles `work`, `history`, and `output`.
- Represent full controls by disjoint constructors for forward source controls,
  forward connectors, four copy-loop controls, reverse source controls, and
  reverse connectors.  This yields the intended `2f+2N+4` cardinality without
  name-freshness hypotheses.
- Index copy-rule families directly by the finite nonblank `Symbol` type.  The
  executable target machine takes an explicit equivalence from the complete
  proof-facing `TableRuleId` carrier to `Fin ruleCount`; a noncomputable
  `Fintype.equivFin` convenience adapter is separate.
- Keep a proof-facing finite rule-tag family separate from the transported
  intrinsic-`Fin` `QuadrupleMachine`.  Prove table semantics/non-overlap on tags,
  then transport them through an explicit equivalence.
- Build the concrete forward/reverse semantic proofs around an exact physical
  history-tape encoding, while relating it to Stage 2's newest-first
  `HistoryState`/`HistoryRecorder` API where useful.

## Big Picture Objective

Reconstruct Bennett's complete three-tape Table 1 machine and prove that, on
accepted standard inputs, it performs forward history recording, reversible
blank-target copying, and exact reverse cleanup, with explicit halting behavior
and global rule non-overlap.

## Detailed Implementation Plan

- Define the three tape roles, dependent alphabet family, full disjoint control
  family, standard initial/final configurations, and physical history encoding.
- Construct a source-machine `HistoryRecorder` whose records are rule IDs and
  whose recovery operation is Stage 5's validated source-rule inverse.
- Define the two forward rules per source rule and prove exact two-target-step
  simulation, history append, auxiliary output blankness, run lifting, and
  forward/source halting correspondence at phase boundaries.
- Reconstruct all seven copy schemas: five fixed rules and two symbol-indexed
  families.  Prove the exact `4λ+5` trace for every standard word including
  `[]`, retention of history, equality of work/output, blank-target precondition,
  and return of both heads to `-1`.
- Define the reverse rules as phase-renamed formal inverses of the forward
  rules.  Prove exact two-step history pop/source recovery and lift it over an
  arbitrary generated forward run, leaving copied output unchanged.
- Assemble the finite table, prove within-family and cross-family domain/range
  disjointness including the `A_f` and `C_f` boundaries, and obtain executable
  determinism plus the pointwise inverse-table property where appropriate.
- State the central theorem with source determinism/normal form, accepted input,
  all initial/final controls/tapes/heads, input retention, output production,
  history cleanup, both halting directions, and malformed-input scope visible.
- Add an end-to-end finite micro-machine audit.  Prove syntax and time totals
  directly from the already constructed carriers/schedules; defer only the
  distinct visited/nonblank/active-cell derivations to Stage 7.

## Build Structure

- `formal/Bennett/Turing/Source/History.lean`: rule-ID source recorder.
- `formal/Bennett/Turing/Simulator/Core.lean`: tape roles, alphabets, controls,
  history encoding, standard physical configurations.
- `formal/Bennett/Turing/Simulator/Compute.lean`: forward rule pairs and run
  simulation.
- `formal/Bennett/Turing/Simulator/Copy.lean`: copy schemas and word traces.
- `formal/Bennett/Turing/Simulator/Reverse.lean`: reverse rule pairs and cleanup.
- `formal/Bennett/Turing/Simulator/Machine.lean`: complete tagged/finite table.
- `formal/Bennett/Turing/Simulator/Nonoverlap.lean`: all rule-family separation.
- `formal/Bennett/Turing/Simulator/Correctness.lean`: central theorem.
- `formal/Bennett/Turing/Simulator/Audit.lean`: executable examples/axiom audit.
- `formal/Bennett/Turing/Simulator/API.lean`: thin stable re-export.

## No-Cheating Checks

- Do not model the history as an abstract list in the central endpoint while
  claiming a tape theorem; prove the list-to-sparse-tape representation laws.
- Do not use Stage 3's semantic macro as the concrete machine scheduler or as a
  proof of rule-family non-overlap.
- Do not omit the history-ID write from lower forward rules or its checked erase
  from reverse rules.
- Do not assume the copy target is blank implicitly; make its exact cells/head a
  precondition and prove the postcondition.
- Do not treat phase-tag freshness as sufficient for the shared `A_f`/`C_f`
  boundaries; check domains and ranges against link rules.
- Do not state literal whole-configuration restoration across distinct forward
  and reverse control constructors.
- Do not infer exact state/rule/time/space totals from semantic correctness;
  retain constructed syntax/traces for Stage 7 derivations.
- Do not silently exclude empty words or malformed inputs.

## Completion Requirements

- Complete Table 1 syntax exists as typed Lean definitions and a finite target
  machine; all rule families are accounted for.
- Forward simulation records exactly one source rule ID per source step and has
  exact two-step correspondence in both one-step and run forms.
- Copy trace proves blank-target copying and exact work/output/head/history
  endpoints for empty and nonempty standard words.
- Reverse trace restores source work, heads, and blank history exactly while
  preserving copied output and ending in the explicit reverse start control.
- Central correctness states both halting directions and every configuration
  condition directly in its signature.
- Global domain/range non-overlap (or any strictly weaker proved scope) is
  stated honestly and covers all stage boundaries.
- Focused/audit/API/root/full builds, hole/shortcut/import/whitespace scans, and
  principal axiom audits pass; documentation and correction logs are updated.

## Stage Results

- `Simulator.Core` defines the three heterogeneous tapes, disjoint phase
  controls, exact standard endpoints, and a physical newest-first history
  encoding whose records occupy cells `0,…,v-1` while the initial head is `-1`.
- `Source.History` instantiates the abstract `HistoryRecorder` with intrinsic
  source rule IDs and the validated quintuple inverse.
- `Simulator.Compute` proves that every selected source quintuple is exactly two
  target rules and lifts every `v`-step source run to a `2v`-rule schedule.
- `Simulator.Copy` reconstructs all seven copy schemas and proves the exact
  sweep for every word, including `[]`: the target must be blank at head `-1`,
  history is unchanged, both word heads return to `-1`, and the schedule has
  length `4λ+5`.
- `Simulator.Reverse` proves exact two-rule history pop/source recovery and
  lifts cleanup over an arbitrary generated run while retaining the copied
  output.  The output head's blank-delimiter premise is explicit.
- `Simulator.Syntax` and `Simulator.Machine` expose constructor-tagged rules and
  transport them through an explicit enumeration to `QuadrupleMachine`.
  Kernel-checked counts are `2f+2N+4` controls, `4N+2z+3` rules, and alphabet
  sizes `(z,N+1,z)` with `z = card Symbol + 1`.
- `Simulator.Nonoverlap` proves global domain and range disjointness.  The
  strongest reusable theorem needs source key injectivity and only the weaker
  condition that no `(finish, blank)` source rule exists; Bennett normal form
  supplies both.  Sharp overlap theorems show why each is needed.
- `Simulator.Correctness.central_correctness` exposes source run/halt,
  acceptance, exact initial/final controls/tapes/heads, input retention, copied
  output, blank history, exact time `4v+4λ+5`, relational determinism, and
  executable-step reversibility.  `terminates_iff_source` proves both halting
  directions on accepted standard inputs.
- `Control.source?` and `logicalControl_restored` make the corrected logical
  control equality explicit while retaining the physically distinct `A₁` and
  `C₁` controls in the endpoint certificate.
- Malformed physical configurations remain executable but are intentionally
  outside the central theorem.  Divergence preservation proves that no such
  premature halt is reachable from a standard initial configuration while the
  source continues.
- `Simulator.Audit` instantiates a three-rule source and the full 19-rule target,
  proves its empty-word computation takes 3 source and 17 target transitions,
  and instantiates global syntactic reversibility.  Focused audit and public
  API/root builds pass.  Principal `#print axioms` checks report only
  `propext`, `Classical.choice`, and `Quot.sound`.
