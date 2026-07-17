# 5-QUADRUPLES

**Status:** Completed on 2026-07-17.

## Current Facts

- Stage 4 supplies canonical tapes, source quintuples, intrinsic finite rule
  identifiers, and an executable/declarative semantics split.  Stage 5 should
  reuse those tapes and the Stage 2 `PartialStep` inverse vocabulary.
- Bennett's target action is typed by construction: on each tape a quadruple
  either checks and rewrites the scanned symbol without moving, or moves without
  reading or writing.  An ill-typed pair of optional fields would recreate the
  source paper's notation ambiguities inside Lean.
- The inverse of a rewrite exchanges its checked and written symbols; the
  inverse of a move reverses its direction.  The target control states exchange
  roles.  Exact inverse execution must include tape contents and absolute heads.
- Domain compatibility depends on equal source controls and compatible checked
  symbols wherever both actions rewrite.  Range compatibility analogously
  depends on equal target controls and compatible written symbols; the
  Markdown source's solidus in an output field is a transcription error.
- Pairwise syntactic non-overlap is sufficient for unique applicable rules and
  unique predecessors, but is stronger than extensional uniqueness if distinct
  syntactic rules induce the same partial map.  Both levels must remain named.
- Splitting a source rule requires one connector per rule.  The first target
  rule checks/rewrites; the second moves.  Other tapes perform a null move, so
  they are neither read nor written during the lifted one-tape simulation.

## Updated Assumptions

- Represent a target configuration by a control, a tape-index type, and a
  dependent alphabet family `Symbol : TapeIndex → Type`.  This specializes
  cleanly to Bennett's three tapes while allowing work/output symbols and
  history rule IDs to have different types; the finite tape-index instance is
  required only for executable matching.
- Represent a per-tape action by an inductive `rewrite scanned written` or
  `move direction`.  Applicability is a proposition/decision; execution is a
  total map used only after applicability has been established.
- Give a finite target machine intrinsic `ruleCount` and indexed rules, matching
  the source syntax.  Keep its existential all-rule relation separate from a
  least-index executable selector.
- Define domain/range overlap semantically first.  Prove the tape-wise criteria
  rather than installing them as definitions.  Use the constructed formal
  inverse to derive range facts where that makes the proof less brittle.
- Use `SplitState Control RuleId := original Control | connector RuleId`; this
  makes freshness and connector uniqueness structural rather than hypotheses.
  The exact two-step theorem will be stated for the lifted work tape and all
  untouched auxiliary tapes.

## Big Picture Objective

Formalize Bennett's reversible read/write-or-move syntax and prove the local,
rule-collection, and source-rule-splitting facts that the paper leaves to
inspection.

## Detailed Implementation Plan

- Add move reversal and exact two-sided tape-movement cancellation lemmas.
- Define typed actions, multi-tape configurations, quadruples, applicability,
  execution, and a partial single-rule step.
- Construct `Action.inverse` and `Quadruple.inverse`; prove converse successful
  graphs and exact restoration in both directions.
- Define semantic domain/range overlap and decidable tape-wise compatibility;
  prove both iff characterizations, including concrete overlap witnesses.
- Define finite quadruple machines, pairwise domain/range disjointness, and
  prove unique applicability, declarative determinism, executable agreement,
  predecessor uniqueness, and a machine-level inverse table.
- Split each indexed source quintuple through a structurally fresh connector
  state, lift it to an arbitrary designated work tape, and prove exact two-step
  agreement with the source write-then-move semantics.
- Add negative and executable audits for overlapping rewrite rules,
  write/move noncommutation, inverse movement, connector uniqueness, and the
  distinction between priority execution and syntactic determinism.

## Build Structure

- `formal/Bennett/Turing/Quadruple/Core.lean`: typed runtime syntax/semantics.
- `formal/Bennett/Turing/Quadruple/Inverse.lean`: local inverse construction.
- `formal/Bennett/Turing/Quadruple/Overlap.lean`: overlap criteria.
- `formal/Bennett/Turing/Quadruple/Machine.lean`: finite rule-table semantics.
- `formal/Bennett/Turing/Quadruple/Split.lean`: fresh-state source splitting.
- `formal/Bennett/Turing/Source/Inverse.lean`: constructive source-quintuple
  shift/read/write inverse.
- `formal/Bennett/Turing/Quadruple/Audit.lean`: diagnostics and axiom audit.
- `formal/Bennett/Turing/Quadruple/API.lean`: thin public re-export.

## No-Cheating Checks

- Do not represent impossible read-plus-move or move-plus-write actions.
- Do not call a rule inverse merely because its syntax looks reversed; prove
  converse successful-step graphs on complete configurations.
- Do not define overlap by the paper's criterion and then claim to have proved
  the criterion.  Start from nonempty semantic domain/range intersection.
- Do not infer rule-table reversibility from each rule being locally injective;
  distinct rule ranges also must be disjoint.
- Do not identify a least-index executor with the whole rule relation before
  proving domain non-overlap.
- Do not assume connector freshness or uniqueness when a sum type can enforce it.
- Do not count Stage 6 history/output actions or Stage 7 resources here.

## Completion Requirements

- Local quadruple inverse laws restore every tape cell, head, and control state.
- Domain and corrected range-overlap iff theorems compile with explicit
  witnesses; the source transcription correction is documented.
- Machine-level pairwise non-overlap yields relational determinism and semantic
  reversibility, with executable agreement under domain disjointness.
- Every source quintuple has a structurally fresh two-rule split whose exact
  two-step execution agrees on the work tape and leaves auxiliaries unchanged.
- Focused/audit/API/root builds and hole/shortcut/whitespace/import scans pass;
  principal exported theorems have an axiom audit.

## Stage Results

- Added `Bennett.Turing.Source.Inverse`.  A source quintuple's checked inverse
  moves the head backward, checks the previously written symbol, then restores
  the scanned symbol.  `singleStep_areInverses` proves exact converse graphs and
  `execute_injective_on` proves individual source-rule injectivity without
  pretending the inverse is another read/write/move quintuple.
- Added `Bennett.Turing.Quadruple.Core` with:
  - typed `Action.rewrite scanned written` versus `Action.move direction`;
  - heterogeneous `MultiConfiguration Control TapeIndex Symbol`, where
    `Symbol index` may differ per tape; and
  - `Quadruple`, exact applicability/execution, and a partial single-rule step.
  Heterogeneity is a model correction discovered during prototyping: it is
  necessary for the later work/history/output alphabet sizes `(z,N+1,z)`.
- Added `Quadruple.Inverse`.  `Move.inverse` and exact movement cancellation
  support pointwise action inversion.  `Quadruple.inverse_execute` restores
  every control, tape cell, and absolute head; `step_areInverses` packages the
  converse successful graph, and `inversePair` exposes a mathlib `PEquiv`.
- Added `Quadruple.Overlap`.  Semantic `DomainsOverlap` and `RangesOverlap` are
  nonempty intersections of complete-configuration domains/ranges.  They are
  proved equivalent to finite tape-wise compatibility tests, rather than being
  defined by those tests.  Range compatibility compares written symbols and
  treats moves as unrestricted, formally repairing the Markdown transcription
  error in `C-001`.  Decidability is transported from the proved criteria.
- Added `Quadruple.Machine` with intrinsic finite rule IDs, least-index
  execution, and a separate existential all-rule relation.  Proved:
  - domain disjointness gives rule uniqueness, relation right-uniqueness, and
    executable/declarative agreement;
  - range disjointness gives relation left-uniqueness and semantic
    `PartialStep.Reversible` even for priority execution; and
  - both obligations make the pointwise inverse table the exact executable
    partial inverse.
- The audit contains a concrete two-rule table whose domains and ranges overlap
  but whose union relation is nevertheless both right- and left-unique because
  the rules agree on their overlap.  This kernel-checks the `C-008` correction:
  pairwise rule-ID non-overlap is sufficient, not extensionally necessary.
- Added `Quadruple.Split`.  `SplitState Control RuleId = Control ⊕ RuleId`
  makes every connector fresh and unique by construction.  `writeHalf` checks
  and rewrites the chosen work tape; `moveHalf` moves it; all auxiliary tapes
  perform an unrestricted null move.  `lift_two_step_of_matches` proves both
  applicability facts and exact agreement with source execution while
  preserving arbitrary heterogeneous auxiliary tapes.
- The actual finite `splitMachine` contains exactly `2N` rules, adds exactly
  `N` connector controls (`f+N` total for this component), and is
  domain-disjoint under source key injectivity.
- Pure splitting is not generally reversible.  The exact theorem
  `moveHalf_rangesOverlap_iff_target_eq` proves that two lower halves overlap in
  range precisely when their source targets agree, and
  `splitRule_ranges_disjoint_iff_target_injective` lifts this to the whole
  tagged split family.  Bennett's Stage 6 history-symbol write is therefore a
  mathematically necessary separator for merging irreversible source rules;
  this is recorded as `C-012`.
- Executable audits cover heterogeneous alphabets, rewrite/move behavior,
  full inverse restoration, write/move noncommutation, semantic overlap
  decisions, a deterministic-but-not-range-disjoint split source, and the
  extensional non-necessity example.  No `native_decide` proof is used.
- Verification commands completed successfully:

  ```text
  lake build Bennett.Turing.Source.Inverse
  lake build Bennett.Turing.Quadruple.Core
  lake build Bennett.Turing.Quadruple.Inverse
  lake build Bennett.Turing.Quadruple.Overlap
  lake build Bennett.Turing.Quadruple.Machine
  lake build Bennett.Turing.Quadruple.Split
  lake build Bennett.Turing.Quadruple.Audit
  lake build Bennett
  lake build
  ```

- The principal axiom audit reports only Lean/mathlib foundations
  `[propext, Classical.choice, Quot.sound]`; the split-table domain-disjointness
  theorem needs only `[propext, Quot.sound]`.  No project axiom, proof hole, or
  compiler-trusting evaluation was introduced.
