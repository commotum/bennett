# 5-QUADRUPLES

**Status:** In progress.

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

- Represent a target configuration by a control and a `Fin tapeCount`-indexed
  family of Stage 4 tapes.  This keeps tape count intrinsic and specializes
  cleanly to Bennett's three tapes.
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

Pending implementation.
