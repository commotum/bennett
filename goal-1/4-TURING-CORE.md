# 4-TURING-CORE

**Status:** In progress.

## Current Facts

- Stage 2 provides generic exact-count `PartialStep` runs and halting.  Stage 4
  should instantiate those definitions rather than create incompatible run
  semantics.
- The paper uses a two-way-infinite tape, reads and writes the scanned cell,
  then moves left/right/stays and changes control.  It supplies no left-boundary
  convention.
- Stage 6 needs executable rule selection and explicit syntax; Stage 7 needs
  finite nonblank support, absolute head positions, distinct visited cells, and
  maximum simultaneous occupancy.  A non-canonical raw zipper would make exact
  equality and inverse proofs unnecessarily representation-dependent.
- The public semantic distinction from Stage 2 remains mandatory: an
  `Option`-valued executable step is extensionally deterministic by type, while
  syntactic determinism means uniqueness of the applicable rule.
- Standard words have no blank symbols and the head scans the blank immediately
  to their left.  The source does not decide whether the empty word is legal.

## Updated Assumptions

- Use absolute `Int` positions and a finitely supported cell function, with
  `0` as the distinguished blank.  This gives a canonical two-way-infinite tape
  and an executable finite nonblank support without trimming invariants.
- Keep the alphabet and control-state types generic.  Require decidable equality
  for execution; require `Fintype` only in later syntax/cardinality theorems.
- Represent a source program as a finite list of quintuples.  Define its
  existential rule relation separately from the first-applicable executable
  scanner, then prove agreement under a visible key-uniqueness assumption.
- Allow empty proof-carrying standard words at the data-model level.  Later
  theorems must either cover them or add an explicit nonempty premise.
- Count source transitions with Stage 2 `Runs`.  Define trace-derived visited,
  footprint, nonblank, and peak-simultaneous measures separately; do not call
  any one of them the paper's ambiguous “squares used” without a theorem.

## Big Picture Objective

Define a canonical executable source Turing-machine core, standard tape format,
and resource vocabulary precise enough for the reversible syntax and simulator
stages without committing resource claims that have not yet been derived.

## Detailed Implementation Plan

- Implement `Tape` over `Int →₀ Symbol`, with blank `0`, absolute head position,
  `read`, `write`, and left/stay/right movement plus exact operation lemmas.
- Define proof-carrying blank-free words and a canonical standard tape whose
  word begins at position `0` and whose head is at `-1`; prove/exercise delimiter
  and empty-word behavior.
- Define source `Direction`, `Configuration`, `Quintuple`, applicable-rule
  relation, finite machine syntax, and executable first-applicable step in the
  paper's read/write/move/control order.
- Define syntactic key uniqueness on `(sourceState, readSymbol)` and prove
  relational successor uniqueness plus agreement between an applicable rule and
  executable selection.
- Define standard source configurations and narrowly scoped standard-source
  entry/exit assumptions needed later, avoiding the paper's ambiguous phrase
  “appear in no other quintuple.”
- Define finite execution traces including both endpoints and resource measures:
  visited head positions, nonblank support, active cells (support plus head),
  whole-trace footprint, and peak simultaneous active-cell count.
- Add executable write-before-move, left-of-origin, empty-word, rule-selection,
  halting, trace-length, and off-by-one examples.

## Build Structure

- `formal/Bennett/Turing/Tape.lean`: canonical tape runtime and cheap laws.
- `formal/Bennett/Turing/Word.lean`: blank-free words and standard tapes.
- `formal/Bennett/Turing/Source/Core.lean`: source syntax/configurations/runtime.
- `formal/Bennett/Turing/Source/Determinism.lean`: relation/selection proofs.
- `formal/Bennett/Turing/Source/Standard.lean`: accepted format and explicit
  source assumptions.
- `formal/Bennett/Turing/Resource.lean`: trace and distinct cost measures.
- `formal/Bennett/Turing/Audit.lean`: executable examples and axiom audit.
- `formal/Bennett/Turing/API.lean`: thin stable re-export.
- Focused builds start at each new leaf; public and root builds run only after
  the API import graph changes.

## No-Cheating Checks

- Do not use a one-sided tape or silently clamp negative moves.
- Do not use a zipper with observationally redundant trailing blanks unless a
  canonicalization theorem is proved.
- Do not identify first-match execution with all-rule relational semantics
  before proving unique applicability.
- Do not call extensional `PartialStep.Deterministic` a proof of syntactic rule
  determinism.
- Do not exclude the empty word silently.
- Do not conflate nonblank support, head-visited cells, whole-trace footprint,
  or peak simultaneous cells.
- Do not infer Bennett's exact Table 1 costs from this source-machine core.

## Completion Requirements

- Tape, source configuration, rules, and finite-machine step are executable and
  their operation order is covered by reduction examples and lemmas.
- Syntactic key uniqueness proves relational successor uniqueness and agreement
  with executable rule selection.
- Standard input/output format names the blank, word origin, head position, and
  empty-word policy explicitly.
- Trace/resource definitions distinguish every measure required by Stage 7 and
  have off-by-one tests.
- Focused, audit, API, root, and full builds pass; audit leaves are not publicly
  re-exported; proof-hole/shortcut/whitespace scans pass.
- Traceability, conventions, corrections, stage results, and `0-plan.md` are
  updated with exact declarations and any model-driven repairs.

## Stage Results

- In progress.
