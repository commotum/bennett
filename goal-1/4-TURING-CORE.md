# 4-TURING-CORE

**Status:** Completed on 2026-07-17.

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
- Represent a source program by an intrinsic count `N` and a table
  `Fin N → Quintuple`.  Define its existential rule relation separately from the
  first-applicable executable scanner, then prove agreement under a visible
  key-injectivity assumption.  This gives exact rule identifiers/counts without
  imposing `Fintype` on the control or nonblank-symbol types.
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

- Added `Bennett.Turing.Tape`:
  - `TapeSymbol Symbol` adjoins exactly one typed blank to the nonblank alphabet;
  - `Tape` is the canonical sparse store `Int →₀ TapeSymbol Symbol` plus an
    absolute `Int` head;
  - custom `CellStore.set` is executable, unlike mathlib's noncomputable
    `Finsupp.update` in the pinned version;
  - read/write/move/write-then-move laws, update idempotence, exact active and
    nonblank positions, `TapeSymbol.equivOption`, and alphabet cardinality are
    exposed.
- Added `Bennett.Turing.Word`.  A standard word is simply `List Symbol`, so an
  embedded blank is unrepresentable.  `Tape.ofWord` places it at absolute cells
  `[0,length)`, scans the left blank `-1`, and deliberately supports `[]`.
  Proved exact support `Finset.Ico`, both delimiter blanks, support cardinality,
  indexed reads, and `Tape.ofWord_injective`.
- Added `Bennett.Turing.Source.Core` with `Configuration`, source `Quintuple`,
  explicit `Matches`, write/move/control `execute`, and finite `Machine` syntax
  with `ruleCount` and `RuleId = Fin ruleCount`.  Execution selects the least
  matching rule and remains separate from the existential `StepRel`.
- Added `Bennett.Turing.Source.Determinism`.  The key condition
  `SyntacticallyDeterministic` is injectivity of indexed
  `(source, scanned)` keys.  It proves declarative `StepRel` right-uniqueness and
  `step = some ↔ StepRel`.  A negative two-rule example demonstrates that a
  priority-based `PartialStep` alone does not prove unique applicability.
- Added `Bennett.Turing.Source.Standard`:
  - exact `Standard.config`, optional `NonemptyWord`, and relational
    `ComputesIn`/`Computes`;
  - accepted inputs are an explicit `Behavior.accepts` predicate rather than
    all syntactically standard words by fiat;
  - `BennettNormalForm` replaces “appear in no other quintuple” with separate
    unique-entry/no-incoming-start/unique-exit/no-outgoing-finish fields;
  - initial-entry execution and final-control halting are proved; and
  - `computes_output_unique` proves the standard relation is a partial function.
- Added `Bennett.Turing.Resource`.  `ExecutionTrace` has a mandatory initial
  state and list of subsequent states, so a successful `n`-step trace contains
  `n+1` states and has transition count `n`.  `runs_iff_exists_run` bridges it
  exactly to Stage 2 `Runs`.
- Resource measures are deliberately separate: `visitedPositions`,
  `everNonblankPositions`, `footprintPositions`, `maximumNonblankCells`, and
  `maximumActiveCells`.  `delimiterTraversal_card` proves a potential complete
  word sweep has `length+2` positions, including two positions for the empty
  word.  This does not assert that a particular machine actually performs the
  sweep.
- Added kernel-checked executable examples for a one-rule machine: it writes at
  old head `-1`, moves to `0`, scans the first original symbol, halts, produces a
  two-state/one-transition trace, and exercises zero-step/empty-word resources.
  No `native_decide` proof is used.
- Added thin `Turing.API`, re-exported it from `Bennett.lean`, and kept
  `Turing.Audit` outside the public import graph.
- Verification passed:

  ```text
  lake build Bennett.Turing.Tape
  lake build Bennett.Turing.Word
  lake build Bennett.Turing.Source.Core
  lake build Bennett.Turing.Source.Determinism
  lake build Bennett.Turing.Source.Standard
  lake build Bennett.Turing.Resource
  lake build Bennett.Turing.Audit
  lake build Bennett.Turing.API
  lake build Bennett
  lake build
  ```

- Principal axiom audit reports only Lean/mathlib foundations.  Sparse-tape,
  finite-support, finite-cardinality, and rule-selection results use
  `[propext, Classical.choice, Quot.sound]`; the generic exact trace/run bridge
  uses `[propext, Quot.sound]`.  No project-specific axiom, proof hole, or
  compiler-trusting `native_decide` proof was introduced.
- Correct interpretation learned for later stages: `Tape.blank` has head `0`,
  while `Tape.ofWord []` is blank with head `-1`; theorem signatures must always
  name blank-tape heads.  For a word of length `λ`, nonblank support is `λ`,
  simultaneous active cells at a delimiter are `λ+1`, and a complete
  delimiter-to-delimiter footprint is `λ+2`.  The paper's “squares used” cannot
  be identified with one of these without a constructed trace theorem.
