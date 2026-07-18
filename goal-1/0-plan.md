# Goal 1 — Verified Bennett Reversible Computation Library

## Big-Picture Objective

Build a pinned, reusable Lean 4 library that reconstructs the mathematical core
of C. H. Bennett's 1973 paper *Logical Reversibility of Computation*.  The
library will separate general partial-transition-system results from a concrete
Turing-machine realization, prove compute-copy-uncompute correctness and the
central three-tape simulation theorem, and audit the exact resource claims that
are meaningful under the chosen cost model.

The paper is evidence and motivation, not a formal specification.  Every claim
used by the library must be restated precisely and proved under inspectable
assumptions.  Material that cannot be verified is recorded as unresolved or
excluded rather than silently weakened.

## Non-Negotiable Constraints

- Pin Lean and mathlib; keep the project compiling incrementally.
- Completed public modules contain no `sorry`, `admit`, or project-specific
  axioms.  Temporary theorem skeletons may exist only in an explicitly
  incomplete stage file and must never be exported.
- Do not equate determinism with reversibility.  Model partiality, domains,
  ranges, and inverse execution explicitly.
- Do not claim global injectivity when only standard reachable configurations
  are covered; theorem signatures must expose the distinction.
- State exact tape, head, control-state, input, output, blankness, halting, and
  cost conventions before proving the central theorem.
- Copying is reversible only with a proved target invariant (normally a known
  blank target); arbitrary overwriting is not admitted as a reversible copy.
- Resource counts are derived from machine syntax and execution traces, not
  inferred from semantic correctness or asymptotic prose.
- No unjustified axioms, invented proofs, or silent repairs.  Failed obligations
  are recorded with the closest useful proved result and classified as a
  mathematical obstruction or infrastructure gap.
- Physical claims about entropy, energy, chemistry, and biology are excluded
  from the mathematical core unless separately reduced to precise assumptions.
- Keep runtime definitions, public API, proof leaves, examples, and diagnostic
  audits in appropriate dependency layers, following `BUILD-PLAN.md`.

## Current Facts

- The source is available as `bennett-1973/bennett-1973.md` and an eight-page
  PDF with images of Tables 1 and 2.
- Stage 1 established the `formal/` Lake project on Lean 4.31.0 (Lean commit
  `68218e876d2a38b1985b8590fff244a83c321783`) and mathlib commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; the resolved manifest pins all
  transitive dependencies.
- The paper's main construction uses read-write-shift quintuples for the source,
  read/write-or-shift quadruples for the reversible target, and three tapes.
- Stages 6–7 reconstruct the complete Table 1 syntax and prove the paper's exact
  target counts `2f + 2N + 4` states, `4N + 2z + 3` quadruples, alphabet sizes
  `(z,N+1,z)`, and run time `4v + 4λ + 5`.  The space audit keeps raw head
  visits, ever-nonblank support, their footprint union, maximum nonblank cells,
  and maximum active cells as distinct metrics.
- The complete PDF and both table images have been audited.  Table 1's state,
  rule, alphabet, and time arithmetic is internally correct under its atomic
  history-symbol/fresh-state conventions.  If `s` is the source-footprint
  cardinality, its tape-1 result is exactly `s` when the final right delimiter
  was already in that footprint and exactly `s+1` otherwise.
- The Markdown range-overlap formula at line 94 is a conversion error: the PDF
  correctly tests unprimed read fields for `/`.  Syntactic rule non-overlap is a
  sufficient unique-rule discipline but is stronger than extensional semantic
  determinism/reversibility.
- Table 1 begins in `A₁` and ends in distinct `C₁`; concrete cleanup restores
  tapes and heads exactly but restores control only through a phase-forgetting
  correspondence.
- Stage 2 now exposes executable `PartialStep`, exact `Runs`/halting, mathlib
  reachability/evaluator bridges, global and reachable-set reversibility,
  two-sided `PEquiv` history instrumentation, exact reverse cleanup, and
  same-step termination/divergence correspondence.
- The paper's segmented-history and physical sections are downstream of the
  main semantic theorem and are not prerequisites for it.
- Stage 5 now exposes heterogeneous multi-tape quadruples, exact formal inverse
  execution, semantic domain/range overlap iff finite compatibility tests,
  finite-table non-overlap theorems, the constructive shift/read/write inverse
  of a source quintuple, and a fresh-state two-rule split.  Pure splitting is
  range-disjoint exactly when source rule targets are injective, so the Stage 6
  history write is an essential part of Bennett's general simulator.
- Stage 6 exposes a globally domain/range-disjoint finite three-tape machine,
  exact forward/copy/retrace schedules (including empty output), two-way halting
  equivalence on accepted standard inputs, and a central certificate naming
  every initial/final tape, head, and phase-tagged control state.
- Stage 7 proves exact copy-phase work/output geometry: visited and footprint
  cardinality `λ+2`, ever-nonblank and peak-nonblank size `λ`, and peak active
  size `λ+1`.  Its canonical physical history trace has footprint `v+1` and
  peak nonblank size `v`.
- For a standard full schedule, Stage 7 proves target work footprint equals the
  source footprint union `Icc (-1) λ`, equivalently insertion of the final
  right delimiter `λ`; the full target creates no new nonblank work position.
- Stage 8 defines complete restart checkpoints abstractly: the checkpoint type
  must include control, tapes, heads, phase, and any other state needed to
  resume.  A `HistoryRecorder` implementation of one segment erases every
  primary-history record it generates and restores the caller's scratch
  baseline exactly.
- Stage 8's global checkpoint chain is a `PEquiv`; a full `n`-segment run keeps
  the permanent original and uses exactly `n-1` intermediate dumps.
  `Checkpoint.Plan` maps block lengths to exact source-step iterates and bridges
  a source run of their sum to full-chain completion and copied-output cleanup.
- The exact discrete temporary budget is `v ⌈/⌉ n + (n-1)s`.
  The paper-rounded `v ⌈/⌉ n + ns` is one `s`-cell dump higher for
  `n > 0`.  The verified ideal time is four source-level passes plus explicit
  parameterized dump I/O.
- The ceiling-square-root segment choice has a proved near-balanced bound but
  is not claimed to minimize the discrete objective exactly.  The paper's
  positive-real `2√(vs)` AM--GM statement is proved separately; nested
  logarithmic-space/quadratic-time checkpointing remains speculative and
  excluded.

## Working Assumptions to Test

- Nested checkpointing remains excluded: the paper offers no construction from
  which to derive its speculative logarithmic-space/quadratic-time claim.  A
  later extension would need an explicit recursive schedule, checkpoint
  invariant, allocation model, and time/space proof.

## Success Metrics and Final Verification

The goal is complete only when all of the following are evidenced:

1. A pinned `lake build` succeeds for the full project.
2. Public APIs expose deterministic partial systems, partial reversibility,
   histories, copying, uncomputation, Turing semantics, simulation, and costs.
3. The abstract recorded-history transition has a proved partial inverse, and
   reverse execution restores the exact initial state and empties history.
4. A reusable compute-copy-uncompute theorem proves input retention, copied
   output production, and cleanup under explicit copy invariants.
5. A concrete source-machine/target-machine theorem states both directions of
   halting equivalence and exact initial/final configurations, determinism, and
   the appropriate form of reversibility.
6. Every exact state/rule/alphabet/time/space claim reported as verified is
   proved in the selected cost model.  Unsupported paper claims remain clearly
   marked unresolved or heuristic.
7. Representative small machines evaluate in examples or tests.
8. Traceability and correction documents classify the paper's principal
   definitions, tables, theorem, resource claims, segmented-history discussion,
   and excluded physical discussion.
9. `rg -n "sorry|admit|axiom"` has no unexplained hit in completed Lean modules,
   `git diff --check` passes, and `#print axioms` audits of principal results are
   recorded.

## Stages

### 1-GUARDRAILS — Source audit and compiling project skeleton

**Status:** Completed.

#### Big Picture Objective

Establish the pinned build, source inventory, semantic guardrails, documentation
skeleton, and narrow module layout needed for fast trustworthy Lean work.

#### Detailed Implementation Plan

- Inspect the complete paper, including both transition-table images, and record
  its formal claims separately from physical/heuristic material.
- Choose and pin compatible Lean/mathlib versions; initialize a `formal/`
  project with narrow modules and a thin public API.
- Create conventions, traceability, and corrections documents with stable item
  identifiers that later stages can update.
- Add a minimal compiling namespace/module and representative build command.
- Record all source ambiguities that affect later statements, especially table
  notation, standard input, space accounting, and exact-count assumptions.

#### Completion Requirements

- `formal/lean-toolchain`, Lake configuration, root module, and initial leaf
  compile with a pinned toolchain/dependency set.
- Full source/table audit is recorded; physical claims are explicitly scoped out.
- Documentation defines initial semantic and resource-accounting decisions or
  flags each unresolved choice for the stage that owns it.
- Focused build, proof-hole scan, and `git diff --check` pass and are recorded in
  `1-GUARDRAILS.md`.

### 2-PARTIAL-SYSTEMS — Determinism, partial inverses, histories, and runs

**Status:** Completed.

#### Big Picture Objective

Prove the model-independent reversible-history theorem for deterministic partial
transition systems.

#### Detailed Implementation Plan

- Define partial steps, finite runs/traces, halting, reachability, injectivity on
  a set, and paired forward/backward steps.
- Define a recorded step whose history record recovers exactly the information
  discarded by the source step.
- Prove single-step inverse laws, multi-step reversal, history length, forward
  halting correspondence, and exact restoration after reversing a trace.
- Separate global reversibility from reversibility restricted to well-formed or
  reachable states.
- Add small executable examples and negative diagnostics showing why a rule ID
  or an injectivity condition is necessary.

#### Completion Requirements

- Focused modules compile without proof holes or new axioms.
- Inverse and run-reversal theorems restore state and empty the complete history.
- Halting/reachability theorem assumptions are directly inspectable.
- Tests cover an irreversible source step and its reversible recorded lift.

### 3-UNCOMPUTE — Reusable compute-copy-uncompute construction

**Status:** Completed.

#### Big Picture Objective

Expose the three-stage pattern independently of Turing-machine details.

#### Detailed Implementation Plan

- Specify output observation and a copy operation with an explicit target
  invariant and partial inverse.
- Prove that copying onto a known blank target is injective on its valid domain;
  prove or exhibit the failure of unrestricted destructive overwrite.
- Compose recorded forward execution, copying, and exact reverse execution.
- Prove preservation of input, copied output, erasure of history/work data, and
  two-way termination correspondence under explicit assumptions.
- Package the construction as a small public API usable by later interpreters,
  circuits, and language semantics.

#### Completion Requirements

- The main compute-copy-uncompute theorem has no Turing-specific premise.
- Exact pre/postconditions and partial inverse laws compile and are tested.
- A diagnostic/no-go result documents destructive copying.
- Axiom audit for the exported theorem is clean apart from Lean/mathlib foundations.

### 4-TURING-CORE — Executable tape and source-machine semantics

**Status:** Completed.

#### Big Picture Objective

Define a manageable Turing-machine model and standard computations precise
enough for Bennett's construction and resource accounting.

#### Detailed Implementation Plan

- Choose and implement the tape representation, moves, read/write order,
  configurations, quintuples, finite machines, source step, and halting.
- Define syntactic determinism and prove semantic uniqueness.
- Define standard strings/configurations, blank surroundings, accepted input,
  output extraction, and standard-source assumptions.
- Define visited cells, used cells, transition count, and output length with
  stated endpoint/head/blank conventions.
- Add executable micro-machines and off-by-one tests.

#### Completion Requirements

- Source execution is executable and its operation order is documented.
- Syntactic determinism implies the intended semantic property.
- Standard input/output and halting are precise and tested.
- Cost definitions cover every later exact-count theorem.

### 5-QUADRUPLES — Reversible syntax, inverses, overlap, and splitting

**Status:** Completed.

#### Big Picture Objective

Formalize Bennett's reversible transition format and replace every “by
inspection” local argument with proofs.

#### Detailed Implementation Plan

- Define per-tape read/write versus shift actions, multi-tape quadruples, and
  their configuration semantics.
- Construct the formal inverse and prove both inverse laws with the correct
  head/write ordering.
- Define and characterize overlapping domains and ranges; prove the finite
  non-overlap criteria used for determinism and reversibility.
- Split each source quintuple through a fresh control state and prove the
  two-step simulation plus freshness/non-overlap obligations.
- Document and correct the paper's ambiguous range-overlap notation if the
  scanned table/prose warrants it.

#### Completion Requirements

- Quadruple inverse and overlap characterizations compile without inspection
  shortcuts.
- Splitting theorem proves exact two-step behavior and names all freshness
  assumptions.
- Machine-level non-overlap yields deterministic semantics and a partial inverse.
- Examples test write/shift noncommutation and inverse order.

### 6-THREE-TAPE — Bennett simulator and central semantic theorem

**Status:** Completed.

#### Big Picture Objective

Construct the concrete three-tape reversible simulator and prove its full
compute-copy-uncompute behavior.

#### Detailed Implementation Plan

- Reconstruct Table 1 as explicit indexed transition syntax with disjoint stage
  states, rule-record alphabet, link transitions, and copy transitions.
- Prove first-stage step and run simulation with one history record per source
  quintuple and the exact lower-level phase relationship.
- Prove the copying loop's standard-format and blank-target invariants.
- Prove stage 3 runs inverse transitions in reverse order, restoring tape 1,
  all relevant heads/control state, and blank history while preserving tape 3.
- Prove domain/range non-overlap across and within all stages.
- State the central theorem with source assumptions, accepted input, all initial
  and final tapes/heads/states, input retention, output, cleanup, two-way halting,
  determinism, and the strongest justified reversibility scope.

#### Completion Requirements

- Central theorem is fully proved for well-formed standard inputs, with no
  hidden “emulates” predicate concealing configuration conditions.
- Both halting directions and malformed-input scope are explicit.
- Constructed machine determinism/reversibility has a proof, including stage
  boundary non-overlap.
- Concrete examples execute end to end.

### 7-RESOURCES — Exact syntax, time, and space accounting

**Status:** Completed.

#### Big Picture Objective

Verify or correct Bennett's exact complexity claims under the formal cost model.

#### Detailed Implementation Plan

- Count states, transition rules, and tape alphabet cardinalities from the
  constructed finite syntax, with collision/freshness assumptions explicit.
- Derive lower-level target trace length from the source trace and output-copy
  loop, auditing every stage-boundary and off-by-one transition.
- Prove per-tape visited/used-cell bounds, distinguishing heads, terminal blanks,
  permanent output, and temporary history/workspace.
- Compare formal formulas to `2f+2N+4`, `4N+2z+3`,
  `4v+4λ+5`, and `(s, v+1, λ+2)` and record every discrepancy.

#### Completion Requirements

- Each reported exact paper count is either a proved theorem or a correction-log
  entry with a proved replacement/precise failed obligation.
- Semantic correctness is not used as a substitute for syntactic counting.
- Tests cover small cardinalities and zero/minimal-length edge cases.
- Cost conventions and consequences are present in public documentation.

### 8-CHECKPOINTS — Segmented history and bounded claims

**Status:** Completed.

#### Big Picture Objective

Treat the later checkpoint argument separately and prove only what a complete
formal construction supports.

#### Detailed Implementation Plan

- Define abstract checkpoints, restart dumps, segmentation, and their time/space
  costs without entangling them with the three-tape theorem.
- Formalize a finite-segment compute-copy-uncompute composition and its cleanup.
- Prove the elementary optimization bound near `n ≈ sqrt (v/s)` with integer
  rounding and explicit dump I/O costs where applicable.
- Classify the paper's `2√(vs)`, ignored-I/O, and nested logarithmic-space
  discussion as exact, conditional, asymptotic, or speculative based on evidence.

#### Completion Requirements

- Any exported checkpoint theorem follows from a defined construction/cost model.
- Integer and nonzero assumptions for optimization are explicit.
- No logarithmic-space theorem is claimed without a full construction and proof.
- Omissions and speculative claims are traceably documented.

### 9-RELEASE-AUDIT — Traceability, examples, API, and final verification

**Status:** In progress.

#### Current Facts

- Stages 1–8 now have kernel-checked proof leaves.  The thin checkpoint API and
  executable audit are integrated; their focused builds and the root `Bennett`
  build pass, and their principal axiom sets contain only standard Lean/mathlib
  foundations.  Stage 9 owns the final full pinned build, consolidated axiom
  report, import/extension guidance, and end-to-end release report.
- Stage 8 intentionally leaves nested checkpointing excluded and leaves
  concrete dump allocation and target-level dump-I/O protocols parameterized;
  these are documented scope boundaries, not proof holes in the exported
  finite checkpoint theorem.

#### Big Picture Objective

Finish the library as an importable, documented, independently auditable result.

#### Detailed Implementation Plan

- Stabilize thin public API modules and module-level documentation.
- Complete the paper-to-Lean traceability matrix and correction log, including
  consequences for dependent theorems.
- Add an import/extension guide and representative executable examples.
- Run full build, proof-hole/forbidden-shortcut scans, `#print axioms` audits,
  whitespace checks, and any evaluator tests.
- Produce the final report required by the objective.

#### Completion Requirements

- Full pinned build succeeds from the documented command.
- Principal theorem signatures and axiom audits are recorded.
- Traceability classifies every important paper item and all physical/heuristic
  exclusions; unresolved claims name exact obligations.
- Documentation explains importing and extending each reusable layer.
- The original objective, rather than a reduced proxy, is either achieved or
  every remaining gap is explicitly carried forward with evidence and next work.
