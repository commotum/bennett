# Formalization Conventions and Scope

This document fixes project-wide boundaries before machine definitions are
written.  A convention marked **selected** constrains later modules.  A choice
marked **owned by Stage N** remains deliberately open until that stage proves it
fits the required semantics.

## Source and Trust Boundary

- **Selected:** the supplied 1973 paper is a mathematical source, not a formal
  specification.  Its prose, equations, and transition tables are independently
  checked.
- **Selected:** the scanned PDF is authoritative when the Markdown conversion
  disagrees with it.  Conversion errors are recorded separately from errors in
  the paper.
- **Selected:** no physical claim follows from logical reversibility alone.
  Sections involving entropy, energy, reaction rates, chemistry, RNA, or
  thermodynamics are documentation-only and excluded from the Lean core.
- **Selected:** “by inspection” is not a proof.  Domain/range non-overlap,
  local inverses, stage boundaries, and resource counts require Lean proofs.

## Transition Systems

- **Selected:** computation is partial.  A configuration may have no successor.
- **Selected:** determinism means at most one successor, while reversibility
  means at most one predecessor.  Neither property implies the other.
- **Selected:** a transition rule may be individually injective while a set of
  rules fails to be reversible because their ranges overlap.
- **Selected:** pairwise domain/range non-overlap is Bennett's syntactic
  unique-rule discipline.  It implies the corresponding semantic properties,
  but is stronger than extensional uniqueness when overlapping rules happen to
  compute the same successor/predecessor.
- **Selected:** global injectivity and injectivity restricted to a well-formed or
  reachable set are separate predicates and may not be substituted silently.
- **Selected and formalized in Stage 2:** executable one-step semantics use
  `PartialStep α := α → Option α`.  Mathlib `PFun`/`Part` remain the
  potentially divergent whole-computation layer through
  `StateTransition.eval`; they are not the runtime one-step representation.
- **Selected and formalized in Stage 2:** `PartialStep.iterate` executes exactly
  `n` successful steps, `Runs` records exact endpoints/count, and `HaltsIn n`
  means `n` successful transitions followed by an undefined next step.  This
  avoids counting the final failed halt query as a machine transition.
- **Selected and formalized in Stage 2:** reflexive-transitive reachability is
  mathlib `StateTransition.Reaches`; exact runs and termination are bridged to
  `StateTransition.eval` in a proof leaf.

## History and Uncomputation

- **Selected:** one abstract history record corresponds to one source transition.
  Lower-level target transitions are counted separately.
- **Selected:** a history entry must carry proved predecessor-recovery data.  A
  bare state snapshot or rule index is accepted only after an inverse law is
  proved for the relevant model.
- **Selected:** an abstract reverse execution theorem restores its entire modeled
  work state, including control, tapes, heads, and history.  In the literal
  Table 1 machine, however, control changes from initial `A₁` to final `C₁`;
  exact restoration therefore applies to tapes/heads and to control only after
  an explicit phase-forgetting `A↔C` projection.  Both concrete states must be
  named in the central theorem.
- **Selected:** compute-copy-uncompute retains the original input unless an
  independently reversible recovery procedure is supplied.
- **Selected and formalized in Stage 2:** `HistoryRecorder` exposes an executable
  `stepWithRecord`, source-forgetting law, recovery function, and both graph
  inverse laws.  It assumes no compactness of records.  Its lifted steps form a
  mathlib `PEquiv`, add exactly one list entry per source step, reject malformed
  records, and reverse any finite generated run exactly.
- **Selected and formalized in Stage 3:** `computeCopyUncompute` is a semantic
  `PEquiv` macro indexed by an externally supplied exact source-step count `n`.
  It performs recorded computation, checks that the endpoint is halted, copies
  an observation onto a blank register, and reverses exactly `n` recorded steps.
  It is not an autonomous phase scheduler or an executable halting search.
- **Selected:** exact bounded reversal preserves an arbitrary initial history
  suffix.  The concrete Stage 6 scheduler instead starts from the exact blank
  history tape at head `-1`; normal-form source syntax makes the reverse-start
  endpoint a genuine halt, so it cannot continue into a pre-existing suffix.

## Segmented Checkpoints

- **Selected and formalized in Stage 8:** a restart checkpoint is a value of a
  caller-chosen complete state type.  For a Turing-machine instantiation this
  must include control, every tape, every head, the execution phase, and any
  other data needed to resume.  An output word or tape contents alone is not a
  sufficient checkpoint unless a separate theorem reconstructs the omitted
  components.
- **Selected and formalized in Stage 8:** `recordedSegmentStage` implements one
  source segment using `HistoryRecorder`.  It loads the permanent checkpoint as
  a fresh `HistoryState` with empty generated history, runs an exact recorded
  iterate, copies the complete terminal checkpoint, reverses the iterate, and
  restores the caller's scratch baseline.  Thus every record generated by the
  segment is erased; the baseline itself is arbitrary and may already contain
  history.
- **Selected and formalized in Stage 8:** `ChainState` separates permanent
  `original`, live `current`, the number of completed segments, and a
  newest-first list of intermediate dumps.  The first segment does not store a
  duplicate input checkpoint because `original` already supplies its
  predecessor.  Each later forward segment pushes its previous `current`;
  backward execution validates the declared segment before removing that dump.
- **Selected and formalized in Stage 8:** the global checkpoint `forward` and
  `backward` partial steps have converse graphs on their complete domains and
  therefore package as a `PEquiv`.  A canonical `n`-segment run has completed
  index `n` and exactly `n-1` intermediate dumps; full reverse cleanup restores
  `ChainState.initial`.
- **Selected and formalized in Stage 8:** `Checkpoint.Plan.segmentSteps` maps a
  list of block lengths to exact iterates of one source step.  A source run whose
  length is the sum of those blocks induces a complete chain with the same
  terminal checkpoint.  This semantic bridge does not assign a physical tape
  encoding or transition cost to a checkpoint dump.
- **Selected and formalized in Stage 8:** checkpoint
  `computeCopyCleanup` is indexed by an externally supplied exact segment
  count, starts with a distinguished blank output register, and has no hidden
  halt guard.  Its endpoint retains the permanent input and copied observation
  while restoring all checkpoint-chain fields and removing every generated
  intermediate dump.

## Copying

- **Selected:** copying classical tape symbols onto a known blank target can be
  reversible on that invariant.  It is not unrestricted cloning, nor does it
  justify copying arbitrary configurations.
- **Selected:** destructive overwrite is not a reversible copy operation.  Copy
  theorems expose blankness/equality invariants in their preconditions.
- **Selected and formalized in Stage 3:** `blankEquiv` has forward domain
  `(value, blank)` and inverse domain `(value, value)`;
  `observedEquiv` retains arbitrary work and copies only an observation.  The
  exact domain/equality laws and destructive-overwrite no-go results are proved.
- **Selected and formalized in Stage 3:** any globally reversible output-only
  realization from a fixed blank ancilla computes an injective function.  Thus a
  noninjective computation must retain the input or equivalent recovery data.
- **Selected and formalized in Stage 6:** the Table 1 copy loop starts with work
  and blank output heads at `-1`, scans the word and its right delimiter in both
  directions, and returns both heads to `-1`.  It works for the empty word and
  takes exactly `4λ+5` target transitions.  Its history actions are identity
  rewrites: no record is appended or erased, but the current terminal record is
  checked throughout the loop.

## Turing-Machine Semantics

- **Selected from equation (1) and formalized in Stages 4–5:** a source
  quintuple reads the current symbol,
  writes its replacement, moves the head left/right/stay, and then changes the
  control state.  `Quintuple.undo` is consequently shift/read/write rather than
  another source quintuple; its validated partial inverse is proved exact.
- **Selected from equation (2) and formalized in Stage 5:** on each tape, a
  target quadruple performs
  exactly one of (a) read and write without moving or (b) move without reading
  or writing.  `Action` makes a read-plus-move or move-plus-write action
  unrepresentable.
- **Selected and formalized in Stage 5:** target configurations are
  heterogeneous: a tape index `i` selects both its tape and its nonblank symbol
  type `Symbol i`.  This is required for the concrete work/history/output
  alphabets `(z,N+1,z)`; a homogeneous multi-tape carrier would lose that claim.
- **Selected and formalized in Stage 5:** a rule's semantic domain/range overlap
  is defined by a common complete configuration, then characterized by the
  finite tape-wise `DomainCompatible`/`RangeCompatible` tests.  A move imposes
  no symbol restriction; two rewrites must agree on scanned symbols for domain
  overlap and written symbols for range overlap.
- **Selected and formalized in Stage 5:** `Quadruple.inverse` swaps controls,
  exchanges scanned/written symbols, and reverses moves.  It has the exact
  converse successful graph on complete controls, tape contents, and heads.
- **Selected:** the tape is two-way infinite, matching the paper's unbounded
  tape diagrams and avoiding a left-boundary convention absent from the source.
- **Selected and formalized in Stage 4:** a tape has absolute `Int` head
  position and canonical finite-support cells
  `Int →₀ TapeSymbol Symbol`.  `TapeSymbol` adjoins exactly one blank to a
  generic type of nonblank symbols.  A custom update is used because the pinned
  mathlib's general `Finsupp.update` is noncomputable.
- **Selected and formalized in Stage 4:** source programs have an intrinsic
  `ruleCount` and table `Fin ruleCount → Quintuple`; control and nonblank-symbol
  types remain generic, with decidable equality required only for execution and
  `Fintype` required only by later cardinality results.
- **Selected:** a standard nonempty word occupies consecutive nonblank cells and
  is surrounded by blanks; its head scans the blank immediately to its left.
- **Selected and formalized in Stage 4:** base standard words are `List Symbol`
  and therefore blank-free by type.  Empty words are admitted by the data model;
  `NonemptyWord` is a separate predicate.  Each later theorem must cover `[]` or
  expose nonemptiness in its signature.
- **Selected:** malformed inputs are outside the central standard-input theorem.
  Behavior on them remains defined where the machine syntax permits, but no
  standard simulation claim is inferred.
- **Selected and formalized in Stage 4:** `Standard.Behavior.accepts` is an
  explicit predicate on standard words.  `BennettNormalForm` states entry/exit
  rule uniqueness, no incoming rule to start, and no outgoing rule from finish
  directionally rather than using “appears nowhere else.”

## Bennett Stage and State Conventions

- **Selected and formalized in Stage 6:** source rules have intrinsic zero-based
  IDs `Fin N`; normal form distinguishes `entryId` and `exitId` without imposing
  a semantically irrelevant table ordering.  The paper's printed labels
  `1,…,N` are presentation names only.  History symbols store these intrinsic
  IDs, so no theorem depends on the exit rule literally being the last element
  of an enumeration.
- **Selected and formalized in Stage 5:** every split source rule receives its
  own fresh connector state.  `SplitState Control RuleId = Control ⊕ RuleId`
  makes connector/original disjointness and connector injectivity structural.
- **Selected and formalized in Stage 5:** pure two-rule splitting is
  domain-disjoint under source key injectivity, but is range-disjoint exactly
  when the source rule-target map is injective.  Ordinary irreversible sources
  need not satisfy this; Bennett's Stage 6 history-symbol write is the mechanism
  that will distinguish the lower-half ranges.
- **Selected and formalized in Stage 6:** forward (`A`), copy (`B`), and reverse
  (`C`) state families are disjoint constructors.  The concrete carrier has
  forward and reverse copies of every source control and connector plus four
  copy controls, giving exactly `2f+2N+4` states.
- **Selected and formalized in Stage 6:** the third stage uses the inverse
  actions in reverse trace order; replacing `A` labels by `C` labels is only the
  syntactic control-state part of that construction.  The proved schedule pops
  exactly the rule IDs written by the forward schedule and restores work tape,
  work/history heads, and the blank history tape while leaving output unchanged.
- **Selected:** the fact that each stage is reversible does not alone make their
  union reversible.  Phase tags and cross-stage domain/range disjointness are
  explicit proof obligations.
- **Selected and formalized in Stage 3 at the macro level:** sequential
  `PEquiv.trans` composition is itself a partial equivalence.  This proves
  injectivity of the entry-to-exit semantic macro, not determinism or
  reversibility of a union of concrete one-step phase rules.
- **Selected and formalized in Stage 6:** the complete Table 1 rule family has
  globally disjoint domains and ranges on every syntactic configuration, not
  merely on standard reachable configurations.  The reusable proof assumes
  source key injectivity and that no source rule has key `(finish, blank)`;
  `BennettNormalForm` supplies both.  Separate counterexamples show these
  assumptions are sharp for the relevant boundary overlaps.

## Halting and Observable Results

- **Selected:** halting means the partial machine step is undefined.  A standard
  source-machine assumption ensures any halting standard run ends in `A_f`.
- **Selected:** the central theorem proves both halting directions on accepted
  standard inputs; a one-way terminating-run simulation is not sufficient.
- **Selected:** initial and final configurations specify every tape, head, and
  control state.  The informal judgment `R : (I;B;B) → (I;B;P)` is only a
  documented abbreviation after this stronger result exists.
- **Selected and formalized in Stage 3:** for fixed `n` and a blank target, the
  semantic macro succeeds iff the source `HaltsIn n`; existence of some
  successful `n` is equivalent to `Terminates`.  This existential theorem is a
  logical equivalence, not a decision procedure for termination.

## Resource Accounting

- **Selected:** keep distinct (1) control states, (2) syntactic rules,
  (3) alphabet cardinalities, (4) target transitions, (5) distinct visited
  cells, (6) simultaneously nonblank/allocated cells, (7) permanent output, and
  (8) temporary workspace.
- **Selected:** a source step is one quintuple execution.  A target step is one
  quadruple execution.  Splitting one source step therefore costs two target
  steps in the forward phase and two more in retracing.
- **Selected and formalized in Stage 5:** the pure split of an `N`-rule source
  contains exactly `2N` quadruples and adds exactly `N` connector controls, so
  its control cardinality is `f+N` when the source control type has cardinality
  `f`.  These are component counts, not the full Table 1 counts.
- **Selected and formalized in Stage 6:** the full constructed syntax has
  exactly `2f+2N+4` controls and `4N+2z+3` rules, where `z` counts source
  nonblank symbols plus blank.  Its three full tape alphabets have cardinalities
  `(z,N+1,z)`.  These are constructor-cardinality theorems, independent of the
  semantic simulation proof.
- **Selected:** exact counts require finite, pairwise-disjoint constructors and
  explicit cardinality/freshness assumptions; semantic equivalence proves no
  numerical count by itself.
- **Selected:** the claimed history alphabet cardinality `N+1` treats each of
  the `N` rule identifiers as one atomic symbol disjoint from blank.  A fixed
  alphabet encoding would change history space, transition counts, and time.
- **Selected and formalized in Stage 4:** a nonempty `ExecutionTrace` contains
  both endpoints and counts only successful transitions.  Tape resource APIs
  distinguish head-visited positions, ever-nonblank positions, their union
  footprint, peak nonblank cells, and peak active cells (support plus head).
- **Selected and formalized in Stage 4:** `Tape.blank` means a blank tape with
  head at `0`, whereas `Tape.ofWord []` is blank with head at `-1`.  “Blank tape”
  in central theorem signatures must always include its head convention.
- **Selected and formalized in Stage 7:** `visitedPositions` is the finite set
  of positions scanned by a head, `everNonblankPositions` is the union of tape
  supports over all trace states, and `footprintPositions` is their union.
  `maximumNonblankCells` and `maximumActiveCells` are separate per-state maxima;
  active positions are the current support with the current head inserted.
- **Selected and formalized in Stage 7:** the copy trace on both work and output
  visits and footprints exactly `Icc (-1) λ`, of cardinality `λ+2`, while its
  ever-nonblank set is `Ico 0 λ`.  Its maximum nonblank and active counts are
  `λ` and `λ+1`; for `λ=0` these are `0` and `1` although the two delimiter
  cells remain in the footprint.  The history head stays on one cell during
  copying.
- **Selected and formalized in Stage 7:** the canonical physical history trace
  for `v` source steps visits and footprints `Icc (-1) (v-1)`, of cardinality
  `v+1`; its ever-nonblank set is `Ico 0 v` and its maximum nonblank count is
  `v`.  Thus the paper's `v+1` is a footprint count, not a simultaneous
  nonblank count.
- **Selected and formalized in Stage 7:** for a standard complete target trace,
  raw work-head visits equal raw source-head visits union `Icc (-1) λ`, while
  target ever-nonblank work positions equal the source trace's ever-nonblank
  positions.  Consequently the target work footprint is source footprint union
  `Icc (-1) λ`.  The initial and final standard endpoints already place the
  left delimiter and all output data cells in the source footprint, so this
  union is exactly insertion of the right delimiter `λ`.
- **Selected correction to the paper's `s`:** if `s` denotes source-footprint
  cardinality, complete target work-footprint cardinality is `s` when the right
  delimiter `λ` already belongs to the source footprint and `s+1` otherwise.
  No unconditional equality is reported because the paper never defines `s`.
  This statement concerns footprint, not the smaller raw head-visited set.
- **Selected:** asymptotic claims and exact equalities are separate results.
  Ignored dump-I/O time is an explicit assumption, never silently omitted.
- **Selected:** Stage 3 proves exact component facts—`n` recorded forward steps,
  one successful blank-target copy, `n` backward steps, and history growth by
  `n`—but assigns no target-machine transition count to their `PEquiv`
  composition.  Concrete scheduler and Table 1 costs belong to Stages 6–7.
- **Selected and formalized in Stage 6:** a standard source run of `v` steps
  producing a word of length `λ` induces a concrete Table 1 run of exactly
  `4v+4λ+5` quadruple transitions: `2v` forward, `4λ+5` copy, and `2v`
  reverse.  Stage 7 derives the resource formulas above from explicit
  constructor-tag schedules and physical tape geometry, not from this semantic
  run theorem.
- **Selected:** permanent output, temporary history, source work, and endpoint
  delimiters are reported separately.  In particular, a standard copied output
  has `λ` permanent nonblank symbols but its copy footprint has `λ+2` cells;
  a history peak has `v` nonblank records but its footprint has `v+1` cells.
  Whole-run maximum-active formulas are not silently substituted for these
  proved footprint/nonblank quantities.
- **Selected and formalized in Stage 8:** for `v` source steps, `n` declared
  segments, and `s` cells per complete restart dump, the discrete temporary
  checkpoint budget is `v ⌈/⌉ n + (n-1)*s`.  It combines the largest
  reusable primary-history block with intermediate dumps and excludes
  permanent input/output, ordinary live machine state, and unmodeled allocator
  overhead.
- **Selected and formalized in Stage 8:** `Cost.SegmentPlan` constructively
  partitions `v` into exactly `n` blocks bounded by `v ⌈/⌉ n` when
  `n > 0`; zero-length blocks are permitted when there are more segments than
  steps.  The stronger positive-block construction additionally assumes
  `n ≤ v`.
- **Selected and formalized in Stage 8:** under the paper's rounded convention
  `v ⌈/⌉ n + n*s`, a positive segment count charges exactly one full dump
  more than the library's `n-1`-dump budget.  Neither expression is called
  total space.
- **Selected and formalized in Stage 8:** ideal segmented cleanup costs four
  source-level passes.  `checkpointTime` adds
  `(n-1)*s*transitionsPerDumpCell`; exact doubling of the unsegmented two-pass
  baseline follows only when this dump-I/O parameter is set to zero.  Concrete
  dump placement, serialization, and target-machine I/O schedules remain
  caller-supplied.
- **Selected and formalized in Stage 8:** `balancedSegments` is a positive
  ceiling-square-root choice with proved near-balanced upper bounds.  It is not
  claimed to be the exact minimizer of the ceiling-rounded discrete objective.
  Separately, `paperContinuousCells_lower_bound` proves the real AM--GM lower
  bound for positive segment count and nonnegative `v,s`, while
  `paperContinuousCells_at_sqrt_ratio` proves equality for positive `v,s`.
- **Selected after Stage 8:** no nested logarithmic-space or quadratic-time
  theorem is exported.  Bennett supplies no recursive schedule, restart
  invariant, allocation model, or complete resource proof for that speculative
  paragraph.

## Build and Axiom Policy

- Lean is pinned to `leanprover/lean4:v4.31.0`.
- Mathlib is pinned to commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- Internal modules import narrow dependencies.  `Bennett.lean` is a thin public
  re-export and is not imported by internal leaves.
- Completed modules contain no `sorry`, `admit`, or project-specific axiom.
  Principal exported theorems receive recorded `#print axioms` audits.
