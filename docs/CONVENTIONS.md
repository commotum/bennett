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
  suffix.  A future autonomous scheduler instead needs an empty/bounded history,
  a baseline marker, or an independently proved backward-halting boundary so it
  does not continue into that suffix.

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
- **Owned by Stages 4 and 6:** the exact standard-tape copy loop and its head
  positions before and after copying.

## Turing-Machine Semantics

- **Selected from equation (1):** a source quintuple reads the current symbol,
  writes its replacement, moves the head left/right/stay, and then changes the
  control state.  The order matters for inversion.
- **Selected from equation (2):** on each tape, a target quadruple performs
  exactly one of (a) read and write without moving or (b) move without reading
  or writing.
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

- **Selected:** source rules are indexed `1,…,N`, with the required entry rule at
  index `1` and exit rule at index `N`.
- **Selected:** every split source rule receives its own fresh connector state.
- **Selected:** forward (`A`), copy (`B`), and reverse (`C`) state families are
  represented with constructors or disjoint sums, not informal name freshness.
- **Selected:** the third stage uses the inverse actions in reverse trace order;
  replacing `A` labels by `C` labels is only the syntactic control-state part of
  that construction.
- **Selected:** the fact that each stage is reversible does not alone make their
  union reversible.  Phase tags and cross-stage domain/range disjointness are
  explicit proof obligations.
- **Selected and formalized in Stage 3 at the macro level:** sequential
  `PEquiv.trans` composition is itself a partial equivalence.  This proves
  injectivity of the entry-to-exit semantic macro, not determinism or
  reversibility of a union of concrete one-step phase rules.
- **Owned by Stage 6:** whether the final concrete theorem proves global
  non-overlap on every syntactic configuration or a weaker reachable invariant.
  The paper intends global rule-domain/range non-overlap, so that is the target.

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
- **Owned by Stage 7:** whether tape 1's paper parameter `s` counts the initial
  head-scanned blank, and exact endpoint-blank conventions for all three tapes.
  The paper explicitly reports `v+1` and `λ+2` on tapes 2 and 3, strongly
  suggesting visited cells including endpoint blanks, but does not define `s`.
- **Selected:** asymptotic claims and exact equalities are separate results.
  Ignored dump-I/O time is an explicit assumption, never silently omitted.
- **Selected:** Stage 3 proves exact component facts—`n` recorded forward steps,
  one successful blank-target copy, `n` backward steps, and history growth by
  `n`—but assigns no target-machine transition count to their `PEquiv`
  composition.  Concrete scheduler and Table 1 costs belong to Stages 6–7.

## Build and Axiom Policy

- Lean is pinned to `leanprover/lean4:v4.31.0`.
- Mathlib is pinned to commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- Internal modules import narrow dependencies.  `Bennett.lean` is a thin public
  re-export and is not imported by internal leaves.
- Completed modules contain no `sorry`, `admit`, or project-specific axiom.
  Principal exported theorems receive recorded `#print axioms` audits.
