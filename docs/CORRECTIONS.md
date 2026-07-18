# Corrections, Ambiguities, and Failed Obligations

This is a cumulative log.  Each entry records a source issue and the disposition
of its dependent Lean results.  An **unresolved** obligation has not been proved
and may not be used silently as though its proposed repair were available.

## C-001 — Range-overlap transcription is ill-typed

- **Location:** journal p. 527, quadruple property 3; Markdown line 94.
- **Original/transcribed claim:** ranges overlap when, on each tape,
  `t'_k = /` or `u'_k = /` or `t'_k = u'_k`.
- **Issue:** by the preceding quadruple definition an output field `t'_k` is a
  written symbol or a shift in `{- ,0,+}`; it is never `/`.  The scanned paper
  uses the unprimed read fields for the slash cases; the Markdown conversion
  introduced primes on those two occurrences.
- **Corrected formulation:** final states agree and, for each tape, either rule
  is a shift action (equivalently its unprimed read field is `/`) or both are
  read/write actions writing the same symbol.
- **Justification:** a shift action is a bijection on tape/head states and has
  unrestricted range; a write-without-move action restricts the scanned final
  symbol to the value it wrote.
- **Consequences:** Stage 5 uses the typed constructors `Action.rewrite` and
  `Action.move`, making the invalid expression unrepresentable.
- **Status:** Corrected and formalized in Stage 5.  The semantic-first theorem
  `Quadruple.rangesOverlap_iff_rangeCompatible` proves the repaired iff;
  `domainsOverlap_iff_domainCompatible` proves the analogous domain formula.
  This remains classified as a Markdown conversion error, not an error in the
  scanned paper.

## C-002 — “Appear in no other quintuple” needs directional precision

- **Location:** journal p. 527, standard-machine requirement 3; lines 104–116.
- **Original claim:** `A₁` and `A_f` “appear in no other quintuple,” making the
  special rules first and last on a terminating standard run.
- **Issue:** “appear” could mean as source, target, or either; exact count and
  stage-link proofs need the intended no-incoming/no-outgoing facts.  Small `f`
  can also identify `A₂` with `A_{f-1}` unless state distinctness is stated.
- **Corrected formulation:** require a distinguished entry state with no incoming
  source rule except no occurrence as a target, a distinguished halt state with
  no outgoing source rule, the two displayed rules, and the state distinctions
  actually used by the construction.  State the stronger source-syntax
  restriction separately if exact fidelity requires it.
- **Justification:** these are the facts used to prove first/last execution and
  cross-stage domain/range non-overlap.
- **Consequences:** `BennettNormalForm` exposes directional source assumptions;
  disjoint simulator-control constructors make the target state count
  unconditional once the finite source cardinalities are fixed.
- **Status:** The directional assumptions are formalized in Stage 4 as
  `Standard.BennettNormalForm` (`entry_only_rule_from_start`,
  `no_rule_targets_start`, `exit_only_rule_to_finish`, and
  `no_rule_sources_finish`).  Stage 6 uses them in the exact endpoint and global
  non-overlap proofs.  Its reusable boundary theorem needs only the weaker
  `NoFinishBlankRule`; normal form supplies that condition.

## C-003 — Empty standard strings are unspecified

- **Location:** journal p. 527, standard format and theorem; lines 98, 128.
- **Original claim:** strings contain no embedded blanks and have a blank
  immediately to their left.
- **Issue:** this does not say whether the empty string is legal.  Table 1's copy
  loop can traverse a zero-length word, but output length and `λ+2` visited-cell
  accounting must be checked separately for that case.
- **Corrected formulation:** define standard words parametrically, then either
  prove the construction for empty and nonempty words or state nonemptiness as
  an explicit theorem assumption.
- **Justification:** avoids silently deriving a domain restriction from a diagram.
- **Consequences:** executable edge cases and the exact copy trace formula belong
  in Stages 4, 6, and 7.
- **Status:** Stage 4's canonical model admits `[]`, represents it as an all-blank
  tape with head at the left delimiter `-1`, and proves its potential complete
  delimiter traversal has two cells (`λ+2 = 2`).  Stage 6's concrete
  `Copy.scheduled_encode` covers `[]` without an extra assumption and proves the
  five-transition endpoint; the general schedule has length `4λ+5`.  Stage 7's
  `Copy.Resource.copyTrace_empty_data_cost` proves that the empty copy trace has
  empty ever-nonblank support, two-cell work/output footprints `Icc (-1) 0`,
  peak nonblank count zero, and peak active count one.

## C-004 — “About twice” conflicts with the target step unit

- **Location:** journal p. 525 introduction, line 30; main cost theorem p. 527,
  lines 148–152.
- **Original claims:** reversible computations take “about twice” as many steps;
  the concrete target takes `4v + 4λ + 5` steps.
- **Issue:** with the paper's later convention that a target quadruple is one
  machine transition and a source quintuple is one source transition, compute
  and retrace each cost `2v`, so the leading overhead is four, not two.
- **Corrected formulation:** report exact costs with named step units.  “Twice” is
  defensible only at the higher level where a split transition pair counts as
  one simulated operation, or relative to an already history-recording forward
  computation.
- **Justification:** direct enumeration of the two forward and two inverse
  quadruples per source step.
- **Consequences:** documentation does not use an unqualified factor-two claim.
  Space accounting remains independent of this transition-count result.
- **Status:** Corrected and formalized in Stage 6.
  `Simulator.scheduled_of_computesIn` and `runs_of_computesIn` prove the exact
  `4v+4λ+5` schedule/run length as `2v + (4λ+5) + 2v` target transitions.

## C-005 — “Uses squares” does not define one uniform space measure

- **Location:** journal p. 527 theorem, lines 148–154; Table 1.
- **Original claim:** the three tapes use `s`, `v+1`, and `λ+2` squares.
- **Issue:** the paper does not define whether “uses” means visited cells,
  nonblank cells, span, or simultaneous allocation.  `v+1` counts `v` history
  records plus an endpoint/initial cell, and `λ+2` evidently counts both
  bounding blanks; it is unclear whether the source parameter `s` follows the
  same endpoint convention.  Under ordinary distinct-scanned-cell accounting,
  the copy sweep scans the blank immediately right of the output even when the
  source computation never scanned it, so tape 1 can use `s+1` cells.
- **Corrected formulation:** prove separate head-visited, ever-nonblank,
  footprint, maximum-nonblank, and maximum-active statements with head/endpoint
  conventions explicit.  For a standard computation with final output length
  `λ`, the complete target work footprint is the source footprint union
  `Icc (-1) λ`.  Standard endpoints already put the left delimiter and every
  output data cell in the source footprint, so the union equals insertion of
  the right delimiter `λ`.  If `s` is the source-footprint cardinality, the
  exact result is `s` when `λ` was already present and `s+1` otherwise.
- **Justification:** the measures differ on blank cells even for Table 1's trace.
- **Consequences:** no exact space theorem is inferred from semantic simulation.
  The paper's `v+1` and `λ+2` are interpreted as footprint/visited counts,
  whereas peak nonblank history and copied-data counts are `v` and `λ`.
  Permanent output, temporary history, and work footprint remain separate.
- **Status:** Corrected and formalized in Stage 7.  Stage 4 defines
  `visitedPositions`, `everNonblankPositions`, `footprintPositions`,
  `maximumNonblankCells`, and `maximumActiveCells`.
  `Copy.Resource.copyTrace_work_footprintPositions_eq_Icc` and its output
  analogue prove `Icc (-1) λ` with cardinality `λ+2`; the copy
  maximum-nonblank and maximum-active theorems prove `λ` and `λ+1`.
  `HistorySpace.concreteTrace_history_cost` proves history footprint cardinality
  `v+1`, ever-nonblank cells `Ico 0 v`, and peak nonblank count `v`.
  `Resource.fullTrace_work_visitedPositions` gives raw source head visits union
  `Icc (-1) λ`, while
  `Resource.WorkSupport.fullTrace_work_everNonblankPositions` proves no new
  nonblank work position.  Its footprint-union, insert-right, and two cardinality
  theorems prove the exact `s`/`s+1` dichotomy above.

## C-006 — Table 2 erasure is conditional inverse copying

- **Location:** journal p. 529, Table 2 stage 6 and lines 211–217.
- **Original claim:** “reversible erasure of extra copy of input.”
- **Issue:** unrestricted erasure is noninjective.  The step is reversible only
  on the invariant that tapes 1 and 3 contain equal standard strings produced by
  a prior copy/recovery computation.
- **Corrected formulation:** stage 6 is the inverse of blank-target copying,
  restricted to equal source/target data and the exact copy-loop head format.
- **Justification:** the retained copy uniquely determines each symbol removed
  from the duplicate; without equality it does not.
- **Consequences:** any Table 2 theorem depends on Stage 3's copy partial inverse
  and on `S₂` computing the original input from the output.
- **Status:** The abstract blank-copy/equality-checked inverse is formalized in
  Stage 3 (`Copy.blankEquiv` and `observedEquiv`).  Stage 6 proves the concrete
  standard-tape loop and exact head invariant.  The result is partial: the full
  seven-stage Table 2 composition is unresolved because it additionally
  requires specified forward and inverse realizations of both `S₁` and the
  recovery machine `S₂`, plus a composed proof of all intermediate tape/head
  invariants.

## C-007 — Segmented optimum is continuous and omits costs

- **Location:** journal p. 527 line 154 and p. 530 lines 221–241.
- **Original claim:** choosing `n = √(v/s)` gives temporary storage
  `2√(vs)` (earlier “less than” that amount) and buys the reduction for twice
  the time, ignoring restart-dump I/O.
- **Issue:** segment count is a positive integer; `v` may not divide evenly;
  dumps may number `n-1` rather than `n`; segment lengths may differ; and dump
  read/write time is explicitly omitted.  A restart dump must encode tape,
  control, head, and phase, not merely `s` tape symbols.  The optimized expression
  concerns temporary history-plus-dump storage, while the theorem preview calls
  it total space; permanent input/output and working space are additional.  The
  earlier strict inequality and later equality cannot both describe the same
  unrounded expression uniformly.
- **Corrected formulation:** a complete checkpoint includes every control,
  tape, head, and phase component required to restart.  For `v` steps split
  into a positive integer `n` of segments and a declared `s` cells per complete
  checkpoint, the verified discrete temporary budget is
  `v ⌈/⌉ n + (n-1)s`.  The paper-rounded convention
  `v ⌈/⌉ n + ns` is exactly one `s`-cell dump higher.  Ideal checkpoint
  cleanup takes four source-level passes; dump I/O is an explicit additive
  parameter.  The ceiling-square-root segment choice has a proved
  near-balanced bound but is not asserted to be the exact minimizer of the
  rounded discrete objective.  The positive-real `2√(vs)` AM--GM theorem and
  equality case are stated separately.
- **Justification:** `Checkpoint.Plan` constructs the semantic segmentation
  from exact source iterates and proves `n-1` higher-level dumps.
  `Cost.SegmentPlan` constructs integer block lengths with maximum
  `v ⌈/⌉ n`; `temporaryCells_eq` and
  `paperRoundedCells_eq_temporaryCells_add_dumpCells` prove the two storage
  formulas.  `checkpointTime_eq_two_unsegmented_add_dumpIO` exposes the omitted
  traffic.  `temporaryCells_balanced_le` proves the rounded bound, while
  `paperContinuousCells_lower_bound` and
  `paperContinuousCells_at_sqrt_ratio` prove the separate real relaxation.
- **Consequences:** the formal result measures temporary primary history plus
  intermediate dumps, not total machine space.  Permanent input/output,
  ordinary live work, concrete dump allocation, and a target-level dump-I/O
  protocol remain separate or caller-parameterized.  No semantic theorem is
  used to infer those physical costs.  The nested `log v`/quadratic-time
  sentence still lacks a recursive schedule and remains speculative/excluded.
- **Status:** Corrected, split, and formalized in Stage 8.
  `recordedSegmentStage_apply_of_run` proves local generated-history cleanup;
  `Plan.exists_completes_segmentPlan_with_dump_count` and
  `Plan.computeCopyCleanup_segmentPlan_apply_of_run` prove the plan-driven
  higher-level semantics; `Checkpoint.Cost` proves the discrete and continuous
  cost statements above.

## C-008 — Rule-level and semantic reversibility must be related, not identified

- **Location:** journal pp. 526–528, lines 49, 96, 205.
- **Original claim:** a machine is reversible iff its rule ranges do not overlap.
- **Issue:** the statement moves between a syntactic finite rule set, the union
  transition relation, and standard reachable computations.  Pairwise
  non-overlap is not necessary for extensional semantic uniqueness when two
  applicable rules agree.  For example, on one tape
  `A[/]→[0]B` and `A[x]→[x]B` overlap when `x` is scanned but produce the
  same successor there; their union remains a partial function and injection.
  Restricted reachability can also be reversible despite unreachable syntactic
  range overlaps.
- **Corrected formulation:** define global semantic predecessor uniqueness,
  set-restricted predecessor uniqueness, and syntactic pairwise range
  disjointness separately.  Prove syntactic non-overlap as a sufficient
  unique-rule discipline, not an unconditional extensional iff.  A converse
  requires rule-separation assumptions or a definition of determinism as unique
  applicable rule rather than unique successor.
- **Justification:** this preserves the paper's intended global construction
  while making later reachable-input theorems honest.
- **Consequences:** Stages 2 and 5 own distinct APIs; Stage 6 reports both global
  constructed-machine properties and standard-run correctness where proved.
- **Status:** Corrected and split across Stages 2 and 5.  Stage 5 defines
  `QuadrupleMachine.DomainsDisjoint`/`RangesDisjoint`, proves relational
  right/left uniqueness, proves `RangesDisjoint.step_reversible`, and proves
  that both conditions make the pointwise inverse table an exact partial
  inverse.  `Quadruple.Audit` also kernel-checks an overlapping two-rule table
  whose union relation is nevertheless right- and left-unique, demonstrating
  why the converse is not unconditional.  Stage 6 proves the stronger global
  syntactic discipline for the complete concrete Table 1 rule family.

## C-009 — Table 1 does not restore the literal whole-machine state

- **Location:** abstract and journal p. 526 cleanup prose; Table 1 pp. 528–529.
- **Original claim:** retracing restores the machine to its original condition,
  apart from the copied output tape.
- **Issue:** the paper itself defines a whole-machine state to include control.
  Table 1 begins in `A₁` and terminates in the distinct state `C₁`.  Its tapes
  and heads are restored as claimed, but the literal full configurations differ.
- **Corrected formulation:** the concrete theorem names `A₁` initially and
  `C₁` finally and proves exact tape/head/history cleanup.  A separate
  phase-forgetting projection maps the `A` and `C` copies to one logical source
  control state and is restored exactly.  The abstract history theorem may use
  a single control carrier and prove literal restoration.
- **Justification:** direct reading of Table 1 and its caption.
- **Consequences:** the central theorem cannot assert raw initial/final
  configuration equality; control-phase renaming remains observable in the
  syntactic machine and in exact state counts.
- **Status:** Corrected and formalized.  Stage 2's abstract
  `HistoryRecorder.trace_cleanup` proves literal restoration on a single state
  carrier.  Stage 6 names the distinct physical controls in
  `SimulationCertificate.initialControl`/`finalControl` and proves the exact
  phase-forgetting equality as `Simulator.logicalControl_restored` (also a
  field of the central certificate).

## C-010 — Reversible stages do not automatically form a reversible union

- **Location:** journal p. 526, line 32; Table 1 non-overlap argument p. 529.
- **Original claim:** the complete computation is reversible and deterministic
  because each of its stages is.
- **Issue:** unions/compositions of individually reversible partial rule families
  can acquire overlapping domains or ranges at their junctions.
- **Corrected formulation:** sequential stages may be composed as a semantic
  partial equivalence.  A concrete one-step machine instead needs a scheduler
  plus explicit cross-stage domain/range separation; broad phase labels alone
  do not prove it.  The Table 1 proof must check the `A_f→B` and `B→C_f`
  bridges against every stage family.
- **Justification:** injectivity is not preserved by an unqualified union of
  partial injections.
- **Consequences:** Stage 3's fixed-`n` macro proves an injective entry-to-exit
  relation but deliberately makes no statement about a union of one-step phase
  rules or its transition count.  Stage 6 proves boundary separation rather
  than citing macro composition or per-stage reversibility alone.
- **Status:** Sequential semantic composition is formalized in Stage 3 as
  `Uncompute.computeCopyUncompute` with global macro reversibility.  Autonomous
  scheduling is formalized in Stage 6 by the finite Table 1 machine.
  `rules_domains_disjoint` and `rules_ranges_disjoint` prove every within- and
  cross-family case; `machineWithEnumeration_syntacticallyReversible` transports
  them to executable machine syntax.

## C-011 — Extensional “only if” inverse tests need nondegeneracy

- **Location:** journal p. 527, quadruple property 1 after equations (5)–(6).
- **Original claim:** the displayed syntactic swap/negation conditions hold iff
  two quadruples define inverse partial maps.
- **Issue:** the construction is uniformly sufficient, but an extensional
  necessity claim can have degenerate exceptions.  On a singleton alphabet, for
  example, read/write identity and null shift can be extensionally indistinguishable
  on tape data despite different syntax.  A one-sided tape boundary would also
  change shift domains/ranges.
- **Corrected formulation:** use two-way-infinite tapes and prove the typed
  syntactic inverse construction unconditionally.  State a characterization iff
  only after adding the tape/alphabet richness and rule-observability assumptions
  needed for necessity.
- **Justification:** equality of partial maps need not imply equality of their
  syntax without a separating configuration universe.
- **Consequences:** Stage 5 prioritizes constructive inverse laws; no unqualified
  necessity theorem is required by the simulator.
- **Status:** Corrected constructive result formalized in Stage 5.
  `Quadruple.step_areInverses` proves the syntactically constructed inverse has
  exactly the converse successful graph on the chosen two-way tapes.  The
  extensional-to-syntactic necessity direction is intentionally not exported
  without rule-observability/nondegeneracy assumptions.

## C-012 — Fresh split states prevent indeterminacy, not source irreversibility

- **Location:** journal p. 527, equations (3)–(4) and line 74; Table 1 compute
  stage lines 189–201.
- **Original claim:** a different connector state must be used for each split
  quintuple “to avoid introducing indeterminacy.”
- **Issue:** the sentence is correct about domains, but connector freshness does
  not separate the ranges of the second (move) halves.  If two source rules
  have the same target control, their move halves have overlapping ranges.
- **Corrected formulation:** source key injectivity plus fresh connectors makes
  the pure split table domain-disjoint.  Its ranges are pairwise disjoint if and
  only if the map from source rule IDs to target controls is injective.  The
  later history-record write, not splitting alone, removes this obstruction for
  a general irreversible source.
- **Justification:** `SourceSplit.moveHalf_rangesOverlap_iff_target_eq` gives an
  explicit semantic overlap iff, and
  `Machine.splitRule_ranges_disjoint_iff_target_injective` lifts it to the full
  tagged rule family.
- **Consequences:** Stage 6 keeps the history write in the move half and uses
  its rule-ID symbol to prove range disjointness.  Omitting it would invalidate
  global reversibility whenever source rules merge into one control state.
- **Status:** Clarified and fully formalized across Stages 5–6.  Stage 6's
  `forwardRecordRule` writes the intrinsic rule ID, `reverseEraseRule` checks and
  erases it, and the global range-disjointness proof uses those distinct history
  outputs.  `duplicate_key_causes_restore_range_overlap` records the separate
  obstruction when source keys themselves are duplicated.

## C-013 — Printed rule numbers are labels, not semantic order

- **Location:** journal pp. 527–529, standard-machine prose and Table 1.
- **Original claim/convention:** source quintuples are numbered `1,…,N`, with
  the entry and exit rules displayed as `1` and `N`; those numbers are then
  written on the history tape.
- **Issue:** a finite rule table has no mathematically canonical ordering, and
  Lean's intrinsic `Fin N` indices are zero-based.  Requiring the entry/exit
  rules to occupy literal first/last enumeration positions would add an
  irrelevant representation assumption to a semantic theorem.
- **Corrected formulation:** normal form supplies distinguished `entryId` and
  `exitId`.  History stores intrinsic rule IDs, while any equivalence used to
  enumerate the target table is semantically opaque.
- **Justification:** recovery requires a unique rule identifier, not an ordinal
  relation between identifiers.
- **Consequences:** the history alphabet still has exactly `N+1` full symbols;
  all counts and schedules are unchanged.  Documentation renders the paper's
  `1`/`N` only as presentation names.
- **Status:** Corrected and formalized in Stages 4 and 6.

## C-014 — “No history writing” still performs checked identity rewrites

- **Location:** journal p. 528, Table 1 copy stage.
- **Original claim/prose:** the copying stage operates without adding to the
  history.
- **Issue:** in the quadruple formalism, copy rows display the terminal history
  symbol on both sides.  They do not append a record, but they do read and
  rewrite that cell identically; treating history as an unrestricted no-op
  would enlarge rule domains and invalidate boundary non-overlap.
- **Corrected formulation:** every copy rule checks the terminal history record
  and applies an identity rewrite at the unchanged head position.
- **Justification:** this is the literal Table 1 action and is used by the
  finite domain/range compatibility proofs.
- **Consequences:** the history tape is extensionally unchanged during copying,
  while the copy phase remains enabled only at the validated forward endpoint.
- **Status:** Clarified and formalized in Stage 6 by `Copy.ruleAt`,
  `Copy.scheduled_encode`, and the cross-family non-overlap theorems.
