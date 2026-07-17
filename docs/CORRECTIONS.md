# Corrections, Ambiguities, and Failed Obligations

This is a cumulative log.  An entry records a source issue before dependent Lean
results are stated.  “Open” means the repaired theorem has not yet been proved;
it does not license silently using the proposed repair.

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
- **Consequences:** Stage 5 will use a typed sum of `write` and `move` actions,
  making the invalid expression unrepresentable, and prove the repaired iff.
- **Status:** Open proof obligation (Stage 5); identified as Markdown conversion
  error rather than a mathematical error in the scan.

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
- **Consequences:** `StandardSource` will expose directional freshness and
  nondegeneracy assumptions; exact state counts remain conditional on them.
- **Status:** The directional assumptions are formalized in Stage 4 as
  `Standard.BennettNormalForm` (`entry_only_rule_from_start`,
  `no_rule_targets_start`, `exit_only_rule_to_finish`, and
  `no_rule_sources_finish`).  Concrete Table 1 use and exact counts remain
  Stages 6–7.

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
  delimiter traversal has two cells (`λ+2 = 2`).  `NonemptyWord` remains an
  explicit optional premise; copy-loop execution/time proofs in Stages 6–7 must
  determine whether the paper theorem covers `λ=0`.

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
- **Consequences:** documentation will not use an unqualified factor-two claim;
  Stage 7 will prove the exact trace length before stating any ratio.
- **Status:** Exact formula awaiting proof (Stage 7); terminology corrected now.

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
- **Corrected formulation:** prove separate visited-cell and occupied/nonblank
  statements with head/endpoint conventions explicit.  The robust tape-1
  footprint is the union of the source-run footprint and the copy traversal of
  the final standard output; an exact `s` follows only if `s` already includes
  that traversal (in particular the right delimiter).
- **Justification:** the measures differ on blank cells even for Table 1's trace.
- **Consequences:** no exact space theorem is inferred from semantic simulation;
  Stage 4 defines measures and Stage 7 audits the formulas.
- **Status:** Stage 4 formalizes separate `visitedPositions`,
  `everNonblankPositions`, `footprintPositions`, `maximumNonblankCells`, and
  `maximumActiveCells`.  It proves only the layout fact that a complete
  delimiter traversal has `λ+2` positions; actual Table 1 trace footprints and
  the source-tape `s`/`s+1` question remain open for Stages 6–7.

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
  Stage 3 (`Copy.blankEquiv` and `observedEquiv`).  The standard-tape copy loop,
  head-format invariant, and full Table 2 composition remain open after Stage 6.

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
- **Corrected formulation:** first define an exact integer cost such as
  `ceil(v/n) + (n-1)s` (or the construction-derived alternative), prove a bound
  for an explicitly rounded `n`, and state dump-I/O assumptions in the time
  theorem.  Retain `2√(vs)` as the continuous relaxation when appropriate.
- **Justification:** elementary discrete optimization and actual checkpoint
  layout, not the semantic simulation theorem.
- **Consequences:** no exact checkpoint bound is exported before Stage 8; the
  nested `log v` sentence remains speculative and excluded.
- **Status:** Open (Stage 8).

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
- **Status:** Semantic distinction formalized in Stage 2 (`PartialStep.Graph`,
  `GraphOn`, `Reversible`, `ReversibleOn`, and Relator bridges); syntactic
  sufficiency/concrete application remain open for Stages 5–6.

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
- **Status:** Stage 2's abstract `HistoryRecorder.trace_cleanup` proves literal
  restoration on a single state carrier.  The concrete `A₁`/`C₁` projection
  remains open for Stage 6.

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
  scheduling and concrete cross-family non-overlap remain open for Stage 6.

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
- **Status:** Open (Stage 5).
