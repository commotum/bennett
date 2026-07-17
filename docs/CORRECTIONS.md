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
- **Status:** Open (Stages 4, 6, and 7).

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
- **Status:** Open.

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
  same endpoint convention.
- **Corrected formulation:** prove separate visited-cell and occupied/nonblank
  statements with head/endpoint conventions explicit, then identify the one
  matching each paper number.
- **Justification:** the measures differ on blank cells even for Table 1's trace.
- **Consequences:** no exact space theorem is inferred from semantic simulation;
  Stage 4 defines measures and Stage 7 audits the formulas.
- **Status:** Open.

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
- **Status:** Open (Stage 3 and post-Stage 6 composition).

## C-007 — Segmented optimum is continuous and omits costs

- **Location:** journal p. 527 line 154 and p. 530 lines 221–241.
- **Original claim:** choosing `n = √(v/s)` gives temporary storage
  `2√(vs)` (earlier “less than” that amount) and buys the reduction for twice
  the time, ignoring restart-dump I/O.
- **Issue:** segment count is a positive integer; `v` may not divide evenly;
  dumps may number `n-1` rather than `n`; segment lengths may differ; and dump
  read/write time is explicitly omitted.  The earlier strict inequality and the
  later equality cannot both describe the same unrounded expression uniformly.
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
  transition relation, and standard reachable computations.  The iff relies on
  each rule being an injective partial map and on the exact meaning of distinct
  rules/range overlap; restricted reachability can be reversible even when
  unreachable syntactic ranges overlap.
- **Corrected formulation:** define global semantic predecessor uniqueness,
  set-restricted predecessor uniqueness, and syntactic pairwise range
  disjointness separately.  Prove the sufficient implication, and prove a
  converse only with the hypotheses it actually needs.
- **Justification:** this preserves the paper's intended global construction
  while making later reachable-input theorems honest.
- **Consequences:** Stages 2 and 5 own distinct APIs; Stage 6 reports both global
  constructed-machine properties and standard-run correctness where proved.
- **Status:** Open (Stages 2, 5, and 6).
