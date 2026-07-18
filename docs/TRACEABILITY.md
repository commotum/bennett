# Paper-to-Lean Traceability

## Status Legend

- **Formalized:** proved as stated.
- **Corrected:** a materially changed statement is proved; see corrections log.
- **Assumptions:** formalized under explicit additional assumptions.
- **Split:** represented by several more precise results.
- **Partial:** a nearby result is proved but an obligation remains.
- **Excluded:** intentionally outside the verified mathematical core.
- **Unresolved:** neither proved nor responsibly repaired yet.

Line references below point to `bennett-1973/bennett-1973.md`; page references
use the journal pages 525–532 in the PDF.

## Formal Claim Inventory

| ID | Paper location | Claim or construction | Lean counterpart or disposition | Status |
|---|---|---|---|---|
| `LR-01` | p. 525; lines 26–30 | Logical reversibility is uniqueness of a predecessor for a partial whole-machine step. | `PartialStep.Reversible`, `ReversibleOn`, `GraphOn`, and standard `Relator.LeftUnique` bridges in `Bennett.Transition.Core`. | Formalized (Stage 2) |
| `INPUT-RETENTION` | p. 525; line 30 | A reversible output-only realization cannot discard inputs when the computed function is noninjective. | `Bennett.Copy.injective_of_reversible_outputOnly`; the constructive retained-input endpoint is `computeCopyUncompute_apply_of_run_halted`. | Corrected and formalized (Stage 3): applies to a precise one-step realization equation |
| `HIST-01` | pp. 525–526; lines 30–34 | Recording discarded information makes a deterministic computation reversible; one record is stored per source step. | `HistoryRecorder`, `HistoryRecorder.areInverses`, `history_length_of_run`, and `trace_cleanup` in `Bennett.History.Core` and `Bennett.History.Run`. | Formalized under explicit executable instrumentation and two-sided recovery laws (Stage 2) |
| `COPY-BLANK` | p. 526; line 32 | A duplicate can be generated/erased reversibly when the target is initially blank or known equal. | `Copy.blankEquiv`, `Copy.observedEquiv`, their exact domain laws, and `CopyAudit.overwriteStep_not_reversible`. | Formalized (Stage 3) |
| `CCU-01` | p. 526; line 32 | Forward compute, blank-target copy, and backward compute retain input/output and erase history. | Abstract `Uncompute.computeCopyUncompute` and its exact domain/inverse theorems; concrete `Simulator.scheduled_of_computesIn`, `runs_of_computesIn`, and `central_correctness`. | Corrected/split and formalized: reusable exact-count macro (Stage 3) and autonomous three-tape machine (Stage 6) |
| `Q5-01` | p. 526; eq. (1), lines 40–49 | A read-write-shift quintuple is an individually injective partial map. | `Quintuple.UndoMatches`, `undo`, `singleStep_areInverses`, and `execute_injective_on` in `Bennett.Turing.Source.Inverse`. | Formalized constructively (Stage 5): inverse order is shift/read/write |
| `Q5-MACHINE` | p. 526; line 49 | Domain/range non-overlap characterizes a deterministic/reversible rule collection. | `QuadrupleMachine.DomainsDisjoint`/`RangesDisjoint`, relational uniqueness theorems, the overlapping-but-extensionally-unique audit example, and the concrete `machineWithEnumeration_syntacticallyReversible`. | Corrected/split and formalized as sufficient, not necessary (Stages 2, 5, and 6); `C-008` |
| `Q4-DEF` | pp. 526–527; eq. (2), lines 53–60 | A quadruple applies read/write or shift, exclusively, on each tape. | Heterogeneous `Action`, `MultiConfiguration`, and `Quadruple` in `Bennett.Turing.Quadruple.Core`. | Formalized by typed constructors (Stage 5) |
| `SPLIT-01` | p. 527; eqs. (3)–(4), lines 62–74 | A quintuple splits into read/write then shift using a fresh connector state. | `SplitState`, `SourceSplit.writeHalf`/`moveHalf`, `lift_two_step_of_matches`, `Machine.splitMachine`, and exact `2N`/`f+N` component counts. | Formalized and clarified (Stage 5); pure split range obstruction is `C-012` |
| `INV-01` | p. 527; item 1, line 92 | Swapping states/symbols and negating shifts constructs the inverse quadruple. | `Action.inverse`, `Quadruple.inverse`, `inverse_execute`, `step_areInverses`, and `inversePair`. | Constructive direction formalized (Stage 5); extensional necessity corrected by `C-011` |
| `OVERLAP-D` | p. 527; item 2, line 93 | Domain overlap is characterized tape-wise by compatible reads. | Semantic `DomainsOverlap` and `domainsOverlap_iff_domainCompatible`, with executable decidability transported from the finite criterion. | Formalized (Stage 5) |
| `OVERLAP-R` | p. 527; item 3, line 94 | Range overlap is characterized tape-wise by compatible writes/shift actions. | Semantic `RangesOverlap` and `rangesOverlap_iff_rangeCompatible` over the well-typed action cases. | Corrected transcription and formalized (Stage 5); `C-001` |
| `MACH-REV` | p. 527; line 96 | Pairwise non-overlap of rule domains and ranges defines a deterministic reversible quadruple machine. | Generic `stepRel_rightUnique`, `stepRel_leftUnique`, `step_reversible`, inverse-table laws, plus `Simulator.machineWithEnumeration_syntacticallyReversible`. | Corrected/split and formalized as a sufficient unique-rule discipline (Stages 5–6); `C-008` |
| `STD-IO` | p. 527; lines 98–124 | Standard word/tape/head format and standard source-machine restrictions. | `Tape.ofWord`, `Standard.config`, `Behavior.accepts`, `BennettNormalForm`, and `ComputesIn`/`Computes`; Stage 6 central endpoints instantiate all three tapes. | Corrected/split and formalized (Stages 4 and 6); empty words included; `C-002`, `C-003` |
| `STANDARDIZE` | note 4, line 296 | Any source machine can allegedly be standardized with a few extra symbols/rules. | No compiler is defined; a result would need an explicit source transformation, preserved standard I/O and halting, and proved symbol/rule overhead. | Unresolved; cited rather than proved by the paper |
| `MAIN-SEM` | p. 527; lines 126–134 | For every standard source `S`, target `R` halts iff `S` halts and maps `(I;B;B)` to `(I;B;P)`. | `Simulator.SimulationCertificate`, `central_correctness`, and `terminates_iff_source` in `Bennett.Turing.Simulator.Correctness`. | Corrected/split and formalized (Stage 6): `central_correctness` assumes decidable source controls/symbols, finite symbols, `BennettNormalForm`, a target-table enumeration equivalence, accepted standard input, and exact `ComputesIn` evidence; all tapes/heads/controls are explicit and raw `A₁`/`C₁` controls differ; `C-009` |
| `MAIN-SYNTAX` | p. 527; lines 136–148 | Exact states/rules/alphabets: `2f+2N+4`, `4N+2z+3`, and `(z,N+1,z)`. | `Simulator.control_card`, `tableRuleId_card_fullAlphabet`, `workAlphabet_card`, `historyAlphabet_card`, and `outputAlphabet_card`. | Formalized (Stage 6), with disjoint constructors and `z = card Symbol + 1` |
| `MAIN-COST` | p. 527; lines 148–154 | Exact time `4v+4λ+5` and tape spaces `(s,v+1,λ+2)`. | Time: `scheduled_of_computesIn`, `Resource.fullRules_length`, and `Resource.exists_fullRules_scheduled_of_computesIn`. History: `HistorySpace.concreteTrace_history_cost`. Work: `Resource.fullTrace_work_visitedPositions`, `Resource.WorkSupport.fullTrace_work_everNonblankPositions`, `fullTrace_work_footprintPositions`, `fullTrace_work_footprintPositions_eq_insert_right`, and its two footprint-cardinality cases. | Corrected/split and formalized (Stages 6–7): time is exact; history footprint is `v+1`; copy work/output footprint is `λ+2`; if `s` is source-footprint cardinality, target work is `s` iff the right delimiter is already present and `s+1` otherwise; `C-004`, `C-005` |
| `TABLE1-COMPUTE` | p. 528; Table 1, eq. (11), lines 183–201 | Two target rules per source rule; history stores rule index `m` out of phase with work/output actions. | `forwardRewriteRule`, `forwardRecordRule`, `forward_two_step`, and `forward_scheduled_of_run_empty` in `Simulator.Compute`. | Formalized (Stage 6), using intrinsic rule IDs rather than ordinal labels; `C-013` |
| `TABLE1-COPY` | p. 528; Table 1 | Five fixed copy-stage rules plus two families over each nonblank `x`; copy target begins blank. | Syntax/semantics: `CopyRuleId`, `Copy.ruleAt`, `Copy.scheduled`, and `Copy.scheduled_encode`. Resources: `Copy.Resource.copyTrace_transitionCount`, `copyTrace_work_footprintPositions_eq_Icc`, `copyTrace_output_footprintPositions_eq_Icc`, their footprint-cardinality theorems, and the four work/output maximum-nonblank/maximum-active theorems. | Formalized (Stages 6–7), including `λ=0`, exact `4λ+5`, blank target, unchanged checked history, footprint `λ+2`, peak nonblank `λ`, and peak active `λ+1`; `C-003`, `C-014` |
| `TABLE1-RETRACE` | p. 528; Table 1, lines 203–205 | `C`-labelled inverses retrace first-stage rules and erase history. | `reverseEraseRule`, `reverseRestoreRule`, `reverse_two_step`, and `forward_reverse_scheduled_to_standard_finish` in `Simulator.Reverse`. | Formalized (Stage 6): exact work/history/head cleanup and retained output; physical control ends in the reverse phase; `C-009` |
| `TABLE1-NONOVERLAP` | p. 529; line 205 | All domains and ranges, including stage boundaries, are non-overlapping. | `rules_domains_disjoint`, `rules_ranges_disjoint`, and `machineWithEnumeration_syntacticallyReversible` in `Simulator.Nonoverlap`. | Formalized globally (Stage 6) under source key injectivity and `NoFinishBlankRule`, both supplied by normal form; sharp failure witnesses are proved |
| `GENERAL-HISTORY` | p. 529; line 209 | The history method applies to any deterministic finite/infinite automaton with sufficient storage. | `HistoryRecorder` theorem for executable partial steps with explicit instrumenting/recovery data; no generic record-size bound. | Corrected and formalized under explicit assumptions (Stage 2) |
| `ONE-TAPE` | p. 529; line 209 | A one-tape reversible simulator may take as many as `v²` steps. | No one-tape simulator or trace-cost proof is defined in the library. | Unresolved; not required by the proved three-tape construction |
| `TABLE2` | prose p. 529, table p. 530; line 211 | If output computably recovers input, seven reversible stages can erase the retained input. | `Copy.blankEquiv`/`observedEquiv` formalize equality-checked inverse copying, and the concrete Table 1 copy loop proves its standard tape/head invariant.  No seven-stage composition is defined. | Partial with an unresolved concrete obligation: specify forward/inverse realizations of `S₁` and recovery machine `S₂`, then prove every intermediate tape/head invariant and the composed endpoint; `C-006` |
| `SEG-SEM` | pp. 529–530; lines 221–222 | Segment histories and higher-level dumps can themselves be uncomputed. | `Checkpoint.recordedSegmentStage_apply_of_run` erases the primary history generated inside one segment; `Checkpoint.areInverses`, `run_from_initial_shape`, and `cleanup_of_completes` give the global chain and exact `n-1` dumps. `Checkpoint.Plan.exists_completes_segmentPlan_with_dump_count` and `computeCopyCleanup_segmentPlan_apply_of_run` bridge exact source iterates to full cleanup. | Corrected/split and formalized (Stage 8): checkpoints are complete restart states containing control, tapes, heads, phase, and other resume data; concrete allocation remains abstract |
| `SEG-COST` | p. 530; lines 223–241 | Idealized storage `v/n+ns`, minimized at `n=√(v/s)` to `2√(vs)`, with doubled time ignoring dump I/O. | `Cost.SegmentPlan`, `temporaryCells_eq`, `paperRoundedCells_eq_temporaryCells_add_dumpCells`, `checkpointTime_eq_two_unsegmented_add_dumpIO`, `temporaryCells_balanced_le`, `paperContinuousCells_lower_bound`, and `paperContinuousCells_at_sqrt_ratio`. | Corrected/split and formalized under an explicit model (Stage 8); exact discrete budget is `v ⌈/⌉ n + (n-1)s`, paper-rounded cost is one dump higher, four-pass time has parameterized dump I/O, and the real AM--GM result is separate; `C-007` |
| `NESTED-LOG` | p. 530; line 241 | Nested reversal might achieve logarithmic temporary space and perhaps quadratic time. | No Lean theorem: a recursive checkpoint schedule, restart invariant, dump allocation, and complete time/space proof are absent from the paper. | Excluded after Stage 8 as explicitly speculative; no logarithmic-space or quadratic-time claim is exported |
| `UNIVERSAL` | pp. 529–530; lines 209, 243 | Broad statements that arbitrary computations can be made reversible. | `HistoryRecorder` covers partial steps supplied with explicit recovery data, and `Simulator.central_correctness` covers accepted inputs for `BennettNormalForm` sources.  No arbitrary-machine standardization compiler is defined. | Partial at those explicit generalities; the unrestricted universality claim is unresolved because `STANDARDIZE` is unresolved |

## Table 1 Reconstruction Ledger

This transcription has been reconstructed and verified as explicit Lean syntax
in `Bennett.Turing.Simulator`.  Bracket
entries are ordered `(working, history, output)`.  `/` means shift/no-read;
`b` is blank; `x` ranges over nonblank source symbols.

### Compute stage

For source rule `m : A_j T → T' σ A_k`:

```text
A_j [T, /, b]   → [T', +, b] A'_m
A'_m [/, b, /]  → [σ, m, 0] A_k
```

The first and last indexed instances shown separately in the table agree with
the special entry/exit quintuples.  Formally, `entryId` and `exitId` are
distinguished intrinsic IDs rather than literal ordinal positions (`C-013`).
After the exit lower rule, state is `A_f`, work is standard output, history head
scans `exitId`, and output tape is blank.

```text
A₁     [b, /, b] → [b, +, b] A'₁
A'₁    [/, b, /] → [+, 1, 0] A₂
A_f₋₁  [b, /, b] → [b, +, b] A'_N
A'_N   [/, b, /] → [0, N, 0] A_f
```

### Copy stage

```text
A_f [b, N, b]   → [b, N, b] B'_1
B'_1 [/, /, /]  → [+, 0, +] B_1
B_1 [x, N, b]   → [x, N, x] B'_1       for every x ≠ b
B_1 [b, N, b]   → [b, N, b] B'_2
B'_2 [/, /, /]  → [-, 0, -] B_2
B_2 [x, N, x]   → [x, N, x] B'_2       for every x ≠ b
B_2 [b, N, b]   → [b, N, b] C_f
```

Thus there are five fixed copy/link rules and `2(z-1)` symbol-indexed rules,
for `2z+3` copy-stage rules when the finite alphabet has one distinguished blank.

### Retrace stage

For source rule `m : A_j T → T' σ A_k`:

```text
C_k [/, m, /]   → [-σ, b, 0] C'_m
C'_m [T', /, b] → [T, -, b] C_j
```

Here the history move in the second rule is `-`; the output tape is only read as
blank and is never changed during compute/retrace.  Table 1's special first and
last rows are instances of these schemas.  Stage 5's `Quadruple.inverse`
verifies the precise inverse action order; Stage 6 instantiates the schemas and
proves every within- and cross-family domain/range separation case.

```text
C_f    [/, N, /] → [0, b, 0] C'_N
C'_N   [b, /, b] → [b, -, b] C_f₋₁
C₂     [/, 1, /] → [-, b, 0] C'₁
C'₁    [b, /, b] → [b, -, b] C₁
```

The literal checkpoints include the standard head positions pictured by the
underbars:

```text
(I, blank, blank) → (P, history, blank)
  → (P, history, P) → (I, blank, P).
```

Work and output heads return to their left-delimiter blanks; the output head
stays there throughout retracing.  Control is `A₁` initially and `C₁` finally,
so “restored” is not literal equality of whole configurations; see `C-009`.

## Table 2 Reconstruction Ledger

Table 2 supplies a semantic seven-stage diagram rather than transition syntax:

```text
(INPUT,  blank,    blank)
  --forward S₁-->       (OUTPUT, HISTORY 1, blank)
  --copy output-->      (OUTPUT, HISTORY 1, OUTPUT)
  --retrace S₁-->       (INPUT,  blank,    OUTPUT)
  --swap tapes 1/3-->  (OUTPUT, blank,    INPUT)
  --forward S₂-->       (INPUT,  HISTORY 2, INPUT)
  --erase equal copy--> (INPUT,  HISTORY 2, blank)
  --retrace S₂-->       (OUTPUT, blank,    blank)
```

It presupposes that `S₂` computes the original input from the output and that
stage 6 is the inverse of a valid blank-target copy on an equality invariant.

## Excluded Physical and Heuristic Material

| ID | Paper location | Material | Classification |
|---|---|---|---|
| `PHYS-LAND` | p. 525, lines 28–30 | Entropy generation and `kT ln 2` per erased bit. | Excluded: requires a thermodynamic model. |
| `PHYS-RW` | pp. 530–531, lines 247–279 | Reaction-chain random walks, drift, final-state probability, and energy/rate formulas. | Excluded: physical/stochastic assumptions are not consequences of machine semantics. |
| `PHYS-RNA` | pp. 531–532, lines 281–285 | RNA synthesis/degradation examples and biochemical energy costs. | Excluded: empirical biochemical claims. |
| `HEUR-INORD` | p. 530, line 243 | “Without inordinate increases” summary. | Excluded as qualitative; replaced only by proved explicit bounds. |

## Maintenance Rule

Every formalized entry names its exact module or declaration.  A status is
classified as **Formalized**, **Corrected**, or **Assumptions** only after the
relevant focused build and proof audit; partial, unresolved, and excluded rows
retain the exact missing obligation or scope boundary.
