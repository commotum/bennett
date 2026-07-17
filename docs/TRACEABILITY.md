# Paper-to-Lean Traceability

## Status Legend

- **Planned:** owning stage and intended Lean artifact are identified.
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

| ID | Paper location | Claim or construction | Planned Lean counterpart | Status |
|---|---|---|---|---|
| `LR-01` | p. 525; lines 26–30 | Logical reversibility is uniqueness of a predecessor for a partial whole-machine step. | `PartialStep.Reversible`, `ReversibleOn`, `GraphOn`, and standard `Relator.LeftUnique` bridges in `Bennett.Transition.Core`. | Formalized (Stage 2) |
| `INPUT-RETENTION` | p. 525; line 30 | A reversible output-only realization cannot discard inputs when the computed function is noninjective. | `Bennett.Copy.injective_of_reversible_outputOnly`; the constructive retained-input endpoint is `computeCopyUncompute_apply_of_run_halted`. | Corrected and formalized (Stage 3): applies to a precise one-step realization equation |
| `HIST-01` | pp. 525–526; lines 30–34 | Recording discarded information makes a deterministic computation reversible; one record is stored per source step. | `HistoryRecorder`, `areInverses`, `history_length_of_run`, and `trace_cleanup` in `Bennett.History`. | Formalized under explicit recovery laws (Stage 2) |
| `COPY-BLANK` | p. 526; line 32 | A duplicate can be generated/erased reversibly when the target is initially blank or known equal. | `Copy.blankEquiv`, `Copy.observedEquiv`, their exact domain laws, and `CopyAudit.overwriteStep_not_reversible`. | Formalized (Stage 3) |
| `CCU-01` | p. 526; line 32 | Forward compute, blank-target copy, and backward compute retain input/output and erase history. | `Uncompute.computeCopyUncompute`, `exists_stages_of_run`, `computeCopyUncompute_eq_some_iff`, `computeCopyUncompute_symm_apply_of_run_halted`, and `exists_computeCopyUncompute_iff_terminates`. | Corrected/split and formalized as an exact-count semantic macro (Stage 3); autonomous scheduling remains Stage 6 |
| `Q5-01` | p. 526; eq. (1), lines 40–49 | A read-write-shift quintuple is an individually injective partial map. | Stage 4 defines `Turing.Quintuple.Matches`/`execute` in read-write-move-control order; the constructive local inverse remains Stage 5. | Partial (Stage 4); inverse proof planned Stage 5 |
| `Q5-MACHINE` | p. 526; line 49 | Domain/range non-overlap characterizes a deterministic/reversible rule collection. | Extensional semantics are separated in `Bennett.Transition.Core`; syntactic rule criteria remain for Stages 4–5. | Partial/corrected (Stage 2); `C-008` |
| `Q4-DEF` | pp. 526–527; eq. (2), lines 53–60 | A quadruple applies read/write or shift, exclusively, on each tape. | Per-tape action and multi-tape quadruple syntax. | Planned (Stage 5) |
| `SPLIT-01` | p. 527; eqs. (3)–(4), lines 62–74 | A quintuple splits into read/write then shift using a fresh connector state. | Exact two-step simulation and freshness theorem. | Planned (Stage 5) |
| `INV-01` | p. 527; item 1, line 92 | Swapping states/symbols and negating shifts constructs the inverse quadruple. | `Quadruple.inverse` and two inverse laws. | Planned (Stage 5) |
| `OVERLAP-D` | p. 527; item 2, line 93 | Domain overlap is characterized tape-wise by compatible reads. | Domain-overlap iff theorem. | Planned (Stage 5) |
| `OVERLAP-R` | p. 527; item 3, line 94 | Range overlap is characterized tape-wise by compatible writes/shift actions. | Range-overlap iff theorem with well-typed action cases. | Corrected transcription / planned (Stage 5); `C-001` |
| `MACH-REV` | p. 527; line 96 | Pairwise non-overlap of rule domains and ranges defines a deterministic reversible quadruple machine. | Semantic target (`Reversible`, `ReversibleOn`) is formalized; syntactic sufficient criteria remain for Stage 5. | Partial/corrected (Stage 2); `C-008` |
| `STD-IO` | p. 527; lines 98–124 | Standard word/tape/head format and standard source-machine restrictions. | `Tape.ofWord`, `Standard.config`, `Behavior.accepts`, `BennettNormalForm`, and `ComputesIn`/`Computes` in `Bennett.Turing`. | Corrected/split and formalized (Stage 4); concrete source instances remain later; `C-002`, `C-003` |
| `STANDARDIZE` | note 4, line 296 | Any source machine can allegedly be standardized with a few extra symbols/rules. | Separate compiler/simulation theorem if later universality claims require it. | Unresolved; cited rather than proved by the paper |
| `MAIN-SEM` | p. 527; lines 126–134 | For every standard source `S`, target `R` halts iff `S` halts and maps `(I;B;B)` to `(I;B;P)`. | Full configuration-level central correctness theorem. | Planned (Stage 6) |
| `MAIN-SYNTAX` | p. 527; lines 136–148 | Exact states/rules/alphabets: `2f+2N+4`, `4N+2z+3`, and `(z,N+1,z)`. | Cardinality theorems over the constructed finite syntax. | Planned (Stage 7) |
| `MAIN-COST` | p. 527; lines 148–154 | Exact time `4v+4λ+5` and tape spaces `(s,v+1,λ+2)`. | Stage 4 defines exact endpoint traces and separate visited/nonblank/footprint/peak measures; construction-derived formulas remain Stage 7. | Partial infrastructure (Stage 4); exact claims planned Stage 7; `C-004`, `C-005` |
| `TABLE1-COMPUTE` | p. 528; Table 1, eq. (11), lines 183–201 | Two target rules per source rule; history stores rule index `m` out of phase with work/output actions. | Indexed forward-stage syntax and one-step/two-step simulation. | Planned (Stage 6) |
| `TABLE1-COPY` | p. 528; Table 1 | Five fixed copy-stage rules plus two families over each nonblank `x`; copy target begins blank. | Standard-word copy loop and blank invariant. | Planned (Stage 6) |
| `TABLE1-RETRACE` | p. 528; Table 1, lines 203–205 | `C`-labelled inverses retrace first-stage rules and erase history. | Reverse trace theorem restoring full configuration. | Planned (Stage 6) |
| `TABLE1-NONOVERLAP` | p. 529; line 205 | All domains and ranges, including stage boundaries, are non-overlapping. | Finite rule-family disjointness and semantic determinism/reversibility. | Planned (Stage 6) |
| `GENERAL-HISTORY` | p. 529; line 209 | The history method applies to any deterministic finite/infinite automaton with sufficient storage. | `HistoryRecorder` theorem for executable partial steps with explicit instrumenting/recovery data; no generic record-size bound. | Corrected and formalized under explicit assumptions (Stage 2) |
| `ONE-TAPE` | p. 529; line 209 | A one-tape reversible simulator may take as many as `v²` steps. | Separate model/construction would be required. | Unresolved; not required by main construction |
| `TABLE2` | prose p. 529, table p. 530; line 211 | If output computably recovers input, seven reversible stages can erase the retained input. | Stage 3 formalizes the required blank-copy/equality-checked uncopy primitive; the seven-stage composition still needs forward/inverse realizations of `S₁` and `S₂`. | Partial; planned after Stage 6; `C-006` |
| `SEG-SEM` | pp. 529–530; lines 221–222 | Segment histories and higher-level dumps can themselves be uncomputed. | Abstract finite checkpoint composition. | Planned (Stage 8) |
| `SEG-COST` | p. 530; lines 223–241 | Idealized storage `v/n+ns`, minimized at `n=√(v/s)` to `2√(vs)`, with doubled time ignoring dump I/O. | Integer-rounded optimization under an explicit cost model. | Assumptions / planned (Stage 8); `C-007` |
| `NESTED-LOG` | p. 530; line 241 | Nested reversal might achieve logarithmic temporary space and perhaps quadratic time. | No theorem absent a complete construction. | Excluded as explicitly speculative |
| `UNIVERSAL` | pp. 529–530; lines 209, 243 | Broad statements that arbitrary computations can be made reversible. | Corollaries only at the generality actually proved. | Partial/planned; depends on model standardization |

## Table 1 Reconstruction Ledger

This transcription is a design input, not yet a verified Lean program.  Bracket
entries are ordered `(working, history, output)`.  `/` means shift/no-read;
`b` is blank; `x` ranges over nonblank source symbols.

### Compute stage

For source rule `m : A_j T → T' σ A_k`:

```text
A_j [T, /, b]   → [T', +, b] A'_m
A'_m [/, b, /]  → [σ, m, 0] A_k
```

The first and last indexed instances shown separately in the table agree with
the special entry/exit quintuples.  After the last lower rule, state is `A_f`,
work is standard output, history head scans record `N`, and output tape is blank.

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
last rows are instances of these schemas.  Stage 5 must verify the precise
formal inverse action order; Stage 6 must prove all cross-family non-overlap.

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

When a declaration is added, replace its planned path with the exact module and
declaration name.  A status may become **Formalized**, **Corrected**, or
**Assumptions** only after the relevant focused build and proof audit are
recorded in the owning stage file.
