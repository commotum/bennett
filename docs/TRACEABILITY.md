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
| `LR-01` | p. 525; lines 26–30 | Logical reversibility is uniqueness of a predecessor for a partial whole-machine step. | `Bennett.Transition` predicates separating partial determinism and reversibility. | Planned (Stage 2) |
| `HIST-01` | pp. 525–526; lines 30–34 | Recording discarded information makes a deterministic computation reversible; one record is stored per source step. | Recorded-step inverse and history-length theorems. | Planned (Stage 2) |
| `CCU-01` | p. 526; line 32 | Forward compute, blank-target copy, and backward compute retain input/output and erase history. | Abstract compute-copy-uncompute theorem with explicit copy invariant. | Planned (Stage 3) |
| `Q5-01` | p. 526; eq. (1), lines 40–49 | A read-write-shift quintuple is an individually injective partial map. | Quintuple semantics and local inverse theorem. | Planned (Stages 4–5) |
| `Q4-DEF` | pp. 526–527; eq. (2), lines 53–60 | A quadruple applies read/write or shift, exclusively, on each tape. | Per-tape action and multi-tape quadruple syntax. | Planned (Stage 5) |
| `SPLIT-01` | p. 527; eqs. (3)–(4), lines 62–74 | A quintuple splits into read/write then shift using a fresh connector state. | Exact two-step simulation and freshness theorem. | Planned (Stage 5) |
| `INV-01` | p. 527; item 1, line 92 | Swapping states/symbols and negating shifts constructs the inverse quadruple. | `Quadruple.inverse` and two inverse laws. | Planned (Stage 5) |
| `OVERLAP-D` | p. 527; item 2, line 93 | Domain overlap is characterized tape-wise by compatible reads. | Domain-overlap iff theorem. | Planned (Stage 5) |
| `OVERLAP-R` | p. 527; item 3, line 94 | Range overlap is characterized tape-wise by compatible writes/shift actions. | Range-overlap iff theorem with well-typed action cases. | Corrected transcription / planned (Stage 5); `C-001` |
| `MACH-REV` | p. 527; line 96 | Pairwise non-overlap of rule domains and ranges defines a deterministic reversible quadruple machine. | Syntactic predicates plus semantic uniqueness proofs. | Split / planned (Stage 5) |
| `STD-IO` | p. 527; lines 98–124 | Standard word/tape/head format and standard source-machine restrictions. | Standard configuration and `StandardSource` assumptions. | Assumptions / planned (Stage 4); `C-002`, `C-003` |
| `MAIN-SEM` | p. 527; lines 126–134 | For every standard source `S`, target `R` halts iff `S` halts and maps `(I;B;B)` to `(I;B;P)`. | Full configuration-level central correctness theorem. | Planned (Stage 6) |
| `MAIN-SYNTAX` | p. 527; lines 136–148 | Exact states/rules/alphabets: `2f+2N+4`, `4N+2z+3`, and `(z,N+1,z)`. | Cardinality theorems over the constructed finite syntax. | Planned (Stage 7) |
| `MAIN-COST` | p. 527; lines 148–154 | Exact time `4v+4λ+5` and tape spaces `(s,v+1,λ+2)`. | Trace-length and per-tape visited/used-cell theorems. | Assumptions / planned (Stage 7); `C-004`, `C-005` |
| `TABLE1-COMPUTE` | p. 528; Table 1, eq. (11), lines 183–201 | Two target rules per source rule; history stores rule index `m` out of phase with work/output actions. | Indexed forward-stage syntax and one-step/two-step simulation. | Planned (Stage 6) |
| `TABLE1-COPY` | p. 528; Table 1 | Five fixed copy-stage rules plus two families over each nonblank `x`; copy target begins blank. | Standard-word copy loop and blank invariant. | Planned (Stage 6) |
| `TABLE1-RETRACE` | p. 528; Table 1, lines 203–205 | `C`-labelled inverses retrace first-stage rules and erase history. | Reverse trace theorem restoring full configuration. | Planned (Stage 6) |
| `TABLE1-NONOVERLAP` | p. 528; line 205 | All domains and ranges, including stage boundaries, are non-overlapping. | Finite rule-family disjointness and semantic determinism/reversibility. | Planned (Stage 6) |
| `ONE-TAPE` | p. 529; line 209 | A one-tape reversible simulator may take as many as `v²` steps. | Separate model/construction would be required. | Unresolved; not required by main construction |
| `TABLE2` | p. 529; Table 2, line 211 | If output computably recovers input, seven reversible stages can erase the retained input. | Composition theorem from forward/inverse realizations of `S₁` and `S₂`. | Planned after Stage 6; copy-erasure precondition noted in `C-006` |
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
