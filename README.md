# Logical Reversibility of Computation in Lean 4

This repository reconstructs the mathematical core of C. H. Bennett's 1973
paper, *Logical Reversibility of Computation*, as a reusable Lean 4 library.
It treats the paper as a fallible source: definitions, simulations,
reversibility arguments, exact counts, and resource claims are stated with
explicit assumptions and checked by Lean.

The verified core includes:

- deterministic partial transition systems and exact finite runs;
- globally or reachably reversible steps and partial equivalences;
- history-recording simulation with exact inverse cleanup;
- blank-target copying and reusable compute-copy-uncompute;
- executable source Turing machines and reversible heterogeneous quadruples;
- Bennett's complete three-tape Table 1 simulator;
- exact state, rule, alphabet, time, and separated tape-resource results; and
- abstract segmented checkpointing with discrete and continuous cost models.

Thermodynamic, chemical, and biological discussion is documented but is not
presented as a consequence of logical reversibility.

## Quick start

The project is under [`formal/`](formal/). It pins Lean 4.31.0 and mathlib
commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

```sh
cd formal
lake build Bennett
lake build Bennett.Audit
```

`Bennett.Audit` imports all executable examples and prints the axiom
dependencies of the principal results. It is intentionally not re-exported by
the public root.

For downstream code, import the complete library:

```lean
import Bennett
```

Or use a narrow stable API:

```lean
import Bennett.Transition.API
import Bennett.History.API
import Bennett.Copy.API
import Bennett.Uncompute.API
import Bennett.Checkpoint.API
import Bennett.Turing.API
import Bennett.Turing.Simulator.API
```

## Main results

At the abstract level:

- `HistoryRecorder.trace_cleanup` proves one record per source step and exact
  reverse restoration of the starting state and history.
- `Uncompute.computeCopyUncompute_apply_of_run_halted` retains the input,
  copies an observed result onto a known blank target, and removes all generated
  history.
- `Checkpoint.recordedSegmentStage_apply_of_run` performs and retraces one
  source segment while leaving only its complete restart checkpoint.
- `Checkpoint.Plan.computeCopyCleanup_segmentPlan_apply_of_run` connects an
  integer `SegmentPlan` to a complete checkpoint chain, copies the final
  observation, and erases all intermediate dumps.

For Bennett's concrete machine,
`Turing.Simulator.central_correctness` takes a `BennettNormalForm` source, an
explicit finite rule enumeration, an accepted standard input, and an exact
source computation. It returns a `SimulationCertificate` containing:

- the exact three-tape initial and final configurations;
- retained input, copied output, blank history, and restored heads;
- a target run of exactly `4v + 4λ + 5` quadruple transitions;
- global table domain/range non-overlap, determinism, and reversibility; and
- the physically distinct forward and reverse controls together with their
  proved logical-control correspondence.

`Turing.Simulator.terminates_iff_source` proves halting equivalence in both
directions on accepted standard inputs.

## Resource conventions

Counts use constructed syntax and explicit traces, never semantic correctness
alone. A source step is one quintuple; a target step is one quadruple. A trace
with `k` successful transitions has `k + 1` states, and a failed halt lookup is
not counted.

Tape measures remain distinct: head-visited cells, cells ever nonblank, their
footprint union, peak nonblank cells, and peak active cells. In particular:

- copy work/output footprint is `λ + 2`, while peak nonblank data is `λ`;
- history footprint is `v + 1`, while peak nonblank history is `v`; and
- target work footprint is the source footprint plus at most the final right
  delimiter, giving exact `s` or `s + 1` under the documented convention.

Checkpoint temporary space is
`ceil(v / n) + (n - 1) * s` for positive segment count `n`, excluding permanent
input/output and ordinary live work storage. Dump I/O is an explicit caller
supplied time charge. The paper's `2 * sqrt(v * s)` expression is proved only
in a separately named real-valued continuous relaxation.

## Extending the library

1. Define a `PartialStep α` and prove exact `Runs` facts.
2. Supply a `HistoryRecorder` with instrumentation, recovery, and both recovery
   laws; the generic inverse and uncomputation results then apply.
3. For a Turing source, define its finite `Machine`, standard I/O behavior, and
   the required `BennettNormalForm` evidence.
4. For checkpointing, use `Checkpoint.Cost.SegmentPlan` and
   `Checkpoint.Plan.segmentSteps`. A restart dump must contain every component
   needed to resume, including control, tapes, heads, and phase.

## Scope and known limitations

- The central simulator theorem covers accepted standard inputs satisfying
  explicit normal-form assumptions; malformed configurations are not claimed
  to encode source computations.
- Checkpoint dumps are abstract complete states. Concrete tape allocation,
  encoding size, and dump read/write/erase costs require a machine-specific
  implementation.
- The paper's concrete seven-stage Table 2 composition is not built, although
  its blank-copy and checked-uncopy primitives are verified.
- The claimed general source-standardization compiler and one-tape `v²`
  simulator are unresolved.
- Nested logarithmic-space checkpointing is speculative in the paper and is
  intentionally not a theorem here.
- Physical claims about entropy, energy, chemistry, or RNA are excluded from
  the verified mathematical core.

## Documentation

- [Formal project and module guide](formal/README.md)
- [Semantic and resource conventions](docs/CONVENTIONS.md)
- [Paper-to-Lean traceability](docs/TRACEABILITY.md)
- [Corrections and unresolved claims](docs/CORRECTIONS.md)
- [Formalization plan and recorded stage results](goal-1/0-plan.md)
- [Transcribed paper](bennett-1973/bennett-1973.md)
