# Bennett Lean library

This Lake project is the verified computational core of Bennett's
*Logical Reversibility of Computation*. The public library combines reusable
partial-system abstractions, a concrete three-tape reversible Turing simulator,
and an abstract checkpoint construction with explicit resource models.

## Pinned environment and builds

- Lean: `leanprover/lean4:v4.31.0`
- mathlib: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`

From this directory:

```sh
lake build Bennett
lake build Bennett.Audit
```

The first command builds the public root. The second builds the umbrella audit,
which imports every diagnostic leaf and prints the axiom dependencies of the
principal results. To build audits separately:

```sh
lake build Bennett.History.Audit Bennett.Copy.Audit
lake build Bennett.Uncompute.Audit Bennett.Checkpoint.Audit
lake build Bennett.Turing.Audit Bennett.Turing.Quadruple.Audit
lake build Bennett.Turing.Simulator.Audit
```

## Module organization

```text
Bennett.lean                       public root
Bennett/
├── Transition/                    partial steps, runs, reachability
├── History/                       recorded reversible execution
├── Copy/                          blank-target copying and no-go result
├── Uncompute/                     abstract compute-copy-uncompute
├── Checkpoint/
│   ├── Core.lean                  reversible stages and checkpoint chains
│   ├── Cost.lean                  discrete costs and continuous relaxation
│   ├── Plan.lean                  source-run and SegmentPlan bridge
│   ├── API.lean
│   └── Audit.lean
└── Turing/
    ├── Tape.lean                  two-way finite-support tapes
    ├── Word.lean                  canonical standard words
    ├── Resource.lean              trace and tape measures
    ├── Source/                    quintuple machines and normal form
    ├── Quadruple/                 typed reversible target syntax
    ├── Simulator/                 complete Bennett Table 1 construction
    ├── API.lean
    └── Audit.lean
Bennett/Audit.lean                 non-public whole-library audit
```

Within `Simulator/`, the implementation is split into syntax, forward compute,
copy, reverse cleanup, finite-machine construction, global non-overlap,
correctness, and resource leaves. Internal modules use narrow imports; audit
leaves are not imported by `Bennett`.

## Imports

Use the root for the complete supported surface:

```lean
import Bennett
```

Prefer narrow imports in libraries that need only one layer:

```lean
import Bennett.Transition.API
import Bennett.History.API
import Bennett.Copy.API
import Bennett.Uncompute.API
import Bennett.Checkpoint.API
import Bennett.Turing.API
import Bennett.Turing.Quadruple.API
import Bennett.Turing.Simulator.API
```

## Principal declarations

The following signatures summarize the public proof layers.

### Partial systems and histories

`PartialStep α` is `α → Option α`. `Runs step n before after` means exactly
`n` successful transitions. Determinism is successor uniqueness;
`Reversible` is predecessor uniqueness on successful transitions.

```lean
HistoryRecorder.trace_cleanup :
  recorder.trace n before = some ⟨after, history⟩ →
    history.length = n ∧
    recorder.backward.iterate n ⟨after, history⟩ = some ⟨before, []⟩
```

`PartialStep.AreInverses.iterate` and `HistoryRecorder.areInverses` expose the
corresponding two-sided partial equivalences.

### Compute-copy-uncompute

At a halted exact endpoint:

```lean
Uncompute.computeCopyUncompute_apply_of_run_halted :
  step.Runs n before after → step.Halted after →
  computeCopyUncompute recorder observe blank n
      (⟨before, initialHistory⟩, blank) =
    some (⟨before, initialHistory⟩, observe after)
```

Copying accepts a known blank target. Its inverse accepts a checked equal copy;
unrestricted destructive overwrite is not treated as reversible copying.

### Checkpoint plans

`Checkpoint.recordedSegmentStage_apply_of_run` implements one irreversible
source segment with primary history, copies its complete endpoint, and restores
the scratch baseline.

```lean
Checkpoint.Plan.computeCopyCleanup_segmentPlan_apply_of_run :
  step.Runs steps input output →
  computeCopyCleanup (segmentSteps step plan.lengths)
      observe blankOutput segments (ChainState.initial input, blankOutput) =
    some (ChainState.initial input, observe output)
```

Here `plan : Checkpoint.Cost.SegmentPlan steps segments`. The companion theorem
`exists_completes_segmentPlan_with_dump_count` proves that the pre-cleanup chain
has exactly `segments - 1` intermediate dumps.

### Bennett three-tape simulator

```lean
Turing.Simulator.central_correctness :
  normal.accepts input →
  Standard.ComputesIn source normal.start normal.finish v input output →
  Turing.Simulator.SimulationCertificate normal enumerate v input output
```

The certificate exposes the complete initial/final configurations, retained
input, copied output, blank history, restored heads, physical/logical control
distinction, target halt, exact `4v + 4λ + 5` run, determinism, and global
reversibility. `Turing.Simulator.terminates_iff_source` proves both directions
of termination equivalence for accepted standard inputs.

Syntax and resource declarations include:

- `Turing.Simulator.control_card` and
  `tableRuleId_card_fullAlphabet` for `2f + 2N + 4` and `4N + 2z + 3`;
- `Turing.Simulator.Resource.fullRules_length` for `4v + 4λ + 5`;
- `Turing.Simulator.HistorySpace.concreteTrace_history_cost` for history;
- `Turing.Simulator.Copy.Resource.copyTrace_work_footprintCard` for copying; and
- `Turing.Simulator.Resource.WorkSupport`
  for the corrected work-footprint `s`/`s + 1` dichotomy.

## Cost conventions

- One source transition executes one quintuple; one target transition executes
  one quadruple.
- An `ExecutionTrace` stores both endpoints and counts successful transitions.
- Head-visited, ever-nonblank, footprint, peak-nonblank, and peak-active cells
  are different measures.
- Copy footprint is `λ + 2`; peak copied data is `λ`.
- History footprint is `v + 1`; peak nonblank history is `v`.
- Complete target work footprint is the source footprint with the final right
  delimiter inserted, so its cardinality is conditionally `s` or `s + 1`.
- Checkpoint temporary cells are
  `v ⌈/⌉ n + (n - 1) * s` for positive `n`. Permanent input/output and ordinary
  live work storage are excluded.
- Checkpoint time is four ideal source passes plus explicit dump I/O. The
  continuous `2 * sqrt(v * s)` relaxation is separately named and proved.

## Adding a computation

1. Define `step : PartialStep α` and prove the needed exact `Runs` statements.
2. Define a `HistoryRecorder step Record`. Its `recover_step` and
   `step_recover` laws must reject forged history as well as undo generated
   history.
3. Apply `computeCopyUncompute` with an explicit observation and blank output.
4. For checkpointing, build a positive `Cost.SegmentPlan`, use
   `Plan.segmentSteps`, and provide a complete restart-state type. A checkpoint
   must contain control, tapes, head positions, and phase when those affect
   resumption.
5. For a Turing instantiation, define the finite source `Machine`, standard
   accepted words, `BennettNormalForm`, and an explicit equivalence enumerating
   `TableRuleId` before applying `Simulator.central_correctness`.

## Limits

- The concrete simulator theorem is scoped to accepted standard inputs and
  explicit normal-form assumptions.
- Abstract checkpoint lists do not implement a tape allocator or an encoded
  dump protocol; concrete dump size and I/O remain caller obligations.
- The paper's concrete Table 2 seven-stage composition, general source
  standardization claim, and one-tape `v²` simulator are not completed.
- Nested logarithmic-space checkpointing is recorded as speculation, not a
  theorem.
- Thermodynamic, chemical, biochemical, and other physical claims are excluded.

See the repository-level [release overview](../README.md),
[conventions](../docs/CONVENTIONS.md),
[traceability matrix](../docs/TRACEABILITY.md), and
[correction log](../docs/CORRECTIONS.md).
