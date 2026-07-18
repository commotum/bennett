# Axiom and Trust Audit

This record covers the verified Lean library at the pinned release versions:

- Lean `v4.31.0` from `formal/lean-toolchain`;
- mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` from
  `formal/lake-manifest.json` and `formal/lakefile.toml`.

`formal/Bennett/Audit.lean` is a diagnostic umbrella over every project audit
leaf.  It is intentionally not imported by `formal/Bennett.lean` or any public
`API.lean` module.  The transition layer has no separate audit leaf; its laws
are exercised by the history audit, and the release umbrella directly audits
its principal finite-inverse theorem.

## Observed Principal Axiom Sets

The following results are the literal output of Lean's `#print axioms` command.
Square brackets denote the complete observed dependency set for that
declaration, not additional assumptions hidden in its theorem signature.

| Layer | Declaration | Observed axioms |
|---|---|---|
| Partial transitions | `PartialStep.AreInverses.iterate` | `[propext, Quot.sound]` |
| Recorded history | `HistoryRecorder.trace_cleanup` | `[propext, Quot.sound]` |
| Copying | `Copy.blankEquiv` | `[propext]` |
| Copying no-go result | `Copy.injective_of_reversible_outputOnly` | `[propext, Quot.sound]` |
| Compute-copy-uncompute | `Uncompute.computeCopyUncompute_apply_of_run_halted` | `[propext, Quot.sound]` |
| Compute-copy-uncompute | `Uncompute.computeCopyUncompute_reversible` | `[propext, Quot.sound]` |
| Turing semantics | `Turing.Standard.computes_output_unique` | `[propext, Classical.choice, Quot.sound]` |
| Execution traces | `ExecutionTrace.runs_iff_exists_run` | `[propext, Quot.sound]` |
| Quadruple machines | `Turing.QuadrupleMachine.step_areInverses` | `[propext, Classical.choice, Quot.sound]` |
| Split source rules | `Turing.Machine.splitMachine_domainsDisjoint` | `[propext, Quot.sound]` |
| Three-tape simulation | `Turing.Simulator.central_correctness` | `[propext, Classical.choice, Quot.sound]` |
| Halting equivalence | `Turing.Simulator.terminates_iff_source` | `[propext, Classical.choice, Quot.sound]` |
| Work-space accounting | `Turing.Simulator.Resource.WorkSupport.fullTrace_work_footprintPositions_eq_insert_right` | `[propext, Classical.choice, Quot.sound]` |
| Recorded checkpoint segment | `Checkpoint.recordedSegmentStage_apply_of_run` | `[propext, Quot.sound]` |
| Checkpoint cleanup | `Checkpoint.computeCopyCleanup_reversible` | `[propext, Quot.sound]` |
| Discrete checkpoint cost | `Checkpoint.Cost.paperRoundedCells_eq_temporaryCells_add_dumpCells` | `[propext, Classical.choice, Quot.sound]` |
| Continuous relaxation | `Checkpoint.Cost.paperContinuousCells_lower_bound` | `[propext, Classical.choice, Quot.sound]` |
| Segment-plan bridge | `Checkpoint.Plan.computeCopyCleanup_segmentPlan_apply_of_run` | `[propext, Classical.choice, Quot.sound]` |

The checkpoint audit also checks a closed numerical theorem,
`Checkpoint.Audit.CostExamples.checkpoint_time_with_io`, for which Lean reports
no axioms (`[]`).  Other audit leaves print additional supporting declarations;
all observed sets are subsets of the same three foundations.

## Interpretation

The reported names are standard Lean foundations used throughout mathlib:

- `propext` identifies logically equivalent propositions;
- `Classical.choice` supplies classical choice where finite representations,
  quotients, or noncomputable mathematical interfaces require it;
- `Quot.sound` is Lean's quotient soundness principle.

These are accepted kernel-level foundations, not axioms introduced by this
project.  No completed `Bennett` module declares a project-specific `axiom`,
and no principal result depends on `sorryAx`.  Completed modules also contain
no `sorry`, `admit`, or `native_decide` shortcut.

An axiom audit does not replace theorem-signature review.  Source-machine
normal form, accepted-input format, blank-target conditions, exact run lengths,
checkpoint completeness, and resource-model choices remain explicit ordinary
hypotheses in the corresponding declarations.

## Diagnostic Inventory

The umbrella imports these audit leaves:

- `Bennett.History.Audit`;
- `Bennett.Copy.Audit`;
- `Bennett.Uncompute.Audit`;
- `Bennett.Turing.Audit`;
- `Bennett.Turing.Quadruple.Audit`;
- `Bennett.Turing.Simulator.Audit`;
- `Bennett.Checkpoint.Audit`.

They contain executable boundary cases as well as layer-specific
`#print axioms` commands.  Keeping them outside the public root prevents
diagnostic examples and output commands from burdening downstream imports.

## Reproduction

From the repository root:

```bash
cd formal
lake build Bennett.Audit
lake env lean Bennett/Audit.lean
```

The first command builds every diagnostic leaf and the release umbrella.  The
second forces Lean to replay the umbrella's principal `#print axioms` commands
even when Lake's artifacts are already cached.

The release hygiene scans are:

```bash
cd formal
rg -n '(^|:=|by|;)[[:space:]]*(sorry|admit)([[:space:]]|$)|\b(native_decide|sorryAx)\b' \
  Bennett -g '*.lean'
rg -n '^[[:space:]]*axiom[[:space:]]' Bennett -g '*.lean'
rg -n '^import .*Audit' Bennett.lean
rg -n '^import .*Audit' Bennett -g 'API.lean'
awk 'length($0) > 100 { print FILENAME ":" FNR ":" length($0) }' \
  Bennett/Audit.lean
git diff --check
```

The first four `rg` scans should produce no output.  The import scans establish
that the audit modules remain diagnostic-only; `Bennett/Audit.lean` itself is
the deliberate exception and is not in the scanned public roots.
