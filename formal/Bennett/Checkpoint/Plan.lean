import Bennett.Checkpoint.Core
import Bennett.Checkpoint.Cost

/-!
# Source runs split by checkpoint segment plans

This module connects the constructive segment lengths in `Checkpoint.Cost` to
the reversible checkpoint-chain semantics in `Checkpoint.Core`.  A list of
block lengths denotes exact iterates of one source step.  Any source run whose
length is their sum induces a complete checkpoint chain, and the higher-level
copy-cleanup macro retains the observed output while erasing the checkpoint
stack.

Each individual `step.iterate length` has the recorded-history realization
proved by `Checkpoint.recordedSegmentStage_apply_of_run`; this module owns the
orthogonal composition of those source segments into one chain.
-/

namespace Bennett.Checkpoint.Plan

variable {Alpha : Type*}

/-- Turn block lengths into exact source-step segment partial computations. -/
def segmentSteps (step : PartialStep Alpha) (lengths : List Nat) :
    List (PartialStep Alpha) :=
  lengths.map step.iterate

@[simp] theorem segmentSteps_length
    (step : PartialStep Alpha) (lengths : List Nat) :
    (segmentSteps step lengths).length = lengths.length := by
  simp [segmentSteps]

/-!
The induction below keeps the already-consumed prefix explicit.  Consequently
the live chain index selects the head of the remaining suffix from the one
fixed complete segment table.
-/

private theorem exists_suffix_run
    [DecidableEq Alpha]
    (step : PartialStep Alpha) (consumed suffix : List Nat)
    {before : ChainState Alpha} {input output : Alpha}
    (hcompleted : before.completed = consumed.length)
    (hcurrent : before.current = input)
    (hwellFormed : before.WellFormed)
    (hrun : step.Runs suffix.sum input output) :
    ∃ after : ChainState Alpha,
      (forward (segmentSteps step (consumed ++ suffix))).Runs
          suffix.length before after ∧
        after.current = output := by
  induction suffix generalizing consumed before input with
  | nil =>
      have hinput : input = output :=
        (PartialStep.runs_zero_iff step input output).mp (by simpa using hrun)
      subst output
      exact ⟨before, PartialStep.runs_refl _ _, hcurrent⟩
  | cons length lengths ih =>
      have hsource : step.Runs (length + lengths.sum) input output := by
        simpa using hrun
      obtain ⟨middle, hfirst, htail⟩ :=
        (PartialStep.runs_add_iff step length lengths.sum input output).mp
          hsource
      let nextState := before.recordNext middle
      have hselected :
          (segmentSteps step
            (consumed ++ length :: lengths))[before.completed]? =
            some (step.iterate length) := by
        rw [hcompleted]
        simp [segmentSteps]
      have hforward :
          forward (segmentSteps step (consumed ++ length :: lengths)) before =
            some nextState := by
        apply (forward_eq_some_iff _ _ _).mpr
        refine ⟨hwellFormed.1, step.iterate length, middle,
          hselected, ?_, rfl⟩
        simpa [PartialStep.Runs, hcurrent] using hfirst
      have hnextCompleted :
          nextState.completed = (consumed ++ [length]).length := by
        simp [nextState, hcompleted]
      have hnextCurrent : nextState.current = middle := by
        simp [nextState]
      have hnextWellFormed : nextState.WellFormed :=
        ChainState.recordNext_wellFormed hwellFormed middle
      obtain ⟨after, htailChain, hafter⟩ :=
        ih (consumed ++ [length]) hnextCompleted hnextCurrent
          hnextWellFormed htail
      have htailChain' :
          (forward (segmentSteps step (consumed ++ length :: lengths))).Runs
            lengths.length nextState after := by
        simpa [List.append_assoc] using htailChain
      refine ⟨after, ?_, hafter⟩
      simpa using
        (PartialStep.runs_succ_iff
          (forward (segmentSteps step (consumed ++ length :: lengths)))
          lengths.length before after).mpr
            ⟨nextState, hforward, htailChain'⟩

/-- Any exact source run split by `lengths` induces a full checkpoint chain. -/
theorem exists_completes_segmentSteps
    [DecidableEq Alpha]
    (step : PartialStep Alpha) (lengths : List Nat)
    {input output : Alpha}
    (hrun : step.Runs lengths.sum input output) :
    ∃ terminal : ChainState Alpha,
      Completes (segmentSteps step lengths) input terminal ∧
        terminal.current = output := by
  obtain ⟨terminal, hcomplete, hcurrent⟩ :=
    exists_suffix_run step [] lengths
      (before := ChainState.initial input)
      (input := input) (output := output)
      (by simp [ChainState.initial])
      (by simp [ChainState.initial])
      (ChainState.initial_wellFormed input) hrun
  refine ⟨terminal, ?_, hcurrent⟩
  simpa [Completes] using hcomplete

/-- The induced terminal contains exactly one fewer intermediate dump. -/
theorem exists_completes_segmentSteps_with_dump_count
    [DecidableEq Alpha]
    (step : PartialStep Alpha) (lengths : List Nat)
    {input output : Alpha}
    (hrun : step.Runs lengths.sum input output) :
    ∃ terminal : ChainState Alpha,
      Completes (segmentSteps step lengths) input terminal ∧
        terminal.current = output ∧
        terminal.intermediateDumps.length = lengths.length - 1 := by
  obtain ⟨terminal, hcomplete, hcurrent⟩ :=
    exists_completes_segmentSteps step lengths hrun
  refine ⟨terminal, hcomplete, hcurrent, ?_⟩
  simpa [segmentSteps] using dump_count_of_completes _ hcomplete

/-- Higher-level copy-cleanup retains the source input and observed output
    while deleting the complete checkpoint stack. -/
theorem computeCopyCleanup_segmentSteps_apply_of_run
    {Beta : Type*} [DecidableEq Alpha] [DecidableEq Beta]
    (step : PartialStep Alpha) (lengths : List Nat)
    (observe : Alpha → Beta) (blankOutput : Beta)
    {input output : Alpha}
    (hrun : step.Runs lengths.sum input output) :
    computeCopyCleanup
        (segmentSteps step lengths) observe blankOutput lengths.length
        (ChainState.initial input, blankOutput) =
      some (ChainState.initial input, observe output) := by
  obtain ⟨terminal, hcomplete, hcurrent⟩ :=
    exists_completes_segmentSteps step lengths hrun
  have hcleanup := computeCopyCleanup_initial_of_completes
    (segmentSteps step lengths) observe blankOutput hcomplete
  simpa [hcurrent] using hcleanup

/-! ## Direct bridge from the constructive cost plan -/

/-- A cost-model plan whose lengths sum to `steps` produces a complete
    semantic chain, the requested output, and exactly `segments - 1` dumps. -/
theorem exists_completes_segmentPlan_with_dump_count
    [DecidableEq Alpha]
    (step : PartialStep Alpha)
    {steps segments : Nat} (plan : Cost.SegmentPlan steps segments)
    {input output : Alpha}
    (hrun : step.Runs steps input output) :
    ∃ terminal : ChainState Alpha,
      Completes (segmentSteps step plan.lengths) input terminal ∧
        terminal.current = output ∧
        terminal.intermediateDumps.length = segments - 1 := by
  have hsplit : step.Runs plan.lengths.sum input output := by
    simpa [plan.sum_eq] using hrun
  obtain ⟨terminal, hcomplete, hcurrent, hdumps⟩ :=
    exists_completes_segmentSteps_with_dump_count
      step plan.lengths hsplit
  refine ⟨terminal, hcomplete, hcurrent, ?_⟩
  simpa [plan.length_eq] using hdumps

/-- The plan-driven higher-level macro retains the original input and observed
    output and removes all `segments - 1` intermediate checkpoints. -/
theorem computeCopyCleanup_segmentPlan_apply_of_run
    {Beta : Type*} [DecidableEq Alpha] [DecidableEq Beta]
    (step : PartialStep Alpha)
    {steps segments : Nat} (plan : Cost.SegmentPlan steps segments)
    (observe : Alpha → Beta) (blankOutput : Beta) {input output : Alpha}
    (hrun : step.Runs steps input output) :
    computeCopyCleanup
        (segmentSteps step plan.lengths) observe blankOutput segments
        (ChainState.initial input, blankOutput) =
      some (ChainState.initial input, observe output) := by
  have hsplit : step.Runs plan.lengths.sum input output := by
    simpa [plan.sum_eq] using hrun
  simpa [plan.length_eq] using
    (computeCopyCleanup_segmentSteps_apply_of_run
      step plan.lengths observe blankOutput hsplit)

end Bennett.Checkpoint.Plan
