import Bennett.Checkpoint.API
import Mathlib.Tactic.NormNum

/-!
# Executable checkpoint audit

The examples below exercise uneven integer segmentation, the corrected
`segments - 1` dump count, explicit dump-I/O time, checkpoint-chain inverse
validation, primary-history cleanup for an irreversible source step, and the
bridge from a cost-model `SegmentPlan` to semantic compute-copy-cleanup.

Nothing in this diagnostic module is re-exported by the public API.
-/

namespace Bennett.Checkpoint.Audit

namespace CostExamples

open Cost

/-- Uneven division `10 = 4 + 3 + 3` realizes the ceiling capacity `4`. -/
def unevenPlan : SegmentPlan 10 3 where
  lengths := [4, 3, 3]
  length_eq := rfl
  sum_eq := rfl
  le_historyCells := by
    intro length hlength
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlength
    rcases hlength with rfl | rfl | rfl <;>
      norm_num [historyCells, Nat.ceilDiv_eq_add_pred_div]

theorem uneven_capacity : historyCells 10 3 = 4 := by decide

theorem uneven_temporary_cells : temporaryCells 10 7 3 = 18 := by decide

theorem paper_rounded_cells : paperRoundedCells 10 7 3 = 25 := by decide

/-- The paper's three-dump convention is one seven-cell dump larger. -/
theorem paper_extra_dump :
    paperRoundedCells 10 7 3 = temporaryCells 10 7 3 + 7 := by
  exact paperRoundedCells_eq_temporaryCells_add_dumpCells 10 7 (by decide)

/-- Four source passes plus two seven-cell dumps charged twice per cell. -/
theorem checkpoint_time_with_io : checkpointTime 10 7 3 2 = 68 := by decide

theorem checkpoint_time_ignoring_io :
    checkpointTime 10 7 3 0 = 2 * unsegmentedIdealTime 10 :=
  checkpointTime_ignoring_dumpIO 10 7 3

theorem ceilSqrt_ten : ceilSqrt 10 = 4 := by
  apply Nat.le_antisymm
  · exact ceilSqrt_le_iff.mpr (by norm_num)
  · by_contra hnot
    have hle : ceilSqrt 10 ≤ 3 := by omega
    have := ceilSqrt_le_iff.mp hle
    omega

theorem balanced_segments_forty_ten : balancedSegments 40 10 = 2 := by
  change max 1 (ceilSqrt 4) = 2
  have hsqrt : ceilSqrt 4 = 2 := by
    apply Nat.le_antisymm
    · exact ceilSqrt_le_iff.mpr (by norm_num)
    · by_contra hnot
      have hle : ceilSqrt 4 ≤ 1 := by omega
      have := ceilSqrt_le_iff.mp hle
      omega
  simp [hsqrt]

/-- The real relaxation attains its lower bound at `n = 2` for `v = 4,s = 1`. -/
theorem continuous_relaxation_four_one :
    paperContinuousCells 4 1 2 = 2 * Real.sqrt (4 * 1) := by
  have h := paperContinuousCells_at_sqrt_ratio
    (steps := (4 : Real)) (dumpCells := (1 : Real))
    (by norm_num) (by norm_num)
  have hsqrt : Real.sqrt (4 : Real) = 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  simpa [paperContinuousCells, hsqrt] using h

end CostExamples

namespace CoreExamples

open Bennett

def add (increment : Nat) : PartialStep Nat :=
  fun value => some (value + increment)

def tinySegments : List (PartialStep Nat) := [add 1, add 2, add 3]

def state0 : ChainState Nat := ChainState.initial 10
def state1 : ChainState Nat := ⟨10, 11, 1, []⟩
def state2 : ChainState Nat := ⟨10, 13, 2, [11]⟩
def state3 : ChainState Nat := ⟨10, 16, 3, [13, 11]⟩

example : forward tinySegments state0 = some state1 := by rfl
example : forward tinySegments state1 = some state2 := by rfl
example : forward tinySegments state2 = some state3 := by rfl

example : backward tinySegments state3 = some state2 := by rfl
example : backward tinySegments state2 = some state1 := by rfl
example : backward tinySegments state1 = some state0 := by rfl

/-- A forged predecessor dump is rejected by the checked inverse. -/
theorem forged_dump_rejected :
    backward tinySegments (⟨10, 13, 2, [12]⟩ : ChainState Nat) = none := by
  rfl

theorem tiny_run : (forward tinySegments).Runs 3 state0 state3 := by
  rfl

theorem tiny_dump_count :
    state3.intermediateDumps.length = tinySegments.length - 1 :=
  dump_count_of_completes tinySegments tiny_run

/-- The chain is recomputed, copied, and restored with every dump erased. -/
theorem tiny_compute_copy_cleanup :
    computeCopyCleanup tinySegments id 0 3 (state0, 0) =
      some (state0, 16) := by
  simpa [state3] using
    computeCopyCleanup_apply_of_run tinySegments id 0 tiny_run

/-- The inverse checks and removes the retained output. -/
theorem tiny_compute_copy_cleanup_inverse :
    (computeCopyCleanup tinySegments id 0 3).symm (state0, 16) =
      some (state0, 0) := by
  simpa [state3] using
    computeCopyCleanup_symm_apply_of_run tinySegments id 0 tiny_run

def localStage : Frame Nat Nat Nat ≃. Frame Nat Nat Nat :=
  stage id (fun value => value + 1) 0 0 (PEquiv.refl Nat)

example : localStage ((5, 0), 0) = some ((5, 0), 6) := by rfl
example : localStage.symm ((5, 0), 6) = some ((5, 0), 0) := by rfl

/-- A forged retained observation is rejected. -/
example : localStage.symm ((5, 0), 7) = none := by rfl

end CoreExamples

namespace RecordedSegmentExamples

open Bennett

/-- An irreversible source step: both Boolean states are overwritten by `true`. -/
def setTrue : PartialStep Bool := fun _ => some true

theorem setTrue_not_reversible : ¬setTrue.Reversible := by
  intro hreversible
  have heq := (PartialStep.reversible_iff setTrue).mp hreversible
    (before₁ := false) (before₂ := true) (after := true) rfl rfl
  exact (by decide : false ≠ true) heq

/-- Recording the overwritten predecessor makes the step recoverable. -/
def setTrueRecorder : HistoryRecorder setTrue Bool where
  stepWithRecord before := some (true, before)
  forget_record := by intro before; rfl
  recover record after := if after = true then some record else none
  recover_step := by
    intro before after record hrecord
    simp only [Option.some.injEq, Prod.mk.injEq] at hrecord
    rcases hrecord with ⟨rfl, rfl⟩
    simp
  step_recover := by
    intro before after record hrecover
    cases after <;> simp_all

def blankHistory : HistoryState Bool Bool := ⟨false, []⟩

theorem setTrue_run : setTrue.Runs 1 false true := rfl

/-- Primary history is generated, retraced, and erased within the stage. -/
theorem recorded_stage_cleans_history :
    recordedSegmentStage setTrueRecorder blankHistory false 1
        ((false, blankHistory), false) =
      some ((false, blankHistory), true) :=
  recordedSegmentStage_apply_of_run
    setTrueRecorder blankHistory false setTrue_run

theorem recorded_stage_inverse_cleans_dump :
    (recordedSegmentStage setTrueRecorder blankHistory false 1).symm
        ((false, blankHistory), true) =
      some ((false, blankHistory), false) :=
  recordedSegmentStage_symm_cleanup_of_run
    setTrueRecorder blankHistory false setTrue_run

end RecordedSegmentExamples

namespace PlanExamples

open Bennett

def unitStep : PartialStep Nat := fun value => some (value + 1)

theorem unitStep_runs_ten : unitStep.Runs 10 0 10 := by rfl

/-- The explicit uneven cost plan yields three segments and two live dumps. -/
theorem uneven_plan_completes :
    ∃ terminal : ChainState Nat,
      Completes
          (Plan.segmentSteps unitStep CostExamples.unevenPlan.lengths)
          0 terminal ∧
        terminal.current = 10 ∧
        terminal.intermediateDumps.length = 2 := by
  simpa using
    Plan.exists_completes_segmentPlan_with_dump_count
      unitStep CostExamples.unevenPlan unitStep_runs_ten

/-- The plan bridge retains input/output and deletes both intermediate dumps. -/
theorem uneven_plan_compute_copy_cleanup :
    computeCopyCleanup
        (Plan.segmentSteps unitStep CostExamples.unevenPlan.lengths)
        id 0 3 (ChainState.initial 0, 0) =
      some (ChainState.initial 0, 10) := by
  simpa using
    Plan.computeCopyCleanup_segmentPlan_apply_of_run
      unitStep CostExamples.unevenPlan id 0 unitStep_runs_ten

end PlanExamples

#print axioms CostExamples.paper_extra_dump
#print axioms CostExamples.checkpoint_time_with_io
#print axioms CostExamples.continuous_relaxation_four_one
#print axioms CoreExamples.forged_dump_rejected
#print axioms CoreExamples.tiny_compute_copy_cleanup
#print axioms RecordedSegmentExamples.setTrue_not_reversible
#print axioms RecordedSegmentExamples.recorded_stage_cleans_history
#print axioms PlanExamples.uneven_plan_completes
#print axioms PlanExamples.uneven_plan_compute_copy_cleanup

#print axioms Cost.exists_segmentPlan
#print axioms Cost.exists_positive_segmentPlan
#print axioms Cost.paperRoundedCells_eq_temporaryCells_add_dumpCells
#print axioms Cost.checkpointTime_eq_two_unsegmented_add_dumpIO
#print axioms Cost.ceilSqrt_le_iff
#print axioms Cost.balancedSegments_le_of_cover
#print axioms Cost.paperContinuousCells_lower_bound
#print axioms Cost.paperContinuousCells_at_sqrt_ratio
#print axioms stage_apply_of_segment
#print axioms stage_symm_cleanup_of_segment
#print axioms recordedSegmentStage_apply_of_run
#print axioms recordedSegmentStage_symm_cleanup_of_run
#print axioms areInverses
#print axioms run_from_initial_shape
#print axioms computeCopyCleanup_apply_of_run
#print axioms computeCopyCleanup_symm_apply_of_run
#print axioms computeCopyCleanup_initial_of_completes
#print axioms computeCopyCleanup_reversible
#print axioms cleanup_of_completes
#print axioms Plan.exists_completes_segmentPlan_with_dump_count
#print axioms Plan.computeCopyCleanup_segmentPlan_apply_of_run

end Bennett.Checkpoint.Audit
