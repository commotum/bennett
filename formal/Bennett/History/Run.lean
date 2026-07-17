import Bennett.History.Core
import Bennett.Transition.Run

/-!
# Runs of recorded transitions

This file proves that history instrumentation preserves the source execution,
adds exactly one record per source transition, and can be run backward for the
same number of steps to restore the exact initial state and history stack.
-/

namespace Bennett
namespace HistoryRecorder

variable {α Record : Type*} {step : PartialStep α}

/-- One recorded step projects to one source step, including undefinedness. -/
theorem forward_current (recorder : HistoryRecorder step Record)
    (state : HistoryState α Record) :
    (recorder.forward state).map HistoryState.current = step state.current := by
  rcases state with ⟨current, history⟩
  rw [← recorder.forget_record current]
  cases hrecord : recorder.stepWithRecord current with
  | none => simp [forward, hrecord]
  | some result =>
      obtain ⟨after, record⟩ := result
      simp [forward, hrecord]

/-- Exact recorded iteration projects to exact source iteration. -/
theorem iterate_forward_current (recorder : HistoryRecorder step Record)
    (n : Nat) (state : HistoryState α Record) :
    (recorder.forward.iterate n state).map HistoryState.current =
      step.iterate n state.current := by
  induction n generalizing state with
  | zero => simp
  | succ n ih =>
      rcases state with ⟨current, history⟩
      cases hrecord : recorder.stepWithRecord current with
      | none =>
          have hsource : step current = none := by
            rw [← recorder.forget_record current]
            simp [hrecord]
          simp [PartialStep.iterate, forward, hrecord, hsource]
      | some result =>
          obtain ⟨after, record⟩ := result
          have hsource : step current = some after :=
            recorder.source_of_stepWithRecord hrecord
          simpa [PartialStep.iterate, forward, hrecord, hsource] using
            ih ⟨after, record :: history⟩

/-- A recorded run always projects to a source run with the same step count. -/
theorem source_run_of_forward_run (recorder : HistoryRecorder step Record)
    {n : Nat} {start finish : HistoryState α Record}
    (hrun : recorder.forward.Runs n start finish) :
    step.Runs n start.current finish.current := by
  have hmapped := congrArg (Option.map HistoryState.current) hrun
  rw [recorder.iterate_forward_current] at hmapped
  simpa [PartialStep.Runs] using hmapped

/-- Every source run lifts from any existing history suffix. -/
theorem exists_forward_run_iff (recorder : HistoryRecorder step Record)
    (n : Nat) (before after : α) (history : List Record) :
    step.Runs n before after ↔
      ∃ history',
        recorder.forward.Runs n ⟨before, history⟩ ⟨after, history'⟩ := by
  constructor
  · intro hrun
    have hmapped :
        (recorder.forward.iterate n ⟨before, history⟩).map HistoryState.current =
          some after := by
      rw [recorder.iterate_forward_current]
      exact hrun
    obtain ⟨finish, hfinish, hcurrent⟩ := Option.map_eq_some_iff.mp hmapped
    rcases finish with ⟨current, history'⟩
    simp only at hcurrent
    subst current
    exact ⟨history', hfinish⟩
  · rintro ⟨history', hrun⟩
    exact recorder.source_run_of_forward_run hrun

/-- Any `n`-step forward run adds exactly `n` records. -/
theorem history_length_of_run (recorder : HistoryRecorder step Record)
    {n : Nat} {start finish : HistoryState α Record}
    (hrun : recorder.forward.Runs n start finish) :
    finish.history.length = start.history.length + n := by
  induction n generalizing start finish with
  | zero =>
      have h : start = finish :=
        (PartialStep.runs_zero_iff recorder.forward start finish).mp hrun
      subst finish
      simp
  | succ n ih =>
      obtain ⟨middle, hfirst, htail⟩ :=
        (PartialStep.runs_succ_iff recorder.forward n start finish).mp hrun
      have hfirstLength := recorder.history_length_of_forward hfirst
      have htailLength := ih htail
      calc
        finish.history.length = middle.history.length + n := htailLength
        _ = (start.history.length + 1) + n := by rw [hfirstLength]
        _ = start.history.length + (n + 1) := by
          simp [Nat.add_comm, Nat.add_left_comm]

/-- Reverse exactly a generated forward run, restoring the full starting state. -/
theorem reverse_run (recorder : HistoryRecorder step Record)
    {n : Nat} {start finish : HistoryState α Record}
    (hrun : recorder.forward.Runs n start finish) :
    recorder.backward.Runs n finish start :=
  (recorder.areInverses.runs_iff n start finish).mp hrun

/-- Forward and backward exact runs are converse relations. -/
theorem runs_iff_backward (recorder : HistoryRecorder step Record)
    (n : Nat) (start finish : HistoryState α Record) :
    recorder.forward.Runs n start finish ↔
      recorder.backward.Runs n finish start :=
  recorder.areInverses.runs_iff n start finish

/-- Run the recorded lift from a source state with initially empty history. -/
def trace (recorder : HistoryRecorder step Record) (n : Nat) (before : α) :
    Option (HistoryState α Record) :=
  recorder.forward.iterate n ⟨before, []⟩

/-- A generated trace has one record per step and cleans up exactly. -/
theorem trace_cleanup (recorder : HistoryRecorder step Record)
    {n : Nat} {before after : α} {history : List Record}
    (htrace : recorder.trace n before = some ⟨after, history⟩) :
    history.length = n ∧
      recorder.backward.iterate n ⟨after, history⟩ = some ⟨before, []⟩ := by
  constructor
  · simpa [trace] using recorder.history_length_of_run htrace
  · exact recorder.reverse_run htrace

/-- Recorded and source execution halt after the same number of successful steps. -/
theorem forward_haltsIn_iff (recorder : HistoryRecorder step Record)
    (n : Nat) (state : HistoryState α Record) :
    recorder.forward.HaltsIn n state ↔ step.HaltsIn n state.current := by
  constructor
  · rintro ⟨finish, hrun, hhalt⟩
    exact ⟨finish.current, recorder.source_run_of_forward_run hrun,
      (recorder.forward_halted_iff finish).mp hhalt⟩
  · rintro ⟨after, hrun, hhalt⟩
    obtain ⟨history', hlift⟩ :=
      (recorder.exists_forward_run_iff n state.current after state.history).mp hrun
    exact ⟨⟨after, history'⟩, hlift,
      (recorder.forward_halted_iff ⟨after, history'⟩).mpr hhalt⟩

/-- Recorded forward execution terminates iff the source execution terminates. -/
theorem forward_terminates_iff (recorder : HistoryRecorder step Record)
    (state : HistoryState α Record) :
    recorder.forward.Terminates state ↔ step.Terminates state.current := by
  constructor
  · rintro ⟨n, hhalt⟩
    exact ⟨n, (recorder.forward_haltsIn_iff n state).mp hhalt⟩
  · rintro ⟨n, hhalt⟩
    exact ⟨n, (recorder.forward_haltsIn_iff n state).mpr hhalt⟩

/-- Recorded forward execution has every finite prefix iff the source does. -/
theorem forward_runsForever_iff (recorder : HistoryRecorder step Record)
    (state : HistoryState α Record) :
    recorder.forward.RunsForever state ↔ step.RunsForever state.current := by
  constructor
  · intro hforever n
    obtain ⟨finish, hrun⟩ := hforever n
    exact ⟨finish.current, recorder.source_run_of_forward_run hrun⟩
  · intro hforever n
    obtain ⟨after, hrun⟩ := hforever n
    obtain ⟨history', hlift⟩ :=
      (recorder.exists_forward_run_iff n state.current after state.history).mp hrun
    exact ⟨⟨after, history'⟩, hlift⟩

end HistoryRecorder
end Bennett
