import Bennett.Transition.Core
import Mathlib.Data.List.Basic

/-!
# Recorded reversible transitions

A `HistoryRecorder` instruments a source step with one explicit recovery record.
Its two recovery laws say that generated records recover their predecessor and
that every accepted `(record, successor)` pair is canonical for a genuine
instrumented step.  The second law is what makes backward execution reject
forged histories and yields a true two-sided partial inverse.
-/

namespace Bennett

/-- A source state paired with a newest-first stack of history records. -/
structure HistoryState (α : Type*) (Record : Type*) where
  current : α
  history : List Record
  deriving DecidableEq, Repr

/--
Executable instrumentation and predecessor recovery for a partial source step.

No bound on `Record` is assumed.  Concrete storage theorems must establish the
size of their own record type rather than infer compactness from this interface.
-/
structure HistoryRecorder {α : Type*} (step : PartialStep α) (Record : Type*) where
  stepWithRecord : α → Option (α × Record)
  forget_record : ∀ state, (stepWithRecord state).map Prod.fst = step state
  recover : Record → α → Option α
  recover_step : ∀ ⦃before after record⦄,
    stepWithRecord before = some (after, record) → recover record after = some before
  step_recover : ∀ ⦃before after record⦄,
    recover record after = some before → stepWithRecord before = some (after, record)

namespace HistoryRecorder

variable {α Record : Type*} {step : PartialStep α}
variable {before after : α} {record : Record}

/-- Execute one source transition and push its recovery record. -/
def forward (recorder : HistoryRecorder step Record) :
    PartialStep (HistoryState α Record)
  | ⟨before, history⟩ =>
      match recorder.stepWithRecord before with
      | none => none
      | some (after, record) => some ⟨after, record :: history⟩

/-- Pop one record and recover the corresponding predecessor. -/
def backward (recorder : HistoryRecorder step Record) :
    PartialStep (HistoryState α Record)
  | ⟨_, []⟩ => none
  | ⟨after, record :: history⟩ =>
      match recorder.recover record after with
      | none => none
      | some before => some ⟨before, history⟩

/-- A recorded transition projects to the declared source transition. -/
theorem source_of_stepWithRecord (recorder : HistoryRecorder step Record)
    (hrecord : recorder.stepWithRecord before = some (after, record)) :
    step before = some after := by
  rw [← recorder.forget_record before]
  simp [hrecord]

/-- Every successful source step has some instrumenting record. -/
theorem exists_stepWithRecord_iff (recorder : HistoryRecorder step Record)
    (before after : α) :
    (∃ record, recorder.stepWithRecord before = some (after, record)) ↔
      step before = some after := by
  constructor
  · rintro ⟨record, hrecord⟩
    exact recorder.source_of_stepWithRecord hrecord
  · intro hstep
    rw [← recorder.forget_record before] at hstep
    obtain ⟨result, hresult, hcurrent⟩ := Option.map_eq_some_iff.mp hstep
    obtain ⟨current, record⟩ := result
    simp only at hcurrent
    subst current
    exact ⟨record, hresult⟩

theorem forward_of_stepWithRecord (recorder : HistoryRecorder step Record)
    (hrecord : recorder.stepWithRecord before = some (after, record))
    (history : List Record) :
    recorder.forward ⟨before, history⟩ =
      some ⟨after, record :: history⟩ := by
  simp [forward, hrecord]

theorem backward_of_recover (recorder : HistoryRecorder step Record)
    (hrecover : recorder.recover record after = some before)
    (history : List Record) :
    recorder.backward ⟨after, record :: history⟩ =
      some ⟨before, history⟩ := by
  simp [backward, hrecover]

/-- A generated recorded step is undone by one backward step. -/
theorem backward_forward (recorder : HistoryRecorder step Record)
    (hrecord : recorder.stepWithRecord before = some (after, record))
    (history : List Record) :
    recorder.backward ⟨after, record :: history⟩ =
      some ⟨before, history⟩ :=
  recorder.backward_of_recover (recorder.recover_step hrecord) history

/-- Every accepted backward step is replayed by one forward step. -/
theorem forward_backward (recorder : HistoryRecorder step Record)
    (hrecover : recorder.recover record after = some before)
    (history : List Record) :
    recorder.forward ⟨before, history⟩ =
      some ⟨after, record :: history⟩ :=
  recorder.forward_of_stepWithRecord (recorder.step_recover hrecover) history

/-- Any successful recorded forward result can be undone. -/
theorem backward_of_forward_eq (recorder : HistoryRecorder step Record)
    {start finish : HistoryState α Record}
    (hforward : recorder.forward start = some finish) :
    recorder.backward finish = some start := by
  rcases start with ⟨before, history⟩
  cases hrecord : recorder.stepWithRecord before with
  | none => simp [forward, hrecord] at hforward
  | some result =>
      obtain ⟨after, record⟩ := result
      have hfinish : finish = ⟨after, record :: history⟩ := by
        simpa [forward, hrecord] using hforward.symm
      subst finish
      exact recorder.backward_forward hrecord history

/-- Any successful backward result can be replayed forward. -/
theorem forward_of_backward_eq (recorder : HistoryRecorder step Record)
    {finish start : HistoryState α Record}
    (hbackward : recorder.backward finish = some start) :
    recorder.forward start = some finish := by
  rcases finish with ⟨after, history⟩
  cases history with
  | nil => simp [backward] at hbackward
  | cons record history =>
      cases hrecover : recorder.recover record after with
      | none => simp [backward, hrecover] at hbackward
      | some before =>
          have hstart : start = ⟨before, history⟩ := by
            simpa [backward, hrecover] using hbackward.symm
          subst start
          exact recorder.forward_backward hrecover history

/-- The recorded forward and backward steps have converse graphs globally. -/
theorem areInverses (recorder : HistoryRecorder step Record) :
    recorder.forward.AreInverses recorder.backward := by
  intro start finish
  exact ⟨recorder.backward_of_forward_eq, recorder.forward_of_backward_eq⟩

/-- The recorded lift as mathlib's executable partial equivalence. -/
def inversePair (recorder : HistoryRecorder step Record) :
    PartialStep.InversePair (HistoryState α Record) :=
  recorder.areInverses.toInversePair

theorem forward_reversible (recorder : HistoryRecorder step Record) :
    recorder.forward.Reversible :=
  recorder.areInverses.forward_reversible

theorem backward_reversible (recorder : HistoryRecorder step Record) :
    recorder.backward.Reversible :=
  recorder.areInverses.backward_reversible

/-- Forward execution is enabled exactly when the source execution is enabled. -/
theorem forward_halted_iff (recorder : HistoryRecorder step Record)
    (state : HistoryState α Record) :
    recorder.forward.Halted state ↔ step.Halted state.current := by
  rcases state with ⟨current, history⟩
  change recorder.forward ⟨current, history⟩ = none ↔ step current = none
  rw [← recorder.forget_record current]
  cases hrecord : recorder.stepWithRecord current with
  | none => simp [forward, hrecord]
  | some result =>
      obtain ⟨after, record⟩ := result
      simp [forward, hrecord]

@[simp]
theorem backward_empty_halted (recorder : HistoryRecorder step Record) (current : α) :
    recorder.backward.Halted ⟨current, []⟩ :=
  rfl

theorem backward_cons_halted_iff (recorder : HistoryRecorder step Record)
    (current : α) (record : Record) (history : List Record) :
    recorder.backward.Halted ⟨current, record :: history⟩ ↔
      recorder.recover record current = none := by
  cases hrecover : recorder.recover record current <;>
    simp [PartialStep.Halted, backward, hrecover]

/-- One recorded forward step adds exactly one history entry. -/
theorem history_length_of_forward (recorder : HistoryRecorder step Record)
    {start finish : HistoryState α Record}
    (hforward : recorder.forward start = some finish) :
    finish.history.length = start.history.length + 1 := by
  rcases start with ⟨before, history⟩
  cases hrecord : recorder.stepWithRecord before with
  | none => simp [forward, hrecord] at hforward
  | some result =>
      obtain ⟨after, record⟩ := result
      have hfinish : finish = ⟨after, record :: history⟩ := by
        simpa [forward, hrecord] using hforward.symm
      subst finish
      simp

end HistoryRecorder
end Bennett
