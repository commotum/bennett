import Bennett.History.Run

/-!
# Recorded-history executable audit

This diagnostic leaf uses a genuinely irreversible list operation: removing a
Boolean head.  Its recorder stores only the discarded bit, not a predecessor
snapshot.  An extra invalid record constructor (`none`) demonstrates that the
backward step rejects malformed history.

Nothing in this file is re-exported by the public API.
-/

namespace Bennett.HistoryAudit

/-- Remove one Boolean head, halting on the empty list. -/
def popStep : PartialStep (List Bool)
  | [] => none
  | _ :: tail => some tail

/-- Instrument `popStep` with the one discarded bit. -/
def popStepWithRecord : List Bool → Option (List Bool × Option Bool)
  | [] => none
  | bit :: tail => some (tail, some bit)

/-- Recover a removed bit; `none` is deliberately an invalid record. -/
def popRecover : Option Bool → List Bool → Option (List Bool)
  | none, _ => none
  | some bit, tail => some (bit :: tail)

/-- A non-snapshot recorder for list-head erasure. -/
def popRecorder : HistoryRecorder popStep (Option Bool) where
  stepWithRecord := popStepWithRecord
  forget_record := by
    intro state
    cases state <;> rfl
  recover := popRecover
  recover_step := by
    intro before after record hrecord
    cases before with
    | nil =>
        change none = some (after, record) at hrecord
        cases hrecord
    | cons bit tail =>
        change some (tail, some bit) = some (after, record) at hrecord
        have hp : (tail, some bit) = (after, record) := Option.some.inj hrecord
        have hafter : tail = after := congrArg Prod.fst hp
        have hrecord' : some bit = record := congrArg Prod.snd hp
        subst after
        subst record
        rfl
  step_recover := by
    intro before after record hrecover
    cases record with
    | none => simp [popRecover] at hrecover
    | some bit =>
        simp [popRecover] at hrecover
        subst before
        rfl

/-- The source is not globally reversible: both one-bit lists step to `[]`. -/
theorem popStep_not_reversible : ¬popStep.Reversible := by
  intro hrev
  have heq : ([false] : List Bool) = [true] :=
    (PartialStep.reversible_iff popStep).mp hrev rfl rfl
  exact (by decide : ([false] : List Bool) ≠ [true]) heq

/-- Recording the discarded bit makes the lifted step globally reversible. -/
theorem recordedPop_reversible : popRecorder.forward.Reversible :=
  popRecorder.forward_reversible

example :
    popRecorder.trace 2 [true, false] =
      some ⟨[], [some false, some true]⟩ :=
  rfl

example :
    popRecorder.backward.iterate 2 ⟨[], [some false, some true]⟩ =
      some ⟨[true, false], []⟩ :=
  rfl

/-- A forged record is outside the backward transition's domain. -/
example : popRecorder.backward ⟨[], [none]⟩ = none :=
  rfl

end Bennett.HistoryAudit

#print axioms Bennett.PartialStep.AreInverses.iterate
#print axioms Bennett.HistoryRecorder.areInverses
#print axioms Bennett.HistoryRecorder.trace_cleanup
#print axioms Bennett.HistoryRecorder.forward_terminates_iff
#print axioms Bennett.HistoryAudit.recordedPop_reversible
