import Bennett.History.Core
import Bennett.Turing.Source.Determinism
import Bennett.Turing.Source.Inverse

/-!
# Rule-ID history recorder for source machines

For a syntactically deterministic source table, the selected intrinsic rule ID
is exactly the information needed to invert a successful source step.  This
instantiates the model-independent `HistoryRecorder` used by the concrete
three-tape simulator.
-/

namespace Bennett.Turing
namespace Machine

variable {Control Symbol : Type*}

/-- Execute the selected source rule and return its intrinsic rule ID. -/
def stepWithRuleId [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) :
    Configuration Control Symbol →
      Option (Configuration Control Symbol × machine.RuleId) :=
  fun config => (machine.select config).map fun ruleId =>
    ((machine.rule ruleId).execute config, ruleId)

/-- Recover through one named rule, rejecting endpoints outside its range. -/
def recoverRule [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) (ruleId : machine.RuleId)
    (after : Configuration Control Symbol) :
    Option (Configuration Control Symbol) :=
  if (machine.rule ruleId).UndoMatches after then
    some ((machine.rule ruleId).undo after)
  else none

theorem stepWithRuleId_forget [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) (config : Configuration Control Symbol) :
    (machine.stepWithRuleId config).map Prod.fst = machine.step config := by
  cases hselect : machine.select config <;>
    simp [stepWithRuleId, Machine.step, hselect]

theorem stepWithRuleId_eq_some_iff
    [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol)
    (before after : Configuration Control Symbol) (ruleId : machine.RuleId) :
    machine.stepWithRuleId before = some (after, ruleId) ↔
      machine.select before = some ruleId ∧
        (machine.rule ruleId).execute before = after := by
  simp only [stepWithRuleId, Option.map_eq_some_iff]
  constructor
  · rintro ⟨selected, hselect, hpair⟩
    have hid : selected = ruleId := congrArg Prod.snd hpair
    subst selected
    exact ⟨hselect, congrArg Prod.fst hpair⟩
  · rintro ⟨hselect, hafter⟩
    exact ⟨ruleId, hselect, by simp [hafter]⟩

theorem recoverRule_of_recorded
    [DecidableEq Control] [DecidableEq Symbol]
    {machine : Machine Control Symbol}
    {before after : Configuration Control Symbol} {ruleId : machine.RuleId}
    (hrecord : machine.stepWithRuleId before = some (after, ruleId)) :
    machine.recoverRule ruleId after = some before := by
  obtain ⟨hselect, hafter⟩ :=
    (machine.stepWithRuleId_eq_some_iff before after ruleId).mp hrecord
  have hmatches := machine.select_matches before hselect
  subst after
  simp [recoverRule, Quintuple.undoMatches_execute,
    Quintuple.undo_execute hmatches]

theorem recorded_of_recoverRule
    [DecidableEq Control] [DecidableEq Symbol]
    {machine : Machine Control Symbol}
    (hdet : machine.SyntacticallyDeterministic)
    {before after : Configuration Control Symbol} {ruleId : machine.RuleId}
    (hrecover : machine.recoverRule ruleId after = some before) :
    machine.stepWithRuleId before = some (after, ruleId) := by
  unfold recoverRule at hrecover
  split at hrecover
  · rename_i hundo
    have hbefore : (machine.rule ruleId).undo after = before :=
      Option.some.inj hrecover
    have hmatchesUndo := Quintuple.matches_undo
      (rule := machine.rule ruleId) (config := after)
    have hmatches : (machine.rule ruleId).Matches before := by
      simpa [← hbefore] using hmatchesUndo
    have hafter : (machine.rule ruleId).execute before = after := by
      rw [← hbefore]
      exact Quintuple.execute_undo hundo
    cases hselect : machine.select before with
    | none =>
        exact False.elim
          ((machine.select_eq_none_iff before).mp hselect ruleId hmatches)
    | some selected =>
        have hselected := machine.select_matches before hselect
        have hid : selected = ruleId :=
          hdet.eq_of_matches before hselected hmatches
        subst selected
        exact (machine.stepWithRuleId_eq_some_iff before after ruleId).mpr
          ⟨hselect, hafter⟩
  · simp at hrecover

/-- The concrete rule-ID instantiation of the abstract history interface. -/
def historyRecorder [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol)
    (hdet : machine.SyntacticallyDeterministic) :
    HistoryRecorder machine.step machine.RuleId where
  stepWithRecord := machine.stepWithRuleId
  forget_record := machine.stepWithRuleId_forget
  recover := machine.recoverRule
  recover_step := by
    intro before after record hrecord
    exact recoverRule_of_recorded (machine := machine) hrecord
  step_recover := by
    intro before after record hrecover
    exact recorded_of_recoverRule (machine := machine) hdet hrecover

end Machine
end Bennett.Turing
