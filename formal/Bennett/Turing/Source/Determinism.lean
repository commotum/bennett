import Bennett.Turing.Source.Core

/-!
# Syntactic determinism and executable selection

The executable `Option` step is extensionally deterministic even for a malformed
overlapping table because it chooses one rule.  The theorems below prove the
separate fact Bennett needs: unique rule keys make the declarative all-rule
relation right-unique and make it coincide with executable selection.
-/

namespace Bennett.Turing
namespace Machine

variable {Control Symbol : Type*}

theorem select_matches [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) (config : Configuration Control Symbol)
    {index : machine.RuleId} (hselect : machine.select config = some index) :
    (machine.rule index).Matches config := by
  have hmem : index ∈ machine.select config := by simp [hselect]
  have hdecide := (Fin.mem_find?_iff.mp hmem).1
  exact of_decide_eq_true hdecide

theorem select_eq_none_iff [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) (config : Configuration Control Symbol) :
    machine.select config = none ↔
      ∀ index : machine.RuleId, ¬(machine.rule index).Matches config := by
  simp [select, Fin.find?_decide_eq_dite]

theorem SyntacticallyDeterministic.eq_of_matches
    {machine : Machine Control Symbol} (hdet : machine.SyntacticallyDeterministic)
    (config : Configuration Control Symbol) {first second : machine.RuleId}
    (hfirst : (machine.rule first).Matches config)
    (hsecond : (machine.rule second).Matches config) : first = second := by
  apply hdet
  exact Prod.ext (hfirst.1.trans hsecond.1.symm)
    (hfirst.2.trans hsecond.2.symm)

theorem SyntacticallyDeterministic.stepRel_rightUnique
    {machine : Machine Control Symbol} (hdet : machine.SyntacticallyDeterministic) :
    Relator.RightUnique machine.StepRel := by
  intro before after₁ after₂ h₁ h₂
  obtain ⟨first, hfirst, rfl⟩ := h₁
  obtain ⟨second, hsecond, hafter⟩ := h₂
  have hindex : first = second := hdet.eq_of_matches before hfirst hsecond
  subst second
  exact hafter

theorem step_eq_none_iff [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) (config : Configuration Control Symbol) :
    machine.step config = none ↔
      ∀ index : machine.RuleId, ¬(machine.rule index).Matches config := by
  rw [step]
  simp only [Option.map_eq_none_iff]
  exact machine.select_eq_none_iff config

theorem step_eq_some_of_select [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) (config : Configuration Control Symbol)
    {index : machine.RuleId} (hselect : machine.select config = some index) :
    machine.step config = some ((machine.rule index).execute config) := by
  simp [step, hselect]

theorem SyntacticallyDeterministic.step_eq_some_iff
    [DecidableEq Control] [DecidableEq Symbol]
    {machine : Machine Control Symbol} (hdet : machine.SyntacticallyDeterministic)
    (before after : Configuration Control Symbol) :
    machine.step before = some after ↔ machine.StepRel before after := by
  constructor
  · intro hstep
    unfold step at hstep
    obtain ⟨index, hselect, hafter⟩ := Option.map_eq_some_iff.mp hstep
    exact ⟨index, machine.select_matches before hselect, hafter⟩
  · rintro ⟨index, hmatches, rfl⟩
    cases hselect : machine.select before with
    | none =>
        exact False.elim
          ((machine.select_eq_none_iff before).mp hselect index hmatches)
    | some selected =>
        have hselected := machine.select_matches before hselect
        have heq : selected = index :=
          hdet.eq_of_matches before hselected hmatches
        subst selected
        exact machine.step_eq_some_of_select before hselect

end Machine
end Bennett.Turing
