import Bennett.Turing.Quadruple.Overlap

/-!
# Finite machines of quadruples

Individual quadruples are partial bijections, but a table is deterministic or
reversible only when distinct rule domains or ranges, respectively, are
disjoint.  Executable least-index selection remains separate from the
existential all-rule relation until domain disjointness proves agreement.
-/

namespace Bennett.Turing

/-- Finite target syntax with intrinsic rule identifiers. -/
structure QuadrupleMachine (Control TapeIndex : Type*)
    (Symbol : TapeIndex → Type*) where
  ruleCount : Nat
  rule : Fin ruleCount → Quadruple Control TapeIndex Symbol

namespace QuadrupleMachine

variable {Control TapeIndex : Type*} {Symbol : TapeIndex → Type*}

/-- Intrinsic target-rule identifier type. -/
abbrev RuleId (machine : QuadrupleMachine Control TapeIndex Symbol) :=
  Fin machine.ruleCount

@[simp] theorem ruleId_card
    (machine : QuadrupleMachine Control TapeIndex Symbol) :
    Fintype.card machine.RuleId = machine.ruleCount :=
  Fintype.card_fin machine.ruleCount

/-- Existential all-rule transition relation, without a priority policy. -/
def StepRel (machine : QuadrupleMachine Control TapeIndex Symbol)
    (before after : MultiConfiguration Control TapeIndex Symbol) : Prop :=
  ∃ index : machine.RuleId,
    (machine.rule index).Matches before ∧
      (machine.rule index).execute before = after

/-- Distinct indexed rules have semantically disjoint domains. -/
def DomainsDisjoint
    (machine : QuadrupleMachine Control TapeIndex Symbol) : Prop :=
  ∀ {first second : machine.RuleId}, first ≠ second →
    ¬(machine.rule first).DomainsOverlap (machine.rule second)

/-- Distinct indexed rules have semantically disjoint ranges. -/
def RangesDisjoint
    (machine : QuadrupleMachine Control TapeIndex Symbol) : Prop :=
  ∀ {first second : machine.RuleId}, first ≠ second →
    ¬(machine.rule first).RangesOverlap (machine.rule second)

/-- Bennett's strong syntactic discipline, expressed via semantic overlap. -/
def SyntacticallyReversible
    (machine : QuadrupleMachine Control TapeIndex Symbol) : Prop :=
  machine.DomainsDisjoint ∧ machine.RangesDisjoint

instance [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (machine : QuadrupleMachine Control TapeIndex Symbol) :
    Decidable machine.DomainsDisjoint := by
  unfold DomainsDisjoint
  infer_instance

instance [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (machine : QuadrupleMachine Control TapeIndex Symbol) :
    Decidable machine.RangesDisjoint := by
  unfold RangesDisjoint
  infer_instance

instance [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (machine : QuadrupleMachine Control TapeIndex Symbol) :
    Decidable machine.SyntacticallyReversible := by
  unfold SyntacticallyReversible
  infer_instance

/-- Select the least indexed matching target rule. -/
def select [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (machine : QuadrupleMachine Control TapeIndex Symbol)
    (config : MultiConfiguration Control TapeIndex Symbol) :
    Option machine.RuleId :=
  Fin.find? fun index => decide ((machine.rule index).Matches config)

/-- Executable one-step semantics using least-index selection. -/
def step [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (machine : QuadrupleMachine Control TapeIndex Symbol) :
    PartialStep (MultiConfiguration Control TapeIndex Symbol) :=
  fun config => (machine.select config).map fun index =>
    (machine.rule index).execute config

theorem select_matches [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (machine : QuadrupleMachine Control TapeIndex Symbol)
    (config : MultiConfiguration Control TapeIndex Symbol)
    {index : machine.RuleId} (hselect : machine.select config = some index) :
    (machine.rule index).Matches config := by
  have hmem : index ∈ machine.select config := by simp [hselect]
  exact of_decide_eq_true (Fin.mem_find?_iff.mp hmem).1

theorem select_eq_none_iff [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (machine : QuadrupleMachine Control TapeIndex Symbol)
    (config : MultiConfiguration Control TapeIndex Symbol) :
    machine.select config = none ↔
      ∀ index : machine.RuleId, ¬(machine.rule index).Matches config := by
  simp [select, Fin.find?_decide_eq_dite]

theorem step_to_stepRel [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (machine : QuadrupleMachine Control TapeIndex Symbol)
    {before after : MultiConfiguration Control TapeIndex Symbol}
    (hstep : machine.step before = some after) :
    machine.StepRel before after := by
  unfold step at hstep
  obtain ⟨index, hselect, hafter⟩ := Option.map_eq_some_iff.mp hstep
  exact ⟨index, machine.select_matches before hselect, hafter⟩

theorem DomainsDisjoint.eq_of_matches
    {machine : QuadrupleMachine Control TapeIndex Symbol}
    (hdisjoint : machine.DomainsDisjoint)
    (config : MultiConfiguration Control TapeIndex Symbol)
    {first second : machine.RuleId}
    (hfirst : (machine.rule first).Matches config)
    (hsecond : (machine.rule second).Matches config) : first = second := by
  by_contra hne
  exact hdisjoint hne ⟨config, hfirst, hsecond⟩

theorem DomainsDisjoint.step_eq_some_iff
    [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    {machine : QuadrupleMachine Control TapeIndex Symbol}
    (hdisjoint : machine.DomainsDisjoint)
    (before after : MultiConfiguration Control TapeIndex Symbol) :
    machine.step before = some after ↔ machine.StepRel before after := by
  constructor
  · exact machine.step_to_stepRel
  · rintro ⟨index, hmatches, rfl⟩
    cases hselect : machine.select before with
    | none =>
        exact False.elim
          ((machine.select_eq_none_iff before).mp hselect index hmatches)
    | some selected =>
        have hselected := machine.select_matches before hselect
        have heq : selected = index :=
          hdisjoint.eq_of_matches before hselected hmatches
        subst selected
        simp [step, hselect]

theorem DomainsDisjoint.stepRel_rightUnique
    {machine : QuadrupleMachine Control TapeIndex Symbol}
    (hdisjoint : machine.DomainsDisjoint) :
    Relator.RightUnique machine.StepRel := by
  rintro before after₁ after₂
    ⟨first, hfirst, rfl⟩ ⟨second, hsecond, hafter⟩
  by_cases hindex : first = second
  · subst second
    exact hafter
  · exact False.elim (hdisjoint hindex ⟨before, hfirst, hsecond⟩)

theorem RangesDisjoint.stepRel_leftUnique
    {machine : QuadrupleMachine Control TapeIndex Symbol}
    (hdisjoint : machine.RangesDisjoint) :
    Relator.LeftUnique machine.StepRel := by
  rintro before₁ before₂ after
    ⟨first, hfirst, hfirsteq⟩ ⟨second, hsecond, hsecondeq⟩
  by_cases hindex : first = second
  · subst second
    apply (machine.rule first).execute_injective_on hfirst hsecond
    exact hfirsteq.trans hsecondeq.symm
  · exact False.elim (hdisjoint hindex
      ⟨after, ⟨before₁, hfirst, hfirsteq⟩,
        ⟨before₂, hsecond, hsecondeq⟩⟩)

/-- Range disjointness alone makes even priority execution reversible. -/
theorem RangesDisjoint.step_reversible
    [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    {machine : QuadrupleMachine Control TapeIndex Symbol}
    (hdisjoint : machine.RangesDisjoint) : machine.step.Reversible := by
  rw [PartialStep.reversible_iff]
  intro before₁ before₂ after hstep₁ hstep₂
  exact hdisjoint.stepRel_leftUnique
    (machine.step_to_stepRel hstep₁) (machine.step_to_stepRel hstep₂)

/-- Pointwise formal inverse table, preserving rule identifiers and count. -/
def inverse (machine : QuadrupleMachine Control TapeIndex Symbol) :
    QuadrupleMachine Control TapeIndex Symbol :=
  { ruleCount := machine.ruleCount
    rule := fun index => (machine.rule index).inverse }

@[simp] theorem inverse_ruleCount
    (machine : QuadrupleMachine Control TapeIndex Symbol) :
    machine.inverse.ruleCount = machine.ruleCount :=
  rfl

@[simp] theorem inverse_rule
    (machine : QuadrupleMachine Control TapeIndex Symbol)
    (index : machine.inverse.RuleId) :
    machine.inverse.rule index = (machine.rule index).inverse :=
  rfl

@[simp] theorem inverse_inverse
    (machine : QuadrupleMachine Control TapeIndex Symbol) :
    machine.inverse.inverse = machine := by
  cases machine
  simp [inverse]

theorem RangesDisjoint.inverse_domainsDisjoint
    {machine : QuadrupleMachine Control TapeIndex Symbol}
    (hdisjoint : machine.RangesDisjoint) :
    machine.inverse.DomainsDisjoint := by
  intro first second hne hoverlap
  apply hdisjoint hne
  exact (Quadruple.rangesOverlap_iff_inverse_domainsOverlap
    (machine.rule first) (machine.rule second)).mpr hoverlap

theorem DomainsDisjoint.inverse_rangesDisjoint
    {machine : QuadrupleMachine Control TapeIndex Symbol}
    (hdisjoint : machine.DomainsDisjoint) :
    machine.inverse.RangesDisjoint := by
  intro first second hne hoverlap
  apply hdisjoint hne
  have hoverlap' :=
    (Quadruple.rangesOverlap_iff_inverse_domainsOverlap
      (machine.rule first).inverse (machine.rule second).inverse).mp hoverlap
  simpa using hoverlap'

/-- Under both non-overlap obligations, the inverse table executes the converse graph. -/
theorem step_areInverses [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    {machine : QuadrupleMachine Control TapeIndex Symbol}
    (hdomains : machine.DomainsDisjoint)
    (hranges : machine.RangesDisjoint) :
    machine.step.AreInverses machine.inverse.step := by
  intro before after
  constructor
  · intro hstep
    obtain ⟨index, hmatches, hafter⟩ := machine.step_to_stepRel hstep
    apply (DomainsDisjoint.step_eq_some_iff
      (machine := machine.inverse) hranges.inverse_domainsDisjoint
      after before).2
    refine ⟨index, ?_⟩
    have hforward : (machine.rule index).step before = some after :=
      ((machine.rule index).step_eq_some_iff before after).2
        ⟨hmatches, hafter⟩
    have hbackward :
        (machine.rule index).inverse.step after = some before :=
      ((machine.rule index).step_areInverses
        (before := before) (after := after)).mp hforward
    exact ((machine.rule index).inverse.step_eq_some_iff after before).1
      hbackward
  · intro hstep
    obtain ⟨index, hmatches, hbefore⟩ := machine.inverse.step_to_stepRel hstep
    apply (DomainsDisjoint.step_eq_some_iff
      (machine := machine) hdomains before after).2
    refine ⟨index, ?_⟩
    have hbackward :
        (machine.rule index).inverse.step after = some before :=
      ((machine.rule index).inverse.step_eq_some_iff after before).2
        ⟨hmatches, hbefore⟩
    have hforward : (machine.rule index).step before = some after :=
      ((machine.rule index).step_areInverses
        (before := before) (after := after)).mpr hbackward
    exact ((machine.rule index).step_eq_some_iff before after).1 hforward

end QuadrupleMachine
end Bennett.Turing
