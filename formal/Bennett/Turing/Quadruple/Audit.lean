import Bennett.Turing.Quadruple.API
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

/-!
# Executable and axiom audits for reversible quadruples
-/

namespace Bennett.Turing.QuadrupleAudit

inductive DemoTape where
  | work
  | auxiliary
deriving DecidableEq, Fintype, Repr

/-- A deliberately heterogeneous pair of tape alphabets. -/
def DemoSymbol : DemoTape → Type
  | .work => Bool
  | .auxiliary => Fin 2

instance (index : DemoTape) : DecidableEq (DemoSymbol index) := by
  cases index
  · change DecidableEq Bool
    infer_instance
  · change DecidableEq (Fin 2)
    infer_instance

def demoConfig : MultiConfiguration Bool DemoTape DemoSymbol where
  control := false
  tape
    | .work => (Tape.blankAt 0).write (.mark true)
    | .auxiliary => Tape.blankAt 4

def demoRule : Quadruple Bool DemoTape DemoSymbol where
  source := false
  action
    | .work => .rewrite (.mark true) (.mark false)
    | .auxiliary => .move .right
  target := true

example : demoRule.Matches demoConfig := by
  constructor
  · rfl
  · intro index
    cases index <;> simp [demoRule, demoConfig, Action.Matches]

example : (demoRule.execute demoConfig).control = true := rfl

example : ((demoRule.execute demoConfig).tape .work).read = .mark false := by
  rfl

example : ((demoRule.execute demoConfig).tape .auxiliary).head = 5 := by
  rfl

example : demoRule.inverse.execute (demoRule.execute demoConfig) = demoConfig := by
  apply Quadruple.inverse_execute
  constructor
  · rfl
  · intro index
    cases index <;> simp [demoRule, demoConfig, Action.Matches]

/-- Writing before moving is observably different from moving before writing. -/
example :
    ((Tape.blankAt 0 : Tape Bool).write (.mark true)).move .right ≠
      ((Tape.blankAt 0 : Tape Bool).move .right).write (.mark true) := by
  decide

def overlapMove : Quadruple Bool DemoTape DemoSymbol where
  source := false
  action _ := .move .stay
  target := true

def overlapRewrite : Quadruple Bool DemoTape DemoSymbol where
  source := false
  action
    | .work => .rewrite .blank .blank
    | .auxiliary => .move .stay
  target := true

/-- A move action imposes no read restriction, so these domains overlap. -/
example : overlapMove.DomainsOverlap overlapRewrite := by
  decide

/-- A move action is surjective, so the corrected range test also overlaps. -/
example : overlapMove.RangesOverlap overlapRewrite := by
  decide

def overlapMachine : QuadrupleMachine Bool DemoTape DemoSymbol where
  ruleCount := 2
  rule index := if index = 0 then overlapMove else overlapRewrite

example : ¬overlapMachine.DomainsDisjoint := by decide
example : ¬overlapMachine.RangesDisjoint := by decide

theorem overlapMove_matches_of_rewrite
    {config : MultiConfiguration Bool DemoTape DemoSymbol}
    (hmatch : overlapRewrite.Matches config) :
    overlapMove.Matches config := by
  refine ⟨hmatch.1, ?_⟩
  intro index
  cases index <;> trivial

theorem overlap_execute_eq_of_rewrite_matches
    {config : MultiConfiguration Bool DemoTape DemoSymbol}
    (hmatch : overlapRewrite.Matches config) :
    overlapMove.execute config = overlapRewrite.execute config := by
  apply MultiConfiguration.ext
  · rfl
  · intro index
    cases index with
    | work =>
        have hread := hmatch.2 DemoTape.work
        change (config.tape .work).read = .blank at hread
        simp only [Quadruple.execute_tape, overlapMove, overlapRewrite,
          Action.execute_move, Action.execute_rewrite, Tape.move_stay]
        rw [← hread, Tape.write_read]
    | auxiliary =>
        simp [overlapMove, overlapRewrite]

/-- Non-overlap is sufficient but not necessary for extensional determinism. -/
example : Relator.RightUnique overlapMachine.StepRel := by
  rintro before after₁ after₂
    ⟨first, hfirst, hafter₁⟩ ⟨second, hsecond, hafter₂⟩
  fin_cases first <;> fin_cases second
  · exact hafter₁.symm.trans hafter₂
  · have hsecond' : overlapRewrite.Matches before := by
      simpa [overlapMachine] using hsecond
    calc
      after₁ = overlapMove.execute before := hafter₁.symm
      _ = overlapRewrite.execute before :=
        overlap_execute_eq_of_rewrite_matches hsecond'
      _ = after₂ := hafter₂
  · have hfirst' : overlapRewrite.Matches before := by
      simpa [overlapMachine] using hfirst
    calc
      after₁ = overlapRewrite.execute before := hafter₁.symm
      _ = overlapMove.execute before :=
        (overlap_execute_eq_of_rewrite_matches hfirst').symm
      _ = after₂ := hafter₂
  · exact hafter₁.symm.trans hafter₂

/-- The same overlapping table is also predecessor-unique as a relation. -/
example : Relator.LeftUnique overlapMachine.StepRel := by
  rintro before₁ before₂ after
    ⟨first, hfirst, hafter₁⟩ ⟨second, hsecond, hafter₂⟩
  fin_cases first <;> fin_cases second
  · exact overlapMove.execute_injective_on hfirst hsecond
      (hafter₁.trans hafter₂.symm)
  · have hsecond' : overlapRewrite.Matches before₂ := by
      simpa [overlapMachine] using hsecond
    have hafter₁' : overlapMove.execute before₁ = after := by
      simpa [overlapMachine] using hafter₁
    have hafter₂' : overlapRewrite.execute before₂ = after := by
      simpa [overlapMachine] using hafter₂
    apply overlapMove.execute_injective_on hfirst
      (overlapMove_matches_of_rewrite hsecond')
    exact hafter₁'.trans (hafter₂'.symm.trans
      (overlap_execute_eq_of_rewrite_matches hsecond').symm)
  · have hfirst' : overlapRewrite.Matches before₁ := by
      simpa [overlapMachine] using hfirst
    have hafter₁' : overlapRewrite.execute before₁ = after := by
      simpa [overlapMachine] using hafter₁
    have hafter₂' : overlapMove.execute before₂ = after := by
      simpa [overlapMachine] using hafter₂
    apply overlapMove.execute_injective_on
      (overlapMove_matches_of_rewrite hfirst') hsecond
    exact (overlap_execute_eq_of_rewrite_matches hfirst').trans
      (hafter₁'.trans hafter₂'.symm)
  · exact overlapRewrite.execute_injective_on hfirst hsecond
      (hafter₁.trans hafter₂.symm)

def sourceRuleBlank : Quintuple Bool Bool where
  source := false
  scanned := .blank
  written := .blank
  move := .right
  target := true

def sourceRuleMark : Quintuple Bool Bool where
  source := false
  scanned := .mark true
  written := .mark false
  move := .left
  target := true

def collisionSource : Machine Bool Bool where
  ruleCount := 2
  rule index := if index = 0 then sourceRuleBlank else sourceRuleMark

theorem collisionSource_deterministic :
    collisionSource.SyntacticallyDeterministic := by
  intro first second hkey
  fin_cases first <;> fin_cases second <;>
    simp [collisionSource, sourceRuleBlank, sourceRuleMark,
      Quintuple.key] at hkey ⊢

/-- Fresh connectors make the pure split table deterministic. -/
example :
    (Machine.splitMachine (TargetSymbol := DemoSymbol) .work
      collisionSource).DomainsDisjoint :=
  Machine.splitMachine_domainsDisjoint (TargetSymbol := DemoSymbol)
    (work := .work) collisionSource_deterministic

/-- Shared source targets make the move-half ranges overlap before history is added. -/
example :
    (SourceSplit.moveHalf (Symbol := DemoSymbol) .work (0 : Fin 2)
      sourceRuleBlank).RangesOverlap
      (SourceSplit.moveHalf (Symbol := DemoSymbol) .work (1 : Fin 2)
        sourceRuleMark) := by
  apply (SourceSplit.moveHalf_rangesOverlap_iff_target_eq
    (Symbol := DemoSymbol) .work (0 : Fin 2) (1 : Fin 2)
      sourceRuleBlank sourceRuleMark).2
  rfl

/-- Consequently, source splitting alone is not a reversible table here. -/
example :
    ¬(Machine.splitMachine (TargetSymbol := DemoSymbol) .work
      collisionSource).RangesDisjoint := by
  decide

#print axioms Bennett.Turing.Quintuple.singleStep_areInverses
#print axioms Bennett.Turing.Quadruple.step_areInverses
#print axioms Bennett.Turing.Quadruple.domainsOverlap_iff_domainCompatible
#print axioms Bennett.Turing.Quadruple.rangesOverlap_iff_rangeCompatible
#print axioms Bennett.Turing.QuadrupleMachine.step_areInverses
#print axioms Bennett.Turing.SourceSplit.lift_two_step_of_matches
#print axioms Bennett.Turing.Machine.splitMachine_domainsDisjoint
#print axioms Bennett.Turing.Machine.splitRule_ranges_disjoint_iff_target_injective

end Bennett.Turing.QuadrupleAudit
