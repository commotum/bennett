import Bennett.Turing.Quadruple.Core

/-!
# Formal inverses of typed quadruples

The inverse swaps checked/written symbols for rewrite actions, reverses head
movements, and exchanges source/target controls.  The proofs below establish
converse successful-step graphs on complete configurations; they are stronger
than a syntactic claim that the displayed rule merely looks reversed.
-/

namespace Bennett.Turing

namespace Action

variable {Symbol : Type*}

/-- The action with the converse partial graph. -/
def inverse : Action Symbol → Action Symbol
  | .rewrite scanned written => .rewrite written scanned
  | .move direction => .move direction.inverse

@[simp] theorem inverse_rewrite (scanned written : TapeSymbol Symbol) :
    (Action.rewrite scanned written).inverse = .rewrite written scanned :=
  rfl

@[simp] theorem inverse_move_action (direction : Move) :
    (Action.move direction : Action Symbol).inverse = .move direction.inverse :=
  rfl

@[simp] theorem inverse_inverse (action : Action Symbol) :
    action.inverse.inverse = action := by
  cases action <;> simp [inverse]

/-- A successfully executed action satisfies the inverse precondition. -/
theorem inverse_matches_execute {action : Action Symbol} {tape : Tape Symbol}
    (hmatch : action.Matches tape) :
    action.inverse.Matches (action.execute tape) := by
  cases action with
  | rewrite scanned written => simp [Matches, execute, inverse]
  | move direction => trivial

/-- The inverse action exactly restores a tape after a successful action. -/
theorem inverse_execute {action : Action Symbol} {tape : Tape Symbol}
    (hmatch : action.Matches tape) :
    action.inverse.execute (action.execute tape) = tape := by
  cases action with
  | rewrite scanned written =>
      change (tape.write written).write scanned = tape
      rw [Tape.write_write, ← hmatch, Tape.write_read]
  | move direction =>
      exact tape.move_inverse direction

/-- The forward action similarly restores a tape after a successful inverse. -/
theorem execute_inverse {action : Action Symbol} {tape : Tape Symbol}
    (hmatch : action.inverse.Matches tape) :
    action.execute (action.inverse.execute tape) = tape := by
  simpa using
    (inverse_execute (action := action.inverse) (tape := tape) hmatch)

end Action

namespace Quadruple

variable {Control TapeIndex : Type*} {Symbol : TapeIndex → Type*}

/-- The formal inverse quadruple. -/
def inverse (rule : Quadruple Control TapeIndex Symbol) :
    Quadruple Control TapeIndex Symbol :=
  { source := rule.target
    action := fun index => (rule.action index).inverse
    target := rule.source }

@[simp] theorem inverse_source (rule : Quadruple Control TapeIndex Symbol) :
    rule.inverse.source = rule.target :=
  rfl

@[simp] theorem inverse_target (rule : Quadruple Control TapeIndex Symbol) :
    rule.inverse.target = rule.source :=
  rfl

@[simp] theorem inverse_action (rule : Quadruple Control TapeIndex Symbol)
    (index : TapeIndex) :
    rule.inverse.action index = (rule.action index).inverse :=
  rfl

@[simp] theorem inverse_inverse (rule : Quadruple Control TapeIndex Symbol) :
    rule.inverse.inverse = rule := by
  cases rule
  simp [inverse]

/-- The endpoint of a successful quadruple matches its formal inverse. -/
theorem inverse_matches_execute {rule : Quadruple Control TapeIndex Symbol}
    {config : MultiConfiguration Control TapeIndex Symbol}
    (hmatch : rule.Matches config) :
    rule.inverse.Matches (rule.execute config) := by
  refine ⟨rfl, ?_⟩
  intro index
  exact Action.inverse_matches_execute (hmatch.2 index)

/-- Formal inverse execution restores the entire configuration exactly. -/
theorem inverse_execute {rule : Quadruple Control TapeIndex Symbol}
    {config : MultiConfiguration Control TapeIndex Symbol}
    (hmatch : rule.Matches config) :
    rule.inverse.execute (rule.execute config) = config := by
  apply MultiConfiguration.ext
  · exact hmatch.1
  · intro index
    exact Action.inverse_execute (hmatch.2 index)

/-- Forward execution restores a configuration after a successful inverse. -/
theorem execute_inverse {rule : Quadruple Control TapeIndex Symbol}
    {config : MultiConfiguration Control TapeIndex Symbol}
    (hmatch : rule.inverse.Matches config) :
    rule.execute (rule.inverse.execute config) = config := by
  simpa using
    (inverse_execute (rule := rule.inverse) (config := config) hmatch)

/-- A quadruple and its formal inverse have exactly converse successful graphs. -/
theorem step_areInverses [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (rule : Quadruple Control TapeIndex Symbol) :
    rule.step.AreInverses rule.inverse.step := by
  intro before after
  rw [step_eq_some_iff, step_eq_some_iff]
  constructor
  · rintro ⟨hmatch, rfl⟩
    exact ⟨inverse_matches_execute hmatch, inverse_execute hmatch⟩
  · rintro ⟨hmatch, hbefore⟩
    subst before
    have hforward := inverse_matches_execute (rule := rule.inverse) hmatch
    have hrestore := inverse_execute (rule := rule.inverse) hmatch
    simpa using And.intro hforward hrestore

/-- Every individual quadruple is injective on its semantic domain. -/
theorem execute_injective_on (rule : Quadruple Control TapeIndex Symbol) :
    Set.InjOn rule.execute {config | rule.Matches config} := by
  intro first hfirst second hsecond hequal
  rw [← rule.inverse_execute hfirst, ← rule.inverse_execute hsecond, hequal]

/-- Package a single rule and its formal inverse as a mathlib partial equivalence. -/
def inversePair [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (rule : Quadruple Control TapeIndex Symbol) :
    PartialStep.InversePair (MultiConfiguration Control TapeIndex Symbol) :=
  (rule.step_areInverses).toInversePair

end Quadruple
end Bennett.Turing
