import Bennett.Transition.Core
import Bennett.Turing.Tape
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Typed read/write-or-move quadruples

Bennett's reversible target syntax performs exactly one kind of operation on
each tape during a transition: either it checks and rewrites the scanned cell
without moving, or it moves the head without reading or writing.  The inductive
`Action` type makes the paper's side condition true by construction.
-/

namespace Bennett.Turing

namespace Move

/-- The opposite head movement. -/
def inverse : Move → Move
  | .left => .right
  | .stay => .stay
  | .right => .left

@[simp] theorem inverse_left : Move.left.inverse = .right := rfl
@[simp] theorem inverse_stay : Move.stay.inverse = .stay := rfl
@[simp] theorem inverse_right : Move.right.inverse = .left := rfl

@[simp] theorem inverse_inverse (direction : Move) :
    direction.inverse.inverse = direction := by
  cases direction <;> rfl

@[simp] theorem offset_inverse_add (direction : Move) :
    direction.offset + direction.inverse.offset = 0 := by
  cases direction <;> rfl

@[simp] theorem inverse_offset_add (direction : Move) :
    direction.inverse.offset + direction.offset = 0 := by
  cases direction <;> rfl

end Move

namespace Tape

variable {Symbol : Type*}

/-- Moving by a direction and then by its inverse restores the complete tape. -/
@[simp] theorem move_inverse (tape : Tape Symbol) (direction : Move) :
    (tape.move direction).move direction.inverse = tape := by
  cases tape
  cases direction <;> simp [move, Move.inverse, Move.offset]

/-- Moving first by the inverse direction also restores the complete tape. -/
@[simp] theorem inverse_move (tape : Tape Symbol) (direction : Move) :
    (tape.move direction.inverse).move direction = tape := by
  simpa using tape.move_inverse direction.inverse

end Tape

/-- One legal per-tape target-machine action. -/
inductive Action (Symbol : Type*) where
  /-- Check the scanned symbol, then rewrite that cell without moving. -/
  | rewrite (scanned written : TapeSymbol Symbol)
  /-- Move without inspecting or changing the tape contents. -/
  | move (direction : Move)
deriving DecidableEq, Repr

namespace Action

variable {Symbol : Type*}

/-- Applicability of one typed action to one tape. -/
def Matches (action : Action Symbol) (tape : Tape Symbol) : Prop :=
  match action with
  | .rewrite scanned _ => tape.read = scanned
  | .move _ => True

instance [DecidableEq Symbol] (action : Action Symbol) (tape : Tape Symbol) :
    Decidable (action.Matches tape) := by
  cases action <;> simp [Matches] <;> infer_instance

/-- Execute an action.  Callers separately establish `Matches`. -/
def execute (action : Action Symbol) (tape : Tape Symbol) : Tape Symbol :=
  match action with
  | .rewrite _ written => tape.write written
  | .move direction => tape.move direction

@[simp] theorem matches_rewrite (tape : Tape Symbol)
    (scanned written : TapeSymbol Symbol) :
    (Action.rewrite scanned written).Matches tape ↔ tape.read = scanned :=
  Iff.rfl

@[simp] theorem matches_move (tape : Tape Symbol) (direction : Move) :
    (Action.move direction : Action Symbol).Matches tape :=
  trivial

@[simp] theorem execute_rewrite (tape : Tape Symbol)
    (scanned written : TapeSymbol Symbol) :
    (Action.rewrite scanned written).execute tape = tape.write written :=
  rfl

@[simp] theorem execute_move (tape : Tape Symbol) (direction : Move) :
    (Action.move direction : Action Symbol).execute tape =
      tape.move direction :=
  rfl

end Action

/-- A complete configuration of an intrinsic finite number of tapes. -/
structure MultiConfiguration (TapeCount : Nat) (Control Symbol : Type*) where
  control : Control
  tapes : Fin TapeCount → Tape Symbol

namespace MultiConfiguration

variable {TapeCount : Nat} {Control Symbol : Type*}

/-- The symbol scanned on a selected tape. -/
def read (config : MultiConfiguration TapeCount Control Symbol)
    (index : Fin TapeCount) : TapeSymbol Symbol :=
  (config.tapes index).read

end MultiConfiguration

/-- A multi-tape read/write-or-move transition. -/
structure Quadruple (TapeCount : Nat) (Control Symbol : Type*) where
  source : Control
  actions : Fin TapeCount → Action Symbol
  target : Control

namespace Quadruple

variable {TapeCount : Nat} {Control Symbol : Type*}

/-- A quadruple matches its source control and every action precondition. -/
def Matches (rule : Quadruple TapeCount Control Symbol)
    (config : MultiConfiguration TapeCount Control Symbol) : Prop :=
  rule.source = config.control ∧
    ∀ index, (rule.actions index).Matches (config.tapes index)

instance [DecidableEq Control] [DecidableEq Symbol]
    (rule : Quadruple TapeCount Control Symbol)
    (config : MultiConfiguration TapeCount Control Symbol) :
    Decidable (rule.Matches config) := by
  unfold Matches
  infer_instance

/-- Execute all tape actions simultaneously, then install the target control. -/
def execute (rule : Quadruple TapeCount Control Symbol)
    (config : MultiConfiguration TapeCount Control Symbol) :
    MultiConfiguration TapeCount Control Symbol :=
  { control := rule.target
    tapes := fun index => (rule.actions index).execute (config.tapes index) }

@[simp] theorem execute_control (rule : Quadruple TapeCount Control Symbol)
    (config : MultiConfiguration TapeCount Control Symbol) :
    (rule.execute config).control = rule.target :=
  rfl

@[simp] theorem execute_tapes (rule : Quadruple TapeCount Control Symbol)
    (config : MultiConfiguration TapeCount Control Symbol)
    (index : Fin TapeCount) :
    (rule.execute config).tapes index =
      (rule.actions index).execute (config.tapes index) :=
  rfl

/-- The partial transition induced by a single quadruple. -/
def step [DecidableEq Control] [DecidableEq Symbol]
    (rule : Quadruple TapeCount Control Symbol) :
    PartialStep (MultiConfiguration TapeCount Control Symbol) :=
  fun config => if rule.Matches config then some (rule.execute config) else none

theorem step_eq_some_iff [DecidableEq Control] [DecidableEq Symbol]
    (rule : Quadruple TapeCount Control Symbol)
    (before after : MultiConfiguration TapeCount Control Symbol) :
    rule.step before = some after ↔
      rule.Matches before ∧ rule.execute before = after := by
  simp [step]

theorem step_eq_none_iff [DecidableEq Control] [DecidableEq Symbol]
    (rule : Quadruple TapeCount Control Symbol)
    (config : MultiConfiguration TapeCount Control Symbol) :
    rule.step config = none ↔ ¬rule.Matches config := by
  simp [step]

end Quadruple
end Bennett.Turing
