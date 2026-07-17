import Bennett.Turing.Quadruple.Core
import Bennett.Turing.Source.Core

/-!
# Constructive inverse of one source quintuple

A read/write/move quintuple is individually a partial bijection even though its
inverse is not itself in read/write/move order.  The inverse first moves the
head back, validates the symbol written at the old head, and then restores the
scanned symbol.  This is precisely why Bennett changes syntax before building a
machine closed under formal inversion.
-/

namespace Bennett.Turing
namespace Quintuple

variable {Control Symbol : Type*}

/-- Preconditions for applying the shift/read/write inverse of one quintuple. -/
def UndoMatches (rule : Quintuple Control Symbol)
    (config : Configuration Control Symbol) : Prop :=
  rule.target = config.control ∧
    (config.tape.move rule.move.inverse).read = rule.written

instance [DecidableEq Control] [DecidableEq Symbol]
    (rule : Quintuple Control Symbol) (config : Configuration Control Symbol) :
    Decidable (rule.UndoMatches config) := by
  unfold UndoMatches
  infer_instance

/-- Shift back first, then restore the symbol checked by the forward rule. -/
def undo (rule : Quintuple Control Symbol)
    (config : Configuration Control Symbol) : Configuration Control Symbol :=
  { control := rule.source
    tape := (config.tape.move rule.move.inverse).write rule.scanned }

/-- A successful forward endpoint satisfies the exact inverse precondition. -/
theorem undoMatches_execute {rule : Quintuple Control Symbol}
    {config : Configuration Control Symbol} :
    rule.UndoMatches (rule.execute config) := by
  refine ⟨rfl, ?_⟩
  simp [execute, Tape.writeMove]

/-- The shift/read/write inverse exactly restores a successful predecessor. -/
theorem undo_execute {rule : Quintuple Control Symbol}
    {config : Configuration Control Symbol} (hmatch : rule.Matches config) :
    rule.undo (rule.execute config) = config := by
  rcases config with ⟨control, tape⟩
  change rule.source = control ∧ _ at hmatch
  rcases hmatch with ⟨hcontrol, hread⟩
  subst control
  change rule.scanned = tape.read at hread
  unfold undo execute
  congr 1
  change (((tape.write rule.written).move rule.move).move
    rule.move.inverse).write rule.scanned = tape
  rw [Tape.move_inverse, Tape.write_write, hread, Tape.write_read]

/-- An inverse-successor reconstructs a configuration matching the forward rule. -/
theorem matches_undo {rule : Quintuple Control Symbol}
    {config : Configuration Control Symbol} :
    rule.Matches (rule.undo config) := by
  exact ⟨rfl, by simp [undo, Configuration.read]⟩

/-- Forward execution exactly restores an endpoint satisfying `UndoMatches`. -/
theorem execute_undo {rule : Quintuple Control Symbol}
    {config : Configuration Control Symbol} (hmatch : rule.UndoMatches config) :
    rule.execute (rule.undo config) = config := by
  rcases config with ⟨control, tape⟩
  change rule.target = control ∧ _ at hmatch
  rcases hmatch with ⟨hcontrol, hwritten⟩
  subst control
  unfold execute undo
  congr 1
  change (((tape.move rule.move.inverse).write rule.scanned).write
    rule.written).move rule.move = tape
  rw [Tape.write_write, ← hwritten, Tape.write_read, Tape.inverse_move]

/-- Partial single-rule source semantics, without a table priority policy. -/
def singleStep [DecidableEq Control] [DecidableEq Symbol]
    (rule : Quintuple Control Symbol) :
    PartialStep (Configuration Control Symbol) :=
  fun config => if rule.Matches config then some (rule.execute config) else none

/-- Executable inverse of `singleStep`, with range validation. -/
def undoStep [DecidableEq Control] [DecidableEq Symbol]
    (rule : Quintuple Control Symbol) :
    PartialStep (Configuration Control Symbol) :=
  fun config => if rule.UndoMatches config then some (rule.undo config) else none

/-- One quintuple and its shift/read/write inverse have converse successful graphs. -/
theorem singleStep_areInverses [DecidableEq Control] [DecidableEq Symbol]
    (rule : Quintuple Control Symbol) :
    rule.singleStep.AreInverses rule.undoStep := by
  intro before after
  simp only [singleStep, undoStep]
  constructor
  · split
    · intro hstep
      have hafter := Option.some.inj hstep
      subst after
      simp [undoMatches_execute,
        undo_execute ‹rule.Matches before›]
    · simp
  · split
    · intro hstep
      have hbefore := Option.some.inj hstep
      subst before
      simp [matches_undo,
        execute_undo ‹rule.UndoMatches after›]
    · simp

/-- Every source quintuple is injective on configurations it matches. -/
theorem execute_injective_on (rule : Quintuple Control Symbol) :
    Set.InjOn rule.execute {config | rule.Matches config} := by
  intro first hfirst second hsecond hequal
  rw [← rule.undo_execute hfirst, ← rule.undo_execute hsecond, hequal]

end Quintuple
end Bennett.Turing
