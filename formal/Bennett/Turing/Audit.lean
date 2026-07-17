import Bennett.Turing.Resource
import Bennett.Turing.Source.Standard

/-!
# Executable source-machine audit

The one-rule machine below writes the old scanned cell before moving right.  It
then halts because no rule has the final control.  Reduction tests cover absolute
left-of-origin writing, first-symbol scanning after the move, exact trace count,
empty-word formatting, and the distinction between first-match execution and
syntactic unique applicability.

Nothing in this file is re-exported by the public API.
-/

namespace Bennett.TuringAudit

open Turing

inductive Control where
  | start
  | halt
deriving DecidableEq, Repr

inductive Symbol where
  | mark
deriving DecidableEq, Repr

def machine : Machine Control Symbol where
  ruleCount := 1
  rule
    | ⟨0, _⟩ =>
        { source := .start
          scanned := .blank
          written := .mark .mark
          move := .right
          target := .halt }

theorem machine_syntacticallyDeterministic :
    machine.SyntacticallyDeterministic := by
  change Function.Injective (fun index : Fin 1 => (machine.rule index).key)
  intro first second _
  apply Fin.eq_of_val_eq
  omega

def initial : Configuration Control Symbol :=
  Standard.config .start [.mark]

def finish : Configuration Control Symbol :=
  { control := .halt
    tape := ((Tape.ofWord [.mark]).write (.mark .mark)).move .right }

theorem machine_step_initial : machine.step initial = some finish := by
  apply (machine_syntacticallyDeterministic.step_eq_some_iff _ _).mpr
  refine ⟨(0 : Fin 1), ?_, rfl⟩
  change Control.start = initial.control ∧ TapeSymbol.blank = initial.read
  exact ⟨rfl, (Standard.config_read Control.start [.mark]).symm⟩

/-- The write occurred at old head `-1`, not at the new head `0`. -/
example : finish.tape.cells (-1) = .mark .mark := by
  rfl

/-- After moving, the head scans the first symbol of the original word. -/
example : finish.read = .mark .mark := by
  rfl

example : finish.tape.head = 0 := by
  rfl

theorem machine_halted_finish : machine.step finish = none := by
  rw [machine.step_eq_none_iff]
  intro index hmatches
  have hlt := index.isLt
  change index.val < 1 at hlt
  have hval : index.val = 0 := by
    omega
  let zero : machine.RuleId := ⟨0, by simp [machine]⟩
  have hindex : index = zero := Fin.eq_of_val_eq hval
  subst index
  have hsource : (machine.rule zero).source = .start := by
    simp [zero, machine]
  exact Control.noConfusion (hsource.symm.trans hmatches.1)

example :
    ExecutionTrace.run machine.step 1 initial =
      some ⟨initial, [finish]⟩ := by
  simp [ExecutionTrace.run, ExecutionTrace.prepend,
    ExecutionTrace.singleton, machine_step_initial]

example : (ExecutionTrace.singleton initial).transitionCount = 0 := rfl

example :
    ExecutionTrace.visitedPositions Configuration.tape
      (ExecutionTrace.singleton initial) = {-1} := by
  rfl

example : (Tape.ofWord ([.mark] : List Symbol)).nonblankPositions.card = 1 := by
  rfl

/-- Empty standard words are legal at this layer and still scan the left blank. -/
example :
    (Standard.config (Symbol := Symbol) (.start : Control) []).tape.head = -1 :=
  rfl

example :
    (Standard.config (Symbol := Symbol) (.start : Control) []).read = .blank :=
  rfl

/-- The empty word's left/right delimiter traversal contains two cells. -/
example : (Tape.delimiterTraversal ([] : List Symbol)).card = 2 := by simp

def overlapMachine : Machine Control Symbol where
  ruleCount := 2
  rule
    | ⟨0, _⟩ =>
        { source := .start, scanned := .blank, written := .blank,
          move := .stay, target := .start }
    | ⟨1, _⟩ =>
        { source := .start, scanned := .blank, written := .mark .mark,
          move := .stay, target := .halt }

/-- First-match execution exists even though declarative unique applicability fails. -/
theorem overlapMachine_not_syntacticallyDeterministic :
    ¬overlapMachine.SyntacticallyDeterministic := by
  intro hdet
  have hindices : (0 : Fin 2) = (1 : Fin 2) := hdet rfl
  exact (by decide : (0 : Fin 2) ≠ 1) hindices

end Bennett.TuringAudit

#print axioms Bennett.Turing.TapeSymbol.card
#print axioms Bennett.Turing.Tape.support_cellsFrom
#print axioms Bennett.Turing.Tape.ofWord_injective
#print axioms Bennett.Turing.Machine.SyntacticallyDeterministic.stepRel_rightUnique
#print axioms Bennett.Turing.Machine.SyntacticallyDeterministic.step_eq_some_iff
#print axioms Bennett.Turing.Standard.BennettNormalForm.initial_step_exact
#print axioms Bennett.Turing.Standard.computes_output_unique
#print axioms Bennett.ExecutionTrace.runs_iff_exists_run
