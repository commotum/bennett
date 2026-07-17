import Bennett.Copy.Core
import Bennett.History.Run

/-!
# Compute-copy-uncompute construction

This file builds the reusable three-stage semantic macro as a composition of
mathlib `PEquiv`s.  It is intentionally not a concrete scheduler or union of
machine rule families; cross-stage rule non-overlap belongs to a later machine
instantiation.
-/

namespace Bennett.Uncompute

variable {α β Record Left Right : Type*}

/-- Lift a partial equivalence through an untouched right-hand register. -/
def liftRight (equiv : Left ≃. Right) (Register : Type*) :
    (Left × Register) ≃. (Right × Register) where
  toFun input := (equiv input.1).map fun output => (output, input.2)
  invFun output := (equiv.symm output.1).map fun input => (input, output.2)
  inv input output := by
    rcases input with ⟨left, register⟩
    rcases output with ⟨right, register'⟩
    simp only [Option.map_eq_some_iff]
    constructor
    · rintro ⟨input, hinput, hp⟩
      have hleft : input = left := congrArg Prod.fst hp
      have hregister : register' = register := congrArg Prod.snd hp
      subst input
      subst register'
      exact ⟨right, (equiv.eq_some_iff.mp hinput), rfl⟩
    · rintro ⟨output, houtput, hp⟩
      have hright : output = right := congrArg Prod.fst hp
      have hregister : register = register' := congrArg Prod.snd hp
      subst output
      subst register'
      exact ⟨left, (equiv.eq_some_iff.mpr houtput), rfl⟩

@[simp]
theorem liftRight_apply (equiv : Left ≃. Right) (Register : Type*)
    (left : Left) (register : Register) :
    liftRight equiv Register (left, register) =
      (equiv left).map fun right => (right, register) :=
  rfl

@[simp]
theorem liftRight_symm_apply (equiv : Left ≃. Right) (Register : Type*)
    (right : Right) (register : Register) :
    (liftRight equiv Register).symm (right, register) =
      (equiv.symm right).map fun left => (left, register) :=
  rfl

/-- Restrict identity to states accepted by an executable Boolean test. -/
def guard (accept : Left → Bool) : Left ≃. Left :=
  PEquiv.ofSet {state | accept state = true}

theorem guard_eq_some_iff (accept : Left → Bool) (state output : Left) :
    guard accept state = some output ↔
      accept state = true ∧ output = state := by
  change
    PEquiv.ofSet {state | accept state = true} state = some output ↔ _
  rw [PEquiv.ofSet_eq_some_iff]
  constructor
  · rintro ⟨rfl, haccept⟩
    exact ⟨haccept, rfl⟩
  · rintro ⟨haccept, rfl⟩
    exact ⟨rfl, haccept⟩

/-- A Boolean guard accepting exactly halted source configurations. -/
def haltGuard (step : PartialStep α) (Record : Type*) :
    HistoryState α Record ≃. HistoryState α Record :=
  guard fun state => (step state.current).isNone

@[simp]
theorem haltGuard_apply_iff (step : PartialStep α) (Record : Type*)
    (state : HistoryState α Record) :
    haltGuard step Record state = some state ↔ step.Halted state.current := by
  simp [haltGuard, guard, PEquiv.ofSet, PartialStep.Halted]

theorem haltGuard_eq_some_iff (step : PartialStep α) (Record : Type*)
    (state output : HistoryState α Record) :
    haltGuard step Record state = some output ↔
      step.Halted state.current ∧ output = state := by
  change
    guard (fun state : HistoryState α Record =>
      (step state.current).isNone) state = some output ↔ _
  rw [guard_eq_some_iff]
  simp [PartialStep.Halted]

/-- The exact `n`-step recorded execution as a partial equivalence. -/
def recordedEquivAt {step : PartialStep α}
    (recorder : HistoryRecorder step Record) (n : Nat) :
    HistoryState α Record ≃. HistoryState α Record :=
  (recorder.areInverses.iterate n).toInversePair

@[simp]
theorem recordedEquivAt_apply {step : PartialStep α}
    (recorder : HistoryRecorder step Record) (n : Nat)
    (state : HistoryState α Record) :
    recordedEquivAt recorder n state = recorder.forward.iterate n state :=
  rfl

@[simp]
theorem recordedEquivAt_symm_apply {step : PartialStep α}
    (recorder : HistoryRecorder step Record) (n : Nat)
    (state : HistoryState α Record) :
    (recordedEquivAt recorder n).symm state = recorder.backward.iterate n state :=
  rfl

/--
Compute for exactly `n` source steps, require a terminal source state, copy its
observed output onto a blank target, then uncompute exactly `n` steps.

The resulting macro is itself a partial equivalence.  Its inverse recomputes,
verifies/uncopies the output, and uncomputes again.
-/
def computeCopyUncompute {step : PartialStep α} [DecidableEq β]
    (recorder : HistoryRecorder step Record) (observe : α → β)
    (blank : β) (n : Nat) :
    (HistoryState α Record × β) ≃. (HistoryState α Record × β) :=
  let compute := liftRight (recordedEquivAt recorder n) β
  let requireHalt := liftRight (haltGuard step Record) β
  let copyOutput := Copy.observedEquiv (fun state => observe state.current) blank
  ((compute.trans requireHalt).trans copyOutput).trans compute.symm

end Bennett.Uncompute
