import Bennett.Transition.Core

/-!
# Finite runs of partial transitions

`PartialStep.iterate step n start` executes exactly `n` successful transitions,
returning `none` if any required step is unavailable.  This file supplies exact
finite runs, termination, composition, and generic reversal by a
specified inverse step.
-/

namespace Bennett
namespace PartialStep

variable {α : Type*}

/-- Execute exactly `n` successful transitions. -/
def iterate (step : PartialStep α) : Nat → PartialStep α
  | 0 => fun state => some state
  | n + 1 => fun state => (step state).bind (step.iterate n)

@[simp]
theorem iterate_zero (step : PartialStep α) (state : α) :
    step.iterate 0 state = some state :=
  rfl

@[simp]
theorem iterate_succ (step : PartialStep α) (n : Nat) (state : α) :
    step.iterate (n + 1) state = (step state).bind (step.iterate n) :=
  rfl

/-- Split an exact iteration after its first `m` transitions. -/
theorem iterate_add (step : PartialStep α) (m n : Nat) (state : α) :
    step.iterate (m + n) state =
      (step.iterate m state).bind (step.iterate n) := by
  induction m generalizing state with
  | zero => simp [iterate]
  | succ m ih =>
      simp only [Nat.succ_add, iterate_succ]
      cases hstep : step state with
      | none => simp
      | some next => simpa using ih next

/-- Expose the final transition of an exact nonempty iteration. -/
theorem iterate_succ_last (step : PartialStep α) (n : Nat) (state : α) :
    step.iterate (n + 1) state = (step.iterate n state).bind step := by
  simpa using step.iterate_add n 1 state

/-- `Runs step n start finish` means exactly `n` successful transitions. -/
def Runs (step : PartialStep α) (n : Nat) (start finish : α) : Prop :=
  step.iterate n start = some finish

/-- Halt after exactly `n` successful transitions. -/
def HaltsIn (step : PartialStep α) (n : Nat) (start : α) : Prop :=
  ∃ finish, step.Runs n start finish ∧ step.Halted finish

/-- Eventually halt after some finite number of successful transitions. -/
def Terminates (step : PartialStep α) (start : α) : Prop :=
  ∃ n, step.HaltsIn n start

@[simp]
theorem runs_zero_iff (step : PartialStep α) (start finish : α) :
    step.Runs 0 start finish ↔ start = finish := by
  simp [Runs]

theorem runs_refl (step : PartialStep α) (state : α) :
    step.Runs 0 state state :=
  rfl

theorem runs_one {step : PartialStep α} {start finish : α}
    (hstep : step start = some finish) : step.Runs 1 start finish := by
  simpa [Runs] using hstep

theorem runs_succ_iff (step : PartialStep α) (n : Nat) (start finish : α) :
    step.Runs (n + 1) start finish ↔
      ∃ next, step start = some next ∧ step.Runs n next finish := by
  simp [Runs, iterate, Option.bind_eq_some_iff]

theorem runs_add_iff (step : PartialStep α) (m n : Nat) (start finish : α) :
    step.Runs (m + n) start finish ↔
      ∃ middle, step.Runs m start middle ∧ step.Runs n middle finish := by
  simp [Runs, iterate_add, Option.bind_eq_some_iff]

theorem runs_trans {step : PartialStep α} {m n : Nat} {start middle finish : α}
    (hfirst : step.Runs m start middle) (hsecond : step.Runs n middle finish) :
    step.Runs (m + n) start finish := by
  rw [Runs, iterate_add, hfirst]
  exact hsecond

theorem runs_deterministic {step : PartialStep α} {n : Nat} {start finish₁ finish₂ : α}
    (h₁ : step.Runs n start finish₁) (h₂ : step.Runs n start finish₂) :
    finish₁ = finish₂ :=
  Option.some.inj (h₁.symm.trans h₂)

/-- Every finite forward iteration reverses under a graph inverse. -/
theorem AreInverses.reverse_iterate {forward backward : PartialStep α}
    (hinv : forward.AreInverses backward) {n : Nat} {before after : α}
    (hrun : forward.iterate n before = some after) :
    backward.iterate n after = some before := by
  induction n generalizing before after with
  | zero => simpa using hrun.symm
  | succ n ih =>
      rw [iterate_succ_last] at hrun
      obtain ⟨middle, hprefix, hlast⟩ := Option.bind_eq_some_iff.mp hrun
      have hback : backward after = some middle :=
        (hinv (before := middle) (after := after)).mp hlast
      have hreversePrefix : backward.iterate n middle = some before := ih hprefix
      simpa [iterate, hback] using hreversePrefix

/-- Pointwise inverse steps remain inverse after exactly `n` iterations. -/
theorem AreInverses.iterate {forward backward : PartialStep α}
    (hinv : forward.AreInverses backward) (n : Nat) :
    (forward.iterate n).AreInverses (backward.iterate n) := by
  intro before after
  exact ⟨hinv.reverse_iterate, hinv.symm.reverse_iterate⟩

theorem AreInverses.runs_iff {forward backward : PartialStep α}
    (hinv : forward.AreInverses backward) (n : Nat) (before after : α) :
    forward.Runs n before after ↔ backward.Runs n after before := by
  change forward.iterate n before = some after ↔
    backward.iterate n after = some before
  exact (hinv.iterate n) (before := before) (after := after)

theorem AreInverses.iterate_reversible {forward backward : PartialStep α}
    (hinv : forward.AreInverses backward) (n : Nat) :
    (forward.iterate n).Reversible :=
  (hinv.iterate n).forward_reversible

end PartialStep
end Bennett
