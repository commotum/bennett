import Bennett.Transition.Run
import Mathlib.Computability.StateTransition

/-!
# Reachability and mathlib evaluator bridges

This proof leaf connects exact transition counts to mathlib's existing
reflexive-transitive reachability and potentially divergent evaluator.  Keeping
the heavier computability import here lets exact-run consumers rebuild the
smaller `Transition.Run` module independently.
-/

namespace Bennett
namespace PartialStep

variable {α : Type*}

/-- Reachability reuses mathlib's state-transition closure. -/
abbrev ReachableFrom (step : PartialStep α) (start finish : α) : Prop :=
  StateTransition.Reaches step start finish

/-- The set of configurations reachable from `start`. -/
def reachableSet (step : PartialStep α) (start : α) : Set α :=
  {finish | step.ReachableFrom start finish}

/-- An exact finite run yields mathlib reachability. -/
theorem Runs.reachable {step : PartialStep α} {n : Nat} {start finish : α}
    (hrun : step.Runs n start finish) : step.ReachableFrom start finish := by
  induction n generalizing start with
  | zero =>
      have h : start = finish := (runs_zero_iff step start finish).mp hrun
      subst finish
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      obtain ⟨next, hstep, htail⟩ :=
        (runs_succ_iff step n start finish).mp hrun
      exact Relation.ReflTransGen.head hstep (ih htail)

/-- Mathlib reachability has an exact finite-run witness. -/
theorem reachable_iff_exists_runs (step : PartialStep α) (start finish : α) :
    step.ReachableFrom start finish ↔ ∃ n, step.Runs n start finish := by
  constructor
  · intro hreach
    induction hreach with
    | refl => exact ⟨0, step.runs_refl start⟩
    | @tail middle finish hprefix hlast ih =>
        obtain ⟨n, hrun⟩ := ih
        exact ⟨n + 1, runs_trans hrun (runs_one hlast)⟩
  · rintro ⟨n, hrun⟩
    exact hrun.reachable

theorem reachable_refl (step : PartialStep α) (state : α) :
    step.ReachableFrom state state :=
  Relation.ReflTransGen.refl

theorem ReachableFrom.step {step : PartialStep α} {initial before after : α}
    (hreach : step.ReachableFrom initial before) (hstep : step before = some after) :
    step.ReachableFrom initial after :=
  Relation.ReflTransGen.tail hreach hstep

theorem reachableSet_initial (step : PartialStep α) (initial : α) :
    initial ∈ step.reachableSet initial :=
  step.reachable_refl initial

theorem reachableSet_step {step : PartialStep α} {initial before after : α}
    (hbefore : before ∈ step.reachableSet initial) (hstep : step before = some after) :
    after ∈ step.reachableSet initial :=
  ReachableFrom.step hbefore hstep

/-- Project termination to mathlib's potentially divergent evaluator. -/
theorem terminates_iff_eval_dom (step : PartialStep α) (start : α) :
    step.Terminates start ↔ (StateTransition.eval step start).Dom := by
  constructor
  · rintro ⟨n, finish, hrun, hhalt⟩
    exact Part.dom_iff_mem.mpr
      ⟨finish, StateTransition.mem_eval.mpr ⟨hrun.reachable, hhalt⟩⟩
  · intro hdom
    obtain ⟨finish, hfinish⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨hreach, hhalt⟩ := StateTransition.mem_eval.mp hfinish
    obtain ⟨n, hrun⟩ := (reachable_iff_exists_runs step start finish).mp hreach
    exact ⟨n, finish, hrun, hhalt⟩

/-- The exact bridge from the library vocabulary to mathlib's evaluator theorem. -/
theorem mem_eval_iff (step : PartialStep α) (start finish : α) :
    finish ∈ StateTransition.eval step start ↔
      step.ReachableFrom start finish ∧ step.Halted finish :=
  StateTransition.mem_eval

end PartialStep
end Bennett
