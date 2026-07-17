import Bennett.Transition.Core

/-!
# Reversible blank-target copying

Copying is a partial bijection, not unrestricted overwrite.  Forward execution
accepts exactly a known blank target; inverse execution accepts exactly an equal
source/target pair.  The observed variant retains an arbitrary work state and
copies only a classical observation of it.
-/

namespace Bennett.Copy

variable {β Work : Type*}

/-- Copy a value onto a target only when the target is the distinguished blank. -/
def blankForward [DecidableEq β] (blank : β) : PartialStep (β × β)
  | (value, target) => if target = blank then some (value, value) else none

/-- Erase only a verified duplicate, restoring the distinguished blank. -/
def blankBackward [DecidableEq β] (blank : β) : PartialStep (β × β)
  | (value, target) => if target = value then some (value, blank) else none

/-- Blank-target copy and verified uncopy as an executable partial equivalence. -/
def blankEquiv [DecidableEq β] (blank : β) : (β × β) ≃. (β × β) where
  toFun := blankForward blank
  invFun := blankBackward blank
  inv input output := by
    rcases input with ⟨value, target⟩
    rcases output with ⟨value', target'⟩
    simp only [blankForward, blankBackward]
    split_ifs <;> simp_all [eq_comm]

@[simp]
theorem blankForward_apply_blank [DecidableEq β] (blank value : β) :
    blankForward blank (value, blank) = some (value, value) := by
  simp [blankForward]

theorem blankForward_eq_some_iff [DecidableEq β] (blank value target : β)
    (output : β × β) :
    blankForward blank (value, target) = some output ↔
      target = blank ∧ output = (value, value) := by
  simp [blankForward, eq_comm]

@[simp]
theorem blankForward_eq_none_iff [DecidableEq β] (blank value target : β) :
    blankForward blank (value, target) = none ↔ target ≠ blank := by
  simp [blankForward]

@[simp]
theorem blankBackward_apply_copy [DecidableEq β] (blank value : β) :
    blankBackward blank (value, value) = some (value, blank) := by
  simp [blankBackward]

theorem blankBackward_eq_some_iff [DecidableEq β] (blank value target : β)
    (output : β × β) :
    blankBackward blank (value, target) = some output ↔
      target = value ∧ output = (value, blank) := by
  simp [blankBackward, eq_comm]

@[simp]
theorem blankBackward_eq_none_iff [DecidableEq β] (blank value target : β) :
    blankBackward blank (value, target) = none ↔ target ≠ value := by
  simp [blankBackward]

/-- Copy an observation while retaining the complete work state. -/
def observedForward [DecidableEq β] (observe : Work → β) (blank : β) :
    PartialStep (Work × β)
  | (work, target) =>
      if target = blank then some (work, observe work) else none

/-- Remove an observed copy only after verifying it against the retained work. -/
def observedBackward [DecidableEq β] (observe : Work → β) (blank : β) :
    PartialStep (Work × β)
  | (work, target) =>
      if target = observe work then some (work, blank) else none

/-- Retained-work observed copying as a partial equivalence. -/
def observedEquiv [DecidableEq β] (observe : Work → β) (blank : β) :
    (Work × β) ≃. (Work × β) where
  toFun := observedForward observe blank
  invFun := observedBackward observe blank
  inv input output := by
    rcases input with ⟨work, target⟩
    rcases output with ⟨work', target'⟩
    simp only [observedForward, observedBackward]
    split_ifs <;> simp_all [eq_comm]

@[simp]
theorem observedForward_apply_blank [DecidableEq β]
    (observe : Work → β) (blank : β) (work : Work) :
    observedForward observe blank (work, blank) = some (work, observe work) := by
  simp [observedForward]

theorem observedForward_eq_some_iff [DecidableEq β]
    (observe : Work → β) (blank target : β) (work outputWork : Work)
    (output : β) :
    observedForward observe blank (work, target) = some (outputWork, output) ↔
      target = blank ∧ outputWork = work ∧ output = observe work := by
  simp [observedForward, eq_comm]

@[simp]
theorem observedBackward_apply_copy [DecidableEq β]
    (observe : Work → β) (blank : β) (work : Work) :
    observedBackward observe blank (work, observe work) = some (work, blank) := by
  simp [observedBackward]

theorem observedBackward_eq_some_iff [DecidableEq β]
    (observe : Work → β) (blank target : β) (work outputWork : Work)
    (output : β) :
    observedBackward observe blank (work, target) = some (outputWork, output) ↔
      target = observe work ∧ outputWork = work ∧ output = blank := by
  simp [observedBackward, eq_comm]

end Bennett.Copy
