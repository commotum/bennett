import Bennett.Copy.Core

/-!
# Copying no-go diagnostics

Unrestricted overwrite discards the old target.  When the target type has two
distinct values it is noninjective, its successful-step graph has multiple
predecessors, and no partial inverse can exist.

This diagnostic leaf is not re-exported by the copy API.
-/

namespace Bennett.CopyAudit

variable {β : Type*}

/-- Destructive copying that ignores and overwrites the old target. -/
def overwrite : β × β → β × β
  | (value, _) => (value, value)

/-- The same destructive overwrite viewed as a total partial step. -/
def overwriteStep : PartialStep (β × β) :=
  fun state => some (overwrite state)

theorem overwrite_not_injective (value : β) {target₁ target₂ : β}
    (hne : target₁ ≠ target₂) : ¬Function.Injective (overwrite : β × β → β × β) := by
  intro hinjective
  have hpairs : (value, target₁) = (value, target₂) := hinjective rfl
  exact hne (congrArg Prod.snd hpairs)

theorem overwriteStep_not_reversible (value : β) {target₁ target₂ : β}
    (hne : target₁ ≠ target₂) : ¬(overwriteStep : PartialStep (β × β)).Reversible := by
  intro hrev
  have hpairs : (value, target₁) = (value, target₂) :=
    (PartialStep.reversible_iff overwriteStep).mp hrev rfl rfl
  exact hne (congrArg Prod.snd hpairs)

theorem overwriteStep_has_no_inverse (value : β) {target₁ target₂ : β}
    (hne : target₁ ≠ target₂) :
    ¬∃ backward : PartialStep (β × β), overwriteStep.AreInverses backward := by
  rintro ⟨backward, hinv⟩
  exact overwriteStep_not_reversible value hne hinv.forward_reversible

end Bennett.CopyAudit
