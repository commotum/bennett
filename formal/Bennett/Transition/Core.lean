import Bennett.Prelude

/-!
# Deterministic partial transitions

This file defines the executable semantic core used throughout the library.  A
partial transition is an `Option`-valued function, so it has at most one
successor by construction.  Reversibility is stated separately as uniqueness of
a predecessor among successful transitions; it is deliberately not ordinary
injectivity of the `Option`-valued function, because many distinct halted states
may all map to `none`.
-/

namespace Bennett

/-- An executable deterministic partial transition on states of type `α`. -/
abbrev PartialStep (α : Type*) := α → Option α

namespace PartialStep

variable {α : Type*}

/-- The successful-step graph of a partial transition. -/
def Graph (step : PartialStep α) (before after : α) : Prop :=
  step before = some after

/-- A state is enabled when it has a successor. -/
def Enabled (step : PartialStep α) (state : α) : Prop :=
  ∃ after, step state = some after

/-- A state is halted when its partial transition is undefined. -/
def Halted (step : PartialStep α) (state : α) : Prop :=
  step state = none

/-- Extensional successor uniqueness.  Every `PartialStep` satisfies this. -/
def Deterministic (step : PartialStep α) : Prop :=
  ∀ ⦃before after₁ after₂⦄,
    step before = some after₁ → step before = some after₂ → after₁ = after₂

/--
Predecessor uniqueness restricted to a set of states.

All two predecessors and their common successor must lie in `states`.  This is
the semantic notion needed for reversibility only on well-formed or reachable
configurations.
-/
def ReversibleOn (step : PartialStep α) (states : Set α) : Prop :=
  ∀ ⦃before₁ before₂ after⦄,
    before₁ ∈ states →
      before₂ ∈ states →
        after ∈ states →
          step before₁ = some after → step before₂ = some after → before₁ = before₂

/-- Global predecessor uniqueness over every state. -/
def Reversible (step : PartialStep α) : Prop :=
  step.ReversibleOn Set.univ

/-- Two partial steps have exactly converse successful-step graphs. -/
def AreInverses (forward backward : PartialStep α) : Prop :=
  ∀ ⦃before after⦄, forward before = some after ↔ backward after = some before

/-- A partial transition bundled with a specified inverse transition. -/
structure InversePair (α : Type*) where
  forward : PartialStep α
  backward : PartialStep α
  inverse : forward.AreInverses backward

theorem deterministic (step : PartialStep α) : step.Deterministic := by
  intro before after₁ after₂ h₁ h₂
  exact Option.some.inj (h₁.symm.trans h₂)

theorem enabled_iff_not_halted (step : PartialStep α) (state : α) :
    step.Enabled state ↔ ¬step.Halted state := by
  cases h : step state with
  | none => simp [Enabled, Halted, h]
  | some after => simp [Enabled, Halted, h]

theorem enabled_or_halted (step : PartialStep α) (state : α) :
    step.Enabled state ∨ step.Halted state := by
  cases h : step state with
  | none => exact Or.inr h
  | some after => exact Or.inl ⟨after, h⟩

theorem ReversibleOn.mono {step : PartialStep α} {smaller larger : Set α}
    (hrev : step.ReversibleOn larger) (hsub : smaller ⊆ larger) :
    step.ReversibleOn smaller := by
  intro before₁ before₂ after h₁ h₂ ha hs₁ hs₂
  exact hrev (hsub h₁) (hsub h₂) (hsub ha) hs₁ hs₂

theorem reversible_iff (step : PartialStep α) :
    step.Reversible ↔
      ∀ ⦃before₁ before₂ after⦄,
        step before₁ = some after → step before₂ = some after → before₁ = before₂ := by
  simp [Reversible, ReversibleOn]

theorem AreInverses.symm {forward backward : PartialStep α}
    (hinv : forward.AreInverses backward) : backward.AreInverses forward := by
  intro before after
  exact (hinv (before := after) (after := before)).symm

theorem AreInverses.forward_reversible {forward backward : PartialStep α}
    (hinv : forward.AreInverses backward) : forward.Reversible := by
  rw [reversible_iff]
  intro before₁ before₂ after h₁ h₂
  have hb₁ : backward after = some before₁ :=
    (hinv (before := before₁) (after := after)).mp h₁
  have hb₂ : backward after = some before₂ :=
    (hinv (before := before₂) (after := after)).mp h₂
  exact Option.some.inj (hb₁.symm.trans hb₂)

theorem AreInverses.backward_reversible {forward backward : PartialStep α}
    (hinv : forward.AreInverses backward) : backward.Reversible :=
  hinv.symm.forward_reversible

theorem InversePair.forward_reversible (pair : InversePair α) :
    pair.forward.Reversible :=
  pair.inverse.forward_reversible

theorem InversePair.backward_reversible (pair : InversePair α) :
    pair.backward.Reversible :=
  pair.inverse.backward_reversible

end PartialStep

end Bennett
