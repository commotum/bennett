import Bennett.Prelude
import Mathlib.Data.PEquiv

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

/-- Restrict both endpoints of the successful-step graph to `states`. -/
def GraphOn (step : PartialStep α) (states : Set α) (before after : α) : Prop :=
  before ∈ states ∧ after ∈ states ∧ step.Graph before after

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

/-- Mathlib's executable partial equivalence, specialized to one state type. -/
abbrev InversePair (α : Type*) := α ≃. α

theorem deterministic (step : PartialStep α) : step.Deterministic := by
  intro before after₁ after₂ h₁ h₂
  exact Option.some.inj (h₁.symm.trans h₂)

/-- The successful graph is right-unique in mathlib's standard vocabulary. -/
theorem graph_rightUnique (step : PartialStep α) :
    Relator.RightUnique step.Graph :=
  step.deterministic

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

/-- Restricted reversibility is standard left-uniqueness of the induced graph. -/
theorem reversibleOn_iff_leftUnique (step : PartialStep α) (states : Set α) :
    step.ReversibleOn states ↔ Relator.LeftUnique (step.GraphOn states) := by
  constructor
  · intro hrev before₁ before₂ after h₁ h₂
    exact hrev h₁.1 h₂.1 h₁.2.1 h₁.2.2 h₂.2.2
  · intro hleft before₁ before₂ after h₁ h₂ ha hs₁ hs₂
    exact hleft ⟨h₁, ha, hs₁⟩ ⟨h₂, ha, hs₂⟩

/-- Global reversibility is left-uniqueness of the successful graph. -/
theorem reversible_iff_leftUnique (step : PartialStep α) :
    step.Reversible ↔ Relator.LeftUnique step.Graph := by
  rw [reversible_iff]
  rfl

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

/-- Package converse successful-step graphs as a mathlib `PEquiv`. -/
def AreInverses.toInversePair {forward backward : PartialStep α}
    (hinv : forward.AreInverses backward) : InversePair α where
  toFun := forward
  invFun := backward
  inv before after := (hinv (before := before) (after := after)).symm

/-- Extract the graph-inverse law from a mathlib `PEquiv`. -/
theorem InversePair.areInverses (pair : InversePair α) :
    AreInverses pair.toFun pair.invFun := by
  intro before after
  exact (pair.inv before after).symm

theorem InversePair.forward_reversible (pair : InversePair α) :
    Reversible pair.toFun :=
  pair.areInverses.forward_reversible

theorem InversePair.backward_reversible (pair : InversePair α) :
    Reversible pair.invFun :=
  pair.areInverses.backward_reversible

end PartialStep

end Bennett
