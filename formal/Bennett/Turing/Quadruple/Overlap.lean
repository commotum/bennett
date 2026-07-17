import Bennett.Turing.Quadruple.Inverse

/-!
# Semantic and syntactic overlap of quadruples

Domain/range overlap is defined semantically as a nonempty intersection.  The
tape-wise tests from Bennett's paper are then proved as characterizations.  In
particular, range compatibility compares symbols *written* by two rewrite
actions; a move action imposes no cell-value restriction on its range.
-/

namespace Bennett.Turing

namespace Action

variable {Symbol : Type*}

/-- Two action domains can contain a common tape. -/
def DomainCompatible : Action Symbol → Action Symbol → Prop
  | .rewrite first _, .rewrite second _ => first = second
  | _, _ => True

/-- Two action ranges can contain a common tape. -/
def RangeCompatible : Action Symbol → Action Symbol → Prop
  | .rewrite _ first, .rewrite _ second => first = second
  | _, _ => True

instance [DecidableEq Symbol] (first second : Action Symbol) :
    Decidable (first.DomainCompatible second) := by
  cases first <;> cases second <;> simp [DomainCompatible] <;> infer_instance

instance [DecidableEq Symbol] (first second : Action Symbol) :
    Decidable (first.RangeCompatible second) := by
  cases first <;> cases second <;> simp [RangeCompatible] <;> infer_instance

/-- A canonical tape witnessing compatible action domains. -/
def commonDomainTape : Action Symbol → Action Symbol → Tape Symbol
  | .rewrite scanned _, _ => (Tape.blankAt 0).write scanned
  | .move _, .rewrite scanned _ => (Tape.blankAt 0).write scanned
  | .move _, .move _ => Tape.blankAt 0

theorem matches_commonDomainTape_left {first second : Action Symbol}
    (hcompatible : first.DomainCompatible second) :
    first.Matches (commonDomainTape first second) := by
  cases first <;> cases second <;>
    simp_all [DomainCompatible, commonDomainTape, Matches]

theorem matches_commonDomainTape_right {first second : Action Symbol}
    (hcompatible : first.DomainCompatible second) :
    second.Matches (commonDomainTape first second) := by
  cases first <;> cases second <;>
    simp_all [DomainCompatible, commonDomainTape, Matches]

@[simp] theorem inverse_domainCompatible_inverse
    (first second : Action Symbol) :
    first.inverse.DomainCompatible second.inverse ↔
      first.RangeCompatible second := by
  cases first <;> cases second <;>
    simp [DomainCompatible, RangeCompatible, inverse]

@[simp] theorem inverse_rangeCompatible_inverse
    (first second : Action Symbol) :
    first.inverse.RangeCompatible second.inverse ↔
      first.DomainCompatible second := by
  cases first <;> cases second <;>
    simp [DomainCompatible, RangeCompatible, inverse]

end Action

namespace Quadruple

variable {Control TapeIndex : Type*} {Symbol : TapeIndex → Type*}

/-- A configuration belongs to the semantic range of one rule. -/
def InRange (rule : Quadruple Control TapeIndex Symbol)
    (config : MultiConfiguration Control TapeIndex Symbol) : Prop :=
  ∃ before, rule.Matches before ∧ rule.execute before = config

/-- Two rule domains overlap when a complete configuration matches both. -/
def DomainsOverlap (first second : Quadruple Control TapeIndex Symbol) : Prop :=
  ∃ config, first.Matches config ∧ second.Matches config

/-- Two rule ranges overlap when a complete configuration is produced by both. -/
def RangesOverlap (first second : Quadruple Control TapeIndex Symbol) : Prop :=
  ∃ config, first.InRange config ∧ second.InRange config

/-- The paper's tape-wise domain-compatibility test. -/
def DomainCompatible (first second : Quadruple Control TapeIndex Symbol) : Prop :=
  first.source = second.source ∧
    ∀ index, (first.action index).DomainCompatible (second.action index)

/-- The corrected tape-wise range-compatibility test. -/
def RangeCompatible (first second : Quadruple Control TapeIndex Symbol) : Prop :=
  first.target = second.target ∧
    ∀ index, (first.action index).RangeCompatible (second.action index)

instance [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (first second : Quadruple Control TapeIndex Symbol) :
    Decidable (first.DomainCompatible second) := by
  unfold DomainCompatible
  infer_instance

instance [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (first second : Quadruple Control TapeIndex Symbol) :
    Decidable (first.RangeCompatible second) := by
  unfold RangeCompatible
  infer_instance

/-- Semantic domain overlap implies the tape-wise compatibility test. -/
theorem domainCompatible_of_domainsOverlap
    {first second : Quadruple Control TapeIndex Symbol}
    (hoverlap : first.DomainsOverlap second) :
    first.DomainCompatible second := by
  obtain ⟨config, hfirst, hsecond⟩ := hoverlap
  refine ⟨hfirst.1.trans hsecond.1.symm, ?_⟩
  intro index
  have hfirstTape := hfirst.2 index
  have hsecondTape := hsecond.2 index
  cases hfirstAction : first.action index <;>
    cases hsecondAction : second.action index <;>
      simp_all [Action.DomainCompatible, Action.Matches]

/-- Compatible rule domains have an explicit common configuration. -/
theorem domainsOverlap_of_domainCompatible
    {first second : Quadruple Control TapeIndex Symbol}
    (hcompatible : first.DomainCompatible second) :
    first.DomainsOverlap second := by
  let config : MultiConfiguration Control TapeIndex Symbol :=
    { control := first.source
      tape := fun index =>
        Action.commonDomainTape (first.action index) (second.action index) }
  refine ⟨config, ?_, ?_⟩
  · refine ⟨rfl, ?_⟩
    intro index
    exact Action.matches_commonDomainTape_left (hcompatible.2 index)
  · refine ⟨hcompatible.1.symm, ?_⟩
    intro index
    exact Action.matches_commonDomainTape_right (hcompatible.2 index)

/-- Bennett's domain-overlap criterion, proved from semantic overlap. -/
theorem domainsOverlap_iff_domainCompatible
    (first second : Quadruple Control TapeIndex Symbol) :
    first.DomainsOverlap second ↔ first.DomainCompatible second :=
  ⟨domainCompatible_of_domainsOverlap, domainsOverlap_of_domainCompatible⟩

instance [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (first second : Quadruple Control TapeIndex Symbol) :
    Decidable (first.DomainsOverlap second) :=
  if hcompatible : first.DomainCompatible second then
    isTrue (domainsOverlap_of_domainCompatible hcompatible)
  else
    isFalse fun hoverlap =>
      hcompatible (domainCompatible_of_domainsOverlap hoverlap)

/-- Range membership is exactly domain membership for the formal inverse. -/
theorem inRange_iff_inverse_matches
    (rule : Quadruple Control TapeIndex Symbol)
    (config : MultiConfiguration Control TapeIndex Symbol) :
    rule.InRange config ↔ rule.inverse.Matches config := by
  constructor
  · rintro ⟨before, hmatch, rfl⟩
    exact inverse_matches_execute hmatch
  · intro hmatch
    refine ⟨rule.inverse.execute config, ?_, ?_⟩
    · simpa using inverse_matches_execute (rule := rule.inverse) hmatch
    · exact execute_inverse hmatch

/-- Range overlap is domain overlap of the two formal inverse rules. -/
theorem rangesOverlap_iff_inverse_domainsOverlap
    (first second : Quadruple Control TapeIndex Symbol) :
    first.RangesOverlap second ↔
      first.inverse.DomainsOverlap second.inverse := by
  simp only [RangesOverlap, DomainsOverlap, inRange_iff_inverse_matches]

@[simp] theorem inverse_domainCompatible_inverse
    (first second : Quadruple Control TapeIndex Symbol) :
    first.inverse.DomainCompatible second.inverse ↔
      first.RangeCompatible second := by
  simp only [DomainCompatible, RangeCompatible, inverse_source,
    inverse_action, Action.inverse_domainCompatible_inverse]

/-- The corrected range-overlap criterion, proved from semantic overlap. -/
theorem rangesOverlap_iff_rangeCompatible
    (first second : Quadruple Control TapeIndex Symbol) :
    first.RangesOverlap second ↔ first.RangeCompatible second := by
  rw [rangesOverlap_iff_inverse_domainsOverlap,
    domainsOverlap_iff_domainCompatible, inverse_domainCompatible_inverse]

instance [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    (first second : Quadruple Control TapeIndex Symbol) :
    Decidable (first.RangesOverlap second) :=
  if hcompatible : first.RangeCompatible second then
    isTrue ((rangesOverlap_iff_rangeCompatible first second).2 hcompatible)
  else
    isFalse fun hoverlap =>
      hcompatible ((rangesOverlap_iff_rangeCompatible first second).1 hoverlap)

end Quadruple
end Bennett.Turing
