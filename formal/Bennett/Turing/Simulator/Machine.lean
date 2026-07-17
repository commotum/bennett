import Bennett.Turing.Simulator.Copy
import Bennett.Turing.Simulator.Reverse

/-!
# Complete finite Table 1 machine

The proof-facing rule family is transported to the existing intrinsic
`Fin ruleCount` machine representation through an explicit equivalence.
Executable clients can supply a concrete enumeration; a choice-based adapter
is provided only as a convenience.
-/

namespace Bennett.Turing
namespace Simulator

variable {SourceControl Symbol : Type}
  [DecidableEq SourceControl] [DecidableEq Symbol]

/-- Complete rule dispatch for Bennett's three phases. -/
def tableRule {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) :
    TableRuleId source.RuleId Symbol → Rule source
  | .forward ruleId => forwardRule source ruleId
  | .copy ruleId => Copy.rule normal ruleId
  | .reverse ruleId => reverseRule source ruleId

/--
Executable finite packaging with a caller-supplied enumeration of nonnumeric
rule tags.  This definition is computational whenever `enumerate` is.
-/
def machineWithEnumeration [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol))) :
    QuadrupleMachine (Control SourceControl source.RuleId) TapeId
      (TapeAlphabet source) where
  ruleCount := Fintype.card (TableRuleId source.RuleId Symbol)
  rule index := tableRule normal (enumerate.symm index)

/-- Choice-based convenience packaging; use `machineWithEnumeration` for an
explicit executable ordering. -/
noncomputable def machine [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) :
    QuadrupleMachine (Control SourceControl source.RuleId) TapeId
      (TapeAlphabet source) :=
  machineWithEnumeration normal
    (Fintype.equivFin (TableRuleId source.RuleId Symbol))

@[simp] theorem machineWithEnumeration_ruleCount [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol))) :
    (machineWithEnumeration normal enumerate).ruleCount =
      4 * source.ruleCount + 2 * (Fintype.card Symbol + 1) + 3 := by
  simp [machineWithEnumeration]

@[simp] theorem machine_ruleCount [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) :
    (machine normal).ruleCount =
      4 * source.ruleCount + 2 * (Fintype.card Symbol + 1) + 3 := by
  simp [machine]

/-- Intrinsic machine index corresponding to one proof-facing rule tag. -/
def indexOf [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    {normal : Standard.BennettNormalForm source}
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    (ruleId : TableRuleId source.RuleId Symbol) :
    (machineWithEnumeration normal enumerate).RuleId :=
  enumerate ruleId

@[simp] theorem rule_indexOf [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    {normal : Standard.BennettNormalForm source}
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    (ruleId : TableRuleId source.RuleId Symbol) :
    (machineWithEnumeration normal enumerate).rule (indexOf enumerate ruleId) =
      tableRule normal ruleId := by
  simp [machineWithEnumeration, indexOf]

/-- A schedule containing only forward rules is contained in the full table. -/
theorem forwardRules_contained [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    {normal : Standard.BennettNormalForm source}
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    {rules : List (Rule source)}
    (hforward : OnlyForwardRules source rules) :
    ∀ rule, rule ∈ rules →
      ∃ index : (machineWithEnumeration normal enumerate).RuleId,
        (machineWithEnumeration normal enumerate).rule index = rule := by
  intro rule hmem
  obtain ⟨ruleId, hrule⟩ := hforward rule hmem
  exact ⟨indexOf enumerate (.forward ruleId), by simpa [tableRule] using hrule⟩

/-- The concrete copy schedule is contained in the full table. -/
theorem copyRules_contained [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    {normal : Standard.BennettNormalForm source}
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    (word : List Symbol) :
    ∀ rule, rule ∈ Copy.schedule normal word →
      ∃ index : (machineWithEnumeration normal enumerate).RuleId,
        (machineWithEnumeration normal enumerate).rule index = rule := by
  intro displayed hmem
  simp only [Copy.schedule, List.mem_map] at hmem
  obtain ⟨ruleId, _, rfl⟩ := hmem
  exact ⟨indexOf enumerate (.copy ruleId), by simp [tableRule]⟩

/-- A schedule containing only reverse rules is contained in the full table. -/
theorem reverseRules_contained [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    {normal : Standard.BennettNormalForm source}
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    {rules : List (Rule source)}
    (hreverse : OnlyReverseRules source rules) :
    ∀ rule, rule ∈ rules →
      ∃ index : (machineWithEnumeration normal enumerate).RuleId,
        (machineWithEnumeration normal enumerate).rule index = rule := by
  intro rule hmem
  obtain ⟨ruleId, hrule⟩ := hreverse rule hmem
  exact ⟨indexOf enumerate (.reverse ruleId), by simpa [tableRule] using hrule⟩

/-- Enumeration-independent statement that a schedule uses only Table 1 rules. -/
def OnlyTableRules {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (rules : List (Rule source)) : Prop :=
  ∀ rule, rule ∈ rules →
    ∃ ruleId : TableRuleId source.RuleId Symbol,
      tableRule normal ruleId = rule

theorem OnlyTableRules.append
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    {first second : List (Rule source)}
    (hfirst : OnlyTableRules normal first)
    (hsecond : OnlyTableRules normal second) :
    OnlyTableRules normal (first ++ second) := by
  intro rule hmem
  rw [List.mem_append] at hmem
  exact hmem.elim (hfirst rule) (hsecond rule)

theorem onlyTableRules_of_forward
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    {rules : List (Rule source)}
    (hforward : OnlyForwardRules source rules) :
    OnlyTableRules normal rules := by
  intro rule hmem
  obtain ⟨ruleId, hrule⟩ := hforward rule hmem
  exact ⟨.forward ruleId, by simpa [tableRule] using hrule⟩

theorem onlyTableRules_copy
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) (word : List Symbol) :
    OnlyTableRules normal (Copy.schedule normal word) := by
  intro displayed hmem
  simp only [Copy.schedule, List.mem_map] at hmem
  obtain ⟨ruleId, _, rfl⟩ := hmem
  exact ⟨.copy ruleId, rfl⟩

theorem onlyTableRules_of_reverse
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    {rules : List (Rule source)}
    (hreverse : OnlyReverseRules source rules) :
    OnlyTableRules normal rules := by
  intro rule hmem
  obtain ⟨ruleId, hrule⟩ := hreverse rule hmem
  exact ⟨.reverse ruleId, by simpa [tableRule] using hrule⟩

/-- Any constructor-tagged Table 1 schedule is contained after enumeration. -/
theorem tableRules_contained [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    {normal : Standard.BennettNormalForm source}
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    {rules : List (Rule source)}
    (htable : OnlyTableRules normal rules) :
    ∀ rule, rule ∈ rules →
      ∃ index : (machineWithEnumeration normal enumerate).RuleId,
        (machineWithEnumeration normal enumerate).rule index = rule := by
  intro rule hmem
  obtain ⟨ruleId, hrule⟩ := htable rule hmem
  exact ⟨indexOf enumerate ruleId, by simpa using hrule⟩

end Simulator
end Bennett.Turing
