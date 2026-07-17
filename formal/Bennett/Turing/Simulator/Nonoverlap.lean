import Bennett.Turing.Simulator.Machine

namespace Bennett.Turing
namespace Simulator

open Bennett.Turing

variable {SourceControl Symbol : Type}

/-- Complete Table 1 dispatch with only its genuine boundary parameters. -/
def tableRuleAt (source : Machine SourceControl Symbol)
    (finish : SourceControl) (terminal : source.RuleId) :
    TableRuleId source.RuleId Symbol → Rule source
  | .forward ruleId => forwardRule source ruleId
  | .copy ruleId => Copy.ruleAt source finish terminal ruleId
  | .reverse ruleId => reverseRule source ruleId

/-!
The proof-facing Table 1 rule family is pairwise domain/range disjoint under
the two assumptions it actually uses:

* injectivity of source `(control, scanned-symbol)` keys; and
* absence of a source rule with key `(finish, blank)`.

`Standard.BennettNormalForm` supplies both, but its other entry/exit fields are
irrelevant to this syntactic argument.
-/

def NoFinishBlankRule (source : Machine SourceControl Symbol)
    (finish : SourceControl) : Prop :=
  ∀ id : source.RuleId,
    (source.rule id).source = finish →
      (source.rule id).scanned ≠ .blank

theorem noFinishBlankRule_of_normal
    [DecidableEq SourceControl] [DecidableEq Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) :
    NoFinishBlankRule source normal.finish := by
  intro id hsource _
  exact normal.no_rule_sources_finish id hsource

private theorem sourceRule_eq_of_key_eq
    {source : Machine SourceControl Symbol}
    (hdet : source.SyntacticallyDeterministic)
    {first second : source.RuleId}
    (hsource : (source.rule first).source = (source.rule second).source)
    (hscan : (source.rule first).scanned = (source.rule second).scanned) :
    first = second := by
  apply hdet
  exact Prod.ext hsource hscan

theorem compute_domainCompatible_eq
    {source : Machine SourceControl Symbol}
    (hdet : source.SyntacticallyDeterministic)
    {first second : ForwardRuleId source.RuleId}
    (hcompat : (forwardRule source first).DomainCompatible
      (forwardRule source second)) :
    first = second := by
  cases first with
  | rewrite first =>
      cases second with
      | rewrite second =>
          have hs : (source.rule first).source =
              (source.rule second).source := by
            simpa [forwardRule, forwardRewriteRule, forwardRecordRule,
              threeRule, Quadruple.DomainCompatible] using
              hcompat.1
          have hr := hcompat.2 TapeId.work
          have hscan : (source.rule first).scanned =
              (source.rule second).scanned := by
            change (source.rule first).scanned =
              (source.rule second).scanned at hr
            exact hr
          exact congrArg ForwardRuleId.rewrite
            (sourceRule_eq_of_key_eq hdet hs hscan)
      | moveRecord second =>
          simp [forwardRule, forwardRewriteRule, forwardRecordRule,
            threeRule, Quadruple.DomainCompatible] at hcompat
  | moveRecord first =>
      cases second with
      | rewrite second =>
          simp [forwardRule, forwardRewriteRule, forwardRecordRule,
            threeRule, Quadruple.DomainCompatible] at hcompat
      | moveRecord second =>
          have hid : first = second := by
            simpa [forwardRule, forwardRewriteRule, forwardRecordRule,
              threeRule, Quadruple.DomainCompatible] using
              hcompat.1
          exact congrArg ForwardRuleId.moveRecord hid

theorem compute_rangeCompatible_eq
    {source : Machine SourceControl Symbol}
    {first second : ForwardRuleId source.RuleId}
    (hcompat : (forwardRule source first).RangeCompatible
      (forwardRule source second)) :
    first = second := by
  cases first with
  | rewrite first =>
      cases second with
      | rewrite second =>
          have hid : first = second := by
            simpa [forwardRule, forwardRewriteRule, forwardRecordRule,
              threeRule, Quadruple.RangeCompatible] using
              hcompat.1
          exact congrArg ForwardRuleId.rewrite hid
      | moveRecord second =>
          simp [forwardRule, forwardRewriteRule, forwardRecordRule,
            threeRule, Quadruple.RangeCompatible] at hcompat
  | moveRecord first =>
      cases second with
      | rewrite second =>
          simp [forwardRule, forwardRewriteRule, forwardRecordRule,
            threeRule, Quadruple.RangeCompatible] at hcompat
      | moveRecord second =>
          have hr := hcompat.2 TapeId.history
          have hid : first = second := by
            change TapeSymbol.mark first = TapeSymbol.mark second at hr
            exact TapeSymbol.mark.inj hr
          exact congrArg ForwardRuleId.moveRecord hid

-- Exhaustive copy-domain matrix; simplification follows full case splitting.
set_option linter.flexible false in
theorem copy_domainCompatible_eq
    {source : Machine SourceControl Symbol} (finish : SourceControl)
    (terminal : source.RuleId)
    {first second : CopyRuleId Symbol}
    (hcompat : (Copy.ruleAt source finish terminal first).DomainCompatible
      (Copy.ruleAt source finish terminal second)) :
    first = second := by
  cases first <;> cases second <;>
    simp_all [Copy.ruleAt, threeRule, Quadruple.DomainCompatible,
      Action.DomainCompatible] <;>
    have hw := hcompat TapeId.work <;>
    simp_all <;>
    exact TapeSymbol.mark.inj hw

-- Exhaustive copy-range matrix; simplification follows full case splitting.
set_option linter.flexible false in
theorem copy_rangeCompatible_eq
    {source : Machine SourceControl Symbol} (finish : SourceControl)
    (terminal : source.RuleId)
    {first second : CopyRuleId Symbol}
    (hcompat : (Copy.ruleAt source finish terminal first).RangeCompatible
      (Copy.ruleAt source finish terminal second)) :
    first = second := by
  cases first <;> cases second <;>
    simp_all [Copy.ruleAt, threeRule, Quadruple.RangeCompatible,
      Action.RangeCompatible] <;>
    have hw := hcompat TapeId.work <;>
    simp_all <;>
    exact TapeSymbol.mark.inj hw

theorem retrace_domainCompatible_eq
    {source : Machine SourceControl Symbol}
    {first second : ReverseRuleId source.RuleId}
    (hcompat : (reverseRule source first).DomainCompatible
      (reverseRule source second)) :
    first = second := by
  cases first with
  | eraseRecordMove first =>
      cases second with
      | eraseRecordMove second =>
          have hr := hcompat.2 TapeId.history
          have hid : first = second := by
            change TapeSymbol.mark first = TapeSymbol.mark second at hr
            exact TapeSymbol.mark.inj hr
          exact congrArg ReverseRuleId.eraseRecordMove hid
      | restoreSymbol second =>
          simp [reverseRule, reverseEraseRule, reverseRestoreRule,
            threeRule, Quadruple.DomainCompatible] at hcompat
  | restoreSymbol first =>
      cases second with
      | eraseRecordMove second =>
          simp [reverseRule, reverseEraseRule, reverseRestoreRule,
            threeRule, Quadruple.DomainCompatible] at hcompat
      | restoreSymbol second =>
          have hid : first = second := by
            simpa [reverseRule, reverseEraseRule, reverseRestoreRule,
              threeRule, Quadruple.DomainCompatible] using
              hcompat.1
          exact congrArg ReverseRuleId.restoreSymbol hid

theorem retrace_rangeCompatible_eq
    {source : Machine SourceControl Symbol}
    (hdet : source.SyntacticallyDeterministic)
    {first second : ReverseRuleId source.RuleId}
    (hcompat : (reverseRule source first).RangeCompatible
      (reverseRule source second)) :
    first = second := by
  cases first with
  | eraseRecordMove first =>
      cases second with
      | eraseRecordMove second =>
          have hid : first = second := by
            simpa [reverseRule, reverseEraseRule, reverseRestoreRule,
              threeRule, Quadruple.RangeCompatible] using
              hcompat.1
          exact congrArg ReverseRuleId.eraseRecordMove hid
      | restoreSymbol second =>
          simp [reverseRule, reverseEraseRule, reverseRestoreRule,
            threeRule, Quadruple.RangeCompatible] at hcompat
  | restoreSymbol first =>
      cases second with
      | eraseRecordMove second =>
          simp [reverseRule, reverseEraseRule, reverseRestoreRule,
            threeRule, Quadruple.RangeCompatible] at hcompat
      | restoreSymbol second =>
          have hs : (source.rule first).source =
              (source.rule second).source := by
            simpa [reverseRule, reverseEraseRule, reverseRestoreRule,
              threeRule, Quadruple.RangeCompatible] using
              hcompat.1
          have hr := hcompat.2 TapeId.work
          have hscan : (source.rule first).scanned =
              (source.rule second).scanned := by
            change (source.rule first).scanned =
              (source.rule second).scanned at hr
            exact hr
          exact congrArg ReverseRuleId.restoreSymbol
            (sourceRule_eq_of_key_eq hdet hs hscan)

private theorem actionDomainCompatible_symm
    {S : Type} {first second : Action S}
    (hcompat : first.DomainCompatible second) :
    second.DomainCompatible first := by
  cases first <;> cases second <;>
    simp_all [Action.DomainCompatible]

private theorem actionRangeCompatible_symm
    {S : Type} {first second : Action S}
    (hcompat : first.RangeCompatible second) :
    second.RangeCompatible first := by
  cases first <;> cases second <;>
    simp_all [Action.RangeCompatible]

private theorem domainCompatible_symm
    {source : Machine SourceControl Symbol} {first second : Rule source}
    (hcompat : first.DomainCompatible second) :
    second.DomainCompatible first := by
  refine ⟨hcompat.1.symm, ?_⟩
  intro index
  exact actionDomainCompatible_symm (hcompat.2 index)

private theorem rangeCompatible_symm
    {source : Machine SourceControl Symbol} {first second : Rule source}
    (hcompat : first.RangeCompatible second) :
    second.RangeCompatible first := by
  refine ⟨hcompat.1.symm, ?_⟩
  intro index
  exact actionRangeCompatible_symm (hcompat.2 index)

-- Boundary-domain matrix; simplification follows full case splitting.
set_option linter.flexible false in
theorem compute_copy_domain_incompatible
    {source : Machine SourceControl Symbol} {finish : SourceControl}
    {terminal : source.RuleId}
    (hfinish : NoFinishBlankRule source finish)
    (first : ForwardRuleId source.RuleId) (second : CopyRuleId Symbol) :
    ¬(forwardRule source first).DomainCompatible
      (Copy.ruleAt source finish terminal second) := by
  intro hcompat
  cases first <;> cases second <;>
    simp [forwardRule, forwardRewriteRule, forwardRecordRule, Copy.ruleAt,
      threeRule, Quadruple.DomainCompatible] at hcompat
  all_goals
    have hw := hcompat.2 TapeId.work
    change (source.rule _).scanned = TapeSymbol.blank at hw
    exact hfinish _ hcompat.1 hw

theorem compute_retrace_domain_incompatible
    {source : Machine SourceControl Symbol}
    (first : ForwardRuleId source.RuleId)
    (second : ReverseRuleId source.RuleId) :
    ¬(forwardRule source first).DomainCompatible
      (reverseRule source second) := by
  intro hcompat
  cases first <;> cases second <;>
    simp [forwardRule, forwardRewriteRule, forwardRecordRule, reverseRule,
      reverseEraseRule, reverseRestoreRule, threeRule,
      Quadruple.DomainCompatible] at hcompat

theorem copy_retrace_domain_incompatible
    {source : Machine SourceControl Symbol} (finish : SourceControl)
    (terminal : source.RuleId)
    (first : CopyRuleId Symbol) (second : ReverseRuleId source.RuleId) :
    ¬(Copy.ruleAt source finish terminal first).DomainCompatible
      (reverseRule source second) := by
  intro hcompat
  cases first <;> cases second <;>
    simp [Copy.ruleAt, reverseRule, reverseEraseRule, reverseRestoreRule,
      threeRule, Quadruple.DomainCompatible] at hcompat

theorem compute_copy_range_incompatible
    {source : Machine SourceControl Symbol} (finish : SourceControl)
    (terminal : source.RuleId)
    (first : ForwardRuleId source.RuleId) (second : CopyRuleId Symbol) :
    ¬(forwardRule source first).RangeCompatible
      (Copy.ruleAt source finish terminal second) := by
  intro hcompat
  cases first <;> cases second <;>
    simp [forwardRule, forwardRewriteRule, forwardRecordRule, Copy.ruleAt,
      threeRule, Quadruple.RangeCompatible] at hcompat

theorem compute_retrace_range_incompatible
    {source : Machine SourceControl Symbol}
    (first : ForwardRuleId source.RuleId)
    (second : ReverseRuleId source.RuleId) :
    ¬(forwardRule source first).RangeCompatible
      (reverseRule source second) := by
  intro hcompat
  cases first <;> cases second <;>
    simp [forwardRule, forwardRewriteRule, forwardRecordRule, reverseRule,
      reverseEraseRule, reverseRestoreRule, threeRule,
      Quadruple.RangeCompatible] at hcompat

-- Boundary-range matrix; simplification follows full case splitting.
set_option linter.flexible false in
theorem copy_retrace_range_incompatible
    {source : Machine SourceControl Symbol} {finish : SourceControl}
    {terminal : source.RuleId}
    (hfinish : NoFinishBlankRule source finish)
    (first : CopyRuleId Symbol) (second : ReverseRuleId source.RuleId) :
    ¬(Copy.ruleAt source finish terminal first).RangeCompatible
      (reverseRule source second) := by
  intro hcompat
  cases first <;> cases second <;>
    simp [Copy.ruleAt, reverseRule, reverseEraseRule, reverseRestoreRule,
      threeRule, Quadruple.RangeCompatible] at hcompat
  all_goals
    have hw := hcompat.2 TapeId.work
    change TapeSymbol.blank = (source.rule _).scanned at hw
    exact hfinish _ hcompat.1.symm hw.symm

/-- Compatibility of complete-family domains identifies the rule tag. -/
theorem rule_domainCompatible_eq
    {source : Machine SourceControl Symbol} {finish : SourceControl}
    {terminal : source.RuleId}
    (hdet : source.SyntacticallyDeterministic)
    (hfinish : NoFinishBlankRule source finish)
    {first second : TableRuleId source.RuleId Symbol}
    (hcompat : (tableRuleAt source finish terminal first).DomainCompatible
      (tableRuleAt source finish terminal second)) :
    first = second := by
  cases first with
  | forward first =>
      cases second with
      | forward second =>
          exact congrArg TableRuleId.forward
            (compute_domainCompatible_eq hdet hcompat)
      | copy second =>
          exact False.elim
            (compute_copy_domain_incompatible hfinish first second hcompat)
      | reverse second =>
          exact False.elim
            (compute_retrace_domain_incompatible first second hcompat)
  | copy first =>
      cases second with
      | forward second =>
          exact False.elim (compute_copy_domain_incompatible hfinish
            second first (domainCompatible_symm hcompat))
      | copy second =>
          exact congrArg TableRuleId.copy
            (copy_domainCompatible_eq finish terminal hcompat)
      | reverse second =>
          exact False.elim
            (copy_retrace_domain_incompatible finish terminal first second hcompat)
  | reverse first =>
      cases second with
      | forward second =>
          exact False.elim (compute_retrace_domain_incompatible second first
            (domainCompatible_symm hcompat))
      | copy second =>
          exact False.elim (copy_retrace_domain_incompatible finish terminal
            second first (domainCompatible_symm hcompat))
      | reverse second =>
          exact congrArg TableRuleId.reverse
            (retrace_domainCompatible_eq hcompat)

/-- Compatibility of complete-family ranges identifies the rule tag. -/
theorem rule_rangeCompatible_eq
    {source : Machine SourceControl Symbol} {finish : SourceControl}
    {terminal : source.RuleId}
    (hdet : source.SyntacticallyDeterministic)
    (hfinish : NoFinishBlankRule source finish)
    {first second : TableRuleId source.RuleId Symbol}
    (hcompat : (tableRuleAt source finish terminal first).RangeCompatible
      (tableRuleAt source finish terminal second)) :
    first = second := by
  cases first with
  | forward first =>
      cases second with
      | forward second =>
          exact congrArg TableRuleId.forward
            (compute_rangeCompatible_eq hcompat)
      | copy second =>
          exact False.elim
            (compute_copy_range_incompatible finish terminal first second hcompat)
      | reverse second =>
          exact False.elim
            (compute_retrace_range_incompatible first second hcompat)
  | copy first =>
      cases second with
      | forward second =>
          exact False.elim (compute_copy_range_incompatible finish terminal
            second first (rangeCompatible_symm hcompat))
      | copy second =>
          exact congrArg TableRuleId.copy
            (copy_rangeCompatible_eq finish terminal hcompat)
      | reverse second =>
          exact False.elim
            (copy_retrace_range_incompatible hfinish first second hcompat)
  | reverse first =>
      cases second with
      | forward second =>
          exact False.elim (compute_retrace_range_incompatible second first
            (rangeCompatible_symm hcompat))
      | copy second =>
          exact False.elim (copy_retrace_range_incompatible hfinish second first
            (rangeCompatible_symm hcompat))
      | reverse second =>
          exact congrArg TableRuleId.reverse
            (retrace_rangeCompatible_eq hdet hcompat)

/-- Distinct complete-family rule tags have disjoint semantic domains. -/
theorem rules_domains_disjoint
    {source : Machine SourceControl Symbol} {finish : SourceControl}
    {terminal : source.RuleId}
    (hdet : source.SyntacticallyDeterministic)
    (hfinish : NoFinishBlankRule source finish)
    {first second : TableRuleId source.RuleId Symbol} (hne : first ≠ second) :
    ¬(tableRuleAt source finish terminal first).DomainsOverlap
      (tableRuleAt source finish terminal second) := by
  intro hoverlap
  apply hne
  exact rule_domainCompatible_eq hdet hfinish
    (Quadruple.domainCompatible_of_domainsOverlap hoverlap)

/-- Distinct complete-family rule tags have disjoint semantic ranges. -/
theorem rules_ranges_disjoint
    {source : Machine SourceControl Symbol} {finish : SourceControl}
    {terminal : source.RuleId}
    (hdet : source.SyntacticallyDeterministic)
    (hfinish : NoFinishBlankRule source finish)
    {first second : TableRuleId source.RuleId Symbol} (hne : first ≠ second) :
    ¬(tableRuleAt source finish terminal first).RangesOverlap
      (tableRuleAt source finish terminal second) := by
  intro hoverlap
  apply hne
  exact rule_rangeCompatible_eq hdet hfinish
    ((Quadruple.rangesOverlap_iff_rangeCompatible _ _).mp hoverlap)

/-- Bennett normal form supplies the exact assumptions used by both proofs. -/
theorem rules_syntacticallyReversible_of_normal
    [DecidableEq SourceControl] [DecidableEq Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) :
    (∀ {first second : TableRuleId source.RuleId Symbol}, first ≠ second →
      ¬(tableRuleAt source normal.finish normal.exitId first).DomainsOverlap
        (tableRuleAt source normal.finish normal.exitId second)) ∧
    (∀ {first second : TableRuleId source.RuleId Symbol}, first ≠ second →
      ¬(tableRuleAt source normal.finish normal.exitId first).RangesOverlap
        (tableRuleAt source normal.finish normal.exitId second)) := by
  have hfinish := noFinishBlankRule_of_normal normal
  exact ⟨rules_domains_disjoint normal.syntacticDeterminism hfinish,
    rules_ranges_disjoint normal.syntacticDeterminism hfinish⟩

/-! The two assumptions above are not proof artifacts: their violations
produce the precise Table 1 overlaps described below. -/

theorem finish_blank_causes_compute_enter_domain_overlap
    {source : Machine SourceControl Symbol} {finish : SourceControl}
    (terminal id : source.RuleId)
    (hsource : (source.rule id).source = finish)
    (hscan : (source.rule id).scanned = .blank) :
    (forwardRule source (.rewrite id)).DomainsOverlap
      (Copy.ruleAt source finish terminal .enter) := by
  apply Quadruple.domainsOverlap_of_domainCompatible
  constructor
  · simp [forwardRule, forwardRewriteRule, Copy.ruleAt, threeRule, hsource]
  · intro index
    cases index <;>
      simp [forwardRule, forwardRewriteRule, Copy.ruleAt, threeRule,
        Action.DomainCompatible, hscan]

theorem finish_blank_causes_exit_restore_range_overlap
    {source : Machine SourceControl Symbol} {finish : SourceControl}
    (terminal id : source.RuleId)
    (hsource : (source.rule id).source = finish)
    (hscan : (source.rule id).scanned = .blank) :
    (Copy.ruleAt source finish terminal .exit).RangesOverlap
      (reverseRule source (.restoreSymbol id)) := by
  rw [Quadruple.rangesOverlap_iff_rangeCompatible]
  constructor
  · simp [Copy.ruleAt, reverseRule, reverseRestoreRule, threeRule, hsource]
  · intro index
    cases index <;>
      simp [Copy.ruleAt, reverseRule, reverseRestoreRule, threeRule,
        Action.RangeCompatible, hscan]

theorem duplicate_key_causes_compute_domain_overlap
    {source : Machine SourceControl Symbol} (first second : source.RuleId)
    (hsource : (source.rule first).source = (source.rule second).source)
    (hscan : (source.rule first).scanned = (source.rule second).scanned) :
    (forwardRule source (.rewrite first)).DomainsOverlap
      (forwardRule source (.rewrite second)) := by
  apply Quadruple.domainsOverlap_of_domainCompatible
  constructor
  · simp [forwardRule, forwardRewriteRule, threeRule, hsource]
  · intro index
    cases index <;>
      simp [forwardRule, forwardRewriteRule, threeRule, Action.DomainCompatible, hscan]

theorem duplicate_key_causes_restore_range_overlap
    {source : Machine SourceControl Symbol} (first second : source.RuleId)
    (hsource : (source.rule first).source = (source.rule second).source)
    (hscan : (source.rule first).scanned = (source.rule second).scanned) :
    (reverseRule source (.restoreSymbol first)).RangesOverlap
      (reverseRule source (.restoreSymbol second)) := by
  rw [Quadruple.rangesOverlap_iff_rangeCompatible]
  constructor
  · simp [reverseRule, reverseRestoreRule, threeRule, hsource]
  · intro index
    cases index <;>
      simp [reverseRule, reverseRestoreRule, threeRule, Action.RangeCompatible, hscan]

/-- The proof-facing result transports directly through any chosen finite
enumeration into the executable `QuadrupleMachine` API. -/
theorem machineWithEnumeration_syntacticallyReversible
    [DecidableEq SourceControl] [DecidableEq Symbol] [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol))) :
    (machineWithEnumeration normal enumerate).SyntacticallyReversible := by
  have hfinish := noFinishBlankRule_of_normal normal
  constructor
  · intro first second hne
    change ¬(tableRuleAt source normal.finish normal.exitId (enumerate.symm first)).DomainsOverlap
      (tableRuleAt source normal.finish normal.exitId (enumerate.symm second))
    apply rules_domains_disjoint normal.syntacticDeterminism hfinish
    intro htags
    apply hne
    exact Equiv.injective enumerate.symm htags
  · intro first second hne
    change ¬(tableRuleAt source normal.finish normal.exitId (enumerate.symm first)).RangesOverlap
      (tableRuleAt source normal.finish normal.exitId (enumerate.symm second))
    apply rules_ranges_disjoint normal.syntacticDeterminism hfinish
    intro htags
    apply hne
    exact Equiv.injective enumerate.symm htags

end Simulator
end Bennett.Turing
