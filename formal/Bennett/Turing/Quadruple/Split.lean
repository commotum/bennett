import Bennett.Turing.Quadruple.Machine
import Bennett.Turing.Source.Determinism
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Fresh-state splitting of source quintuples

A source read/write/move step becomes a rewrite quadruple followed by a move
quadruple through a connector indexed by the source rule.  Sum types make all
freshness obligations structural.  Pure splitting guarantees deterministic
domains under source key uniqueness, but it does **not** generally make an
irreversible source table reversible; the exact range obstruction is proved
below.
-/

namespace Bennett.Turing

/-- Original controls plus one definitionally fresh connector per source rule. -/
abbrev SplitState (Control RuleId : Type*) := Control ⊕ RuleId

namespace SourceSplit

variable {Control TapeIndex RuleId : Type*} {Symbol : TapeIndex → Type*}
  [DecidableEq TapeIndex]

/-- Put a one-tape source configuration on a selected heterogeneous work tape. -/
def liftConfiguration (work : TapeIndex)
    (auxiliary : (index : TapeIndex) → Tape (Symbol index))
    (config : Configuration Control (Symbol work)) :
    MultiConfiguration (SplitState Control RuleId) TapeIndex Symbol where
  control := .inl config.control
  tape index := if h : index = work then by
      subst index
      exact config.tape
    else auxiliary index

/-- First half of a source rule: check/rewrite work and enter its connector. -/
def writeHalf (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work)) :
    Quadruple (SplitState Control RuleId) TapeIndex Symbol where
  source := .inl rule.source
  action index := if h : index = work then by
      subst index
      exact .rewrite rule.scanned rule.written
    else .move .stay
  target := .inr ruleId

/-- Second half of a source rule: move work and return to an original control. -/
def moveHalf (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work)) :
    Quadruple (SplitState Control RuleId) TapeIndex Symbol where
  source := .inr ruleId
  action index := if h : index = work then by
      subst index
      exact .move rule.move
    else .move .stay
  target := .inl rule.target

@[simp] theorem writeHalf_source (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work)) :
    (writeHalf work ruleId rule).source = .inl rule.source :=
  rfl

@[simp] theorem writeHalf_target (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work)) :
    (writeHalf work ruleId rule).target = .inr ruleId :=
  rfl

@[simp] theorem moveHalf_source (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work)) :
    (moveHalf work ruleId rule).source = .inr ruleId :=
  rfl

@[simp] theorem moveHalf_target (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work)) :
    (moveHalf work ruleId rule).target = .inl rule.target :=
  rfl

@[simp] theorem writeHalf_action_work (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work)) :
    (writeHalf work ruleId rule).action work =
      .rewrite rule.scanned rule.written := by
  simp [writeHalf]

@[simp] theorem moveHalf_action_work (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work)) :
    (moveHalf work ruleId rule).action work = .move rule.move := by
  simp [moveHalf]

theorem writeHalf_matches
    (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work))
    (config : MultiConfiguration (SplitState Control RuleId) TapeIndex Symbol)
    (hcontrol : config.control = .inl rule.source)
    (hread : rule.scanned = (config.tape work).read) :
    (writeHalf work ruleId rule).Matches config := by
  constructor
  · exact hcontrol.symm
  · intro index
    by_cases hindex : index = work
    · subst index
      simpa [writeHalf, Action.Matches] using hread.symm
    · simp [writeHalf, hindex, Action.Matches]

theorem moveHalf_matches_after_write
    (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work))
    (config : MultiConfiguration (SplitState Control RuleId) TapeIndex Symbol) :
    (moveHalf work ruleId rule).Matches
      ((writeHalf work ruleId rule).execute config) := by
  constructor
  · rfl
  · intro index
    by_cases hindex : index = work
    · subst index
      simp [moveHalf, Action.Matches]
    · simp [moveHalf, Action.Matches, hindex]

/-- Exact endpoint after both halves, preserving every auxiliary tape. -/
def liftedExecute
    (work : TapeIndex) (rule : Quintuple Control (Symbol work))
    (config : MultiConfiguration (SplitState Control RuleId) TapeIndex Symbol) :
    MultiConfiguration (SplitState Control RuleId) TapeIndex Symbol where
  control := .inl rule.target
  tape index := if h : index = work then by
      subst index
      exact (config.tape work).writeMove rule.written rule.move
    else config.tape index

theorem execute_two
    (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work))
    (config : MultiConfiguration (SplitState Control RuleId) TapeIndex Symbol) :
    (moveHalf work ruleId rule).execute
        ((writeHalf work ruleId rule).execute config) =
      liftedExecute work rule config := by
  apply MultiConfiguration.ext
  · rfl
  · intro index
    by_cases hindex : index = work
    · subst index
      simp [Quadruple.execute, writeHalf, moveHalf, liftedExecute,
        Action.execute, Tape.writeMove]
    · simp [Quadruple.execute, writeHalf, moveHalf, liftedExecute,
        Action.execute, hindex]

/-- Applicability and exact endpoint for one split source step. -/
theorem two_step_of_source_match
    (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work))
    (config : MultiConfiguration (SplitState Control RuleId) TapeIndex Symbol)
    (hcontrol : config.control = .inl rule.source)
    (hread : rule.scanned = (config.tape work).read) :
    (writeHalf work ruleId rule).Matches config ∧
      (moveHalf work ruleId rule).Matches
        ((writeHalf work ruleId rule).execute config) ∧
      (moveHalf work ruleId rule).execute
          ((writeHalf work ruleId rule).execute config) =
        liftedExecute work rule config :=
  ⟨writeHalf_matches work ruleId rule config hcontrol hread,
    moveHalf_matches_after_write work ruleId rule config,
    execute_two work ruleId rule config⟩

/-- Direct endpoint bridge to Stage 4 source-rule execution. -/
theorem execute_two_liftConfiguration
    (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work))
    (auxiliary : (index : TapeIndex) → Tape (Symbol index))
    (config : Configuration Control (Symbol work)) :
    (moveHalf work ruleId rule).execute
        ((writeHalf work ruleId rule).execute
          (liftConfiguration (RuleId := RuleId) work auxiliary config)) =
      liftConfiguration (RuleId := RuleId) work auxiliary
        (rule.execute config) := by
  rw [execute_two]
  apply MultiConfiguration.ext
  · rfl
  · intro index
    by_cases hindex : index = work
    · subst index
      simp [liftedExecute, liftConfiguration, Quintuple.execute]
    · simp [liftedExecute, liftConfiguration, hindex]

/-- A matching source rule becomes an exact successful two-quadruple execution. -/
theorem lift_two_step_of_matches
    (work : TapeIndex) (ruleId : RuleId)
    (rule : Quintuple Control (Symbol work))
    (auxiliary : (index : TapeIndex) → Tape (Symbol index))
    (config : Configuration Control (Symbol work))
    (hmatches : rule.Matches config) :
    (writeHalf work ruleId rule).Matches
        (liftConfiguration (RuleId := RuleId) work auxiliary config) ∧
      (moveHalf work ruleId rule).Matches
        ((writeHalf work ruleId rule).execute
          (liftConfiguration (RuleId := RuleId) work auxiliary config)) ∧
      (moveHalf work ruleId rule).execute
          ((writeHalf work ruleId rule).execute
            (liftConfiguration (RuleId := RuleId) work auxiliary config)) =
        liftConfiguration (RuleId := RuleId) work auxiliary
          (rule.execute config) := by
  refine ⟨writeHalf_matches work ruleId rule _ ?_ ?_,
    moveHalf_matches_after_write work ruleId rule _,
    execute_two_liftConfiguration work ruleId rule auxiliary config⟩
  · simp [liftConfiguration, hmatches.1]
  · rw [show
        (liftConfiguration (RuleId := RuleId) work auxiliary config).tape work =
          config.tape by simp [liftConfiguration]]
    simpa [Configuration.read] using hmatches.2

section Overlap

variable {RuleId : Type*}

theorem writeHalf_domainsOverlap_keys
    {work : TapeIndex} {firstId secondId : RuleId}
    {first second : Quintuple Control (Symbol work)}
    (hoverlap : (writeHalf work firstId first).DomainsOverlap
      (writeHalf work secondId second)) :
    first.key = second.key := by
  have hcompatible := Quadruple.domainCompatible_of_domainsOverlap hoverlap
  apply Prod.ext
  · exact Sum.inl_injective hcompatible.1
  · have hwork := hcompatible.2 work
    change first.scanned = second.scanned
    simpa [writeHalf, Action.DomainCompatible] using hwork

theorem moveHalf_domainsOverlap_ids
    {work : TapeIndex} {firstId secondId : RuleId}
    {first second : Quintuple Control (Symbol work)}
    (hoverlap : (moveHalf work firstId first).DomainsOverlap
      (moveHalf work secondId second)) :
    firstId = secondId := by
  exact Sum.inr_injective
    (Quadruple.domainCompatible_of_domainsOverlap hoverlap).1

theorem write_move_domains_disjoint
    (work : TapeIndex) (firstId secondId : RuleId)
    (first second : Quintuple Control (Symbol work)) :
    ¬(writeHalf work firstId first).DomainsOverlap
      (moveHalf work secondId second) := by
  intro hoverlap
  have hcontrol := (Quadruple.domainCompatible_of_domainsOverlap hoverlap).1
  simp [writeHalf, moveHalf] at hcontrol

theorem writeHalf_rangesOverlap_ids
    {work : TapeIndex} {firstId secondId : RuleId}
    {first second : Quintuple Control (Symbol work)}
    (hoverlap : (writeHalf work firstId first).RangesOverlap
      (writeHalf work secondId second)) :
    firstId = secondId := by
  exact Sum.inr_injective
    ((Quadruple.rangesOverlap_iff_rangeCompatible _ _).mp hoverlap).1

theorem write_move_ranges_disjoint
    (work : TapeIndex) (firstId secondId : RuleId)
    (first second : Quintuple Control (Symbol work)) :
    ¬(writeHalf work firstId first).RangesOverlap
      (moveHalf work secondId second) := by
  intro hoverlap
  have hcontrol :=
    ((Quadruple.rangesOverlap_iff_rangeCompatible _ _).mp hoverlap).1
  simp [writeHalf, moveHalf] at hcontrol

/-- Exact obstruction: move-half ranges overlap iff source targets agree. -/
theorem moveHalf_rangesOverlap_iff_target_eq
    (work : TapeIndex) (firstId secondId : RuleId)
    (first second : Quintuple Control (Symbol work)) :
    (moveHalf work firstId first).RangesOverlap
        (moveHalf work secondId second) ↔
      first.target = second.target := by
  rw [Quadruple.rangesOverlap_iff_rangeCompatible]
  constructor
  · intro hcompatible
    exact Sum.inl_injective hcompatible.1
  · intro htarget
    refine ⟨congrArg Sum.inl htarget, ?_⟩
    intro index
    by_cases hindex : index = work
    · subst index
      simp [moveHalf, Action.RangeCompatible]
    · simp [moveHalf, Action.RangeCompatible, hindex]

end Overlap

end SourceSplit

namespace Machine

variable {Control Symbol TapeIndex : Type*}
  {TargetSymbol : TapeIndex → Type*} {work : TapeIndex}
  [DecidableEq TapeIndex]

/-- Natural proof-facing identifiers for the two halves of every source rule. -/
abbrev SplitRuleId (source : Machine Control Symbol) :=
  source.RuleId ⊕ source.RuleId

/-- Interpret a tagged source rule as its write or move half. -/
def splitRule (work : TapeIndex) (source : Machine Control (TargetSymbol work)) :
    SplitRuleId source →
      Quadruple (SplitState Control source.RuleId) TapeIndex TargetSymbol
  | .inl ruleId =>
      SourceSplit.writeHalf work ruleId (source.rule ruleId)
  | .inr ruleId =>
      SourceSplit.moveHalf work ruleId (source.rule ruleId)

omit [DecidableEq TapeIndex] in
@[simp] theorem splitRuleId_card
    (source : Machine Control (TargetSymbol work)) :
    Fintype.card (SplitRuleId source) = 2 * source.ruleCount := by
  simp [SplitRuleId, Nat.two_mul]

omit [DecidableEq TapeIndex] in
@[simp] theorem splitState_card [Fintype Control]
    (source : Machine Control (TargetSymbol work)) :
    Fintype.card (SplitState Control source.RuleId) =
      Fintype.card Control + source.ruleCount := by
  simp [SplitState]

theorem splitRule_domains_disjoint
    {source : Machine Control (TargetSymbol work)}
    (hdet : source.SyntacticallyDeterministic)
    {first second : SplitRuleId source} (hne : first ≠ second) :
    ¬(splitRule work source first).DomainsOverlap
      (splitRule work source second) := by
  cases first with
  | inl firstId =>
      cases second with
      | inl secondId =>
          intro hoverlap
          have hid := hdet (SourceSplit.writeHalf_domainsOverlap_keys hoverlap)
          exact hne (congrArg Sum.inl hid)
      | inr secondId =>
          exact SourceSplit.write_move_domains_disjoint work firstId secondId
            (source.rule firstId) (source.rule secondId)
  | inr firstId =>
      cases second with
      | inl secondId =>
          intro hoverlap
          obtain ⟨config, hfirst, hsecond⟩ := hoverlap
          exact SourceSplit.write_move_domains_disjoint work secondId firstId
            (source.rule secondId) (source.rule firstId)
            ⟨config, hsecond, hfirst⟩
      | inr secondId =>
          intro hoverlap
          have hid := SourceSplit.moveHalf_domainsOverlap_ids hoverlap
          exact hne (congrArg Sum.inr hid)

theorem splitRule_ranges_disjoint_of_target_injective
    (source : Machine Control (TargetSymbol work))
    (htarget : Function.Injective fun ruleId : source.RuleId =>
      (source.rule ruleId).target)
    {first second : SplitRuleId source} (hne : first ≠ second) :
    ¬(splitRule work source first).RangesOverlap
      (splitRule work source second) := by
  cases first with
  | inl firstId =>
      cases second with
      | inl secondId =>
          intro hoverlap
          have hid := SourceSplit.writeHalf_rangesOverlap_ids hoverlap
          exact hne (congrArg Sum.inl hid)
      | inr secondId =>
          exact SourceSplit.write_move_ranges_disjoint work firstId secondId
            (source.rule firstId) (source.rule secondId)
  | inr firstId =>
      cases second with
      | inl secondId =>
          intro hoverlap
          obtain ⟨config, hfirst, hsecond⟩ := hoverlap
          exact SourceSplit.write_move_ranges_disjoint work secondId firstId
            (source.rule secondId) (source.rule firstId)
            ⟨config, hsecond, hfirst⟩
      | inr secondId =>
          intro hoverlap
          have htargetEq :=
            (SourceSplit.moveHalf_rangesOverlap_iff_target_eq
              work firstId secondId (source.rule firstId)
                (source.rule secondId)).mp hoverlap
          have hid := htarget htargetEq
          exact hne (congrArg Sum.inr hid)

/-- Conversely, range-disjoint pure splitting forces source targets to identify rules. -/
theorem target_injective_of_splitRule_ranges_disjoint
    (source : Machine Control (TargetSymbol work))
    (hdisjoint : ∀ {first second : SplitRuleId source}, first ≠ second →
      ¬(splitRule work source first).RangesOverlap
        (splitRule work source second)) :
    Function.Injective fun ruleId : source.RuleId =>
      (source.rule ruleId).target := by
  intro first second htarget
  by_contra hne
  apply hdisjoint (first := Sum.inr first) (second := Sum.inr second)
  · intro heq
    exact hne (Sum.inr_injective heq)
  · exact (SourceSplit.moveHalf_rangesOverlap_iff_target_eq
      work first second (source.rule first) (source.rule second)).2 htarget

/-- Exact criterion: splitting alone is range-disjoint iff source targets are injective. -/
theorem splitRule_ranges_disjoint_iff_target_injective
    (source : Machine Control (TargetSymbol work)) :
    (∀ {first second : SplitRuleId source}, first ≠ second →
      ¬(splitRule work source first).RangesOverlap
        (splitRule work source second)) ↔
      Function.Injective fun ruleId : source.RuleId =>
        (source.rule ruleId).target :=
  ⟨target_injective_of_splitRule_ranges_disjoint source,
    splitRule_ranges_disjoint_of_target_injective source⟩

/-- Intrinsic `Fin (N+N)` table containing all write halves then all move halves. -/
def splitMachine (work : TapeIndex)
    (source : Machine Control (TargetSymbol work)) :
    QuadrupleMachine (SplitState Control source.RuleId) TapeIndex TargetSymbol where
  ruleCount := source.ruleCount + source.ruleCount
  rule index := splitRule work source (finSumFinEquiv.symm index)

@[simp] theorem splitMachine_ruleCount (work : TapeIndex)
    (source : Machine Control (TargetSymbol work)) :
    (splitMachine work source).ruleCount = 2 * source.ruleCount := by
  simp [splitMachine, Nat.two_mul]

/-- Source determinism makes the actual finite split table domain-disjoint. -/
theorem splitMachine_domainsDisjoint
    {source : Machine Control (TargetSymbol work)}
    (hdet : source.SyntacticallyDeterministic) :
    (splitMachine work source).DomainsDisjoint := by
  intro first second hne hoverlap
  apply splitRule_domains_disjoint hdet
    (first := finSumFinEquiv.symm first)
    (second := finSumFinEquiv.symm second)
  · intro heq
    exact hne (finSumFinEquiv.symm.injective heq)
  · exact hoverlap

/-- Pure splitting is range-disjoint under the extra injective-target premise. -/
theorem splitMachine_rangesDisjoint_of_target_injective
    (source : Machine Control (TargetSymbol work))
    (htarget : Function.Injective fun ruleId : source.RuleId =>
      (source.rule ruleId).target) :
    (splitMachine work source).RangesDisjoint := by
  intro first second hne hoverlap
  apply splitRule_ranges_disjoint_of_target_injective source htarget
    (first := finSumFinEquiv.symm first)
    (second := finSumFinEquiv.symm second)
  · intro heq
    exact hne (finSumFinEquiv.symm.injective heq)
  · exact hoverlap

theorem connector_ne_original (source : Machine Control Symbol)
    (ruleId : source.RuleId) (control : Control) :
    (Sum.inr ruleId : SplitState Control source.RuleId) ≠ .inl control := by
  simp

theorem connector_injective (source : Machine Control Symbol) :
    Function.Injective
      (Sum.inr : source.RuleId → SplitState Control source.RuleId) :=
  Sum.inr_injective

end Machine
end Bennett.Turing
