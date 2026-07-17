import Bennett.Turing.Quadruple.Schedule
import Bennett.Turing.Simulator.Syntax

/-!
# Exact forward simulation rules

Each selected source quintuple is split into two typed three-tape rules.  The
first rule rewrites the work cell and advances the history head onto a known
blank.  The second moves the work head and writes the intrinsic source-rule ID
as the history record.  The output tape remains exactly blank throughout this
phase.
-/

namespace Bennett.Turing
namespace Simulator

variable {SourceControl Symbol : Type}

/-- First half of the forward simulation of a named source quintuple. -/
def forwardRewriteRule (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId) : Rule source :=
  let sourceRule := source.rule ruleId
  threeRule (.forward sourceRule.source) (.forwardConnector ruleId)
    (.rewrite sourceRule.scanned sourceRule.written)
    (.move .right)
    (.rewrite .blank .blank)

/-- Second half: move the work head and commit the rule ID to history. -/
def forwardRecordRule (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId) : Rule source :=
  let sourceRule := source.rule ruleId
  threeRule (.forwardConnector ruleId) (.forward sourceRule.target)
    (.move sourceRule.move)
    (.rewrite .blank (.mark ruleId))
    (.move .stay)

/-- Proof-facing dispatch for the complete forward rule family. -/
def forwardRule (source : Machine SourceControl Symbol) :
    ForwardRuleId source.RuleId → Rule source
  | .rewrite ruleId => forwardRewriteRule source ruleId
  | .moveRecord ruleId => forwardRecordRule source ruleId

/-- Exact configuration between the two forward simulator rules. -/
def forwardMiddle (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId)
    (state : HistoryState (Bennett.Turing.Configuration SourceControl Symbol)
      source.RuleId) : Configuration source where
  control := .forwardConnector ruleId
  tape
    | .work => state.current.tape.write (source.rule ruleId).written
    | .history => (HistoryTape.encode state.history).move .right
    | .output => Tape.blankAt (-1)

theorem forwardRewriteRule_matches (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId)
    (state : HistoryState (Bennett.Turing.Configuration SourceControl Symbol)
      source.RuleId)
    (hmatches : (source.rule ruleId).Matches state.current) :
    (forwardRewriteRule source ruleId).Matches
      (forwardConfiguration source state) := by
  constructor
  · exact congrArg Control.forward hmatches.1
  · intro index
    cases index with
    | work =>
        exact hmatches.2.symm
    | history =>
        trivial
    | output =>
        rfl

theorem forwardRewriteRule_execute (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId)
    (state : HistoryState (Bennett.Turing.Configuration SourceControl Symbol)
      source.RuleId) :
    (forwardRewriteRule source ruleId).execute
        (forwardConfiguration source state) =
      forwardMiddle source ruleId state := by
  apply MultiConfiguration.ext
  · rfl
  · intro index
    cases index with
    | work => rfl
    | history => rfl
    | output =>
        change (Tape.blankAt (-1) : Tape Symbol).write .blank =
          Tape.blankAt (-1)
        simpa using Tape.write_read (Tape.blankAt (-1) : Tape Symbol)

theorem forwardRecordRule_matches (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId)
    (state : HistoryState (Bennett.Turing.Configuration SourceControl Symbol)
      source.RuleId) :
    (forwardRecordRule source ruleId).Matches
      (forwardMiddle source ruleId state) := by
  constructor
  · rfl
  · intro index
    cases index with
    | work =>
        trivial
    | history =>
        exact HistoryTape.read_move_right_encode state.history
    | output =>
        trivial

theorem forwardRecordRule_execute (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId)
    (state : HistoryState (Bennett.Turing.Configuration SourceControl Symbol)
      source.RuleId) :
    (forwardRecordRule source ruleId).execute
        (forwardMiddle source ruleId state) =
      forwardConfiguration source
        { current := (source.rule ruleId).execute state.current
          history := ruleId :: state.history } := by
  apply MultiConfiguration.ext
  · rfl
  · intro index
    cases index with
    | work => rfl
    | history => rfl
    | output =>
        exact Tape.move_stay (Tape.blankAt (-1) : Tape Symbol)

/-- A matching source quintuple is simulated by exactly two target steps. -/
theorem forward_two_steps_of_matches
    [DecidableEq SourceControl] [DecidableEq Symbol]
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId)
    (state : HistoryState (Bennett.Turing.Configuration SourceControl Symbol)
      source.RuleId)
    (hmatches : (source.rule ruleId).Matches state.current) :
    (forwardRewriteRule source ruleId).step
        (forwardConfiguration source state) =
      some (forwardMiddle source ruleId state) ∧
    (forwardRecordRule source ruleId).step
        (forwardMiddle source ruleId state) =
      some (forwardConfiguration source
        { current := (source.rule ruleId).execute state.current
          history := ruleId :: state.history }) := by
  constructor
  · exact (Quadruple.step_eq_some_iff _ _ _).mpr
      ⟨forwardRewriteRule_matches source ruleId state hmatches,
        forwardRewriteRule_execute source ruleId state⟩
  · exact (Quadruple.step_eq_some_iff _ _ _).mpr
      ⟨forwardRecordRule_matches source ruleId state,
        forwardRecordRule_execute source ruleId state⟩

/--
Executable source selection and physical forward simulation agree exactly.
No global determinism hypothesis is needed here: the premise already names the
rule selected by the source machine's executable priority semantics.
-/
theorem forward_two_steps_of_stepWithRuleId
    [DecidableEq SourceControl] [DecidableEq Symbol]
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId)
    (state : HistoryState (Bennett.Turing.Configuration SourceControl Symbol)
      source.RuleId)
    (after : Bennett.Turing.Configuration SourceControl Symbol)
    (hstep : source.stepWithRuleId state.current = some (after, ruleId)) :
    (forwardRewriteRule source ruleId).step
        (forwardConfiguration source state) =
      some (forwardMiddle source ruleId state) ∧
    (forwardRecordRule source ruleId).step
        (forwardMiddle source ruleId state) =
      some (forwardConfiguration source
        { current := after, history := ruleId :: state.history }) := by
  obtain ⟨hselect, hafter⟩ :=
    (source.stepWithRuleId_eq_some_iff state.current after ruleId).mp hstep
  have hmatches := source.select_matches state.current hselect
  subst after
  exact forward_two_steps_of_matches source ruleId state hmatches

/-- The displayed two-rule schedule for one named source transition. -/
def forwardPairRules (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId) : List (Rule source) :=
  [forwardRewriteRule source ruleId, forwardRecordRule source ruleId]

theorem forwardPair_scheduled (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId)
    (state : HistoryState (Bennett.Turing.Configuration SourceControl Symbol)
      source.RuleId)
    (hmatches : (source.rule ruleId).Matches state.current) :
    Quadruple.Scheduled (forwardPairRules source ruleId)
      (forwardConfiguration source state)
      (forwardConfiguration source
        { current := (source.rule ruleId).execute state.current
          history := ruleId :: state.history }) := by
  simp only [forwardPairRules, Quadruple.Scheduled]
  refine ⟨forwardRewriteRule_matches source ruleId state hmatches, ?_⟩
  rw [forwardRewriteRule_execute source ruleId state]
  exact ⟨forwardRecordRule_matches source ruleId state,
    forwardRecordRule_execute source ruleId state⟩

/-- Every displayed rule belongs to the forward family of `source`. -/
def OnlyForwardRules (source : Machine SourceControl Symbol)
    (rules : List (Rule source)) : Prop :=
  ∀ rule, rule ∈ rules →
    ∃ ruleId : ForwardRuleId source.RuleId, forwardRule source ruleId = rule

theorem onlyForwardRules_pair (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId) :
    OnlyForwardRules source (forwardPairRules source ruleId) := by
  intro rule hmem
  simp only [forwardPairRules, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hrewrite | hrecord
  · exact ⟨ForwardRuleId.rewrite ruleId, by
      simpa [forwardRule] using hrewrite.symm⟩
  · exact ⟨ForwardRuleId.moveRecord ruleId, by
      simpa [forwardRule] using hrecord.symm⟩

theorem OnlyForwardRules.append (source : Machine SourceControl Symbol)
    {first second : List (Rule source)}
    (hfirst : OnlyForwardRules source first)
    (hsecond : OnlyForwardRules source second) :
    OnlyForwardRules source (first ++ second) := by
  intro rule hmem
  rw [List.mem_append] at hmem
  exact hmem.elim (hfirst rule) (hsecond rule)

/--
Lift any exact source run to an explicit `2n`-rule physical schedule.  The
theorem returns the actual newest-first rule-ID history and works from an
arbitrary pre-existing history suffix.
-/
theorem forward_scheduled_of_run
    [DecidableEq SourceControl] [DecidableEq Symbol]
    (source : Machine SourceControl Symbol)
    {n : Nat}
    {before after : Bennett.Turing.Configuration SourceControl Symbol}
    (history : List source.RuleId)
    (hrun : source.step.Runs n before after) :
    ∃ finalHistory rules,
      finalHistory.length = history.length + n ∧
      rules.length = 2 * n ∧
      Quadruple.Scheduled rules
        (forwardConfiguration source
          { current := before, history := history })
        (forwardConfiguration source
          { current := after, history := finalHistory }) ∧
      OnlyForwardRules source rules := by
  induction n generalizing before history with
  | zero =>
      have hbefore : before = after :=
        (PartialStep.runs_zero_iff source.step before after).mp hrun
      subst before
      exact ⟨history, [], by simp, by simp, rfl, by simp [OnlyForwardRules]⟩
  | succ n ih =>
      obtain ⟨next, hstep, htail⟩ :=
        (PartialStep.runs_succ_iff source.step n before after).mp hrun
      unfold Machine.step at hstep
      obtain ⟨ruleId, hselect, hnext⟩ := Option.map_eq_some_iff.mp hstep
      have hmatches := source.select_matches before hselect
      have hnextEq : (source.rule ruleId).execute before = next := hnext
      subst next
      obtain ⟨finalHistory, tailRules, hhistory, htailLength,
          htailScheduled, htailOnly⟩ := ih (ruleId :: history) htail
      refine ⟨finalHistory, forwardPairRules source ruleId ++ tailRules,
        ?_, ?_, ?_, ?_⟩
      · simp [hhistory, Nat.add_comm, Nat.add_left_comm]
      · simp [htailLength, forwardPairRules]
        omega
      · exact Quadruple.Scheduled.append
          (forwardPair_scheduled source ruleId
            { current := before, history := history } hmatches)
          htailScheduled
      · exact OnlyForwardRules.append source
          (onlyForwardRules_pair source ruleId) htailOnly

theorem forward_scheduled_of_run_empty
    [DecidableEq SourceControl] [DecidableEq Symbol]
    (source : Machine SourceControl Symbol)
    {n : Nat}
    {before after : Bennett.Turing.Configuration SourceControl Symbol}
    (hrun : source.step.Runs n before after) :
    ∃ history rules,
      history.length = n ∧ rules.length = 2 * n ∧
      Quadruple.Scheduled rules
        (forwardConfiguration source { current := before, history := [] })
        (forwardConfiguration source
          { current := after, history := history }) ∧
      OnlyForwardRules source rules := by
  simpa using forward_scheduled_of_run source ([] : List source.RuleId) hrun

end Simulator
end Bennett.Turing
