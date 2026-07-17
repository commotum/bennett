import Bennett.Turing.Simulator.Core

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

end Simulator
end Bennett.Turing
