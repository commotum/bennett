import Bennett.Turing.Simulator.Compute
import Bennett.Turing.Quadruple.Inverse

/-!
# Exact reverse simulation and history cleanup

The two reverse rules mirror the lower and upper forward rules in reverse
order, with disjoint `C`-phase controls.  A copied output tape is retained
unchanged.  Its head must scan blank because the second Table 1 rule checks the
output delimiter rather than merely staying put.
-/

namespace Bennett.Turing
namespace Simulator

variable {SourceControl Symbol : Type}

/-- Erase the newest rule record while undoing the source head movement. -/
def reverseEraseRule (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId) : Rule source :=
  let sourceRule := source.rule ruleId
  threeRule (.reverse sourceRule.target) (.reverseConnector ruleId)
    (.move sourceRule.move.inverse)
    (.rewrite (.mark ruleId) .blank)
    (.move .stay)

/-- Restore the overwritten source symbol and move the history head left. -/
def reverseRestoreRule (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId) : Rule source :=
  let sourceRule := source.rule ruleId
  threeRule (.reverseConnector ruleId) (.reverse sourceRule.source)
    (.rewrite sourceRule.written sourceRule.scanned)
    (.move .left)
    (.rewrite .blank .blank)

/-- Proof-facing dispatch for the complete retrace rule family. -/
def reverseRule (source : Machine SourceControl Symbol) :
    ReverseRuleId source.RuleId → Rule source
  | .eraseRecordMove ruleId => reverseEraseRule source ruleId
  | .restoreSymbol ruleId => reverseRestoreRule source ruleId

/-- Exact configuration between the two reverse simulator rules. -/
def reverseMiddle (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId)
    (before : Bennett.Turing.Configuration SourceControl Symbol)
    (history : List source.RuleId) (copiedOutput : Tape Symbol) :
    Configuration source where
  control := .reverseConnector ruleId
  tape
    | .work => before.tape.write (source.rule ruleId).written
    | .history => (HistoryTape.encode history).move .right
    | .output => copiedOutput

theorem reverseEraseRule_matches (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId)
    (before : Bennett.Turing.Configuration SourceControl Symbol)
    (history : List source.RuleId) (copiedOutput : Tape Symbol) :
    (reverseEraseRule source ruleId).Matches
      (reverseConfiguration source
        { current := (source.rule ruleId).execute before
          history := ruleId :: history }
        copiedOutput) := by
  constructor
  · rfl
  · intro index
    cases index with
    | work => trivial
    | history => exact HistoryTape.read_encode_cons ruleId history
    | output => trivial

theorem reverseEraseRule_execute (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId)
    (before : Bennett.Turing.Configuration SourceControl Symbol)
    (history : List source.RuleId) (copiedOutput : Tape Symbol) :
    (reverseEraseRule source ruleId).execute
        (reverseConfiguration source
          { current := (source.rule ruleId).execute before
            history := ruleId :: history }
          copiedOutput) =
      reverseMiddle source ruleId before history copiedOutput := by
  apply MultiConfiguration.ext
  · rfl
  · intro index
    cases index with
    | work =>
        exact Tape.move_inverse
          (before.tape.write (source.rule ruleId).written)
          (source.rule ruleId).move
    | history => exact HistoryTape.erase_encode_cons ruleId history
    | output => exact Tape.move_stay copiedOutput

theorem reverseRestoreRule_matches (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId)
    (before : Bennett.Turing.Configuration SourceControl Symbol)
    (history : List source.RuleId) (copiedOutput : Tape Symbol)
    (houtput : copiedOutput.read = .blank) :
    (reverseRestoreRule source ruleId).Matches
      (reverseMiddle source ruleId before history copiedOutput) := by
  constructor
  · rfl
  · intro index
    cases index with
    | work => exact Tape.read_write _ _
    | history => trivial
    | output => exact houtput

theorem reverseRestoreRule_execute (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId)
    (before : Bennett.Turing.Configuration SourceControl Symbol)
    (history : List source.RuleId) (copiedOutput : Tape Symbol)
    (hmatches : (source.rule ruleId).Matches before)
    (houtput : copiedOutput.read = .blank) :
    (reverseRestoreRule source ruleId).execute
        (reverseMiddle source ruleId before history copiedOutput) =
      reverseConfiguration source
        { current := before, history := history } copiedOutput := by
  apply MultiConfiguration.ext
  · exact congrArg Control.reverse hmatches.1
  · intro index
    cases index with
    | work =>
        change
          (before.tape.write (source.rule ruleId).written).write
              (source.rule ruleId).scanned = before.tape
        rw [Tape.write_write, hmatches.2]
        exact Tape.write_read before.tape
    | history =>
        exact Tape.move_inverse (HistoryTape.encode history) .right
    | output =>
        change copiedOutput.write .blank = copiedOutput
        rw [← houtput, Tape.write_read]

/-- A recorded source step is undone by exactly two reverse target steps. -/
theorem reverse_two_steps
    [DecidableEq SourceControl] [DecidableEq Symbol]
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId)
    (before : Bennett.Turing.Configuration SourceControl Symbol)
    (history : List source.RuleId) (copiedOutput : Tape Symbol)
    (hmatches : (source.rule ruleId).Matches before)
    (houtput : copiedOutput.read = .blank) :
    (reverseEraseRule source ruleId).step
        (reverseConfiguration source
          { current := (source.rule ruleId).execute before
            history := ruleId :: history }
          copiedOutput) =
      some (reverseMiddle source ruleId before history copiedOutput) ∧
    (reverseRestoreRule source ruleId).step
        (reverseMiddle source ruleId before history copiedOutput) =
      some (reverseConfiguration source
        { current := before, history := history } copiedOutput) := by
  constructor
  · exact (Quadruple.step_eq_some_iff _ _ _).mpr
      ⟨reverseEraseRule_matches source ruleId before history copiedOutput,
        reverseEraseRule_execute source ruleId before history copiedOutput⟩
  · exact (Quadruple.step_eq_some_iff _ _ _).mpr
      ⟨reverseRestoreRule_matches source ruleId before history copiedOutput
          houtput,
        reverseRestoreRule_execute source ruleId before history copiedOutput
          hmatches houtput⟩

/-- The displayed two-rule cleanup schedule for one recorded source step. -/
def reversePairRules (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId) : List (Rule source) :=
  [reverseEraseRule source ruleId, reverseRestoreRule source ruleId]

theorem reversePair_scheduled (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId)
    (before : Bennett.Turing.Configuration SourceControl Symbol)
    (history : List source.RuleId) (copiedOutput : Tape Symbol)
    (hmatches : (source.rule ruleId).Matches before)
    (houtput : copiedOutput.read = .blank) :
    Quadruple.Scheduled (reversePairRules source ruleId)
      (reverseConfiguration source
        { current := (source.rule ruleId).execute before
          history := ruleId :: history }
        copiedOutput)
      (reverseConfiguration source
        { current := before, history := history } copiedOutput) := by
  simp only [reversePairRules, Quadruple.Scheduled]
  refine ⟨reverseEraseRule_matches source ruleId before history copiedOutput, ?_⟩
  rw [reverseEraseRule_execute source ruleId before history copiedOutput]
  exact ⟨reverseRestoreRule_matches source ruleId before history copiedOutput
      houtput,
    reverseRestoreRule_execute source ruleId before history copiedOutput
      hmatches houtput⟩

/-- Every displayed rule belongs to the retrace family of `source`. -/
def OnlyReverseRules (source : Machine SourceControl Symbol)
    (rules : List (Rule source)) : Prop :=
  ∀ rule, rule ∈ rules →
    ∃ ruleId : ReverseRuleId source.RuleId, reverseRule source ruleId = rule

theorem onlyReverseRules_pair (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId) :
    OnlyReverseRules source (reversePairRules source ruleId) := by
  intro rule hmem
  simp only [reversePairRules, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with herase | hrestore
  · exact ⟨ReverseRuleId.eraseRecordMove ruleId, by
      simpa [reverseRule] using herase.symm⟩
  · exact ⟨ReverseRuleId.restoreSymbol ruleId, by
      simpa [reverseRule] using hrestore.symm⟩

theorem OnlyReverseRules.append (source : Machine SourceControl Symbol)
    {first second : List (Rule source)}
    (hfirst : OnlyReverseRules source first)
    (hsecond : OnlyReverseRules source second) :
    OnlyReverseRules source (first ++ second) := by
  intro rule hmem
  rw [List.mem_append] at hmem
  exact hmem.elim (hfirst rule) (hsecond rule)

/-!
## Run-level compute/retrace schedules
-/

/--
An exact `n`-step source run generates a `2n`-rule forward schedule and a
`2n`-rule reverse cleanup schedule.  Cleanup retains an arbitrary copied output
tape whose stationary head scans blank.
-/
theorem forward_reverse_scheduled_of_run
    [DecidableEq SourceControl] [DecidableEq Symbol]
    (source : Machine SourceControl Symbol)
    {n : Nat}
    {before after : Bennett.Turing.Configuration SourceControl Symbol}
    (history : List source.RuleId) (copiedOutput : Tape Symbol)
    (houtput : copiedOutput.read = .blank)
    (hrun : source.step.Runs n before after) :
    ∃ finalHistory forwardRules reverseRules,
      finalHistory.length = history.length + n ∧
      forwardRules.length = 2 * n ∧ reverseRules.length = 2 * n ∧
      Quadruple.Scheduled forwardRules
        (forwardConfiguration source
          { current := before, history := history })
        (forwardConfiguration source
          { current := after, history := finalHistory }) ∧
      Quadruple.Scheduled reverseRules
        (reverseConfiguration source
          { current := after, history := finalHistory } copiedOutput)
        (reverseConfiguration source
          { current := before, history := history } copiedOutput) ∧
      OnlyForwardRules source forwardRules ∧
      OnlyReverseRules source reverseRules := by
  induction n generalizing before history with
  | zero =>
      have hbefore : before = after :=
        (PartialStep.runs_zero_iff source.step before after).mp hrun
      subst before
      exact ⟨history, [], [], by simp, by simp, by simp, rfl, rfl,
        by simp [OnlyForwardRules], by simp [OnlyReverseRules]⟩
  | succ n ih =>
      obtain ⟨next, hstep, htail⟩ :=
        (PartialStep.runs_succ_iff source.step n before after).mp hrun
      unfold Machine.step at hstep
      obtain ⟨ruleId, hselect, hnext⟩ := Option.map_eq_some_iff.mp hstep
      have hmatches := source.select_matches before hselect
      have hnextEq : (source.rule ruleId).execute before = next := hnext
      subst next
      obtain ⟨finalHistory, forwardTail, reverseTail, hhistory,
          hforwardLength, hreverseLength, hforwardTail, hreverseTail,
          hforwardOnly, hreverseOnly⟩ :=
        ih (ruleId :: history) htail
      refine ⟨finalHistory,
        forwardPairRules source ruleId ++ forwardTail,
        reverseTail ++ reversePairRules source ruleId,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hhistory, Nat.add_comm, Nat.add_left_comm]
      · simp [forwardPairRules, hforwardLength]
        omega
      · simp [reversePairRules, hreverseLength]
        omega
      · exact Quadruple.Scheduled.append
          (forwardPair_scheduled source ruleId
            { current := before, history := history } hmatches)
          hforwardTail
      · exact Quadruple.Scheduled.append hreverseTail
          (reversePair_scheduled source ruleId before history copiedOutput
            hmatches houtput)
      · exact OnlyForwardRules.append source
          (onlyForwardRules_pair source ruleId) hforwardOnly
      · exact OnlyReverseRules.append source hreverseOnly
          (onlyReverseRules_pair source ruleId)

/--
For a nonempty normal-form run ending at the standard finish control, the
newest physical history record is exactly the distinguished exit rule.  This
is the checked junction precondition for the copy phase.
-/
theorem forward_reverse_scheduled_to_standard_finish
    [DecidableEq SourceControl] [DecidableEq Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    {n : Nat}
    {before : Bennett.Turing.Configuration SourceControl Symbol}
    (output : List Symbol)
    (hrun : source.step.Runs (n + 1) before
      (Standard.config normal.finish output)) :
    ∃ history forwardRules reverseRules,
      history.length = n ∧
      forwardRules.length = 2 * (n + 1) ∧
      reverseRules.length = 2 * (n + 1) ∧
      Quadruple.Scheduled forwardRules
        (forwardConfiguration source { current := before, history := [] })
        (forwardConfiguration source
          { current := Standard.config normal.finish output
            history := normal.exitId :: history }) ∧
      Quadruple.Scheduled reverseRules
        (reverseConfiguration source
          { current := Standard.config normal.finish output
            history := normal.exitId :: history }
          (Tape.ofWord output))
        (reverseConfiguration source
          { current := before, history := [] } (Tape.ofWord output)) ∧
      OnlyForwardRules source forwardRules ∧
      OnlyReverseRules source reverseRules := by
  obtain ⟨middle, hprefix, hlast⟩ :=
    (PartialStep.runs_add_iff source.step n 1 before
      (Standard.config normal.finish output)).mp (by simpa using hrun)
  have hstep : source.step middle =
      some (Standard.config normal.finish output) := by
    simpa [PartialStep.Runs, PartialStep.iterate] using hlast
  unfold Machine.step at hstep
  obtain ⟨ruleId, hselect, hfinal⟩ := Option.map_eq_some_iff.mp hstep
  have hmatches := source.select_matches middle hselect
  have htarget : (source.rule ruleId).target = normal.finish := by
    have hcontrol := congrArg Bennett.Turing.Configuration.control hfinal
    simpa using hcontrol
  have hid : ruleId = normal.exitId :=
    normal.exit_only_rule_to_finish ruleId htarget
  subst ruleId
  obtain ⟨history, forwardPrefix, reversePrefix, hhistory,
      hforwardLength, hreverseLength, hforwardPrefix, hreversePrefix,
      hforwardOnly, hreverseOnly⟩ :=
    forward_reverse_scheduled_of_run source ([] : List source.RuleId)
      (Tape.ofWord output) (Tape.read_ofWord output) hprefix
  have hforwardLast := forwardPair_scheduled source normal.exitId
    { current := middle, history := history } hmatches
  have hreverseLast := reversePair_scheduled source normal.exitId middle history
    (Tape.ofWord output) hmatches (Tape.read_ofWord output)
  rw [hfinal] at hforwardLast hreverseLast
  refine ⟨history,
    forwardPrefix ++ forwardPairRules source normal.exitId,
    reversePairRules source normal.exitId ++ reversePrefix,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hhistory
  · simp [hforwardLength, forwardPairRules]
    omega
  · simp [hreverseLength, reversePairRules]
    omega
  · exact Quadruple.Scheduled.append hforwardPrefix hforwardLast
  · exact Quadruple.Scheduled.append hreverseLast hreversePrefix
  · exact OnlyForwardRules.append source hforwardOnly
      (onlyForwardRules_pair source normal.exitId)
  · exact OnlyReverseRules.append source
      (onlyReverseRules_pair source normal.exitId) hreverseOnly

/-- Reverse erasure uses exactly the inverse tape actions of forward recording. -/
theorem reverseEraseRule_action (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId) (index : TapeId) :
    (reverseEraseRule source ruleId).action index =
      ((forwardRecordRule source ruleId).action index).inverse := by
  cases index <;> rfl

/-- Reverse restoration uses exactly the inverse tape actions of forward rewrite. -/
theorem reverseRestoreRule_action (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId) (index : TapeId) :
    (reverseRestoreRule source ruleId).action index =
      ((forwardRewriteRule source ruleId).action index).inverse := by
  cases index <;> rfl

end Simulator
end Bennett.Turing
