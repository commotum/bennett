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
