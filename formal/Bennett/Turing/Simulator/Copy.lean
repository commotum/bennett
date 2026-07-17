import Bennett.Turing.Quadruple.Schedule
import Bennett.Turing.Simulator.Syntax
import Lean.Elab.Tactic.Omega

/-!
# Exact three-tape copy sweep

This is Table 1's reversible copy loop on the concrete simulator carriers and
proof-facing `CopyRuleId` syntax.  The target tape starts blank, the work word
and history tape are retained exactly, and empty words are supported.
-/

namespace Bennett.Turing.Simulator.Copy

variable {SourceControl Symbol : Type}
  [DecidableEq SourceControl] [DecidableEq Symbol]

/-- Copy rules with their two genuine boundary parameters exposed. -/
def ruleAt (source : Machine SourceControl Symbol) (finish : SourceControl)
    (terminal : source.RuleId) :
    CopyRuleId Symbol → Simulator.Rule source
  | .enter =>
      threeRule (.forward finish) .copyRightMove
        (.rewrite .blank .blank)
        (.rewrite (.mark terminal) (.mark terminal))
        (.rewrite .blank .blank)
  | .moveRight =>
      threeRule .copyRightMove .copyRightRead
        (.move .right) (.move .stay) (.move .right)
  | .copySymbol symbol =>
      threeRule .copyRightRead .copyRightMove
        (.rewrite (.mark symbol) (.mark symbol))
        (.rewrite (.mark terminal) (.mark terminal))
        (.rewrite .blank (.mark symbol))
  | .turn =>
      threeRule .copyRightRead .copyLeftMove
        (.rewrite .blank .blank)
        (.rewrite (.mark terminal) (.mark terminal))
        (.rewrite .blank .blank)
  | .moveLeft =>
      threeRule .copyLeftMove .copyLeftRead
        (.move .left) (.move .stay) (.move .left)
  | .checkSymbol symbol =>
      threeRule .copyLeftRead .copyLeftMove
        (.rewrite (.mark symbol) (.mark symbol))
        (.rewrite (.mark terminal) (.mark terminal))
        (.rewrite (.mark symbol) (.mark symbol))
  | .exit =>
      threeRule .copyLeftRead (.reverse finish)
        (.rewrite .blank .blank)
        (.rewrite (.mark terminal) (.mark terminal))
        (.rewrite .blank .blank)

/-- Normal-form specialization used by the complete simulator. -/
def rule {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) :
    CopyRuleId Symbol → Simulator.Rule source :=
  ruleAt source normal.finish normal.exitId

def configuration (source : Machine SourceControl Symbol)
    (control : Control SourceControl source.RuleId)
    (work : Tape Symbol) (history : Tape source.RuleId) (output : Tape Symbol) :
    Simulator.Configuration source where
  control := control
  tape
    | .work => work
    | .history => history
    | .output => output

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem configuration_control (source : Machine SourceControl Symbol)
    (control : Control SourceControl source.RuleId)
    (work : Tape Symbol) (history : Tape source.RuleId) (output : Tape Symbol) :
    (configuration source control work history output).control = control := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem configuration_work (source : Machine SourceControl Symbol)
    (control : Control SourceControl source.RuleId)
    (work : Tape Symbol) (history : Tape source.RuleId) (output : Tape Symbol) :
    (configuration source control work history output).tape .work = work := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem configuration_history (source : Machine SourceControl Symbol)
    (control : Control SourceControl source.RuleId)
    (work : Tape Symbol) (history : Tape source.RuleId) (output : Tape Symbol) :
    (configuration source control work history output).tape .history = history := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem configuration_output (source : Machine SourceControl Symbol)
    (control : Control SourceControl source.RuleId)
    (work : Tape Symbol) (history : Tape source.RuleId) (output : Tape Symbol) :
    (configuration source control work history output).tape .output = output := rfl

namespace TapeInvariant

def withHead {α : Type*} (tape : Tape α) (head : Int) : Tape α :=
  { tape with head := head }

@[simp] theorem withHead_cells {α} (tape : Tape α) (head : Int) :
    (withHead tape head).cells = tape.cells := rfl

@[simp] theorem withHead_head {α} (tape : Tape α) (head : Int) :
    (withHead tape head).head = head := rfl

def workAt {α : Type*} (word : List α) (position : Int) : Tape α :=
  withHead (Tape.ofWord word) position

def prefixAt {α : Type*} (pre : List α) : Tape α :=
  { cells := Tape.cellsFrom pre 0, head := pre.length }

@[simp] theorem prefixAt_nil {α : Type*} :
    prefixAt ([] : List α) = Tape.blankAt 0 := rfl

private theorem set_comm {α : Type*} (cells : Int →₀ TapeSymbol α)
    {first second : Int} (hne : first ≠ second)
    (firstValue secondValue : TapeSymbol α) :
    CellStore.set (CellStore.set cells first firstValue) second secondValue =
      CellStore.set (CellStore.set cells second secondValue) first firstValue := by
  ext index
  by_cases hfirst : index = first
  · subst index
    simp [hne]
  · by_cases hsecond : index = second
    · subst index
      simp [hfirst]
    · simp [hfirst, hsecond]

theorem cellsFrom_append_singleton {α : Type*}
    (pre : List α) (symbol : α) (start : Int) :
    Tape.cellsFrom (pre ++ [symbol]) start =
      CellStore.set (Tape.cellsFrom pre start)
        (start + (pre.length : Int)) (.mark symbol) := by
  induction pre generalizing start with
  | nil => simp [Tape.cellsFrom]
  | cons head tail ih =>
      simp only [List.cons_append, Tape.cellsFrom, List.length_cons,
        Int.natCast_succ]
      rw [ih]
      rw [set_comm]
      · congr 1
        omega
      · omega

theorem prefixAt_write_move {α : Type*} (pre : List α) (symbol : α) :
    ((prefixAt pre).write (.mark symbol)).move .right =
      prefixAt (pre ++ [symbol]) := by
  simp [prefixAt, Tape.move, Tape.write, cellsFrom_append_singleton]

theorem read_workAt_append {α : Type*}
    (pre : List α) (symbol : α) (suffix : List α) :
    (workAt (pre ++ symbol :: suffix) pre.length).read = .mark symbol := by
  simp only [workAt, withHead, Tape.read, Tape.ofWord, Tape.ofWordAt]
  rw [show (pre.length : Int) = 0 + (pre.length : Int) by omega]
  rw [Tape.cellsFrom_at_nat]
  simp

theorem read_workAt_end {α : Type*} (word : List α) :
    (workAt word word.length).read = .blank := by
  change Tape.cellsFrom word 0 (word.length : Int) = .blank
  simpa using Tape.cellsFrom_right_blank word 0

theorem read_prefixAt {α : Type*} (pre : List α) :
    (prefixAt pre).read = .blank := by
  change Tape.cellsFrom pre 0 (pre.length : Int) = .blank
  simpa using Tape.cellsFrom_right_blank pre 0

theorem workAt_move_right {α : Type*} (word : List α) (position : Int) :
    (workAt word position).move .right = workAt word (position + 1) := by
  simp [workAt, withHead, Tape.move]

theorem workAt_move_left {α : Type*} (word : List α) (position : Int) :
    (workAt word position).move .left = workAt word (position - 1) := by
  simp [workAt, withHead, Tape.move]
  omega

theorem withHead_eq_self {α : Type*} (tape : Tape α) (position : Int)
    (hhead : tape.head = position) : withHead tape position = tape := by
  cases tape
  simp_all [withHead]

@[simp] theorem workAt_leftDelimiter {α : Type*} (word : List α) :
    workAt word (-1) = Tape.ofWord word := by
  apply withHead_eq_self
  exact Tape.ofWord_head word

theorem prefixAt_eq_workAt {α : Type*} (word : List α) :
    prefixAt word = workAt word word.length := by
  simp [prefixAt, workAt, withHead, Tape.ofWord, Tape.ofWordAt]

theorem ofWord_move_right {α : Type*} (word : List α) :
    (Tape.ofWord word).move .right = workAt word 0 := by
  simp [workAt, withHead, Tape.move, Tape.ofWord, Tape.ofWordAt]

theorem blankLeft_move_right {α : Type*} :
    (Tape.blankAt (-1) : Tape α).move .right = prefixAt [] := by
  simp [Tape.blankAt, Tape.move, prefixAt]

end TapeInvariant

open TapeInvariant

theorem forward_pair {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (history : Tape source.RuleId)
    (hhistory : history.read = .mark normal.exitId)
    (pre suffix : List Symbol) (symbol : Symbol) :
    let before := configuration source .copyRightRead
      (workAt (pre ++ symbol :: suffix) pre.length) history (prefixAt pre)
    (rule normal (.copySymbol symbol)).Matches before /\
      (rule normal .moveRight).Matches
        ((rule normal (.copySymbol symbol)).execute before) /\
      (rule normal .moveRight).execute
          ((rule normal (.copySymbol symbol)).execute before) =
        configuration source .copyRightRead
          (workAt (pre ++ symbol :: suffix) (pre.length + 1))
          history (prefixAt (pre ++ [symbol])) := by
  dsimp
  constructor
  · constructor
    · rfl
    · intro index
      cases index
      · exact read_workAt_append pre symbol suffix
      · exact hhistory
      · exact read_prefixAt pre
  constructor
  · constructor
    · rfl
    · intro index
      cases index <;> trivial
  · apply MultiConfiguration.ext
    · rfl
    · intro index
      cases index
      · simp only [rule, Quadruple.execute_tape,
          configuration_work]
        change
          ((workAt (pre ++ symbol :: suffix) pre.length).write
            (.mark symbol)).move .right =
            workAt (pre ++ symbol :: suffix) (pre.length + 1)
        rw [← read_workAt_append pre symbol suffix, Tape.write_read,
          workAt_move_right]
      · simp only [rule, Quadruple.execute_tape,
          configuration_history]
        change (history.write (.mark normal.exitId)).move .stay = history
        rw [← hhistory, Tape.write_read, Tape.move_stay]
      · simp only [rule, Quadruple.execute_tape,
          configuration_output]
        exact prefixAt_write_move pre symbol

theorem backward_pair {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (history : Tape source.RuleId)
    (hhistory : history.read = .mark normal.exitId)
    (pre done tail : List Symbol) (symbol : Symbol) :
    let full := pre ++ tail.reverse ++ symbol :: done
    let position : Int := pre.length + tail.length
    let before := configuration source .copyLeftRead
      (workAt full position) history (workAt full position)
    (rule normal (.checkSymbol symbol)).Matches before /\
      (rule normal .moveLeft).Matches
        ((rule normal (.checkSymbol symbol)).execute before) /\
      (rule normal .moveLeft).execute
          ((rule normal (.checkSymbol symbol)).execute before) =
        configuration source .copyLeftRead
          (workAt full (position - 1)) history (workAt full (position - 1)) := by
  dsimp
  have hread :
      (workAt (pre ++ tail.reverse ++ symbol :: done)
        (pre.length + tail.length)).read = .mark symbol := by
    simpa using read_workAt_append (pre ++ tail.reverse) symbol done
  constructor
  · constructor
    · rfl
    · intro index
      cases index
      · exact hread
      · exact hhistory
      · exact hread
  constructor
  · constructor
    · rfl
    · intro index
      cases index <;> trivial
  · apply MultiConfiguration.ext
    · rfl
    · intro index
      cases index
      · simp only [rule, Quadruple.execute_tape,
          configuration_work]
        change
          ((workAt (pre ++ tail.reverse ++ symbol :: done)
            (pre.length + tail.length)).write (.mark symbol)).move .left =
            workAt (pre ++ tail.reverse ++ symbol :: done)
              (pre.length + tail.length - 1)
        rw [← hread, Tape.write_read, workAt_move_left]
      · simp only [rule, Quadruple.execute_tape,
          configuration_history]
        change (history.write (.mark normal.exitId)).move .stay = history
        rw [← hhistory, Tape.write_read, Tape.move_stay]
      · simp only [rule, Quadruple.execute_tape,
          configuration_output]
        change
          ((workAt (pre ++ tail.reverse ++ symbol :: done)
            (pre.length + tail.length)).write (.mark symbol)).move .left =
            workAt (pre ++ tail.reverse ++ symbol :: done)
              (pre.length + tail.length - 1)
        rw [← hread, Tape.write_read, workAt_move_left]

theorem enter_pair {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (history : Tape source.RuleId)
    (hhistory : history.read = .mark normal.exitId)
    (word : List Symbol) :
    let before := configuration source (.forward normal.finish)
      (Tape.ofWord word) history (Tape.blankAt (-1))
    (rule normal .enter).Matches before /\
      (rule normal .moveRight).Matches ((rule normal .enter).execute before) /\
      (rule normal .moveRight).execute ((rule normal .enter).execute before) =
        configuration source .copyRightRead
          (workAt word 0) history (prefixAt []) := by
  dsimp
  constructor
  · constructor
    · rfl
    · intro index
      cases index
      · exact Tape.read_ofWord word
      · exact hhistory
      · exact Tape.read_blankAt (-1)
  constructor
  · constructor
    · rfl
    · intro index
      cases index <;> trivial
  · apply MultiConfiguration.ext
    · rfl
    · intro index
      cases index
      · simp only [rule, Quadruple.execute_tape,
          configuration_work]
        change ((Tape.ofWord word).write .blank).move .right = workAt word 0
        rw [← Tape.read_ofWord word, Tape.write_read, ofWord_move_right]
      · simp only [rule, Quadruple.execute_tape,
          configuration_history]
        change (history.write (.mark normal.exitId)).move .stay = history
        rw [← hhistory, Tape.write_read, Tape.move_stay]
      · simp only [rule, Quadruple.execute_tape,
          configuration_output]
        change ((Tape.blankAt (-1)).write .blank).move .right = prefixAt []
        rw [← Tape.read_blankAt (-1), Tape.write_read, blankLeft_move_right]

theorem turn_pair {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (history : Tape source.RuleId)
    (hhistory : history.read = .mark normal.exitId)
    (word : List Symbol) :
    let before := configuration source .copyRightRead
      (workAt word word.length) history (prefixAt word)
    (rule normal .turn).Matches before /\
      (rule normal .moveLeft).Matches ((rule normal .turn).execute before) /\
      (rule normal .moveLeft).execute ((rule normal .turn).execute before) =
        configuration source .copyLeftRead
          (workAt word (word.length - 1)) history
          (workAt word (word.length - 1)) := by
  dsimp
  constructor
  · constructor
    · rfl
    · intro index
      cases index
      · exact read_workAt_end word
      · exact hhistory
      · exact read_prefixAt word
  constructor
  · constructor
    · rfl
    · intro index
      cases index <;> trivial
  · apply MultiConfiguration.ext
    · rfl
    · intro index
      cases index
      · simp only [rule, Quadruple.execute_tape,
          configuration_work]
        change ((workAt word word.length).write .blank).move .left =
          workAt word (word.length - 1)
        rw [← read_workAt_end word, Tape.write_read, workAt_move_left]
      · simp only [rule, Quadruple.execute_tape,
          configuration_history]
        change (history.write (.mark normal.exitId)).move .stay = history
        rw [← hhistory, Tape.write_read, Tape.move_stay]
      · simp only [rule, Quadruple.execute_tape,
          configuration_output]
        rw [prefixAt_eq_workAt]
        change ((workAt word word.length).write .blank).move .left =
          workAt word (word.length - 1)
        rw [← read_workAt_end word, Tape.write_read, workAt_move_left]

theorem exit_step {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (history : Tape source.RuleId)
    (hhistory : history.read = .mark normal.exitId)
    (word : List Symbol) :
    let before := configuration source .copyLeftRead
      (workAt word (-1)) history (workAt word (-1))
    (rule normal .exit).Matches before /\
      (rule normal .exit).execute before =
        configuration source (.reverse normal.finish)
          (Tape.ofWord word) history (Tape.ofWord word) := by
  dsimp
  have hread : (workAt word (-1)).read = .blank := by
    rw [workAt_leftDelimiter]
    exact Tape.read_ofWord word
  constructor
  · constructor
    · rfl
    · intro index
      cases index
      · exact hread
      · exact hhistory
      · exact hread
  · apply MultiConfiguration.ext
    · rfl
    · intro index
      cases index
      · simp only [rule, Quadruple.execute_tape,
          configuration_work]
        change (workAt word (-1)).write .blank = Tape.ofWord word
        rw [← hread, Tape.write_read, workAt_leftDelimiter]
      · simp only [rule, Quadruple.execute_tape,
          configuration_history]
        change history.write (.mark normal.exitId) = history
        rw [← hhistory, Tape.write_read]
      · simp only [rule, Quadruple.execute_tape,
          configuration_output]
        change (workAt word (-1)).write .blank = Tape.ofWord word
        rw [← hread, Tape.write_read, workAt_leftDelimiter]

def forwardIds : List Symbol → List (CopyRuleId Symbol)
  | [] => []
  | symbol :: suffix => .copySymbol symbol :: .moveRight :: forwardIds suffix

def backwardIds : List Symbol → List (CopyRuleId Symbol)
  | [] => []
  | symbol :: suffix => .checkSymbol symbol :: .moveLeft :: backwardIds suffix

def ids (word : List Symbol) : List (CopyRuleId Symbol) :=
  [.enter, .moveRight] ++ forwardIds word ++ [.turn, .moveLeft] ++
    backwardIds word.reverse ++ [.exit]

def schedule {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) (word : List Symbol) :
    List (Simulator.Rule source) :=
  (ids word).map (rule normal)

omit [DecidableEq Symbol] in
@[simp] theorem forwardIds_length (word : List Symbol) :
    (forwardIds word).length = 2 * word.length := by
  induction word with
  | nil => rfl
  | cons symbol suffix ih => simp [forwardIds, ih]; omega

omit [DecidableEq Symbol] in
@[simp] theorem backwardIds_length (word : List Symbol) :
    (backwardIds word).length = 2 * word.length := by
  induction word with
  | nil => rfl
  | cons symbol suffix ih => simp [backwardIds, ih]; omega

omit [DecidableEq Symbol] in
@[simp] theorem ids_length (word : List Symbol) :
    (ids word).length = 4 * word.length + 5 := by
  simp [ids]
  omega

@[simp] theorem schedule_length {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) (word : List Symbol) :
    (schedule normal word).length = 4 * word.length + 5 := by
  simp [schedule]

theorem forward_scheduled {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (history : Tape source.RuleId)
    (hhistory : history.read = .mark normal.exitId)
    (pre suffix : List Symbol) :
    Quadruple.Scheduled ((forwardIds suffix).map (rule normal))
      (configuration source .copyRightRead
        (workAt (pre ++ suffix) pre.length) history (prefixAt pre))
      (configuration source .copyRightRead
        (workAt (pre ++ suffix) (pre ++ suffix).length)
        history (prefixAt (pre ++ suffix))) := by
  induction suffix generalizing pre with
  | nil => simp [forwardIds, Quadruple.Scheduled]
  | cons symbol tail ih =>
      have hpair := forward_pair normal history hhistory pre tail symbol
      simp only [forwardIds, List.map_cons, Quadruple.Scheduled]
      refine ⟨hpair.1, hpair.2.1, ?_⟩
      rw [hpair.2.2]
      simpa [List.append_assoc] using ih (pre ++ [symbol])

theorem backward_scheduled {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (history : Tape source.RuleId)
    (hhistory : history.read = .mark normal.exitId)
    (pre done rev : List Symbol) :
    let full := pre ++ rev.reverse ++ done
    Quadruple.Scheduled ((backwardIds rev).map (rule normal))
      (configuration source .copyLeftRead
        (workAt full (pre.length + rev.length - 1)) history
        (workAt full (pre.length + rev.length - 1)))
      (configuration source .copyLeftRead
        (workAt full (pre.length - 1)) history
        (workAt full (pre.length - 1))) := by
  dsimp
  induction rev generalizing done with
  | nil => simp [backwardIds, Quadruple.Scheduled]
  | cons symbol tail ih =>
      have hpair := backward_pair normal history hhistory pre done tail symbol
      simp only [List.append_assoc] at hpair
      simp only [backwardIds, List.map_cons, Quadruple.Scheduled]
      simp only [List.reverse_cons, List.length_cons, Int.natCast_succ,
        List.append_assoc, List.singleton_append]
      rw [show (pre.length : Int) + ((tail.length : Int) + 1) - 1 =
        (pre.length : Int) + tail.length by omega]
      refine ⟨hpair.1, hpair.2.1, ?_⟩
      rw [hpair.2.2]
      simpa [List.append_assoc] using ih (symbol :: done)

/-- Exact Table 1 copy sweep on an arbitrary physical history tape whose head
    scans the final source-rule identifier. -/
theorem scheduled {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (history : Tape source.RuleId)
    (hhistory : history.read = .mark normal.exitId)
    (word : List Symbol) :
    Quadruple.Scheduled (schedule normal word)
      (configuration source (.forward normal.finish)
        (Tape.ofWord word) history (Tape.blankAt (-1)))
      (configuration source (.reverse normal.finish)
        (Tape.ofWord word) history (Tape.ofWord word)) := by
  let start : Simulator.Configuration source :=
    configuration source (.forward normal.finish)
      (Tape.ofWord word) history (Tape.blankAt (-1))
  let rightStart : Simulator.Configuration source :=
    configuration source .copyRightRead (workAt word 0) history (prefixAt [])
  let rightEnd : Simulator.Configuration source :=
    configuration source .copyRightRead
      (workAt word word.length) history (prefixAt word)
  let leftStart : Simulator.Configuration source :=
    configuration source .copyLeftRead
      (workAt word (word.length - 1)) history
      (workAt word (word.length - 1))
  let leftEnd : Simulator.Configuration source :=
    configuration source .copyLeftRead
      (workAt word (-1)) history (workAt word (-1))
  let final : Simulator.Configuration source :=
    configuration source (.reverse normal.finish)
      (Tape.ofWord word) history (Tape.ofWord word)
  have henterPair := enter_pair normal history hhistory word
  have henter : Quadruple.Scheduled
      ([rule normal .enter, rule normal .moveRight] :
        List (Simulator.Rule source)) start rightStart := by
    simp only [Quadruple.Scheduled]
    exact ⟨henterPair.1, henterPair.2.1, henterPair.2.2⟩
  have hforward : Quadruple.Scheduled
      ((forwardIds word).map (rule normal)) rightStart rightEnd := by
    simpa [rightStart, rightEnd] using
      forward_scheduled normal history hhistory ([] : List Symbol) word
  have hturnPair := turn_pair normal history hhistory word
  have hturn : Quadruple.Scheduled
      ([rule normal .turn, rule normal .moveLeft] :
        List (Simulator.Rule source)) rightEnd leftStart := by
    simp only [Quadruple.Scheduled]
    exact ⟨hturnPair.1, hturnPair.2.1, hturnPair.2.2⟩
  have hbackward : Quadruple.Scheduled
      ((backwardIds word.reverse).map (rule normal)) leftStart leftEnd := by
    simpa [leftStart, leftEnd] using
      backward_scheduled normal history hhistory
        ([] : List Symbol) ([] : List Symbol) word.reverse
  have hexitStep := exit_step normal history hhistory word
  have hexit : Quadruple.Scheduled
      ([rule normal .exit] : List (Simulator.Rule source)) leftEnd final := by
    simp only [Quadruple.Scheduled]
    exact ⟨hexitStep.1, hexitStep.2⟩
  have hall := Quadruple.Scheduled.append
    (Quadruple.Scheduled.append
      (Quadruple.Scheduled.append
        (Quadruple.Scheduled.append henter hforward) hturn) hbackward)
    hexit
  simpa [schedule, ids, start, final, List.map_append, List.append_assoc] using hall

theorem inverse_scheduled {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (history : Tape source.RuleId)
    (hhistory : history.read = .mark normal.exitId)
    (word : List Symbol) :
    Quadruple.Scheduled (Quadruple.inverseSchedule (schedule normal word))
      (configuration source (.reverse normal.finish)
        (Tape.ofWord word) history (Tape.ofWord word))
      (configuration source (.forward normal.finish)
        (Tape.ofWord word) history (Tape.blankAt (-1))) :=
  (scheduled normal history hhistory word).inverse

/-- Specialization to the physical newest-first history encoding used by the
    compute/retrace stages. -/
theorem scheduled_encode {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (history : List source.RuleId) (word : List Symbol) :
    Quadruple.Scheduled (schedule normal word)
      (forwardConfiguration source
        { current := Standard.config normal.finish word
          history := normal.exitId :: history })
      (reverseConfiguration source
        { current := Standard.config normal.finish word
          history := normal.exitId :: history }
        (Tape.ofWord word)) := by
  change Quadruple.Scheduled (schedule normal word)
    (configuration source (.forward normal.finish) (Tape.ofWord word)
      (HistoryTape.encode (normal.exitId :: history)) (Tape.blankAt (-1)))
    (configuration source (.reverse normal.finish) (Tape.ofWord word)
      (HistoryTape.encode (normal.exitId :: history)) (Tape.ofWord word))
  exact scheduled normal (HistoryTape.encode (normal.exitId :: history))
    (HistoryTape.read_encode_cons normal.exitId history) word

example {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) :
    (schedule normal []).length = 5 := by simp

end Bennett.Turing.Simulator.Copy
