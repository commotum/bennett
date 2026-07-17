import Bennett.History.Core
import Bennett.Turing.Source.History
import Bennett.Turing.Source.Standard
import Lean.Elab.Tactic.Omega

/-!
# Three-tape simulator carriers and physical history encoding

The three tape roles have heterogeneous nonblank alphabets.  Histories are
abstractly newest-first lists, but are stored physically oldest-to-newest from
left to right.  The recursive sparse-tape encoding below makes pushing one
record definitionally equal to moving right onto a blank and writing it.
-/

namespace Bennett.Turing
namespace Simulator

/-- The three physical tapes in Bennett's Table 1. -/
inductive TapeId where
  | work
  | history
  | output
deriving DecidableEq, Repr

instance : Fintype TapeId where
  elems := {.work, .history, .output}
  complete index := by cases index <;> simp

/-- Work/output carry source symbols; history carries source rule IDs. -/
def TapeAlphabet {SourceControl Symbol : Type}
    (source : Machine SourceControl Symbol) : TapeId → Type
  | .work => Symbol
  | .history => source.RuleId
  | .output => Symbol

instance {SourceControl Symbol : Type} [DecidableEq Symbol]
    (source : Machine SourceControl Symbol)
    (index : TapeId) : DecidableEq (TapeAlphabet source index) := by
  cases index
  · change DecidableEq Symbol
    infer_instance
  · change DecidableEq source.RuleId
    infer_instance
  · change DecidableEq Symbol
    infer_instance

instance {SourceControl Symbol : Type} [Fintype Symbol]
    (source : Machine SourceControl Symbol)
    (index : TapeId) : Fintype (TapeAlphabet source index) := by
  cases index
  · change Fintype Symbol
    infer_instance
  · change Fintype source.RuleId
    infer_instance
  · change Fintype Symbol
    infer_instance

/-- Disjoint `A`, four-state `B`, and `C` control families. -/
inductive Control (SourceControl RuleId : Type) where
  | forward (control : SourceControl)
  | forwardConnector (ruleId : RuleId)
  | copyRightMove
  | copyRightRead
  | copyLeftMove
  | copyLeftRead
  | reverse (control : SourceControl)
  | reverseConnector (ruleId : RuleId)
deriving DecidableEq, Repr

/-- Complete physical simulator configuration for one source machine. -/
abbrev Configuration {SourceControl Symbol : Type}
    (source : Machine SourceControl Symbol) :=
  MultiConfiguration (Control SourceControl source.RuleId) TapeId
    (TapeAlphabet source)

/-- Complete typed Table 1 rule for one source machine. -/
abbrev Rule {SourceControl Symbol : Type}
    (source : Machine SourceControl Symbol) :=
  Quadruple (Control SourceControl source.RuleId) TapeId
    (TapeAlphabet source)

/-- Assemble one heterogeneous three-tape rule without dependent casts. -/
def threeRule {SourceControl Symbol : Type}
    {source : Machine SourceControl Symbol}
    (before after : Control SourceControl source.RuleId)
    (work : Action Symbol) (history : Action source.RuleId)
    (output : Action Symbol) : Rule source where
  source := before
  action
    | .work => work
    | .history => history
    | .output => output
  target := after

@[simp] theorem threeRule_work {SourceControl Symbol : Type}
    {source : Machine SourceControl Symbol}
    (before after : Control SourceControl source.RuleId)
    (work : Action Symbol) (history : Action source.RuleId)
    (output : Action Symbol) :
    (threeRule (source := source) before after work history output).action .work =
      work :=
  rfl

@[simp] theorem threeRule_history {SourceControl Symbol : Type}
    {source : Machine SourceControl Symbol}
    (before after : Control SourceControl source.RuleId)
    (work : Action Symbol) (history : Action source.RuleId)
    (output : Action Symbol) :
    (threeRule (source := source) before after work history output).action
      .history = history :=
  rfl

@[simp] theorem threeRule_output {SourceControl Symbol : Type}
    {source : Machine SourceControl Symbol}
    (before after : Control SourceControl source.RuleId)
    (work : Action Symbol) (history : Action source.RuleId)
    (output : Action Symbol) :
    (threeRule (source := source) before after work history output).action
      .output = output :=
  rfl

namespace HistoryTape

variable {RuleId : Type*}

/-- Every cell strictly to the right of the history head is blank. -/
def RightBlank (tape : Tape RuleId) : Prop :=
  ∀ position, tape.head < position → tape.cells position = .blank

/--
Physical encoding of a newest-first history stack.

The tail is encoded first.  A new top record is appended at the right by moving
once and writing, so `record :: history` is physically oldest-to-newest.
-/
def encode : List RuleId → Tape RuleId
  | [] => Tape.blankAt (-1)
  | record :: history => (encode history).move .right |>.write (.mark record)

@[simp] theorem encode_nil : encode ([] : List RuleId) = Tape.blankAt (-1) :=
  rfl

@[simp] theorem encode_cons (record : RuleId) (history : List RuleId) :
    encode (record :: history) =
      ((encode history).move .right).write (.mark record) :=
  rfl

@[simp] theorem head_encode (history : List RuleId) :
    (encode history).head = (history.length : Int) + (-1) := by
  induction history with
  | nil => rfl
  | cons record history ih =>
      simp [encode, ih]

theorem rightBlank_encode (history : List RuleId) :
    RightBlank (encode history) := by
  induction history with
  | nil =>
      intro position hposition
      rfl
  | cons record history ih =>
      intro position hposition
      rw [encode]
      have hne : position ≠ ((encode history).move .right).head := by
        exact ne_of_gt hposition
      rw [Tape.write_cells_of_ne _ _ hne]
      exact ih position (by
        have hmoved :
            ((encode history).move .right).head < position := by
          simpa using hposition
        exact lt_trans (by simp) hmoved)

@[simp] theorem read_move_right_encode (history : List RuleId) :
    ((encode history).move .right).read = .blank := by
  apply rightBlank_encode history
  simp

@[simp] theorem read_encode_cons (record : RuleId) (history : List RuleId) :
    (encode (record :: history)).read = .mark record := by
  simp [encode]

/-- Erasing the newest record exposes the blank just beyond the remaining stack. -/
@[simp] theorem erase_encode_cons (record : RuleId) (history : List RuleId) :
    (encode (record :: history)).write .blank =
      (encode history).move .right := by
  simp only [encode, Tape.write_write]
  rw [← read_move_right_encode history, Tape.write_read]

/-- Erase the newest record and move left to recover the exact tail encoding. -/
@[simp] theorem pop_encode_cons (record : RuleId) (history : List RuleId) :
    ((encode (record :: history)).write .blank).move .left =
      encode history := by
  rw [erase_encode_cons]
  exact Tape.move_inverse (encode history) .right

theorem support_encode (history : List RuleId) :
    (encode history).nonblankPositions =
      Finset.Ico 0 (history.length : Int) := by
  induction history with
  | nil => simp [encode, Tape.nonblankPositions]
  | cons record history ih =>
      rw [encode]
      change insert ((encode history).move .right).head
        (encode history).cells.support =
          Finset.Ico 0 ((List.length (record :: history) : Nat) : Int)
      change (encode history).cells.support =
        Finset.Ico 0 (history.length : Int) at ih
      rw [show ((encode history).move .right).head =
        (history.length : Int) by simp [head_encode], ih]
      simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
      ext position
      simp only [Finset.mem_insert, Finset.mem_Ico]
      constructor
      · rintro (hposition | ⟨hlower, hupper⟩)
        · subst position
          omega
        · omega
      · rintro ⟨hlower, hupper⟩
        by_cases hposition : position = (history.length : Int)
        · exact Or.inl hposition
        · exact Or.inr (by omega)

@[simp] theorem nonblankCard_encode (history : List RuleId) :
    (encode history).nonblankPositions.card = history.length := by
  rw [support_encode]
  simp

end HistoryTape

variable {SourceControl Symbol : Type}

/-- Physical forward-phase encoding of an abstract recorded source state. -/
def forwardConfiguration (source : Machine SourceControl Symbol)
    (state : HistoryState (Bennett.Turing.Configuration SourceControl Symbol)
      source.RuleId) :
    Simulator.Configuration source where
  control := .forward state.current.control
  tape
    | .work => state.current.tape
    | .history => HistoryTape.encode state.history
    | .output => Tape.blankAt (-1)

/-- Physical reverse-phase encoding, with an arbitrary retained copied output. -/
def reverseConfiguration (source : Machine SourceControl Symbol)
    (state : HistoryState (Bennett.Turing.Configuration SourceControl Symbol)
      source.RuleId)
    (copiedOutput : Tape Symbol) : Simulator.Configuration source where
  control := .reverse state.current.control
  tape
    | .work => state.current.tape
    | .history => HistoryTape.encode state.history
    | .output => copiedOutput

/-- Exact initial physical configuration for a standard input word. -/
def initialConfiguration (source : Machine SourceControl Symbol)
    (start : SourceControl) (input : List Symbol) :
    Simulator.Configuration source :=
  forwardConfiguration source
    { current := Standard.config start input, history := [] }

/-- Exact cleaned endpoint retaining standard input and copied standard output. -/
def finalConfiguration (source : Machine SourceControl Symbol)
    (start : SourceControl) (input output : List Symbol) :
    Simulator.Configuration source :=
  reverseConfiguration source
    { current := Standard.config start input, history := [] }
    (Tape.ofWord output)

@[simp] theorem initial_control (source : Machine SourceControl Symbol)
    (start : SourceControl) (input : List Symbol) :
    (initialConfiguration source start input).control = .forward start :=
  rfl

@[simp] theorem initial_work (source : Machine SourceControl Symbol)
    (start : SourceControl) (input : List Symbol) :
    (initialConfiguration source start input).tape .work = Tape.ofWord input :=
  rfl

@[simp] theorem initial_history (source : Machine SourceControl Symbol)
    (start : SourceControl) (input : List Symbol) :
    (initialConfiguration source start input).tape .history = Tape.blankAt (-1) :=
  rfl

@[simp] theorem initial_output (source : Machine SourceControl Symbol)
    (start : SourceControl) (input : List Symbol) :
    (initialConfiguration source start input).tape .output = Tape.blankAt (-1) :=
  rfl

@[simp] theorem final_control (source : Machine SourceControl Symbol)
    (start : SourceControl) (input output : List Symbol) :
    (finalConfiguration source start input output).control = .reverse start :=
  rfl

@[simp] theorem final_work (source : Machine SourceControl Symbol)
    (start : SourceControl) (input output : List Symbol) :
    (finalConfiguration source start input output).tape .work = Tape.ofWord input :=
  rfl

@[simp] theorem final_history (source : Machine SourceControl Symbol)
    (start : SourceControl) (input output : List Symbol) :
    (finalConfiguration source start input output).tape .history =
      Tape.blankAt (-1) :=
  rfl

@[simp] theorem final_output (source : Machine SourceControl Symbol)
    (start : SourceControl) (input output : List Symbol) :
    (finalConfiguration source start input output).tape .output =
      Tape.ofWord output :=
  rfl

end Simulator
end Bennett.Turing
