import Bennett.Transition.Run
import Bennett.Turing.Word
import Lean.Elab.Tactic.Omega

/-!
# Execution traces and tape resource measures

`ExecutionTrace` makes the initial state structurally mandatory.  Thus a
zero-transition trace contains one state and visits its scanned cell; a final
failed halting query contributes neither a transition nor an additional state.

The tape measures deliberately remain distinct:

* `visitedPositions`: head positions scanned by trace states;
* `everNonblankPositions`: union of finite nonblank supports;
* `footprintPositions`: their union;
* `maximumNonblankCells`: peak simultaneous nonblank support;
* `maximumActiveCells`: peak simultaneous support plus the scanned cell.
-/

namespace Bennett

/-- A nonempty finite state trace, split into mandatory initial and later states. -/
structure ExecutionTrace (State : Type*) where
  initial : State
  subsequent : List State
deriving DecidableEq, Repr

namespace ExecutionTrace

variable {State Symbol : Type*}

/-- The one-state, zero-transition trace. -/
def singleton (state : State) : ExecutionTrace State :=
  ⟨state, []⟩

/-- Prefix a state before an already nonempty trace. -/
def prepend (state : State) (trace : ExecutionTrace State) :
    ExecutionTrace State :=
  ⟨state, trace.initial :: trace.subsequent⟩

/-- All states in chronological order, including both endpoints. -/
def states (trace : ExecutionTrace State) : List State :=
  trace.initial :: trace.subsequent

/-- Number of successful transitions represented by the trace. -/
def transitionCount (trace : ExecutionTrace State) : Nat :=
  trace.subsequent.length

/-- Last state, equal to the initial state for a zero-transition trace. -/
def final (trace : ExecutionTrace State) : State :=
  trace.subsequent.foldl (fun _ next => next) trace.initial

/-- Execute exactly `n` transitions and retain every state including endpoints. -/
def run (step : PartialStep State) : Nat → State → Option (ExecutionTrace State)
  | 0, state => some (singleton state)
  | n + 1, state => do
      let next ← step state
      let rest ← run step n next
      pure (prepend state rest)

@[simp] theorem states_singleton (state : State) :
    (singleton state).states = [state] := rfl

@[simp] theorem states_prepend (state : State) (trace : ExecutionTrace State) :
    (prepend state trace).states = state :: trace.states := rfl

@[simp] theorem states_length (trace : ExecutionTrace State) :
    trace.states.length = trace.transitionCount + 1 := by
  simp [states, transitionCount]

@[simp] theorem transitionCount_singleton (state : State) :
    (singleton state).transitionCount = 0 := rfl

@[simp] theorem transitionCount_prepend (state : State)
    (trace : ExecutionTrace State) :
    (prepend state trace).transitionCount = trace.transitionCount + 1 := by
  simp [prepend, transitionCount]

@[simp] theorem final_singleton (state : State) :
    (singleton state).final = state := rfl

@[simp] theorem final_prepend (state : State) (trace : ExecutionTrace State) :
    (prepend state trace).final = trace.final := rfl

@[simp] theorem run_zero (step : PartialStep State) (state : State) :
    run step 0 state = some (singleton state) := rfl

theorem transitionCount_of_run (step : PartialStep State)
    {n : Nat} {start : State} {trace : ExecutionTrace State}
    (htrace : run step n start = some trace) :
    trace.transitionCount = n := by
  induction n generalizing start trace with
  | zero =>
      simp only [run, Option.some.injEq] at htrace
      subst trace
      rfl
  | succ n ih =>
      change
        (step start).bind (fun next =>
          (run step n next).bind (fun rest =>
            some (prepend start rest))) = some trace at htrace
      cases hstep : step start with
      | none => simp [hstep] at htrace
      | some next =>
          cases hrest : run step n next with
          | none => simp [hstep, hrest] at htrace
          | some rest =>
              simp [hstep, hrest] at htrace
              subst trace
              simp [ih hrest]

/-- A generated trace has the same exact endpoint as `PartialStep.iterate`. -/
theorem runs_final_of_run (step : PartialStep State)
    {n : Nat} {start : State} {trace : ExecutionTrace State}
    (htrace : run step n start = some trace) :
    step.Runs n start trace.final := by
  induction n generalizing start trace with
  | zero =>
      simp only [run, Option.some.injEq] at htrace
      subst trace
      rfl
  | succ n ih =>
      change
        (step start).bind (fun next =>
          (run step n next).bind (fun rest =>
            some (prepend start rest))) = some trace at htrace
      cases hstep : step start with
      | none => simp [hstep] at htrace
      | some next =>
          cases hrest : run step n next with
          | none => simp [hstep, hrest] at htrace
          | some rest =>
              have htraceEq : prepend start rest = trace := by
                apply Option.some.inj
                simpa [hstep, hrest] using htrace
              subst trace
              rw [PartialStep.Runs, PartialStep.iterate_succ, hstep]
              simpa [PartialStep.Runs] using ih hrest

/-- Exact runs are equivalently nonempty traces with the same endpoint. -/
theorem runs_iff_exists_run (step : PartialStep State)
    (n : Nat) (start finish : State) :
    step.Runs n start finish ↔
      ∃ trace : ExecutionTrace State,
        run step n start = some trace ∧ trace.final = finish := by
  constructor
  · intro hrun
    induction n generalizing start finish with
    | zero =>
        have hfinish := (PartialStep.runs_zero_iff step start finish).mp hrun
        subst finish
        exact ⟨singleton start, rfl, rfl⟩
    | succ n ih =>
        obtain ⟨next, hstep, htail⟩ :=
          (PartialStep.runs_succ_iff step n start finish).mp hrun
        obtain ⟨rest, hrest, hfinal⟩ :=
          ih (start := next) (finish := finish) htail
        refine ⟨prepend start rest, ?_, ?_⟩
        · simp [run, hstep, hrest]
        · simp [hfinal]
  · rintro ⟨trace, htrace, rfl⟩
    exact runs_final_of_run step htrace

/-- Absolute head positions scanned by a nonempty trace. -/
def visitedPositions (tape : State → Turing.Tape Symbol)
    (trace : ExecutionTrace State) : Finset Int :=
  (trace.states.map fun state => (tape state).head).toFinset

/-- Every position holding a nonblank symbol in at least one trace state. -/
def everNonblankPositions (tape : State → Turing.Tape Symbol)
    (trace : ExecutionTrace State) : Finset Int :=
  trace.states.foldl
    (fun positions state => positions ∪ (tape state).nonblankPositions) ∅

/-- Scanned positions together with every position ever holding nonblank data. -/
def footprintPositions (tape : State → Turing.Tape Symbol)
    (trace : ExecutionTrace State) : Finset Int :=
  visitedPositions tape trace ∪ everNonblankPositions tape trace

/-- Peak simultaneous number of nonblank cells. -/
def maximumNonblankCells (tape : State → Turing.Tape Symbol)
    (trace : ExecutionTrace State) : Nat :=
  trace.states.foldl
    (fun peak state => max peak (tape state).nonblankPositions.card) 0

/-- Peak simultaneous nonblank cells plus the currently scanned cell. -/
def maximumActiveCells (tape : State → Turing.Tape Symbol)
    (trace : ExecutionTrace State) : Nat :=
  trace.states.foldl
    (fun peak state => max peak (tape state).activePositions.card) 0

@[simp] theorem visitedPositions_singleton
    (tape : State → Turing.Tape Symbol) (state : State) :
    visitedPositions tape (singleton state) = {(tape state).head} := by
  simp [visitedPositions]

@[simp] theorem everNonblankPositions_singleton
    (tape : State → Turing.Tape Symbol) (state : State) :
    everNonblankPositions tape (singleton state) =
      (tape state).nonblankPositions := by
  simp [everNonblankPositions]

@[simp] theorem footprintPositions_singleton
    (tape : State → Turing.Tape Symbol) (state : State) :
    footprintPositions tape (singleton state) = (tape state).activePositions := by
  ext position
  simp [footprintPositions, Turing.Tape.activePositions]

@[simp] theorem maximumNonblankCells_singleton
    (tape : State → Turing.Tape Symbol) (state : State) :
    maximumNonblankCells tape (singleton state) =
      (tape state).nonblankPositions.card := by
  simp [maximumNonblankCells]

@[simp] theorem maximumActiveCells_singleton
    (tape : State → Turing.Tape Symbol) (state : State) :
    maximumActiveCells tape (singleton state) =
      (tape state).activePositions.card := by
  simp [maximumActiveCells]

end ExecutionTrace

namespace Turing.Tape

variable {Symbol : Type*}

/-- Potential complete left-delimiter-to-right-delimiter sweep of a word. -/
def delimiterTraversal (word : List Symbol) : Finset Int :=
  Finset.Icc (-1) (word.length : Int)

/-- A delimiter-to-delimiter sweep has `length + 2` distinct positions. -/
@[simp] theorem delimiterTraversal_card (word : List Symbol) :
    (delimiterTraversal word).card = word.length + 2 := by
  rw [delimiterTraversal, Int.card_Icc]
  omega

/-- Even the empty word has distinct left and right delimiter cells. -/
example : (delimiterTraversal ([] : List Symbol)).card = 2 := by simp

end Turing.Tape
end Bennett
