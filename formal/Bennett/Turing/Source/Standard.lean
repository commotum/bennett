import Bennett.Transition.Run
import Bennett.Turing.Source.Determinism
import Bennett.Turing.Word

/-!
# Standard source-machine inputs and outputs

The nonblank alphabet is the type parameter `Symbol`; hence a `List Symbol` has
no embedded blank by construction.  Empty words remain legal at this layer.
`NonemptyWord` is a separate explicit premise for later statements that need
the paper's diagrams' apparent nonempty convention.

The semantic standard-behavior assumptions are separated from Bennett's
stronger entry/exit normal form.  In particular, directional no-incoming and
no-outgoing fields replace the paper's ambiguous phrase “appear in no other
quintuple.”
-/

namespace Bennett.Turing
namespace Standard

variable {Control Symbol : Type*}

/-- The optional nonempty-word policy, never hidden in standard formatting. -/
def NonemptyWord (word : List Symbol) : Prop :=
  word ≠ []

/-- Exact standard configuration: word at `0,1,…`, head at the left blank `-1`. -/
def config (control : Control) (word : List Symbol) :
    Configuration Control Symbol :=
  { control := control, tape := Tape.ofWord word }

/-- Proposition exposing the represented control and word in a signature. -/
def IsConfig (state : Configuration Control Symbol)
    (control : Control) (word : List Symbol) : Prop :=
  state = config control word

@[simp] theorem config_control (control : Control) (word : List Symbol) :
    (config control word).control = control := rfl

@[simp] theorem config_head (control : Control) (word : List Symbol) :
    (config control word).tape.head = -1 := rfl

@[simp] theorem config_read (control : Control) (word : List Symbol) :
    (config control word).read = .blank :=
  Tape.read_ofWord word

theorem config_word_injective (control : Control) :
    Function.Injective (config (Symbol := Symbol) control) := by
  intro first second hconfig
  apply Tape.ofWord_injective
  exact congrArg Configuration.tape hconfig

/-- Exact source-machine computation from one standard word to another. -/
def ComputesIn [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) (start finish : Control)
    (n : Nat) (input output : List Symbol) : Prop :=
  machine.step.Runs n (config start input) (config finish output) ∧
    machine.step.Halted (config finish output)

/-- Partial input/output behavior, with exact running time existentially hidden. -/
def Computes [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) (start finish : Control)
    (input output : List Symbol) : Prop :=
  ∃ n, ComputesIn machine start finish n input output

private theorem final_eq_of_halted_runs {State : Type*}
    {step : PartialStep State} {n m : Nat} {start finish₁ finish₂ : State}
    (hrun₁ : step.Runs n start finish₁) (hhalt₁ : step.Halted finish₁)
    (hrun₂ : step.Runs m start finish₂) (hhalt₂ : step.Halted finish₂) :
    finish₁ = finish₂ := by
  have shorter_unique :
      ∀ {n m : Nat} {first second : State}, n ≤ m →
        step.Runs n start first → step.Halted first →
        step.Runs m start second → first = second := by
    intro short long first second hle hshort hhalt hlong
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [PartialStep.Runs] at hshort hlong
    rw [PartialStep.iterate_add, hshort] at hlong
    simp only [Option.bind_some] at hlong
    cases extra with
    | zero => exact Option.some.inj hlong
    | succ extra =>
        rw [PartialStep.iterate_succ, hhalt] at hlong
        contradiction
  rcases Nat.le_total n m with hle | hle
  · exact shorter_unique hle hrun₁ hhalt₁ hrun₂
  · exact (shorter_unique hle hrun₂ hhalt₂ hrun₁).symm

/-- The standard input/output relation is a partial function. -/
theorem computes_output_unique [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) (start finish : Control) (input : List Symbol)
    {output₁ output₂ : List Symbol}
    (h₁ : Computes machine start finish input output₁)
    (h₂ : Computes machine start finish input output₂) : output₁ = output₂ := by
  obtain ⟨n, hrun₁, hhalt₁⟩ := h₁
  obtain ⟨m, hrun₂, hhalt₂⟩ := h₂
  have hconfig : config finish output₁ = config finish output₂ :=
    final_eq_of_halted_runs hrun₁ hhalt₁ hrun₂ hhalt₂
  exact config_word_injective finish hconfig

/--
Semantic standard behavior: every reachable halt on an accepted standard input
has the named final control and exact standard-tape form.
-/
structure Behavior [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) where
  start : Control
  finish : Control
  accepts : List Symbol → Prop
  syntacticDeterminism : machine.SyntacticallyDeterministic
  halted_standard :
    ∀ (input : List Symbol) {n : Nat}
      {halted : Configuration Control Symbol},
      accepts input →
        machine.step.Runs n (config start input) halted →
        machine.step.Halted halted →
          ∃ output : List Symbol, halted = config finish output

/--
Bennett's stronger source normal form with directionally precise entry/exit
freshness assumptions.
-/
structure BennettNormalForm [DecidableEq Control] [DecidableEq Symbol]
    (machine : Machine Control Symbol) extends Behavior machine where
  afterEntry : Control
  beforeExit : Control
  entryId : machine.RuleId
  exitId : machine.RuleId
  entry_ne_exit : entryId ≠ exitId
  entry_rule : machine.rule entryId =
    { source := start, scanned := .blank, written := .blank,
      move := .right, target := afterEntry }
  exit_rule : machine.rule exitId =
    { source := beforeExit, scanned := .blank, written := .blank,
      move := .stay, target := finish }
  entry_only_rule_from_start :
    ∀ index, (machine.rule index).source = start → index = entryId
  no_rule_targets_start :
    ∀ index, (machine.rule index).target ≠ start
  exit_only_rule_to_finish :
    ∀ index, (machine.rule index).target = finish → index = exitId
  no_rule_sources_finish :
    ∀ index, (machine.rule index).source ≠ finish

theorem BennettNormalForm.start_ne_finish
    [DecidableEq Control] [DecidableEq Symbol]
    {machine : Machine Control Symbol} (normal : BennettNormalForm machine) :
    normal.start ≠ normal.finish := by
  have hsource := normal.no_rule_sources_finish normal.entryId
  rw [normal.entry_rule] at hsource
  exact hsource

theorem BennettNormalForm.initial_step
    [DecidableEq Control] [DecidableEq Symbol]
    {machine : Machine Control Symbol} (normal : BennettNormalForm machine)
    (word : List Symbol) :
    machine.step (config normal.start word) =
      some ((machine.rule normal.entryId).execute
        (config normal.start word)) := by
  apply (normal.syntacticDeterminism.step_eq_some_iff _ _).mpr
  refine ⟨normal.entryId, ?_, rfl⟩
  rw [normal.entry_rule]
  exact ⟨rfl, (config_read normal.start word).symm⟩

theorem BennettNormalForm.initial_step_exact
    [DecidableEq Control] [DecidableEq Symbol]
    {machine : Machine Control Symbol} (normal : BennettNormalForm machine)
    (word : List Symbol) :
    machine.step (config normal.start word) =
      some (Configuration.mk normal.afterEntry
        ((Tape.ofWord word).move .right)) := by
  have hwrite : (Tape.ofWord word).write .blank = Tape.ofWord word := by
    simpa using Tape.write_read (Tape.ofWord word)
  rw [normal.initial_step word, normal.entry_rule]
  simp [Quintuple.execute, Tape.writeMove, config, hwrite]

theorem BennettNormalForm.finish_halted
    [DecidableEq Control] [DecidableEq Symbol]
    {machine : Machine Control Symbol} (normal : BennettNormalForm machine)
    (tape : Tape Symbol) :
    machine.step.Halted { control := normal.finish, tape := tape } := by
  rw [PartialStep.Halted, machine.step_eq_none_iff]
  intro index hmatches
  exact normal.no_rule_sources_finish index hmatches.1

end Standard
end Bennett.Turing
