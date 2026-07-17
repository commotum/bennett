import Bennett.Turing.Simulator.API

/-!
# Executable audit for the three-tape simulator

The three-rule source machine below traverses one blank cell to the right,
returns left, and exits in Bennett normal form.  On the empty word it computes
in exactly three source transitions.  The examples exercise the complete Table
1 construction, including its exact rule and transition counts and its global
domain/range nonoverlap theorem.

The accepted-input predicate is deliberately empty: the audit needs only one
explicit `ComputesIn` witness and does not claim a semantic classification of
all inputs.  Nothing in this file is re-exported by the public API.
-/

namespace Bennett.Turing.SimulatorAudit

open Bennett

abbrev TinyControl := Fin 4
abbrev TinySymbol := Unit

/-- Entry-right, return-left, and exit-stay source rules. -/
def tinyRule : Fin 3 → Quintuple TinyControl TinySymbol
  | ⟨0, _⟩ =>
      { source := 0, scanned := .blank, written := .blank,
        move := .right, target := 1 }
  | ⟨1, _⟩ =>
      { source := 1, scanned := .blank, written := .blank,
        move := .left, target := 2 }
  | ⟨2, _⟩ =>
      { source := 2, scanned := .blank, written := .blank,
        move := .stay, target := 3 }

def tinySource : Machine TinyControl TinySymbol where
  ruleCount := 3
  rule := tinyRule

def tinyEntryId : tinySource.RuleId := ⟨0, by decide⟩
def tinyReturnId : tinySource.RuleId := ⟨1, by decide⟩
def tinyExitId : tinySource.RuleId := ⟨2, by decide⟩

@[simp] theorem tiny_rule_entry : tinySource.rule tinyEntryId =
    { source := 0, scanned := .blank, written := .blank,
      move := .right, target := 1 } := rfl

@[simp] theorem tiny_rule_return : tinySource.rule tinyReturnId =
    { source := 1, scanned := .blank, written := .blank,
      move := .left, target := 2 } := rfl

@[simp] theorem tiny_rule_exit : tinySource.rule tinyExitId =
    { source := 2, scanned := .blank, written := .blank,
      move := .stay, target := 3 } := rfl

/-- A source normal-form witness sufficient for the concrete execution audit. -/
def tinyNormal : Standard.BennettNormalForm tinySource where
  start := 0
  finish := 3
  accepts := fun _ => False
  syntacticDeterminism := by
    intro first second hkey
    fin_cases first <;> fin_cases second <;>
      simp [tinySource, tinyRule, Quintuple.key] at hkey ⊢
  halted_standard := by
    intro input n halted haccept
    exact False.elim haccept
  afterEntry := 1
  beforeExit := 2
  entryId := tinyEntryId
  exitId := tinyExitId
  entry_ne_exit := by decide
  entry_rule := rfl
  exit_rule := rfl
  entry_only_rule_from_start := by
    intro index hsource
    fin_cases index <;>
      simp [tinySource, tinyRule, tinyEntryId] at hsource ⊢
  no_rule_targets_start := by
    intro index
    fin_cases index <;> simp [tinySource, tinyRule]
  exit_only_rule_to_finish := by
    intro index htarget
    fin_cases index <;>
      simp [tinySource, tinyRule, tinyExitId] at htarget ⊢
  no_rule_sources_finish := by
    intro index
    fin_cases index <;> simp [tinySource, tinyRule]

def tinyAfterEntry : Configuration TinyControl TinySymbol :=
  { control := 1, tape := (Tape.ofWord []).move .right }

private theorem write_blank_of_read_blank {Symbol : Type} (tape : Tape Symbol)
    (hread : tape.read = .blank) : tape.write .blank = tape := by
  rw [← hread]
  exact Tape.write_read tape

theorem tiny_step_entry :
    tinySource.step (Standard.config 0 ([] : List TinySymbol)) =
      some tinyAfterEntry := by
  apply (tinyNormal.syntacticDeterminism.step_eq_some_iff _ _).mpr
  refine ⟨tinyEntryId, ?_, ?_⟩
  · rw [tiny_rule_entry]
    exact ⟨rfl, rfl⟩
  · rw [tiny_rule_entry]
    change
      { control := 1,
        tape := ((Tape.ofWord ([] : List TinySymbol)).write .blank).move .right } =
      tinyAfterEntry
    rw [write_blank_of_read_blank _ (Tape.read_ofWord [])]
    rfl

theorem tiny_step_return :
    tinySource.step tinyAfterEntry =
      some (Standard.config 2 ([] : List TinySymbol)) := by
  apply (tinyNormal.syntacticDeterminism.step_eq_some_iff _ _).mpr
  refine ⟨tinyReturnId, ?_, ?_⟩
  · rw [tiny_rule_return]
    exact ⟨rfl, rfl⟩
  · rw [tiny_rule_return]
    rw [Quintuple.execute_order]
    simp only
    rw [write_blank_of_read_blank _ (by rfl)]
    rfl

theorem tiny_step_exit :
    tinySource.step (Standard.config 2 ([] : List TinySymbol)) =
      some (Standard.config 3 ([] : List TinySymbol)) := by
  apply (tinyNormal.syntacticDeterminism.step_eq_some_iff _ _).mpr
  refine ⟨tinyExitId, ?_, ?_⟩
  · rw [tiny_rule_exit]
    exact ⟨rfl, rfl⟩
  · rw [tiny_rule_exit]
    rw [Quintuple.execute_order]
    simp only
    rw [write_blank_of_read_blank _ (by rfl)]
    rfl

/-- The empty word reaches the standard finish configuration in exactly three steps. -/
theorem tiny_computes_empty :
    Standard.ComputesIn tinySource tinyNormal.start tinyNormal.finish
      3 ([] : List TinySymbol) [] := by
  unfold Standard.ComputesIn
  constructor
  · simpa [tinyNormal] using
      PartialStep.runs_trans (PartialStep.runs_one tiny_step_entry)
        (PartialStep.runs_trans (PartialStep.runs_one tiny_step_return)
          (PartialStep.runs_one tiny_step_exit))
  · change tinySource.step.Halted
      { control := tinyNormal.finish, tape := Tape.ofWord [] }
    exact tinyNormal.finish_halted (Tape.ofWord [])

noncomputable def tinyEnumeration :
    Simulator.TableRuleId tinySource.RuleId TinySymbol ≃
      Fin (Fintype.card (Simulator.TableRuleId tinySource.RuleId TinySymbol)) :=
  Fintype.equivFin _

/-- `4N + 2z + 3 = 19` for `N = 3` and full source alphabet size `z = 2`. -/
theorem tiny_table_rule_count :
    (Simulator.machineWithEnumeration tinyNormal tinyEnumeration).ruleCount = 19 := by
  simp [tinySource]

/-- The instantiated Table 1 machine has disjoint rule domains and ranges. -/
theorem tiny_table_syntactically_reversible :
    (Simulator.machineWithEnumeration tinyNormal
      tinyEnumeration).SyntacticallyReversible :=
  Simulator.machineWithEnumeration_syntacticallyReversible
    tinyNormal tinyEnumeration

/-- Exact end-to-end target time: `4 * 3 + 4 * 0 + 5 = 17`. -/
theorem tiny_simulator_runs_17 :
    (Simulator.machineWithEnumeration tinyNormal tinyEnumeration).step.Runs 17
      (Simulator.initialConfiguration tinySource tinyNormal.start [])
      (Simulator.finalConfiguration tinySource tinyNormal.start [] []) := by
  simpa using Simulator.runs_of_computesIn
    tinyNormal tinyEnumeration tiny_computes_empty

#print axioms tiny_computes_empty
#print axioms tiny_table_rule_count
#print axioms tiny_table_syntactically_reversible
#print axioms tiny_simulator_runs_17
#print axioms Bennett.Turing.Simulator.scheduled_of_computesIn
#print axioms Bennett.Turing.Simulator.machineWithEnumeration_syntacticallyReversible
#print axioms Bennett.Turing.Simulator.terminates_iff_source
#print axioms Bennett.Turing.Simulator.central_correctness

end Bennett.Turing.SimulatorAudit
