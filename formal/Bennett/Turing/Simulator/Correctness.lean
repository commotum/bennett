import Bennett.Turing.Simulator.Nonoverlap

/-!
# End-to-end three-tape simulation correctness

This file composes the exact forward recording, blank-target copy, and reverse
cleanup schedules.  The final endpoint retains the original standard input,
contains the standard output on the third tape, and has a literally blank
history tape with all three heads restored to their standard positions.
-/

namespace Bennett.Turing
namespace Simulator

variable {SourceControl Symbol : Type}
  [DecidableEq SourceControl] [DecidableEq Symbol]

/-- A normal-form source run reaching its finish state has positive length. -/
theorem sourceSteps_ne_zero_of_run_to_finish
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    {sourceSteps : Nat} {input output : List Symbol}
    (hrun : source.step.Runs sourceSteps
      (Standard.config normal.start input)
      (Standard.config normal.finish output)) :
    sourceSteps ≠ 0 := by
  intro hzero
  subst sourceSteps
  have hconfig :=
    (PartialStep.runs_zero_iff source.step
      (Standard.config normal.start input)
      (Standard.config normal.finish output)).mp hrun
  have hcontrol := congrArg Bennett.Turing.Configuration.control hconfig
  exact normal.start_ne_finish (by simpa using hcontrol)

/--
Exact constructor-tagged compute–copy–retrace schedule for a known standard
source computation.  Its transition count is `4v + 4λ + 5`, where `v` is
the source running time and `λ` the output length.
-/
theorem scheduled_of_computesIn
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    {sourceSteps : Nat} {input output : List Symbol}
    (hcompute : Standard.ComputesIn source normal.start normal.finish
      sourceSteps input output) :
    ∃ historyTail rules,
      (normal.exitId :: historyTail).length = sourceSteps ∧
      rules.length = 4 * sourceSteps + 4 * output.length + 5 ∧
      Quadruple.Scheduled rules
        (initialConfiguration source normal.start input)
        (finalConfiguration source normal.start input output) ∧
      OnlyTableRules normal rules := by
  obtain ⟨hrun, _⟩ := hcompute
  have hpositive := sourceSteps_ne_zero_of_run_to_finish normal hrun
  obtain ⟨n, hsteps⟩ := Nat.exists_eq_succ_of_ne_zero hpositive
  subst sourceSteps
  obtain ⟨historyTail, forwardRules, reverseRules, hhistory,
      hforwardLength, hreverseLength, hforward, hreverse,
      hforwardOnly, hreverseOnly⟩ :=
    forward_reverse_scheduled_to_standard_finish normal output hrun
  have hcopy := Copy.scheduled_encode normal historyTail output
  let rules := forwardRules ++ Copy.schedule normal output ++ reverseRules
  refine ⟨historyTail, rules, ?_, ?_, ?_, ?_⟩
  · simp [hhistory]
  · simp [rules, hforwardLength, hreverseLength]
    omega
  · simpa [rules, initialConfiguration, finalConfiguration] using
      Quadruple.Scheduled.append
        (Quadruple.Scheduled.append hforward hcopy) hreverse
  · exact OnlyTableRules.append normal
      (OnlyTableRules.append normal
        (onlyTableRules_of_forward normal hforwardOnly)
        (onlyTableRules_copy normal output))
      (onlyTableRules_of_reverse normal hreverseOnly)

/-- No Table 1 rule is enabled at the cleaned reverse-start endpoint. -/
theorem tableRule_not_matches_final
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (input output : List Symbol)
    (ruleId : TableRuleId source.RuleId Symbol) :
    ¬(tableRule normal ruleId).Matches
      (finalConfiguration source normal.start input output) := by
  intro hmatches
  have hcontrol := hmatches.1
  cases ruleId with
  | forward ruleId =>
      cases ruleId <;>
        simp [tableRule, forwardRule, forwardRewriteRule,
          forwardRecordRule, finalConfiguration, reverseConfiguration,
          threeRule] at hcontrol
  | copy ruleId =>
      cases ruleId <;>
        simp [tableRule, Copy.rule, Copy.ruleAt, finalConfiguration,
          reverseConfiguration, threeRule] at hcontrol
  | reverse ruleId =>
      cases ruleId with
      | eraseRecordMove sourceRuleId =>
          have htarget : (source.rule sourceRuleId).target = normal.start := by
            simpa [tableRule, reverseRule, reverseEraseRule,
              finalConfiguration, reverseConfiguration, threeRule] using hcontrol
          exact normal.no_rule_targets_start sourceRuleId htarget
      | restoreSymbol sourceRuleId =>
          simp [tableRule, reverseRule, reverseRestoreRule,
            finalConfiguration, reverseConfiguration, threeRule] at hcontrol

/-- The cleaned endpoint is a genuine halt of every enumerated Table 1 table. -/
theorem final_halted [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    (input output : List Symbol) :
    (machineWithEnumeration normal enumerate).step.Halted
      (finalConfiguration source normal.start input output) := by
  rw [PartialStep.Halted, QuadrupleMachine.step]
  simp only [Option.map_eq_none_iff]
  rw [QuadrupleMachine.select_eq_none_iff]
  intro index
  exact tableRule_not_matches_final normal input output
    (enumerate.symm index)

/-- Transport the exact constructor schedule to executable table semantics. -/
theorem runs_of_computesIn_of_domains [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    (hdomains : (machineWithEnumeration normal enumerate).DomainsDisjoint)
    {sourceSteps : Nat} {input output : List Symbol}
    (hcompute : Standard.ComputesIn source normal.start normal.finish
      sourceSteps input output) :
    (machineWithEnumeration normal enumerate).step.Runs
      (4 * sourceSteps + 4 * output.length + 5)
      (initialConfiguration source normal.start input)
      (finalConfiguration source normal.start input output) := by
  obtain ⟨history, rules, _, hlength, hscheduled, htable⟩ :=
    scheduled_of_computesIn normal hcompute
  have hrun := Quadruple.Scheduled.toRuns hdomains
    (tableRules_contained enumerate htable) hscheduled
  simpa [hlength] using hrun

/--
If the source has every finite prefix, so does the full simulator.  This rules
out premature target halting on standard inputs without assuming a priori that
the source eventually reaches the copy phase.
-/
theorem runsForever_of_source_runsForever_of_domains [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    (hdomains : (machineWithEnumeration normal enumerate).DomainsDisjoint)
    (input : List Symbol)
    (hforever : source.step.RunsForever
      (Standard.config normal.start input)) :
    (machineWithEnumeration normal enumerate).step.RunsForever
      (initialConfiguration source normal.start input) := by
  intro targetSteps
  obtain ⟨after, hsource⟩ := hforever targetSteps
  obtain ⟨history, rules, _, hlength, hscheduled, hforward⟩ :=
    forward_scheduled_of_run_empty source hsource
  have htable := onlyTableRules_of_forward normal hforward
  have htarget := Quadruple.Scheduled.toRuns hdomains
    (tableRules_contained enumerate htable) hscheduled
  have htwice : (machineWithEnumeration normal enumerate).step.Runs
      (2 * targetSteps)
      (initialConfiguration source normal.start input)
      (forwardConfiguration source { current := after, history := history }) := by
    simpa [hlength, initialConfiguration] using htarget
  exact PartialStep.exists_prefix_of_runs (by omega) htwice

/-- Accepted source termination implies termination at the exact cleaned endpoint. -/
theorem terminates_of_source_terminates_of_domains [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    (hdomains : (machineWithEnumeration normal enumerate).DomainsDisjoint)
    (input : List Symbol) (haccept : normal.accepts input)
    (hterminates : source.step.Terminates
      (Standard.config normal.start input)) :
    (machineWithEnumeration normal enumerate).step.Terminates
      (initialConfiguration source normal.start input) := by
  obtain ⟨sourceSteps, halted, hrun, hhalt⟩ := hterminates
  obtain ⟨output, hstandard⟩ :=
    normal.halted_standard input haccept hrun hhalt
  subst halted
  let targetSteps := 4 * sourceSteps + 4 * output.length + 5
  refine ⟨targetSteps, finalConfiguration source normal.start input output,
    ?_, final_halted normal enumerate input output⟩
  exact runs_of_computesIn_of_domains normal enumerate hdomains ⟨hrun, hhalt⟩

/--
On accepted standard inputs, full simulator termination is equivalent to
source termination.  The backward implication is proved by divergence
preservation and therefore also excludes malformed mid-phase halts reachable
from the standard initial configuration.
-/
theorem terminates_iff_source_of_domains [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    (hdomains : (machineWithEnumeration normal enumerate).DomainsDisjoint)
    (input : List Symbol) (haccept : normal.accepts input) :
    (machineWithEnumeration normal enumerate).step.Terminates
        (initialConfiguration source normal.start input) ↔
      source.step.Terminates (Standard.config normal.start input) := by
  constructor
  · intro htarget
    by_contra hsource
    have hsourceForever :=
      (PartialStep.runsForever_iff_not_terminates source.step
        (Standard.config normal.start input)).mpr hsource
    have htargetForever := runsForever_of_source_runsForever_of_domains
      normal enumerate hdomains input hsourceForever
    exact PartialStep.not_runsForever_of_terminates htarget htargetForever
  · exact terminates_of_source_terminates_of_domains normal enumerate
      hdomains input haccept

/-- Exact target run under the proved global nonoverlap theorem. -/
theorem runs_of_computesIn [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    {sourceSteps : Nat} {input output : List Symbol}
    (hcompute : Standard.ComputesIn source normal.start normal.finish
      sourceSteps input output) :
    (machineWithEnumeration normal enumerate).step.Runs
      (4 * sourceSteps + 4 * output.length + 5)
      (initialConfiguration source normal.start input)
      (finalConfiguration source normal.start input output) :=
  runs_of_computesIn_of_domains normal enumerate
    (machineWithEnumeration_syntacticallyReversible normal enumerate).1 hcompute

/-- Full-machine/source halting equivalence on accepted standard inputs. -/
theorem terminates_iff_source [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    (input : List Symbol) (haccept : normal.accepts input) :
    (machineWithEnumeration normal enumerate).step.Terminates
        (initialConfiguration source normal.start input) ↔
      source.step.Terminates (Standard.config normal.start input) :=
  terminates_iff_source_of_domains normal enumerate
    (machineWithEnumeration_syntacticallyReversible normal enumerate).1
    input haccept

/--
Inspectable certificate for the central simulation theorem.  Endpoint fields
spell out every tape and control rather than hiding them behind the word
"emulates"; the exact run field proves input retention, output production, and
cleanup operationally.
-/
structure SimulationCertificate [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    (sourceSteps : Nat) (input output : List Symbol) : Prop where
  accepted : normal.accepts input
  sourceRun : source.step.Runs sourceSteps
    (Standard.config normal.start input)
    (Standard.config normal.finish output)
  sourceHalted : source.step.Halted (Standard.config normal.finish output)
  tableSyntacticallyReversible :
    (machineWithEnumeration normal enumerate).SyntacticallyReversible
  tableRelationDeterministic :
    Relator.RightUnique (machineWithEnumeration normal enumerate).StepRel
  tableStepReversible :
    (machineWithEnumeration normal enumerate).step.Reversible
  targetRun : (machineWithEnumeration normal enumerate).step.Runs
    (4 * sourceSteps + 4 * output.length + 5)
    (initialConfiguration source normal.start input)
    (finalConfiguration source normal.start input output)
  targetHalted : (machineWithEnumeration normal enumerate).step.Halted
    (finalConfiguration source normal.start input output)
  initialControl : (initialConfiguration source normal.start input).control =
    .forward normal.start
  initialWork : (initialConfiguration source normal.start input).tape .work =
    Tape.ofWord input
  initialHistory :
    (initialConfiguration source normal.start input).tape .history =
      Tape.blankAt (-1)
  initialOutput :
    (initialConfiguration source normal.start input).tape .output =
      Tape.blankAt (-1)
  finalControl :
    (finalConfiguration source normal.start input output).control =
      .reverse normal.start
  finalWork :
    (finalConfiguration source normal.start input output).tape .work =
      Tape.ofWord input
  finalHistory :
    (finalConfiguration source normal.start input output).tape .history =
      Tape.blankAt (-1)
  finalOutput :
    (finalConfiguration source normal.start input output).tape .output =
      Tape.ofWord output
  initialWorkHead :
    ((initialConfiguration source normal.start input).tape .work).head = -1
  initialHistoryHead :
    ((initialConfiguration source normal.start input).tape .history).head = -1
  initialOutputHead :
    ((initialConfiguration source normal.start input).tape .output).head = -1
  finalWorkHead :
    ((finalConfiguration source normal.start input output).tape .work).head = -1
  finalHistoryHead :
    ((finalConfiguration source normal.start input output).tape .history).head = -1
  finalOutputHead :
    ((finalConfiguration source normal.start input output).tape .output).head = -1

/--
Central Bennett simulation theorem with source assumptions, accepted input,
exact endpoints, exact time, determinism, reversibility, and cleanup exposed in
its result type.
-/
theorem central_correctness [Fintype Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (enumerate : TableRuleId source.RuleId Symbol ≃
      Fin (Fintype.card (TableRuleId source.RuleId Symbol)))
    {sourceSteps : Nat} {input output : List Symbol}
    (haccept : normal.accepts input)
    (hcompute : Standard.ComputesIn source normal.start normal.finish
      sourceSteps input output) :
    SimulationCertificate normal enumerate sourceSteps input output := by
  have hsyntax :=
    machineWithEnumeration_syntacticallyReversible normal enumerate
  refine
    { accepted := haccept
      sourceRun := hcompute.1
      sourceHalted := hcompute.2
      tableSyntacticallyReversible := hsyntax
      tableRelationDeterministic :=
        QuadrupleMachine.DomainsDisjoint.stepRel_rightUnique hsyntax.1
      tableStepReversible :=
        QuadrupleMachine.RangesDisjoint.step_reversible hsyntax.2
      targetRun := runs_of_computesIn normal enumerate hcompute
      targetHalted := final_halted normal enumerate input output
      initialControl := by simp
      initialWork := by simp
      initialHistory := by simp
      initialOutput := by simp
      finalControl := by simp
      finalWork := by simp
      finalHistory := by simp
      finalOutput := by simp
      initialWorkHead := by simp
      initialHistoryHead := by simp
      initialOutputHead := by simp
      finalWorkHead := by simp
      finalHistoryHead := by simp
      finalOutputHead := by simp }

end Simulator
end Bennett.Turing
