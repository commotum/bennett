import Bennett.Transition.Run
import Bennett.Turing.Quadruple.Machine

/-!
# Explicit schedules of typed quadruples

An explicit schedule records which syntactic rule is intended at every step.
It is useful for proving exact traces before transporting them to the
least-index execution semantics of a finite, domain-disjoint rule table.
-/

namespace Bennett.Turing
namespace Quadruple

variable {Control TapeIndex : Type*} {Symbol : TapeIndex → Type*}

/-- Execute a displayed list of matching quadruples in order. -/
def Scheduled :
    List (Quadruple Control TapeIndex Symbol) →
      MultiConfiguration Control TapeIndex Symbol →
      MultiConfiguration Control TapeIndex Symbol → Prop
  | [], before, after => before = after
  | rule :: rules, before, after =>
      rule.Matches before ∧ Scheduled rules (rule.execute before) after

theorem Scheduled.append
    {first second : List (Quadruple Control TapeIndex Symbol)}
    {start middle finish : MultiConfiguration Control TapeIndex Symbol}
    (hfirst : Scheduled first start middle)
    (hsecond : Scheduled second middle finish) :
    Scheduled (first ++ second) start finish := by
  induction first generalizing start with
  | nil =>
      simp only [Scheduled] at hfirst
      subst middle
      exact hsecond
  | cons rule rules ih =>
      simp only [Scheduled] at hfirst ⊢
      exact ⟨hfirst.1, ih hfirst.2⟩

/-- Reverse rule order and formally invert every displayed quadruple. -/
def inverseSchedule
    (rules : List (Quadruple Control TapeIndex Symbol)) :
    List (Quadruple Control TapeIndex Symbol) :=
  rules.reverse.map Quadruple.inverse

@[simp] theorem inverseSchedule_length
    (rules : List (Quadruple Control TapeIndex Symbol)) :
    (inverseSchedule rules).length = rules.length := by
  simp [inverseSchedule]

/-- The formal inverse schedule restores the exact starting configuration. -/
theorem Scheduled.inverse
    {rules : List (Quadruple Control TapeIndex Symbol)}
    {before after : MultiConfiguration Control TapeIndex Symbol}
    (hrun : Scheduled rules before after) :
    Scheduled (inverseSchedule rules) after before := by
  induction rules generalizing before with
  | nil =>
      simp only [Scheduled] at hrun
      subst after
      simp [inverseSchedule, Scheduled]
  | cons rule rules ih =>
      simp only [Scheduled] at hrun
      have htail := ih hrun.2
      have hone : Scheduled [rule.inverse] (rule.execute before) before := by
        simp only [Scheduled]
        exact ⟨Quadruple.inverse_matches_execute hrun.1,
          Quadruple.inverse_execute hrun.1⟩
      simpa [inverseSchedule] using Scheduled.append htail hone

/--
A scheduled proof becomes an executable finite-machine run once every displayed
rule belongs to a domain-disjoint table.
-/
theorem Scheduled.toRuns
    [DecidableEq Control] [Fintype TapeIndex]
    [∀ index, DecidableEq (Symbol index)]
    {machine : QuadrupleMachine Control TapeIndex Symbol}
    (hdomains : machine.DomainsDisjoint)
    {rules : List (Quadruple Control TapeIndex Symbol)}
    {start finish : MultiConfiguration Control TapeIndex Symbol}
    (hcontained : ∀ rule, rule ∈ rules →
      ∃ index : machine.RuleId, machine.rule index = rule)
    (hscheduled : Scheduled rules start finish) :
    machine.step.Runs rules.length start finish := by
  induction rules generalizing start with
  | nil =>
      simp only [Scheduled] at hscheduled
      subst finish
      exact PartialStep.runs_refl machine.step start
  | cons rule rules ih =>
      simp only [Scheduled] at hscheduled
      obtain ⟨index, hrule⟩ := hcontained rule (by simp)
      have hrel : machine.StepRel start (rule.execute start) := by
        refine ⟨index, ?_, ?_⟩
        · simpa [hrule] using hscheduled.1
        · simp [hrule]
      have hstep : machine.step start = some (rule.execute start) :=
        (hdomains.step_eq_some_iff start (rule.execute start)).2 hrel
      apply (PartialStep.runs_succ_iff machine.step rules.length
        start finish).2
      refine ⟨rule.execute start, hstep, ?_⟩
      apply ih
      · intro tailRule hmem
        exact hcontained tailRule (by simp [hmem])
      · exact hscheduled.2

end Quadruple
end Bennett.Turing
