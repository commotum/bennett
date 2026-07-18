import Bennett.Turing.Simulator.WorkResource
import Lean.Elab.Tactic.Omega

/-!
# Work-tape support preservation for the complete Bennett schedule

This module complements the exact head-walk theorems in `WorkResource`.
It first develops append laws for explicit execution traces, then compares the
nonblank work support of each two-rule compute/retrace pair with the
corresponding raw source step.
-/

namespace Bennett.Turing

namespace ExecutionTrace.WorkSupport

variable {State Symbol : Type*}

private theorem mem_foldl_union_nonblank
    (states : List State) (tape : State → Tape Symbol)
    (initial : Finset Int) (position : Int) :
    position ∈ states.foldl
        (fun positions state =>
          positions ∪ (tape state).nonblankPositions) initial ↔
      position ∈ initial ∨
        ∃ state ∈ states,
          position ∈ (tape state).nonblankPositions := by
  induction states generalizing initial with
  | nil => simp
  | cons state states ih =>
      rw [List.foldl_cons, ih]
      simp only [Finset.mem_union, List.mem_cons]
      aesop

theorem mem_everNonblankPositions_iff
    (tape : State → Tape Symbol) (trace : ExecutionTrace State)
    (position : Int) :
    position ∈ ExecutionTrace.everNonblankPositions tape trace ↔
      ∃ state ∈ trace.states,
        position ∈ (tape state).nonblankPositions := by
  unfold ExecutionTrace.everNonblankPositions
  rw [mem_foldl_union_nonblank]
  simp

end ExecutionTrace.WorkSupport

namespace Quadruple.WorkSupport

variable {Control TapeIndex : Type*} {Symbol : TapeIndex → Type*}

theorem mem_executionTrace_states_append_iff
    {first second : List (Quadruple Control TapeIndex Symbol)}
    {start middle : MultiConfiguration Control TapeIndex Symbol}
    (hfirst : Quadruple.Scheduled first start middle)
    (state : MultiConfiguration Control TapeIndex Symbol) :
    state ∈ (Quadruple.executionTrace (first ++ second) start).states ↔
      state ∈ (Quadruple.executionTrace first start).states ∨
      state ∈ (Quadruple.executionTrace second middle).states := by
  induction first generalizing start with
  | nil =>
      simp only [Quadruple.Scheduled] at hfirst
      subst middle
      constructor
      · exact Or.inr
      · rintro (hstart | hsecond)
        · have hstate : state = start := by
            change state ∈ [start] at hstart
            simpa using hstart
          subst state
          simp [Quadruple.executionTrace, ExecutionTrace.states]
        · exact hsecond
  | cons rule rules ih =>
      simp only [Quadruple.Scheduled] at hfirst
      simp only [List.cons_append, Quadruple.executionTrace_states_cons,
        List.mem_cons]
      rw [ih hfirst.2]
      tauto

theorem executionTrace_everNonblankPositions_append
    (index : TapeIndex)
    {first second : List (Quadruple Control TapeIndex Symbol)}
    {start middle : MultiConfiguration Control TapeIndex Symbol}
    (hfirst : Quadruple.Scheduled first start middle) :
    ExecutionTrace.everNonblankPositions
        (fun state => state.tape index)
        (Quadruple.executionTrace (first ++ second) start) =
      ExecutionTrace.everNonblankPositions
          (fun state => state.tape index)
          (Quadruple.executionTrace first start) ∪
        ExecutionTrace.everNonblankPositions
          (fun state => state.tape index)
          (Quadruple.executionTrace second middle) := by
  ext position
  simp only [Finset.mem_union]
  rw [ExecutionTrace.WorkSupport.mem_everNonblankPositions_iff,
    ExecutionTrace.WorkSupport.mem_everNonblankPositions_iff,
    ExecutionTrace.WorkSupport.mem_everNonblankPositions_iff]
  constructor
  · rintro ⟨state, hstate, hposition⟩
    rw [mem_executionTrace_states_append_iff hfirst] at hstate
    exact hstate.elim
      (fun h => Or.inl ⟨state, h, hposition⟩)
      (fun h => Or.inr ⟨state, h, hposition⟩)
  · rintro (⟨state, hstate, hposition⟩ | ⟨state, hstate, hposition⟩)
    · exact ⟨state,
        (mem_executionTrace_states_append_iff hfirst state).mpr (Or.inl hstate),
        hposition⟩
    · exact ⟨state,
        (mem_executionTrace_states_append_iff hfirst state).mpr (Or.inr hstate),
        hposition⟩

end Quadruple.WorkSupport

namespace Simulator.Resource.WorkSupport

variable {SourceControl Symbol : Type}

theorem source_execute_support
    (rule : Quintuple SourceControl Symbol)
    (before : Bennett.Turing.Configuration SourceControl Symbol) :
    (rule.execute before).tape.nonblankPositions =
      (before.tape.write rule.written).nonblankPositions := by
  rfl

theorem forwardPair_work_supports
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId)
    (before : Bennett.Turing.Configuration SourceControl Symbol)
    (history : List source.RuleId) :
    ((Quadruple.executionTrace (forwardPairRules source ruleId)
      (forwardConfiguration source { current := before, history := history })).states.map
        fun state => (state.tape .work).nonblankPositions) =
      [before.tape.nonblankPositions,
        ((source.rule ruleId).execute before).tape.nonblankPositions,
        ((source.rule ruleId).execute before).tape.nonblankPositions] := by
  simp only [forwardPairRules, Quadruple.executionTrace_states_cons,
    Quadruple.executionTrace_states_nil, List.map_cons, List.map_nil]
  rw [forwardRewriteRule_execute, forwardRecordRule_execute]
  simp only [forwardConfiguration, forwardMiddle]
  congr 1

theorem forwardPair_work_everNonblankPositions
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId)
    (before : Bennett.Turing.Configuration SourceControl Symbol)
    (history : List source.RuleId) :
    ExecutionTrace.everNonblankPositions
        (fun state : Simulator.Configuration source => state.tape .work)
        (Quadruple.executionTrace (forwardPairRules source ruleId)
          (forwardConfiguration source
            { current := before, history := history })) =
      ExecutionTrace.everNonblankPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source [ruleId] before) := by
  unfold ExecutionTrace.everNonblankPositions
  rw [← List.foldl_map, ← List.foldl_map,
    forwardPair_work_supports]
  simp [Machine.Resource.executionTrace, Machine.Resource.executeTail,
    ExecutionTrace.states, Finset.union_assoc]

theorem source_everNonblankPositions_cons
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId)
    (ruleIds : List source.RuleId)
    (before : Bennett.Turing.Configuration SourceControl Symbol) :
    ExecutionTrace.everNonblankPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source (ruleId :: ruleIds) before) =
      before.tape.nonblankPositions ∪
        ExecutionTrace.everNonblankPositions
          Bennett.Turing.Configuration.tape
          (Machine.Resource.executionTrace source ruleIds
            ((source.rule ruleId).execute before)) := by
  ext position
  simp only [Finset.mem_union]
  rw [ExecutionTrace.WorkSupport.mem_everNonblankPositions_iff,
    ExecutionTrace.WorkSupport.mem_everNonblankPositions_iff]
  simp only [Machine.Resource.executionTrace_states_cons, List.mem_cons]
  constructor <;> aesop

@[simp] theorem source_everNonblankPositions_nil
    (source : Machine SourceControl Symbol)
    (before : Bennett.Turing.Configuration SourceControl Symbol) :
    ExecutionTrace.everNonblankPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source [] before) =
      before.tape.nonblankPositions := by
  simp [ExecutionTrace.everNonblankPositions,
    Machine.Resource.executionTrace, Machine.Resource.executeTail,
    ExecutionTrace.states]

theorem forwardRules_work_everNonblankPositions
    (source : Machine SourceControl Symbol)
    {ruleIds : List source.RuleId}
    {before after : Bennett.Turing.Configuration SourceControl Symbol}
    (history : List source.RuleId)
    (hscheduled : Machine.Resource.Scheduled source ruleIds before after) :
    ExecutionTrace.everNonblankPositions
        (fun state : Simulator.Configuration source => state.tape .work)
        (Quadruple.executionTrace (forwardRules source ruleIds)
          (forwardConfiguration source
            { current := before, history := history })) =
      ExecutionTrace.everNonblankPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source ruleIds before) := by
  induction ruleIds generalizing before history with
  | nil =>
      simp only [Machine.Resource.Scheduled] at hscheduled
      subst after
      simp [forwardRules_nil, ExecutionTrace.everNonblankPositions,
        Quadruple.executionTrace, Machine.Resource.executionTrace,
        Quadruple.executeTail, Machine.Resource.executeTail,
        ExecutionTrace.states, forwardConfiguration]
      rfl
  | cons ruleId ruleIds ih =>
      simp only [Machine.Resource.Scheduled] at hscheduled
      let next := (source.rule ruleId).execute before
      have hpair := forwardPair_scheduled source ruleId
        { current := before, history := history } hscheduled.1
      rw [forwardRules_cons,
        Quadruple.WorkSupport.executionTrace_everNonblankPositions_append
          .work hpair,
        forwardPair_work_everNonblankPositions,
        ih (ruleId :: history) hscheduled.2,
        source_everNonblankPositions_cons source ruleId [] before,
        source_everNonblankPositions_cons source ruleId ruleIds before,
        source_everNonblankPositions_nil]
      have hnext : next.tape.nonblankPositions ⊆
          ExecutionTrace.everNonblankPositions
            Bennett.Turing.Configuration.tape
            (Machine.Resource.executionTrace source ruleIds next) := by
        apply ExecutionTrace.Resource.nonblankPositions_subset_everNonblankPositions
          Bennett.Turing.Configuration.tape
          (Machine.Resource.executionTrace source ruleIds next)
        simp [ExecutionTrace.states, Machine.Resource.executionTrace]
      change
        (before.tape.nonblankPositions ∪ next.tape.nonblankPositions) ∪
            ExecutionTrace.everNonblankPositions
              Bennett.Turing.Configuration.tape
              (Machine.Resource.executionTrace source ruleIds next) =
          before.tape.nonblankPositions ∪
            ExecutionTrace.everNonblankPositions
              Bennett.Turing.Configuration.tape
              (Machine.Resource.executionTrace source ruleIds next)
      ext position
      simp only [Finset.mem_union]
      aesop

theorem reversePair_work_supports
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId)
    (before : Bennett.Turing.Configuration SourceControl Symbol)
    (history : List source.RuleId) (copiedOutput : Tape Symbol)
    (hmatches : (source.rule ruleId).Matches before)
    (houtput : copiedOutput.read = .blank) :
    ((Quadruple.executionTrace (reversePairRules source ruleId)
      (reverseConfiguration source
        { current := (source.rule ruleId).execute before
          history := ruleId :: history }
        copiedOutput)).states.map
        fun state => (state.tape .work).nonblankPositions) =
      [((source.rule ruleId).execute before).tape.nonblankPositions,
        ((source.rule ruleId).execute before).tape.nonblankPositions,
        before.tape.nonblankPositions] := by
  simp only [reversePairRules, Quadruple.executionTrace_states_cons,
    Quadruple.executionTrace_states_nil, List.map_cons, List.map_nil]
  rw [reverseEraseRule_execute,
    reverseRestoreRule_execute source ruleId before history copiedOutput
      hmatches houtput]
  simp only [reverseConfiguration, reverseMiddle]
  congr 1

theorem reversePair_work_everNonblankPositions
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId)
    (before : Bennett.Turing.Configuration SourceControl Symbol)
    (history : List source.RuleId) (copiedOutput : Tape Symbol)
    (hmatches : (source.rule ruleId).Matches before)
    (houtput : copiedOutput.read = .blank) :
    ExecutionTrace.everNonblankPositions
        (fun state : Simulator.Configuration source => state.tape .work)
        (Quadruple.executionTrace (reversePairRules source ruleId)
          (reverseConfiguration source
            { current := (source.rule ruleId).execute before
              history := ruleId :: history }
            copiedOutput)) =
      ExecutionTrace.everNonblankPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source [ruleId] before) := by
  unfold ExecutionTrace.everNonblankPositions
  rw [← List.foldl_map, ← List.foldl_map,
    reversePair_work_supports source ruleId before history copiedOutput
      hmatches houtput]
  simp [Machine.Resource.executionTrace, Machine.Resource.executeTail,
    ExecutionTrace.states, Finset.union_comm]

theorem reverseRules_work_everNonblankPositions
    (source : Machine SourceControl Symbol)
    {ruleIds : List source.RuleId}
    {before after : Bennett.Turing.Configuration SourceControl Symbol}
    (history : List source.RuleId) (copiedOutput : Tape Symbol)
    (houtput : copiedOutput.read = .blank)
    (hscheduled : Machine.Resource.Scheduled source ruleIds before after) :
    ExecutionTrace.everNonblankPositions
        (fun state : Simulator.Configuration source => state.tape .work)
        (Quadruple.executionTrace (reverseRules source ruleIds)
          (reverseConfiguration source
            { current := after, history := ruleIds.reverse ++ history }
            copiedOutput)) =
      ExecutionTrace.everNonblankPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source ruleIds before) := by
  induction ruleIds generalizing before history with
  | nil =>
      simp only [Machine.Resource.Scheduled] at hscheduled
      subst after
      simp [reverseRules_nil, ExecutionTrace.everNonblankPositions,
        Quadruple.executionTrace, Machine.Resource.executionTrace,
        Quadruple.executeTail, Machine.Resource.executeTail,
        ExecutionTrace.states, reverseConfiguration]
      rfl
  | cons ruleId ruleIds ih =>
      simp only [Machine.Resource.Scheduled] at hscheduled
      let next := (source.rule ruleId).execute before
      have htail := reverseRules_scheduled_of_sourceScheduled source
        (ruleId :: history) copiedOutput houtput hscheduled.2
      have hpair := reversePair_scheduled source ruleId before history
        copiedOutput hscheduled.1 houtput
      rw [reverseRules_cons]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [Quadruple.WorkSupport.executionTrace_everNonblankPositions_append
          .work htail,
        ih (ruleId :: history) hscheduled.2,
        reversePair_work_everNonblankPositions source ruleId before history
          copiedOutput hscheduled.1 houtput,
        source_everNonblankPositions_cons source ruleId [] before,
        source_everNonblankPositions_cons source ruleId ruleIds before,
        source_everNonblankPositions_nil]
      have hnext : next.tape.nonblankPositions ⊆
          ExecutionTrace.everNonblankPositions
            Bennett.Turing.Configuration.tape
            (Machine.Resource.executionTrace source ruleIds next) := by
        apply ExecutionTrace.Resource.nonblankPositions_subset_everNonblankPositions
          Bennett.Turing.Configuration.tape
          (Machine.Resource.executionTrace source ruleIds next)
        simp [ExecutionTrace.states, Machine.Resource.executionTrace]
      change
        ExecutionTrace.everNonblankPositions
              Bennett.Turing.Configuration.tape
              (Machine.Resource.executionTrace source ruleIds next) ∪
            (before.tape.nonblankPositions ∪ next.tape.nonblankPositions) =
          before.tape.nonblankPositions ∪
            ExecutionTrace.everNonblankPositions
              Bennett.Turing.Configuration.tape
              (Machine.Resource.executionTrace source ruleIds next)
      ext position
      simp only [Finset.mem_union]
      aesop

/--
The complete compute--copy--retrace trace creates no new nonblank work cell.
Copying retains the final source work store, while compute and retrace expose
exactly the supports already present in the raw source execution trace.
-/
theorem fullTrace_work_everNonblankPositions
    [DecidableEq SourceControl] [DecidableEq Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (ruleIds : List source.RuleId) (input output : List Symbol)
    (hsource : Machine.Resource.Scheduled source ruleIds
      (Standard.config normal.start input)
      (Standard.config normal.finish output)) :
    ExecutionTrace.everNonblankPositions
        (fun state : Simulator.Configuration source => state.tape .work)
        (Quadruple.executionTrace (fullRules normal ruleIds output)
          (initialConfiguration source normal.start input)) =
      ExecutionTrace.everNonblankPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source ruleIds
          (Standard.config normal.start input)) := by
  obtain ⟨historyTail, hhistory⟩ :=
    Machine.Resource.exists_reverse_eq_exit_cons_of_scheduled normal hsource
  have hforward := forwardRules_scheduled_of_sourceScheduled source
    ([] : List source.RuleId) hsource
  have hcopy := Copy.scheduled_encode normal historyTail output
  have hreverse := reverseRules_scheduled_of_sourceScheduled source
    ([] : List source.RuleId) (Tape.ofWord output)
    (Tape.read_ofWord output) hsource
  rw [hhistory] at hforward hreverse
  simp only [List.append_nil] at hforward hreverse
  have hreverseEver := reverseRules_work_everNonblankPositions source
    ([] : List source.RuleId) (Tape.ofWord output)
    (Tape.read_ofWord output) hsource
  rw [hhistory] at hreverseEver
  simp only [List.append_nil] at hreverseEver
  have hcopyEver :
      ExecutionTrace.everNonblankPositions
          (fun state : Simulator.Configuration source => state.tape .work)
          (Quadruple.executionTrace (Copy.schedule normal output)
            (forwardConfiguration source
              { current := Standard.config normal.finish output
                history := normal.exitId :: historyTail })) =
        Finset.Ico 0 (output.length : Int) := by
    change ExecutionTrace.everNonblankPositions
        (fun state : Simulator.Configuration source => state.tape .work)
        (Copy.Resource.copyTrace normal
          (HistoryTape.encode (normal.exitId :: historyTail)) output) = _
    exact Copy.Resource.copyTrace_work_everNonblankPositions normal
      (HistoryTape.encode (normal.exitId :: historyTail)) output
  have hfinalSupport : Finset.Ico 0 (output.length : Int) ⊆
      ExecutionTrace.everNonblankPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source ruleIds
          (Standard.config normal.start input)) := by
    have htraceFinal :=
      Machine.Resource.executionTrace_final_of_scheduled source hsource
    rw [← Tape.ofWord_nonblankPositions output]
    change
      (Standard.config normal.finish output).tape.nonblankPositions ⊆ _
    rw [← htraceFinal]
    exact ExecutionTrace.Resource.final_nonblankPositions_subset_everNonblankPositions
      Bennett.Turing.Configuration.tape
      (Machine.Resource.executionTrace source ruleIds
        (Standard.config normal.start input))
  unfold fullRules
  simp only [initialConfiguration]
  rw [List.append_assoc]
  rw [Quadruple.WorkSupport.executionTrace_everNonblankPositions_append
      .work hforward,
    Quadruple.WorkSupport.executionTrace_everNonblankPositions_append
      .work hcopy,
    forwardRules_work_everNonblankPositions source [] hsource,
    hreverseEver, hcopyEver]
  ext position
  simp only [Finset.mem_union]
  aesop

/-- Exact work footprint: source footprint plus the copy delimiter sweep. -/
theorem fullTrace_work_footprintPositions
    [DecidableEq SourceControl] [DecidableEq Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (ruleIds : List source.RuleId) (input output : List Symbol)
    (hsource : Machine.Resource.Scheduled source ruleIds
      (Standard.config normal.start input)
      (Standard.config normal.finish output)) :
    ExecutionTrace.footprintPositions
        (fun state : Simulator.Configuration source => state.tape .work)
        (Quadruple.executionTrace (fullRules normal ruleIds output)
          (initialConfiguration source normal.start input)) =
      ExecutionTrace.footprintPositions
          Bennett.Turing.Configuration.tape
          (Machine.Resource.executionTrace source ruleIds
            (Standard.config normal.start input)) ∪
        Tape.delimiterTraversal output := by
  have hfinish : Machine.Resource.finalHead source (-1) ruleIds = -1 := by
    simpa using Machine.Resource.finalHead_eq_of_scheduled source hsource
  have hever := fullTrace_work_everNonblankPositions normal ruleIds input
    output hsource
  simp only [initialConfiguration] at hever
  unfold ExecutionTrace.footprintPositions
  simp only [initialConfiguration]
  rw [Simulator.Resource.fullTrace_work_visitedPositions normal
      (Standard.config normal.start input) ruleIds output hfinish,
    hever]
  ext position
  simp only [Finset.mem_union]
  tauto

/-- Standard endpoints force all output data cells into the source footprint. -/
theorem throughData_subset_sourceFootprint
    [DecidableEq SourceControl] [DecidableEq Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (ruleIds : List source.RuleId) (input output : List Symbol)
    (hsource : Machine.Resource.Scheduled source ruleIds
      (Standard.config normal.start input)
      (Standard.config normal.finish output)) :
    Tape.throughData output ⊆
      ExecutionTrace.footprintPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source ruleIds
          (Standard.config normal.start input)) := by
  let sourceTrace := Machine.Resource.executionTrace source ruleIds
    (Standard.config normal.start input)
  apply ExecutionTrace.Resource.throughData_subset_footprint
    Bennett.Turing.Configuration.tape sourceTrace output
  · rfl
  · have hfinal :=
      Machine.Resource.executionTrace_final_of_scheduled source hsource
    change sourceTrace.final = Standard.config normal.finish output at hfinal
    rw [hfinal]
    rfl

/-- Copying can add only the output's right delimiter to source work space. -/
theorem fullTrace_work_footprintPositions_eq_insert_right
    [DecidableEq SourceControl] [DecidableEq Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (ruleIds : List source.RuleId) (input output : List Symbol)
    (hsource : Machine.Resource.Scheduled source ruleIds
      (Standard.config normal.start input)
      (Standard.config normal.finish output)) :
    ExecutionTrace.footprintPositions
        (fun state : Simulator.Configuration source => state.tape .work)
        (Quadruple.executionTrace (fullRules normal ruleIds output)
          (initialConfiguration source normal.start input)) =
      insert (output.length : Int)
        (ExecutionTrace.footprintPositions
          Bennett.Turing.Configuration.tape
          (Machine.Resource.executionTrace source ruleIds
            (Standard.config normal.start input))) := by
  rw [fullTrace_work_footprintPositions normal ruleIds input output hsource,
    Tape.delimiterTraversal_eq_insert_right]
  have hthrough := throughData_subset_sourceFootprint normal ruleIds input
    output hsource
  ext position
  simp only [Finset.mem_union, Finset.mem_insert]
  constructor
  · rintro (hsourcePosition | hright | hdata)
    · exact Or.inr hsourcePosition
    · exact Or.inl hright
    · exact Or.inr (hthrough hdata)
  · rintro (hright | hsourcePosition)
    · exact Or.inr (Or.inl hright)
    · exact Or.inl hsourcePosition

/-- Exact unchanged-`s` case: the source footprint already contains the right delimiter. -/
theorem fullTrace_work_footprintCard_of_right_mem
    [DecidableEq SourceControl] [DecidableEq Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (ruleIds : List source.RuleId) (input output : List Symbol)
    (hsource : Machine.Resource.Scheduled source ruleIds
      (Standard.config normal.start input)
      (Standard.config normal.finish output))
    (hright : (output.length : Int) ∈
      ExecutionTrace.footprintPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source ruleIds
          (Standard.config normal.start input))) :
    (ExecutionTrace.footprintPositions
        (fun state : Simulator.Configuration source => state.tape .work)
        (Quadruple.executionTrace (fullRules normal ruleIds output)
          (initialConfiguration source normal.start input))).card =
      (ExecutionTrace.footprintPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source ruleIds
          (Standard.config normal.start input))).card := by
  rw [fullTrace_work_footprintPositions_eq_insert_right normal ruleIds input
    output hsource, Finset.insert_eq_of_mem hright]

/-- Exact corrected case: copying adds one previously absent right delimiter. -/
theorem fullTrace_work_footprintCard_of_right_not_mem
    [DecidableEq SourceControl] [DecidableEq Symbol]
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (ruleIds : List source.RuleId) (input output : List Symbol)
    (hsource : Machine.Resource.Scheduled source ruleIds
      (Standard.config normal.start input)
      (Standard.config normal.finish output))
    (hright : (output.length : Int) ∉
      ExecutionTrace.footprintPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source ruleIds
          (Standard.config normal.start input))) :
    (ExecutionTrace.footprintPositions
        (fun state : Simulator.Configuration source => state.tape .work)
        (Quadruple.executionTrace (fullRules normal ruleIds output)
          (initialConfiguration source normal.start input))).card =
      (ExecutionTrace.footprintPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source ruleIds
          (Standard.config normal.start input))).card + 1 := by
  rw [fullTrace_work_footprintPositions_eq_insert_right normal ruleIds input
    output hsource, Finset.card_insert_of_notMem hright]

end Simulator.Resource.WorkSupport

end Bennett.Turing
