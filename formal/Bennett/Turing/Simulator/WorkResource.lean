import Bennett.Turing.Simulator.Resource
import Bennett.Turing.Simulator.Correctness
import Lean.Elab.Tactic.Omega

/-!
# Work/output head resources for the complete three-tape simulator

This module exposes the chronological source rule IDs underlying a standard
computation and constructs the matching compute--copy--retrace schedule from
those same IDs.  Its concrete target trace has work-head visited set exactly
the source trace's visited set union the output delimiter traversal; the output
head visits exactly that delimiter traversal.

The scalar results deliberately distinguish raw head visits from a tape
footprint.  Relative to raw source visits, copying can add every output cell
that the source never scanned.  Relative to the source footprint, it adds at
most the right delimiter, so the checked bound is explicitly named as a target
*head-visit* bound against a source *footprint*.

This module does not claim equality between the complete target work tape's
`everNonblankPositions` and the source trace's `everNonblankPositions`.  That
requires a separate per-state support-correspondence proof across both the
forward and reverse appended execution traces.  Consequently, no theorem here
silently promotes the head-visit bound to a total work-footprint theorem.
-/

namespace Bennett.Turing

namespace Tape

variable {Symbol : Type*}

/-- Left delimiter and data-cell positions, excluding the right delimiter. -/
def throughData (word : List Symbol) : Finset Int :=
  Finset.Ico (-1) (word.length : Int)

theorem delimiterTraversal_eq_insert_right (word : List Symbol) :
    delimiterTraversal word =
      insert (word.length : Int) (throughData word) := by
  ext position
  simp only [delimiterTraversal, throughData, Finset.mem_Icc,
    Finset.mem_insert, Finset.mem_Ico]
  omega

@[simp] theorem throughData_card (word : List Symbol) :
    (throughData word).card = word.length + 1 := by
  rw [throughData, Int.card_Ico]
  omega

end Tape

namespace ExecutionTrace.Resource

variable {State Symbol : Type*}

theorem final_mem_states (trace : ExecutionTrace State) :
    trace.final ∈ trace.states := by
  cases trace with
  | mk initial subsequent =>
      simp only [ExecutionTrace.final, ExecutionTrace.states]
      induction subsequent generalizing initial with
      | nil => simp
      | cons next rest ih =>
          simp only [List.foldl_cons]
          right
          exact ih next

private theorem mem_foldl_union_iff
    (positions : State → Finset Int) (candidate : Int)
    (states : List State) (initial : Finset Int) :
    candidate ∈ states.foldl
        (fun accumulated state => accumulated ∪ positions state) initial ↔
      candidate ∈ initial ∨
        ∃ state ∈ states, candidate ∈ positions state := by
  induction states generalizing initial with
  | nil => simp
  | cons state states ih =>
      rw [List.foldl_cons, ih]
      simp only [Finset.mem_union, List.mem_cons]
      aesop

theorem nonblankPositions_subset_everNonblankPositions
    (tape : State → Tape Symbol) (trace : ExecutionTrace State)
    {state : State} (hstate : state ∈ trace.states) :
    (tape state).nonblankPositions ⊆
      ExecutionTrace.everNonblankPositions tape trace := by
  intro position hposition
  unfold ExecutionTrace.everNonblankPositions
  rw [mem_foldl_union_iff]
  exact Or.inr ⟨state, hstate, hposition⟩

theorem final_nonblankPositions_subset_everNonblankPositions
    (tape : State → Tape Symbol) (trace : ExecutionTrace State) :
    (tape trace.final).nonblankPositions ⊆
      ExecutionTrace.everNonblankPositions tape trace :=
  nonblankPositions_subset_everNonblankPositions tape trace
    (final_mem_states trace)

theorem initial_head_mem_visitedPositions
    (tape : State → Tape Symbol) (trace : ExecutionTrace State) :
    (tape trace.initial).head ∈
      ExecutionTrace.visitedPositions tape trace := by
  simp [ExecutionTrace.visitedPositions, ExecutionTrace.states]

/-- A trace beginning on the left delimiter and ending in a standard word has
    the left delimiter and all final data cells in its footprint. -/
theorem throughData_subset_footprint
    (tape : State → Tape Symbol) (trace : ExecutionTrace State)
    (output : List Symbol)
    (hinitial : (tape trace.initial).head = -1)
    (hfinal : tape trace.final = Tape.ofWord output) :
    Tape.throughData output ⊆
      ExecutionTrace.footprintPositions tape trace := by
  intro position hposition
  rw [Tape.throughData] at hposition
  simp only [Finset.mem_Ico] at hposition
  unfold ExecutionTrace.footprintPositions
  rw [Finset.mem_union]
  by_cases hleft : position = -1
  · left
    rw [hleft, ← hinitial]
    exact initial_head_mem_visitedPositions tape trace
  · right
    apply final_nonblankPositions_subset_everNonblankPositions tape trace
    rw [hfinal, Tape.ofWord_nonblankPositions]
    simp only [Finset.mem_Ico]
    omega

end ExecutionTrace.Resource

namespace Quadruple.Resource

variable {Control TapeIndex : Type*} {Symbol : TapeIndex → Type*}

/-- The head displacement made by one typed tape action. -/
def actionOffset : Action α → Int
  | .rewrite _ _ => 0
  | .move direction => direction.offset

/-- The head displacement made by a rule on a chosen tape. -/
def ruleOffset (index : TapeIndex)
    (rule : Quadruple Control TapeIndex Symbol) : Int :=
  actionOffset (rule.action index)

/-- Head positions before, between, and after a displayed rule list. -/
def headWalk (index : TapeIndex) :
    Int → List (Quadruple Control TapeIndex Symbol) → List Int
  | position, [] => [position]
  | position, rule :: rules =>
      position :: headWalk index (position + ruleOffset index rule) rules

/-- Final head position after a displayed rule list. -/
def finalHead (index : TapeIndex) :
    Int → List (Quadruple Control TapeIndex Symbol) → Int
  | position, [] => position
  | position, rule :: rules =>
      finalHead index (position + ruleOffset index rule) rules

/-- The finite set of positions in a displayed head walk. -/
def headPositions (index : TapeIndex) (position : Int)
    (rules : List (Quadruple Control TapeIndex Symbol)) : Finset Int :=
  (headWalk index position rules).toFinset

@[simp] theorem headWalk_nil (index : TapeIndex) (position : Int) :
    headWalk (Control := Control) (Symbol := Symbol) index position [] =
      [position] := rfl

@[simp] theorem headWalk_cons (index : TapeIndex) (position : Int)
    (rule : Quadruple Control TapeIndex Symbol)
    (rules : List (Quadruple Control TapeIndex Symbol)) :
    headWalk index position (rule :: rules) =
      position :: headWalk index (position + ruleOffset index rule) rules := rfl

@[simp] theorem finalHead_nil (index : TapeIndex) (position : Int) :
    finalHead (Control := Control) (Symbol := Symbol) index position [] =
      position := rfl

@[simp] theorem finalHead_cons (index : TapeIndex) (position : Int)
    (rule : Quadruple Control TapeIndex Symbol)
    (rules : List (Quadruple Control TapeIndex Symbol)) :
    finalHead index position (rule :: rules) =
      finalHead index (position + ruleOffset index rule) rules := rfl

@[simp] theorem headPositions_nil (index : TapeIndex) (position : Int) :
    headPositions (Control := Control) (Symbol := Symbol) index position [] =
      {position} := by
  simp [headPositions]

@[simp] theorem headPositions_cons (index : TapeIndex) (position : Int)
    (rule : Quadruple Control TapeIndex Symbol)
    (rules : List (Quadruple Control TapeIndex Symbol)) :
    headPositions index position (rule :: rules) =
      insert position
        (headPositions index (position + ruleOffset index rule) rules) := by
  simp [headPositions]

theorem start_mem_headPositions (index : TapeIndex) (position : Int)
    (rules : List (Quadruple Control TapeIndex Symbol)) :
    position ∈ headPositions index position rules := by
  cases rules <;> simp

theorem finalHead_append (index : TapeIndex) (position : Int)
    (first second : List (Quadruple Control TapeIndex Symbol)) :
    finalHead index position (first ++ second) =
      finalHead index (finalHead index position first) second := by
  induction first generalizing position with
  | nil => rfl
  | cons rule rules ih => simp [ih]

theorem headPositions_append (index : TapeIndex) (position : Int)
    (first second : List (Quadruple Control TapeIndex Symbol)) :
    headPositions index position (first ++ second) =
      headPositions index position first ∪
        headPositions index (finalHead index position first) second := by
  induction first generalizing position with
  | nil =>
      ext candidate
      simp [start_mem_headPositions]
  | cons rule rules ih =>
      simp only [List.cons_append, headPositions_cons, finalHead_cons, ih,
        Finset.insert_union]

theorem execute_head (index : TapeIndex)
    (rule : Quadruple Control TapeIndex Symbol)
    (before : MultiConfiguration Control TapeIndex Symbol) :
    ((rule.execute before).tape index).head =
      (before.tape index).head + ruleOffset index rule := by
  rw [Quadruple.execute_tape]
  cases action : rule.action index with
  | rewrite scanned written =>
      simp [ruleOffset, actionOffset, action]
  | move direction =>
      simp [ruleOffset, actionOffset, action]

theorem executionTrace_heads (index : TapeIndex)
    (rules : List (Quadruple Control TapeIndex Symbol))
    (start : MultiConfiguration Control TapeIndex Symbol) :
    ((Quadruple.executionTrace rules start).states.map
      (fun state => (state.tape index).head)) =
      headWalk index (start.tape index).head rules := by
  induction rules generalizing start with
  | nil => rfl
  | cons rule rules ih =>
      simp only [Quadruple.executionTrace_states_cons, List.map_cons,
        headWalk_cons]
      congr 1
      rw [ih, execute_head]

theorem executionTrace_visitedPositions (index : TapeIndex)
    (rules : List (Quadruple Control TapeIndex Symbol))
    (start : MultiConfiguration Control TapeIndex Symbol) :
    ExecutionTrace.visitedPositions (fun state => state.tape index)
        (Quadruple.executionTrace rules start) =
      headPositions index (start.tape index).head rules := by
  unfold ExecutionTrace.visitedPositions headPositions
  rw [executionTrace_heads]

end Quadruple.Resource

namespace Machine.Resource

variable {Control Symbol : Type*}

/-- Head positions of the raw source-rule execution named by intrinsic IDs. -/
def headWalk (source : Machine Control Symbol) :
    Int → List source.RuleId → List Int
  | position, [] => [position]
  | position, ruleId :: ruleIds =>
      position :: headWalk source
        (position + (source.rule ruleId).move.offset) ruleIds

/-- Final head position of the raw source-rule execution. -/
def finalHead (source : Machine Control Symbol) :
    Int → List source.RuleId → Int
  | position, [] => position
  | position, ruleId :: ruleIds =>
      finalHead source (position + (source.rule ruleId).move.offset) ruleIds

/-- Distinct source head positions of a rule-ID execution. -/
def headPositions (source : Machine Control Symbol) (position : Int)
    (ruleIds : List source.RuleId) : Finset Int :=
  (headWalk source position ruleIds).toFinset

@[simp] theorem headWalk_nil (source : Machine Control Symbol)
    (position : Int) : headWalk source position [] = [position] := rfl

@[simp] theorem headWalk_cons (source : Machine Control Symbol)
    (position : Int) (ruleId : source.RuleId)
    (ruleIds : List source.RuleId) :
    headWalk source position (ruleId :: ruleIds) =
      position :: headWalk source
        (position + (source.rule ruleId).move.offset) ruleIds := rfl

@[simp] theorem finalHead_nil (source : Machine Control Symbol)
    (position : Int) : finalHead source position [] = position := rfl

@[simp] theorem finalHead_cons (source : Machine Control Symbol)
    (position : Int) (ruleId : source.RuleId)
    (ruleIds : List source.RuleId) :
    finalHead source position (ruleId :: ruleIds) =
      finalHead source
        (position + (source.rule ruleId).move.offset) ruleIds := rfl

@[simp] theorem headPositions_nil (source : Machine Control Symbol)
    (position : Int) : headPositions source position [] = {position} := by
  simp [headPositions]

@[simp] theorem headPositions_cons (source : Machine Control Symbol)
    (position : Int) (ruleId : source.RuleId)
    (ruleIds : List source.RuleId) :
    headPositions source position (ruleId :: ruleIds) =
      insert position (headPositions source
        (position + (source.rule ruleId).move.offset) ruleIds) := by
  simp [headPositions]

theorem start_mem_headPositions (source : Machine Control Symbol)
    (position : Int) (ruleIds : List source.RuleId) :
    position ∈ headPositions source position ruleIds := by
  cases ruleIds <;> simp

/-- Raw source configurations produced by a named rule list. -/
def executeTail (source : Machine Control Symbol) :
    List source.RuleId → Configuration Control Symbol →
      List (Configuration Control Symbol)
  | [], _ => []
  | ruleId :: ruleIds, before =>
      let after := (source.rule ruleId).execute before
      after :: executeTail source ruleIds after

/-- Nonempty raw source trace generated by intrinsic rule IDs. -/
def executionTrace (source : Machine Control Symbol)
    (ruleIds : List source.RuleId) (start : Configuration Control Symbol) :
    ExecutionTrace (Configuration Control Symbol) :=
  ⟨start, executeTail source ruleIds start⟩

@[simp] theorem executionTrace_states_nil (source : Machine Control Symbol)
    (start : Configuration Control Symbol) :
    (executionTrace source [] start).states = [start] := rfl

@[simp] theorem executionTrace_states_cons (source : Machine Control Symbol)
    (ruleId : source.RuleId) (ruleIds : List source.RuleId)
    (start : Configuration Control Symbol) :
    (executionTrace source (ruleId :: ruleIds) start).states =
      start :: (executionTrace source ruleIds
        ((source.rule ruleId).execute start)).states := rfl

theorem executionTrace_heads (source : Machine Control Symbol)
    (ruleIds : List source.RuleId) (start : Configuration Control Symbol) :
    ((executionTrace source ruleIds start).states.map
      (fun state => state.tape.head)) =
      headWalk source start.tape.head ruleIds := by
  induction ruleIds generalizing start with
  | nil => rfl
  | cons ruleId ruleIds ih =>
      simp only [executionTrace_states_cons, List.map_cons, headWalk_cons]
      congr 1
      rw [ih, Quintuple.execute_head]

theorem executionTrace_visitedPositions (source : Machine Control Symbol)
    (ruleIds : List source.RuleId) (start : Configuration Control Symbol) :
    ExecutionTrace.visitedPositions Configuration.tape
        (executionTrace source ruleIds start) =
      headPositions source start.tape.head ruleIds := by
  unfold ExecutionTrace.visitedPositions headPositions
  rw [executionTrace_heads]

/-- Every named rule matches the state reached by its predecessors. -/
def Scheduled (source : Machine Control Symbol) :
    List source.RuleId → Configuration Control Symbol →
      Configuration Control Symbol → Prop
  | [], before, after => before = after
  | ruleId :: ruleIds, before, after =>
      (source.rule ruleId).Matches before ∧
        Scheduled source ruleIds ((source.rule ruleId).execute before) after

theorem finalHead_eq_of_scheduled (source : Machine Control Symbol)
    {ruleIds : List source.RuleId}
    {before after : Configuration Control Symbol}
    (hscheduled : Scheduled source ruleIds before after) :
    finalHead source before.tape.head ruleIds = after.tape.head := by
  induction ruleIds generalizing before with
  | nil =>
      simp only [Scheduled] at hscheduled
      subst after
      rfl
  | cons ruleId ruleIds ih =>
      simp only [Scheduled] at hscheduled
      rw [finalHead_cons]
      have htail := ih hscheduled.2
      simpa using htail

theorem executionTrace_final_of_scheduled (source : Machine Control Symbol)
    {ruleIds : List source.RuleId}
    {before after : Configuration Control Symbol}
    (hscheduled : Scheduled source ruleIds before after) :
    (executionTrace source ruleIds before).final = after := by
  induction ruleIds generalizing before with
  | nil =>
      simp only [Scheduled] at hscheduled
      subst after
      rfl
  | cons ruleId ruleIds ih =>
      simp only [Scheduled] at hscheduled
      change (ExecutionTrace.prepend before
        (executionTrace source ruleIds
          ((source.rule ruleId).execute before))).final = after
      rw [ExecutionTrace.final_prepend]
      exact ih hscheduled.2

theorem lastRule_target_of_scheduled (source : Machine Control Symbol)
    {ruleIds : List source.RuleId}
    {before after : Configuration Control Symbol} {lastId : source.RuleId}
    (hscheduled : Scheduled source ruleIds before after)
    (hlast : ruleIds.getLast? = some lastId) :
    (source.rule lastId).target = after.control := by
  induction ruleIds generalizing before with
  | nil => simp at hlast
  | cons ruleId ruleIds ih =>
      simp only [Scheduled] at hscheduled
      cases ruleIds with
      | nil =>
          simp at hlast
          subst lastId
          simp only [Scheduled] at hscheduled
          have hcontrol := congrArg Configuration.control hscheduled.2
          simpa using hcontrol
      | cons next rest =>
          apply ih hscheduled.2
          simpa using hlast

theorem exists_reverse_eq_exit_cons_of_scheduled
    [DecidableEq Control] [DecidableEq Symbol]
    {source : Machine Control Symbol}
    (normal : Standard.BennettNormalForm source)
    {ruleIds : List source.RuleId} {input output : List Symbol}
    (hscheduled : Scheduled source ruleIds
      (Standard.config normal.start input)
      (Standard.config normal.finish output)) :
    ∃ historyTail, ruleIds.reverse = normal.exitId :: historyTail := by
  have hnonempty : ruleIds ≠ [] := by
    intro hnil
    subst ruleIds
    simp only [Scheduled] at hscheduled
    have hcontrol := congrArg Configuration.control hscheduled
    exact normal.start_ne_finish (by simpa using hcontrol)
  let lastId := ruleIds.getLast hnonempty
  have hlast : ruleIds.getLast? = some lastId :=
    List.getLast?_eq_some_getLast hnonempty
  have htarget := lastRule_target_of_scheduled source hscheduled hlast
  have hid : lastId = normal.exitId :=
    normal.exit_only_rule_to_finish lastId (by simpa using htarget)
  obtain ⟨initialIds, hids⟩ := List.getLast?_eq_some_iff.mp hlast
  refine ⟨initialIds.reverse, ?_⟩
  rw [hids, hid]
  simp

theorem Scheduled.toRuns [DecidableEq Control] [DecidableEq Symbol]
    {source : Machine Control Symbol}
    (hdet : source.SyntacticallyDeterministic)
    {ruleIds : List source.RuleId}
    {before after : Configuration Control Symbol}
    (hscheduled : Scheduled source ruleIds before after) :
    source.step.Runs ruleIds.length before after := by
  induction ruleIds generalizing before with
  | nil =>
      simp only [Scheduled] at hscheduled
      subst after
      exact PartialStep.runs_refl source.step before
  | cons ruleId ruleIds ih =>
      simp only [Scheduled] at hscheduled
      apply (PartialStep.runs_succ_iff source.step ruleIds.length
        before after).2
      refine ⟨(source.rule ruleId).execute before, ?_, ih hscheduled.2⟩
      exact (hdet.step_eq_some_iff before
        ((source.rule ruleId).execute before)).2
        ⟨ruleId, hscheduled.1, rfl⟩

theorem exists_scheduled_of_runs [DecidableEq Control] [DecidableEq Symbol]
    (source : Machine Control Symbol)
    {n : Nat} {before after : Configuration Control Symbol}
    (hrun : source.step.Runs n before after) :
    ∃ ruleIds : List source.RuleId,
      ruleIds.length = n ∧ Scheduled source ruleIds before after := by
  induction n generalizing before with
  | zero =>
      have hbefore :=
        (PartialStep.runs_zero_iff source.step before after).mp hrun
      subst after
      exact ⟨[], rfl, rfl⟩
  | succ n ih =>
      obtain ⟨next, hstep, htail⟩ :=
        (PartialStep.runs_succ_iff source.step n before after).mp hrun
      unfold Machine.step at hstep
      obtain ⟨ruleId, hselect, hnext⟩ := Option.map_eq_some_iff.mp hstep
      have hmatches := source.select_matches before hselect
      subst next
      obtain ⟨ruleIds, hlength, hscheduled⟩ := ih htail
      exact ⟨ruleId :: ruleIds, by simp [hlength], hmatches, hscheduled⟩

end Machine.Resource

namespace Simulator.Resource

open Quadruple.Resource

variable {SourceControl Symbol : Type}
  [DecidableEq SourceControl] [DecidableEq Symbol]

/-- Forward physical rules generated by chronological source rule IDs. -/
def forwardRules (source : Machine SourceControl Symbol)
    (ruleIds : List source.RuleId) : List (Simulator.Rule source) :=
  ruleIds.flatMap (forwardPairRules source)

/-- Reverse physical rules generated in reverse chronological order. -/
def reverseRules (source : Machine SourceControl Symbol)
    (ruleIds : List source.RuleId) : List (Simulator.Rule source) :=
  ruleIds.reverse.flatMap (reversePairRules source)

/-- Complete compute–copy–retrace displayed rule list. -/
def fullRules {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (ruleIds : List source.RuleId) (output : List Symbol) :
    List (Simulator.Rule source) :=
  forwardRules source ruleIds ++ Copy.schedule normal output ++
    reverseRules source ruleIds

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem forwardRules_nil (source : Machine SourceControl Symbol) :
    forwardRules source [] = [] := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem forwardRules_cons (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId) (ruleIds : List source.RuleId) :
    forwardRules source (ruleId :: ruleIds) =
      forwardPairRules source ruleId ++ forwardRules source ruleIds := by
  simp [forwardRules]

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem reverseRules_nil (source : Machine SourceControl Symbol) :
    reverseRules source [] = [] := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
theorem reverseRules_cons (source : Machine SourceControl Symbol)
    (ruleId : source.RuleId) (ruleIds : List source.RuleId) :
    reverseRules source (ruleId :: ruleIds) =
      reverseRules source ruleIds ++ reversePairRules source ruleId := by
  simp [reverseRules, List.flatMap_append]

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem forwardRules_length (source : Machine SourceControl Symbol)
    (ruleIds : List source.RuleId) :
    (forwardRules source ruleIds).length = 2 * ruleIds.length := by
  induction ruleIds with
  | nil => rfl
  | cons ruleId ruleIds ih =>
      simp [forwardRules_cons, forwardPairRules, ih]
      omega

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem reverseRules_length (source : Machine SourceControl Symbol)
    (ruleIds : List source.RuleId) :
    (reverseRules source ruleIds).length = 2 * ruleIds.length := by
  induction ruleIds with
  | nil => rfl
  | cons ruleId ruleIds ih =>
      simp [reverseRules_cons, reversePairRules, ih]
      omega

/-- The matching explicit list has the same exact time formula as the semantic
    correctness theorem: `4v + 4λ + 5`. -/
@[simp] theorem fullRules_length
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (ruleIds : List source.RuleId) (output : List Symbol) :
    (fullRules normal ruleIds output).length =
      4 * ruleIds.length + 4 * output.length + 5 := by
  simp [fullRules]
  omega

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
/-- A matching source rule-ID schedule lifts to the explicit forward rule list,
    with chronological IDs accumulated newest-first on history. -/
theorem forwardRules_scheduled_of_sourceScheduled
    (source : Machine SourceControl Symbol)
    {ruleIds : List source.RuleId}
    {before after : Bennett.Turing.Configuration SourceControl Symbol}
    (history : List source.RuleId)
    (hscheduled : Machine.Resource.Scheduled source ruleIds before after) :
    Quadruple.Scheduled (forwardRules source ruleIds)
      (forwardConfiguration source { current := before, history := history })
      (forwardConfiguration source
        { current := after, history := ruleIds.reverse ++ history }) := by
  induction ruleIds generalizing before history with
  | nil =>
      simp only [Machine.Resource.Scheduled] at hscheduled
      subst after
      rfl
  | cons ruleId ruleIds ih =>
      simp only [Machine.Resource.Scheduled] at hscheduled
      have hfirst := forwardPair_scheduled source ruleId
        { current := before, history := history } hscheduled.1
      have htail := ih (ruleId :: history) hscheduled.2
      simpa [forwardRules_cons, List.reverse_cons, List.append_assoc] using
        Quadruple.Scheduled.append hfirst htail

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
/-- The reverse list exactly retraces a matching source rule-ID schedule. -/
theorem reverseRules_scheduled_of_sourceScheduled
    (source : Machine SourceControl Symbol)
    {ruleIds : List source.RuleId}
    {before after : Bennett.Turing.Configuration SourceControl Symbol}
    (history : List source.RuleId) (copiedOutput : Tape Symbol)
    (houtput : copiedOutput.read = .blank)
    (hscheduled : Machine.Resource.Scheduled source ruleIds before after) :
    Quadruple.Scheduled (reverseRules source ruleIds)
      (reverseConfiguration source
        { current := after, history := ruleIds.reverse ++ history }
        copiedOutput)
      (reverseConfiguration source
        { current := before, history := history } copiedOutput) := by
  induction ruleIds generalizing before history with
  | nil =>
      simp only [Machine.Resource.Scheduled] at hscheduled
      subst after
      rfl
  | cons ruleId ruleIds ih =>
      simp only [Machine.Resource.Scheduled] at hscheduled
      have htail := ih (ruleId :: history) hscheduled.2
      have hlast := reversePair_scheduled source ruleId before history
        copiedOutput hscheduled.1 houtput
      simpa [reverseRules_cons, List.reverse_cons, List.append_assoc] using
        Quadruple.Scheduled.append htail hlast

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
/-- Every generated forward rule belongs to the simulator's forward family. -/
theorem onlyForwardRules_forwardRules
    (source : Machine SourceControl Symbol) (ruleIds : List source.RuleId) :
    OnlyForwardRules source (forwardRules source ruleIds) := by
  induction ruleIds with
  | nil => simp [forwardRules, OnlyForwardRules]
  | cons ruleId ruleIds ih =>
      rw [forwardRules_cons]
      exact OnlyForwardRules.append source
        (onlyForwardRules_pair source ruleId) ih

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
/-- Every generated reverse rule belongs to the simulator's reverse family. -/
theorem onlyReverseRules_reverseRules
    (source : Machine SourceControl Symbol) (ruleIds : List source.RuleId) :
    OnlyReverseRules source (reverseRules source ruleIds) := by
  induction ruleIds with
  | nil => simp [reverseRules, OnlyReverseRules]
  | cons ruleId ruleIds ih =>
      rw [reverseRules_cons]
      exact OnlyReverseRules.append source ih
        (onlyReverseRules_pair source ruleId)

/-- Every rule of the generated complete schedule occurs in Table 1. -/
theorem onlyTableRules_fullRules
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (ruleIds : List source.RuleId) (output : List Symbol) :
    OnlyTableRules normal (fullRules normal ruleIds output) := by
  exact OnlyTableRules.append normal
    (OnlyTableRules.append normal
      (onlyTableRules_of_forward normal
        (onlyForwardRules_forwardRules source ruleIds))
      (onlyTableRules_copy normal output))
    (onlyTableRules_of_reverse normal
      (onlyReverseRules_reverseRules source ruleIds))

/-- The exact `fullRules` list is a genuinely matching constructor schedule,
    not merely a raw displayed-rule execution. -/
theorem fullRules_scheduled_of_sourceScheduled
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    {ruleIds : List source.RuleId} {input output : List Symbol}
    (hsource : Machine.Resource.Scheduled source ruleIds
      (Standard.config normal.start input)
      (Standard.config normal.finish output)) :
    Quadruple.Scheduled (fullRules normal ruleIds output)
      (initialConfiguration source normal.start input)
      (finalConfiguration source normal.start input output) := by
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
  simpa [fullRules, initialConfiguration, finalConfiguration] using
    Quadruple.Scheduled.append
      (Quadruple.Scheduled.append hforward hcopy) hreverse

/-- A standard exact computation exposes chronological source IDs and the
    exact matching complete simulator schedule built from those same IDs. -/
theorem exists_fullRules_scheduled_of_computesIn
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    {sourceSteps : Nat} {input output : List Symbol}
    (hcompute : Standard.ComputesIn source normal.start normal.finish
      sourceSteps input output) :
    ∃ ruleIds : List source.RuleId,
      ruleIds.length = sourceSteps ∧
      Machine.Resource.Scheduled source ruleIds
        (Standard.config normal.start input)
        (Standard.config normal.finish output) ∧
      Quadruple.Scheduled (fullRules normal ruleIds output)
        (initialConfiguration source normal.start input)
        (finalConfiguration source normal.start input output) ∧
      OnlyTableRules normal (fullRules normal ruleIds output) := by
  obtain ⟨hrun, _⟩ := hcompute
  obtain ⟨ruleIds, hlength, hsource⟩ :=
    Machine.Resource.exists_scheduled_of_runs source hrun
  exact ⟨ruleIds, hlength, hsource,
    fullRules_scheduled_of_sourceScheduled normal hsource,
    onlyTableRules_fullRules normal ruleIds output⟩

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem forwardRewrite_work_offset
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId) :
    ruleOffset .work (forwardRewriteRule source ruleId) = 0 := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem forwardRecord_work_offset
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId) :
    ruleOffset .work (forwardRecordRule source ruleId) =
      (source.rule ruleId).move.offset := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem reverseErase_work_offset
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId) :
    ruleOffset .work (reverseEraseRule source ruleId) =
      (source.rule ruleId).move.inverse.offset := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem reverseRestore_work_offset
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId) :
    ruleOffset .work (reverseRestoreRule source ruleId) = 0 := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem forwardRewrite_output_offset
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId) :
    ruleOffset .output (forwardRewriteRule source ruleId) = 0 := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem forwardRecord_output_offset
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId) :
    ruleOffset .output (forwardRecordRule source ruleId) = 0 := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem reverseErase_output_offset
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId) :
    ruleOffset .output (reverseEraseRule source ruleId) = 0 := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem reverseRestore_output_offset
    (source : Machine SourceControl Symbol) (ruleId : source.RuleId) :
    ruleOffset .output (reverseRestoreRule source ruleId) = 0 := rfl

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
theorem forward_work_finalHead (source : Machine SourceControl Symbol)
    (position : Int) (ruleIds : List source.RuleId) :
    finalHead .work position (forwardRules source ruleIds) =
      Machine.Resource.finalHead source position ruleIds := by
  induction ruleIds generalizing position with
  | nil => rfl
  | cons ruleId ruleIds ih =>
      simp [forwardRules_cons, forwardPairRules, ih]

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
theorem forward_work_headPositions (source : Machine SourceControl Symbol)
    (position : Int) (ruleIds : List source.RuleId) :
    headPositions .work position (forwardRules source ruleIds) =
      Machine.Resource.headPositions source position ruleIds := by
  induction ruleIds generalizing position with
  | nil => simp
  | cons ruleId ruleIds ih =>
      simp [forwardRules_cons, forwardPairRules, ih,
        Machine.Resource.headPositions_cons]

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
theorem reverse_work_finalHead (source : Machine SourceControl Symbol)
    (position : Int) (ruleIds : List source.RuleId) :
    finalHead .work (Machine.Resource.finalHead source position ruleIds)
        (reverseRules source ruleIds) = position := by
  induction ruleIds generalizing position with
  | nil => rfl
  | cons ruleId ruleIds ih =>
      rw [Machine.Resource.finalHead_cons, reverseRules_cons,
        finalHead_append, ih]
      simp only [reversePairRules, finalHead_cons, finalHead_nil,
        reverseErase_work_offset, reverseRestore_work_offset]
      cases (source.rule ruleId).move <;> simp [Move.offset, Move.inverse]

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
theorem reverse_work_headPositions (source : Machine SourceControl Symbol)
    (position : Int) (ruleIds : List source.RuleId) :
    headPositions .work
        (Machine.Resource.finalHead source position ruleIds)
        (reverseRules source ruleIds) =
      Machine.Resource.headPositions source position ruleIds := by
  induction ruleIds generalizing position with
  | nil => simp
  | cons ruleId ruleIds ih =>
      rw [Machine.Resource.finalHead_cons, reverseRules_cons,
        headPositions_append, ih, reverse_work_finalHead]
      simp only [reversePairRules, headPositions_cons, headPositions_nil,
        reverseErase_work_offset, reverseRestore_work_offset,
        Machine.Resource.headPositions_cons]
      cases (source.rule ruleId).move <;>
        simp [Move.offset, Move.inverse,
          Machine.Resource.start_mem_headPositions]

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem forward_output_finalHead
    (source : Machine SourceControl Symbol)
    (position : Int) (ruleIds : List source.RuleId) :
    finalHead .output position (forwardRules source ruleIds) = position := by
  induction ruleIds generalizing position with
  | nil => rfl
  | cons ruleId ruleIds ih =>
      simp [forwardRules_cons, forwardPairRules, ih]

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
@[simp] theorem reverse_output_finalHead
    (source : Machine SourceControl Symbol)
    (position : Int) (ruleIds : List source.RuleId) :
    finalHead .output position (reverseRules source ruleIds) = position := by
  induction ruleIds generalizing position with
  | nil => rfl
  | cons ruleId ruleIds ih =>
      rw [reverseRules_cons, finalHead_append, ih]
      simp [reversePairRules]

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
theorem forward_output_headPositions
    (source : Machine SourceControl Symbol)
    (position : Int) (ruleIds : List source.RuleId) :
    headPositions .output position (forwardRules source ruleIds) =
      {position} := by
  induction ruleIds generalizing position with
  | nil => simp
  | cons ruleId ruleIds ih =>
      simp [forwardRules_cons, forwardPairRules, ih]

omit [DecidableEq SourceControl] [DecidableEq Symbol] in
theorem reverse_output_headPositions
    (source : Machine SourceControl Symbol)
    (position : Int) (ruleIds : List source.RuleId) :
    headPositions .output position (reverseRules source ruleIds) =
      {position} := by
  induction ruleIds generalizing position with
  | nil => simp
  | cons ruleId ruleIds ih =>
      rw [reverseRules_cons, headPositions_append,
        reverse_output_finalHead, ih]
      simp [reversePairRules]

theorem copy_work_finalHead_eq {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) (position : Int)
    (ruleIds : List (CopyRuleId Symbol)) :
    finalHead .work position (ruleIds.map (Copy.rule normal)) =
      Copy.Resource.finalHead position ruleIds := by
  induction ruleIds generalizing position with
  | nil => rfl
  | cons ruleId ruleIds ih =>
      simp only [List.map_cons, finalHead_cons]
      rw [ih]
      cases ruleId <;>
        simp [Copy.ruleAt, threeRule, ruleOffset, actionOffset,
          Copy.rule, Copy.Resource.finalHead, Copy.Resource.headOffset]

theorem copy_output_finalHead_eq {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) (position : Int)
    (ruleIds : List (CopyRuleId Symbol)) :
    finalHead .output position (ruleIds.map (Copy.rule normal)) =
      Copy.Resource.finalHead position ruleIds := by
  induction ruleIds generalizing position with
  | nil => rfl
  | cons ruleId ruleIds ih =>
      simp only [List.map_cons, finalHead_cons]
      rw [ih]
      cases ruleId <;>
        simp [Copy.ruleAt, threeRule, ruleOffset, actionOffset,
          Copy.rule, Copy.Resource.finalHead, Copy.Resource.headOffset]

theorem copy_work_finalHead {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) (word : List Symbol) :
    finalHead .work (-1) (Copy.schedule normal word) = -1 := by
  unfold Copy.schedule
  rw [copy_work_finalHead_eq]
  simp [Copy.ids, Copy.Resource.finalHead_append,
    Copy.Resource.headOffset]

theorem copy_output_finalHead {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) (word : List Symbol) :
    finalHead .output (-1) (Copy.schedule normal word) = -1 := by
  unfold Copy.schedule
  rw [copy_output_finalHead_eq]
  simp [Copy.ids, Copy.Resource.finalHead_append,
    Copy.Resource.headOffset]

theorem copy_work_headPositions {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) (word : List Symbol) :
    headPositions .work (-1) (Copy.schedule normal word) =
      Tape.delimiterTraversal word := by
  have h := Copy.Resource.copyTrace_work_visitedPositions normal
    (Tape.blankAt (-1) : Tape source.RuleId) word
  unfold Copy.Resource.copyTrace at h
  rw [Quadruple.Resource.executionTrace_visitedPositions] at h
  simpa using h

theorem copy_output_headPositions {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source) (word : List Symbol) :
    headPositions .output (-1) (Copy.schedule normal word) =
      Tape.delimiterTraversal word := by
  have h := Copy.Resource.copyTrace_output_visitedPositions normal
    (Tape.blankAt (-1) : Tape source.RuleId) word
  unfold Copy.Resource.copyTrace at h
  rw [Quadruple.Resource.executionTrace_visitedPositions] at h
  simpa using h

/-- Exact work-head set of the complete displayed construction. -/
theorem fullRules_work_headPositions
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (position : Int) (ruleIds : List source.RuleId) (output : List Symbol)
    (hfinish : Machine.Resource.finalHead source position ruleIds = -1) :
    headPositions .work position (fullRules normal ruleIds output) =
      Machine.Resource.headPositions source position ruleIds ∪
        Tape.delimiterTraversal output := by
  unfold fullRules
  rw [headPositions_append, headPositions_append,
    forward_work_headPositions, forward_work_finalHead, hfinish,
    copy_work_headPositions, finalHead_append,
    forward_work_finalHead, hfinish, copy_work_finalHead]
  rw [← hfinish, reverse_work_headPositions]
  simp [Finset.union_left_comm, Finset.union_comm]

/-- Exact output-head set of the complete displayed construction. -/
theorem fullRules_output_headPositions
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (ruleIds : List source.RuleId) (output : List Symbol) :
    headPositions .output (-1) (fullRules normal ruleIds output) =
      Tape.delimiterTraversal output := by
  unfold fullRules
  rw [headPositions_append, headPositions_append,
    forward_output_headPositions, forward_output_finalHead,
    copy_output_headPositions, finalHead_append,
    forward_output_finalHead, copy_output_finalHead,
    reverse_output_headPositions]
  ext candidate
  simp [Tape.delimiterTraversal]

/-- Exact number of additional work-head cells introduced by copying. -/
theorem fullRules_work_headCard
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (position : Int) (ruleIds : List source.RuleId) (output : List Symbol)
    (hfinish : Machine.Resource.finalHead source position ruleIds = -1) :
    (headPositions .work position (fullRules normal ruleIds output)).card =
      (Machine.Resource.headPositions source position ruleIds).card +
        (Tape.delimiterTraversal output \
          Machine.Resource.headPositions source position ruleIds).card := by
  rw [fullRules_work_headPositions normal position ruleIds output hfinish]
  have hcard := Finset.card_sdiff_add_card
    (Tape.delimiterTraversal output)
    (Machine.Resource.headPositions source position ruleIds)
  rw [Finset.union_comm] at hcard
  omega

/-- If the source visited the left delimiter and every output data cell, the
    copy sweep can add only the right delimiter. -/
theorem fullRules_work_headPositions_eq_insert_right
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (position : Int) (ruleIds : List source.RuleId) (output : List Symbol)
    (hfinish : Machine.Resource.finalHead source position ruleIds = -1)
    (hcovered : Tape.throughData output ⊆
      Machine.Resource.headPositions source position ruleIds) :
    headPositions .work position (fullRules normal ruleIds output) =
      insert (output.length : Int)
        (Machine.Resource.headPositions source position ruleIds) := by
  rw [fullRules_work_headPositions normal position ruleIds output hfinish,
    Tape.delimiterTraversal_eq_insert_right]
  ext candidate
  simp only [Finset.mem_union, Finset.mem_insert]
  constructor
  · rintro (hsource | hright | hdata)
    · exact Or.inr hsource
    · exact Or.inl hright
    · exact Or.inr (hcovered hdata)
  · rintro (hright | hsource)
    · exact Or.inr (Or.inl hright)
    · exact Or.inl hsource

/-- Under data-cell coverage, the paper's unchanged `s` count is exact iff
    the source also visited the output's right delimiter. -/
theorem fullRules_work_headCard_of_right_mem
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (position : Int) (ruleIds : List source.RuleId) (output : List Symbol)
    (hfinish : Machine.Resource.finalHead source position ruleIds = -1)
    (hcovered : Tape.throughData output ⊆
      Machine.Resource.headPositions source position ruleIds)
    (hright : (output.length : Int) ∈
      Machine.Resource.headPositions source position ruleIds) :
    (headPositions .work position (fullRules normal ruleIds output)).card =
      (Machine.Resource.headPositions source position ruleIds).card := by
  rw [fullRules_work_headPositions_eq_insert_right normal position ruleIds
    output hfinish hcovered, Finset.insert_eq_of_mem hright]

/-- If that right delimiter was not visited, the exact work-head count is
    `s + 1`, not `s`. -/
theorem fullRules_work_headCard_of_right_not_mem
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (position : Int) (ruleIds : List source.RuleId) (output : List Symbol)
    (hfinish : Machine.Resource.finalHead source position ruleIds = -1)
    (hcovered : Tape.throughData output ⊆
      Machine.Resource.headPositions source position ruleIds)
    (hright : (output.length : Int) ∉
      Machine.Resource.headPositions source position ruleIds) :
    (headPositions .work position (fullRules normal ruleIds output)).card =
      (Machine.Resource.headPositions source position ruleIds).card + 1 := by
  rw [fullRules_work_headPositions_eq_insert_right normal position ruleIds
    output hfinish hcovered, Finset.card_insert_of_notMem hright]

/-- Relative to the source *footprint* (visited or ever nonblank), the complete
    target work-head sweep introduces at most the output's right delimiter.
    This is the automatic `s + 1` statement; it is deliberately not phrased
    using the smaller raw source head-visited set. -/
theorem fullRules_work_headCard_le_sourceFootprint_add_one
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (ruleIds : List source.RuleId) (input output : List Symbol)
    (hscheduled : Machine.Resource.Scheduled source ruleIds
      (Standard.config normal.start input)
      (Standard.config normal.finish output)) :
    (headPositions .work (-1) (fullRules normal ruleIds output)).card ≤
      (ExecutionTrace.footprintPositions
        Bennett.Turing.Configuration.tape
        (Machine.Resource.executionTrace source ruleIds
          (Standard.config normal.start input))).card + 1 := by
  let sourceTrace := Machine.Resource.executionTrace source ruleIds
    (Standard.config normal.start input)
  let sourceFootprint := ExecutionTrace.footprintPositions
    Bennett.Turing.Configuration.tape sourceTrace
  have hfinish : Machine.Resource.finalHead source (-1) ruleIds = -1 := by
    simpa using Machine.Resource.finalHead_eq_of_scheduled source hscheduled
  have htraceFinal : sourceTrace.final =
      Standard.config normal.finish output := by
    exact Machine.Resource.executionTrace_final_of_scheduled source hscheduled
  have hthrough : Tape.throughData output ⊆ sourceFootprint := by
    apply ExecutionTrace.Resource.throughData_subset_footprint
      Bennett.Turing.Configuration.tape sourceTrace output
    · rfl
    · rw [htraceFinal]
      rfl
  have hsource : Machine.Resource.headPositions source (-1) ruleIds ⊆
      sourceFootprint := by
    intro position hposition
    unfold sourceFootprint ExecutionTrace.footprintPositions
    rw [Finset.mem_union]
    left
    have hvisited := Machine.Resource.executionTrace_visitedPositions source
      ruleIds (Standard.config normal.start input)
    rw [hvisited]
    exact hposition
  have hsubset :
      headPositions .work (-1) (fullRules normal ruleIds output) ⊆
        insert (output.length : Int) sourceFootprint := by
    rw [fullRules_work_headPositions normal (-1) ruleIds output hfinish,
      Tape.delimiterTraversal_eq_insert_right]
    intro position hposition
    simp only [Finset.mem_union, Finset.mem_insert] at hposition ⊢
    rcases hposition with hsourcePosition | hright | hdata
    · exact Or.inr (hsource hsourcePosition)
    · exact Or.inl hright
    · exact Or.inr (hthrough hdata)
  exact (Finset.card_le_card hsubset).trans
    (Finset.card_insert_le (output.length : Int) sourceFootprint)

/-- Exact work-head visited set of the concrete nonempty target trace. -/
theorem fullTrace_work_visitedPositions
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (start : Bennett.Turing.Configuration SourceControl Symbol)
    (ruleIds : List source.RuleId) (output : List Symbol)
    (hfinish : Machine.Resource.finalHead source start.tape.head ruleIds = -1) :
    ExecutionTrace.visitedPositions
        (fun state : Simulator.Configuration source => state.tape .work)
        (Quadruple.executionTrace (fullRules normal ruleIds output)
          (forwardConfiguration source { current := start, history := [] })) =
      ExecutionTrace.visitedPositions Bennett.Turing.Configuration.tape
          (Machine.Resource.executionTrace source ruleIds start) ∪
        Tape.delimiterTraversal output := by
  rw [Quadruple.Resource.executionTrace_visitedPositions,
    Machine.Resource.executionTrace_visitedPositions]
  change headPositions .work start.tape.head (fullRules normal ruleIds output) =
    Machine.Resource.headPositions source start.tape.head ruleIds ∪
      Tape.delimiterTraversal output
  exact fullRules_work_headPositions normal start.tape.head ruleIds
    output hfinish

/-- Exact output-head visited set of the concrete nonempty target trace. -/
theorem fullTrace_output_visitedPositions
    {source : Machine SourceControl Symbol}
    (normal : Standard.BennettNormalForm source)
    (start : Bennett.Turing.Configuration SourceControl Symbol)
    (ruleIds : List source.RuleId) (output : List Symbol) :
    ExecutionTrace.visitedPositions
        (fun state : Simulator.Configuration source => state.tape .output)
        (Quadruple.executionTrace (fullRules normal ruleIds output)
          (forwardConfiguration source { current := start, history := [] })) =
      Tape.delimiterTraversal output := by
  rw [Quadruple.Resource.executionTrace_visitedPositions]
  change headPositions .output (-1) (fullRules normal ruleIds output) =
    Tape.delimiterTraversal output
  exact fullRules_output_headPositions normal ruleIds output

end Simulator.Resource
end Bennett.Turing
