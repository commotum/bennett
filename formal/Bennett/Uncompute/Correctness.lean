import Bennett.Uncompute.Core

/-!
# Correctness of compute-copy-uncompute

The theorems here are stated at the semantic-macro level.  One successful
application consists of an exact recorded run, an explicit halt check, a copy
onto the distinguished blank target, and the exact inverse run.  No concrete
machine-transition cost is assigned to that macro.
-/

namespace Bennett.Uncompute

variable {α β Record : Type*} {step : PartialStep α} [DecidableEq β]

/--
The four stages of compute-copy-uncompute, including the exact temporary
history length and exact cleanup of an arbitrary pre-existing history suffix.
-/
theorem exists_stages_of_run
    (recorder : HistoryRecorder step Record) (observe : α → β) (blank : β)
    {n : Nat} {before after : α} (initialHistory : List Record)
    (hrun : step.Runs n before after) (hhalt : step.Halted after) :
    ∃ generatedHistory : List Record,
      generatedHistory.length = initialHistory.length + n ∧
      recorder.forward.iterate n ⟨before, initialHistory⟩ =
        some ⟨after, generatedHistory⟩ ∧
      haltGuard step Record ⟨after, generatedHistory⟩ =
        some ⟨after, generatedHistory⟩ ∧
      Copy.observedForward
          (fun state : HistoryState α Record => observe state.current) blank
          (⟨after, generatedHistory⟩, blank) =
        some (⟨after, generatedHistory⟩, observe after) ∧
      recorder.backward.iterate n ⟨after, generatedHistory⟩ =
        some ⟨before, initialHistory⟩ := by
  obtain ⟨generatedHistory, hforward⟩ :=
    (recorder.exists_forward_run_iff n before after initialHistory).mp hrun
  refine ⟨generatedHistory, recorder.history_length_of_run hforward,
    hforward, ?_, ?_, recorder.reverse_run hforward⟩
  · exact (haltGuard_apply_iff step Record _).2 hhalt
  · simp

/--
Exact endpoint theorem: the input state and its entire initial history are
restored, while the observation of the terminal state remains on the output
register.
-/
theorem computeCopyUncompute_apply_of_run_halted
    (recorder : HistoryRecorder step Record) (observe : α → β) (blank : β)
    {n : Nat} {before after : α} (initialHistory : List Record)
    (hrun : step.Runs n before after) (hhalt : step.Halted after) :
    computeCopyUncompute recorder observe blank n
        (⟨before, initialHistory⟩, blank) =
      some (⟨before, initialHistory⟩, observe after) := by
  obtain ⟨generatedHistory, _, hcompute, hguard, hcopy, huncompute⟩ :=
    exists_stages_of_run recorder observe blank initialHistory hrun hhalt
  change
    ((((recorder.forward.iterate n ⟨before, initialHistory⟩).map
            (fun computed => (computed, blank))).bind
          (fun computed =>
            (haltGuard step Record computed.1).map
              (fun accepted => (accepted, computed.2)))).bind
        (Copy.observedForward
          (fun state : HistoryState α Record => observe state.current) blank)).bind
      (fun copied =>
        (recorder.backward.iterate n copied.1).map
          (fun restored => (restored, copied.2))) =
      some (⟨before, initialHistory⟩, observe after)
  simp [hcompute, hguard, hcopy, huncompute]

end Bennett.Uncompute
