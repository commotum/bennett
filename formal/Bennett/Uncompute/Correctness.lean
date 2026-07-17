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

/--
The partial inverse verifies and removes the copied output, then returns the
output register to blank while preserving the restored source and history.
-/
theorem computeCopyUncompute_symm_apply_of_run_halted
    (recorder : HistoryRecorder step Record) (observe : α → β) (blank : β)
    {n : Nat} {before after : α} (initialHistory : List Record)
    (hrun : step.Runs n before after) (hhalt : step.Halted after) :
    (computeCopyUncompute recorder observe blank n).symm
        (⟨before, initialHistory⟩, observe after) =
      some (⟨before, initialHistory⟩, blank) := by
  apply (computeCopyUncompute recorder observe blank n).eq_some_iff.mpr
  exact computeCopyUncompute_apply_of_run_halted
    recorder observe blank initialHistory hrun hhalt

/--
For a blank output register, the exact-`n` macro has some result precisely when
the source computation halts after exactly `n` successful transitions.
-/
theorem computeCopyUncompute_succeeds_iff_haltsIn
    (recorder : HistoryRecorder step Record) (observe : α → β) (blank : β)
    (n : Nat) (before : α) (initialHistory : List Record) :
    (∃ result,
        computeCopyUncompute recorder observe blank n
            (⟨before, initialHistory⟩, blank) = some result) ↔
      step.HaltsIn n before := by
  constructor
  · rintro ⟨result, hresult⟩
    change
      ((((recorder.forward.iterate n ⟨before, initialHistory⟩).map
              (fun computed => (computed, blank))).bind
            (fun computed =>
              (haltGuard step Record computed.1).map
                (fun accepted => (accepted, computed.2)))).bind
          (Copy.observedForward
            (fun state : HistoryState α Record => observe state.current)
            blank)).bind
        (fun copied =>
          (recorder.backward.iterate n copied.1).map
            (fun restored => (restored, copied.2))) = some result at hresult
    obtain ⟨copied, hthroughCopy, _⟩ :=
      Option.bind_eq_some_iff.mp hresult
    obtain ⟨accepted, hthroughGuard, _⟩ :=
      Option.bind_eq_some_iff.mp hthroughCopy
    obtain ⟨computed, hcompute, hguard⟩ :=
      Option.bind_eq_some_iff.mp hthroughGuard
    obtain ⟨terminal, hforward, rfl⟩ :=
      Option.map_eq_some_iff.mp hcompute
    obtain ⟨acceptedState, haccepted, _⟩ :=
      Option.map_eq_some_iff.mp hguard
    have hhalt : step.Halted terminal.current :=
      (haltGuard_eq_some_iff step Record terminal acceptedState).mp haccepted |>.1
    exact ⟨terminal.current, recorder.source_run_of_forward_run hforward, hhalt⟩
  · rintro ⟨after, hrun, hhalt⟩
    exact ⟨(⟨before, initialHistory⟩, observe after),
      computeCopyUncompute_apply_of_run_halted
        recorder observe blank initialHistory hrun hhalt⟩

/--
With an arbitrary initial output register, successful execution requires
exactly the distinguished blank value in addition to exact source halting.
-/
theorem computeCopyUncompute_succeeds_iff_blank_and_haltsIn
    (recorder : HistoryRecorder step Record) (observe : α → β) (blank : β)
    (n : Nat) (before : α) (initialHistory : List Record) (target : β) :
    (∃ result,
        computeCopyUncompute recorder observe blank n
            (⟨before, initialHistory⟩, target) = some result) ↔
      target = blank ∧ step.HaltsIn n before := by
  constructor
  · rintro ⟨result, hresult⟩
    change
      ((((recorder.forward.iterate n ⟨before, initialHistory⟩).map
              (fun computed => (computed, target))).bind
            (fun computed =>
              (haltGuard step Record computed.1).map
                (fun accepted => (accepted, computed.2)))).bind
          (Copy.observedForward
            (fun state : HistoryState α Record => observe state.current)
            blank)).bind
        (fun copied =>
          (recorder.backward.iterate n copied.1).map
            (fun restored => (restored, copied.2))) = some result at hresult
    obtain ⟨copied, hthroughCopy, _⟩ :=
      Option.bind_eq_some_iff.mp hresult
    obtain ⟨accepted, hthroughGuard, hcopy⟩ :=
      Option.bind_eq_some_iff.mp hthroughCopy
    obtain ⟨computed, hcompute, hguard⟩ :=
      Option.bind_eq_some_iff.mp hthroughGuard
    obtain ⟨terminal, hforward, rfl⟩ :=
      Option.map_eq_some_iff.mp hcompute
    obtain ⟨acceptedState, haccepted, rfl⟩ :=
      Option.map_eq_some_iff.mp hguard
    rcases copied with ⟨copiedWork, copiedOutput⟩
    have hblank : target = blank :=
      (Copy.observedForward_eq_some_iff
        (fun state : HistoryState α Record => observe state.current)
        blank target acceptedState copiedWork copiedOutput).mp hcopy |>.1
    have hhalt : step.Halted terminal.current :=
      (haltGuard_eq_some_iff step Record terminal acceptedState).mp haccepted |>.1
    exact ⟨hblank, terminal.current,
      recorder.source_run_of_forward_run hforward, hhalt⟩
  · rintro ⟨htarget, hhalts⟩
    subst target
    exact (computeCopyUncompute_succeeds_iff_haltsIn
      recorder observe blank n before initialHistory).mpr hhalts

/-- Every successful result has exactly the restored-work/copy-output shape. -/
theorem computeCopyUncompute_eq_some_iff
    (recorder : HistoryRecorder step Record) (observe : α → β) (blank : β)
    (n : Nat) (before : α) (initialHistory : List Record)
    (result : HistoryState α Record × β) :
    computeCopyUncompute recorder observe blank n
        (⟨before, initialHistory⟩, blank) = some result ↔
      ∃ after,
        step.Runs n before after ∧
        step.Halted after ∧
        result = (⟨before, initialHistory⟩, observe after) := by
  constructor
  · intro hresult
    obtain ⟨after, hrun, hhalt⟩ :=
      (computeCopyUncompute_succeeds_iff_haltsIn
        recorder observe blank n before initialHistory).mp ⟨result, hresult⟩
    have hexact := computeCopyUncompute_apply_of_run_halted
      recorder observe blank initialHistory hrun hhalt
    exact ⟨after, hrun, hhalt, Option.some.inj (hresult.symm.trans hexact)⟩
  · rintro ⟨after, hrun, hhalt, rfl⟩
    exact computeCopyUncompute_apply_of_run_halted
      recorder observe blank initialHistory hrun hhalt

/-- Boolean-domain form of exact-count success. -/
theorem computeCopyUncompute_isSome_iff_haltsIn
    (recorder : HistoryRecorder step Record) (observe : α → β) (blank : β)
    (n : Nat) (before : α) (initialHistory : List Record) :
    (computeCopyUncompute recorder observe blank n
      (⟨before, initialHistory⟩, blank)).isSome ↔
      step.HaltsIn n before := by
  rw [Option.isSome_iff_exists]
  exact computeCopyUncompute_succeeds_iff_haltsIn
    recorder observe blank n before initialHistory

/-- Some successful exact-count macro exists exactly when the source terminates. -/
theorem exists_computeCopyUncompute_iff_terminates
    (recorder : HistoryRecorder step Record) (observe : α → β) (blank : β)
    (before : α) (initialHistory : List Record) :
    (∃ n, (computeCopyUncompute recorder observe blank n
      (⟨before, initialHistory⟩, blank)).isSome) ↔
      step.Terminates before := by
  simp only [computeCopyUncompute_isSome_iff_haltsIn,
    PartialStep.Terminates]

/-- The packaged semantic macro is globally reversible on its full domain. -/
theorem computeCopyUncompute_reversible
    (recorder : HistoryRecorder step Record) (observe : α → β)
    (blank : β) (n : Nat) :
    PartialStep.Reversible
      (computeCopyUncompute recorder observe blank n).toFun :=
  PartialStep.InversePair.forward_reversible _

end Bennett.Uncompute
