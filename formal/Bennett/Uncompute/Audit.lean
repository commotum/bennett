import Bennett.Copy.Audit
import Bennett.History.Audit
import Bennett.Uncompute.Correctness

/-!
# Compute-copy-uncompute executable audit

This diagnostic leaf runs the Stage 2 irreversible list-head eraser through
the reusable Stage 3 macro.  The copied observation is `true` exactly at the
empty terminal list; `false` is the distinguished blank output.

Nothing in this file is re-exported by the public API.
-/

namespace Bennett.UncomputeAudit

open HistoryAudit

def terminalObservation (state : List Bool) : Bool := state.isEmpty

example :
    computeCopyUncompute popRecorder terminalObservation false 2
        (⟨[true, false], []⟩, false) =
      some (⟨[true, false], []⟩, true) :=
  rfl

example :
    (computeCopyUncompute popRecorder terminalObservation false 2).symm
        (⟨[true, false], []⟩, true) =
      some (⟨[true, false], []⟩, false) :=
  rfl

/-- The same source run is rejected when the target is not initially blank. -/
example :
    computeCopyUncompute popRecorder terminalObservation false 2
        (⟨[true, false], []⟩, true) = none :=
  rfl

/-- The inverse rejects an output that does not match the terminal observation. -/
example :
    (computeCopyUncompute popRecorder terminalObservation false 2).symm
        (⟨[true, false], []⟩, false) = none :=
  rfl

end Bennett.UncomputeAudit

#print axioms Bennett.Copy.blankEquiv
#print axioms Bennett.Copy.observedEquiv
#print axioms Bennett.CopyAudit.overwriteStep_not_reversible
#print axioms Bennett.Uncompute.computeCopyUncompute_apply_of_run_halted
#print axioms Bennett.Uncompute.computeCopyUncompute_eq_some_iff
#print axioms Bennett.Uncompute.exists_computeCopyUncompute_iff_terminates
#print axioms Bennett.Uncompute.computeCopyUncompute_reversible
