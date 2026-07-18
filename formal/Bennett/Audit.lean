import Bennett.Checkpoint.Audit
import Bennett.Copy.Audit
import Bennett.History.Audit
import Bennett.Turing.Audit
import Bennett.Turing.Quadruple.Audit
import Bennett.Turing.Simulator.Audit
import Bennett.Uncompute.Audit

/-!
# Whole-library diagnostic audit

This umbrella imports every project audit leaf.  The transition layer has no
standalone audit module; its executable laws are exercised by
`Bennett.History.Audit`, and its principal inverse-iteration theorem is printed
below.  This module is deliberately absent from the public `Bennett` root.
-/

open Bennett

#print axioms PartialStep.AreInverses.iterate
#print axioms HistoryRecorder.trace_cleanup
#print axioms Copy.blankEquiv
#print axioms Copy.injective_of_reversible_outputOnly
#print axioms Uncompute.computeCopyUncompute_apply_of_run_halted
#print axioms Uncompute.computeCopyUncompute_reversible
#print axioms Turing.Standard.computes_output_unique
#print axioms ExecutionTrace.runs_iff_exists_run
#print axioms Turing.QuadrupleMachine.step_areInverses
#print axioms Turing.Machine.splitMachine_domainsDisjoint
#print axioms Turing.Simulator.central_correctness
#print axioms Turing.Simulator.terminates_iff_source

open Turing.Simulator.Resource.WorkSupport

#print axioms fullTrace_work_footprintPositions_eq_insert_right

#print axioms Checkpoint.recordedSegmentStage_apply_of_run
#print axioms Checkpoint.computeCopyCleanup_reversible
#print axioms Checkpoint.Cost.paperRoundedCells_eq_temporaryCells_add_dumpCells
#print axioms Checkpoint.Cost.paperContinuousCells_lower_bound

open Checkpoint.Plan

#print axioms computeCopyCleanup_segmentPlan_apply_of_run
