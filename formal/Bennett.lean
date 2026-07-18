import Bennett.Copy.API
import Bennett.Checkpoint.API
import Bennett.History.API
import Bennett.Transition.API
import Bennett.Turing.API
import Bennett.Uncompute.API

/-!
# Bennett

Public root for the verified reversible-computation library.  It exports the
deterministic partial-transition, recorded-history, blank-target copying, and
compute-copy-uncompute APIs together with abstract finite checkpoint chains,
constructive segment plans and costs, executable source Turing-machine
semantics, reversible heterogeneous quadruple syntax, and the verified Bennett
three-tape simulator.  Diagnostic examples remain in their audit leaves.
-/
