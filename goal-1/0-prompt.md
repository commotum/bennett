# Continuation Prompt

```text
Work autonomously through goal-1/0-plan.md using the repeatable protocol in
goal-1/0-loop.md and the fast incremental Lean guidance in BUILD-PLAN.md.

The high-level objective is to reconstruct and formally verify the mathematical
content of Bennett's “Logical Reversibility of Computation” as a reusable pinned
Lean 4/mathlib library: general deterministic partial systems and recorded
histories, compute-copy-uncompute, executable Turing-machine and quadruple
semantics, the concrete three-tape simulator, halting/correctness/reversibility,
and justified resource bounds.

Treat the paper as fallible.  State all assumptions and configuration
preconditions explicitly; distinguish global from reachable reversibility;
prove blank-target copying and exact uncomputation; derive counts from syntax
and traces; never invent a proof, silently weaken a theorem, introduce an
unjustified axiom, or leave sorry/admit in a completed module.  Keep physical
claims out of the verified core and record corrections, exclusions, and exact
failed obligations in the traceability/correction documents.

At each iteration, inspect actual files and current build results, update the
plan facts, select the first incomplete stage, refresh its stage file, implement
only that stage with narrow modules, run focused and required full verification,
record evidence, and fold results back into the plan.  Continue past planning
and through successive stages as far as the environment permits.  Completion
means the original objective is genuinely achieved; any open issue must remain
explicit next work with evidence, consequences, and a concrete unblock action.
```

