# Goal 1 Execution Loop

Use `BUILD-PLAN.md` together with this protocol.  Work on one narrow stage at a
time and keep the Lean dependency graph cheap to rebuild.

## Repeatable Loop

1. Sync current state with the actual files, Lean modules, documentation, git
   diff, and test/build results.
2. Update `goal-1/0-plan.md` with current facts before starting the next stage.
3. Select the first incomplete stage.
4. Create or refresh `goal-1/[INDEX]-[SHORTHAND].md` from the template below.
5. Implement only that stage, using narrow leaf modules and focused builds.
6. Add stage-specific verification, negative tests, and no-cheating checks.
7. Run focused builds, required adjacent builds, broader verification when the
   API/build configuration warrants it, proof-hole scans, and whitespace/diff
   checks.
8. Record exact commands, outcomes, theorem names, failed obligations, and new
   facts in the stage file.
9. Fold those results back into `goal-1/0-plan.md`, including any justified
   change to later stages.
10. Continue toward the original objective.  If stopping for the session, leave
    the goal resumable with current evidence, next experiments, unblock actions,
    and assumptions that still need to be challenged.

## Invariants

- Do not narrow the user's objective without saying so and recording why.
- Do not mark a stage complete without requirement-by-requirement evidence.
- Do not treat tests or green builds as evidence unless they cover the stated
  requirement.
- Prefer small, low-complexity stages that reduce uncertainty and rebuild cost.
- Convert blockers into work items: decompose them, route around them, or state
  them as precise proof, model, source-audit, or verification obligations.
- Preserve the distinction between runtime definitions, public API, proof-side
  results, diagnostics, and fallback paths.
- Treat the paper as fallible.  Never repair a claim silently; update the
  traceability matrix and correction log with downstream consequences.
- Keep global versus reachable reversibility, semantic versus syntactic results,
  and exact versus asymptotic resource claims visibly distinct.
- Completed Lean modules must not contain `sorry`, `admit`, or unexplained axioms.

## Stage File Template

```markdown
# [INDEX]-[SHORTHAND]

## Current Facts

- Facts from current code, tests, docs, the paper, and previous stage results.

## Updated Assumptions

- Assumptions that still look valid.
- Assumptions that changed.
- Assumptions that need tests or proofs before being trusted.

## Big Picture Objective

- Restate the stage objective, adjusted for current facts.

## Detailed Implementation Plan

- Concrete code/doc/test changes for this stage.
- Files expected to change.
- New tests or commands required.

## Build Structure

- New or touched Lean modules and why they own their declarations.
- High-fanout modules intentionally avoided.
- Focused build command and required adjacent consumer builds.

## No-Cheating Checks

- Explicit checks proving the implementation does not route through forbidden
  fallback paths, hide assumptions, overstate scope, or infer costs from
  semantic correctness.

## Completion Requirements

- Requirement-by-requirement checks.
- Required build/test/scan commands.
- Documentation and traceability updates required.

## Stage Results

- Fill in at the end of the stage.
- Include definitions/theorems added, tests run, and outcomes.
- Include what was learned and every failed obligation.
- Include what should change in `0-plan.md` before the next stage.
```

