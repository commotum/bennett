# Generic Lean Goal Build Plan

Use this file as a reusable build plan for any goal folder that changes Lean
code. Treat `GOAL_DIR` as the active goal directory, for example `goal-N`, and
replace stage names, module names, target theorems, and verification commands
with the ones required by that goal.

The stage-specific facts belong in `GOAL_DIR/[INDEX]-[SHORTHAND].md`.
This file should stay generic.

The main purpose of this file is to keep Lean work fast and incremental:
structure modules so small changes rebuild small parts of the dependency graph,
then run the smallest builds that actually verify the stage.

## Objective

Advance the active goal toward one of two valid outcomes:

- the intended Lean theorem, API, proof surface, or executable definition is
  implemented and verified; or
- a checked obstruction is recorded, with the next concrete construction
  target identified.

Do not treat green builds of unused abstractions as goal completion. Completion
requires evidence that covers the stated goal requirements.

## Initial Sync

1. Read `GOAL_DIR/0-plan.md`.
2. Read `GOAL_DIR/0-loop.md` if it exists.
3. Find the first incomplete stage.
4. Read the previous completed stage file, if one exists.
5. Inspect the current Lean modules, docs, and tests relevant to the stage.
6. Update the stage file's `Current Facts` before changing code.

If the repository state contradicts the plan, update the plan before
implementation and record why.

## Scope Rules

- Implement one stage at a time.
- Keep edits limited to the modules and docs needed for the stage.
- Prefer adding a narrow leaf module over editing a large shared module.
- Do not silently widen or narrow the objective.
- If a stage target changes because of checked evidence, record the revised
  target in both the stage file and `0-plan.md`.
- Classify new declarations as runtime, public API, proof-side, diagnostic,
  fallback, or temporary scaffolding.
- Keep temporary scaffolding out of public APIs unless the stage explicitly
  promotes it.

## Lean Module Structure

Optimize for incremental builds before writing proofs.

Use this default layout when a stage adds nontrivial Lean code:

```text
Feature/
  Core.lean        small structures, notation, simple defs
  Basic.lean       cheap simp lemmas and constructors
  Update.lean      executable/update definitions
  Projection.lean  projection/reference theorem statements and proofs
  Audit.lean       diagnostics, no-go lemmas, examples, negative tests
  API.lean         stable public re-exports only
```

For a smaller feature, use one narrow leaf module. Split only when a file starts
pulling in imports that unrelated consumers do not need.

Rules:

- Put data structures and cheap definitions in low-dependency modules.
- Put heavy proofs in leaf modules that few later files import.
- Put diagnostics, counterexamples, exhaustive checks, and no-go probes in
  `Audit` or stage-specific leaf modules, not in public runtime/API modules.
- Keep `API.lean` thin: imports and re-exports only, or very small wrappers.
- Do not import an `API` or umbrella module from internal leaves if importing
  the specific dependency would work.
- Do not add experimental declarations to shared core files just because they
  are convenient.
- Avoid editing high-fanout modules unless the stage explicitly changes the
  shared API.

## Import Hygiene

Before adding an import, ask whether the file really needs all of it.

Preferred:

```lean
import Formal.Some.Narrow.Module
```

Avoid in leaf files when a narrower import exists:

```lean
import Formal.Some.API
import Formal.Some.All
```

Guidelines:

- Keep imports acyclic and layered: core definitions should not import theorem
  leaves, audits, or runtime consumers.
- If a theorem needs a heavy reference/proof surface, isolate that theorem in a
  proof leaf and keep the runtime definition file light.
- If two files import each other conceptually, split shared definitions into a
  lower `Core` file.
- Re-run a focused build after import changes before continuing; import churn
  can invalidate much more of the graph than theorem edits.
- Prefer local helper lemmas in a leaf file until at least two real consumers
  need them.

## Build-Time Checklist

Before implementation:

1. Identify the lowest existing module that should own the new declaration.
2. Identify high-fanout files that should not be touched.
3. Decide whether the change belongs in:
   - a new leaf module;
   - a low-level core module;
   - a proof/audit module;
   - a public API module.
4. Write down the focused build command for the intended module.
5. Write down the adjacent consumer builds that prove the public surface still
   works.

During implementation:

- Build after defining the skeleton before starting large proofs.
- Build after import changes.
- Keep unrelated theorem cleanup out of the stage.
- Move slow or diagnostic proofs out of shared modules.
- If a proof search tactic becomes slow, prefer smaller explicit lemmas over
  broad simp/global automation changes.

After implementation:

- Run the touched leaf build.
- Run only the adjacent consumers needed by the stage.
- Avoid full project builds unless the stage changes high-fanout API, build
  configuration, notation, or global instances.

## Lean Construction Rules

- Prefer existing local definitions, theorem names, namespace style, and proof
  patterns.
- Name the target definitions and theorem statements before filling in large
  proofs.
- Prove small lemmas that match real proof obligations; avoid broad helper
  lemmas without a known consumer.
- Keep theorem statements strong enough for the next stage, but avoid proving
  a stronger invariant just because it sounds cleaner.
- If a proof fails for structural reasons, turn the failure into either:
  - a smaller checked lemma;
  - a named obstruction;
  - a documented change to the stage target.
- Do not leave `sorry`, `admit`, or new axioms unless the stage explicitly
  allows a theorem-target scaffold, and then label it as incomplete.
- Avoid broad global attributes such as new global `[simp]` lemmas or
  instances in high-fanout modules unless the stage requires them. Prefer local
  simp sets or narrow theorem leaves.
- Keep reducibility and instance search predictable. If a new instance is only
  needed locally, keep it local or avoid making it an instance.

## Boundary Checks

Each goal should define its own forbidden shortcuts. Common examples:

- using a reference implementation as runtime state;
- routing through dense structures that the goal is meant to avoid;
- using future context in a causal update theorem;
- proving only a diagnostic theorem and treating it as the final theorem;
- adding broad state fields without a checked necessity proof;
- replacing a general theorem with a special-case bridge.

For each stage, write the relevant boundary in the stage file and verify it
with scans, theorem signatures, or code inspection.

## Implementation Checklist

For the selected stage:

1. Create or refresh `GOAL_DIR/[INDEX]-[SHORTHAND].md`.
2. Record current facts, assumptions, and exact completion requirements.
3. Identify files expected to change.
4. Identify the dependency layer and whether a new leaf module is better than
   editing an existing shared module.
5. Add or update Lean definitions.
6. Add or update theorem statements and proofs.
7. Add size, cost, closure, or invariance facts if the stage creates growing
   data or a reusable state transition.
8. Build the touched modules.
9. Run goal-specific adjacent builds.
10. Run scans for forbidden shortcuts and proof holes.
11. Run whitespace/diff checks.
12. Record exact results in the stage file.
13. Fold results back into `GOAL_DIR/0-plan.md`.

## Verification

Run the smallest focused build that covers every touched Lean module:

```text
cd formal && lake build MODULE.NAME
```

For a new file, first build the new leaf directly:

```text
cd formal && lake build New.Leaf.Module
```

When touching a shared API, run adjacent builds for known consumers:

```text
cd formal && lake build ADJACENT.MODULE.ONE ADJACENT.MODULE.TWO
```

Run a broader build only when needed:

- public API module changed;
- imports in a high-fanout module changed;
- global notation, instances, or simp lemmas changed;
- build configuration changed;
- the stage completion requirements explicitly demand it.

Run a proof-hole scan over changed Lean code and the goal folder:

```text
rg -n "sorry|admit|axiom" formal/Formal GOAL_DIR
```

Run goal-specific shortcut scans. Replace the patterns with the forbidden
terms for the active goal:

```text
rg -n "FORBIDDEN_PATTERN_1|FORBIDDEN_PATTERN_2" formal/Formal GOAL_DIR
```

Run:

```text
git diff --check
```

Documentation hits for guardrail text are acceptable when recorded. Lean code
hits need removal or explicit classification as proof-side, diagnostic, or
allowed by the stage.

## Stage Report Template

Each stage file should use this structure:

```markdown
# [INDEX]-[SHORTHAND]

## Current Facts

- Facts from current code, tests, docs, and previous stage results.

## Updated Assumptions

- Assumptions that still look valid.
- Assumptions that changed.
- Assumptions that need tests before being trusted.

## Big Picture Objective

- The stage objective, adjusted for current facts.

## Detailed Implementation Plan

- Concrete code/doc/test changes.
- Files expected to change.
- New tests or commands.

## Build Structure

- New or touched Lean modules.
- Why each module owns the declarations placed there.
- High-fanout modules intentionally avoided.
- Focused build command.
- Adjacent consumer builds required.

## Boundary Checks

- Runtime/API/proof-side boundaries relevant to this stage.
- Forbidden shortcuts and how they will be checked.

## Completion Requirements

- Requirement-by-requirement checks.
- Required build commands.
- Required scans.
- Documentation updates.

## Stage Results

- Work completed.
- Definitions, theorem names, and modules added or changed.
- Builds and scans run.
- What was learned.
- What changes in `0-plan.md` before the next stage.
```

## Fold-Back

Before stopping:

1. Update the stage file with exact results.
2. Update `GOAL_DIR/0-plan.md` current facts and stage status.
3. Record exact theorem names and module paths.
4. Record failed obligations and next actions.
5. Leave the next stage resumable.

Do not mark a stage complete unless its completion requirements are covered by
the recorded evidence.
