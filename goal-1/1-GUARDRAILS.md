# 1-GUARDRAILS

## Current Facts

- The repository has the paper in Markdown/PDF form and a generic
  `BUILD-PLAN.md`, but no Lean project.
- No earlier `goal-*` folder existed, so this is `goal-1`.
- The host reports Lean 4.31.0 and Lake 5.0.0.
- Table 1 and Table 2 are images in the Markdown edition; exact syntax must be
  inspected from those images or the PDF before reconstruction.
- The formal core starts with semantics and guardrails, not the paper's physical
  discussion or segmented-history speculation.

## Updated Assumptions

- A `formal/` Lake project will isolate the Lean build from source documents.
- The toolchain should be pinned to an exact official release compatible with a
  pinned mathlib revision; availability must be checked before selecting it.
- Initial modules can remain narrow and foundational while table reconstruction
  is documented separately.

## Big Picture Objective

Create a reproducible compiling project skeleton and a complete source/claim
audit that fixes the semantic boundaries for later proof stages.

## Detailed Implementation Plan

- Inspect the remaining paper and both transition-table images.
- Locate a compatible available Lean/mathlib pin or fetch it if authorization
  and network access permit.
- Add `formal/` Lake configuration, toolchain pin, a narrow root namespace, and
  a thin initial API/root module.
- Add `docs/CONVENTIONS.md`, `docs/TRACEABILITY.md`, and
  `docs/CORRECTIONS.md` with stable source identifiers and initial decisions.
- Build the smallest module, then the root target; scan for proof holes and run
  `git diff --check`.

## Build Structure

- `formal/Bennett/Prelude.lean`: namespace and small project-level declarations
  only; no heavy imports.
- `formal/Bennett.lean`: thin public root import.
- High-fanout semantic modules do not yet exist and will not be invented before
  their owning stages.
- Focused build: `cd formal && lake build Bennett.Prelude`.
- Adjacent/root build: `cd formal && lake build Bennett`.

## No-Cheating Checks

- Do not claim the paper's main theorem, counts, or overlap criteria are verified
  merely because the skeleton compiles.
- Do not encode physical assertions in Lean.
- Do not choose semantics that conflate total bijections with partial inverse
  transitions.
- Scan completed Lean modules for `sorry`, `admit`, and project axioms.

## Completion Requirements

- Exact Lean and mathlib revisions are pinned and build successfully.
- Both table images and the full formal portion of the paper are audited.
- Conventions, traceability, and corrections documents exist with initial
  classifications and unresolved obligations.
- Focused and root builds pass.
- Proof-hole scan and `git diff --check` pass.
- Exact commands and results are recorded below and folded into `0-plan.md`.

## Stage Results

- In progress.

