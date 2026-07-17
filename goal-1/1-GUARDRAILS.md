# 1-GUARDRAILS

## Current Facts

- The source, PDF, Table 1, and Table 2 have now been inspected completely.
- The repository has a minimal compiling `formal/` project pinned to Lean 4.31.0
  and the matching mathlib release commit.
- The full resolved dependency graph is recorded in `formal/lake-manifest.json`.
- The formal core starts with semantics and guardrails, not the paper's physical
  discussion or segmented-history speculation.
- Source claims, table syntax, corrections, exclusions, and open obligations are
  indexed in `docs/TRACEABILITY.md` and `docs/CORRECTIONS.md`.

## Updated Assumptions

- `Config → Option Config` remains the leading runtime partial-step candidate,
  but Stage 2 must compare it against mathlib `PFun`; the Stage 1 import does not
  preselect either representation.
- Two-way-infinite tapes are needed for Bennett's stated shift domains/ranges;
  the concrete executable representation remains owned by Stage 4.
- Syntactic pairwise rule non-overlap must be kept separate from extensional
  semantic determinism and injectivity.
- Literal Table 1 control is not restored (`A₁` becomes `C₁`), so later
  cleanup theorems require both exact concrete endpoints and a phase projection.

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

- **Project created:** `formal/lean-toolchain`, `formal/lakefile.toml`, the fully
  resolved `formal/lake-manifest.json`, `formal/Bennett/Prelude.lean`, the thin
  `formal/Bennett.lean` root, and `formal/README.md`.
- **Exact pins:** Lean `leanprover/lean4:v4.31.0`, commit
  `68218e876d2a38b1985b8590fff244a83c321783`; mathlib
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.  All nine dependency checkout
  revisions agree with the committed manifest.
- **Documentation created:** `docs/CONVENTIONS.md` fixes scope/model boundaries;
  `docs/TRACEABILITY.md` inventories the formal claims and transcribes both
  tables; `docs/CORRECTIONS.md` records eleven initial corrections/ambiguities
  with consequences and owning stages.
- **Source findings:** the PDF's range-overlap formula is well-typed but the
  Markdown conversion is not; non-overlap is stronger than extensional semantic
  uniqueness; `A₁`/`C₁` prevent literal full-state restoration; the exact
  state/rule/time arithmetic checks out; space and checkpoint claims need
  corrected cost models.
- **Dependency resolution:** the first sandboxed `lake update` failed only at DNS
  resolution.  Re-running with scoped network authorization fetched the exact
  pins and completed mathlib's cache hook successfully.
- **Build correction:** the first build exposed that Lean 4.31 requires imports
  before module documentation comments.  Moving the two imports fixed the only
  code error.
- **Focused build:** `cd formal && lake build Bennett.Prelude` succeeded with
  398 jobs and built the leaf in 937 ms.
- **Adjacent root build:** `cd formal && lake build Bennett` succeeded with 400
  jobs and built the root in 1.1 s.
- **Full default build:** `cd formal && lake build` succeeded with 400 jobs.
- **Audits:** the completed Lean files have no `sorry`, `admit`, `axiom`, or
  physical-model terms; the repository-wide trailing-whitespace scan had no
  hits; `git diff --check` passed.  `.lake/` is ignored while the manifest remains
  a source artifact.
- **Plan fold-back:** Stage 1 is complete.  Stage 2 must begin by defining the
  semantic/syntactic distinction and an exact history recovery interface; it
  must not inherit Bennett's unqualified overlap iff or Table 1's phase-renamed
  cleanup as literal state equality.
