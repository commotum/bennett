# 9-RELEASE-AUDIT

**Status:** Completed.

## Current Facts

- Stages 1–8 supply kernel-checked abstract transition/history/copy/uncompute
  layers, executable source and reversible-target Turing semantics, Bennett's
  complete three-tape simulator, exact syntax/time/tape resource theorems, and
  finite checkpoint semantics with a discrete cost model.
- Thin public APIs and `import Bennett` expose every supported layer.  Audit
  leaves and the `Bennett.Audit` umbrella remain outside the public import
  graph.
- The root and formal-project READMEs now document the module tree, exact
  theorem surfaces, builds, cost conventions, extension workflow, and limits.
- The release traceability, correction, convention, and axiom-audit documents
  name the final declarations and preserve every partial, unresolved,
  speculative, and excluded claim.
- Principal audit results use only Lean/mathlib foundations (`propext`,
  `Classical.choice`, and `Quot.sound`); no project axiom or `sorryAx` occurs.
- The finite checkpoint result is abstract over complete restart states and a
  declared dump-cell/I/O model.  No concrete Turing tape allocator or nested
  logarithmic-space construction is claimed.

## Updated Assumptions

- Treat an API as public only when it is reachable from `import Bennett` or a
  documented narrower `*.API` module; audits remain deliberately unexported.
- Record theorem signatures and axiom dependencies from Lean output rather
  than paraphrasing implementation details.
- A full build verifies compilation but not documentation accuracy; separately
  scan the traceability/correction tables for stale lifecycle labels and
  overclaimed statuses.
- Classify occurrences of words such as `axiom` or `admit` in prose and
  `#print axioms` diagnostics rather than treating a raw text hit as a proof
  hole.
- Preserve explicitly unresolved paper claims in the release report.  Release
  completion means a verified scoped library and an exact gap ledger, not a
  fabricated theorem for every informal sentence.

## Big Picture Objective

Make the finished formalization straightforward to import, extend, rebuild,
and independently audit, then produce the requested evidence-backed final
report without weakening or overstating the formal scope.

## Detailed Implementation Plan

- Finish `Bennett.Checkpoint.API`, checkpoint executable examples, and root
  re-export integration while keeping all audit commands out of public APIs.
- Update the root and Lean-project READMEs with the current module tree,
  focused/full build commands, principal theorem signatures, import examples,
  extension points, cost conventions, and known limitations.
- Add or refresh a release axiom-audit record naming the principal abstract,
  concrete simulator, resource, and checkpoint theorems and their reported
  dependencies.
- Re-read conventions, corrections, and traceability against the final Lean
  namespace and theorem names; remove stale stage statuses and preserve
  unresolved/excluded classifications.
- Run all relevant audit leaves, the public root build, then the full Lake
  library build.  Run proof-hole/project-axiom, forbidden-shortcut, long-line,
  whitespace, and import-boundary scans.
- Record exact commands/results here and fold final facts into `0-plan.md`.

## Build Structure

- `formal/Bennett/Checkpoint/API.lean`: thin stable checkpoint re-export.
- `formal/Bennett/Checkpoint/Audit.lean`: examples, forged-state rejection,
  edge cases, and checkpoint axiom prints.
- `formal/Bennett.lean`: public root, no diagnostics.
- `formal/README.md` and `README.md`: import/build/extension guide.
- `docs/AXIOM-AUDIT.md`: release-level declaration and dependency inventory.
- Existing `docs/CONVENTIONS.md`, `docs/CORRECTIONS.md`, and
  `docs/TRACEABILITY.md`: final accuracy pass.

## Boundary Checks

- Do not import an audit leaf from a public API or the root module.
- Do not report `#eval`/example success as a proof of a general theorem.
- Do not call an abstract checkpoint cell budget a concrete three-tape bound.
- Do not describe global syntactic reversibility as merely reachable-state
  reversibility, or vice versa.
- Do not hide standard-input, blank-target, normal-form, key-injectivity,
  finite-enumeration, or positivity assumptions in prose.
- Do not convert physical, one-tape, standardization, Table 2, or nested
  checkpoint gaps into release claims without new checked constructions.

## Completion Requirements

- `lake build Bennett` and a full `lake build` pass on the pinned toolchain and
  manifest; every diagnostic audit named in the release guide also builds.
- Completed Lean modules have no `sorry`, `admit`, `native_decide`, or
  project-specific `axiom` declaration.
- Principal exported theorem signatures and `#print axioms` results are
  recorded and directly inspectable.
- Public APIs are thin, audits are unexported, and import examples compile.
- Documentation maps every important paper claim to formalized, corrected,
  partial, unresolved, speculative, or excluded status.
- The final report lists what is proved, precise assumptions and resource
  metrics, corrections, exclusions, remaining obligations, build/audit
  evidence, and extension guidance.

## Stage Results

- Added `Bennett.Audit`, a diagnostic-only umbrella over all seven audit leaves,
  and recorded its principal declarations and literal axiom sets in
  `docs/AXIOM-AUDIT.md`.
- Replaced both READMEs with release guides covering narrow and root imports,
  public theorem signatures, exact resource conventions, example workflows,
  and extension points.
- Audited `docs/CONVENTIONS.md`, `docs/CORRECTIONS.md`, and
  `docs/TRACEABILITY.md` against the final namespace.  Table 2 and unrestricted
  universality remain partial with exact missing obligations; standardization,
  the one-tape simulator, concrete checkpoint allocation, nested checkpointing,
  and physical claims remain unresolved, speculative, or excluded as
  appropriate.
- `cd formal && lake build Bennett` passed all 2027 jobs.
- `cd formal && lake build` passed all 2027 jobs.
- `cd formal && lake build Bennett.Audit` passed all 2026 jobs and replayed all
  audit leaves.
- `cd formal && lake env lean Bennett/Audit.lean` printed the consolidated
  dependency sets.  Every set is a subset of `propext`, `Classical.choice`, and
  `Quot.sound`; none contains `sorryAx`.
- Proof-hole, forbidden-shortcut, project-axiom, public-audit-import, stale
  status, non-table line-length, and whitespace scans passed.  Public modules
  contain no `sorry`, `admit`, `native_decide`, or project `axiom` declaration.
- The release meets the scoped objective: every completed claim is checked and
  every omitted claim is traceably separated from the verified core.
