# Bennett Lean Library

This directory contains the pinned Lean 4 formalization project for Bennett's
*Logical Reversibility of Computation*.

The current public root contains the completed Stage 2–5 foundations:

```text
Bennett.lean
└── Bennett/
    ├── Prelude.lean
    ├── Transition/
    │   ├── Core.lean
    │   ├── Run.lean
    │   ├── Reachability.lean
    │   └── API.lean
    ├── History/
    │   ├── Core.lean
    │   ├── Run.lean
    │   ├── Audit.lean       # diagnostic; not publicly re-exported
    │   └── API.lean
    ├── Copy/
    │   ├── Core.lean
    │   ├── Audit.lean       # diagnostic; not publicly re-exported
    │   └── API.lean
    ├── Uncompute/
    │   ├── Core.lean
    │   ├── Correctness.lean
    │   ├── Audit.lean       # diagnostic; not publicly re-exported
    │   └── API.lean
    └── Turing/
        ├── Tape.lean
        ├── Word.lean
        ├── Resource.lean
        ├── Audit.lean       # diagnostic; not publicly re-exported
        ├── Source/
        │   ├── Core.lean
        │   ├── Determinism.lean
        │   ├── Standard.lean
        │   └── Inverse.lean
        ├── Quadruple/
        │   ├── Core.lean
        │   ├── Inverse.lean
        │   ├── Overlap.lean
        │   ├── Machine.lean
        │   ├── Split.lean
        │   ├── Audit.lean   # diagnostic; not publicly re-exported
        │   └── API.lean
        └── API.lean
```

From this directory, representative focused and public builds are:

```sh
lake build Bennett.Transition.Run
lake build Bennett.History.Run
lake build Bennett.History.Audit
lake build Bennett.Copy.Audit
lake build Bennett.Uncompute.Audit
lake build Bennett.Turing.Audit
lake build Bennett.Turing.Quadruple.Audit
lake build Bennett
```

The toolchain is Lean 4.31.0.  Mathlib is pinned in `lakefile.toml` to commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (the `v4.31.0` release commit).
See `../docs/CONVENTIONS.md` for semantic scope and `../docs/TRACEABILITY.md`
for the paper-to-library map.
