# Bennett Lean Library

This directory contains the pinned Lean 4 formalization project for Bennett's
*Logical Reversibility of Computation*.

The current Stage 1 root is deliberately small:

```text
Bennett.lean
└── Bennett/Prelude.lean
```

From this directory, build the narrow leaf and public root with:

```sh
lake build Bennett.Prelude
lake build Bennett
```

The toolchain is Lean 4.31.0.  Mathlib is pinned in `lakefile.toml` to commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (the `v4.31.0` release commit).
See `../docs/CONVENTIONS.md` for semantic scope and `../docs/TRACEABILITY.md`
for the paper-to-library map.
