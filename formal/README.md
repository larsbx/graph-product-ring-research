# Finite maximal-support component

Lean 4.24.0 and Mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (v4.24.0) are pinned. All transitive
Git dependencies are fixed in `lake-manifest.json`.

From this directory, with Elan installed:

```sh
lake exe cache get Mathlib/Tactic.lean Mathlib/Data/Fintype/Perm.lean Mathlib/Data/Fintype/BigOperators.lean Mathlib/Data/Setoid/Basic.lean Mathlib/Algebra/Group/Fin/Basic.lean
cd ..
python3 tools/check_lean.py
python3 oracles/lean_word_vectors.py
```

The gate builds every module with warnings treated as errors, then checks the
transitive axioms of the public theorem API. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed. No `sorryAx`, native-evaluation axiom, or custom
axiom is allowed. `Examples.lean` uses ordinary kernel-reduced `decide`.
The Python replay is independent finite evidence, not an axiom of the proofs.

See [the statement and remaining obligations](../proof/finite-maximal-support-lean.md).
The graph ring and its centered augmentation filtration are not formalized here.
