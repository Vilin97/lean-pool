/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/

module

public import LeanPool.HopfProblem.MainTheorem.Core3

/-!
# A complex structure on the six-sphere

Source: url:https://github.com/plby/HopfProblem/tree/9ac8a456b526527837d7082ff775213ca8bc9809
Authors: Boris Alexeev
Status: verified
Main declarations: `Mathoverflow1973.mathoverflow_1973`
Tags: complex-geometry, differential-topology, complex-manifolds, six-sphere, torus-fibrations
MSC: 32Q55, 57R15
-/

/-!
# A complex structure on the six-sphere

This project formalizes the construction in Levent Alpöge's paper
*A compact complex threefold fibred by tori over the projective line, and the six-sphere*.
It constructs a compact complex threefold, identifies its underlying smooth manifold with the
standard six-sphere, and transports the complex atlas to `unitSphere 6`.

## Provenance

The canonical source is Boris Alexeev's Apache-2.0-licensed
[`plby/HopfProblem`](https://github.com/plby/HopfProblem) at commit
`9ac8a456b526527837d7082ff775213ca8bc9809`. The thematic source tree was prepared in
[upstream pull request #1](https://github.com/plby/HopfProblem/pull/1) at commit
`bcbeff1324f22d228c9bde649532228826dab47d`. The original source states that most of its Lean
code was written by Codex, so this import is classified as AI provenance.

The mathematics follows [Alpöge's paper](https://alpo.ge/s6.pdf). The final statement was adapted
from the Formal Conjectures rendering of MathOverflow question 1973. Complex-analysis material,
including the Riemann mapping and Hurwitz developments, was adapted from Yury Kudryashov's
[Mathlib pull request #33505](https://github.com/leanprover-community/mathlib4/pull/33505) at
commit `d43061d911b1aeae0788591da437a3b115098962`. Topological material, including simple
connectedness of spheres and path-factorization results used for van Kampen, was adapted from
Sebastian Kumar's [Mathlib pull request #28246](https://github.com/leanprover-community/mathlib4/pull/28246)
at commit `037ad801e1e5a5b7aa1750957c07f7769812effc`.

The reused upstream material is Apache-2.0 licensed and was modified and reorganized here.
Copyright (c) 2025, 2026 Yury Kudryashov; copyright (c) 2026 Sebastian Kumar; copyright 2025
The Formal Conjectures Authors.
-/
