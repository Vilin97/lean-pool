/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import LeanPool.ErdosTuzaValtr.All

/-!
# The Erdős–Tuza–Valtr conjecture

Source: url:https://github.com/jcpaik/erdos-tuza-valtr
Authors: Jineon Baek
Status: verified
Main declarations: `ErdosTuzaValtr.main`, `Config.main_lemma`
Tags: combinatorics, discrete-geometry, convex-geometry, ramsey-theory
MSC: 52C10, 05D10
-/

/-!
## Mathematical overview

A formalization of the Erdős–Tuza–Valtr conjecture, a refinement of the
Erdős–Szekeres "happy ending" theorem on convex configurations in planar point
sets in general position.

- `main`: for a cup/cap configuration `C` and a finite point set `S` with
  `Nat.choose (n + 2) 2 + 2 ≤ S.card`, `S` contains the target Erdős–Tuza–Valtr
  configuration. This is the sharp upper bound for the function `E(n)`.
- `Config.main_lemma`: the configuration-relative induction lemma driving the
  proof, combined with a mirror-symmetry reduction (`Config.Mirror_mainGoal`).
-/
