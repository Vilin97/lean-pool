/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import LeanPool.LeanPolyABC.All
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# Polynomial ABC (Mason–Stothers) and its corollaries

Source: arxiv:2408.15180
Authors: Seewoo Lee
Status: verified
Main declarations: `LeanPolyABC.Polynomial.abc`, `LeanPolyABC.Polynomial.flt`
Tags: number-theory, polynomials, algebra, mason-stothers
MSC: 11C08, 12E05
-/

@[expose] public section

/-!
## Mathematical overview

A formalization of the **Mason–Stothers theorem** — the polynomial analogue of
the ABC conjecture — together with its classical consequences.

- `LeanPolyABC.Polynomial.abc`: for coprime polynomials `a + b = c` over a field,
  not all constant, `max (deg a) (deg b) (deg c) < deg (rad (a*b*c))`.
- `LeanPolyABC.Polynomial.flt`: the polynomial Fermat's Last Theorem — no
  nontrivial coprime polynomial solutions of `aⁿ + bⁿ = cⁿ` for `n ≥ 3`.
- The `Corollaries` modules also derive the Fermat–Catalan inequality and
  Davenport's theorem, and rule out polynomial parametrizations.
-/
