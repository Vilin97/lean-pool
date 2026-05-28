/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/

import LeanPool.LeanPolyABC.All

/-!
# Polynomial ABC (Mason–Stothers) and its corollaries

Source: url:https://github.com/seewoo5/lean-poly-abc
Authors: Seewoo Lee
Status: verified
Main declarations: `LeanPolyABC.Polynomial.abc`, `LeanPolyABC.Polynomial.flt`
Tags: number-theory, polynomials, algebra, mason-stothers
MSC: 11C08, 12E05
-/

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
