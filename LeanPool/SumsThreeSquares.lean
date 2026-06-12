/-
Copyright (c) 2026 Bhavik Mehta, Pietro Monticone, Abel Doñate Muñoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Pietro Monticone, Abel Doñate Muñoz
-/

import LeanPool.SumsThreeSquares.MinkowskiConvex
import LeanPool.SumsThreeSquares.SumThreeSquares

/-!
# Sums of Three Squares

Source: doi:10.1090/S0002-9939-1957-0085275-8
Authors: Bhavik Mehta, Pietro Monticone, Abel Donate Munoz
Status: verified
Main declarations: `LeanPool.SumsThreeSquares.blueprint_case_mod8_eq3`
Tags: number-theory, quadratic-forms, geometry-of-numbers
MSC: 11E25, 11H06
-/

/-!
## Mathematical overview

A positive integer `m` is a sum of three squares if and only if it is not of the
form `4ᵃ(8n + 7)` (Legendre's three-square theorem, in the form proved by
N. C. Ankeny). This project formalises the core case `m ≡ 3 (mod 8)`, following
Davenport's geometry-of-numbers argument.

Given a squarefree `m ≡ 3 (mod 8)`, one selects a prime `q ≡ 1 (mod 4)` with
`(-2q / p) = 1` for every prime `p ∣ m` (Dirichlet's theorem), then produces
integers `b, h, t` with `b² - 4qh = -m` and `2qt² ≡ -1 (mod m)`. Applying
Minkowski's convex body theorem to a suitable lattice gives a nonzero lattice
point whose associated quadratic form value `v` satisfies `R² + 2v = m` with
`v > 0`; a sum-of-two-squares argument writes `2v = a² + b²`, and then
`m = R² + a² + b²`.

The main result, `blueprint_case_mod8_eq3`, packages this as
`IsSumOfThreeSquares m` for every positive squarefree `m ≡ 3 (mod 8)`.

## Provenance

Imported from <https://github.com/pitmonticone/SumsThreeSquares>; the upstream
Lean proof (initial draft generated with the Aristotle prover) contains no
`sorry`s. Ported from Lean v4.29.1 to Lean Pool's v4.30.0-rc2.
-/
