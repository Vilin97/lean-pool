/-
Copyright (c) 2026 seb488, Aristotle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: seb488, Aristotle
-/

import LeanPool.LeanComplexAnalysis.Harmonic
import LeanPool.LeanComplexAnalysis.UnivalentFunctions

/-!
# Formalized Complex Analysis in Lean

Source: url:https://github.com/seb488/LeanComplexAnalysis
Authors: seb488, Aristotle
Status: verified
Main declarations: `LeanPool.LeanComplexAnalysis.harnack_ineq`
Tags: complex-analysis, harmonic-functions, poisson-integral, univalent-functions
MSC: 30A99, 31A05, 30C55
-/

/-!
## Mathematical overview

A collection of formalized theorems in complex analysis using Lean 4 and Mathlib. The
formalization centers on harmonic and analytic functions on the unit disc, with three
headline results:

* **The Poisson integral formula** for harmonic functions on the unit disc and arbitrary
  centered discs, expressing the value of a harmonic function inside the disc as an
  integral over its boundary values against the Poisson kernel.
* **The Herglotz–Riesz representation theorem** for positive harmonic functions on the
  unit disc, representing each such function as the Poisson integral of a uniquely
  determined probability measure on the unit circle. An analytic version is also
  obtained for analytic functions on the unit disc with positive real part and
  `p(0) = 1`.
* **Harnack's inequality** for positive harmonic functions on the unit disc, giving
  two-sided bounds on the values of a positive harmonic function in terms of its
  distance to the boundary.

The development also formalizes infrastructure for univalent functions on the unit disc
in `LeanPool.LeanComplexAnalysis.UnivalentFunctions`: the class `S` of normalized
univalent analytic functions, the class `Σ` of univalent functions on the exterior of
the closed unit disc, the square-root transform `g(z) = sqrt(f(z²))`, and the connection
`1 / f(1 / z) ∈ Σ` for `f ∈ S`.

## Provenance

Imported from <https://github.com/seb488/LeanComplexAnalysis>. The acknowledgement in
the upstream README credits Harmonic's AI system Aristotle for assistance.
Ported from Lean v4.28.0-rc1 to Lean Pool's v4.30.0-rc2.
-/
