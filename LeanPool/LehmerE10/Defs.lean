/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# the objects of the claim.
This file is intentionally byte-identical (after the header) to the definitions in
`Challenge.lean`: it defines Lehmer's polynomial, the generalized Cartan matrix of
the hyperbolic Kac–Moody root system E₁₀, its simple reflections acting on the root
lattice in the basis of simple roots, and a Coxeter element as the product of the
ten simple reflections.
-/

open Polynomial

/-- **Lehmer's polynomial** (Lehmer, 1933):
`x¹⁰ + x⁹ − x⁷ − x⁶ − x⁵ − x⁴ − x³ + x + 1`.
Its Mahler measure `λ ≈ 1.17628` is the smallest known Mahler measure `> 1` of an
integer polynomial. -/
noncomputable def lehmerPolynomial : Polynomial ℤ :=
  X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1

/-- The generalized Cartan matrix of the rank-10 hyperbolic Kac–Moody root system
**E₁₀**: nodes `0–8` form an A₉ chain and node `9` is attached to node `2`
(Bourbaki-style E-series labelling, extended once more past E₉ = E₈⁽¹⁾). -/
def cartanE10 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![ 2, -1,  0,  0,  0,  0,  0,  0,  0,  0;
     -1,  2, -1,  0,  0,  0,  0,  0,  0,  0;
      0, -1,  2, -1,  0,  0,  0,  0,  0, -1;
      0,  0, -1,  2, -1,  0,  0,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0,  0,  0;
      0,  0,  0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0,  0,  0, -1,  2,  0;
      0,  0, -1,  0,  0,  0,  0,  0,  0,  2]

/-- The simple reflection `sᵢ` of the E₁₀ Weyl group acting on the root lattice, in
the basis of simple roots: `sᵢ(αⱼ) = αⱼ − aᵢⱼ αᵢ`, so as a matrix
`(sᵢ)ⱼₖ = δⱼₖ − δⱼᵢ aᵢₖ`. -/
def simpleReflection (i : Fin 10) : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of fun j k => (if j = k then 1 else 0) - (if j = i then cartanE10 i k else 0)

/-- A **Coxeter element** of the E₁₀ Weyl group: the product `s₀ s₁ ⋯ s₉` of the ten
simple reflections, as a matrix acting on the root lattice. -/
def coxeterE10 : Matrix (Fin 10) (Fin 10) ℤ :=
  ((List.finRange 10).map simpleReflection).prod
