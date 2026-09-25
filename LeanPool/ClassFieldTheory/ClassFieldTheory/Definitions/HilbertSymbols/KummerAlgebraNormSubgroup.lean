/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
public import Mathlib.RingTheory.Norm.Basic
/-!
# Norm subgroup of a Kummer algebra

This is the image of the determinant norm on units of `K[X] / (X^n - a)`.
The algebra need not be a field, so this subgroup is defined without any
irreducibility assumption on the polynomial.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u

/-- The unit-norm image of the possibly reducible Kummer algebra. -/
def kummerAlgebraNormSubgroup
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) : Subgroup Kˣ :=
  (Units.map (Algebra.norm K : KummerAlgebra K n a →* K)).range

end ClassFieldTheory
