/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
public import Mathlib.RingTheory.Norm.Basic
/-!
# Norms from Kummer algebras
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- A nonzero element `b` is a norm from the Kummer algebra
`K[X] / (X^n - a)`. -/
def IsKummerNorm
    (K : Type u) [Field K] (n : ℕ+) (a b : Kˣ) : Prop :=
  ∃ y : (KummerAlgebra K n a)ˣ,
    Algebra.norm K (y : KummerAlgebra K n a) = (b : K)

end ClassFieldTheory
