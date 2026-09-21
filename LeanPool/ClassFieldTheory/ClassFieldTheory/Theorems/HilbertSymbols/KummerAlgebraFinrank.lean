/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
import Mathlib.RingTheory.AdjoinRoot
/-!
# Rank of a Kummer algebra

The rank of `K[X] / (X ^ n - a)` is `n` regardless of whether the polynomial
is irreducible. This is distinct from the index of its norm subgroup.
-/

namespace ClassFieldTheory

universe u

/-- The Kummer algebra has the polynomial's degree as its dimension. -/
theorem kummerAlgebra_finrank
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :
    Module.finrank K (KummerAlgebra K n a) = (n : ℕ) := by
  let p : Polynomial K :=
    Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
  change Module.finrank K (Polynomial K ⧸ Ideal.span {p}) = (n : ℕ)
  rw [finrank_quotient_span_eq_natDegree]
  exact Polynomial.natDegree_X_pow_sub_C

end ClassFieldTheory
