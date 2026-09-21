/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveInfinityDifferentDegree

/-!
# The complementary different bound above infinity

For a primitive infinity-chart equation of bidegree at most `(a,b)`, the
weighted different contribution above infinity is bounded by

`a * (2 * b - 2) - degree(discriminant)`.

Together with the finite-place discriminant bound, this gives the sharp total
different budget used in the Corvaja--Zannier plane-curve estimate.
-/

open scoped Polynomial nonZeroDivisors
open Multiplicative WithZero Polynomial IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance infinityComplementConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance infinityComplementConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K) (RatFunc K) :=
  .of_algebraMap_eq' rfl

local instance infinityComplementTopIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

/-- The residue-degree-weighted different above infinity is bounded by the
complement of the finite discriminant degree in the full bidegree budget. -/
theorem planeCurveInfinityDifferentDegree_le_bidegreeComplement
    (a : ℕ) (F : K[X][X])
    (hcoeff : ∀ i, (F.coeff i).natDegree ≤ a)
    (i : ℕ) (hFi : F.coeff i ≠ 0)
    (hi : (F.coeff i).natDegree = a)
    (v : L)
    (hv : aeval v (infinityNormalizedIntegralPolynomial K a F hcoeff) = 0)
    (hprimitive : Algebra.adjoin (RatFunc K) {v} = ⊤)
    (hdegree : F.natDegree = Module.finrank (RatFunc K) L)
    (hFdiscr : F.discr ≠ 0)
    (hcard : (F.natDegree : Cardinal) < Cardinal.mk K) :
    (infinityDifferentDegree K L : ℤ) ≤
      (a * (2 * F.natDegree - 2) : ℕ) - (F.discr.natDegree : ℤ) := by
  let A := RatFuncInfinityIntegers K
  let G : A[X] := infinityNormalizedIntegralPolynomial K a F hcoeff
  have hGprimitive : G.IsPrimitive := by
    exact infinityNormalizedIntegralPolynomial_isPrimitive K a F hcoeff i hFi hi
  have hmapG : G.map (algebraMap A (RatFunc K)) =
      infinityNormalizedPolynomial K a F := by
    exact infinityNormalizedIntegralPolynomial_map K a F hcoeff
  have hGdegree : G.natDegree = F.natDegree := by
    have h := congrArg Polynomial.natDegree hmapG
    rw [natDegree_map_eq_of_injective
      (IsFractionRing.injective A (RatFunc K)),
      infinityNormalizedPolynomial_natDegree] at h
    exact h
  obtain ⟨c, hc⟩ :=
    exists_local_center_eval_isUnit_of_isPrimitive_natDegree_lt_card
      G hGprimitive (by simpa [hGdegree] using hcard)
  have hcunit := hc
  obtain ⟨u, hu⟩ := hc
  have hvc : v ≠ algebraMap A L c := by
    intro heq
    have hzero : algebraMap A L (G.eval c) = 0 := by
      simpa [G, heq] using hv
    exact (IsUnit.map (algebraMap A L) hcunit).ne_zero hzero
  have hdiscrMap : algebraMap A (RatFunc K) G.discr =
      (infinityNormalizedPolynomial K a F).discr := by
    rw [← hmapG]
    exact (discr_map_of_injective (algebraMap A (RatFunc K))
      (IsFractionRing.injective A (RatFunc K)) G).symm
  have hnormDiscr : (infinityNormalizedPolynomial K a F).discr ≠ 0 := by
    rw [infinityNormalizedPolynomial_discr]
    exact mul_ne_zero
      (pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero RatFunc.X_ne_zero)))
      (RatFunc.algebraMap_ne_zero hFdiscr)
  have hGdiscr : G.discr ≠ 0 := by
    intro hzero
    apply hnormDiscr
    rw [← hdiscrMap, hzero, map_zero]
  have hbound :=
    infinityDifferentDegree_le_discriminantOrder_of_primitiveElement
      K L G c u v hu.symm hvc hv hprimitive
        (hGdegree.trans hdegree) hGdiscr
  calc
    (infinityDifferentDegree K L : ℤ) ≤
        ratFuncInfinityOrder (algebraMap A (RatFunc K) G.discr) := hbound
    _ = ratFuncInfinityOrder (infinityNormalizedPolynomial K a F).discr := by
      rw [hdiscrMap]
    _ = (a * (2 * F.natDegree - 2) : ℕ) -
        (F.discr.natDegree : ℤ) :=
      ratFuncInfinityOrder_infinityNormalizedPolynomial_discr K a F hFdiscr

end

end BGS.CorvajaZannier
