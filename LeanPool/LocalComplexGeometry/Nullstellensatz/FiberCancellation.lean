/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Nullstellensatz.PolynomialFibers
import LeanPool.LocalComplexGeometry.Nullstellensatz.ZeroSetGerms

/-!
# Removing the exceptional fibers

After denominator clearing, the generic-fiber argument gives coefficient
vanishing away from one analytic bad factor.  This file packages the pure
pointwise step: fiber rigidity makes every lower-degree coefficient zero on
the good locus, so multiplying by the bad factor extends the conclusion over
the exceptional locus as well.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-- If a degree-`< e` polynomial vanishes on all roots of a separable
degree-`e` fiber whenever `D` is nonzero, then every coefficient multiplied
by `D` vanishes, including on the exceptional fibers where `D = 0`. -/
theorem eventually_mul_coefficient_eq_zero_of_vanishes_on_good_fibers
    {n e : ℕ} (he : 0 < e)
    (Z : ComplexEuclidean n → Prop)
    (D : ComplexEuclidean n → ℂ)
    (q : ComplexEuclidean n → Polynomial ℂ)
    (b : Fin e → ComplexEuclidean n → ℂ)
    (hgood : ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      Z z → D z ≠ 0 →
        q z ≠ 0 ∧ (q z).Separable ∧ (q z).natDegree = e ∧
          ∀ w : ℂ, (q z).eval w = 0 →
            (remainderPolynomialAt b z).eval w = 0) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      Z z → ∀ i : Fin e, D z * b i z = 0 := by
  filter_upwards [hgood] with z hz
  intro hZ i
  by_cases hD : D z = 0
  · simp [hD]
  · obtain ⟨hqne, hqsep, hqdegree, hvanish⟩ := hz hZ hD
    have hbdegree : (remainderPolynomialAt b z).natDegree < (q z).natDegree := by
      rw [hqdegree]
      exact remainderPolynomialAt_natDegree_lt he b z
    have hbzero : remainderPolynomialAt b z = 0 :=
      polynomial_eq_zero_of_natDegree_lt_of_vanishes_on_separableRoots
        hqne hqsep hbdegree hvanish
    have hbi : b i z = 0 :=
      remainderPolynomialAt_coeff_eq_zero b z hbzero i
    simp [hbi]

/-- Turn the representative-level product-vanishing conclusion into the
corresponding inclusion of local set germs. -/
theorem localSetGerm_le_germZeroLocus_mul_of_eventually
    {n : ℕ} (Z : LocalSetGerm n)
    (Zrep : ComplexEuclidean n → Prop)
    (D c : ComplexEuclidean n → ℂ)
    (hD : AnalyticAt ℂ D 0) (hc : AnalyticAt ℂ c 0)
    (hZ : Z = (Zrep : LocalSetGerm n))
    (hvanish : ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      Zrep z → D z * c z = 0) :
    Z ≤ germZeroLocus
      (HolomorphicGerm.ofFunction D hD * HolomorphicGerm.ofFunction c hc) := by
  rw [hZ]
  change
    (Zrep : LocalSetGerm n) ≤
      ((fun z : ComplexEuclidean n ↦ D z * c z = 0) : LocalSetGerm n)
  rw [Filter.Germ.coe_le]
  exact hvanish

end

end LocalComplexGeometry
