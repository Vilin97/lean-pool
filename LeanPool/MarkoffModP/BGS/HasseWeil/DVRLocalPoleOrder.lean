/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.LocalPoleFiltration
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindPlaceOrder

/-!
# Local pole spaces and valuation order

The denominator presentation of `localPoleSpace` agrees with the usual
valuation-order condition when its denominator is a power of a uniformizer.
This is the bridge from the exact DVR quotient to exhaustive function-field
places.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

variable {K R L : Type*} [Field K] [CommRing R]
  [IsDedekindDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra K R] [Algebra R L] [Algebra K L]
  [IsScalarTower K R L] [IsFractionRing R L]

/-- Membership in the local denominator filtration is exactly the expected
lower bound on the discrete valuation. -/
theorem mem_localPoleSpace_iff_finitePlaceOrder
    (π : R) (hπ : Irreducible π)
    (hπIdeal : (IsDiscreteValuationRing.maximalIdeal R).asIdeal =
      Ideal.span {π}) (n : ℕ) (x : L) :
    x ∈ localPoleSpace (K := K) (L := L) π n ↔
      x = 0 ∨ (x ≠ 0 ∧
        -(n : ℤ) ≤ finitePlaceOrder
          (IsDiscreteValuationRing.maximalIdeal R) x) := by
  let v := IsDiscreteValuationRing.maximalIdeal R
  have hπMap : algebraMap R L π ≠ 0 := by
    simpa using (IsFractionRing.injective R L).ne hπ.ne_zero
  have hπPowMap : algebraMap R L (π ^ n) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero n hπMap
  have hπPowOrder :
      finitePlaceOrderTop v (algebraMap R L (π ^ n)) =
        ((n : ℤ) : WithTop ℤ) := by
    rw [map_pow]
    simpa only [zpow_natCast] using
      (finitePlaceOrderTop_uniformizer_zpow
        (L := L) v π hπ hπIdeal (n : ℤ))
  constructor
  · intro hx
    rw [mem_localPoleSpace_iff] at hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    obtain ⟨r, hr⟩ := hx
    refine Or.inr ⟨hx0, ?_⟩
    have hregular :=
      finitePlaceOrderTop_algebraMap_nonnegative (L := L) v r
    rw [← hr, finitePlaceOrderTop_mul, hπPowOrder,
      finitePlaceOrderTop_eq_coe v x hx0] at hregular
    have hregularInt : 0 ≤ (n : ℤ) + finitePlaceOrder v x := by
      exact_mod_cast hregular
    change -(n : ℤ) ≤ finitePlaceOrder v x
    omega
  · rintro (rfl | ⟨hx0, hx⟩)
    · exact (localPoleSpace (K := K) (L := L) π n).zero_mem
    change -(n : ℤ) ≤ finitePlaceOrder v x at hx
    rw [mem_localPoleSpace_iff]
    let y : L := algebraMap R L (π ^ n) * x
    have hy0 : y ≠ 0 := mul_ne_zero hπPowMap hx0
    have hyOrderTop : (0 : WithTop ℤ) ≤ finitePlaceOrderTop v y := by
      dsimp only [y]
      rw [finitePlaceOrderTop_mul, hπPowOrder,
        finitePlaceOrderTop_eq_coe v x hx0]
      exact_mod_cast (show 0 ≤ (n : ℤ) + finitePlaceOrder v x by omega)
    have hyOrder : 0 ≤ finitePlaceOrder v y := by
      rw [finitePlaceOrderTop_eq_coe v y hy0] at hyOrderTop
      exact_mod_cast hyOrderTop
    have hyValuation : v.valuation L y ≤ 1 := by
      rw [valuation_eq_exp_neg_finitePlaceOrder v y hy0]
      simpa only [← WithZero.exp_zero] using
        (WithZero.exp_le_exp.mpr (by omega : -finitePlaceOrder v y ≤ 0))
    obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hyValuation
    exact ⟨r, hr.symm⟩

end

end BGS.HasseWeil
