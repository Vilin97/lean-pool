/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindPlaceOrder
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic

/-!
# Compatibility of global and localized Dedekind orders

The height-one valuation of a Dedekind domain and the maximal-ideal
valuation of its localization at that height-one prime have the same
normalization.  This file proves equality, rather than equivalence up to an
unspecified rescaling, and transfers the associated principal-ideal orders.
-/

open scoped nonZeroDivisors
open IsDedekindDomain Multiplicative WithZero

namespace BGS.CorvajaZannier

noncomputable section

/-- Equivalent surjective valuations with value group `ℤᵐ⁰` have the same
normalization.  Surjectivity rules out a nontrivial integral rescaling. -/
theorem valuation_eq_of_isEquiv_of_surjective
    {F : Type*} [Field F]
    {v w : Valuation F ℤᵐ⁰}
    (h : v.IsEquiv w)
    (hv : Function.Surjective v)
    (hw : Function.Surjective w) :
    v = w := by
  ext x
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨π, hπv⟩ := hv (exp (-1 : ℤ))
  obtain ⟨ρ, hρw⟩ := hw (exp (-1 : ℤ))
  have hπw0 : w π ≠ 0 := by
    intro hzero
    have : v π = 0 := h.eq_zero.mpr hzero
    rw [hπv] at this
    exact exp_ne_zero this
  have hρv0 : v ρ ≠ 0 := by
    intro hzero
    have : w ρ = 0 := h.eq_zero.mp hzero
    rw [hρw] at this
    exact exp_ne_zero this
  let a : ℤ := log (w π)
  let b : ℤ := log (v ρ)
  have hπw : w π = exp a := by
    simpa [a] using (exp_log hπw0).symm
  have hρv : v ρ = exp b := by
    simpa [b] using (exp_log hρv0).symm
  have ha : a < 0 := by
    rw [← exp_lt_exp, ← hπw]
    have hvlt : v π < v 1 := by
      rw [hπv, map_one]
      simpa using (WithZero.exp_lt_exp.mpr (show (-1 : ℤ) < 0 by omega))
    simpa using h.lt_iff_lt.mp hvlt
  have hb : b < 0 := by
    rw [← exp_lt_exp, ← hρv]
    have hwlt : w ρ < w 1 := by
      rw [hρw, map_one]
      simpa using (WithZero.exp_lt_exp.mpr (show (-1 : ℤ) < 0 by omega))
    simpa using h.lt_iff_lt.mpr hwlt
  have hwEq : w π = w (ρ ^ (-a)) := by
    rw [hπw, map_zpow₀, hρw, ← exp_zsmul]
    congr 1
    simp
  have hvEq : v π = v (ρ ^ (-a)) := h.eq_iff.mpr hwEq
  have hab : (-a) * b = -1 := by
    rw [hπv, map_zpow₀, hρv, ← exp_zsmul] at hvEq
    apply exp_injective
    simpa [mul_comm] using hvEq.symm
  have ha1 : a = -1 := by nlinarith
  have hπw1 : w π = exp (-1 : ℤ) := by simpa [ha1] using hπw
  have hwx0 : w x ≠ 0 := by simpa using hx
  let n : ℤ := log (w x)
  have hwx : w x = exp n := by
    simpa [n] using (exp_log hwx0).symm
  have hwPow : w x = w (π ^ (-n)) := by
    rw [hwx, map_zpow₀, hπw1, ← exp_zsmul]
    congr 1
    simp
  have hvPow : v x = v (π ^ (-n)) := h.eq_iff.mpr hwPow
  rw [map_zpow₀, hπv, ← exp_zsmul] at hvPow
  calc
    v x = exp n := by simpa using hvPow
    _ = w x := hwx.symm

section FractionRingEquiv

variable {R L : Type*} [CommRing R] [IsDedekindDomain R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- The canonical equivalence from the chosen fraction-ring model preserves
every normalized height-one valuation. -/
theorem fractionRingAlgEquiv_valuation
    (q : HeightOneSpectrum R) (x : FractionRing R) :
    q.valuation L (FractionRing.algEquiv R L x) =
      q.valuation (FractionRing R) x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  rw [map_div₀, (FractionRing.algEquiv R L).commutes a,
    (FractionRing.algEquiv R L).commutes b,
    Valuation.map_div, Valuation.map_div,
    q.valuation_of_algebraMap, q.valuation_of_algebraMap,
    q.valuation_of_algebraMap, q.valuation_of_algebraMap]

/-- The canonical fraction-ring equivalence preserves the additive order at
every height-one prime, including Mathlib's zero-order convention. -/
theorem fractionRingAlgEquiv_finitePlaceOrder_eq
    (q : HeightOneSpectrum R) (x : FractionRing R) :
    finitePlaceOrder q (FractionRing.algEquiv R L x) =
      finitePlaceOrder q x := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, finitePlaceOrder,
      FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]
  · have hmap : FractionRing.algEquiv R L x ≠ 0 := by simpa using hx
    have hactual := valuation_eq_exp_neg_finitePlaceOrder
      q (FractionRing.algEquiv R L x) hmap
    have hcanonical := valuation_eq_exp_neg_finitePlaceOrder q x hx
    rw [fractionRingAlgEquiv_valuation q x, hcanonical] at hactual
    exact neg_injective (exp_injective hactual.symm)

end FractionRingEquiv

variable {R S L : Type*}
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L]
  [Algebra R S] [Algebra R L] [Algebra S L]
  [IsScalarTower R S L]
  [IsFractionRing R L]
  [IsFractionRing S L]

/-- The normalized valuation of the maximal ideal of `R_q` is the normalized
height-one valuation attached to `q`. -/
theorem localizationAtPrime_valuation_eq
    (q : HeightOneSpectrum R)
    [IsLocalization q.asIdeal.primeCompl S] :
    (IsDiscreteValuationRing.maximalIdeal S).valuation L = q.valuation L := by
  apply valuation_eq_of_isEquiv_of_surjective
  · rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    constructor
    · intro hlocal
      obtain ⟨s, hs⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hlocal
      obtain ⟨⟨a, d, hd⟩, had⟩ := IsLocalization.surj q.asIdeal.primeCompl s
      have hdOne : q.valuation L (algebraMap R L d) = 1 := by
        rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
        exact hd
      have hEq :
          algebraMap S L s * algebraMap R L d = algebraMap R L a := by
        calc
          algebraMap S L s * algebraMap R L d =
              algebraMap S L (s * algebraMap R S d) := by
                rw [map_mul, IsScalarTower.algebraMap_apply R S L]
          _ = algebraMap S L (algebraMap R S a) := by
                exact congrArg (algebraMap S L) (by simpa using had)
          _ = algebraMap R L a :=
                (IsScalarTower.algebraMap_apply R S L a).symm
      have hValEq := congrArg (q.valuation L) hEq
      rw [map_mul, hdOne, mul_one] at hValEq
      rw [← hs, hValEq]
      exact HeightOneSpectrum.valuation_le_one (K := L) q a
    · intro hglobal
      obtain ⟨a, d, had⟩ :=
        HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer q x hglobal
      let s : S := IsLocalization.mk' S a d
      have hs : algebraMap S L s = x := by
        have hdR : (d : R) ≠ 0 := by
          intro hd0
          exact d.2 (hd0 ▸ q.asIdeal.zero_mem)
        have hdL : algebraMap R L (d : R) ≠ 0 := by
          simpa only [map_zero] using (IsFractionRing.injective R L).ne hdR
        apply (mul_right_cancel₀ hdL)
        calc
          algebraMap S L s * algebraMap R L (d : R) =
              algebraMap S L (s * algebraMap R S (d : R)) := by
                rw [map_mul, IsScalarTower.algebraMap_apply R S L]
          _ = algebraMap R L a := by
                dsimp [s]
                rw [IsLocalization.mk'_spec,
                  IsScalarTower.algebraMap_apply R S L]
          _ = x * algebraMap R L (d : R) := had.symm
      rw [← hs]
      exact HeightOneSpectrum.valuation_le_one
        (K := L) (IsDiscreteValuationRing.maximalIdeal S) s
  · exact (IsDiscreteValuationRing.maximalIdeal S).valuation_surjective L
  · exact q.valuation_surjective L

/-- Principal-ideal orders computed globally and in the localized DVR agree. -/
theorem localizationAtPrime_finitePlaceOrder_eq
    (q : HeightOneSpectrum R)
    [IsLocalization q.asIdeal.primeCompl S]
    (x : L) :
    finitePlaceOrder (IsDiscreteValuationRing.maximalIdeal S) x =
      finitePlaceOrder q x := by
  by_cases hx : x = 0
  · subst x
    simp only [finitePlaceOrder, FractionalIdeal.spanSingleton_zero,
      FractionalIdeal.count_zero]
  · have hlocal := valuation_eq_exp_neg_finitePlaceOrder
      (IsDiscreteValuationRing.maximalIdeal S) x hx
    have hglobal := valuation_eq_exp_neg_finitePlaceOrder q x hx
    rw [localizationAtPrime_valuation_eq q, hglobal] at hlocal
    exact neg_injective (exp_injective hlocal.symm)

/-- `WithTop`-valued orders computed globally and in the localized DVR agree,
including the zero element. -/
theorem localizationAtPrime_finitePlaceOrderTop_eq
    (q : HeightOneSpectrum R)
    [IsLocalization q.asIdeal.primeCompl S]
    (x : L) :
    finitePlaceOrderTop (IsDiscreteValuationRing.maximalIdeal S) x =
      finitePlaceOrderTop q x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [finitePlaceOrderTop_eq_coe _ _ hx,
      finitePlaceOrderTop_eq_coe _ _ hx,
      localizationAtPrime_finitePlaceOrder_eq q x]

end

end BGS.CorvajaZannier
