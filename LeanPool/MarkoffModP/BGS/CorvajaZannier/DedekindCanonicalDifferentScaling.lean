/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindDifferentKaehler
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindRamifiedDerivationScaling

/-!
# Canonical different scalings at Dedekind places

This file removes the explicit comparison hypothesis between the trace
different and the Kähler differentials from the finite- and infinite-place
derivation-scaling certificates.

The different need not be principal globally.  At a prescribed height-one
place `v`, Dedekind approximation supplies a global element `δ` in the
different whose principal ideal has exactly the same `v`-multiplicity.  Thus
`δ` is a generator after localization at `v`.  The theorem that the different
annihilates relative Kähler differentials then makes `δ` a derivation-clearing
factor.  No local power basis or finiteness assertion for a map between two
independently localized rings is used.
-/

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

open IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

/-- Every nonzero ideal in a Dedekind domain admits, at a prescribed height-one
place, a global element which generates that ideal after localization. -/
theorem exists_element_locally_generating_ideal
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) (hI : I ≠ ⊥) (v : HeightOneSpectrum R) :
    ∃ a : R, a ≠ 0 ∧ a ∈ I ∧
      multiplicity v.asIdeal (Ideal.span {a}) =
        multiplicity v.asIdeal I := by
  have hprod : v.asIdeal * I ≠ ⊥ := mul_ne_zero v.ne_bot hI
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (I := v.asIdeal * I) (J := I) Ideal.mul_le_right hprod
  have ha0 : a ≠ 0 := by
    intro ha_zero
    have hprod_eq : v.asIdeal * I = I := by
      simpa [ha_zero] using ha
    have hmult := congrArg (multiplicity v.asIdeal) hprod_eq
    rw [multiplicity_mul v.prime
      (FiniteMultiplicity.of_prime_left v.prime hprod), multiplicity_self (FiniteMultiplicity.of_prime_left v.prime v.ne_bot)] at hmult
    omega
  have hspan0 : Ideal.span {a} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using ha0
  have ha_mem : a ∈ I := by
    rw [← Ideal.span_singleton_le_iff_mem]
    rw [← ha]
    exact le_sup_right
  have hsup := v.multiplicity_sup hprod hspan0
  rw [ha, multiplicity_mul v.prime
    (FiniteMultiplicity.of_prime_left v.prime hprod), multiplicity_self (FiniteMultiplicity.of_prime_left v.prime v.ne_bot)] at hsup
  have hmult : multiplicity v.asIdeal (Ideal.span {a}) =
      multiplicity v.asIdeal I := by
    by_cases hle : multiplicity v.asIdeal (Ideal.span {a}) ≤
        1 + multiplicity v.asIdeal I
    · rw [min_eq_right hle] at hsup
      exact hsup.symm
    · have hle' : 1 + multiplicity v.asIdeal I ≤
          multiplicity v.asIdeal (Ideal.span {a}) := by omega
      rw [min_eq_left hle'] at hsup
      omega
  exact ⟨a, ha0, ha_mem, hmult⟩

/-- At every height-one place, a global element locally generates the
different and clears the obstruction to preserving the integral closure. -/
theorem exists_finitePlace_different_localGenerator_scaling_certificate
    {C S T U F : Type*}
    [CommRing C] [CommRing S] [CommRing T] [CommRing U]
    [Algebra C S] [Algebra C T] [Algebra S T]
    [Algebra C U] [Algebra S U] [Algebra T U]
    [IsScalarTower C S T] [IsScalarTower C S U]
    [IsScalarTower C T U] [IsScalarTower S T U]
    [IsDomain S] [IsIntegrallyClosed S] [IsDedekindDomain T]
    [Module.IsTorsionFree S T] [Module.Finite S T] [Module.Free S T]
    [Algebra.IsSeparable (FractionRing S) (FractionRing T)]
    [Field F] [Algebra T F] [IsFractionRing T F]
    (v : HeightOneSpectrum T)
    (D : Derivation C S S) (E : Derivation C U U)
    (hE : ∀ s : S, E (algebraMap S U s) = algebraMap S U (D s)) :
    ∃ δ : T,
      δ ≠ 0 ∧
      δ ∈ differentIdeal S T ∧
      multiplicity v.asIdeal (Ideal.span {δ}) =
        multiplicity v.asIdeal (differentIdeal S T) ∧
      finitePlaceOrder v (algebraMap T F δ) =
        (multiplicity v.asIdeal (differentIdeal S T) : ℤ) ∧
      δ ∈ kaehlerDifferentialAnnihilator S T ∧
      ∀ t : T, ∃ t' : T,
        algebraMap T U δ * E (algebraMap T U t) = algebraMap T U t' := by
  have hDifferent : differentIdeal S T ≠ ⊥ :=
    differentIdeal_ne_bot (A := S) (B := T)
  obtain ⟨δ, hδ, hδmem, hδmult⟩ :=
    exists_element_locally_generating_ideal (differentIdeal S T) hDifferent v
  have hDifferentKaehler :
      differentIdeal S T ≤ kaehlerDifferentialAnnihilator S T := by
    simpa [kaehlerDifferentialAnnihilator] using
      (differentIdeal_le_kaehlerDifferentialAnnihilator (A := S) (B := T))
  have hδann : δ ∈ kaehlerDifferentialAnnihilator S T :=
    hDifferentKaehler hδmem
  have hδorder :
      finitePlaceOrder v (algebraMap T F δ) =
        (multiplicity v.asIdeal (differentIdeal S T) : ℤ) := by
    rw [finitePlaceOrder_algebraMap_eq_multiplicity v δ hδ, hδmult]
  exact ⟨δ, hδ, hδmem, hδmult, hδorder, hδann,
    scaled_ambientDerivation_preserves_of_mem_kaehlerDifferentialAnnihilator
      D E hE δ hδann⟩

/-- At a place over the pole of the reciprocal parameter `s`, the scalar
`-δ/s²` has order equal to the different multiplicity minus twice the
ramification index and makes the reparameterized derivation integral. -/
theorem exists_infinity_different_localGenerator_scaling_certificate
    {C S T L : Type*}
    [CommRing C] [CommRing S] [CommRing T] [Field L]
    [Algebra C S] [Algebra C T] [Algebra S T]
    [Algebra C L] [Algebra S L] [Algebra T L]
    [IsScalarTower C S T] [IsScalarTower C S L]
    [IsScalarTower C T L] [IsScalarTower S T L]
    [IsDomain S] [IsIntegrallyClosed S] [IsDedekindDomain T]
    [Module.IsTorsionFree S T] [Module.Finite S T] [Module.Free S T]
    [Algebra.IsSeparable (FractionRing S) (FractionRing T)]
    [IsFractionRing T L]
    (p : HeightOneSpectrum S) (v : HeightOneSpectrum T)
    [v.asIdeal.LiesOver p.asIdeal]
    (s : S) (hs : s ≠ 0) (hspan : p.asIdeal = Ideal.span {s})
    (Ds : Derivation C S S) (Es DX : Derivation C L L)
    (hEs : ∀ r : S, Es (algebraMap S L r) = algebraMap S L (Ds r))
    (hDX : DX = (-(algebraMap S L s) ^ 2) • Es) :
    ∃ δ : T,
      δ ≠ 0 ∧
      δ ∈ differentIdeal S T ∧
      multiplicity v.asIdeal (Ideal.span {δ}) =
        multiplicity v.asIdeal (differentIdeal S T) ∧
      let c : L := -(algebraMap T L δ) / (algebraMap S L s) ^ 2
      finitePlaceOrder v c =
          (multiplicity v.asIdeal (differentIdeal S T) : ℤ) -
            2 * (v.asIdeal.ramificationIdx S : ℤ) ∧
        ∀ t : T, ∃ t' : T,
          c * DX (algebraMap T L t) = algebraMap T L t' := by
  obtain ⟨δ, hδ, hδmem, hδmult, hδorder, _hδann, hδpreserves⟩ :=
    exists_finitePlace_different_localGenerator_scaling_certificate
      (U := L) (F := L) v Ds Es hEs
  refine ⟨δ, hδ, hδmem, hδmult, ?_, ?_⟩
  · have hsT : algebraMap S T s ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective S T).ne hs
    have hsL : algebraMap S L s ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply S T L]
      simpa using (IsFractionRing.injective T L).ne hsT
    have hδL : algebraMap T L δ ≠ 0 := by
      simpa using (IsFractionRing.injective T L).ne hδ
    have hsOrder :
        finitePlaceOrder v (algebraMap S L s) =
          (v.asIdeal.ramificationIdx S : ℤ) := by
      simpa only [IsScalarTower.algebraMap_apply S T L] using
        finitePlaceOrder_algebraMap_uniformizer_eq_ramificationIdx
          (F := L) p v s hs hspan
    rw [div_eq_mul_inv,
      finitePlaceOrder_mul_eq_add v
        (-(algebraMap T L δ)) (((algebraMap S L s) ^ 2)⁻¹)
        (neg_ne_zero.mpr hδL) (inv_ne_zero (pow_ne_zero 2 hsL)),
      finitePlaceOrder_neg_eq v (algebraMap T L δ) hδL,
      finitePlaceOrder_inv_eq_neg' v ((algebraMap S L s) ^ 2)
        (pow_ne_zero 2 hsL)]
    have hsSquareOrder := finitePlaceOrder_mul_eq_add v
      (algebraMap S L s) (algebraMap S L s) hsL hsL
    rw [← pow_two] at hsSquareOrder
    rw [hδorder, hsSquareOrder, hsOrder]
    ring
  · intro t
    obtain ⟨t', ht'⟩ := hδpreserves t
    refine ⟨t', ?_⟩
    have hsT : algebraMap S T s ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective S T).ne hs
    have hsL : algebraMap S L s ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply S T L]
      simpa using (IsFractionRing.injective T L).ne hsT
    rw [hDX, Derivation.smul_apply, Algebra.smul_def]
    calc
      (-(algebraMap T L δ) / (algebraMap S L s) ^ 2) *
          (-(algebraMap S L s) ^ 2 * Es (algebraMap T L t)) =
          algebraMap T L δ * Es (algebraMap T L t) := by
            field_simp
      _ = algebraMap T L t' := ht'

end

end BGS.CorvajaZannier
