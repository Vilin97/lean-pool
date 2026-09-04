/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Unramified extensions

## Main results
- `comap_map_eq_of_unramified`: If `K/L` is galois, `S/R` is unramified, then any
  ideal `I` fixed by `Gal(L/K)` satisfies `(I ∩ R)S = I`.
- `isUnramifiedAt_of_Separable_minpoly`: If `L = K[α]` with `α` integral over `R`, and
  `f'(α) mod p` is separable for the prime below `P`, then `S/R` is unramified at `P`.
-/

@[expose] public section
open UniqueFactorizationMonoid Ideal

attribute [local instance] FractionRing.liftAlgebra

variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]

variable {R} {S}

omit [IsDedekindDomain R] [IsIntegralClosure S R L] [FiniteDimensional K L] in
include K L in
/-- In the AKLB setup, the map from `R` to the integral closure `S` of `R` in `L` is
injective. -/
lemma algebraMap_injective_of_isIntegralClosure : Function.Injective (algebraMap R S) := by
  refine Function.Injective.of_comp (f := algebraMap S L) ?_
  rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)

lemma comap_map_eq_of_unramified [IsGalois K L] [Algebra.Unramified R S] (I : Ideal S)
    (hI : ∀ σ : L ≃ₐ[K] L, I.comap (galRestrict R K L S σ) = I) :
    (I.comap (algebraMap R S)).map (algebraMap R S) = I := by
  classical
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have hRS := algebraMap_injective_of_isIntegralClosure K L (R := R) (S := S)
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hRS
  by_cases hIbot : I = ⊥
  · rw [hIbot, Ideal.comap_bot_of_injective _ hRS, Ideal.map_bot]
  have : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  have hIbot' : I.comap (algebraMap R S) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hIbot
  have : ∀ p, (p.IsPrime ∧ I.comap (algebraMap R S) ≤ p) →
      ∃ P ≥ I, P ∈ primesOver p S := by
    intro p ⟨hp₁, hp₂⟩
    obtain ⟨P, hP1, hP2, hP3⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ _ hp₂
    exact ⟨P, hP1, hP2, ⟨hP3.symm⟩⟩
  choose 𝔓 h𝔓 h𝔓' using this
  suffices I = ∏ p ∈ (factors (I.comap <| algebraMap R S)).toFinset,
    (p.map (algebraMap R S)) ^ (if h : _ then (factors I).count (𝔓 p h) else 0) by
    simp_rw [← Ideal.mapHom_apply, ← map_pow, ← map_prod, Ideal.mapHom_apply] at this
    rw [this, Ideal.map_comap_map]
  conv_lhs => rw [← associated_iff_eq.mp (factors_pow_count_prod hIbot)]
  rw [← Finset.prod_fiberwise_of_maps_to (g := Ideal.comap (algebraMap R S))]
  · apply Finset.prod_congr rfl
    intros p hp
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot'] at hp
    have hpbot : p ≠ ⊥ := fun hp' ↦ hIbot' (eq_bot_iff.mpr (hp.2.trans_eq hp'))
    have : p.IsPrime := hp.1
    have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hpbot this
    rw [Ideal.map_algebraMap_eq_finsetProd_pow hpbot, ← Finset.prod_pow]
    apply Finset.prod_congr
    · ext P
      rw [factors_eq_normalizedFactors, Finset.mem_filter, Multiset.mem_toFinset,
        Ideal.mem_normalizedFactors_iff hIbot, Set.mem_toFinset]
      refine ⟨fun H ↦ ⟨H.1.1, ⟨H.2.symm⟩⟩, fun H ↦ ⟨⟨H.1, ?_⟩, ?_⟩⟩
      · have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S (h𝔓' _ hp) H
        rw [← hσ, ← hI σ]
        exact Ideal.comap_mono (h𝔓 _ hp)
      · simpa only [Ideal.under_def] using H.2.1.symm
    · intro P hP
      rw [Set.mem_toFinset] at hP
      have : P.IsPrime := hP.1
      have : P.LiesOver p := hP.2
      rw [Ideal.ramificationIdx_eq_one P R, pow_one]
      congr
      rw [dite_eq_left hp, ← Nat.cast_inj (R := ENat), ← normalize_eq P,
        factors_eq_normalizedFactors,
        ← emultiplicity_eq_count_normalizedFactors
          (prime_of_mem_primesOver hpbot hP).irreducible hIbot,
        ← normalize_eq (𝔓 p hp), ← emultiplicity_eq_count_normalizedFactors
          (prime_of_mem_primesOver hpbot <| h𝔓' p hp).irreducible hIbot,
          emultiplicity_eq_emultiplicity_iff]
      intro n
      have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S (h𝔓' _ hp) hP
      rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le]
      conv_lhs => rw [← hI σ, ← hσ,
        Ideal.comap_le_iff_le_map _ (AlgEquiv.bijective _), Ideal.map_pow,
        Ideal.map_comap_of_surjective _ (AlgEquiv.surjective _)]
  · intro P hP
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot] at hP
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot']
    exact ⟨hP.1.comap _, Ideal.comap_mono hP.2⟩

open nonZeroDivisors Polynomial

attribute [local instance] Ideal.Quotient.field in
lemma isUnramifiedAt_of_Separable_minpoly' [Algebra.IsSeparable K L]
    (P : Ideal S) [hP : P.IsPrime] (hPbot : P ≠ ⊥) (x : S)
    (hx' : Algebra.adjoin K {algebraMap S L x} = ⊤)
    (h : Polynomial.Separable ((minpoly R x).map (Ideal.Quotient.mk (P.under R)))) :
    Algebra.IsUnramifiedAt R P := by
  classical
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have hRS := algebraMap_injective_of_isIntegralClosure K L (R := R) (S := S)
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hRS
  have := IsIntegralClosure.isNoetherian R K L S
  have := IsIntegralClosure.isDedekindDomain R K L S
  have := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  have : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv R K).symm.toRingEquiv
      (FractionRing.algEquiv S L).symm.toRingEquiv (RingHom.ext fun x ↦
        IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
          (FractionRing.algEquiv S L).symm x)
  rw [← not_dvd_differentIdeal_iff (A := R) (B := S) (P := P)]
  intro hPdiv
  have hxP : aeval x (derivative (minpoly R x)) ∈ P :=
    (Ideal.dvd_iff_le.mp hPdiv) (aeval_derivative_mem_differentIdeal R K L _ hx')
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq] at hxP
  let p : Ideal R := P.under R
  have hpbot : p ≠ ⊥ := Ideal.under_ne_bot R hPbot
  have : p.IsMaximal := (show p.IsPrime from inferInstance).isMaximal hpbot
  have hle : p ≤ P.comap (algebraMap R S) := Localization.le_comap_primeCompl_iff.mp fun _ a ↦ a
  have hs := (separable_map (Ideal.quotientMap P (algebraMap R S) hle)).mpr h
  rw [Polynomial.map_map, Ideal.quotientMap_comp_mk] at hs
  apply hs.aeval_derivative_ne_zero (x := Ideal.Quotient.mk P x)
  · rw [← Polynomial.map_map]
    simp
  · rw [derivative_map, ← Polynomial.map_map]
    simpa [aeval_map_algebraMap] using hxP

lemma isUnramifiedAt_of_Separable_minpoly [Algebra.IsSeparable K L]
    (P : Ideal S) [hP : P.IsPrime] (hPbot : P ≠ ⊥) (x : L) (hx : IsIntegral R x)
    (hx' : Algebra.adjoin K {x} = ⊤)
    (h : Polynomial.Separable ((minpoly R x).map (Ideal.Quotient.mk (P.under R)))) :
    Algebra.IsUnramifiedAt R P := by
  rw [← IsIntegralClosure.algebraMap_mk' S x hx, minpoly.algebraMap_eq
    (IsIntegralClosure.algebraMap_injective S R L)] at h
  exact isUnramifiedAt_of_Separable_minpoly' K L P hPbot (IsIntegralClosure.mk' S x hx)
    (by rwa [IsIntegralClosure.algebraMap_mk']) h
