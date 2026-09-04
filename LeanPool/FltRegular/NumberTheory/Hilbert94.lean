/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

public import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

import LeanPool.FltRegular.NumberTheory.Hilbert92
import LeanPool.FltRegular.NumberTheory.RegularPrimes
import LeanPool.FltRegular.NumberTheory.Unramified

@[expose] public section

open scoped NumberField

variable {K : Type} [Field K]

open Polynomial Module

variable {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
    [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L]

instance : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L

include hσ in
lemma comap_span_galRestrict_eq_of_cyclic (β : B) (η : Bˣ)
    (hβ : η * (galRestrict A K L B σ) β = β) (σ' : L ≃ₐ[K] L) :
    (Ideal.span {β}).comap (galRestrict A K L B σ') = Ideal.span {β} := by
  suffices (Ideal.span {β}).map
      (galRestrict A K L B σ'⁻¹).toRingEquiv.toRingHom = Ideal.span {β} by
    rwa [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv, map_inv] at this
  apply_fun (Ideal.span {·}) at hβ
  rw [← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_top.mpr η.isUnit,
    ← Ideal.one_eq_top, one_mul, ← Set.image_singleton, ← Ideal.map_span] at hβ
  change Ideal.map (galRestrict A K L B σ : B →+* B) _ = _ at hβ
  generalize σ'⁻¹ = τ
  obtain ⟨n, rfl : σ ^ n = τ⟩ := mem_powers_iff_mem_zpowers.mpr (hσ τ)
  rw [map_pow]
  induction n with
  | zero =>
    simp only [pow_zero, RingEquiv.toRingHom_eq_coe]
    exact Ideal.map_id _
  | succ n IH =>
    simp only [RingEquiv.toRingHom_eq_coe, pow_succ] at IH ⊢
    conv_lhs at IH => rw [← hβ, Ideal.map_map]
    exact IH

variable [IsGalois K L]

include hσ in
open FiniteDimensional in
theorem exists_not_isPrincipal_and_isPrincipal_map_aux
    [IsDedekindDomain A] [Algebra.Unramified A B] (η : Bˣ)
    (hη : Algebra.norm K (algebraMap B L η) = 1)
    (hη' : ¬∃ α : Bˣ, algebraMap B L η = (algebraMap B L α) / σ (algebraMap B L α)) :
    ∃ I : Ideal A, ¬I.IsPrincipal ∧ (I.map (algebraMap A B)).IsPrincipal := by
  have := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ, (Subgroup.eq_top_iff' _).2 hσ⟩
  obtain ⟨β, hβ_zero, hβ⟩ := groupCohomology.exists_mul_galRestrict_of_norm_eq_one (A := A)
    (B := B) hσ hη
  have : IsDomain B := (IsIntegralClosure.equiv A B L (integralClosure A L)).toMulEquiv.isDomain
    (integralClosure A L)
  have hβ' := comap_map_eq_of_unramified K L _
    (comap_span_galRestrict_eq_of_cyclic σ hσ (A := A) (B := B) β η hβ)
  refine ⟨(Ideal.span {β}).comap (algebraMap A B), ?_, ?_⟩
  · rintro ⟨⟨γ, hγ : _ = Ideal.span _⟩⟩
    rw [hγ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_span_singleton] at hβ'
    obtain ⟨a, rfl⟩ := hβ'
    rw [map_mul, AlgEquiv.commutes, mul_left_comm, (mul_right_injective₀ _).eq_iff] at hβ
    · apply hη'
      use a
      conv_rhs =>
        enter [1]
        rw [← hβ]
      rw [map_mul, ← algebraMap_galRestrict_apply A]
      refine (mul_div_cancel_right₀ _ ?_).symm
      · rw [ne_eq,
          (injective_iff_map_eq_zero' _).mp (IsIntegralClosure.algebraMap_injective B A L),
          (injective_iff_map_eq_zero' _).mp (galRestrict A K L B σ).injective]
        exact a.isUnit.ne_zero
    · exact (mul_ne_zero_iff.mp hβ_zero).1
  · rw [hβ']
    exact ⟨⟨_, rfl⟩⟩

theorem Ideal.isPrincipal_pow_finrank_of_isPrincipal_map [IsDedekindDomain A] {I : Ideal A}
    (hI : (I.map (algebraMap A B)).IsPrincipal) : (I ^ finrank K L).IsPrincipal := by
  have : IsDomain B := (IsIntegralClosure.equiv A B L (integralClosure A L)).toMulEquiv.isDomain
    (integralClosure A L)
  have := IsIntegralClosure.isNoetherian A K L B
  have := IsIntegralClosure.isDedekindDomain A K L B
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hAB := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (algebraMap_injective_of_isIntegralClosure K L (R := A) (S := B))
  rw [IsFractionRing.finrank_eq A K B L, ← Ideal.relNorm_algebraMap,
    ← (I.map (algebraMap A B)).span_singleton_generator, Ideal.relNorm_singleton]
  exact ⟨⟨_, rfl⟩⟩

/-- This is the first part of **Hilbert Theorem 94**, which states that if `L/K` is an unramified
  cyclic finite extension of number fields of odd prime degree,
  then there is an ideal that capitulates in `K`. -/
theorem exists_not_isPrincipal_and_isPrincipal_map (K L : Type)
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra.Unramified (𝓞 K) (𝓞 L)]
    [h : IsCyclic (L ≃ₐ[K] L)] (hKL : Nat.Prime (finrank K L)) (hKL' : finrank K L ≠ 2) :
    ∃ I : Ideal (𝓞 K), ¬I.IsPrincipal ∧
      (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by
  obtain ⟨⟨σ, hσ⟩⟩ := h
  obtain ⟨η, hη, hη'⟩ := Hilbert92 hKL hKL' σ hσ
  exact exists_not_isPrincipal_and_isPrincipal_map_aux σ hσ η hη (not_exists.mpr hη')

/-- This is the second part of **Hilbert Theorem 94**, which states that if `L/K` is an unramified
  cyclic finite extension of number fields of odd prime degree,
  then the degree divides the class number of `K`. -/
theorem dvd_card_classGroup_of_unramified_isCyclic {K L : Type}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra.Unramified (𝓞 K) (𝓞 L)]
    [IsCyclic (L ≃ₐ[K] L)] (hKL : Nat.Prime (finrank K L)) (hKL' : finrank K L ≠ 2) :
    finrank K L ∣ Fintype.card (ClassGroup (𝓞 K)) := by
  obtain ⟨I, hI, hI'⟩ := exists_not_isPrincipal_and_isPrincipal_map K L hKL hKL'
  have := Fact.mk hKL
  rw [hKL.dvd_iff_not_coprime]
  exact fun h ↦ hI (Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime h
    (Ideal.isPrincipal_pow_finrank_of_isPrincipal_map hI'))
