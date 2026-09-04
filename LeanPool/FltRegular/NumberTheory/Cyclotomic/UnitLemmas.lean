/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import LeanPool.FltRegular.NumberTheory.Cyclotomic.MoreLemmas

/-!
# Units in cyclotomic fields

This file records how complex conjugation acts on cyclotomic units and proves that the quotient
of a unit by its conjugate is a square of a root of unity.
-/

@[expose] public section

variable {p : ℕ} [NeZero p] {K : Type*} [Field K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

open scoped nonZeroDivisors NumberField

open IsCyclotomicExtension NumberField Polynomial IsCMField

noncomputable section

local notation3 "η" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit

local notation "I" => (Ideal.span ({(η - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))

theorem eq_one_mod_one_sub {A : Type*} [CommRing A] {t : A} :
    algebraMap A (A ⧸ Ideal.span ({t - 1} : Set A)) t = 1 := by
  rw [← map_one <| algebraMap A <| A ⧸ Ideal.span ({t - 1} : Set A),
    ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

variable [NumberField K] [IsCyclotomicExtension {p} ℚ K]

include hζ in
/-- Complex conjugation sends a primitive `p`-th root of unity to its inverse. -/
theorem complexConj_zeta (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    complexConj K ζ = ζ⁻¹ := by
  let _ := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  have hη : η ∈ Units.torsion K := by
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, NeZero.pos p, ?_⟩)
    ext
    exact hζ.pow_eq_one
  exact complexConj_torsion (K := K) ⟨η, hη⟩

theorem roots_of_unity_in_cyclo (hpo : Odd p) (x : K)
    (h : ∃ (n : ℕ) (_ : 0 < n), x ^ n = 1) :
    ∃ (m k : ℕ), x = (-1) ^ k * (η.1 : K) ^ m := by
  obtain ⟨n, hn, hxn⟩ := h
  have hη : (η.1 : K) = ζ := by rw [IsUnit.unit_spec]; rfl
  simp only [hη]
  obtain ⟨r, -, hr | hr⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hpo
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hxn⟩)
  · exact ⟨r, 2, by simp [hr]⟩
  · exact ⟨r, 1, by simp [hr]⟩
lemma unit_inv_conj_not_neg_zeta_runity_aux (u : (𝓞 K)ˣ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    algebraMap (𝓞 K) (𝓞 K ⧸ I) (unitsMulComplexConjInv K u).1 = 1 := by
  let _ := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  have hmap := Units.coe_map_inv (N := 𝓞 K ⧸ I) (algebraMap (𝓞 K) (𝓞 K ⧸ I))
    (unitsComplexConj K u)
  rw [unitsMulComplexConjInv_apply, Units.val_mul, map_mul, ← MonoidHom.coe_coe, ← hmap,
    Units.mul_inv_eq_one, Units.coe_map, MonoidHom.coe_coe]
  exact (RingHom.congr_fun (quotient_zero_sub_one_comp_aut hζ
    (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) (u : 𝓞 K)).symm

theorem unit_inv_conj_not_neg_zeta_runity (u : (𝓞 K)ˣ) (n : ℕ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    u * (unitsComplexConj K u)⁻¹ ≠ -η ^ n := by
  by_contra H
  have hμ : algebraMap (𝓞 K) (𝓞 K ⧸ I) ((η : 𝓞 K) ^ n) = 1 := by
    have hpow : ((η : 𝓞 K) ^ n) ^ p = 1 := by
      change (hζ.toInteger ^ n) ^ p = 1
      rw [← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    obtain ⟨k, -, hk⟩ := hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hpow
    rw [← hk, map_pow]
    change (algebraMap (𝓞 K) (𝓞 K ⧸ I) (η : 𝓞 K)) ^ k = 1
    rw [eq_one_mod_one_sub, one_pow]
  have hμ' : algebraMap (𝓞 K) (𝓞 K ⧸ I) ((η : 𝓞 K) ^ n) = -1 := by
    rw [← neg_eq_iff_eq_neg, ← map_neg, ← Units.val_pow_eq_pow_val, ← Units.val_neg, ← H]
    apply unit_inv_conj_not_neg_zeta_runity_aux hζ u hp
  let _ := Fact.mk hp
  apply (IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' _ hζ hp : (2 : 𝓞 K) ∉ I)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat, ← one_add_one_eq_two,
    ← neg_eq_iff_add_eq_zero]
  exact hμ'.symm.trans hμ

theorem unit_inv_conj_is_root_of_unity (u : (𝓞 K)ˣ) [H : Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    ∃ m : ℕ, u * (unitsComplexConj K u)⁻¹ = (η ^ m) ^ 2 := by
  let _ := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  have hpo : Odd p := H.out.odd_of_ne_two hp.ne'
  let : NormedAlgebra ℚ ℂ := normedAlgebraRat
  have hroot := Embeddings.pow_eq_one_of_norm_eq_one K ℂ
    (x := u * (unitsComplexConj K u)⁻¹) ?_ ?_
  · obtain ⟨n, k, hz⟩ :=
      roots_of_unity_in_cyclo hζ hpo (u * (unitsComplexConj K u)⁻¹ : K) hroot
    simp_rw [← pow_mul]
    rcases Nat.even_or_odd k with hk | hk
    · simp only [hk.neg_one_pow, one_mul] at hz
      rw [← map_mul, ← Units.val_mul, ← map_pow, ← Units.val_pow_eq_pow_val] at hz
      norm_cast at hz
      rw [hz]
      simpa only [mul_comm] using
        ((hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)).exists_pow_eq_pow_two_mul hpo n)
    · by_contra
      simp only [hk.neg_one_pow, neg_mul, one_mul] at hz
      rw [← map_mul, ← Units.val_mul, ← map_pow, ← Units.val_pow_eq_pow_val,
        ← map_neg] at hz
      norm_cast at hz
      simpa [hz] using unit_inv_conj_not_neg_zeta_runity hζ u n hp
  · apply RingHom.IsIntegralElem.mul
    · exact NumberField.RingOfIntegers.isIntegral_coe _
    · exact NumberField.RingOfIntegers.isIntegral_coe _
  · simp
