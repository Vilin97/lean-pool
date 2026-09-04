/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

import Mathlib.RingTheory.NormTrace
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Additional lemmas for cyclotomic fields

This file proves divisibility results for cyclotomic integers, traces, and norms that are used by
the surrounding FLT development.
-/

@[expose] public section

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K]
  [IsCyclotomicExtension {p} ℚ K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat

variable (hp : p ≠ 2)

lemma exists_zeta_sub_one_dvd_sub_Int (a : 𝓞 K) :
    ∃ b : ℤ, (hζ.toInteger - 1 : 𝓞 K) ∣ a - b := by
  have hdiv := hζ.subOneIntegralPowerBasis.exists_gen_dvd_sub a
  rwa [hζ.subOneIntegralPowerBasis_gen] at hdiv

include hp in
lemma exists_dvd_pow_sub_Int_pow (a : 𝓞 K) : ∃ b : ℤ, ↑p ∣ a ^ p - (b : 𝓞 K) ^ p := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K (Set.mem_singleton p)
    hpri.1.ne_zero
  obtain ⟨b, k, e⟩ := exists_zeta_sub_one_dvd_sub_Int hζ a
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hpri.out a (-b)
  obtain ⟨u, hu⟩ := (associated_zeta_sub_one_pow_prime _ hζ).symm
  rw [(Nat.Prime.odd_of_ne_two hpri.out hp).neg_pow, ← sub_eq_add_neg, e,
    mul_pow, ← sub_eq_add_neg] at hr
  use b, ↑u * ((hζ.toInteger - 1 : 𝓞 K) * k ^ p) - r * a * (-b)
  rw [← sub_eq_iff_eq_add.mpr hr, mul_sub, ← mul_assoc, ← mul_assoc, hu, ← pow_succ,
    Nat.sub_add_cancel (n := p) (m := 1) hpri.out.one_lt.le]
  ring

lemma quotient_zero_sub_one_comp_aut (σ : 𝓞 K →+* 𝓞 K) :
    (Ideal.Quotient.mk (Ideal.span {(hζ.toInteger : 𝓞 K) - 1})).comp σ =
      Ideal.Quotient.mk _ := by
  let _ := IsCyclotomicExtension.numberField {p} ℚ K
  let : AddGroup (𝓞 K ⧸ Ideal.span (singleton (hζ.toInteger - 1 : 𝓞 K))) := inferInstance
  apply RingHom.toIntAlgHom_injective
  apply hζ.integralPowerBasis.algHom_ext
  have hgen : hζ.integralPowerBasis.gen = hζ.toInteger := by
    simp only [IsPrimitiveRoot.integralPowerBasis_gen]
  rw [hgen]
  simp only [RingHom.toIntAlgHom, AlgHom.coe_mk, RingHom.coe_comp, Function.comp_apply]
  rw [← sub_eq_zero, ← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk,
    ← Submodule.Quotient.mk_sub, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  apply hζ.toInteger_isPrimitiveRoot.sub_one_dvd_sub hpri.out
  · rw [mem_nthRootsFinset (NeZero.pos p), ← map_pow]
    change σ (hζ.toInteger ^ p) = 1
    rw [hζ.toInteger_isPrimitiveRoot.pow_eq_one, map_one]
  · rw [mem_nthRootsFinset (NeZero.pos p)]
    exact hζ.toInteger_isPrimitiveRoot.pow_eq_one

open NumberField.RingOfIntegers in
lemma zeta_sub_one_dvd_trace_sub_smul (x : 𝓞 K) :
    (hζ.toInteger - 1 : 𝓞 K) ∣ Algebra.trace ℤ _ x - (p - 1) • x := by
  let _ := IsCyclotomicExtension.numberField {p} ℚ K
  let _ := IsCyclotomicExtension.isGalois {p} ℚ K
  have htrace : (Algebra.trace ℤ _ x : 𝓞 K) =
      ∑ σ : K ≃ₐ[ℚ] K, (mapAlgHom σ).toRingHom x := by
    apply (show Function.Injective (algebraMap (𝓞 K) K) from Subtype.val_injective)
    rw [← eq_intCast (algebraMap ℤ (𝓞 K)), ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply ℤ ℚ K, eq_intCast, Algebra.coe_trace_int,
      trace_eq_sum_automorphisms, map_sum]
    rfl
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, htrace,
    map_sum]
  simp_rw [← RingHom.comp_apply, quotient_zero_sub_one_comp_aut]
  rw [Finset.sum_const, map_nsmul, sub_eq_zero, Finset.card_univ, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank,
    IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat (NeZero.pos p)),
    Nat.totient_prime hpri.out]

lemma zeta_sub_one_pow_dvd_norm_sub_pow (x : 𝓞 K) :
    (hζ.toInteger - 1 : 𝓞 K) ^ p ∣
      (Algebra.norm ℤ (1 + p • x) : 𝓞 K) - 1 + p • x := by
  let _ := IsCyclotomicExtension.numberField {p} ℚ K
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (p : ℤ) x
  obtain ⟨s, hs⟩ := zeta_sub_one_dvd_trace_sub_smul hζ x
  obtain ⟨t, ht⟩ := (associated_zeta_sub_one_pow_prime _ hζ).dvd
  rw [sub_eq_iff_eq_add] at hs
  simp only [zsmul_eq_mul, Int.cast_natCast] at hr
  simp only [nsmul_eq_mul, hr, Int.cast_add, Int.cast_one, Int.cast_mul, hs, NeZero.pos p,
    Nat.cast_pred, Int.cast_natCast, Int.cast_pow]
  suffices (hζ.toInteger - 1 : 𝓞 K) ^ p ∣
      (hζ.toInteger - 1) * p * s + (p : 𝓞 K) ^ 2 * (r + x) by
    convert this using 1
    ring
  apply dvd_add
  · apply dvd_mul_of_dvd_left
    rw [ht, ← mul_assoc, ← pow_succ', tsub_add_cancel_of_le (Nat.Prime.one_lt hpri.out).le]
    exact dvd_mul_right _ _
  · rw [ht, mul_pow, ← pow_mul, mul_assoc]
    apply dvd_mul_of_dvd_left
    apply pow_dvd_pow
    zify [(Nat.Prime.one_lt hpri.out).le]
    linarith only [Nat.Prime.two_le hpri.out]

lemma norm_add_one_smul_of_isUnit {K} [Field K] [NumberField K] {p : ℕ} (hpri : p.Prime)
    (hp : p ≠ 2) (x : 𝓞 K)
    (hx : IsUnit (1 + p • x)) : Algebra.norm ℤ (1 + p • x) = 1 := by
  have hnorm : Algebra.norm ℤ (1 + p • x) = 1 ∨ Algebra.norm ℤ (1 + p • x) = -1 := by
    apply Int.natAbs_eq_iff.mp
    apply (Int.cast_injective (α := ℚ)).comp Nat.cast_injective
    simp only [Int.cast_abs, Function.comp_apply, Nat.cast_one, Int.cast_one, ← Int.abs_eq_natAbs,
      Algebra.coe_norm_int, ← NumberField.isUnit_iff_norm.mp hx, RingOfIntegers.coe_norm]
  have hne : Algebra.norm ℤ (1 + p • x) ≠ -1 := by
    intro e
    apply hp
    obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (p : ℤ) x
    have heq : (p : ℤ) * (- Algebra.trace ℤ _ x - r * p) = 2 := by
      rw [zsmul_eq_mul, Int.cast_natCast, ← nsmul_eq_mul, e, eq_comm, ← sub_eq_zero] at hr
      rw [eq_comm, ← sub_eq_zero, ← hr]
      ring
    exact (Nat.prime_two.eq_one_or_self_of_dvd _
      (Int.natCast_dvd_natCast.mp ⟨_, heq.symm⟩)).resolve_left hpri.ne_one
  exact hnorm.resolve_right hne
