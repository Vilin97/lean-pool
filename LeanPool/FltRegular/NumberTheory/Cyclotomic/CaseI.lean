/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

import LeanPool.FltRegular.NumberTheory.Cyclotomic.MoreLemmas
import LeanPool.FltRegular.NumberTheory.Cyclotomic.UnitLemmas

/-!
# Cyclotomic lemmas for Case I

This file establishes the complex-conjugation congruence used in the first case of Fermat's Last
Theorem for regular primes.
-/

@[expose] public section

open scoped NumberField nonZeroDivisors

variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

local notation3 "zetaUnit" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit

open FractionalIdeal NumberField IsCMField

namespace FltRegular.CaseI

omit [NeZero p] in
/-- The difference between a `p`-th power and its complex conjugate is divisible by `p`. -/
theorem pow_sub_intGalConj_mem (α : 𝓞 K) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    (α ^ p - ringOfIntegersComplexConj K (α ^ p)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨a, γ, hγ⟩ := exists_dvd_pow_sub_Int_pow hp.ne' α
  rw [Ideal.mem_span_singleton]
  rw [sub_eq_iff_eq_add] at hγ
  rw [hγ, _root_.map_add, _root_.map_mul, map_natCast, map_pow, map_intCast,
    add_sub_add_right_eq_sub, ← mul_sub]
  exact dvd_mul_right _ _

/-- Complex conjugation negates the exponent of the distinguished cyclotomic unit. -/
theorem exists_int_sum_eq_zero'_aux (x y i : ℤ) (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    ringOfIntegersComplexConj K (x + y * ↑(zetaUnit ^ i) : 𝓞 K) =
      x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ) := by
  have := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  ext
  simp only [map_add, map_intCast, map_mul, coe_ringOfIntegersComplexConj, zpow_neg, map_units_inv,
    add_right_inj, mul_eq_mul_left_iff, Int.cast_eq_zero]
  simp_rw [NumberField.Units.coe_zpow]
  left
  simp only [map_zpow₀]
  rw [← inv_zpow]
  congr
  change (complexConj K) ζ = ζ⁻¹
  exact complexConj_zeta hζ hp

/-- A natural exponent giving the Case I complex-conjugation congruence modulo `p`. -/
theorem exists_int_sum_eq_zero' (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) = u * α ^ p) [Fact (p.Prime)]
    (hp : 2 < p) :
    ∃ k : ℕ, (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) -
      ((zetaUnit ^ k) ^ 2 : (𝓞 K)ˣ) *
        (x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨k, hroot⟩ := unit_inv_conj_is_root_of_unity hζ u hp
  refine ⟨k, ?_⟩
  rw [← exists_int_sum_eq_zero'_aux _ _ _ _ hp, h, ← hroot, Units.val_mul, mul_assoc,
    ← mul_sub]
  convert Ideal.mul_mem_left _ ↑u (pow_sub_intGalConj_mem α hp) using 3
  ext
  simp only [map_mul, map_pow, map_units_inv, Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv,
    RingOfIntegers.mapRingEquiv_apply, RingEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    coe_ringOfIntegersComplexConj, ne_eq, EmbeddingLike.map_eq_zero_iff,
    FaithfulSMul.algebraMap_eq_zero_iff, Units.ne_zero, not_false_eq_true, inv_mul_cancel_left₀]

/-- An integer exponent giving the Case I complex-conjugation congruence modulo `p`. -/
theorem exists_int_sum_eq_zero (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) = u * α ^ p) [Fact (p.Prime)]
    (hp : 2 < p) :
    ∃ k : ℤ, (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) -
      (zetaUnit ^ (2 * k) : (𝓞 K)ˣ) *
        (x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨k, hk⟩ := exists_int_sum_eq_zero' hζ x y i h hp
  refine ⟨k, ?_⟩
  have hz : ((zetaUnit ^ k) ^ 2 : (𝓞 K)ˣ) = (zetaUnit ^ (2 * (k : ℤ)) : (𝓞 K)ˣ) := by
    rw [← zpow_natCast (zetaUnit ^ k) 2, ← zpow_natCast zetaUnit k, ← zpow_mul]
    congr 1
    exact mul_comm _ _
  exact hz ▸ hk

end FltRegular.CaseI
