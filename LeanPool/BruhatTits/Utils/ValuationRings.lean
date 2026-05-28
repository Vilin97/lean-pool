/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Utils.Misc
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

open Module

section

variable {K : Type*} [Field K] (R : Subring K)

variable {R} in
open Pointwise in
lemma maximalIdeal_smul_eq_uniformizer_smul [IsDiscreteValuationRing R] {ι : Type*}
    (M : Submodule R (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal R • M = ϖ • M := by
  rw [hϖ.maximalIdeal_eq]
  exact Submodule.ideal_span_singleton_smul ϖ M

@[simp]
lemma Subring.coe_zpow (a : Rˣ) (n : ℤ) :
    (a ^ n).val.val = a.val.val ^ n := by
  change (Units.map R.subtype (a ^ n) : Kˣ).val = (Units.map R.subtype a).val ^ n
  simp

end

variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]

variable (ϖ : R) (hϖ : Irreducible ϖ)

local notation "v" => ValuationRing.valuation R K

lemma mem_subring_iff_integer (x : K) : x ∈ R ↔ v x ≤ 1 := by
  rw [← Valuation.mem_integer_iff, ValuationRing.mem_integer_iff, ← Set.mem_range]
  change x ∈ R ↔ x ∈ R.subtype.range
  rw [Subring.range_subtype]

omit [ValuationRing ↥R] [IsFractionRing (↥R) K] in
lemma coe_inv_eq_inv_coe (u : Rˣ) : (u : K)⁻¹ = u⁻¹ := by
  symm
  apply eq_inv_of_mul_eq_one_right
  change ((u : R) : K) * ((u⁻¹ : Rˣ) : R) = 1
  rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]

lemma mem_or_inv_mem (x : K) : x ∈ R ∨ x⁻¹ ∈ R := by
  rw [mem_subring_iff_integer, mem_subring_iff_integer]
  by_cases h : v x ≤ 1
  · exact Or.inl h
  · apply Or.inr
    have hx : x ≠ 0 := by
      rintro rfl
      simp at h
    have hvx : 1 < v x := not_le.mp h
    rw [Valuation.one_lt_val_iff v hx] at hvx
    exact le_of_lt hvx

include hϖ in
lemma eq_unit_mul_pow_irreducible [IsDiscreteValuationRing R] (x : K) (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : Rˣ), x = u * ϖ ^ n := by
  cases mem_or_inv_mem (R := R) x
  · next h =>
    let x' : R := ⟨x, h⟩
    have hx' : x' ≠ 0 := Subtype.coe_ne_coe.mp hx
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' hϖ
    use n, u
    simpa using congrArg Subtype.val hu
  · next h =>
    let x' : R := ⟨x⁻¹, h⟩
    have hx' : x' ≠ 0 := (Subtype.coe_ne_coe).mp (inv_ne_zero hx)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' hϖ
    have : x = x'.val⁻¹ := by simp [x']
    use -n, u⁻¹
    rw [this, hu, mul_comm]
    ring_nf
    simp [coe_inv_eq_inv_coe]

lemma eq_unit_mul_pow_irreducible' [IsDiscreteValuationRing R] (x : Kˣ) :
    ∃ (n : ℤ) (u : Rˣ), x = Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ n := by
  have hx : x.val ≠ 0 := x.ne_zero
  obtain ⟨n, u, h⟩ := eq_unit_mul_pow_irreducible ϖ hϖ x.val hx
  use n, u
  ext
  rw [h]
  simp

/-
NOTE: The following lemmas are mostly copied from the analogous lemmas for `ValuationSubring`s.
It could be advisable to change our setup, started a Zulip discussion for that.
-/

theorem valuation_eq_iff (x y : K) :
    v x = v y ↔ ∃ (a : Rˣ), a * y = x :=
  Quotient.eq''

theorem valuation_unit (a : Rˣ) : v a = 1 := by
  rw [← Valuation.map_one v, valuation_eq_iff]; use a; simp

lemma valuation_isUnit (a : R) (ha : IsUnit a) : v a = 1 :=
  valuation_unit ha.unit

lemma valuation_eq_one_iff (a : R) : IsUnit a ↔ v a = 1 :=
  ⟨fun h => valuation_unit h.unit, fun h => by
    have ha : (a : K) ≠ 0 := by
      intro c
      rw [c, Valuation.map_zero] at h
      exact zero_ne_one h
    have ha' : (a : K)⁻¹ ∈ R := by rw [mem_subring_iff_integer, map_inv₀, h, inv_one]
    apply IsUnit.of_mul_eq_one ⟨(a : K)⁻¹, ha'⟩
    ext
    change (a : K) * (a : K)⁻¹ = 1
    field_simp [ha]⟩

lemma valuation_unit_eq_one (x : Rˣ) : v x = 1 :=
  valuation_unit x

include hϖ in
lemma valuation_lt_one_of_irreducible : v ϖ < 1 := by
  by_contra h
  apply hϖ.not_isUnit
  rw [valuation_eq_one_iff]
  apply le_antisymm
  · simp [← mem_subring_iff_integer]
  · simpa using h

variable [IsDiscreteValuationRing R]

/-- The exponent of a unit relative to a chosen irreducible element. -/
noncomputable def zaddVal' (x : Kˣ) : ℤ :=
  (eq_unit_mul_pow_irreducible' ϖ hϖ x).choose

/-- The exponent of a unit relative to an arbitrary chosen irreducible element of the DVR. -/
noncomputable def zaddVal (x : Kˣ) : ℤ :=
  zaddVal'
    (IsDiscreteValuationRing.exists_irreducible R).choose
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec
    x

lemma zaddVal'_spec (x : Kˣ) : ∃ (u : Rˣ),
    x = Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ (zaddVal' ϖ hϖ x) :=
  (eq_unit_mul_pow_irreducible' ϖ hϖ x).choose_spec

lemma zaddVal_spec' (x : Kˣ) : ∃ (ϖ : R) (hϖ : Irreducible ϖ),
    zaddVal (R := R) x = zaddVal' ϖ hϖ x := by
  use (IsDiscreteValuationRing.exists_irreducible R).choose
  use (IsDiscreteValuationRing.exists_irreducible R).choose_spec
  rfl

lemma zaddVal_spec (x : Kˣ) : ∃ (ϖ : R) (hϖ : Irreducible ϖ)
    (u : Rˣ),
    x = Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ (zaddVal (R := R) x) := by
  obtain ⟨ϖ, hϖ, h⟩ := zaddVal_spec' (R := R) x
  use ϖ, hϖ
  obtain ⟨u, hu⟩ := zaddVal'_spec ϖ hϖ x
  use u
  rwa [h]

include hϖ in
lemma unit_mul_zpow_congr_zpow' (a b : Rˣ) (m n : ℤ) (h : a * ϖ.val ^ m = b * ϖ.val ^ n) :
    m = n := by
  wlog hmn : m ≤ n
  · simp only [not_le] at hmn
    symm
    exact this ϖ hϖ b a n m h.symm (le_of_lt hmn)
  have h' : a * ϖ.val ^ m * ϖ.val ^ (-m) = b * ϖ.val ^ n * ϖ.val ^ (-m) :=
    congrFun (congrArg HMul.hMul h) (ϖ.val ^ (-m))
  rw [mul_assoc, mul_assoc, ← zpow_add₀ (by simpa using hϖ.ne_zero),
    ← zpow_add₀ (by simpa using hϖ.ne_zero)] at h'
  ring_nf at h'
  simp only [zpow_zero, mul_one] at h'
  rw [add_comm] at h'
  have : a * ϖ ^ 0 = b * ϖ ^ (Int.toNat (n - m)) := by
    ext
    simp only [pow_zero, mul_one, Subring.coe_mul, SubmonoidClass.coe_pow]
    rw [h']
    rw [← sub_eq_add_neg]
    rw [← Int.toNat_sub_of_le hmn]
    norm_cast
  have : 0 = Int.toNat (n - m) :=
    IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ a b 0 (Int.toNat (n - m)) this
  rw [← Nat.cast_inj (R := ℤ)] at this
  simp only [CharP.cast_eq_zero, Int.ofNat_toNat, right_eq_sup, tsub_le_iff_right, zero_add] at this
  symm
  exact Int.le_antisymm this hmn

lemma unit_mul_zpow_congr_zpow {p q : R} (hp : Irreducible p) (hq : Irreducible q)
    (a b : Rˣ) (m n : ℤ) (h : a * p.val ^ m = b * q.val ^ n) :
    m = n := by
  obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible R hp hq
  simp only [Subring.coe_mul] at h
  rw [mul_zpow] at h
  nth_rw 3 [mul_comm] at h
  have : (b * u ^ n).val.val = b.val.val * u.val.val ^ n := by simp
  rw [← mul_assoc, ← this] at h
  apply unit_mul_zpow_congr_zpow' _ hp
  exact h

include hϖ in
omit [IsDiscreteValuationRing R] in
lemma valuation_irreducible_zpow_eq_one_iff (n : ℤ) : v (ϖ.val ^ n) = 1 ↔ n = 0 := by
  constructor
  · intro h
    rw [map_zpow₀] at h
    have : v ϖ < 1 := valuation_lt_one_of_irreducible ϖ hϖ
    exact exp_zero_of_zpow_eq_one this h
  · rintro rfl
    simp

include hϖ in
omit [ValuationRing R] [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K] in
lemma inv_irreducible_not_mem_subring : ϖ.val⁻¹ ∉ R := by
  by_contra h
  apply hϖ.not_isUnit
  have hϖnzero : ϖ.val ≠ 0 := by
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact hϖ.ne_zero
  let x : Rˣ :=
    ⟨ϖ, ⟨ϖ.val⁻¹, h⟩,
      by
        ext
        change ϖ.val * ϖ.val⁻¹ = 1
        field_simp [hϖnzero],
      by
        ext
        change ϖ.val⁻¹ * ϖ.val = 1
        field_simp [hϖnzero]⟩
  use x

include hϖ in
omit [ValuationRing R] [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K] in
lemma neg_pow_not_mem_subring (n : ℕ) (hn : n > 0) : ϖ.val ^ (- n : ℤ) ∉ R := by
  induction n with
  | zero => contradiction
  | succ n ih =>
      have hϖnzero : ϖ.val ≠ 0 := by
        simp only [ne_eq, ZeroMemClass.coe_eq_zero]
        exact hϖ.ne_zero
      simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg]
      rw [zpow_add₀ hϖnzero]
      simp only [Int.reduceNeg, zpow_neg, zpow_one, zpow_natCast]
      simp only [gt_iff_lt, zpow_neg, zpow_natCast] at ih
      by_cases hnz : n = 0
      · subst hnz
        simp only [pow_zero, inv_one, mul_one]
        exact inv_irreducible_not_mem_subring ϖ hϖ
      · have : (ϖ.val ^ n)⁻¹ ∉ R := by
          apply ih
          exact Nat.zero_lt_of_ne_zero hnz
        contrapose! this
        have : ϖ.val * ϖ.val⁻¹ * (ϖ.val ^ n)⁻¹ = (ϖ.val ^ n)⁻¹ := by field_simp
        rw [← this, mul_assoc]
        apply Subring.mul_mem
        · exact ϖ.property
        · assumption

omit [ValuationRing R] [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K] in
include hϖ in
lemma irreducible_zpow_mem_subring_iff (n : ℤ) : ϖ.val ^ n ∈ R ↔ n ≥ 0 := by
  constructor
  · intro h
    contrapose! h
    have hn : - n ≥ 0 := by
      simp only [ge_iff_le, Left.nonneg_neg_iff]
      exact Int.le_of_lt h
    convert_to (ϖ.val ^ (- (- n).toNat : ℤ)) ∉ R
    · rw [Int.toNat_of_nonneg hn]
      simp
    · apply neg_pow_not_mem_subring _ (-n).toNat (hϖ := hϖ)
      simpa
  · intro hn
    convert_to (ϖ ^ n.toNat).val ∈ R
    · rw [SubmonoidClass.coe_pow, ← zpow_natCast, Int.toNat_of_nonneg hn]
    · exact SetLike.coe_mem (ϖ ^ n.toNat)

lemma zaddVal'_eq_iff (n : ℤ) (x : Kˣ) :
    zaddVal' (R := R) ϖ hϖ x = n ↔ ∃ (u : Rˣ), Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ n = x := by
  constructor
  · intro h
    rw [← h]
    use (eq_unit_mul_pow_irreducible' ϖ hϖ x).choose_spec.choose
    exact (eq_unit_mul_pow_irreducible' ϖ hϖ x).choose_spec.choose_spec.symm
  · rintro ⟨u, hu⟩
    obtain ⟨y, hy⟩ := zaddVal'_spec ϖ hϖ x
    nth_rw 1 [← hu] at hy
    rw [Units.ext_iff] at hy
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Subring.coe_subtype,
      Units.val_zpow_eq_zpow_val, Units.val_mk0] at hy
    apply unit_mul_zpow_congr_zpow hϖ hϖ y u
    exact hy.symm

lemma zaddVal_eq_iff (n : ℤ) (x : Kˣ) :
    zaddVal (R := R) x = n ↔ ∃ (u : Rˣ), Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ n = x := by
  constructor
  · intro h
    obtain ⟨p, hp, y, hy⟩ := zaddVal_spec (R := R) x
    rw [h] at hy
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ hp
    use y * a ^ n
    ext
    simp [hy, mul_zpow]
    group
  · rintro ⟨u, hu⟩
    obtain ⟨p, hp, y, hy⟩ := zaddVal_spec (R := R) x
    nth_rw 1 [← hu] at hy
    rw [Units.ext_iff] at hy
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Subring.coe_subtype,
      Units.val_zpow_eq_zpow_val, Units.val_mk0] at hy
    apply unit_mul_zpow_congr_zpow hp hϖ y u
    exact hy.symm

include hϖ in
lemma zaddVal_eq_iff' (n : ℤ) (x : Kˣ) :
    zaddVal (R := R) x = n ↔ ∃ (u : Rˣ), u * ϖ.val ^ n = x := by
  rw [zaddVal_eq_iff ϖ hϖ]
  simp [Units.ext_iff]

include hϖ in
lemma eq_unit_mul_zpow_zaddVal (x : Kˣ) :
    ∃ (u : Rˣ), u * ϖ.val ^ zaddVal (R := R) x = x :=
  (zaddVal_eq_iff' ϖ hϖ (zaddVal (R := R) x) x).mp rfl

@[simp]
lemma zaddVal_mul (x y : Kˣ) :
    zaddVal (R := R) (x * y) = zaddVal (R := R) x + zaddVal (R := R) y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ux, hux⟩ := eq_unit_mul_zpow_zaddVal ϖ hϖ x
  obtain ⟨uy, huy⟩ := eq_unit_mul_zpow_zaddVal ϖ hϖ y
  rw [zaddVal_eq_iff' ϖ hϖ]
  use ux * uy
  simp only [Units.val_mul, Subring.coe_mul]
  rw [zpow_add₀ (by simpa using hϖ.ne_zero), ← hux, ← huy]
  ring

@[simp]
lemma zaddVal_units_map (x : Rˣ) :
    zaddVal (R := R) (Units.map R.subtype x) = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [zaddVal_eq_iff' ϖ hϖ]
  use x
  simp
