/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Valuation.ValuationSubring
/-! Provides the public declarations in the `ValuationTheory.AbsoluteValue.Theory.ExponentialValuations` Lean module. -/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace LubinTate
namespace Valuations

/-- The additive exponential valuation with value `∞` at zero. -/
structure ExponentialValuation (K : Type*) [Field K] where
  /-- The value map into `ℝ ∪ {∞}`. -/
  toFun : K → WithTop ℝ
  /-- Exactly zero has value `∞`. -/
  eq_top_iff : ∀ x, toFun x = ⊤ ↔ x = 0
  /-- Multiplication becomes addition of values. -/
  map_mul : ∀ x y, toFun (x * y) = toFun x + toFun y
  /-- The nonarchimedean inequality in additive form. -/
  add_le_min : ∀ x y, min (toFun x) (toFun y) ≤ toFun (x + y)

/-- Coerce an exponential valuation to its function. -/
instance exponentialValuationCoeFun {K : Type*} [Field K] :
    CoeFun (ExponentialValuation K) (fun _ => K → WithTop ℝ) where
  coe v := v.toFun

/-- The trivial exponential valuation: every nonzero element has value `0`. -/
def TrivialExponentialValuation {K : Type*} [Field K]
    (v : ExponentialValuation K) : Prop :=
  ∀ x : K, x ≠ 0 → v x = 0

/-- Equivalence of exponential valuations by multiplication by a positive real scalar. -/
def EquivalentExponentialValuations {K : Type*} [Field K]
    (v w : ExponentialValuation K) : Prop :=
  ∃ s : ℝ, 0 < s ∧ ∀ x : K, x ≠ 0 → ∃ r : ℝ,
    w x = (r : WithTop ℝ) ∧ v x = ((s * r : ℝ) : WithTop ℝ)

/-- A multiplicative absolute value associated to an exponential valuation by `|x| = q^{-v(x)}`. -/
def AssociatedAbsoluteValue {K : Type*} [Field K]
    (v : ExponentialValuation K) (q : ℝ) (abv : AbsoluteValue K ℝ) : Prop :=
  1 < q ∧ ∀ x : K, x ≠ 0 → ∃ r : ℝ,
    v x = (r : WithTop ℝ) ∧ abv x = Real.rpow q (-r)

/-- The valuation ring `{x | v(x) ≥ 0}` attached to an exponential valuation. -/
def exponentialValuationRing {K : Type*} [Field K]
    (v : ExponentialValuation K) : Set K :=
  {x | (0 : WithTop ℝ) ≤ v x}

/-- Nonzero elements have finite value for a exponential valuation. -/
theorem exponentialValuation_ne_top_of_ne_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : x ≠ 0) :
    v x ≠ ⊤ := by
  intro htop
  exact hx ((v.eq_top_iff x).mp htop)

/-- A nonzero element has a real-valued exponential valuation. -/
theorem exponentialValuation_exists_real_of_ne_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : x ≠ 0) :
    ∃ r : ℝ, v x = (r : WithTop ℝ) := by
  rcases WithTop.ne_top_iff_exists.mp
      (exponentialValuation_ne_top_of_ne_zero v hx) with ⟨r, hr⟩
  exact ⟨r, hr.symm⟩

/-- The value of `1` is `0` for a exponential valuation. -/
@[simp]
theorem exponentialValuation_one {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    v (1 : K) = 0 := by
  obtain ⟨r, hr⟩ :=
    exponentialValuation_exists_real_of_ne_zero v (one_ne_zero : (1 : K) ≠ 0)
  have hmul := v.map_mul (1 : K) (1 : K)
  rw [one_mul, hr] at hmul
  have hmul_real : r = r + r :=
    WithTop.coe_eq_coe.mp (by simpa [WithTop.coe_add] using hmul)
  have hr0 : r = 0 := by linarith
  simp [hr, hr0]

/-- The value of `-1` is `0` for a exponential valuation. -/
@[simp]
theorem exponentialValuation_neg_one {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    v (-1 : K) = 0 := by
  obtain ⟨r, hr⟩ :=
    exponentialValuation_exists_real_of_ne_zero v
      (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))
  have hmul := v.map_mul (-1 : K) (-1 : K)
  have hsq : (-1 : K) * (-1 : K) = 1 := by ring
  rw [hsq, exponentialValuation_one v, hr] at hmul
  have hmul_real : (0 : ℝ) = r + r :=
    WithTop.coe_eq_coe.mp (by simpa [WithTop.coe_add] using hmul)
  have hr0 : r = 0 := by linarith
  simp [hr, hr0]

/-- Negation does not change a exponential valuation. -/
@[simp]
theorem exponentialValuation_neg {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : K) :
    v (-x) = v x := by
  rw [← neg_one_mul, v.map_mul, exponentialValuation_neg_one, zero_add]

/-- An element of value zero is nonzero. -/
theorem exponentialValuation_ne_zero_of_value_eq_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : v x = 0) :
    x ≠ 0 := by
  intro hzero
  have htop : v x = ⊤ := (v.eq_top_iff x).mpr hzero
  rw [hx] at htop
  simp at htop

/-- The inverse of a value-zero element again has value zero. -/
theorem exponentialValuation_inv_of_value_eq_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : v x = 0) :
    v x⁻¹ = 0 := by
  have hx0 : x ≠ 0 := exponentialValuation_ne_zero_of_value_eq_zero v hx
  have hmul := v.map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx0, exponentialValuation_one v, hx] at hmul
  simpa using hmul.symm

/-- Finite inverse-value formula for a exponential valuation. -/
theorem exponentialValuation_inv_value {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : x ≠ 0) {r : ℝ}
    (hval : v x = (r : WithTop ℝ)) :
    v x⁻¹ = ((-r : ℝ) : WithTop ℝ) := by
  obtain ⟨s, hs⟩ :=
    exponentialValuation_exists_real_of_ne_zero v (inv_ne_zero hx)
  have hmul := v.map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, exponentialValuation_one v, hval, hs] at hmul
  have hmul_real : (0 : ℝ) = r + s :=
    WithTop.coe_eq_coe.mp (by simpa [WithTop.coe_add] using hmul)
  have hs_eq : s = -r := by
    linarith
  simp [hs, hs_eq]

/-- The set `{x | 0 ≤ v x}` is a subring. -/
def exponentialValuationSubring {K : Type*} [Field K]
    (v : ExponentialValuation K) : Subring K where
  carrier := exponentialValuationRing v
  zero_mem' := by
    change (0 : WithTop ℝ) ≤ v (0 : K)
    rw [(v.eq_top_iff 0).mpr rfl]
    simp
  one_mem' := by
    change (0 : WithTop ℝ) ≤ v (1 : K)
    simp
  add_mem' := by
    intro x y hx hy
    change (0 : WithTop ℝ) ≤ v (x + y)
    exact (le_min hx hy).trans (v.add_le_min x y)
  neg_mem' := by
    intro x hx
    change (0 : WithTop ℝ) ≤ v x at hx
    change (0 : WithTop ℝ) ≤ v (-x)
    simpa using hx
  mul_mem' := by
    intro x y hx hy
    change (0 : WithTop ℝ) ≤ v (x * y)
    rw [v.map_mul]
    exact add_nonneg hx hy

/-- Membership in the exponential-valuation subring is exactly the defining
condition `0 ≤ v x`. -/
theorem mem_exponentialValuationSubring_iff {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationSubring v ↔ (0 : WithTop ℝ) ≤ v x :=
  Iff.rfl

/-- Every element of the field or its inverse lies in the exponential-valuation ring. -/
theorem exponentialValuationRing_mem_or_inv_mem {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationRing v ∨ x⁻¹ ∈ exponentialValuationRing v := by
  by_cases hx : x = 0
  · left
    subst x
    change (0 : WithTop ℝ) ≤ v (0 : K)
    rw [(v.eq_top_iff 0).mpr rfl]
    simp
  · obtain ⟨r, hr⟩ := exponentialValuation_exists_real_of_ne_zero v hx
    by_cases hr_nonneg : 0 ≤ r
    · left
      change (0 : WithTop ℝ) ≤ v x
      rw [hr]
      exact WithTop.coe_le_coe.mpr hr_nonneg
    · right
      have hneg_nonneg : 0 ≤ -r := by
        linarith
      change (0 : WithTop ℝ) ≤ v x⁻¹
      rw [exponentialValuation_inv_value v hx hr]
      exact WithTop.coe_le_coe.mpr hneg_nonneg

/-- The absolute values subring satisfies mathlib's valuation-subring
membership alternative. -/
theorem exponentialValuationSubring_mem_or_inv_mem {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationSubring v ∨
      x⁻¹ ∈ exponentialValuationSubring v := by
  simpa [exponentialValuationSubring] using
    exponentialValuationRing_mem_or_inv_mem v x

/-- The exponential-valuation ring, bundled as mathlib's `ValuationSubring`. -/
def exponentialValuationSubringAsValuationSubring
    {K : Type*} [Field K] (v : ExponentialValuation K) :
    ValuationSubring K :=
  ValuationSubring.ofSubring (exponentialValuationSubring v)
    (exponentialValuationSubring_mem_or_inv_mem v)

/-- Membership in the bundled mathlib valuation subring is the defining condition
`0 ≤ v x`. -/
theorem mem_exponentialValuationSubringAsValuationSubring_iff
    {K : Type*} [Field K] (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationSubringAsValuationSubring v ↔
      (0 : WithTop ℝ) ≤ v x :=
  Iff.rfl

/-- The unit set `{x | v(x) = 0}` attached to an exponential valuation. -/
def exponentialUnitSet {K : Type*} [Field K]
    (v : ExponentialValuation K) : Set K :=
  {x | v x = 0}

/-- The maximal ideal `{x | v(x) > 0}` attached to an exponential valuation. -/
def exponentialMaxIdealSet {K : Type*} [Field K]
    (v : ExponentialValuation K) : Set K :=
  {x | (0 : WithTop ℝ) < v x}

/-- Equivalent exponential valuations have the same nonnegative elements. -/
theorem equivalentExponentialValuations_value_nonneg_iff
    {K : Type*} [Field K] {v w : ExponentialValuation K}
    (hequiv : EquivalentExponentialValuations v w) (x : K) :
    (0 : WithTop ℝ) ≤ v x ↔ (0 : WithTop ℝ) ≤ w x := by
  rcases hequiv with ⟨s, hs_pos, hscale⟩
  by_cases hx : x = 0
  · subst x
    simp [(v.eq_top_iff 0).mpr rfl, (w.eq_top_iff 0).mpr rfl]
  · rcases hscale x hx with ⟨r, hw, hv⟩
    constructor
    · intro hv_nonneg
      have hsr_nonneg : 0 ≤ s * r := by
        have hwt :
            ((0 : ℝ) : WithTop ℝ) ≤ ((s * r : ℝ) : WithTop ℝ) := by
          simpa [hv] using hv_nonneg
        exact WithTop.coe_le_coe.mp hwt
      have hr_nonneg : 0 ≤ r :=
        nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hsr_nonneg) hs_pos
      have hwt : ((0 : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ) :=
        WithTop.coe_le_coe.mpr hr_nonneg
      simpa [hw] using hwt
    · intro hw_nonneg
      have hr_nonneg : 0 ≤ r := by
        have hwt : ((0 : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ) := by
          simpa [hw] using hw_nonneg
        exact WithTop.coe_le_coe.mp hwt
      have hsr_nonneg : 0 ≤ s * r :=
        mul_nonneg (le_of_lt hs_pos) hr_nonneg
      have hwt :
          ((0 : ℝ) : WithTop ℝ) ≤ ((s * r : ℝ) : WithTop ℝ) :=
        WithTop.coe_le_coe.mpr hsr_nonneg
      simpa [hv] using hwt

/-- Equivalent exponential valuations have the same value-zero elements. -/
theorem equivalentExponentialValuations_value_eq_zero_iff
    {K : Type*} [Field K] {v w : ExponentialValuation K}
    (hequiv : EquivalentExponentialValuations v w) (x : K) :
    v x = 0 ↔ w x = 0 := by
  rcases hequiv with ⟨s, hs_pos, hscale⟩
  by_cases hx : x = 0
  · subst x
    simp [(v.eq_top_iff 0).mpr rfl, (w.eq_top_iff 0).mpr rfl]
  · rcases hscale x hx with ⟨r, hw, hv⟩
    constructor
    · intro hv_zero
      have hsr_zero : s * r = 0 := by
        exact WithTop.coe_eq_coe.mp (by simpa [hv] using hv_zero)
      have hr_zero : r = 0 :=
        (mul_eq_zero.mp hsr_zero).resolve_left hs_pos.ne'
      simp [hw, hr_zero]
    · intro hw_zero
      have hr_zero : r = 0 := by
        exact WithTop.coe_eq_coe.mp (by simpa [hw] using hw_zero)
      simp [hv, hr_zero]

/-- Equivalent exponential valuations have the same positive-value elements. -/
theorem equivalentExponentialValuations_value_pos_iff
    {K : Type*} [Field K] {v w : ExponentialValuation K}
    (hequiv : EquivalentExponentialValuations v w) (x : K) :
    (0 : WithTop ℝ) < v x ↔ (0 : WithTop ℝ) < w x := by
  constructor
  · intro hv_pos
    have hw_nonneg :
        (0 : WithTop ℝ) ≤ w x :=
      (equivalentExponentialValuations_value_nonneg_iff hequiv x).mp
        (le_of_lt hv_pos)
    have hw_ne_zero : w x ≠ 0 := by
      intro hw_zero
      have hv_zero :
          v x = 0 :=
        (equivalentExponentialValuations_value_eq_zero_iff hequiv x).mpr
          hw_zero
      exact (ne_of_gt hv_pos) hv_zero
    exact lt_of_le_of_ne hw_nonneg (Ne.symm hw_ne_zero)
  · intro hw_pos
    have hv_nonneg :
        (0 : WithTop ℝ) ≤ v x :=
      (equivalentExponentialValuations_value_nonneg_iff hequiv x).mpr
        (le_of_lt hw_pos)
    have hv_ne_zero : v x ≠ 0 := by
      intro hv_zero
      have hw_zero :
          w x = 0 :=
        (equivalentExponentialValuations_value_eq_zero_iff hequiv x).mp
          hv_zero
      exact (ne_of_gt hw_pos) hw_zero
    exact lt_of_le_of_ne hv_nonneg (Ne.symm hv_ne_zero)

/-- Equivalent exponential valuations have the same exponential-valuation ring. -/
theorem equivalentExponentialValuations_ring_eq
    {K : Type*} [Field K] {v w : ExponentialValuation K}
    (hequiv : EquivalentExponentialValuations v w) :
    exponentialValuationRing v = exponentialValuationRing w := by
  ext x
  exact equivalentExponentialValuations_value_nonneg_iff hequiv x

/-- Equivalent exponential valuations have the same bundled valuation subring. -/
theorem equivalentExponentialValuations_subring_eq
    {K : Type*} [Field K] {v w : ExponentialValuation K}
    (hequiv : EquivalentExponentialValuations v w) :
    exponentialValuationSubring v = exponentialValuationSubring w := by
  ext x
  exact equivalentExponentialValuations_value_nonneg_iff hequiv x

/-- Equivalent exponential valuations define the same mathlib valuation
subring. -/
theorem equivalentExponentialValuations_valuationSubring_eq
    {K : Type*} [Field K] {v w : ExponentialValuation K}
    (hequiv : EquivalentExponentialValuations v w) :
    exponentialValuationSubringAsValuationSubring v =
      exponentialValuationSubringAsValuationSubring w := by
  ext x
  exact equivalentExponentialValuations_value_nonneg_iff hequiv x

/-- Equivalent exponential valuations have the same unit set. -/
theorem equivalentExponentialValuations_unitSet_eq
    {K : Type*} [Field K] {v w : ExponentialValuation K}
    (hequiv : EquivalentExponentialValuations v w) :
    exponentialUnitSet v = exponentialUnitSet w := by
  ext x
  exact equivalentExponentialValuations_value_eq_zero_iff hequiv x

/-- Equivalent exponential valuations have the same positive-value ideal set. -/
theorem equivalentExponentialValuations_maxIdealSet_eq
    {K : Type*} [Field K] {v w : ExponentialValuation K}
    (hequiv : EquivalentExponentialValuations v w) :
    exponentialMaxIdealSet v = exponentialMaxIdealSet w := by
  ext x
  exact equivalentExponentialValuations_value_pos_iff hequiv x

/-- For an associated multiplicative absolute value, `|x| ≤ 1` is the same as
the exponential value being nonnegative. -/
theorem associatedAbsoluteValue_le_one_iff
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) {x : K} (hx : x ≠ 0) :
    abv x ≤ 1 ↔ (0 : WithTop ℝ) ≤ v x := by
  rcases hassoc.2 x hx with ⟨r, hval, habv⟩
  have hq : 1 < q := hassoc.1
  have hq_pos : 0 < q := zero_lt_one.trans hq
  have hq_not_le_one : ¬ q ≤ 1 := not_le.mpr hq
  constructor
  · intro habv_le
    have hpow : q ^ (-r) ≤ 1 := by
      simpa [habv] using habv_le
    have hneg_nonpos : -r ≤ 0 := by
      rcases (Real.rpow_le_one_iff_of_pos hq_pos).mp hpow with hcase | hcase
      · exact hcase.2
      · exact (hq_not_le_one hcase.1).elim
    have hr_nonneg : 0 ≤ r := by linarith
    have hwt : ((0 : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ) :=
      WithTop.coe_le_coe.mpr hr_nonneg
    simpa [hval] using hwt
  · intro hval_nonneg
    have hr_nonneg : 0 ≤ r := by
      have hwt : ((0 : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ) := by
        simpa [hval] using hval_nonneg
      exact WithTop.coe_le_coe.mp hwt
    have hneg_nonpos : -r ≤ 0 := by linarith
    have hpow : q ^ (-r) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hq) hneg_nonpos
    simpa [habv] using hpow

/-- For an associated multiplicative absolute value, `|x| < 1` is the same as
the exponential value being positive. -/
theorem associatedAbsoluteValue_lt_one_iff
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) {x : K} (hx : x ≠ 0) :
    abv x < 1 ↔ (0 : WithTop ℝ) < v x := by
  rcases hassoc.2 x hx with ⟨r, hval, habv⟩
  have hq : 1 < q := hassoc.1
  have hq_pos : 0 < q := zero_lt_one.trans hq
  have hq_not_lt_one : ¬ q < 1 := not_lt.mpr (le_of_lt hq)
  constructor
  · intro habv_lt
    have hpow : q ^ (-r) < 1 := by
      simpa [habv] using habv_lt
    have hneg_neg : -r < 0 := by
      rcases (Real.rpow_lt_one_iff_of_pos hq_pos).mp hpow with hcase | hcase
      · exact hcase.2
      · exact (hq_not_lt_one hcase.1).elim
    have hr_pos : 0 < r := by linarith
    have hwt : ((0 : ℝ) : WithTop ℝ) < (r : WithTop ℝ) :=
      WithTop.coe_lt_coe.mpr hr_pos
    simpa [hval] using hwt
  · intro hval_pos
    have hr_pos : 0 < r := by
      have hwt : ((0 : ℝ) : WithTop ℝ) < (r : WithTop ℝ) := by
        simpa [hval] using hval_pos
      exact WithTop.coe_lt_coe.mp hwt
    have hneg_neg : -r < 0 := by linarith
    have hpow : q ^ (-r) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hq hneg_neg
    simpa [habv] using hpow

/-- For an associated multiplicative absolute value, `|x| = 1` is the same as
the exponential value being zero. -/
theorem associatedAbsoluteValue_eq_one_iff
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) {x : K} (hx : x ≠ 0) :
    abv x = 1 ↔ v x = 0 := by
  constructor
  · intro habv_one
    have hle : (0 : WithTop ℝ) ≤ v x :=
      (associatedAbsoluteValue_le_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx).mp
        (le_of_eq habv_one)
    have hnlt : ¬ (0 : WithTop ℝ) < v x := by
      intro hvpos
      have habv_lt :
          abv x < 1 :=
        (associatedAbsoluteValue_lt_one_iff
          (v := v) (q := q) (abv := abv) hassoc hx).mpr hvpos
      exact (not_lt_of_ge (le_of_eq habv_one.symm)) habv_lt
    exact le_antisymm (le_of_not_gt hnlt) hle
  · intro hvzero
    have hle : abv x ≤ 1 :=
      (associatedAbsoluteValue_le_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx).mpr
        (by simp [hvzero])
    have hnlt : ¬ abv x < 1 := by
      intro habv_lt
      have hvpos :
          (0 : WithTop ℝ) < v x :=
        (associatedAbsoluteValue_lt_one_iff
          (v := v) (q := q) (abv := abv) hassoc hx).mp habv_lt
      simp [hvzero] at hvpos
    exact le_antisymm hle (le_of_not_gt hnlt)

/-- The valuation ring of an exponential valuation is the closed unit ball for
any associated multiplicative absolute value. -/
theorem associatedAbsoluteValue_ring_eq_closed_unit_ball
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) :
    exponentialValuationRing v = {x : K | abv x ≤ 1} := by
  ext x
  by_cases hx : x = 0
  · subst x
    simp [exponentialValuationRing, (v.eq_top_iff 0).mpr rfl]
  · simpa [exponentialValuationRing] using
      (associatedAbsoluteValue_le_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx).symm

/-- The zero-value unit set `{x | v x = 0}` is the unit sphere for any associated
multiplicative absolute value. -/
theorem associatedAbsoluteValue_unitSet_eq_unit_sphere
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) :
    exponentialUnitSet v = {x : K | abv x = 1} := by
  ext x
  by_cases hx : x = 0
  · subst x
    simp [exponentialUnitSet, (v.eq_top_iff 0).mpr rfl]
  · simpa [exponentialUnitSet] using
      (associatedAbsoluteValue_eq_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx).symm

/-- The positive-value ideal of an exponential valuation is the open unit ball
for any associated multiplicative absolute value. -/
theorem associatedAbsoluteValue_maxIdealSet_eq_open_unit_ball
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) :
    exponentialMaxIdealSet v = {x : K | abv x < 1} := by
  ext x
  by_cases hx : x = 0
  · subst x
    simp [exponentialMaxIdealSet, (v.eq_top_iff 0).mpr rfl]
  · simpa [exponentialMaxIdealSet] using
      (associatedAbsoluteValue_lt_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx).symm

/-- Elements of value zero lie in the valuation subring. -/
theorem exponentialUnitSet_subset_ring {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    exponentialUnitSet v ⊆ exponentialValuationRing v := by
  intro x hx
  change (0 : WithTop ℝ) ≤ v x
  rw [hx]

/-- Elements of positive value lie in the valuation subring. -/
theorem exponentialMaxIdealSet_subset_ring {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    exponentialMaxIdealSet v ⊆ exponentialValuationRing v := by
  intro x hx
  change (0 : WithTop ℝ) < v x at hx
  change (0 : WithTop ℝ) ≤ v x
  exact le_of_lt hx

/-- The positive-value elements form an ideal of the exponential-valuation ring. -/
def exponentialMaxIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) : Ideal (exponentialValuationSubring v) where
  carrier := {x | (0 : WithTop ℝ) < v (x : K)}
  zero_mem' := by
    change (0 : WithTop ℝ) < v (0 : K)
    rw [(v.eq_top_iff 0).mpr rfl]
    simp
  add_mem' := by
    intro x y hx hy
    change (0 : WithTop ℝ) < v ((x + y : exponentialValuationSubring v) : K)
    have hmin : (0 : WithTop ℝ) < min (v (x : K)) (v (y : K)) :=
      lt_min hx hy
    exact lt_of_lt_of_le hmin (by simpa using v.add_le_min (x : K) (y : K))
  smul_mem' := by
    intro a x hx
    change (0 : WithTop ℝ) < v ((a : K) * (x : K))
    have ha : (0 : WithTop ℝ) ≤ v (a : K) := a.property
    rw [v.map_mul]
    have hx_le : v (x : K) ≤ v (a : K) + v (x : K) := by
      simpa [zero_add] using
        (add_le_add ha (le_rfl : v (x : K) ≤ v (x : K)))
    exact lt_of_lt_of_le hx hx_le

/-- Membership in the bundled positive-value ideal is the defining condition `0 < v x`. -/
theorem mem_exponentialMaxIdeal_iff {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : exponentialValuationSubring v) :
    x ∈ exponentialMaxIdeal v ↔ (0 : WithTop ℝ) < v (x : K) :=
  Iff.rfl

/-- The unit element is not in the positive-value ideal. -/
theorem one_not_mem_exponentialMaxIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    (1 : exponentialValuationSubring v) ∉ exponentialMaxIdeal v := by
  change ¬ (0 : WithTop ℝ) < v (1 : K)
  simp

/-- Inside the valuation ring, not lying in the positive-value ideal is the same
as having value zero. -/
theorem not_mem_exponentialMaxIdeal_iff_value_eq_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : exponentialValuationSubring v) :
    x ∉ exponentialMaxIdeal v ↔ v (x : K) = 0 := by
  constructor
  · intro hx
    change ¬ (0 : WithTop ℝ) < v (x : K) at hx
    exact le_antisymm (le_of_not_gt hx) x.property
  · intro hx
    change ¬ (0 : WithTop ℝ) < v (x : K)
    simp [hx]

/-- Value-zero elements of the valuation ring are units of that ring. -/
theorem isUnit_of_exponentialValuation_eq_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : v (x : K) = 0) :
    IsUnit x := by
  rw [Submonoid.isUnit_iff_and (S := exponentialValuationSubring v) (a := x)]
  constructor
  · exact exponentialValuation_ne_zero_of_value_eq_zero v hx
  · change (0 : WithTop ℝ) ≤ v ((x : K)⁻¹)
    simp [exponentialValuation_inv_of_value_eq_zero v hx]

/-- Units of the valuation ring have value zero. -/
theorem exponentialValuation_eq_zero_of_isUnit {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : IsUnit x) :
    v (x : K) = 0 := by
  have hx_inv :=
    (Submonoid.isUnit_iff_and (S := exponentialValuationSubring v) (a := x)).mp hx
  have hx_nonneg : (0 : WithTop ℝ) ≤ v (x : K) := x.property
  have hinv_nonneg : (0 : WithTop ℝ) ≤ v ((x : K)⁻¹) := hx_inv.2
  have hmul := v.map_mul (x : K) ((x : K)⁻¹)
  rw [mul_inv_cancel₀ hx_inv.1, exponentialValuation_one v] at hmul
  have hx_le_zero : v (x : K) ≤ 0 := by
    calc
      v (x : K) ≤ v (x : K) + v ((x : K)⁻¹) :=
        le_add_of_nonneg_right hinv_nonneg
      _ = 0 := hmul.symm
  exact le_antisymm hx_le_zero hx_nonneg

/-- A valuation-ring element outside the positive-value ideal is a unit. -/
theorem isUnit_of_not_mem_exponentialMaxIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : x ∉ exponentialMaxIdeal v) :
    IsUnit x :=
  isUnit_of_exponentialValuation_eq_zero v
    ((not_mem_exponentialMaxIdeal_iff_value_eq_zero v x).mp hx)

/-- Units of the valuation ring do not lie in the positive-value ideal. -/
theorem not_mem_exponentialMaxIdeal_of_isUnit {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : IsUnit x) :
    x ∉ exponentialMaxIdeal v := by
  have hzero : v (x : K) = 0 :=
    exponentialValuation_eq_zero_of_isUnit v hx
  change ¬ (0 : WithTop ℝ) < v (x : K)
  simp [hzero]

/-- In the valuation ring, the units are exactly the complement of the
positive-value ideal. -/
theorem isUnit_iff_not_mem_exponentialMaxIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : exponentialValuationSubring v) :
    IsUnit x ↔ x ∉ exponentialMaxIdeal v := by
  constructor
  · exact not_mem_exponentialMaxIdeal_of_isUnit v
  · exact isUnit_of_not_mem_exponentialMaxIdeal v

/-- For an associated absolute value, the units of the valuation ring are
exactly the elements of absolute value `1`. -/
theorem associatedAbsoluteValue_isUnit_iff_eq_one
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv)
    (x : exponentialValuationSubring v) :
    IsUnit x ↔ abv (x : K) = 1 := by
  constructor
  · intro hx
    have hvzero : v (x : K) = 0 :=
      exponentialValuation_eq_zero_of_isUnit v hx
    have hx0 : (x : K) ≠ 0 :=
      exponentialValuation_ne_zero_of_value_eq_zero v hvzero
    exact
      (associatedAbsoluteValue_eq_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx0).mpr hvzero
  · intro habv_one
    have hx0 : (x : K) ≠ 0 := by
      intro hx_zero
      have hzero : abv (x : K) = 0 := by
        simp [hx_zero]
      rw [hzero] at habv_one
      norm_num at habv_one
    have hvzero : v (x : K) = 0 :=
      (associatedAbsoluteValue_eq_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx0).mp habv_one
    exact isUnit_of_exponentialValuation_eq_zero v hvzero

/-- The positive-value ideal is maximal in the exponential-valuation ring. -/
theorem exponentialMaxIdeal_isMaximal {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    (exponentialMaxIdeal v).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · exact one_not_mem_exponentialMaxIdeal v
  · intro J x hIJ hx_not_mem hxJ
    exact (Ideal.eq_top_iff_one J).mp
      (J.eq_top_of_isUnit_mem hxJ
        ((isUnit_iff_not_mem_exponentialMaxIdeal v x).mpr hx_not_mem))

/-- The exponential-valuation ring is local. -/
instance exponentialValuationSubringIsLocalRing {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    IsLocalRing (exponentialValuationSubring v) :=
  IsLocalRing.of_nonunits_add fun x y hx hy => by
    have hx_mem : x ∈ exponentialMaxIdeal v := by
      by_contra hx_not_mem
      exact hx ((isUnit_iff_not_mem_exponentialMaxIdeal v x).mpr hx_not_mem)
    have hy_mem : y ∈ exponentialMaxIdeal v := by
      by_contra hy_not_mem
      exact hy ((isUnit_iff_not_mem_exponentialMaxIdeal v y).mpr hy_not_mem)
    have hxy_mem : x + y ∈ exponentialMaxIdeal v :=
      (exponentialMaxIdeal v).add_mem hx_mem hy_mem
    exact fun hxy_unit =>
      (not_mem_exponentialMaxIdeal_of_isUnit v hxy_unit) hxy_mem

/-- The positive-value ideal agrees with mathlib's maximal ideal of the
valuation ring. -/
theorem exponentialMaxIdeal_eq_maximalIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    exponentialMaxIdeal v =
      IsLocalRing.maximalIdeal (exponentialValuationSubring v) :=
  IsLocalRing.eq_maximalIdeal (exponentialMaxIdeal_isMaximal v)

/-- A discrete exponential valuation has a positive generator for its value group. -/
def DiscreteExponentialValuation {K : Type*} [Field K]
    (v : ExponentialValuation K) : Prop :=
  ∃ s : ℝ, 0 < s ∧
    (∀ x : K, x ≠ 0 → ∃ m : ℤ, v x = (((m : ℝ) * s : ℝ) : WithTop ℝ)) ∧
      ∃ π : K, v π = (s : WithTop ℝ)

/-- A normalized discrete exponential valuation has value group `ℤ`
and a prime element of value `1`.
-/
def NormalizedExponentialValuation {K : Type*} [Field K]
    (v : ExponentialValuation K) : Prop :=
  DiscreteExponentialValuation v ∧
    (∀ x : K, x ≠ 0 → ∃ m : ℤ, v x = ((m : ℝ) : WithTop ℝ)) ∧
      ∃ π : K, v π = (1 : WithTop ℝ)

/-- A prime element for a normalized exponential valuation. -/
def PrimeElementFor {K : Type*} [Field K]
    (v : ExponentialValuation K) (π : K) : Prop :=
  π ≠ 0 ∧ v π = (1 : WithTop ℝ)

/-- Value `1` gives a prime element for a normalized exponential valuation. -/
theorem primeElementFor_of_value_eq_one {K : Type*} [Field K]
    (v : ExponentialValuation K) {π : K}
    (hπ : v π = (1 : WithTop ℝ)) :
    PrimeElementFor v π := by
  constructor
  · intro hzero
    have htop : v π = ⊤ := (v.eq_top_iff π).mpr hzero
    rw [hπ] at htop
    simp at htop
  · exact hπ

/-- A normalized exponential valuation has a normalized prime element. -/
theorem normalizedExponentialValuation_exists_primeElement
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) :
    ∃ π : K, PrimeElementFor v π := by
  rcases hv.2.2 with ⟨π, hπ⟩
  exact ⟨π, primeElementFor_of_value_eq_one v hπ⟩

/-- A normalized prime element, regarded as an element of the valuation ring. -/
def primeElementInValuationSubring {K : Type*} [Field K]
    (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) :
    exponentialValuationSubring v :=
  ⟨π, by
    change (0 : WithTop ℝ) ≤ v π
    rw [hπ.2]
    change ((0 : ℝ) : WithTop ℝ) ≤ ((1 : ℝ) : WithTop ℝ)
    exact WithTop.coe_le_coe.mpr zero_le_one⟩

/-- A normalized prime element lies in the positive-value maximal ideal. -/
theorem primeElement_mem_exponentialMaxIdeal
    {K : Type*} [Field K] (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) :
    primeElementInValuationSubring v hπ ∈ exponentialMaxIdeal v := by
  change (0 : WithTop ℝ) < v π
  rw [hπ.2]
  change ((0 : ℝ) : WithTop ℝ) < ((1 : ℝ) : WithTop ℝ)
  exact WithTop.coe_lt_coe.mpr zero_lt_one

/-- A normalized prime element lies in mathlib's maximal ideal of the valuation ring. -/
theorem primeElement_mem_maximalIdeal
    {K : Type*} [Field K] (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) :
    primeElementInValuationSubring v hπ ∈
      IsLocalRing.maximalIdeal (exponentialValuationSubring v) := by
  rw [← exponentialMaxIdeal_eq_maximalIdeal v]
  exact primeElement_mem_exponentialMaxIdeal v hπ

/-- A normalized prime element is nonzero as an element of the valuation ring. -/
theorem primeElementInValuationSubring_ne_zero
    {K : Type*} [Field K] (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) :
    primeElementInValuationSubring v hπ ≠ 0 := by
  intro hzero
  exact hπ.1 (by
    simpa [primeElementInValuationSubring] using
      congrArg (fun x : exponentialValuationSubring v => (x : K)) hzero)

/-- A normalized prime element is not a unit of the valuation ring. -/
theorem primeElementInValuationSubring_not_isUnit
    {K : Type*} [Field K] (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) :
    ¬ IsUnit (primeElementInValuationSubring v hπ) := by
  intro hunit
  exact
    (not_mem_exponentialMaxIdeal_of_isUnit v hunit)
      (primeElement_mem_exponentialMaxIdeal v hπ)

/-- The inverse of a normalized prime element has value `-1`. -/
theorem primeElementFor_inv_value {K : Type*} [Field K]
    (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) :
    v π⁻¹ = ((-1 : ℝ) : WithTop ℝ) := by
  obtain ⟨s, hs⟩ :=
    exponentialValuation_exists_real_of_ne_zero v (inv_ne_zero hπ.1)
  have hmul := v.map_mul π π⁻¹
  rw [mul_inv_cancel₀ hπ.1, exponentialValuation_one v, hπ.2, hs] at hmul
  have hmul_real : (0 : ℝ) = 1 + s :=
    WithTop.coe_eq_coe.mp (by simpa [WithTop.coe_add] using hmul)
  have hs_eq : s = -1 := by
    linarith
  simp [hs, hs_eq]

/-- Powers of a normalized prime element have the expected normalized value. -/
theorem primeElementFor_pow_value {K : Type*} [Field K]
    (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) (n : ℕ) :
    v (π ^ n) = ((n : ℝ) : WithTop ℝ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, v.map_mul, ih, hπ.2]
      norm_num [Nat.cast_succ, WithTop.coe_add]

/-- Powers of a normalized prime element are nonzero in the ambient field. -/
theorem primeElementFor_pow_ne_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) (n : ℕ) :
    π ^ n ≠ 0 :=
  pow_ne_zero n hπ.1

/-- Integer powers of a normalized prime element have the expected normalized value. -/
theorem primeElementFor_zpow_value {K : Type*} [Field K]
    (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) (m : ℤ) :
    v (π ^ m) = ((m : ℝ) : WithTop ℝ) := by
  cases m with
  | ofNat n =>
      simpa [zpow_natCast] using primeElementFor_pow_value v hπ n
  | negSucc n =>
      have hpow_ne : π ^ (n + 1) ≠ 0 :=
        pow_ne_zero (n + 1) hπ.1
      have hpow_val :
          v (π ^ (n + 1)) = (((n + 1 : ℕ) : ℝ) : WithTop ℝ) :=
        primeElementFor_pow_value v hπ (n + 1)
      have hinv :
          v ((π ^ (n + 1))⁻¹) =
            ((-(((n + 1 : ℕ) : ℝ)) : ℝ) : WithTop ℝ) :=
        exponentialValuation_inv_value v hpow_ne hpow_val
      simpa [zpow_negSucc, Int.cast_negSucc, Nat.cast_add, Nat.cast_one] using hinv

/-- A unit times an integer power of a normalized prime element has value equal to the
exponent. -/
theorem primeElementFor_unit_mul_zpow_value
    {K : Type*} [Field K] (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π)
    (u : exponentialValuationSubring v) (hu : IsUnit u) (m : ℤ) :
    v ((u : K) * π ^ m) = ((m : ℝ) : WithTop ℝ) := by
  have hu_val : v (u : K) = 0 :=
    exponentialValuation_eq_zero_of_isUnit v hu
  rw [v.map_mul, hu_val, primeElementFor_zpow_value v hπ m]
  simp

/-- For a normalized exponential valuation and a normalized prime element, every
nonzero field element is a unit times an integer power of the prime element. -/
theorem normalizedExponentialValuation_exists_unit_mul_zpow
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π x : K}
    (hπ : PrimeElementFor v π) (hx : x ≠ 0) :
    ∃ m : ℤ, ∃ u : exponentialValuationSubring v,
      IsUnit u ∧ x = (u : K) * π ^ m := by
  rcases hv.2.1 x hx with ⟨m, hm⟩
  have hπm_ne : π ^ m ≠ 0 :=
    zpow_ne_zero m hπ.1
  have hπm_val : v (π ^ m) = ((m : ℝ) : WithTop ℝ) :=
    primeElementFor_zpow_value v hπ m
  have hπm_inv_val :
      v ((π ^ m)⁻¹) = ((-(m : ℝ) : ℝ) : WithTop ℝ) :=
    exponentialValuation_inv_value v hπm_ne hπm_val
  let uK : K := x * (π ^ m)⁻¹
  have hu_val : v uK = 0 := by
    dsimp [uK]
    rw [v.map_mul, hm, hπm_inv_val]
    norm_num [WithTop.coe_add]
  have hu_mem : uK ∈ exponentialValuationSubring v := by
    change (0 : WithTop ℝ) ≤ v uK
    rw [hu_val]
  let u : exponentialValuationSubring v := ⟨uK, hu_mem⟩
  have hu_val_sub : v (u : K) = 0 := by
    simpa [u, uK] using hu_val
  refine ⟨m, u, isUnit_of_exponentialValuation_eq_zero v hu_val_sub, ?_⟩
  change x = (x * (π ^ m)⁻¹) * π ^ m
  rw [mul_assoc, inv_mul_cancel₀ hπm_ne, mul_one]

/-- For a fixed integer exponent, the unit in a representation `u * π^m` is
unique. -/
theorem primeElementFor_unit_mul_zpow_unit_unique
    {K : Type*} [Field K] {v : ExponentialValuation K} {π : K}
    (hπ : PrimeElementFor v π) {m : ℤ}
    {u t : exponentialValuationSubring v}
    (h : (u : K) * π ^ m = (t : K) * π ^ m) :
    u = t := by
  apply Subtype.ext
  exact mul_right_cancel₀ (zpow_ne_zero m hπ.1) h

/-- The exponent in a representation `u * π^m` by a unit and a normalized prime
element is unique. -/
theorem primeElementFor_unit_mul_zpow_exponent_unique
    {K : Type*} [Field K] (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π)
    {m n : ℤ} {u t : exponentialValuationSubring v}
    (hu : IsUnit u) (ht : IsUnit t)
    (h : (u : K) * π ^ m = (t : K) * π ^ n) :
    m = n := by
  have hmval := primeElementFor_unit_mul_zpow_value v hπ u hu m
  have hnval := primeElementFor_unit_mul_zpow_value v hπ t ht n
  have hcoe : ((m : ℝ) : WithTop ℝ) = ((n : ℝ) : WithTop ℝ) := by
    rw [← hmval, h, hnval]
  have hreal : (m : ℝ) = (n : ℝ) :=
    WithTop.coe_eq_coe.mp hcoe
  exact Int.cast_inj.mp hreal

/-- The canonical representation `x = u * π^m` is unique: both the exponent and
the unit are determined by the represented element. -/
theorem primeElementFor_unit_mul_zpow_unique
    {K : Type*} [Field K] (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π)
    {m n : ℤ} {u t : exponentialValuationSubring v}
    (hu : IsUnit u) (ht : IsUnit t)
    (h : (u : K) * π ^ m = (t : K) * π ^ n) :
    m = n ∧ u = t := by
  have hmn : m = n :=
    primeElementFor_unit_mul_zpow_exponent_unique v hπ hu ht h
  have hunit : u = t := by
    apply primeElementFor_unit_mul_zpow_unit_unique hπ
    simpa [hmn] using h
  exact ⟨hmn, hunit⟩

/-- In a normalized exponential valuation, every nonzero element has a unique
normalized representation as a unit times an integer power of a prime element. -/
theorem normalizedExponentialValuation_exists_unique_unit_mul_zpow
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π x : K}
    (hπ : PrimeElementFor v π) (hx : x ≠ 0) :
    ∃ m : ℤ, ∃ u : exponentialValuationSubring v,
      IsUnit u ∧ x = (u : K) * π ^ m ∧
        ∀ n : ℤ, ∀ t : exponentialValuationSubring v,
          IsUnit t → x = (t : K) * π ^ n → n = m ∧ t = u := by
  rcases normalizedExponentialValuation_exists_unit_mul_zpow hv hπ hx with
    ⟨m, u, hu, hrep⟩
  refine ⟨m, u, hu, hrep, ?_⟩
  intro n t ht ht_rep
  have htu : (t : K) * π ^ n = (u : K) * π ^ m := by
    rw [← ht_rep, hrep]
  have huniq :=
    primeElementFor_unit_mul_zpow_unique v hπ ht hu htu
  exact huniq

/-- The same power-value formula for the prime element viewed inside the
valuation ring. -/
theorem primeElementInValuationSubring_pow_value
    {K : Type*} [Field K] (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) (n : ℕ) :
    v ((primeElementInValuationSubring v hπ : exponentialValuationSubring v) ^ n : K) =
      ((n : ℝ) : WithTop ℝ) := by
  change v (π ^ n) = ((n : ℝ) : WithTop ℝ)
  exact primeElementFor_pow_value v hπ n

/-- In a normalized exponential valuation, a normalized prime element generates the
positive-value maximal ideal. -/
theorem exponentialMaxIdeal_eq_span_primeElement_of_normalized
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) :
    exponentialMaxIdeal v =
      Ideal.span
        ({primeElementInValuationSubring v hπ} :
          Set (exponentialValuationSubring v)) := by
  apply le_antisymm
  · intro x hx
    change (0 : WithTop ℝ) < v (x : K) at hx
    by_cases hx0 : (x : K) = 0
    · have hx_eq : x = 0 := Subtype.ext hx0
      rw [hx_eq]
      exact
        Ideal.zero_mem
          (Ideal.span
            ({primeElementInValuationSubring v hπ} :
              Set (exponentialValuationSubring v)))
    · rcases hv.2.1 (x : K) hx0 with ⟨m, hm⟩
      have hxpos_real : (0 : ℝ) < (m : ℝ) := by
        have hxpos_wt :
            ((0 : ℝ) : WithTop ℝ) < ((m : ℝ) : WithTop ℝ) := by
          simpa [hm] using hx
        exact WithTop.coe_lt_coe.mp hxpos_wt
      have hm_pos : (0 : ℤ) < m := by
        exact Int.cast_pos.mp hxpos_real
      have hm_ge_one : (1 : ℤ) ≤ m := by
        omega
      have hm_sub_nonneg : (0 : ℝ) ≤ (m : ℝ) - 1 := by
        have hm_real : (1 : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast hm_ge_one
        linarith
      have hπinv : v π⁻¹ = ((-1 : ℝ) : WithTop ℝ) :=
        primeElementFor_inv_value v hπ
      have hy_val :
          v ((x : K) * π⁻¹) = (((m : ℝ) - 1 : ℝ) : WithTop ℝ) := by
        rw [v.map_mul, hm, hπinv]
        simp [sub_eq_add_neg, add_comm]
      have hy_mem : (x : K) * π⁻¹ ∈ exponentialValuationSubring v := by
        change (0 : WithTop ℝ) ≤ v ((x : K) * π⁻¹)
        rw [hy_val]
        change ((0 : ℝ) : WithTop ℝ) ≤ (((m : ℝ) - 1 : ℝ) : WithTop ℝ)
        exact WithTop.coe_le_coe.mpr hm_sub_nonneg
      let y : exponentialValuationSubring v := ⟨(x : K) * π⁻¹, hy_mem⟩
      refine Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩
      apply Subtype.ext
      change ((x : K) * π⁻¹) * π = (x : K)
      rw [mul_assoc, inv_mul_cancel₀ hπ.1, mul_one]
  · exact
      (Ideal.span_singleton_le_iff_mem
        (I := exponentialMaxIdeal v)
        (x := primeElementInValuationSubring v hπ)).mpr
        (primeElement_mem_exponentialMaxIdeal v hπ)

/-- A normalized prime element generates mathlib's maximal ideal of the valuation
ring for a normalized exponential valuation. -/
theorem maximalIdeal_eq_span_primeElement_of_normalized
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) :
    IsLocalRing.maximalIdeal (exponentialValuationSubring v) =
      Ideal.span
        ({primeElementInValuationSubring v hπ} :
          Set (exponentialValuationSubring v)) := by
  rw [← exponentialMaxIdeal_eq_maximalIdeal v]
  exact exponentialMaxIdeal_eq_span_primeElement_of_normalized hv hπ

/-- The principal ideal generated by a normalized prime element is maximal. -/
theorem span_primeElement_isMaximal_of_normalized
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) :
    (Ideal.span
      ({primeElementInValuationSubring v hπ} :
        Set (exponentialValuationSubring v))).IsMaximal := by
  rw [← maximalIdeal_eq_span_primeElement_of_normalized hv hπ]
  exact IsLocalRing.maximalIdeal.isMaximal (exponentialValuationSubring v)

/-- The principal ideal generated by a normalized prime element is prime. -/
theorem span_primeElement_isPrime_of_normalized
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) :
    (Ideal.span
      ({primeElementInValuationSubring v hπ} :
        Set (exponentialValuationSubring v))).IsPrime :=
  Ideal.IsMaximal.isPrime
    (span_primeElement_isMaximal_of_normalized hv hπ)

/-- A normalized prime element is prime as an element of the valuation ring. -/
theorem primeElementInValuationSubring_prime_of_normalized
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) :
    Prime (primeElementInValuationSubring v hπ) :=
  (Ideal.span_singleton_prime
    (primeElementInValuationSubring_ne_zero v hπ)).mp
    (span_primeElement_isPrime_of_normalized hv hπ)

/-- A normalized prime element is irreducible as an element of the valuation ring. -/
theorem primeElementInValuationSubring_irreducible_of_normalized
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) :
    Irreducible (primeElementInValuationSubring v hπ) :=
  (primeElementInValuationSubring_prime_of_normalized hv hπ).irreducible

/-- In a normalized exponential valuation, powers of the positive-value
maximal ideal are generated by powers of a normalized prime element. -/
theorem exponentialMaxIdeal_pow_eq_span_primeElement_pow_of_normalized
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) (n : ℕ) :
    (exponentialMaxIdeal v) ^ n =
      Ideal.span
        ({(primeElementInValuationSubring v hπ) ^ n} :
          Set (exponentialValuationSubring v)) := by
  rw [exponentialMaxIdeal_eq_span_primeElement_of_normalized hv hπ]
  exact Ideal.span_singleton_pow (primeElementInValuationSubring v hπ) n

/-- The DVR ideal `π^n𝒪`. -/
def uniformizerPowerIdeal {O : Type*} [CommRing O] (π : O) (n : ℕ) : Ideal O :=
  Ideal.span ({π ^ n} : Set O)

/-- Value description of a principal power ideal from the value of powers of
its generator.  This is the common calculation behind both the normalized
and the scaled discrete forms of the ideal structure theorem for discrete valuation rings. -/
theorem uniformizerPowerIdeal_mem_iff_value_ge_of_pow_value
    {K : Type*} [Field K] (v : ExponentialValuation K)
    {π : K} (πR : exponentialValuationSubring v)
    (hπR : (πR : K) = π) {s : ℝ} (hπ0 : π ≠ 0)
    (hpow : ∀ n : ℕ, v (π ^ n) = (((n : ℝ) * s : ℝ) : WithTop ℝ))
    (n : ℕ) (x : exponentialValuationSubring v) :
    x ∈ uniformizerPowerIdeal πR n ↔
      (((n : ℝ) * s : ℝ) : WithTop ℝ) ≤ v (x : K) := by
  constructor
  · intro hx
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton'] at hx
    rcases hx with ⟨a, ha⟩
    have hcast : (x : K) = (a : K) * π ^ n := by
      have hcast0 :=
        congrArg (fun y : exponentialValuationSubring v => (y : K)) ha.symm
      simpa [hπR] using hcast0
    have ha_nonneg : (0 : WithTop ℝ) ≤ v (a : K) := a.property
    have hpow_val :
        v (π ^ n) = (((n : ℝ) * s : ℝ) : WithTop ℝ) :=
      hpow n
    have hx_val :
        v (x : K) = v (a : K) + (((n : ℝ) * s : ℝ) : WithTop ℝ) := by
      rw [hcast, v.map_mul, hpow_val]
    calc
      (((n : ℝ) * s : ℝ) : WithTop ℝ) =
          0 + (((n : ℝ) * s : ℝ) : WithTop ℝ) := by simp
      _ ≤ v (a : K) + (((n : ℝ) * s : ℝ) : WithTop ℝ) :=
        add_le_add ha_nonneg le_rfl
      _ = v (x : K) := hx_val.symm
  · intro hx
    by_cases hx0 : (x : K) = 0
    · have hx_eq : x = 0 := Subtype.ext hx0
      rw [hx_eq]
      exact Ideal.zero_mem (uniformizerPowerIdeal πR n)
    · obtain ⟨r, hr⟩ := exponentialValuation_exists_real_of_ne_zero v hx0
      have hn_le_r : (n : ℝ) * s ≤ r := by
        have hle :
            ((((n : ℝ) * s : ℝ) : WithTop ℝ) ≤ ((r : ℝ) : WithTop ℝ)) := by
          simpa [hr] using hx
        exact WithTop.coe_le_coe.mp hle
      have hpow_ne : π ^ n ≠ 0 := pow_ne_zero n hπ0
      have hpow_val :
          v (π ^ n) = (((n : ℝ) * s : ℝ) : WithTop ℝ) :=
        hpow n
      have hinv_val :
          v ((π ^ n)⁻¹) = ((-((n : ℝ) * s) : ℝ) : WithTop ℝ) :=
        exponentialValuation_inv_value v hpow_ne hpow_val
      let aK : K := (x : K) * (π ^ n)⁻¹
      have ha_val :
          v aK = (((r - (n : ℝ) * s) : ℝ) : WithTop ℝ) := by
        dsimp [aK]
        rw [v.map_mul, hr, hinv_val]
        simp [sub_eq_add_neg, add_comm]
      have ha_mem : aK ∈ exponentialValuationSubring v := by
        change (0 : WithTop ℝ) ≤ v aK
        rw [ha_val]
        exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr hn_le_r)
      let a : exponentialValuationSubring v := ⟨aK, ha_mem⟩
      rw [uniformizerPowerIdeal, Ideal.mem_span_singleton']
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change ((x : K) * (π ^ n)⁻¹) * (πR : K) ^ n = (x : K)
      rw [hπR, mul_assoc, inv_mul_cancel₀ hpow_ne, mul_one]

/-- If an ideal contains an element whose value is exactly the value of
`π^n`, then it contains the principal ideal generated by `π^n`. -/
theorem uniformizerPowerIdeal_le_ideal_of_mem_value_eq_of_pow_value
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {π : K} (πR : exponentialValuationSubring v)
    (hπR : (πR : K) = π) {s : ℝ} (hπ0 : π ≠ 0)
    (hpow : ∀ n : ℕ, v (π ^ n) = (((n : ℝ) * s : ℝ) : WithTop ℝ))
    {I : Ideal (exponentialValuationSubring v)} {n : ℕ}
    {x : exponentialValuationSubring v}
    (hxI : x ∈ I)
    (hxval : v (x : K) = (((n : ℝ) * s : ℝ) : WithTop ℝ)) :
    uniformizerPowerIdeal πR n ≤ I := by
  have hpow_ne : π ^ n ≠ 0 := pow_ne_zero n hπ0
  have hpow_val :
      v (π ^ n) = (((n : ℝ) * s : ℝ) : WithTop ℝ) :=
    hpow n
  have hinv_val :
      v ((π ^ n)⁻¹) = ((-((n : ℝ) * s) : ℝ) : WithTop ℝ) :=
    exponentialValuation_inv_value v hpow_ne hpow_val
  let uK : K := (x : K) * (π ^ n)⁻¹
  have hu_val : v uK = 0 := by
    dsimp [uK]
    rw [v.map_mul, hxval, hinv_val]
    change ((((n : ℝ) * s + -((n : ℝ) * s) : ℝ) : WithTop ℝ) = 0)
    simp
  have hu_mem : uK ∈ exponentialValuationSubring v := by
    change (0 : WithTop ℝ) ≤ v uK
    rw [hu_val]
  let u : exponentialValuationSubring v := ⟨uK, hu_mem⟩
  have hu_subval : v (u : K) = 0 := by
    simpa [u, uK] using hu_val
  have hu_unit : IsUnit u :=
    isUnit_of_exponentialValuation_eq_zero v hu_subval
  have hx_repr : x = u * πR ^ n := by
    apply Subtype.ext
    change (x : K) = ((x : K) * (π ^ n)⁻¹) * (πR : K) ^ n
    rw [hπR, mul_assoc, inv_mul_cancel₀ hpow_ne, mul_one]
  rw [uniformizerPowerIdeal, Ideal.span_singleton_le_iff_mem]
  rcases hu_unit with ⟨uUnit, huUnit⟩
  have hxI' : u * πR ^ n ∈ I := by
    simpa [hx_repr] using hxI
  have hmem :
      ((uUnit⁻¹ : (exponentialValuationSubring v)ˣ) :
          exponentialValuationSubring v) *
        (u * πR ^ n) ∈ I :=
    I.mul_mem_left _ hxI'
  simpa [← huUnit, mul_assoc] using hmem

/-- A nonzero ideal has an element of least indexed value whenever every
nonzero element has a value in a monotone sequence.  This isolates the
well-ordering argument shared by the normalized and scaled forms of
the ideal structure theorem for discrete valuation rings. -/
theorem ideal_exists_min_value_of_nat_indexed_values
    {O α : Type*} [CommRing O] [Preorder α]
    (value : O → α) (weight : ℕ → α) (hweight : Monotone weight)
    (hvalue : ∀ x : O, x ≠ 0 → ∃ n : ℕ, value x = weight n)
    (I : Ideal O) (hI : I ≠ ⊥) :
    ∃ n : ℕ, ∃ x : O,
      x ∈ I ∧ x ≠ 0 ∧ value x = weight n ∧
        ∀ y : O, y ∈ I → y ≠ 0 → weight n ≤ value y := by
  classical
  have hnonzero : ∃ x : O, x ∈ I ∧ x ≠ 0 := by
    by_contra h
    push Not at h
    apply hI
    apply le_antisymm
    · intro x hx
      simp [h x hx]
    · exact bot_le
  let P : ℕ → Prop := fun n => ∃ x : O, x ∈ I ∧ x ≠ 0 ∧ value x = weight n
  have hP : ∃ n : ℕ, P n := by
    rcases hnonzero with ⟨x, hxI, hx0⟩
    rcases hvalue x hx0 with ⟨n, hn⟩
    exact ⟨n, x, hxI, hx0, hn⟩
  let n : ℕ := Nat.find hP
  rcases Nat.find_spec hP with ⟨x, hxI, hx0, hxval⟩
  refine ⟨n, x, hxI, hx0, hxval, ?_⟩
  intro y hyI hy0
  rcases hvalue y hy0 with ⟨m, hm⟩
  have hnm : n ≤ m := Nat.find_min' hP ⟨y, hyI, hy0, hm⟩
  exact (hweight hnm).trans_eq hm.symm

/-- The ideal structure theorem for discrete valuation rings, value description of the ideals `π^n𝒪`: for a normalized
prime element, membership in the principal power ideal is exactly the lower
bound `v(x) ≥ n`. -/
theorem uniformizerPowerIdeal_mem_iff_value_ge
    {K : Type*} [Field K] (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) (n : ℕ)
    (x : exponentialValuationSubring v) :
    x ∈ uniformizerPowerIdeal (primeElementInValuationSubring v hπ) n ↔
      ((n : ℝ) : WithTop ℝ) ≤ v (x : K) := by
  simpa [mul_one] using
    uniformizerPowerIdeal_mem_iff_value_ge_of_pow_value
      (v := v) (π := π) (πR := primeElementInValuationSubring v hπ)
      rfl (s := 1) hπ.1
      (fun n => by
        simpa [mul_one] using primeElementFor_pow_value v hπ n)
      n x

/-- A nonnegative member of a positive real lattice has a natural-number
index.  This is the order-theoretic step common to normalized and scaled
discrete valuations. -/
theorem exists_nat_index_of_nonneg_int_multiple
    {a : WithTop ℝ} {s : ℝ} (ha : 0 ≤ a) (hs : 0 < s)
    (h : ∃ m : ℤ, a = (((m : ℝ) * s : ℝ) : WithTop ℝ)) :
    ∃ n : ℕ, a = (((n : ℝ) * s : ℝ) : WithTop ℝ) := by
  rcases h with ⟨m, rfl⟩
  cases m with
  | ofNat n => exact ⟨n, by simp⟩
  | negSucc n =>
      have hmneg : ((Int.negSucc n : ℤ) : ℝ) < 0 := by
        have hcast :
            ((Int.negSucc n : ℤ) : ℝ) = -((n : ℝ) + 1) := by
          norm_num [Int.cast_negSucc]
        rw [hcast]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
      exact False.elim <| (not_lt_of_ge (WithTop.coe_le_coe.mp ha))
        (mul_neg_of_neg_of_pos hmneg hs)

/-- In a normalized exponential valuation, a nonzero element of the valuation
ring has a natural-number value. -/
theorem normalizedExponentialValuation_subring_exists_nat_value
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v)
    {x : exponentialValuationSubring v} (hx : (x : K) ≠ 0) :
    ∃ n : ℕ, v (x : K) = ((n : ℝ) : WithTop ℝ) := by
  have hindexed :
      ∃ m : ℤ, v (x : K) = (((m : ℝ) * 1 : ℝ) : WithTop ℝ) := by
    rcases hv.2.1 (x : K) hx with ⟨m, hm⟩
    exact ⟨m, by simpa using hm⟩
  rcases exists_nat_index_of_nonneg_int_multiple x.property zero_lt_one hindexed with
    ⟨n, hn⟩
  exact ⟨n, by simpa using hn⟩

/-- If an ideal contains an element of value exactly `n`, then it contains
`π^n𝒪`. -/
theorem uniformizerPowerIdeal_le_ideal_of_mem_value_eq
    {K : Type*} [Field K] {v : ExponentialValuation K} {π : K}
    (hπ : PrimeElementFor v π)
    {I : Ideal (exponentialValuationSubring v)} {n : ℕ}
    {x : exponentialValuationSubring v}
    (hxI : x ∈ I)
    (hxval : v (x : K) = ((n : ℝ) : WithTop ℝ)) :
    uniformizerPowerIdeal (primeElementInValuationSubring v hπ) n ≤ I := by
  exact
    uniformizerPowerIdeal_le_ideal_of_mem_value_eq_of_pow_value
      (v := v) (π := π) (πR := primeElementInValuationSubring v hπ)
      rfl (s := 1) hπ.1
      (fun n => by
        simpa [mul_one] using primeElementFor_pow_value v hπ n)
      hxI (by simpa [mul_one] using hxval)

/-- The ideal structure theorem for discrete valuation rings, ideal classification part: every nonzero ideal of a
normalized exponential-valuation ring is one of the ideals `π^n𝒪`. -/
theorem nonzero_ideal_eq_uniformizerPowerIdeal
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π)
    (I : Ideal (exponentialValuationSubring v)) (hI : I ≠ ⊥) :
    ∃ n : ℕ,
      I = uniformizerPowerIdeal (primeElementInValuationSubring v hπ) n := by
  have hvalue :
      ∀ x : exponentialValuationSubring v, x ≠ 0 →
        ∃ n : ℕ, v (x : K) = ((n : ℝ) : WithTop ℝ) := by
    intro x hx
    apply normalizedExponentialValuation_subring_exists_nat_value hv
    intro hxK
    exact hx (Subtype.ext hxK)
  rcases ideal_exists_min_value_of_nat_indexed_values
      (value := fun x : exponentialValuationSubring v => v (x : K))
      (weight := fun n : ℕ => ((n : ℝ) : WithTop ℝ))
      (fun _ _ hnm => WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnm))
      hvalue I hI with
    ⟨n, x, hxI, _hx0, hxval, hmin⟩
  refine ⟨n, le_antisymm ?_ ?_⟩
  · intro y hyI
    rw [uniformizerPowerIdeal_mem_iff_value_ge v hπ n y]
    by_cases hyK0 : (y : K) = 0
    · have hyval_top : v (y : K) = ⊤ := (v.eq_top_iff (y : K)).mpr hyK0
      rw [hyval_top]
      simp
    · have hy0 : y ≠ 0 := by
        intro hy0
        exact hyK0 (by
          simpa using
            congrArg (fun z : exponentialValuationSubring v => (z : K)) hy0)
      exact hmin y hyI hy0
  · exact uniformizerPowerIdeal_le_ideal_of_mem_value_eq hπ hxI hxval

/-- The ideal structure theorem for discrete valuation rings, PID part: the valuation ring of a normalized
exponential valuation is a principal ideal ring. -/
theorem normalizedExponentialValuationSubring_isPrincipalIdealRing
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) :
    IsPrincipalIdealRing (exponentialValuationSubring v) := by
  constructor
  intro I
  by_cases hI : I = ⊥
  · rw [hI]
    exact ⟨0, by simp⟩
  · rcases nonzero_ideal_eq_uniformizerPowerIdeal hv hπ I hI with
      ⟨n, hIn⟩
    refine ⟨(primeElementInValuationSubring v hπ) ^ n, ?_⟩
    rw [hIn, uniformizerPowerIdeal]

/-- The ideal structure theorem for discrete valuation rings, DVR part: the valuation ring of a normalized
exponential valuation is a discrete valuation ring. -/
theorem normalizedExponentialValuationSubring_isDiscreteValuationRing
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) :
    IsDiscreteValuationRing (exponentialValuationSubring v) := by
  have : IsPrincipalIdealRing (exponentialValuationSubring v) :=
    normalizedExponentialValuationSubring_isPrincipalIdealRing hv hπ
  refine { not_a_field' := ?_ }
  intro hmax
  have hπ_mem :
      primeElementInValuationSubring v hπ ∈
        IsLocalRing.maximalIdeal (exponentialValuationSubring v) :=
    primeElement_mem_maximalIdeal v hπ
  have hπ_bot :
      primeElementInValuationSubring v hπ ∈
        (⊥ : Ideal (exponentialValuationSubring v)) := by
    simpa [hmax] using hπ_mem
  have hπ_zero : primeElementInValuationSubring v hπ = 0 := by
    simpa using hπ_bot
  exact primeElementInValuationSubring_ne_zero v hπ hπ_zero

/-- A field element of positive discrete value, viewed inside the valuation ring. -/
def discretePrimeElementInValuationSubring
    {K : Type*} [Field K] (v : ExponentialValuation K)
    {π : K} {s : ℝ} (hs : 0 ≤ s) (hπ : v π = (s : WithTop ℝ)) :
    exponentialValuationSubring v :=
  ⟨π, by
    change (0 : WithTop ℝ) ≤ v π
    rw [hπ]
    exact WithTop.coe_le_coe.mpr hs⟩

/-- A finite positive value forces the chosen discrete prime element to be nonzero. -/
theorem discretePrimeElement_ne_zero_of_value
    {K : Type*} [Field K] (v : ExponentialValuation K)
    {π : K} {s : ℝ} (hπ : v π = (s : WithTop ℝ)) :
    π ≠ 0 := by
  intro hzero
  have htop : v π = ⊤ := (v.eq_top_iff π).mpr hzero
  rw [hπ] at htop
  simp at htop

/-- Powers of a discrete prime element have the expected scaled value. -/
theorem discretePrimeElement_pow_value
    {K : Type*} [Field K] (v : ExponentialValuation K)
    {π : K} {s : ℝ} (hπ : v π = (s : WithTop ℝ)) (n : ℕ) :
    v (π ^ n) = (((n : ℝ) * s : ℝ) : WithTop ℝ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, v.map_mul, ih, hπ]
      change ((((n : ℝ) * s + s : ℝ) : WithTop ℝ) =
        ((((n + 1 : ℕ) : ℝ) * s : ℝ) : WithTop ℝ))
      congr 1
      norm_num [Nat.cast_succ]
      ring

/-- A nonzero element of the valuation ring of a discrete valuation has a
nonnegative integer multiple of the least positive value. -/
theorem discreteExponentialValuation_subring_exists_nat_value
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {s : ℝ} (hs : 0 < s)
    (hvalues : ∀ x : K, x ≠ 0 → ∃ m : ℤ,
      v x = (((m : ℝ) * s : ℝ) : WithTop ℝ))
    {x : exponentialValuationSubring v} (hx : (x : K) ≠ 0) :
    ∃ n : ℕ, v (x : K) = (((n : ℝ) * s : ℝ) : WithTop ℝ) := by
  exact exists_nat_index_of_nonneg_int_multiple x.property hs (hvalues (x : K) hx)

/-- The ideal structure theorem for discrete valuation rings, scaled value description for a non-normalized discrete
prime element: membership in `π^n𝒪` is the lower bound `n * s ≤ v(x)`. -/
theorem discrete_uniformizerPowerIdeal_mem_iff_value_ge
    {K : Type*} [Field K] (v : ExponentialValuation K)
    {π : K} {s : ℝ} (hs : 0 < s) (hπ : v π = (s : WithTop ℝ))
    (n : ℕ) (x : exponentialValuationSubring v) :
    x ∈ uniformizerPowerIdeal
        (discretePrimeElementInValuationSubring v (le_of_lt hs) hπ) n ↔
      (((n : ℝ) * s : ℝ) : WithTop ℝ) ≤ v (x : K) := by
  have hπ0 : π ≠ 0 := discretePrimeElement_ne_zero_of_value v hπ
  exact
    uniformizerPowerIdeal_mem_iff_value_ge_of_pow_value
      (v := v) (π := π)
      (πR := discretePrimeElementInValuationSubring v (le_of_lt hs) hπ)
      rfl (s := s) hπ0 (discretePrimeElement_pow_value v hπ) n x

/-- If an ideal contains an element of scaled value `n * s`, then it contains
the principal ideal `π^n𝒪`. -/
theorem discreteUniformizerPowerIdeal_le_ideal_of_mem_value_eq
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {π : K} {s : ℝ} (hs : 0 < s) (hπ : v π = (s : WithTop ℝ))
    {I : Ideal (exponentialValuationSubring v)} {n : ℕ}
    {x : exponentialValuationSubring v}
    (hxI : x ∈ I)
    (hxval : v (x : K) = (((n : ℝ) * s : ℝ) : WithTop ℝ)) :
    uniformizerPowerIdeal
      (discretePrimeElementInValuationSubring v (le_of_lt hs) hπ) n ≤ I := by
  have hπ0 : π ≠ 0 := discretePrimeElement_ne_zero_of_value v hπ
  exact
    uniformizerPowerIdeal_le_ideal_of_mem_value_eq_of_pow_value
      (v := v) (π := π)
      (πR := discretePrimeElementInValuationSubring v (le_of_lt hs) hπ)
      rfl (s := s) hπ0 (discretePrimeElement_pow_value v hπ) hxI hxval

/-- The ideal structure theorem for discrete valuation rings, canonical PID part for an arbitrary discrete
exponential valuation, before choosing the normalized representative. -/
theorem discreteExponentialValuationSubring_isPrincipalIdealRing
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : DiscreteExponentialValuation v) :
    IsPrincipalIdealRing (exponentialValuationSubring v) := by
  rcases hv with ⟨s, hs, hvalues, π, hπ⟩
  let πR : exponentialValuationSubring v :=
    discretePrimeElementInValuationSubring v (le_of_lt hs) hπ
  constructor
  intro I
  by_cases hI : I = ⊥
  · rw [hI]
    exact ⟨0, by simp⟩
  · have hvalue :
        ∀ x : exponentialValuationSubring v, x ≠ 0 →
          ∃ n : ℕ, v (x : K) = (((n : ℝ) * s : ℝ) : WithTop ℝ) := by
      intro x hx
      apply discreteExponentialValuation_subring_exists_nat_value hs hvalues
      intro hxK
      exact hx (Subtype.ext hxK)
    rcases ideal_exists_min_value_of_nat_indexed_values
        (value := fun x : exponentialValuationSubring v => v (x : K))
        (weight := fun n : ℕ => (((n : ℝ) * s : ℝ) : WithTop ℝ))
        (fun _ _ hnm => WithTop.coe_le_coe.mpr
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm) (le_of_lt hs)))
        hvalue I hI with ⟨n, x, hxI, _hx0, hxval, hmin⟩
    refine ⟨πR ^ n, le_antisymm ?_ ?_⟩
    · intro y hyI
      change y ∈ uniformizerPowerIdeal πR n
      rw [discrete_uniformizerPowerIdeal_mem_iff_value_ge v hs hπ n y]
      by_cases hyK0 : (y : K) = 0
      · have hyval_top : v (y : K) = ⊤ := (v.eq_top_iff (y : K)).mpr hyK0
        rw [hyval_top]
        simp
      · have hy0 : y ≠ 0 := by
          intro hy0
          exact hyK0 (by
            simpa using
              congrArg (fun z : exponentialValuationSubring v => (z : K)) hy0)
        exact hmin y hyI hy0
    · change uniformizerPowerIdeal πR n ≤ I
      exact discreteUniformizerPowerIdeal_le_ideal_of_mem_value_eq hs hπ hxI hxval

/-- The ideal structure theorem for discrete valuation rings, canonical DVR part for an arbitrary discrete
exponential valuation. -/
theorem discreteExponentialValuationSubring_isDiscreteValuationRing
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : DiscreteExponentialValuation v) :
    IsDiscreteValuationRing (exponentialValuationSubring v) := by
  rcases hv with ⟨s, hs, hvalues, π, hπ⟩
  have hv' : DiscreteExponentialValuation v :=
    ⟨s, hs, hvalues, π, hπ⟩
  have : IsPrincipalIdealRing (exponentialValuationSubring v) :=
    discreteExponentialValuationSubring_isPrincipalIdealRing hv'
  refine { not_a_field' := ?_ }
  intro hmax
  let πR : exponentialValuationSubring v :=
    discretePrimeElementInValuationSubring v (le_of_lt hs) hπ
  have hπ_mem :
      πR ∈ IsLocalRing.maximalIdeal (exponentialValuationSubring v) := by
    rw [← exponentialMaxIdeal_eq_maximalIdeal v]
    change (0 : WithTop ℝ) < v π
    rw [hπ]
    exact WithTop.coe_lt_coe.mpr hs
  have hπ_bot : πR ∈ (⊥ : Ideal (exponentialValuationSubring v)) := by
    simpa [hmax] using hπ_mem
  have hπ_zero : πR = 0 := by
    simpa using hπ_bot
  have hπ_ne : π ≠ 0 := discretePrimeElement_ne_zero_of_value v hπ
  exact hπ_ne (by
    simpa [πR, discretePrimeElementInValuationSubring] using
      congrArg (fun x : exponentialValuationSubring v => (x : K)) hπ_zero)
end Valuations
end LubinTate
