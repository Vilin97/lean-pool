/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.Core
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring
/-!
# Closed unit balls of nonarchimedean absolute values

This file records the valuation ring attached directly to a multiplicative
absolute value in the nonarchimedean case.  It is the section-3 object used by
the finite-degree norm construction before any discrete-valuation-field packaging.
-/

@[expose] public section

noncomputable
section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- The closed unit ball `{x | |x| ≤ 1}` of a nonarchimedean absolute value,
bundled as a subring. -/
def absoluteValueUnitBallSubring
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) : Subring K where
  carrier := {x | v x ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact (LubinTate.Valuations.strong_triangle_of_nonarchimedean
      v hnonarch x y).trans (max_le hx hy)
  neg_mem' := by
    intro x hx
    simpa using hx
  mul_mem' := by
    intro x y hx hy
    change v (x * y) ≤ 1
    rw [v.map_mul]
    exact (mul_le_of_le_one_left (v.nonneg y) hx).trans hy

/-- Membership in the absolute-value valuation subring is the closed-unit-ball
condition. -/
theorem mem_absoluteValueUnitBallSubring_iff
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (x : K) :
    x ∈ absoluteValueUnitBallSubring v hnonarch ↔ v x ≤ 1 :=
  Iff.rfl

/-- Every field element or its inverse lies in the closed unit ball of a
nonarchimedean absolute value. -/
theorem absoluteValueUnitBallSubring_mem_or_inv_mem
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (x : K) :
    x ∈ absoluteValueUnitBallSubring v hnonarch ∨
      x⁻¹ ∈ absoluteValueUnitBallSubring v hnonarch := by
  by_cases hx : v x ≤ 1
  · exact Or.inl ((mem_absoluteValueUnitBallSubring_iff
      v hnonarch x).2 hx)
  · right
    have hx_gt : 1 < v x := lt_of_not_ge hx
    rw [mem_absoluteValueUnitBallSubring_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hx_gt.le

/-- The closed unit ball of a nonarchimedean absolute value, bundled as
mathlib's `ValuationSubring`. -/
def absoluteValueValuationSubring
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    ValuationSubring K :=
  ValuationSubring.ofSubring
    (absoluteValueUnitBallSubring v hnonarch)
    (absoluteValueUnitBallSubring_mem_or_inv_mem v hnonarch)

/-- Membership in the bundled valuation subring is again the closed-unit-ball
condition. -/
theorem mem_absoluteValueValuationSubring_iff
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (x : K) :
    x ∈ absoluteValueValuationSubring v hnonarch ↔
      v x ≤ 1 := by
  exact (ValuationSubring.mem_ofSubring
    (absoluteValueUnitBallSubring v hnonarch)
    (absoluteValueUnitBallSubring_mem_or_inv_mem v hnonarch) x).trans
    (mem_absoluteValueUnitBallSubring_iff v hnonarch x)

/-- In any submonoid of a field whose elements are exactly the closed unit
ball of an absolute value, the units are exactly the elements of absolute
value `1`. -/
theorem isUnit_iff_abs_eq_one_of_mem_iff_le_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {C : Type*} [SetLike C K] [SubmonoidClass C K]
    (S : C) (hS : ∀ x : K, x ∈ S ↔ v x ≤ 1) (x : S) :
    IsUnit x ↔ v (x : K) = 1 := by
  constructor
  · intro hx
    have hx_inv :=
      (Submonoid.isUnit_iff_and (S := S) (a := x)).mp hx
    have hx_le : v (x : K) ≤ 1 := (hS (x : K)).1 x.property
    have hinv_le : v ((x : K)⁻¹) ≤ 1 :=
      (hS ((x : K)⁻¹)).1 hx_inv.2
    have hmul : v (x : K) * v ((x : K)⁻¹) = 1 := by
      rw [← v.map_mul, mul_inv_cancel₀ hx_inv.1]
      simp
    have hge : 1 ≤ v (x : K) := by
      calc
        1 = v (x : K) * v ((x : K)⁻¹) := hmul.symm
        _ ≤ v (x : K) * 1 :=
          mul_le_mul_of_nonneg_left hinv_le (v.nonneg (x : K))
        _ = v (x : K) := by simp
    exact le_antisymm hx_le hge
  · intro hx
    rw [Submonoid.isUnit_iff_and (S := S) (a := x)]
    constructor
    · intro hx_zero
      have hzero_one : (0 : ℝ) = 1 := by
        simp [hx_zero] at hx
      exact zero_ne_one hzero_one
    · exact (hS ((x : K)⁻¹)).2 <| by
        rw [map_inv₀, hx]
        simp

/-- In the same closed-unit-ball situation, nonunits are exactly the elements
of absolute value strictly less than `1`. -/
theorem not_isUnit_iff_abs_lt_one_of_mem_iff_le_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {C : Type*} [SetLike C K] [SubmonoidClass C K]
    (S : C) (hS : ∀ x : K, x ∈ S ↔ v x ≤ 1) (x : S) :
    ¬ IsUnit x ↔ v (x : K) < 1 := by
  have hx_le : v (x : K) ≤ 1 := (hS (x : K)).1 x.property
  rw [isUnit_iff_abs_eq_one_of_mem_iff_le_one v S hS]
  exact hx_le.lt_iff_ne.symm

/-- The same unit criterion for the valuation-subring bundle of the closed
unit ball. -/
theorem absoluteValueUnitBallSubringAsValuationSubring_isUnit_iff_abs_eq_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (x : absoluteValueValuationSubring v hnonarch) :
    IsUnit x ↔ v (x : K) = 1 :=
  isUnit_iff_abs_eq_one_of_mem_iff_le_one
    v (absoluteValueValuationSubring v hnonarch)
    (mem_absoluteValueValuationSubring_iff v hnonarch) x

/-- The maximal ideal of the closed-unit-ball valuation subring consists
exactly of the elements of absolute value strictly less than `1`. -/
theorem absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (x : absoluteValueValuationSubring v hnonarch) :
    x ∈ IsLocalRing.maximalIdeal
        (absoluteValueValuationSubring v hnonarch) ↔
      v (x : K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_isUnit_iff_abs_lt_one_of_mem_iff_le_one
    v (absoluteValueValuationSubring v hnonarch)
    (mem_absoluteValueValuationSubring_iff v hnonarch) x

/-- A closed-unit-ball element reduces to zero in the residue field exactly
when its absolute value is strictly less than `1`. -/
theorem absoluteValueUnitBallSubringAsValuationSubring_residue_eq_zero_iff_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (x : absoluteValueValuationSubring v hnonarch) :
    IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch) x = 0 ↔
      v (x : K) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff,
    absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one]

/-- A closed-unit-ball element has nonzero residue exactly when its absolute
value is `1`. -/
theorem absoluteValueUnitBallSubringAsValuationSubring_residue_ne_zero_iff_abs_eq_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (x : absoluteValueValuationSubring v hnonarch) :
    IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch) x ≠ 0 ↔
      v (x : K) = 1 := by
  have hx_le : v (x : K) ≤ 1 :=
    (mem_absoluteValueValuationSubring_iff
      v hnonarch (x : K)).1 x.property
  rw [ne_eq,
    absoluteValueUnitBallSubringAsValuationSubring_residue_eq_zero_iff_abs_lt_one]
  constructor
  · intro hx
    exact le_antisymm hx_le (not_lt.mp hx)
  · intro hx
    rw [hx]
    exact not_lt_of_ge le_rfl

/-- The closed unit ball of a nonarchimedean absolute value is integrally
closed in the ambient field. -/
theorem absoluteValueUnitBallSubring_isIntegrallyClosedIn
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    IsIntegrallyClosedIn (absoluteValueUnitBallSubring v hnonarch) K := by
  let V := absoluteValueValuationSubring v hnonarch
  change IsIntegrallyClosedIn V K
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn (R := V) (K := K)).mp
    inferInstance

/-- If an absolute value on `L` extends one on `K`, then its valuation subring
pulls back to the base valuation subring. -/
theorem comap_absoluteValueUnitBallSubring_eq_of_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (hvnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hwnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue w)
    (hw_ext : ∀ x : K, w (algebraMap K L x) = v x) :
    (absoluteValueUnitBallSubring w hwnonarch).comap
        (algebraMap K L) =
      absoluteValueUnitBallSubring v hvnonarch := by
  ext x
  change w (algebraMap K L x) ≤ 1 ↔ v x ≤ 1
  rw [hw_ext x]

/-- A polynomial over the field lifts from the closed-unit-ball valuation
subring exactly when all its coefficients lie in that valuation subring. -/
theorem polynomial_lifts_absoluteValueUnitBallSubring_iff_coeff_mem
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (f : K[X]) :
    f ∈ Polynomial.lifts
        (algebraMap (absoluteValueUnitBallSubring v hnonarch) K) ↔
      ∀ n : ℕ, f.coeff n ∈ absoluteValueUnitBallSubring v hnonarch := by
  rw [Polynomial.lifts_iff_coeff_lifts
    (f := algebraMap (absoluteValueUnitBallSubring v hnonarch) K)]
  constructor
  · intro h n
    rcases h n with ⟨a, ha⟩
    rw [← ha]
    exact a.property
  · intro h n
    exact ⟨⟨f.coeff n, h n⟩, rfl⟩

/-- Monic lift form used by irreducible-polynomial lifting: a monic field polynomial whose
coefficients lie in the closed unit ball has a monic valuation-ring lift of
the same natural degree. -/
theorem exists_monic_polynomial_over_absoluteValueUnitBallSubring_of_coeff_mem
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) {f : K[X]}
    (hfmonic : f.Monic)
    (hfcoeff : ∀ n : ℕ, f.coeff n ∈ absoluteValueUnitBallSubring v hnonarch) :
    ∃ F : (absoluteValueUnitBallSubring v hnonarch)[X],
      F.Monic ∧
        F.map (algebraMap (absoluteValueUnitBallSubring v hnonarch) K) = f ∧
        F.natDegree = f.natDegree := by
  have hlifts :
      f ∈ Polynomial.lifts
        (algebraMap (absoluteValueUnitBallSubring v hnonarch) K) :=
    (polynomial_lifts_absoluteValueUnitBallSubring_iff_coeff_mem
      v hnonarch f).2 hfcoeff
  rcases Polynomial.lifts_and_natDegree_eq_and_monic
      (f := algebraMap (absoluteValueUnitBallSubring v hnonarch) K)
      hlifts hfmonic with
    ⟨F, hmap, hdeg, hmonic⟩
  exact ⟨F, hmonic, hmap, hdeg⟩

/-- A field polynomial whose coefficients lie in the closed unit ball has a
degree-preserving lift to the actual valuation-subring bundle used for
residue fields.  The lift may be chosen coefficientwise, so the absolute
values of the lifted coefficients are the original coefficient values. -/
theorem exists_polynomial_over_absoluteValueUnitBallSubringAsValuationSubring_of_coeff_abs_le_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (f : K[X])
    (hfcoeff : ∀ n : ℕ, v (f.coeff n) ≤ 1) :
    ∃ F : (absoluteValueValuationSubring v hnonarch)[X],
      F.map (algebraMap
          (absoluteValueValuationSubring v hnonarch) K) = f ∧
        F.natDegree = f.natDegree ∧
          ∀ n : ℕ, v (F.coeff n : K) = v (f.coeff n) := by
  let V := absoluteValueValuationSubring v hnonarch
  have hlifts : f ∈ Polynomial.lifts (algebraMap V K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact
      ⟨⟨f.coeff n,
          (mem_absoluteValueValuationSubring_iff
            v hnonarch (f.coeff n)).2 (hfcoeff n)⟩,
        by simp [V]⟩
  rcases Polynomial.exists_degree_eq_of_mem_lifts hlifts with
    ⟨F, hmap, hdegree⟩
  refine ⟨F, hmap, Polynomial.natDegree_eq_of_degree_eq hdegree, ?_⟩
  intro n
  have hcoeff :
      (F.coeff n : K) = f.coeff n := by
    have h := congrArg (fun P : K[X] => P.coeff n) hmap
    simpa [Polynomial.coeff_map, V] using h
  rw [hcoeff]

end Valuations
end AlgebraicNumberTheory

end
