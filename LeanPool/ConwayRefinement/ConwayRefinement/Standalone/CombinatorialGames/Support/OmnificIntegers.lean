/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.HahnSeries.Basic
public import Mathlib.Algebra.Ring.Subring.Defs

import all LeanPool.ConwayRefinement.CombinatorialGames.Surreal.HahnSeries.Basic

/-!
# Omnific integers in Conway normal-form coordinates

CombinatorialGames supplies `SurrealHahnSeries`, the target of Conway normal form. In these
coordinates, the omnific integers are exactly the series whose exponents are nonnegative and whose
constant coefficient is an integer [LM24, §1.1].

This module constructs that subring using only Mathlib and CombinatorialGames. It does not assume a
normal-form map from surreals; the statement module next to it formulates the identification with
Conway's cut definition of `Oz`.

## References

* S. L'Innocente, V. Mantova, *A factorisation theory for generalised power series and omnific
  integers*, Adv. Math. 442 (2024) 109513, <https://doi.org/10.1016/j.aim.2024.109513>, cited
  as [LM24].
-/

universe u

public noncomputable section

namespace ConwayRefinement.Standalone.Oz

open Order Set

private theorem ofLex_coe_mul (x y : SurrealHahnSeries) :
    ofLex (x * y).1 = ofLex x.1 * ofLex y.1 := by
  with_unfolding_all rfl

private theorem ofLex_coe_single (p : Surreal) (r : ℝ) :
    ofLex (SurrealHahnSeries.single p r).1 =
      HahnSeries.single (OrderDual.toDual p) r := by
  apply HahnSeries.ext
  funext k
  rw [HahnSeries.coeff_single]
  unfold SurrealHahnSeries.single SurrealHahnSeries.mk
  by_cases hk : k = OrderDual.toDual p
  · subst k
    simp
  · have hk' : k.ofDual ≠ p := fun h ↦ hk (by simpa using congrArg OrderDual.toDual h)
    simp [hk, hk']

private theorem mem_support_ofLex_coe_iff (x : SurrealHahnSeries) (k : Surreal) :
    OrderDual.toDual k ∈ (ofLex x.1).support ↔ k ∈ x.support := by
  rfl

private theorem exists_add_eq_of_mem_support_mul
    {x y : SurrealHahnSeries.{u}} {k : Surreal}
    (hk : k ∈ (x * y).support) :
    ∃ p ∈ x.support, ∃ q ∈ y.support, p + q = k := by
  have hk' : OrderDual.toDual k ∈ (ofLex (x * y).1).support :=
    (mem_support_ofLex_coe_iff (x * y) k).2 hk
  rw [ofLex_coe_mul] at hk'
  obtain ⟨p, hp, q, hq, hpq⟩ := HahnSeries.support_mul_subset hk'
  refine ⟨p.ofDual, (mem_support_ofLex_coe_iff x p.ofDual).1 ?_,
    q.ofDual, (mem_support_ofLex_coe_iff y q.ofDual).1 ?_, ?_⟩
  · simpa using hp
  · simpa using hq
  · simpa using congrArg OrderDual.ofDual hpq

private theorem support_mul_subset_Ici {x y : SurrealHahnSeries}
    (hx : x.support ⊆ Ici 0) (hy : y.support ⊆ Ici 0) :
    (x * y).support ⊆ Ici 0 := by
  intro k hk
  obtain ⟨p, hp, q, hq, rfl⟩ := exists_add_eq_of_mem_support_mul hk
  rw [mem_Ici]
  exact add_nonneg (show 0 ≤ p by simpa only [mem_Ici] using hx hp)
    (show 0 ≤ q by simpa only [mem_Ici] using hy hq)

private theorem single_mul_single (p q : Surreal.{u}) (r s : ℝ) :
    SurrealHahnSeries.single p r * SurrealHahnSeries.single q s =
      SurrealHahnSeries.single (p + q) (r * s) := by
  apply Subtype.ext
  rw [← ofLex_inj, ofLex_coe_mul, ofLex_coe_single, ofLex_coe_single,
    HahnSeries.single_mul_single, ofLex_coe_single]
  congr 2

private theorem coeff_mul_zero_of_support_subsets {x y : SurrealHahnSeries}
    (hx : x.support ⊆ Ioi 0) (hy : y.support ⊆ Ici 0) :
    (x * y).coeff 0 = 0 := by
  rw [← not_ne_iff]
  intro hcoeff
  have hzero : 0 ∈ (x * y).support :=
    SurrealHahnSeries.mem_support_iff.mpr hcoeff
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_add_eq_of_mem_support_mul hzero
  have hpPos : 0 < p := hx hp
  have hqNonneg : 0 ≤ q := hy hq
  have : 0 < p + q := add_pos_of_pos_of_nonneg hpPos hqNonneg
  rw [hpq] at this
  exact this.false

private theorem coeff_zero_mul_of_support_subset_Ici {x y : SurrealHahnSeries}
    (hx : x.support ⊆ Ici 0) (hy : y.support ⊆ Ici 0) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  have hxSplit : x.trunc 0 + SurrealHahnSeries.single 0 (x.coeff 0) = x :=
    SurrealHahnSeries.trunc_add_single fun i hi ↦ hx hi
  have hySplit : y.trunc 0 + SurrealHahnSeries.single 0 (y.coeff 0) = y :=
    SurrealHahnSeries.trunc_add_single fun i hi ↦ hy hi
  conv_lhs => rw [← hxSplit, ← hySplit]
  rw [add_mul, mul_add, mul_add,
    SurrealHahnSeries.coeff_add_apply, SurrealHahnSeries.coeff_add_apply,
    SurrealHahnSeries.coeff_add_apply]
  have hxTrunc : (x.trunc 0).support ⊆ Ioi 0 := by
    intro i hi
    rw [SurrealHahnSeries.support_trunc] at hi
    exact hi.2
  have hyTrunc : (y.trunc 0).support ⊆ Ioi 0 := by
    intro i hi
    rw [SurrealHahnSeries.support_trunc] at hi
    exact hi.2
  have hxTruncNonneg : (x.trunc 0).support ⊆ Ici 0 := by
    intro i hi
    rw [mem_Ici]
    exact (show 0 < i by simpa only [mem_Ioi] using hxTrunc hi).le
  have hyTruncNonneg : (y.trunc 0).support ⊆ Ici 0 := by
    intro i hi
    rw [mem_Ici]
    exact (show 0 < i by simpa only [mem_Ioi] using hyTrunc hi).le
  have hsingleNonneg (r : ℝ) :
      (SurrealHahnSeries.single 0 r).support ⊆ Ici 0 := by
    intro i hi
    have hi' := SurrealHahnSeries.support_single_subset hi
    rw [mem_Ici]
    have : i = 0 := by simpa only [mem_singleton_iff] using hi'
    simp [this]
  rw [coeff_mul_zero_of_support_subsets hxTrunc hyTruncNonneg,
    coeff_mul_zero_of_support_subsets hxTrunc (hsingleNonneg _)]
  have hsingleTrunc :
      (SurrealHahnSeries.single 0 (x.coeff 0) * y.trunc 0).coeff 0 = 0 := by
    rw [mul_comm]
    exact coeff_mul_zero_of_support_subsets hyTrunc (hsingleNonneg _)
  rw [hsingleTrunc, single_mul_single]
  simp [SurrealHahnSeries.coeff_single_self]

/-- The Conway normal form of an integer is concentrated at exponent zero. -/
theorem intCast_eq_single_zero (z : ℤ) :
    (z : SurrealHahnSeries) = SurrealHahnSeries.single 0 (z : ℝ) := by
  apply Subtype.ext
  rw [← ofLex_inj, ofLex_coe_single]
  with_unfolding_all rfl

/-- The Conway normal form of one has coefficient one at exponent zero. -/
theorem one_eq_single_zero :
    (1 : SurrealHahnSeries) = SurrealHahnSeries.single 0 1 := by
  apply Subtype.ext
  rw [← ofLex_inj, ofLex_coe_single]
  with_unfolding_all rfl

/-- The omnific integers in Conway normal-form coordinates: surreal Hahn series with nonnegative
exponents and an integer constant coefficient [LM24, §1.1]. -/
def omnificIntegers : Subring SurrealHahnSeries.{u} where
  carrier := {x | x.support ⊆ Ici 0 ∧ x.coeff 0 ∈ range ((↑) : ℤ → ℝ)}
  zero_mem' := by
    refine ⟨by simp [SurrealHahnSeries.support_zero], ⟨0, by simp⟩⟩
  one_mem' := by
    rw [one_eq_single_zero]
    refine ⟨?_, ⟨1, by simp⟩⟩
    intro i hi
    have hi' := SurrealHahnSeries.support_single_subset hi
    rw [mem_Ici]
    have : i = 0 := by simpa only [mem_singleton_iff] using hi'
    simp [this]
  add_mem' := by
    rintro x y ⟨hxSupport, ⟨m, hm⟩⟩ ⟨hySupport, ⟨n, hn⟩⟩
    refine ⟨?_, ⟨m + n, ?_⟩⟩
    · exact SurrealHahnSeries.support_add_subset.trans
        (union_subset hxSupport hySupport)
    · rw [SurrealHahnSeries.coeff_add_apply, ← hm, ← hn]
      simp
  neg_mem' := by
    rintro x ⟨hxSupport, ⟨m, hm⟩⟩
    refine ⟨?_, ⟨-m, ?_⟩⟩
    · intro i hi
      apply hxSupport
      rw [SurrealHahnSeries.mem_support_iff] at hi ⊢
      simpa only [SurrealHahnSeries.coeff_neg, Pi.neg_apply, neg_ne_zero] using hi
    · rw [show (-x).coeff 0 = -x.coeff 0 by
        exact congrFun (SurrealHahnSeries.coeff_neg x) 0, ← hm]
      simp
  mul_mem' := by
    rintro x y ⟨hxSupport, ⟨m, hm⟩⟩ ⟨hySupport, ⟨n, hn⟩⟩
    refine ⟨support_mul_subset_Ici hxSupport hySupport, ⟨m * n, ?_⟩⟩
    rw [coeff_zero_mul_of_support_subset_Ici hxSupport hySupport, ← hm, ← hn]
    simp

/-- Membership in the normal-form presentation of the omnific integers. -/
theorem mem_omnificIntegers {x : SurrealHahnSeries.{u}} :
    x ∈ omnificIntegers ↔
      x.support ⊆ Ici 0 ∧ x.coeff 0 ∈ range ((↑) : ℤ → ℝ) := by
  rfl

/-- The omnific integers in Conway normal-form coordinates. -/
abbrev OmnificInteger := ↥(omnificIntegers : Subring SurrealHahnSeries.{u})

/-- The integer coefficient of `ω ^ 0` in an omnific integer's Conway normal form. -/
def integerConstantCoeff (x : OmnificInteger.{u}) : ℤ :=
  Classical.choose x.2.2

/-- The chosen integer really is the coefficient of `ω ^ 0`. -/
@[simp]
theorem coe_integerConstantCoeff (x : OmnificInteger.{u}) :
    (integerConstantCoeff x : ℝ) = x.1.coeff 0 := by
  exact Classical.choose_spec x.2.2

/-- Taking the integer constant coefficient is a ring homomorphism `Oz →+* ℤ`. -/
def integerConstantCoeffRingHom : OmnificInteger.{u} →+* ℤ where
  toFun := integerConstantCoeff
  map_zero' := by
    apply Int.cast_injective (α := ℝ)
    rw [coe_integerConstantCoeff]
    simp
  map_one' := by
    apply Int.cast_injective (α := ℝ)
    rw [coe_integerConstantCoeff]
    rw [show (1 : OmnificInteger).1 = (1 : SurrealHahnSeries) by rfl,
      one_eq_single_zero]
    simp
  map_add' x y := by
    apply Int.cast_injective (α := ℝ)
    rw [coe_integerConstantCoeff, Int.cast_add, coe_integerConstantCoeff,
      coe_integerConstantCoeff]
    exact SurrealHahnSeries.coeff_add_apply x.1 y.1 0
  map_mul' x y := by
    apply Int.cast_injective (α := ℝ)
    rw [coe_integerConstantCoeff, Int.cast_mul, coe_integerConstantCoeff,
      coe_integerConstantCoeff]
    exact coeff_zero_mul_of_support_subset_Ici x.2.1 y.2.1

@[simp]
theorem integerConstantCoeffRingHom_apply (x : OmnificInteger.{u}) :
    integerConstantCoeffRingHom x = integerConstantCoeff x := (rfl)

/-- A monomial with nonnegative exponent and coefficient one is an omnific integer. -/
theorem single_one_mem_omnificIntegers (p : Surreal.{u}) (hp : 0 ≤ p) :
    SurrealHahnSeries.single p 1 ∈ omnificIntegers := by
  rw [mem_omnificIntegers]
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · have hip := SurrealHahnSeries.support_single_subset hi
    have hiEq : i = p := by simpa only [Set.mem_singleton_iff] using hip
    simpa only [Set.mem_Ici, hiEq] using hp
  · by_cases hp0 : p = 0
    · subst p
      exact ⟨1, by simp [SurrealHahnSeries.coeff_single_self]⟩
    · exact ⟨0, by simp [SurrealHahnSeries.coeff_single_of_ne hp0]⟩

/-- Powers of coefficient-one monomials multiply their exponent by the power. -/
theorem single_one_pow (p : Surreal.{u}) (n : ℕ) :
    (SurrealHahnSeries.single p 1) ^ n = SurrealHahnSeries.single (n • p) 1 := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, one_eq_single_zero]
  | succ n ih => rw [pow_succ, ih, single_mul_single, succ_nsmul, one_mul]

end ConwayRefinement.Standalone.Oz
