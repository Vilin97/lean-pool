/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Maximal divisors along a multiplicative map

For a multiplicative map `f : D →* R`, an associate class `a : Associates D` is the maximal
divisor of `x : R` coming from `D` when `f q ∣ x` holds exactly for the elements `q : D` whose
associate classes divide `a`.

The definition is invariant under multiplication by units in `D`. It supplies the common
divisibility interface later used for both the associated graded ring and the Hahn-series ring in
LM24.
-/

universe u v

public section

/-- `a` records exactly the divisors of `x` that arise through `f`. -/
def IsMaximalDivisorAlong
    {D : Type u} {R : Type v}
    [CommMonoidWithZero D]
    [CommMonoidWithZero R]
    (f : D →* R) (x : R) (a : Associates D) : Prop :=
  ∀ q : D, Associates.mk q ≤ a ↔ f q ∣ x

/-- The defining divisibility characterization of a maximal divisor along a map. -/
theorem isMaximalDivisorAlong_iff
    {D : Type u} {R : Type v}
    [CommMonoidWithZero D] [IsCancelMulZero D]
    [CommMonoidWithZero R]
    (f : D →* R) (x : R) (a : Associates D) :
    IsMaximalDivisorAlong f x a ↔
      ∀ q : D, Associates.mk q ≤ a ↔ f q ∣ x :=
  Iff.rfl

namespace IsMaximalDivisorAlong

variable {D : Type u} {R : Type v}
variable [CommMonoidWithZero D] [IsCancelMulZero D]
variable [CommMonoidWithZero R]
variable {f : D →* R} {x y : R} {a b c : Associates D}

/-- Zero has zero as its maximal divisor class along every multiplicative map. -/
theorem zero (f : D →* R) : IsMaximalDivisorAlong f 0 0 := by
  rw [isMaximalDivisorAlong_iff]
  intro q
  constructor
  · intro _
    exact dvd_zero _
  · intro _
    change Associates.mk q ≤ Associates.mk 0
    exact Associates.mk_le_mk_of_dvd (dvd_zero q)

/-- The maximal-divisor property determines at most one associate class. -/
theorem eq (ha : IsMaximalDivisorAlong f x a)
    (hb : IsMaximalDivisorAlong f x b) : a = b := by
  induction a using Quotient.inductionOn with
  | _ p =>
      induction b using Quotient.inductionOn with
      | _ q =>
          apply le_antisymm
          · exact (hb p).2 ((ha p).1 le_rfl)
          · exact (ha q).2 ((hb q).1 le_rfl)

omit [IsCancelMulZero D] in
/-- Every representative of the maximal associate class divides the target after applying `f`.
-/
theorem map_dvd_of_mk_eq (ha : IsMaximalDivisorAlong f x a)
    {p : D} (hp : Associates.mk p = a) : f p ∣ x := by
  exact (ha p).1 hp.le

omit [IsCancelMulZero D] in
/-- Maximal divisor classes are supermultiplicative: the product of maximal divisors of two
elements divides every maximal divisor of their product. -/
theorem mul_le (ha : IsMaximalDivisorAlong f x a)
    (hb : IsMaximalDivisorAlong f y b)
    (hc : IsMaximalDivisorAlong f (x * y) c) : a * b ≤ c := by
  induction a using Quotient.inductionOn with
  | _ p =>
      induction b using Quotient.inductionOn with
      | _ q =>
          apply (hc (p * q)).2
          obtain ⟨x', hx⟩ := (ha p).1 le_rfl
          obtain ⟨y', hy⟩ := (hb q).1 le_rfl
          refine ⟨x' * y', ?_⟩
          rw [map_mul, hx, hy]
          ac_rfl

end IsMaximalDivisorAlong
