/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Primality.ZFC
public import LeanPool.ConwayRefinement.ConwayRefinement.Examples.OmnificInteger.DegreeTwoPrime

/-!
# A degree-two prime in the class presentation of the omnific integers

The explicit degree-two prime transfers through the equivalence between the library and
set-coded presentations of the omnific integers.
-/

universe u

public noncomputable section

namespace ZFSet.Surreal.OmnificInteger.DegreeTwoExample

/-- The explicit degree-two prime, as a Conway-equivalence class of omnific ZFC codes. -/
def degreeTwoOz : OmnificInteger.{u} :=
  ringEquiv.symm _root_.Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz

@[simp]
theorem toOmnificInteger_degreeTwoOz : toOmnificInteger degreeTwoOz.{u} =
    _root_.Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz := by
  rw [← ringEquiv_apply]
  exact ringEquiv.apply_symm_apply _

/-- The class-valued example has exactly the displayed Conway normal form. -/
theorem degreeTwoOz_toHahnSeries :
    ZFSet.Surreal.toHahnSeries (degreeTwoOz.{u} : ZFSet.Surreal.{u}) =
      _root_.Surreal.OmnificInteger.DegreeTwoExample.normalForm := by
  rw [ZFSet.Surreal.toHahnSeries_eq_toSurreal, ← coe_toOmnificInteger,
    toOmnificInteger_degreeTwoOz]
  exact _root_.Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz_toHahnSeries

/-- The prescribed normal form identifies the class-valued example uniquely. -/
theorem toHahnSeries_eq_normalForm_iff (x : OmnificInteger.{u}) :
    ZFSet.Surreal.toHahnSeries (x : ZFSet.Surreal.{u}) =
      _root_.Surreal.OmnificInteger.DegreeTwoExample.normalForm ↔ x = degreeTwoOz := by
  rw [← degreeTwoOz_toHahnSeries]
  constructor
  · intro h
    apply Subtype.ext
    apply ZFSet.Surreal.toSurreal_injective
    simpa only [ZFSet.Surreal.toHahnSeries_eq_toSurreal,
      _root_.Surreal.toSurreal_toHahnSeries] using congrArg SurrealHahnSeries.toSurreal h
  · rintro rfl
    rfl

/-- The normal form of the class-valued example has support order type `ω ^ 2 + 1`. -/
theorem degreeTwoOz_length :
    (ZFSet.Surreal.toHahnSeries (degreeTwoOz.{u} : ZFSet.Surreal.{u})).length =
      Ordinal.omega0 ^ (2 : Ordinal) + 1 := by
  rw [ZFSet.Surreal.toHahnSeries_eq_toSurreal, ← coe_toOmnificInteger,
    toOmnificInteger_degreeTwoOz, _root_.Surreal.length_toHahnSeries]
  exact _root_.Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz_length

/-- The explicit class-valued example is reduced in the native Conway-support sense. -/
theorem degreeTwoOz_isReduced :
    ZFSet.Surreal.IsReduced (degreeTwoOz.{u} : ZFSet.Surreal.{u}) := by
  apply (isReduced_iff_toSignedNonpositiveHahn degreeTwoOz).2
  rw [ringEquiv_apply, toOmnificInteger_degreeTwoOz]
  exact _root_.Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz_isReduced

/-- The explicit degree-two omnific class value is prime. -/
theorem degreeTwoOz_prime : Prime degreeTwoOz.{u} := by
  apply (MulEquiv.prime_iff ringEquiv).1
  rw [ringEquiv_apply, toOmnificInteger_degreeTwoOz]
  exact _root_.Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz_prime

end ZFSet.Surreal.OmnificInteger.DegreeTwoExample
