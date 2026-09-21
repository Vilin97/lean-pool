/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.NormalForm

/-!
# Checks for Conway normal forms of omnific integers

The positive example `ω + 3` has both a genuinely positive exponent and a nonzero integral
constant coefficient, so it excludes the degenerate pure-constant and zero cases. The negative
monomial `ω⁻¹` separates the intended nonnegative-support criterion from the nearby wrong
definition that permits arbitrary exponents with an integral constant coefficient.
-/

universe u

noncomputable section

public section

namespace Tests

open Set Surreal

/-- The monomial `ω` satisfies the normal-form criterion for omnific integers. -/
theorem omega_isOmnificInteger :
    IsOmnificInteger (ω^ (1 : Surreal.{u})) := by
  rw [isOmnificInteger_iff_normalForm]
  constructor
  · simp
  · simp

/-- The nonconstant surreal `ω + 3` is an omnific integer. -/
theorem omega_add_three_isOmnificInteger :
    IsOmnificInteger (ω^ (1 : Surreal.{u}) + 3) :=
  omega_isOmnificInteger.add (IsOmnificInteger.natCast 3)

/-- The nonconstant check has the expected integral coefficient at exponent zero. -/
theorem omega_add_three_coeff_zero :
    (ω^ (1 : Surreal.{u}) + 3).coeff 0 = 3 := by
  have homega :
      (ω^ (1 : Surreal.{u})).toHahnSeries.coeff 0 = 0 := by
    rw [toHahnSeries_wpow,
      SurrealHahnSeries.coeff_single_of_ne (by norm_num)]
  have hthree : (3 : Surreal.{u}).toHahnSeries.coeff 0 = 3 := by
    calc
      (3 : Surreal.{u}).toHahnSeries.coeff 0 =
          (SurrealHahnSeries.single 0 3).coeff 0 :=
        congrArg (fun q : SurrealHahnSeries ↦ q.coeff 0)
          (toHahnSeries_natCast 3)
      _ = 3 := SurrealHahnSeries.coeff_single_self 0 3
  calc
    (ω^ (1 : Surreal.{u}) + 3).coeff 0 =
        (ω^ (1 : Surreal.{u}) + 3).toHahnSeries.coeff 0 :=
      congrFun (coeff_toHahnSeries _).symm 0
    _ = ((ω^ (1 : Surreal.{u})).toHahnSeries +
        (3 : Surreal.{u}).toHahnSeries).coeff 0 := by
      rw [toHahnSeries_add]
    _ = (ω^ (1 : Surreal.{u})).toHahnSeries.coeff 0 +
        (3 : Surreal.{u}).toHahnSeries.coeff 0 :=
      SurrealHahnSeries.coeff_add_apply _ _ _
    _ = 3 := by rw [homega, hthree, zero_add]

/-- A negative monomial is not an omnific integer. -/
theorem wpow_neg_one_not_isOmnificInteger :
    ¬IsOmnificInteger (ω^ (-1 : Surreal.{u})) := by
  rw [isOmnificInteger_iff_normalForm]
  rintro ⟨hsupport, _⟩
  have hnonnegative : (0 : Surreal.{u}) ≤ -1 := hsupport (by
    rw [support_wpow]
    exact mem_singleton _)
  norm_num at hnonnegative

/-- The unit gap makes two sufficiently close omnific integers equal. -/
example {x y : Surreal.{u}} (hx : IsOmnificInteger x) (hy : IsOmnificInteger y)
    (hbound : x - y ∈ Ioo (-1) 1) : x = y :=
  hx.eq_of_sub_mem_Ioo_neg_one_one hy hbound

end Tests
