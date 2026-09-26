/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.FinitePowerFamilyProof

/-!
# Boundary examples for the finite-power family

At `n = 0`, the positive support consists of one exponent, and adjoining the constant term gives
a support of order type two. At `n = 1`, the first two positive exponents are `4 / 3` and
`4 / 9`. At `n = 2`, the first exponent is `13 / 9` and the support has order type `ω ^ 2 + 1`.
These values distinguish
the recursive lexicographic construction from a constant sequence or a one-dimensional
flattening.

The constant coefficient is one before subtracting one and zero afterwards. The doubled family
has the same exponent support, showing directly that the support is insensitive to this change of
coefficients.
-/

public noncomputable section

namespace Tests.HahnSeries.OrdinalValue.AlgebraicIndependence.FinitePowerFamily

open Ordinal
open ConwayRefinement.Standalone.Oz.FinitePowerFamily

example : finitePowerConwayExponent 0 () = 1 := by
  rw [finitePowerConwayExponent_apply, finitePowerExponent_zero]
  norm_num

example : finitePowerConwayExponent 1 (toLex (0, ())) = 4 / 3 := by
  rw [finitePowerConwayExponent_apply, finitePowerExponent_succ,
    finitePowerExponent_zero, scale_eq_one_div_three]
  norm_num

example : finitePowerConwayExponent 1 (toLex (1, ())) = 4 / 9 := by
  rw [finitePowerConwayExponent_apply, finitePowerExponent_succ,
    finitePowerExponent_zero, scale_eq_one_div_three]
  norm_num

example :
    finitePowerConwayExponent 2 (toLex (0, toLex (0, ()))) = 13 / 9 := by
  rw [finitePowerConwayExponent_apply, finitePowerExponent_succ,
    finitePowerExponent_succ, finitePowerExponent_zero,
    scale_eq_one_div_three]
  norm_num

example : (finitePowerOz 0).1.length = 2 := by
  rw [finitePowerOz_length]
  norm_num

example : (finitePowerOz 1).1.length = ω + 1 := by
  simpa using finitePowerOz_length 1

example : (finitePowerOz 2).1.length = ω ^ (2 : Ordinal) + 1 :=
  finitePowerOz_length 2

example : finitePowerOz 1 ≠ finitePowerOz 2 := by
  intro h
  have := finitePowerOz_injective h
  omega

example (n : ℕ) : 0 ∉ ((finitePowerOz n).1 - 1).support :=
  zero_not_mem_finitePowerOz_sub_one_support n

example (n : ℕ) :
    (finitePowerFoil n).1.support = (finitePowerOz n).1.support :=
  finitePowerFoil_support n

example (n : ℕ) : ¬ ConwayRefinement.Standalone.Oz.IsReduced (finitePowerFoil n) :=
  finitePowerFoil_not_isReduced n

example (n : ℕ) : IsPrimal (finitePowerOz n) :=
  PrimalFamily.proof n

end Tests.HahnSeries.OrdinalValue.AlgebraicIndependence.FinitePowerFamily
