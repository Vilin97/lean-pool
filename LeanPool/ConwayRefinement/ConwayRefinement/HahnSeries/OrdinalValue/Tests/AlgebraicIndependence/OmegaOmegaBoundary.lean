/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.OmegaOmegaBoundary

/-!
# Concrete values at the `ω ^ ω` boundary

The unique exponent in block zero is `7 / 9`, while the first exponent in block one is `25 / 81`.
Thus successive tuple blocks are genuinely rescaled and separated rather than superimposed. The
normal form has coefficient zero at exponent zero, distinguishing the purely infinite boundary
element from the finite-power family, whose normal forms include a constant term.
-/

public noncomputable section

namespace Tests.HahnSeries.OrdinalValue.AlgebraicIndependence.OmegaOmegaBoundary

open Ordinal
open ConwayRefinement.Standalone.Oz.FinitePowerFamily
open ConwayRefinement.Standalone.Oz.OmegaOmegaBoundary

example : boundaryConwayExponent (toLex ⟨0, ()⟩) = 7 / 9 := by
  rw [boundaryConwayExponent_apply, boundarySignedExponent_mk,
    finitePowerExponent_zero, scale_eq_one_div_three]
  norm_num

example : boundaryConwayExponent (toLex ⟨1, toLex (0, ())⟩) = 25 / 81 := by
  rw [boundaryConwayExponent_apply, boundarySignedExponent_mk,
    finitePowerExponent_succ, finitePowerExponent_zero, scale_eq_one_div_three]
  norm_num

example :
    boundaryConwayExponent (toLex ⟨1, toLex (0, ())⟩) <
      boundaryConwayExponent (toLex ⟨0, ()⟩) := by
  norm_num [boundaryConwayExponent_apply, boundarySignedExponent_mk,
    finitePowerExponent_succ, finitePowerExponent_zero, scale_eq_one_div_three]

example :
    boundaryOz.1.coeff (boundaryExponentAtIndex (toLex ⟨0, ()⟩)) = 1 :=
  boundaryOz_coeff_exponent _

example : boundaryOz.1.coeff 0 = 0 :=
  boundaryOz_coeff_zero

example : boundaryOz.1.length = ω ^ ω :=
  boundaryOz_length

example : ¬ ConwayRefinement.Standalone.Oz.IsOrdinaryInteger boundaryOz :=
  boundaryOz_not_isOrdinaryInteger

example : ConwayRefinement.Standalone.Oz.IsReduced boundaryOz :=
  boundaryOz_isReduced

example : ¬ ConwayRefinement.Standalone.Oz.HasFiniteDegree boundaryOz :=
  boundaryOz_not_hasFiniteDegree

end Tests.HahnSeries.OrdinalValue.AlgebraicIndependence.OmegaOmegaBoundary
