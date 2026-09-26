/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Examples.DegreeTwoPrimeProof

/-!
# API checks for the explicit degree-two prime

This separately compiled client consumes only the public standalone statement/proof boundary. It
checks the literal prime, the coefficient-doubled reducible foil, their exact common support order
type, and the support equality that makes the comparison mathematically sharp, in the surreal
numbers of an arbitrary universe.
-/

universe u

public noncomputable section

namespace Tests.DegreeTwoOz

open ConwayRefinement.Standalone.Oz.DegreeTwoExample

/-- The literal coefficient-one normal form is certified prime. -/
example : Prime degreeTwoOz.{u} :=
  IsPrime.proof

/-- Its Conway support has exact order type `ω² + 1`. -/
example : HasExactSupportOrderType.{u} :=
  HasExactSupportOrderType.proof

/-- The coefficient-doubled comparison has the same exact order type. -/
example : FoilHasExactSupportOrderType.{u} :=
  FoilHasExactSupportOrderType.proof

/-- The comparison element has an explicit factorisation into two nonunits. -/
example : FoilHasNontrivialFactorization.{u} :=
  FoilHasNontrivialFactorization.proof

/-- The prime and reducible foil have literally equal Conway supports. -/
example : degreeTwoFoil.{u}.1.support = degreeTwoOz.1.support :=
  degreeTwoFoil_support

/-- The two normal forms differ; their constant coefficients are two and one. -/
theorem degreeTwoFoil_ne_degreeTwoOz : degreeTwoFoil.{u} ≠ degreeTwoOz := by
  intro h
  have hcoeff := congrArg
    (fun q : ConwayRefinement.Standalone.Oz.OmnificInteger.{u} ↦ q.1.coeff 0) h
  rw [degreeTwoFoil_val, degreeTwoOz_val, two_mul] at hcoeff
  rw [SurrealHahnSeries.coeff_add_apply, normalForm_coeff_zero] at hcoeff
  norm_num at hcoeff

end Tests.DegreeTwoOz
