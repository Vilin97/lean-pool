/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.WPTBridge.Preparation
import LeanPool.LocalComplexGeometry.WPTBridge.GermDivision

/-!
# The prepared divisor is associate to the regularized germ
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry.WPTBridge

open ClassicalComplexWPT

noncomputable section

/-- Transport an analytic WPT unit from product coordinates to standard coordinates. -/
def standardPreparationUnitGerm {n : ℕ} (u : Ambient n → ℂ)
    (hu : AnalyticAt ℂ u 0) : HolomorphicGerm (n + 1) :=
  HolomorphicGerm.ofFunction (fun x ↦ u (wptAmbientEquiv n x))
    (by
      have hu' : AnalyticAt ℂ u (wptAmbientEquiv n 0) := by rw [map_zero]; exact hu
      simpa [Function.comp_def] using hu'.compContinuousLinearMap
        (u := (wptAmbientEquiv n : ComplexEuclidean (n + 1) →L[ℂ] Ambient n))
        (x := 0))

theorem standardPreparationUnitGerm_isUnit {n : ℕ} (u : Ambient n → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) :
    IsUnit (standardPreparationUnitGerm u hu) := by
  apply (holomorphicGerm_isUnit_iff _).2
  change u (wptAmbientEquiv n 0) ≠ 0
  simpa only [map_zero] using hu0

/--
The raw representative identity supplied by regularized preparation descends to
an equality saying that the coordinate pullback is a unit times the prepared
polynomial germ.
-/
theorem coordinatePullback_eq_unit_mul_preparedPolynomialGerm
    {n d : ℕ} {f : HolomorphicGerm (n + 1)}
    (L : ComplexEuclidean (n + 1) ≃L[ℂ] ComplexEuclidean (n + 1))
    (H : Ambient n → ℂ) (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ)
    (hcoord :
      ((fun x : ComplexEuclidean (n + 1) ↦ H (wptAmbientEquiv n x)) :
          FunctionGerm (n + 1)) =
        (coordinatePullback L f : FunctionGerm (n + 1)))
    (hprep : IsWeierstrassPreparation H d a u) :
    coordinatePullback L f =
      standardPreparationUnitGerm u hprep.2.2.1 *
        preparedPolynomialGerm a hprep.1 := by
  apply Subtype.ext
  rw [← hcoord]
  change ((fun x : ComplexEuclidean (n + 1) ↦ H (wptAmbientEquiv n x)) :
      FunctionGerm (n + 1)) =
    ((fun x ↦ u (wptAmbientEquiv n x)) : FunctionGerm (n + 1)) *
      (preparedPolynomialFunction a : FunctionGerm (n + 1))
  rw [← Filter.Germ.coe_mul]
  apply Filter.Germ.coe_eq.mpr
  have htendsto : Tendsto (wptAmbientEquiv n) (𝓝 0) (𝓝 0) := by
    have h : Tendsto (wptAmbientEquiv n) (𝓝 0)
        (𝓝 (wptAmbientEquiv n 0)) :=
      (wptAmbientEquiv n).continuous.continuousAt
    rwa [map_zero] at h
  have hfactor := hprep.2.2.2.2.comp_tendsto htendsto
  filter_upwards [hfactor] with x hx
  exact hx

/-- The prepared divisor is an associate of the coordinate pullback. -/
theorem coordinatePullback_associated_preparedPolynomialGerm
    {n d : ℕ} {f : HolomorphicGerm (n + 1)}
    (L : ComplexEuclidean (n + 1) ≃L[ℂ] ComplexEuclidean (n + 1))
    (H : Ambient n → ℂ) (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ)
    (hcoord :
      ((fun x : ComplexEuclidean (n + 1) ↦ H (wptAmbientEquiv n x)) :
          FunctionGerm (n + 1)) =
        (coordinatePullback L f : FunctionGerm (n + 1)))
    (hprep : IsWeierstrassPreparation H d a u) :
    Associated (coordinatePullback L f) (preparedPolynomialGerm a hprep.1) := by
  rw [coordinatePullback_eq_unit_mul_preparedPolynomialGerm L H a u hcoord hprep]
  exact associated_unit_mul_left _ _
    (standardPreparationUnitGerm_isUnit u hprep.2.2.1 hprep.2.2.2.1)

end

end LocalComplexGeometry.WPTBridge
