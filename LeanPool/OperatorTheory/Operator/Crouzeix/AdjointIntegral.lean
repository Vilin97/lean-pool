/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Adjoint of operator-valued integrals

The symmetrized Crouzeix--Palencia contour operator contains the adjoint of
an operator-valued integral.  Since adjoint is conjugate-linear, moving it
through integration is not an instance of the usual complex-linear integral
API.  This file supplies that bridge using Mathlib's semilinear integration
theorem and records the resulting contour formula.

## Main declarations

* `ContinuousLinearMap.adjoint_integral` -- adjoint commutes with an
  integrable Bochner integral.
* `ContinuousLinearMap.adjoint_intervalIntegral` -- the corresponding
  interval-integral statement.
* `ContinuousLinearMap.adjoint_contourIntegral` -- the adjoint of a contour
  integral has conjugated tangent weight and pointwise-adjoint integrand.
* `ContinuousLinearMap.intervalIntegral_smul_add_adjoint` -- complex-weighted
  symmetrization of an operator kernel and its adjoint.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ContourIntegral
import Mathlib.Analysis.InnerProductSpace.Adjoint

open MeasureTheory
open scoped InnerProductSpace Interval

universe u v w

namespace ContinuousLinearMap

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}
variable {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Adjoint commutes with an integrable operator-valued Bochner integral.
The proof uses adjoint as a continuous conjugate-linear map and the fact that
complex conjugation fixes real scalars. -/
theorem adjoint_integral (f : X → E →L[ℂ] F) (hf : Integrable f μ) :
    ContinuousLinearMap.adjoint (∫ x, f x ∂μ) =
      ∫ x, ContinuousLinearMap.adjoint (f x) ∂μ := by
  symm
  exact ContinuousLinearMap.integral_comp_commSL
    RCLike.conj_smul
    ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap hf

/-- Adjoint commutes with an operator-valued interval integral whenever the
integrand is interval integrable. -/
theorem adjoint_intervalIntegral (f : ℝ → E →L[ℂ] F) {a b : ℝ}
    {ν : Measure ℝ} (hf : IntervalIntegrable f ν a b) :
    ContinuousLinearMap.adjoint (∫ x in a..b, f x ∂ν) =
      ∫ x in a..b, ContinuousLinearMap.adjoint (f x) ∂ν := by
  unfold intervalIntegral
  rw [map_sub, adjoint_integral _ hf.1, adjoint_integral _ hf.2]

/-- Moving adjoint through a contour integral conjugates the tangent scalar
and takes the pointwise adjoint of the operator-valued integrand. -/
theorem adjoint_contourIntegral (f : ℂ → E →L[ℂ] F) (γ : ℝ → ℂ)
    (hf : ContourIntegrable f γ) :
    ContinuousLinearMap.adjoint (contourIntegral f γ) =
      ∫ t in (0 : ℝ)..(2 * Real.pi),
        star (deriv γ t) • ContinuousLinearMap.adjoint (f (γ t)) := by
  unfold contourIntegral
  rw [adjoint_intervalIntegral _ hf]
  congr 1
  funext t
  exact map_smulₛₗ ContinuousLinearMap.adjoint (deriv γ t) (f (γ t))

/-- Complex-weighted symmetrization of an operator-valued interval integral.
The conjugate weight before taking adjoint becomes the original weight, so
the two terms combine into the symmetric kernel `K t + (K t)†`. -/
theorem intervalIntegral_smul_add_adjoint (K : ℝ → E →L[ℂ] E) (f : ℝ → ℂ)
    {a b : ℝ} {ν : Measure ℝ}
    (hfK : IntervalIntegrable (fun t => f t • K t) ν a b)
    (hstarfK : IntervalIntegrable (fun t => star (f t) • K t) ν a b) :
    (∫ t in a..b, f t • K t ∂ν) +
        ContinuousLinearMap.adjoint (∫ t in a..b, star (f t) • K t ∂ν) =
      ∫ t in a..b,
        f t • (K t + ContinuousLinearMap.adjoint (K t)) ∂ν := by
  let adjointCLM : (E →L[ℂ] E) →L⋆[ℂ] (E →L[ℂ] E) :=
    ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap
  have hfAdjointK : IntervalIntegrable
      (fun t => f t • ContinuousLinearMap.adjoint (K t)) ν a b := by
    have hcomp : IntervalIntegrable
        (fun t => adjointCLM (star (f t) • K t)) ν a b :=
      ⟨adjointCLM.integrable_comp hstarfK.1,
        adjointCLM.integrable_comp hstarfK.2⟩
    have hfun : (fun t => adjointCLM (star (f t) • K t)) =
        fun t => f t • ContinuousLinearMap.adjoint (K t) := by
      funext t
      change ContinuousLinearMap.adjoint (star (f t) • K t) =
        f t • ContinuousLinearMap.adjoint (K t)
      exact (map_smulₛₗ ContinuousLinearMap.adjoint (star (f t)) (K t)).trans (by
        rw [starRingEnd_apply, star_star])
    rw [hfun] at hcomp
    exact hcomp
  rw [adjoint_intervalIntegral _ hstarfK]
  have hadjoint : (fun t => ContinuousLinearMap.adjoint (star (f t) • K t)) =
      fun t => f t • ContinuousLinearMap.adjoint (K t) := by
    funext t
    exact (map_smulₛₗ ContinuousLinearMap.adjoint (star (f t)) (K t)).trans (by
      rw [starRingEnd_apply, star_star])
  rw [hadjoint, ← intervalIntegral.integral_add hfK hfAdjointK]
  congr 1
  funext t
  exact (smul_add (f t) (K t) (ContinuousLinearMap.adjoint (K t))).symm

end ContinuousLinearMap

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
