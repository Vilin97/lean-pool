/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Normalization of the integrated double-layer kernel

The positive-kernel route to the symmetrized Crouzeix--Palencia estimate
needs two independent inputs: pointwise positivity of the double-layer
kernel, and its total mass.  This file supplies the algebraic second input.

First, integration commutes with symmetrization `B ↦ B + B†`.  Consequently,
if a parametrized resolvent satisfies the Cauchy identity

`integral (gamma' • R_A(gamma)) = 2 * pi * i • 1`,

then its outward-normal kernel `(-i * gamma') • R_A(gamma)` has integral
`2 * pi • 1`, and the double-layer kernel obtained by adding the pointwise
adjoint has integral `4 * pi • 1`.

The resolvent Cauchy identity remains an explicit hypothesis here.  It is
the analytic input supplied separately by a circle or contour Cauchy theorem;
no such boundary-value assertion is hidden in the normalization argument.

## Main declarations

* `ContinuousLinearMap.intervalIntegral_add_adjoint` -- interval integration
  commutes with pointwise symmetrization.
* `intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy` --
  the double-layer kernel has total mass `4 * pi • 1` whenever the underlying
  resolvent contour has Cauchy integral `2 * pi * i • 1`.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.AdjointIntegral
import Mathlib.Algebra.Algebra.Spectrum.Basic

open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace ContinuousLinearMap

/-- Interval integration commutes with symmetrization of an
operator-valued integrand. -/
theorem intervalIntegral_add_adjoint {f : ℝ → E →L[ℂ] E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, f t + ContinuousLinearMap.adjoint (f t)) =
      (∫ t in a..b, f t) +
        ContinuousLinearMap.adjoint (∫ t in a..b, f t) := by
  let adj : (E →L[ℂ] E) →L⋆[ℂ] (E →L[ℂ] E) :=
    ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap
  have hfadj : IntervalIntegrable (fun t ↦ ContinuousLinearMap.adjoint (f t))
      volume a b := by
    constructor
    · change Integrable (fun t ↦ adj (f t)) (volume.restrict (Ioc a b))
      exact adj.integrable_comp hf.1
    · change Integrable (fun t ↦ adj (f t)) (volume.restrict (Ioc b a))
      exact adj.integrable_comp hf.2
  rw [intervalIntegral.integral_add hf hfadj,
    ← ContinuousLinearMap.adjoint_intervalIntegral f hf]

end ContinuousLinearMap

/-- If the parametrized resolvent has its expected Cauchy integral
`2 * pi * i • 1`, then the associated outward-normal double-layer kernel
has total mass `4 * pi • 1`. -/
theorem intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy
    (A : E →L[ℂ] E) (gamma : ℝ → ℂ)
    (hint : IntervalIntegrable
      (fun t ↦ deriv gamma t • resolvent A (gamma t)) volume 0 (2 * Real.pi))
    (hCauchy : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv gamma t • resolvent A (gamma t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E)) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      ((-I * deriv gamma t) • resolvent A (gamma t)) +
        ContinuousLinearMap.adjoint
          ((-I * deriv gamma t) • resolvent A (gamma t))) =
      (4 * Real.pi) • (1 : E →L[ℂ] E) := by
  let B : ℝ → E →L[ℂ] E := fun t ↦
    (-I * deriv gamma t) • resolvent A (gamma t)
  have hBfun : B = fun t ↦ (-I) • (deriv gamma t • resolvent A (gamma t)) := by
    funext t
    simp only [B, smul_smul]
  have hB : IntervalIntegrable B volume 0 (2 * Real.pi) := by
    rw [hBfun]
    exact ⟨hint.1.smul_enorm (-I), hint.2.smul_enorm (-I)⟩
  have hBint : (∫ t in (0 : ℝ)..(2 * Real.pi), B t) =
      (2 * Real.pi) • (1 : E →L[ℂ] E) := by
    rw [hBfun, intervalIntegral.integral_smul, hCauchy, smul_smul]
    congr 1
    have hI : I * (2 * ((Real.pi : ℂ) * I)) = -(2 * (Real.pi : ℂ)) := by
      calc
        I * (2 * ((Real.pi : ℂ) * I)) = (2 * (Real.pi : ℂ)) * (I * I) := by ring
        _ = -(2 * (Real.pi : ℂ)) := by rw [I_mul_I, mul_neg, mul_one]
    calc
      -I * (2 * (Real.pi : ℂ) * I) = -(I * (2 * ((Real.pi : ℂ) * I))) := by ring
      _ = -(-(2 * (Real.pi : ℂ))) := congrArg Neg.neg hI
      _ = (((2 * Real.pi : ℝ) : ℂ)) := by norm_num
  change (∫ t in (0 : ℝ)..(2 * Real.pi),
      B t + ContinuousLinearMap.adjoint (B t)) = _
  rw [ContinuousLinearMap.intervalIntegral_add_adjoint hB, hBint]
  have hadj : ContinuousLinearMap.adjoint
      ((2 * Real.pi) • (1 : E →L[ℂ] E)) =
      (2 * Real.pi) • (1 : E →L[ℂ] E) := by
    change ContinuousLinearMap.adjoint
      (((2 * Real.pi : ℝ) : ℂ) • (1 : E →L[ℂ] E)) =
      (((2 * Real.pi : ℝ) : ℂ) • (1 : E →L[ℂ] E))
    rw [map_smulₛₗ, Complex.conj_ofReal, ContinuousLinearMap.adjoint_one]
  rw [hadj, ← add_smul]
  congr 1
  ring

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
