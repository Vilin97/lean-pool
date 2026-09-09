/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.TransportDerivatives
import LeanPool.NavierStokesAndEuler.Euler.Foundations.IntervalTrace
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Cylinder Graph Trace
-/

@[expose] public section

noncomputable section

namespace EulerCylinderGraphTrace

open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open Set
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [Fact (0 < period)] [CompleteSpace F] in
theorem angular_hasDerivAt (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : Vector3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x, (s : AddCircle period)))
      (fieldDerivative period (0, 1) f (x, (t : AddCircle period))) t := by
  have hd := ((hf 0).differentiable (by simp) (x, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have he := fderiv_localFieldLift_cover period f (x, t)
  change fderiv ℝ (localFieldLift period f (x, (t : AddCircle period))) 0 =
    fderiv ℝ (localFieldLift period f 0) (x, t) at he
  change HasDerivAt _ ((fderiv ℝ (localFieldLift period f (x, (t : AddCircle period))) 0) (0, 1)) t
  rw [he]
  simpa [Function.comp_def, localFieldLift] using hd

/-- Point evaluation in the periodic coordinate costs one angular derivative,
with a bound independent of the chosen phase. -/
theorem cylinder_pointwise_trace (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (x : Vector3) (θ : AddCircle period) :
    ‖f (x, θ)‖ ^ 2 ≤
      (2 / period) * (∫ s : AddCircle period, ‖f (x, s)‖ ^ 2) +
      (2 * period) * (∫ s : AddCircle period,
        ‖fieldDerivative period (0, 1) f (x, s)‖ ^ 2) := by
  have hT : 0 < period := Fact.out
  let θ₀ := AddCircle.equivIco period 0 θ
  have hθ : (θ₀ : ℝ) ∈ Icc 0 period := by
    have hh := θ₀.property
    simp only [zero_add] at hh
    exact ⟨hh.1, hh.2.le⟩
  have hcont : Continuous (fun s : ℝ => fieldDerivative period (0, 1) f
      (x, (s : AddCircle period))) := by
    exact (smoothField_continuous period _
      (fieldDerivative_smooth period (0, 1) f hf)).comp
      (continuous_const.prodMk (AddCircle.continuous_mk' period))
  have h := EulerIntervalTrace.pointwise_H1_trace
    (fun s : ℝ => f (x, (s : AddCircle period)))
    (fun s : ℝ => fieldDerivative period (0, 1) f (x, (s : AddCircle period)))
    0 period hT hcont.continuousOn (fun s _ => angular_hasDerivAt period f hf x s)
    θ₀ hθ
  have hcoe : ((θ₀ : ℝ) : AddCircle period) = θ := AddCircle.coe_equivIco
  rw [hcoe] at h
  have hfi := AddCircle.intervalIntegral_preimage period 0
    (fun s : AddCircle period => ‖f (x, s)‖ ^ 2)
  have hdi := AddCircle.intervalIntegral_preimage period 0
    (fun s : AddCircle period => ‖fieldDerivative period (0, 1) f (x, s)‖ ^ 2)
  simp only [zero_add] at hfi hdi
  simpa only [sub_zero, hfi, hdi] using h

/-- Pullback to any continuous phase graph preserves square integrability.
The estimate has no dependence on the phase frequency. -/
theorem graph_memLp_and_energy_bound (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : MemLp f 2 (liftMeasure period))
    (hdL2 : MemLp (fieldDerivative period (0, 1) f) 2 (liftMeasure period))
    (θ : Vector3 → AddCircle period) (hθ : Continuous θ) :
    MemLp (fun x => f (x, θ x)) 2 volume ∧
      (∫ x : Vector3, ‖f (x, θ x)‖ ^ 2) ≤
        (2 / period) * (∫ z, ‖f z‖ ^ 2 ∂liftMeasure period) +
        (2 * period) * (∫ z, ‖fieldDerivative period (0, 1) f z‖ ^ 2
          ∂liftMeasure period) := by
  have hfc : Continuous (fun x => f (x, θ x)) :=
    (smoothField_continuous period f hf).comp (continuous_id.prodMk hθ)
  have hfint := hfL2.norm.integrable_sq
  have hdint := hdL2.norm.integrable_sq
  have hi := (hfint.integral_prod_left.const_mul (2 / period)).add
    (hdint.integral_prod_left.const_mul (2 * period))
  have hgraph : Integrable (fun x => ‖f (x, θ x)‖ ^ 2) volume := by
    apply hi.mono' (hfc.norm.pow 2).aestronglyMeasurable
    filter_upwards [] with x
    change ‖‖f (x, θ x)‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f (x, θ x)‖)]
    exact cylinder_pointwise_trace period f hf x (θ x)
  refine ⟨(memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).mpr hgraph, ?_⟩
  have hbound := integral_mono hgraph hi (fun x => cylinder_pointwise_trace period f hf x (θ x))
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hfint.integral_prod_left.const_mul (2 / period))
    (hdint.integral_prod_left.const_mul (2 * period)), integral_const_mul, integral_const_mul,
    integral_integral hfint, integral_integral hdint] at hbound
  exact hbound

end EulerCylinderGraphTrace
