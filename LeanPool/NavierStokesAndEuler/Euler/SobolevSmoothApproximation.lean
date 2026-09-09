/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeat
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevDensity
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction

@[expose] public section

/-! Smooth high-regularity approximations converging contractively in the original Sobolev order. -/

noncomputable section

namespace EulerCylinderSobolevSpace

open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerCylinderSobolev
  EulerCylinderMollifier
  EulerMollifierRepresentative EulerSobolevHeat EulerGaussianCylinderHeat EulerNoncompactTransport
open scoped Topology ContDiff NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Three successive genuine heat smoothing steps. -/
def heatGainThree (q : ℕ) (v : ℝ≥0) (hv : 0 < v) :
    SobolevSpace period q →L[ℝ] SobolevSpace period (q+3) :=
  (heatGain period (q+2) v hv).comp ((heatGain period (q+1) v hv).comp (heatGain period q v hv))

/-- Its underlying field is exactly heat evolution with three times the variance. -/
theorem heatGainThree_value {q : ℕ} (v : ℝ≥0) (hv : 0 < v) (u : SobolevSpace period q) :
    value period (heatGainThree period q v hv u) = cylinderHeat period (v+(v+v)) (value period u)
      := by
  simp only [heatGainThree, ContinuousLinearMap.comp_apply, heatGain_value, cylinderHeat_semigroup]

/-- Forgetting the three gained derivatives recovers the usual contractive heat operator. -/
theorem restrict_heatGainThree {q : ℕ} (v : ℝ≥0) (hv : 0 < v) (u : SobolevSpace period q) :
    restrictOperator period (by omega : q ≤ q+3) (heatGainThree period q v hv u) = heatOperator
      period q (v+(v+v)) u := by
  apply value_injective period
  rw [value_restrictOperator, heatGainThree_value, heatOperator_value]

/-- A positive Gaussian scale tending to zero. -/
def smoothingVariance (n : ℕ) : ℝ≥0 := (cutoffScale n).toNNReal

theorem smoothingVariance_pos (n : ℕ) : 0 < smoothingVariance n := Real.toNNReal_pos.mpr
  (cutoffScale_pos n)

theorem smoothingVariance_tendsto : Filter.Tendsto smoothingVariance Filter.atTop (𝓝 0) := by
  change Filter.Tendsto (fun n => (cutoffScale n).toNNReal) Filter.atTop (𝓝 (0 : ℝ≥0))
  have h := continuous_real_toNNReal.continuousAt.tendsto.comp cutoffScale_tendsto
  simpa only [Real.toNNReal_zero, Function.comp_def, smoothingVariance] using h

/-- An approximation having three extra strong derivatives and an actual C∞ representative. -/
def smoothApprox (q n : ℕ) : SobolevSpace period q →L[ℝ] SobolevSpace period (q+3) :=
  (sobolevMollifier period (q+3) n).comp
    (heatGainThree period q (smoothingVariance n) (smoothingVariance_pos n))

/-- Exact description of the approximation in its original Sobolev topology. -/
theorem restrict_smoothApprox {q : ℕ} (n : ℕ) (u : SobolevSpace period q) :
    restrictOperator period (by omega : q ≤ q+3) (smoothApprox period q n u) =
      sobolevMollifier period q n (heatOperator period q
        (smoothingVariance n+(smoothingVariance n+smoothingVariance n)) u) := by
  apply value_injective period
  change mollify period n (value period (heatGainThree period q (smoothingVariance n)
    (smoothingVariance_pos n) u)) = _
  rw [heatGainThree_value]
  rfl

/-- The approximations are contractive at the original Sobolev order. -/
theorem smoothApprox_bound {q : ℕ} (n : ℕ) (u : SobolevSpace period q) :
    ‖restrictOperator period (by omega : q ≤ q+3) (smoothApprox period q n u)‖ ≤ ‖u‖ := by
  rw [restrict_smoothApprox]
  exact (sobolevMollifier_bound period n _).trans (heatOperator_bound period _ u)

theorem contractive_comp_dist {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (M : X →L[ℝ] X) (hM : ∀ z, ‖M z‖ ≤ ‖z‖) (H u : X) :
    dist (M H) u ≤ dist H u + dist (M u) u := by
  have hd : dist (M H) (M u) ≤ dist H u := by
    simpa only [map_sub, ← dist_eq_norm] using hM (H-u)
  exact (dist_triangle (M H) (M u) u).trans (add_le_add hd (le_refl (dist (M u) u)))

/-- A useful perturbation bound for simultaneous heat and convolution regularization. -/
theorem smoothApprox_dist {q : ℕ} (n : ℕ) (u : SobolevSpace period q) :
    dist (restrictOperator period (by omega : q ≤ q+3) (smoothApprox period q n u)) u ≤
      dist (heatOperator period q (smoothingVariance n+(smoothingVariance n+smoothingVariance n))
        u) u +
        dist (sobolevMollifier period q n u) u := by
  rw [restrict_smoothApprox]
  exact contractive_comp_dist (sobolevMollifier period q n) (sobolevMollifier_bound period n)
    (heatOperator period q (smoothingVariance n+(smoothingVariance n+smoothingVariance n)) u) u

/-- The smooth high-regularity approximations converge in the complete original Sobolev norm. -/
theorem smoothApprox_tendsto {q : ℕ} (u : SobolevSpace period q) :
    Filter.Tendsto (fun n => restrictOperator period (by omega : q ≤ q+3) (smoothApprox period q n
      u))
      Filter.atTop (𝓝 u) := by
  have hv : Filter.Tendsto (fun n => smoothingVariance n+(smoothingVariance n+smoothingVariance n))
      Filter.atTop (𝓝 0) := by
    simpa only [add_zero] using smoothingVariance_tendsto.add (smoothingVariance_tendsto.add
      smoothingVariance_tendsto)
  have hh := (heatOperator_continuous period u).continuousAt.tendsto.comp hv
  rw [heatOperator_zero] at hh
  have hm := sobolevMollifier_tendsto period u
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n => dist_nonneg) (fun n => smoothApprox_dist period n u)
  have hc : Filter.Tendsto (fun _n : ℕ => u) Filter.atTop (𝓝 u) := tendsto_const_nhds
  have hh' : Filter.Tendsto (fun n => dist (heatOperator period q
      (smoothingVariance n+(smoothingVariance n+smoothingVariance n)) u) u) Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_apply, dist_self] using hh.dist hc
  have hm' : Filter.Tendsto (fun n => dist (sobolevMollifier period q n u) u) Filter.atTop (𝓝 0) :=
    by
    simpa only [dist_self] using hm.dist hc
  simpa only [add_zero] using hh'.add hm'

/-- Each high-regularity approximation has a concrete smooth cylinder representative. -/
theorem smoothApprox_representative {q : ℕ} (n : ℕ) (u : SobolevSpace period q) :
    ∃ f : LiftDomain period → Vector3,
      (value period (smoothApprox period q n u) : LiftDomain period → Vector3) =ᵐ[liftMeasure
        period] f ∧
      ∀ x, ContDiff ℝ ∞ (localFieldLift period f x) := by
  let U := heatGainThree period q (smoothingVariance n) (smoothingVariance_pos n) u
  exact ⟨smoothMollifier period n (value period U), sobolevMollifier_representative period n U,
    smoothMollifier_smooth period n (value period U)⟩

end EulerCylinderSobolevSpace
