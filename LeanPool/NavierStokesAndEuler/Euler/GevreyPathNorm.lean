/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EnergyMetricPaths
import LeanPool.NavierStokesAndEuler.Euler.GevreyContinuationNorm

/-! A genuine metric Gevrey bound supplies the uniform Banach norm used in actual continuation. -/

@[expose] public section


noncomputable section

namespace EulerGevreyPathNorm

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGevreyMetricEstimate
  EulerGevreyContinuationNorm EulerEnergyMetricPaths EulerPacketWeights
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A uniform metric-energy bound controls the actual continuous Sobolev path norm. -/
theorem norm_le_of_energy_bound {q : ℕ} (N : ℕ) (hN : N + 6 ≤ q + 1) (hS : q + 1 ≤ N + 6)
    (T : ℝ) (R : C(Icc (0 : ℝ) T, ℝ))
    (K : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (c δ E : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hE : 0 ≤ E)
    (hR : ∀ t, δ ≤ R t) (hK : ∀ t v, c ^ 2 * ‖v‖ ^ 2 ≤ inner ℝ (K t v) v)
    (he : ∀ t, energyPath period N hN T R K e t ≤ E) :
    ‖e‖ ≤ metricAmplification c*E/weight δ N := by
  have ha : 0 ≤ metricAmplification c := (by
      norm_num : (0 : ℝ) ≤ 1).trans (metricAmplification_one_le hc)
  have hw := weight_pos hδ N
  apply (ContinuousMap.norm_le e (div_nonneg (mul_nonneg ha hE) hw.le)).mpr
  intro t
  have h := norm_le_metric period N hN hS (R t) δ hδ (hR t) hδ1 (K t) (e t) c hc (hK t)
  have he' : energyNorm period N hN (R t) (K t) (e t) ≤ E := by
    simpa only [energyPath_apply] using he t
  exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he' ha) hw.le)

end EulerGevreyPathNorm
