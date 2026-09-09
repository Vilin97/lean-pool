/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanScaledCutoff

/-! Actual initial support in physical-label coordinates for the mean boundary operator. -/

@[expose] public section


noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal

theorem scaledBoundary_zero_outside (ℓ : ℝ) (hℓ : 0 < ℓ) (z : L2) :
    ∀ᵐ x ∂volume, 2 < ‖ℓ • x‖ → boundaryOperator (scaledCutoff ℓ hℓ) z x = 0 := by
  have H := (ae_restrict_iff' (isClosed_tsupport (scaledCutoff ℓ hℓ).field).measurableSet.compl).1
    (boundaryOperator_zero_off_support (scaledCutoff ℓ hℓ) z)
  filter_upwards [H] with x hx
  intro hnorm
  apply hx
  intro hm
  exact (not_le_of_gt hnorm) (scaledCutoff_support ℓ hℓ hm)

theorem scaledBoundary_multiple_zero_outside (ℓ : ℝ) (hℓ : 0 < ℓ) (L : ℝ) (z : L2) :
    ∀ᵐ x ∂volume, 2 < ‖ℓ • x‖ → (L • boundaryOperator (scaledCutoff ℓ hℓ) z : L2) x = 0 := by
  filter_upwards [scaledBoundary_zero_outside ℓ hℓ z,
    Lp.coeFn_smul L (boundaryOperator (scaledCutoff ℓ hℓ) z)] with x hx hs
  intro hnorm
  rw [hs]
  change L • boundaryOperator (scaledCutoff ℓ hℓ) z x = 0
  rw [hx hnorm, smul_zero]

/-- Any continuous representative of the actual initial boundary velocity has this support. -/
theorem scaledBoundary_continuous_support (ℓ : ℝ) (hℓ : 0 < ℓ) (L : ℝ) (z : L2)
    (b : Space → Space) (hb : Continuous b)
    (hrep : b =ᵐ[volume] (L • boundaryOperator (scaledCutoff ℓ hℓ) z : L2)) :
    tsupport b ⊆ {x : Space | ‖ℓ • x‖ ≤ 2} := by
  have hU : IsOpen {x : Space | 2 < ‖ℓ • x‖} :=
    isOpen_lt continuous_const (continuous_const_smul ℓ).norm
  have hae : b =ᵐ[volume.restrict {x : Space | 2 < ‖ℓ • x‖}] 0 := by
    apply (ae_restrict_iff' hU.measurableSet).2
    filter_upwards [hrep, scaledBoundary_multiple_zero_outside ℓ hℓ L z] with x hx hz
    intro hnorm
    exact hx.trans (hz hnorm)
  have hzero := MeasureTheory.Measure.eqOn_open_of_ae_eq hae hU hb.continuousOn
    continuous_const.continuousOn
  apply closure_minimal _ (isClosed_le (continuous_const_smul ℓ).norm continuous_const)
  intro x hx
  by_contra h
  have hnorm : 2 < ‖ℓ • x‖ := lt_of_not_ge h
  exact hx (hzero hnorm)

theorem scaledBoundary_continuous_compact (ℓ : ℝ) (hℓ : 0 < ℓ) (L : ℝ) (z : L2)
    (b : Space → Space) (hb : Continuous b)
    (hrep : b =ᵐ[volume] (L • boundaryOperator (scaledCutoff ℓ hℓ) z : L2)) :
    HasCompactSupport b := by
  apply (isCompact_closedBall (0 : Space) (2/ℓ)).of_isClosed_subset (isClosed_tsupport b)
  intro x hx
  have hs := scaledBoundary_continuous_support ℓ hℓ L z b hb hrep hx
  change ‖ℓ • x‖ ≤ 2 at hs
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ] at hs
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact (le_div_iff₀ hℓ).2 (by simpa only [mul_comm] using hs)

end EulerMeanBoundary
