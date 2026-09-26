/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.Configuration

/-!
# Normalization of six-point configurations

This file translates and rescales a configuration for the finite six-point problem.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

namespace SixPointConfiguration

/-- Translate a configuration by `origin` and divide all coordinates by `scale`. -/
def normalize (configuration : SixPointConfiguration)
    (origin : (EuclideanSpace ℝ (Fin 2))) (scale : ℝ) :
    SixPointConfiguration :=
  fun color label ↦ scale⁻¹ • (configuration color label - origin)

/-- Normalization by a positive scale divides every pairwise distance by that scale. -/
theorem dist_normalize (configuration : SixPointConfiguration)
    (origin : (EuclideanSpace ℝ (Fin 2))) {scale : ℝ}
    (hscale : 0 < scale) (color₁ color₂ : SixPointColor) (label₁ label₂ : SixPointLabel) :
    dist (configuration.normalize origin scale color₁ label₁)
        (configuration.normalize origin scale color₂ label₂) =
      dist (configuration color₁ label₁) (configuration color₂ label₂) / scale := by
  simp [normalize, dist_smul₀, Real.norm_eq_abs, abs_of_pos hscale, div_eq_inv_mul]

/-- Multiplying normalized distances by the positive scale recovers physical distances. -/
theorem dist_eq_scale_mul_dist_normalize (configuration : SixPointConfiguration)
    (origin : (EuclideanSpace ℝ (Fin 2))) {scale : ℝ} (hscale : 0 < scale)
    (color₁ color₂ : SixPointColor) (label₁ label₂ : SixPointLabel) :
    dist (configuration color₁ label₁) (configuration color₂ label₂) =
      scale * dist (configuration.normalize origin scale color₁ label₁)
        (configuration.normalize origin scale color₂ label₂) := by
  rw [configuration.dist_normalize origin hscale]
  field_simp

/-- Distance bounds at scale `scale` give an admissible normalized configuration. -/
theorem isAdmissibleAt_normalize_of_distances (configuration : SixPointConfiguration)
    (origin : (EuclideanSpace ℝ (Fin 2))) {scale d γ q s : ℝ} (hscale : 0 < scale)
    (hroot : dist (configuration .red .root) (configuration .blue .root) = scale)
    (hchild : ∀ color label, label ≠ .root →
      dist (configuration color .root) (configuration color label) ≤ d)
    (hsibling : ∀ color,
      2 * γ * d < dist (configuration color .left) (configuration color .right))
    (hq : q = d / scale) (hq_le_one : q ≤ 1) (hs_le : s ≤ γ * q) :
    (configuration.normalize origin scale).IsAdmissibleAt s := by
  constructor
  · rw [configuration.dist_normalize origin hscale, hroot]
    exact div_self hscale.ne'
  · intro color label hlabel
    rw [configuration.dist_normalize origin hscale]
    calc
      _ ≤ d / scale := div_le_div_of_nonneg_right (hchild color label hlabel) hscale.le
      _ = q := hq.symm
      _ ≤ 1 := hq_le_one
  · intro color
    rw [configuration.dist_normalize origin hscale]
    have hscaled : 2 * γ * (d / scale) <
        dist (configuration color .left) (configuration color .right) / scale := by
      calc
        _ = (2 * γ * d) / scale := by ring
        _ < _ := (div_lt_div_iff_of_pos_right hscale).2 (hsibling color)
    rw [← hq] at hscaled
    nlinarith

end SixPointConfiguration

end LeanPool.Besicovitch
