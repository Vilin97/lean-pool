/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvariance
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingQuantities

/-!
# Scaling

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-! The rescaling identities used to move a centre to the unit cylinder. -/

/-- The parabolic rescaling preserves suitability and transports all four
scale quantities to the original centre at the dilated radius. -/
theorem thmA_scaling_data
    (κ μ : ℝ) (hμ : 0 < μ)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) (r : ℝ) (hr : 0 < r) :
    IsSuitableWeakSolutionIntegrable (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) q
        (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
        (rescalePressure μ z₀ p) (rescaleForce μ z₀ f) ∧
      theta κ (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
          (rescalePressure μ z₀ p) ((0 : Vec3), (0 : ℝ)) r =
        theta κ u Du p z₀ (μ * r) ∧
      beta (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
          ((0 : Vec3), (0 : ℝ)) r = beta u Du z₀ (μ * r) ∧
      gamma (rescaleVelocity μ z₀ u) ((0 : Vec3), (0 : ℝ)) r =
        gamma u z₀ (μ * r) ∧
      delta (rescalePressure μ z₀ p) ((0 : Vec3), (0 : ℝ)) r =
        delta p z₀ (μ * r) ∧
      lambda q (rescaleForce μ z₀ f) ((0 : Vec3), (0 : ℝ)) r =
        lambda q f z₀ (μ * r) := by
  have hres := isSuitableWeakSolutionIntegrable_rescale hsol z₀ hμ
  refine ⟨hres, ?_, ?_, ?_, ?_, ?_⟩
  · exact theta_rescale_of_sws hsol κ μ hμ z₀ r hr
  · exact beta_rescale μ hμ z₀ u Du r
  · exact gamma_rescale μ hμ z₀ u r hr
  · exact delta_rescale μ hμ z₀ p r hr
  · exact lambda_rescale q μ
      (lt_trans (by norm_num : (0 : ℝ) < 5 / 2) hsol.2.2.2.1) hμ z₀ f r hr

/-- A start estimate at the rescaled unit centre transports to the original
centre.  The constants occur before the solution data, as in the paper. -/
theorem thmA_scaling_step
    (κ μ η Λ₀ : ℝ) (hμ : 0 < μ)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) (hstart :
      theta κ (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
          (rescalePressure μ z₀ p) ((0 : Vec3), (0 : ℝ)) (1 / 4) ≤ η ∧
      lambda q (rescaleForce μ z₀ f) ((0 : Vec3), (0 : ℝ)) (1 / 4) ≤ Λ₀) :
    theta κ u Du p z₀ (μ / 4) ≤ η ∧
      lambda q f z₀ (μ / 4) ≤ Λ₀ := by
  have hμ4 : 0 < (1 / 4 : ℝ) := by norm_num
  have htheta := (thmA_scaling_data κ μ hμ hsol z₀ (1 / 4) hμ4).2.1
  have hlambda := (thmA_scaling_data κ μ hμ hsol z₀ (1 / 4) hμ4).2.2.2.2.2
  have harg : μ * (1 / 4 : ℝ) = μ / 4 := by ring
  rw [harg] at htheta hlambda
  exact ⟨htheta.symm ▸ hstart.1, hlambda.symm ▸ hstart.2⟩

end CKN
