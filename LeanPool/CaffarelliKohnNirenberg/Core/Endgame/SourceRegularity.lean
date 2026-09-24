/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.HeatRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.HolderGluing
public import LeanPool.CaffarelliKohnNirenberg.Core.Parameters

/-! # Local regularity from actual heat-potential sources

An almost-everywhere heat representation transfers the quantitative estimate
for compactly supported Morrey sources to the represented velocity.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- Genuine Morrey sources and an almost-everywhere heat representation give
a bounded Hölder representative and regularity at the center of the ball. -/
theorem regular_point_of_heat_sources
    {Ω : Set Vec3} {I : Set ℝ} {u F : ParabolicPoint → Vec3}
    {G : Fin 3 → ParabolicPoint → Vec3} {z : ParabolicPoint} {R γ θ₀ θ₁ P : ℝ}
    (hR : 0 < R) (hball : Metric.ball z R ⊆ spaceTimeSet Ω I)
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5) (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : ∀ i, AEMeasurable (fun x => F x i) volume)
    (hG : ∀ j i, AEMeasurable (fun x => G j x i) volume)
    (hNF : ∀ i, morreyNorm P θ₀ (fun x => F x i) < ∞)
    (hNG : ∀ j i, morreyNorm P θ₁ (fun x => G j x i) < ∞)
    (hSupportF : ∀ i, HasCompactSupport (fun x => F x i))
    (hSupportG : ∀ j i, HasCompactSupport (fun x => G j x i))
    (hrep : u =ᵐ[volume.restrict (Metric.ball z R)]
      (fun x i => heatPotential (fun y => F y i) (fun j y => G j y i) x)) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (Metric.ball z R)] u ∧
      ParabolicHolderVecNormLE (Metric.ball z R) w γ
        (vectorHeatValueBound F G γ θ₀ θ₁ P z R +
          vectorHeatHolderCoefficient F G γ θ₀ θ₁ P) ∧
      IsRegularPoint Ω I u z := by
  obtain ⟨w, hw, hnorm⟩ := vector_heat_representative_of_morrey
    hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ hF hG hNF hNG hSupportF hSupportG
  have hwlocal : w =ᵐ[volume.restrict (Metric.ball z R)]
      (fun x i => heatPotential (fun y => F y i) (fun j y => G j y i) x) :=
    ae_restrict_of_ae hw
  have hwu : w =ᵐ[volume.restrict (Metric.ball z R)] u := hwlocal.trans hrep.symm
  refine ⟨w, hwu, hnorm z R hR, ?_⟩
  exact regular_point_of_holder_norm Metric.isOpen_ball (Metric.mem_ball_self hR)
    (Subset.refl _) hball hγ hγ1.le hwu (hnorm z R hR)

/-- The standing exponent choices discharge all numerical conditions of the
heat regularity estimate at integrability exponent `6/5`. -/
theorem regular_point_of_heat_sources_at_step_parameters
    {Ω : Set Vec3} {I : Set ℝ} {u F : ParabolicPoint → Vec3}
    {G : Fin 3 → ParabolicPoint → Vec3} {z : ParabolicPoint} {R q : ℝ}
    (hq : (5 : ℝ) / 2 < q)
    (hR : 0 < R) (hball : Metric.ball z R ⊆ spaceTimeSet Ω I)
    (hF : ∀ i, AEMeasurable (fun x => F x i) volume)
    (hG : ∀ j i, AEMeasurable (fun x => G j x i) volume)
    (hNF : ∀ i, morreyNorm (6 / 5) (stepTheta₀ (stepGamma₀ q))
      (fun x => F x i) < ∞)
    (hNG : ∀ j i, morreyNorm (6 / 5) (stepTheta₁ (stepGamma₀ q))
      (fun x => G j x i) < ∞)
    (hSupportF : ∀ i, HasCompactSupport (fun x => F x i))
    (hSupportG : ∀ j i, HasCompactSupport (fun x => G j x i))
    (hrep : u =ᵐ[volume.restrict (Metric.ball z R)]
      (fun x i => heatPotential (fun y => F y i) (fun j y => G j y i) x)) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (Metric.ball z R)] u ∧
      ParabolicHolderVecNormLE (Metric.ball z R) w (stepGamma₀ q)
        (vectorHeatValueBound F G (stepGamma₀ q) (stepTheta₀ (stepGamma₀ q))
          (stepTheta₁ (stepGamma₀ q)) (6 / 5) z R +
          vectorHeatHolderCoefficient F G (stepGamma₀ q) (stepTheta₀ (stepGamma₀ q))
            (stepTheta₁ (stepGamma₀ q)) (6 / 5)) ∧
      IsRegularPoint Ω I u z := by
  have hγ := stepGamma₀_pos hq
  have hγ1 := stepGamma₀_lt_one q
  have hθ₀ := stepTheta₀_gt_half hγ hγ1
  have hθ₁ := stepTheta₁_gt_five hγ hγ1
  exact regular_point_of_heat_sources hR hball hγ hγ1
    (stepTheta₀_inv _) (stepTheta₁_inv _) (by norm_num)
    (by linarith only [hθ₀]) (by linarith only [hθ₁])
    hF hG hNF hNG hSupportF hSupportG hrep

end CKN.Core.Endgame
