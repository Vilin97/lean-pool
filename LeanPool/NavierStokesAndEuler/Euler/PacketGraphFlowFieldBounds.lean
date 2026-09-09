/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphFlowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketGraphFlowFrequency

@[expose] public section

/-! The frequency estimates apply directly to the actual rescaled graph
flow fields, with arbitrarily small losses in the frequency exponent. -/

noncomputable section


namespace EulerPhysicalGraphFlowBounds

open Set Filter EulerLiftedGradientSpace EulerSmoothFlowGevrey
  EulerPacketGraphFlowFrequency EulerCylinderGraphGevrey
  EulerLpTranslation.SmoothL2Field

variable (P T : ℝ) [Fact (0 < P)]

theorem data_field_bounds_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℝ in atTop, ∀ (G : Data P T),
      G.C=G.B → G.S=G.R → G.S₁=G.R →
      G.B ≤ 2*k^(-(1/2 : ℝ)) → G.R ≤ k^(inputExponent ε) →
      G.C₁ ≤ k^(inputExponent ε) → T ≤ k^(inputExponent ε) →
      ∀ m : Vector3, ‖m‖=1 → ∀ (ell : ℝ) (hell : 0 < ell), ell ≤ 1 →
      ∀ t : Icc (0 : ℝ) T,
      (G.displacementField k m ell hell t).HasJetBound
        (k^(-(1/2 : ℝ)+ε)) (ell⁻¹*k^(1+ε)) ∧
      (G.velocityField k m ell hell t).HasJetBound
        (k^(-(1/2 : ℝ)+ε)) (ell⁻¹*k^(1+ε)) ∧
      (G.accelerationFieldL2 k m ell hell t).HasJetBound
        (k^ε) (ell⁻¹*k^(1+ε)) := by
  filter_upwards [physical_bounds_eventually ε (Real.sqrt (2/P+2*P)) hε (Real.sqrt_nonneg _),
    eventually_ge_atTop (1 : ℝ)] with k hnum hk
  intro G hC hS hS₁ hB hR hC₁ hT m hm ell hell hell1 t
  have hn := hnum G.B G.R T G.C₁ ell G.B_nonneg G.R_pos.le G.time_nonneg
    G.C₁_nonneg hell hR hT hC₁ hB
  have hvr : G.velocityRadius=flowRadius G.B G.R T G.R := by rw [Data.velocityRadius,hS]
  have har : G.accelerationRadius=flowRadius G.B G.R T (6*G.R) := by
    rw [Data.accelerationRadius,hS,hS₁]
    congr 1
    ring
  have haa : G.accelerationAmplitude=G.C₁+3*G.B^2*G.R := by
    rw [Data.accelerationAmplitude,hC]
    ring
  have hgf : graphFactor k m=1+k := by
    rw [graphFactor,hm,abs_of_nonneg (by linarith : 0 ≤ k),mul_one]
  have hv0 := G.velocityRadius_nonneg
  have ha0 := G.accelerationRadius_nonneg
  have hc0 := G.C_nonneg
  have ht0 := G.time_nonneg
  have hac0 := G.accelerationAmplitude_nonneg
  have hg0 := graphFactor_nonneg k m
  refine ⟨?_,?_,?_⟩
  · apply (G.displacementField_bound k m ell hell hell1 t).mono
    · positivity
    · positivity
    · simpa only [hC,hvr] using hn.1
    · simpa only [hvr,hgf] using hn.2.2.2.1
  · apply (G.velocityField_bound k m ell hell hell1 t).mono
    · positivity
    · positivity
    · simpa only [hC,hvr] using hn.2.1
    · simpa only [hvr,hgf] using hn.2.2.2.1
  · apply (G.accelerationField_bound k m ell hell hell1 t).mono
    · positivity
    · positivity
    · simpa only [haa,har] using hn.2.2.1
    · simpa only [har,hgf] using hn.2.2.2.2

end EulerPhysicalGraphFlowBounds
