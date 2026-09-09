/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphFlowSupBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketGraphFlowFrequency

@[expose] public section

/-! The actual physical graph displacement and velocity obey the same
arbitrarily small exponent losses as the cylinder-to-graph L² bounds. -/

noncomputable section


namespace EulerPhysicalGraphFlowBounds

open Set Filter EulerLiftedGradientSpace EulerSmoothFlowGevrey
  EulerPacketGraphFlowFrequency EulerCylinderGraphGevrey EulerGevrey

private theorem radius_le_flowRadius (B R T : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R) (hT : 0 ≤ T) :
    R ≤ flowRadius B R T R := by
  have h₁ : (1 : ℝ) ≤ 4*R+1 := by linarith
  have h₂ : R ≤ (1+B*T)*R+2 := by nlinarith [mul_nonneg (mul_nonneg hB hT) hR]
  have h := mul_le_mul h₁ h₂ hR (by positivity : 0 ≤ 4*R+1)
  simpa only [one_mul,flowRadius] using h

variable (P T : ℝ) [Fact (0 < P)]

theorem data_sup_bounds_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℝ in atTop, ∀ (G : Data P T),
      G.B ≤ 2*k^(-(1/2 : ℝ)) → G.R ≤ k^(inputExponent ε) → T ≤ k^(inputExponent ε) →
      ∀ m : Vector3, ‖m‖=1 → ∀ (ell : ℝ) (hell : 0 < ell), ell ≤ 1 →
      ∀ t : Icc (0 : ℝ) T,
      HasSupBound (G.displacementField k m ell hell t).field
        (k^(-(1/2 : ℝ)+ε)) (ell⁻¹*k^(1+ε)) ∧
      HasSupBound (G.velocityField k m ell hell t).field
        (k^(-(1/2 : ℝ)+ε)) (ell⁻¹*k^(1+ε)) := by
  filter_upwards [physical_bounds_eventually ε 1 hε zero_le_one,
    eventually_ge_atTop (1 : ℝ)] with k hnum hk
  intro G hB hR hT m hm ell hell hell1 t
  have hk0 : 0 ≤ k := by linarith
  have hn := hnum G.B G.R T 0 ell G.B_nonneg G.R_pos.le G.time_nonneg le_rfl hell
    hR hT (Real.rpow_nonneg hk0 _) hB
  have hgf : graphFactor k m=1+k := by rw [graphFactor,hm,abs_of_nonneg hk0,mul_one]
  have hf0 : 0 ≤ flowRadius G.B G.R T G.R := by
    have := G.B_nonneg
    have := G.R_pos
    have := G.time_nonneg
    unfold flowRadius
    positivity
  have hrad := hn.2.2.2.1
  have hB0 := G.B_nonneg
  have hT0 := G.time_nonneg
  have hR0 := G.R_pos.le
  have hg0 := graphFactor_nonneg k m
  have hdisp : G.B*T ≤ k^(-(1/2 : ℝ)+ε) := by
    apply (show G.B*T ≤ T*G.B*(1+flowRadius G.B G.R T G.R) by
      nlinarith [mul_nonneg (mul_nonneg hB0 hT0) hf0]).trans
    simpa only [one_mul] using hn.1
  have hvel : G.B ≤ k^(-(1/2 : ℝ)+ε) := by
    apply (show G.B ≤ G.B*(1+flowRadius G.B G.R T G.R) by nlinarith [mul_nonneg hB0 hf0]).trans
    simpa only [one_mul] using hn.2.1
  constructor
  · apply (G.displacement_sup_bound k m ell hell hell1 t).mono (mul_nonneg hB0 hT0) (by positivity)
    hdisp
    rw [hgf]
    apply le_trans _ hrad
    gcongr
    exact radius_le_flowRadius G.B G.R T hB0 hR0 hT0
  · apply (G.velocity_sup_bound k m ell hell hell1 t).mono hB0 (by positivity) hvel
    rw [hgf]
    apply le_trans _ hrad
    gcongr
    nlinarith

end EulerPhysicalGraphFlowBounds
