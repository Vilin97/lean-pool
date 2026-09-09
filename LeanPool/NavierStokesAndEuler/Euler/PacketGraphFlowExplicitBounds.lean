/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGraphFlowFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketGraphFlowSupBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyMargin

@[expose] public section

/-! The quarter-power physical-flow bounds follow from the same tiny-power
source comparison and one parent-independent numerical margin. -/

noncomputable section

namespace EulerPacketGraphFlowFrequency

open Real EulerSmoothFlowGevrey EulerPacketSourceFrequency

theorem physical_bounds_of_costs (K B R T C1 k ell : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hR : 0 ≤ R) (hT : 0 ≤ T) (hC1 : 0 ≤ C1)
    (hk : 1 ≤ k) (hell : 0 < ell)
    (hw : max 71 K ≤ k^(1/24 : ℝ)) (hroot : 16 ≤ k^(1/4 : ℝ))
    (hRk : R ≤ smallPower k) (hTk : T ≤ smallPower k) (hCk : C1 ≤ smallPower k)
    (hsmall : B ≤ 2*k^(-(1/2 : ℝ))) :
    K*(T*B)*(1+flowRadius B R T R) ≤ k^(-(1/4 : ℝ)) ∧
    K*B*(1+flowRadius B R T R) ≤ k^(-(1/4 : ℝ)) ∧
    K*(C1+3*B^2*R)*(1+flowRadius B R T (6*R)) ≤ k^(1/4 : ℝ) ∧
    ell⁻¹*(4*flowRadius B R T R*(1+k)) ≤ ell⁻¹*k^(5/4 : ℝ) ∧
    ell⁻¹*(4*flowRadius B R T (6*R)*(1+k)) ≤ ell⁻¹*k^(5/4 : ℝ) := by
  have hs := smallPower_le_power k (1/24) hk (by norm_num [theta])
  have hr : 2 ≤ k^(1/2-(1/24 : ℝ)) :=
    (show 2 ≤ k^(1/4 : ℝ) by linarith).trans
      (Real.rpow_le_rpow_of_exponent_le hk (by norm_num))
  simpa only [show -(1/2 : ℝ)+1/4=-(1/4) by norm_num,
    show (1 : ℝ)+1/4=5/4 by norm_num] using
    physical_bounds_of_power (1/4) (1/24) K k B R T C1 ell
      (by norm_num) (by norm_num) (by norm_num) hK hB hR hT hC1 hk hell
      ((le_max_left _ _).trans hw) ((le_max_right _ _).trans hw)
      (hRk.trans hs) (hTk.trans hs) (hCk.trans hs) hr hsmall

end EulerPacketGraphFlowFrequency

namespace EulerPhysicalGraphFlowBounds

open Set Real EulerLiftedGradientSpace EulerSmoothFlowGevrey
  EulerPacketGraphFlowFrequency EulerPacketSourceFrequency EulerCylinderGraphGevrey
  EulerLpTranslation.SmoothL2Field EulerGevrey

variable (P T : ℝ) [Fact (0 < P)]

theorem data_field_bounds_explicit (G : Data P T) (k : ℝ)
    (hC : G.C=G.B) (hS : G.S=G.R) (hS1 : G.S₁=G.R)
    (hk : 1 ≤ k) (hw : max 71 (Real.sqrt (2/P+2*P)) ≤ k^(1/24 : ℝ))
    (hroot : 16 ≤ k^(1/4 : ℝ)) (hB : G.B ≤ 2*k^(-(1/2 : ℝ)))
    (hR : G.R ≤ smallPower k) (hC1 : G.C₁ ≤ smallPower k) (hT : T ≤ smallPower k)
    (m : Vector3) (hm : ‖m‖=1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) :
    (G.displacementField k m ell hell t).HasJetBound (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) ∧
    (G.velocityField k m ell hell t).HasJetBound (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) ∧
    (G.accelerationFieldL2 k m ell hell t).HasJetBound (k^(1/4 : ℝ)) (ell⁻¹*k^(5/4 : ℝ)) := by
  have hn := physical_bounds_of_costs (Real.sqrt (2/P+2*P)) G.B G.R T G.C₁ k ell
    (Real.sqrt_nonneg _) G.B_nonneg G.R_pos.le G.time_nonneg G.C₁_nonneg hk hell
    hw hroot hR hT hC1 hB
  have hvr : G.velocityRadius=flowRadius G.B G.R T G.R := by rw [Data.velocityRadius,hS]
  have har : G.accelerationRadius=flowRadius G.B G.R T (6*G.R) := by
    rw [Data.accelerationRadius,hS,hS1]
    congr 1
    ring
  have haa : G.accelerationAmplitude=G.C₁+3*G.B^2*G.R := by rw [Data.accelerationAmplitude,hC]; ring
  have hgf : graphFactor k m=1+k := by
    rw [graphFactor,hm,abs_of_nonneg (zero_le_one.trans hk),mul_one]
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

theorem data_sup_bounds_explicit (G : Data P T) (k : ℝ)
    (hk : 1 ≤ k) (hw : 71 ≤ k^(1/24 : ℝ)) (hroot : 16 ≤ k^(1/4 : ℝ))
    (hB : G.B ≤ 2*k^(-(1/2 : ℝ))) (hR : G.R ≤ smallPower k) (hT : T ≤ smallPower k)
    (m : Vector3) (hm : ‖m‖=1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) :
    HasSupBound (G.displacementField k m ell hell t).field (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) ∧
    HasSupBound (G.velocityField k m ell hell t).field (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) := by
  have hk0 := zero_le_one.trans hk
  have hn := physical_bounds_of_costs 1 G.B G.R T 0 k ell zero_le_one
    G.B_nonneg G.R_pos.le G.time_nonneg le_rfl hk hell
    (by simpa only [max_eq_left (by norm_num : (1 : ℝ) ≤ 71)] using hw)
    hroot hR hT (Real.rpow_nonneg hk0 _) hB
  have hgf : graphFactor k m=1+k := by rw [graphFactor,hm,abs_of_nonneg hk0,mul_one]
  have hB0 := G.B_nonneg
  have hT0 := G.time_nonneg
  have hR0 := G.R_pos.le
  have hf0 : 0 ≤ flowRadius G.B G.R T G.R := by unfold flowRadius; positivity
  have hrad := hn.2.2.2.1
  have hg0 := graphFactor_nonneg k m
  have hdisp : G.B*T ≤ k^(-(1/4 : ℝ)) := by
    apply (show G.B*T ≤ T*G.B*(1+flowRadius G.B G.R T G.R) by
      nlinarith [mul_nonneg (mul_nonneg hB0 hT0) hf0]).trans
    simpa only [one_mul] using hn.1
  have hvel : G.B ≤ k^(-(1/4 : ℝ)) := by
    apply (show G.B ≤ G.B*(1+flowRadius G.B G.R T G.R) by nlinarith [mul_nonneg hB0 hf0]).trans
    simpa only [one_mul] using hn.2.1
  have hRflow : G.R ≤ flowRadius G.B G.R T G.R := by
    have hleft : (1 : ℝ) ≤ 4*G.R+1 := by linarith
    have hright : G.R ≤ (1+G.B*T)*G.R+2 := by nlinarith [mul_nonneg (mul_nonneg hB0 hT0) hR0]
    have h := mul_le_mul hleft hright hR0 (by positivity : 0 ≤ 4*G.R+1)
    simpa only [one_mul,flowRadius] using h
  constructor
  · apply (G.displacement_sup_bound k m ell hell hell1 t).mono (mul_nonneg hB0 hT0) (by positivity)
    hdisp
    rw [hgf]
    apply le_trans _ hrad
    gcongr
  · apply (G.velocity_sup_bound k m ell hell hell1 t).mono hB0 (by positivity) hvel
    rw [hgf]
    apply le_trans _ hrad
    gcongr
    nlinarith

end EulerPhysicalGraphFlowBounds
