/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TMaterialProfiles
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TMaterialSpatialCoefficient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SourceJetLevels
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureDiffusionRates

/-! Uniform minimal material estimate from the abstract-amplitude theta profile. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory AVenhance
open AVenhance.Infra.Section4 AVenhance.Infra.Section5.RelativeError
open AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.Contracts

/-- All source inputs of the first material step are discharged. The only
remaining temperature input is the independently owned theta profile. The
radius may be enlarged before the instance is selected. -/
theorem tMaterial_of_thetaProfile_contract (β Ccut CsReq : ℝ) (hReq : 1 ≤ CsReq) :
    ∃ Cs A C₁ : ℝ, CsReq ≤ Cs ∧ 0 ≤ A ∧
      OnA7Instances β Ccut C₁ (fun I Φ _hΦ κ M _R _θ₀ m θprev T =>
        ∀ S : ℝ, 0 ≤ S → ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs S →
          TMaterialContract I Φ m (I.kappaSeq κ M (m - 1)) T A S) := by
  obtain ⟨cv, Cv, hcv, hcvC, hv⟩ := iterate_V_upgrade_of_theta β Ccut
  obtain ⟨c, Ck, hc, hcC, hrec⟩ := AVenhance.l_recurse β Ccut
  obtain ⟨_, _, hreg⟩ := AVenhance.stream_regularity β
  let Cs := max CsReq (iterateReducedSourceConstant β Ccut cv Cv 40 (2 ^ 10) 1)
  have hReqCs : CsReq ≤ Cs := le_max_left _ _
  have hSrc : iterateReducedSourceConstant β Ccut cv Cv 40 (2 ^ 10) 1 ≤ Cs := le_max_right _ _
  have hCs : 1 ≤ Cs := hReq.trans hReqCs
  have hCspos : 0 < Cs := zero_lt_one.trans_le hCs
  obtain ⟨Cg, hCg, Λj, hj⟩ := relative_iterate_gradient_jets β Cs hCspos
  let D := max Cs (iterateDischargeThreshold β Ccut Ck)
  have hD : 1 ≤ D := hCs.trans (le_max_left _ _)
  obtain ⟨Λs, hs⟩ := iterate_contract_scales β D hD
  let CL := max (max Cs 1) (2 ^ 10)
  let Cb := max 1 (amnrSpatialVelocityConstant (Nstar β))
  let Q := max 0 (iterateKmatConstant β Ccut)
  let CA := 200000 * (Q + 1)
  let Cd := Ck * CL ^ 2
  let Cstep := tMaterialSpatialStepConstant Cb CA Cd
  let Cr := 2 * Real.sqrt 2 * Cstep * Cg
  refine ⟨Cs, Cr * (2 : ℝ) ^ (-27 : ℤ), max Λj Λs, hReqCs, ?_, ?_⟩
  · have hCk : 0 ≤ Ck := (hc.trans hcC).le
    have hQ : 0 ≤ Q := le_max_left _ _
    have hCb : 0 ≤ Cb := zero_le_one.trans (le_max_left _ _)
    have hCA : 0 ≤ CA := by dsimp [CA]; positivity
    have hCd : 0 ≤ Cd := by dsimp [Cd]; positivity
    have hn : 0 ≤ amnrNormalOrderConstant 2 Cb 2 :=
      zero_le_one.trans (amnrNormalOrderConstant_one_le hCb 2)
    dsimp [Cr, Cstep, tMaterialSpatialStepConstant]
    positivity
  · intro I hz hx hh hΛ Φ hΦ κ hset M hM hperm R hR θ₀ hsm hp hmz ha m hm hmM θprev T hθ hT S hS
      hbase
    have hκ : 0 < κ := (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
          _)).trans_le hperm.1
    have hκm : 0 < I.kappaSeq κ M m := Infra.Section3.kappaAt_pos I hκ m (M - m)
    have hν : 0 < I.kappaSeq κ M (m - 1) := Infra.Section3.kappaAt_pos I hκ (m - 1) (M - (m - 1))
    have hscale := hs I ((le_max_right _ _).trans hΛ) R hR m hm
    obtain ⟨hm2, hradius, hsmallD⟩ := hscale
    have hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * Cs ^ 3)⁻¹ :=
      hsmallD.trans ((inv_le_inv₀ (by positivity) (by positivity)).mpr
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hCspos.le (le_max_left _ _) 3) (by norm_num)))
    have hV := hv I hz hx hh hΦ κ M hT hθ hm2 hmM hperm 1 R Cs S hS hR hSrc hradius hsmall hbase
    have hjet := hj I ((le_max_left _ _).trans hΛ) Φ hΦ κ M m hm2 θ₀ θprev T hκm hν hθ hT
      S R hS hradius hbase hV
    have hA5 := hrec I hz hx hh κ hset M hM hperm
    have hinputs := iterate_chain_upgrade_inputs I hz hh hm2 hmM hκ hperm (hc.trans hcC).le
      hD (le_max_right _ _) hsmallD (fun j hj hjM => (hA5.2 j hj hjM).2)
    have hQ : 0 ≤ Q := le_max_left _ _
    have hCb : 0 ≤ Cb := zero_le_one.trans (le_max_left _ _)
    have hCA : 0 ≤ CA := by dsimp [CA]; positivity
    have hCd : 0 ≤ Cd := by dsimp [Cd]; exact mul_nonneg (hc.trans hcC).le (sq_nonneg _)
    have hn : 0 ≤ amnrNormalOrderConstant 2 Cb 2 := zero_le_one.trans
        (amnrNormalOrderConstant_one_le hCb 2)
    have hCr : 0 ≤ Cr := by dsimp [Cr, Cstep, tMaterialSpatialStepConstant]; positivity
    have he : 0 < epsilon β I.Λ (m - 1) := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le
    let L₀ := epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))
    let L := CL * L₀
    let G := Cg * (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ * S
    have hCL : 0 < CL := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 ^ 10) (le_max_right _ _)
    have hL₀ : 0 < L₀ := Real.rpow_pos_of_pos he _
    have hL : 0 < L := mul_pos hCL hL₀
    have hG : 0 ≤ G := by dsimp [G]; positivity
    have hfreq : 2 ^ 10 / epsilon β I.Λ (m - 1) ≤ L := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (le_max_right _ _) (amnr_physical_rates I (by omega)).1
        (inv_nonneg.mpr he.le) hCL.le
    have hRate₀ := amnr_diffusion_rate_le he (hA5.1 (m - 1) (by omega) (by omega)).2 le_rfl
        (hc.trans hcC).le
    have hRate : I.kappaSeq κ M (m - 1) * L ^ 2 ≤ Cd * a β I.Λ (m - 1) := by
      have hb := mul_le_mul_of_nonneg_right hRate₀ (sq_nonneg CL)
      convert hb using 1 <;> dsimp [L, L₀, Cd, Ingredients.kappaSeq] <;> ring
    have hCoefficient := tMaterial_coefficient_spatial_two I hΦ hm2 hκm hν.le hQ hL
      (iterate_kappaSeq_abs_le_previous I hκ (by omega) hmM) hfreq (fun t i j => (hinputs.1 t i
          j).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hν.le))
    have hVelocity : ∀ q p z, |amnrVelocityGradient (fun y => streamVel (Φ (m - 1)) y.1 y.2) q p
        z| ≤ Cb * a β I.Λ (m - 1) := by
      intro q p z
      have hb := (amnrSourceJetLevels_spatial I hΦ (hreg I Φ hΦ)).gradient
        (m - 1) [] 0 le_rfl (by
          have hN := Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
          simp
          omega) q p z
      simpa only [amnrMixedWord, List.map_nil, List.replicate_zero, List.append_nil,
        amnrWord, List.length_nil, pow_zero, mul_one] using hb
    have hSpatial : ∀ i, i ≤ Nstar β → ∀ p (α : List (Fin 2)), α.length ≤ 2 →
        eLpNorm (amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
          (α.map some) (amnrTGradient (T i) p)) 2 (volume.restrict timeCube) ≤ ENNReal.ofReal (G *
              L ^ α.length) := by
      intro i hi p α hα
      have hN : α.length ≤ Nstar β := by
        have hstar := Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
        omega
      have hb := hjet i hi p α hN
      rw [amnr_product_measure_eq_timeCube] at hb
      apply hb.trans
      apply ENNReal.ofReal_le_ofReal
      rw [div_eq_mul_inv]
      have hpow := pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans (le_max_right Cs 1)) hL₀.le)
        (mul_le_mul_of_nonneg_right (show max Cs 1 ≤ CL from le_max_left _ _) hL₀.le) α.length
      convert mul_le_mul_of_nonneg_left hpow hG using 1
      dsimp [G, L, L₀]
      ring
    have hmaterial := tMaterial_rate_profile_of_spatial_profiles I hΦ (by omega) hκm hν hθ hT
      hL hG hCA hCb hCd (le_refl G) hRate hCoefficient hVelocity hSpatial
    exact tMaterial_contract_of_material_rate I (by omega) hS hCr hmaterial

end AVenhance.Infra.Section5.Contracts
