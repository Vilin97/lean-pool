/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureMaterialRate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateFluxJets

/-! Material induction simultaneously across the actual temperature family. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Primitive coefficient jets and proved spatial gradient jets imply all
material levels. Every flux consumes only a strictly lower material level,
including when its preceding iterate has a larger construction index. -/
theorem amnr_tIterates_material_gradient_induction {β : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    {κm κprev : ℝ} (hκm : 0 < κm) (hκprev : 0 < κprev) {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : AVenhance.IsClassicalSol (AVenhance.streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict (Ioi (0 : ℝ) ×ˢ univ))
    {S H G Ccoeff Cb Cd : ℝ} (hS : 0 < S) (hH : 0 < H) (hG : 0 ≤ G)
    (hC : 0 ≤ Ccoeff) (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd)
    (hRate : κprev * S ^ 2 ≤ Cd * H)
    (hAb : ∀ j p w, IsAmnrMixedWord w → amnrBudget w ≤ AVenhance.Nstar β → ∀ z,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
        (amnrTemperatureCoefficient I hΦ m κm κprev j p) z| ≤
          (Ccoeff * κprev) * amnrWeight S H w)
    (hBb : ∀ q p α n, α.length + 2 * n + 2 ≤ AVenhance.Nstar β → ∀ z,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord α n) (amnrVelocityGradient
          (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) q p) z| ≤
        (Cb * H) * amnrWeight S H (amnrMixedWord α n))
    (hbase : ∀ i, i ≤ AVenhance.Nstar β → ∀ (p : Fin 2) (α : List (Fin 2)), α.length ≤
        AVenhance.Nstar β →
      eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (α.map some) (amnrTGradient (T i) p)) 2 μ ≤ ENNReal.ofReal (G * S ^ α.length)) :
    let N := AVenhance.Nstar β
    let K := amnrNormalOrderConstant N Cb N * (amnrCanonicalSamples N N).card
    let R := 1 + 2 * Cd * K * (1 + (2 : ℝ) ^ (N + 1) * Ccoeff) + (2 : ℝ) ^ (N + 1) * Cb
    ∀ r i, i ≤ N → ∀ (p : Fin 2) (α : List (Fin 2)), α.length + 2 * r ≤ N →
      eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord α r) (amnrTGradient (T i) p)) 2 μ ≤
          ENNReal.ofReal (R ^ r * G * amnrWeight S H (amnrMixedWord α r)) := by
  intro N K R
  let b := fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2
  have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
    contDiff_infty.mpr (fun n => amnr_previous_velocity_contDiff I hΦ hm n)
  have hK : 0 ≤ K := mul_nonneg
    (le_trans (by norm_num) (amnrNormalOrderConstant_one_le hCb N)) (Nat.cast_nonneg _)
  have hR : 1 ≤ R := by
    have hh : 0 ≤ 2 * Cd * K * (1 + (2 : ℝ) ^ (N + 1) * Ccoeff) := by positivity
    have hh' : 0 ≤ (2 : ℝ) ^ (N + 1) * Cb := by positivity
    dsimp only [R]
    linarith only [hh, hh']
  have hRn : 0 ≤ R := le_trans (by norm_num) hR
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro i hi p α hbudget
    cases r with
    | zero =>
      simpa only [amnrMixedWord, List.replicate_zero, List.append_nil, pow_zero, one_mul,
        amnrWeight, List.map_map, Function.comp_def, List.prod_replicate,
        List.map_const', List.length_map] using hbase i hi p α (by omega)
    | succ r =>
      have hLower : ∀ j, j ≤ N → ∀ q η s, η.length + 2 * s ≤ N → s ≤ r →
          eLpNorm (amnrWord b (amnrMixedWord η s) (amnrTGradient (T j) q)) 2 μ ≤
            ENNReal.ofReal ((R ^ r * G) * amnrWeight S H (amnrMixedWord η s)) := by
        intro j hj q η s hbud hs
        refine (ih s (by omega) j hj q η hbud).trans (ENNReal.ofReal_le_ofReal ?_)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hR hs) hG) (amnrWeight_nonneg hS.le hH.le _)
      have hRG : 0 ≤ R ^ r * G := mul_nonneg (pow_nonneg hRn _) hG
      have hFlux := amnr_tIterates_flux_mixed_bound_of_lower_gradients I hΦ hm hκm
        hθprev hT hμ hS.le hH.le (mul_nonneg hC hκprev.le) hRG hAb hLower i hi
      have hh := amnr_gradient_material_step_L2 (isOpen_Ioi.prod isOpen_univ) hμ hb
        (amnr_tIterates_gradient_smooth I hΦ hθprev hT i hi)
        (amnr_tIterates_flux_smooth I hΦ hm hκm hθprev hT i hi)
        hκprev.le hS hH hRG
        (show 0 ≤ (2 : ℝ) ^ (N + 1) * (Ccoeff * κprev) * (R ^ r * G) by positivity)
        hCb (hLower i hi) hFlux (fun q p η s hbud z _ => hBb q p η s hbud z) p
        (amnr_tIterates_gradient_pde I hΦ hm hκm hθprev hT i hi p) α hbudget
      refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
      have hnorm := amnr_material_gradient_rate_le (Cb := Cb) hK hRG hC hCd
        (show 0 ≤ (2 : ℝ) ^ (N + 1) by positivity)
        (amnrWeight_nonneg hS.le hH.le (amnrMixedWord α r)) hH.le hRate
      convert hnorm using 1
      · dsimp [K]
        ring
      · rw [amnrMixedWord_weight, amnrMixedWord_weight, pow_succ, pow_succ]
        dsimp [R, K]
        ring

end AVenhance.Infra.Section4
