/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureMaterialStepL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateFluxJets

/-! One actual material gradient step from spatial orders at most two. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set AVenhance
open AVenhance.Infra.Section4
namespace AVenhance.Infra.Section5.Contracts

theorem TMaterialSpatialStep.weight_spatial (L H : ℝ) (α : List (Fin 2)) :
    amnrWeight L H (α.map some) = L ^ α.length := by
  simpa only [amnrMixedWord, List.replicate_zero, List.append_nil, pow_zero, mul_one]
    using amnrMixedWord_weight L H α 0

/-- Step constant for spatial derivatives of the temperature material coefficient. -/
def tMaterialSpatialStepConstant (Cb CA Cd : ℝ) : ℝ :=
  2 * (amnrNormalOrderConstant 2 Cb 2 * (amnrCanonicalSamples 2 2).card) *
    (1 + 8 * CA) * Cd + 8 * Cb

/-- The local budget is exactly two. No positive material coefficient or
velocity-gradient derivative is among the hypotheses. -/
theorem tMaterial_component_of_spatial_profiles {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    {κm ν : ℝ} (hκm : 0 < κm) (hν : 0 < ν)
    {g : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) ν (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κm ν g θprev T)
    {L G CA Cb Cd : ℝ} (hL : 0 < L) (hG : 0 ≤ G)
    (hCA : 0 ≤ CA) (hCb : 0 ≤ Cb)
    (hRate : ν * L ^ 2 ≤ Cd * a β I.Λ (m - 1))
    (hCoefficient : ∀ j p (α : List (Fin 2)), α.length ≤ 2 → ∀ z,
      |amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2) (α.map some)
        (amnrTemperatureCoefficient I hΦ m κm ν j p) z| ≤ CA * ν * L ^ α.length)
    (hVelocity : ∀ q p z, |amnrVelocityGradient
      (fun y => streamVel (Φ (m - 1)) y.1 y.2) q p z| ≤ Cb * a β I.Λ (m - 1))
    (hSpatial : ∀ i, i ≤ Nstar β → ∀ p (α : List (Fin 2)), α.length ≤ 2 →
      eLpNorm (amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
        (α.map some) (amnrTGradient (T i) p)) 2 (volume.restrict timeCube) ≤
        ENNReal.ofReal (G * L ^ α.length)) (p : Fin 2) :
    eLpNorm (amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2) [none]
      (amnrTGradient (T (Nstar β)) p)) 2 (volume.restrict timeCube) ≤
      ENNReal.ofReal (tMaterialSpatialStepConstant Cb CA Cd * a β I.Λ (m - 1) * G) := by
  let b : AmnrSpace → Vec 2 := fun y => streamVel (Φ (m - 1)) y.1 y.2
  let U : Set AmnrSpace := Ioi (0 : ℝ) ×ˢ univ
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hμ : volume.restrict timeCube ≪ volume.restrict U :=
    Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set volume (by
      intro z hz; exact ⟨hz.1.1, mem_univ _⟩))
  have hN : 2 ≤ Nstar β := by
    have := Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt; omega
  have ha : 0 < a β I.Λ (m - 1) :=
    Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
    contDiff_infty.mpr (fun n => amnr_previous_velocity_contDiff I hΦ hm n)
  have hflux : ∀ q (α : List (Fin 2)), α.length ≤ 2 →
      eLpNorm (amnrWord b (α.map some) (amnrIterateFlux I hΦ m κm ν T (Nstar β) q)) 2
        (volume.restrict timeCube) ≤ ENNReal.ofReal (8 * (CA * ν) * G * L ^ α.length) := by
    intro q α hα
    have hpos : Nstar β ≠ 0 := by omega
    simp only [amnrIterateFlux, ite_eq_right hpos]
    have hh := amnrWord_sum_mul_L2_le (M := 2) (N := 2) hU hμ le_rfl
      (hb.of_le (by simp)).contDiffOn
      (fun j => (amnr_temperatureCoefficient_contDiff I hΦ hm hκm ν q j).of_le
        (by exact_mod_cast hN) |>.contDiffOn)
      (fun j => (amnr_tIterates_gradient_smooth I hΦ hθ hT (Nstar β - 1) (by omega) j).of_le (by
          simp))
      hL.le ha.le (mul_nonneg hCA hν.le) hG
      (amnrMixedWord α 0) (by rw [amnrMixedWord_budget]; omega)
      (fun j v hv z _ => by
        obtain ⟨η, r, rfl, hr, hbud⟩ := amnrMixedWord_subword_normalForm hv
        have hr0 : r = 0 := by omega
        subst r
        simpa only [amnrMixedWord, List.replicate_zero, List.append_nil,
          amnrMixedWord_weight, TMaterialSpatialStep.weight_spatial, pow_zero, mul_one] using
              hCoefficient q j η (by omega) z)
      (fun j v hv => by
        obtain ⟨η, r, rfl, hr, hbud⟩ := amnrMixedWord_subword_normalForm hv
        have hr0 : r = 0 := by omega
        subst r
        simpa only [amnrMixedWord_weight, pow_zero, mul_one,
          amnrMixedWord, List.replicate_zero, List.append_nil,
              TMaterialSpatialStep.weight_spatial] using
          hSpatial (Nstar β - 1) (by omega) j η (by omega))
    unfold amnrTemperatureFlux
    simpa only [amnrMixedWord_weight, pow_zero, mul_one, amnrMixedWord,
      List.replicate_zero, List.append_nil, TMaterialSpatialStep.weight_spatial, show (2 : ℝ) ^ (2
          + 1) = 8 by norm_num] using hh
  have hstep := amnr_gradient_material_step_L2 (N := 2) (r := 0) (H := a β I.Λ (m - 1)) hU hμ hb
    (amnr_tIterates_gradient_smooth I hΦ hθ hT (Nstar β) le_rfl)
    (fun q => (amnr_tIterates_flux_smooth I hΦ hm hκm hθ hT (Nstar β) le_rfl q).of_le
      (by exact_mod_cast hN)) hν.le hL
    ha hG
    (by positivity : 0 ≤ 8 * (CA * ν) * G) hCb
    (fun q α n hbudget hn => by
      have hn0 : n = 0 := by omega
      subst n
      simpa only [amnrMixedWord_weight, pow_zero, mul_one,
        amnrMixedWord, List.replicate_zero, List.append_nil, TMaterialSpatialStep.weight_spatial]
            using
        hSpatial (Nstar β) le_rfl q α (by omega))
    (fun q α n hbudget hn => by
      have hn0 : n = 0 := by omega
      subst n
      simpa only [amnrMixedWord_weight, pow_zero, mul_one,
        amnrMixedWord, List.replicate_zero, List.append_nil, TMaterialSpatialStep.weight_spatial]
            using hflux q α (by omega))
    (fun q j α n hbudget z _ => by
      have hn0 : n = 0 := by omega
      have hα0 : α = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst n; subst α
      simpa only [amnrMixedWord, List.map_nil, List.replicate_zero, List.append_nil,
        amnrWord, amnrWeight, List.prod_nil, List.map_nil, mul_one] using hVelocity q j z)
    p (amnr_tIterates_gradient_pde I hΦ hm hκm hθ hT (Nstar β) le_rfl p) [] (by simp)
  refine hstep.trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [amnrMixedWord, List.map_nil, List.replicate_zero, List.append_nil,
    amnrWeight, List.map_nil, List.prod_nil, mul_one] at *
  have hK : 0 ≤ amnrNormalOrderConstant 2 Cb 2 * (amnrCanonicalSamples 2 2).card :=
    mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (amnrNormalOrderConstant_one_le hCb 2))
        (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hRate
    (show 0 ≤ 2 * (amnrNormalOrderConstant 2 Cb 2 * (amnrCanonicalSamples 2 2).card) * (1 + 8 *
        CA) * G by positivity)
  dsimp [tMaterialSpatialStepConstant]
  convert add_le_add_right hh (8 * Cb * a β I.Λ (m - 1) * G) using 1 <;> ring

end AVenhance.Infra.Section5.Contracts
