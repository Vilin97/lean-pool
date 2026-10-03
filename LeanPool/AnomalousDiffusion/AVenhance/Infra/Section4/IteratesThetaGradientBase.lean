/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesThetaSourceBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoordinateProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAnalyticRadiusDoubling

/-! # Iterates Theta Gradient Base

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- An abstract-amplitude theta base for both normalizations. The zeroth-order
input is exclusively its integrated gradient, never its scalar supremum. -/
theorem iterate_theta_gradient_base_profile {κ : ℝ}
    {u : ℝ → Vec 2 → ℝ} {B l L : ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hκ : 0 < κ) (hB : 0 ≤ B) (hl : 0 ≤ l) (hL : 4 * l ≤ L)
    (hzero : κ * spaceTimeGradNormSq (fun t => spaceGrad (u t)) ≤ B ^ 2)
    (hsource : ∀ v w : List (Fin 2), 1 ≤ v.length → w.length = v.length + 1 →
      ∀ s, 0 ≤ s → s ≤ 1 →
      Real.sqrt (l2NormSq (iterateSpatialWord v (u s))) + Real.sqrt κ *
        Real.sqrt (∫ z in timeCube, (iterateSpatialWord w (u z.1) z.2) ^ 2) ≤
      2 * B * (v.length.factorial : ℝ) * l ^ v.length) :
    iterateCoordinateEnergyProfile u κ B L 0 := by
  have hL0 : 0 ≤ L := (by positivity : 0 ≤ 4 * l).trans hL
  have he (w : List (Fin 2)) (s : ℝ) : 0 ≤ l2NormSq (iterateSpatialWord w (u s)) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have henergy (v : List (Fin 2)) (hv : 1 ≤ v.length) (j : Fin 2) :
      κ * (∫ z in timeCube, (iterateSpatialWord (j :: v) (u z.1) z.2) ^ 2) ≤
        (2 * B * (v.length.factorial : ℝ) * l ^ v.length) ^ 2 := by
    exact (iterate_norm_le_energy_components (he v 0)
      (integral_nonneg (fun _ => sq_nonneg _)) hκ.le (by positivity)
      (hsource v (j :: v) hv (by simp) 0 (by norm_num) (by norm_num))).2
  have hgrad (v : List (Fin 2)) (hv : 1 ≤ v.length) : κ * spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord v (u t))) ≤
      8 * B ^ 2 * ((v.length.factorial : ℝ) * l ^ v.length) ^ 2 := by
    have hi (j : Fin 2) : IntegrableOn
        (fun z : AmnrSpace => spaceGrad (iterateSpatialWord v (u z.1)) z.2 j ^ 2) timeCube := by
      exact iterate_timeCube_integrable_of_continuousOn
        (((continuous_apply j).comp_continuousOn
          (iterate_word_gradient_smooth_up_to_initial hu v).continuousOn).pow 2)
    have heq : κ * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord v (u t))) =
        κ * (∫ z in timeCube, (iterateSpatialWord (0 :: v) (u z.1) z.2) ^ 2) +
        κ * (∫ z in timeCube, (iterateSpatialWord (1 :: v) (u z.1) z.2) ^ 2) := by
      unfold spaceTimeGradNormSq vecNormSq vecDot
      simp only [Fin.sum_univ_two, ← pow_two]
      rw [integral_add (hi 0) (hi 1)]
      simp only [iterateSpatialWord]
      ring
    have h0 := henergy v hv 0
    have h1 := henergy v hv 1
    rw [heq]
    nlinarith only [h0, h1]
  constructor
  · intro v hv s hs hs1
    have hvp : 1 ≤ v.length := hv.resolve_right (by omega)
    have hb := (iterate_norm_le_energy_components (he v s)
      (integral_nonneg (fun _ => sq_nonneg _)) hκ.le (by positivity)
      (hsource v (0 :: v) hvp (by simp) s hs hs1)).1
    have hp := iterate_positive_order_radius_four hl hL hvp
    have hw := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg v.length.factorial)
    have hsquare := (sq_le_sq₀ (by positivity) (by positivity)).mpr hw
    have hm := mul_le_mul_of_nonneg_left hsquare (sq_nonneg B)
    have hz : 0 ≤ B ^ 2 * ((v.length.factorial : ℝ) * l ^ v.length) ^ 2 := by positivity
    simp only [iterateAnalyticWeight, Nat.mul_zero, Nat.add_zero]
    nlinarith only [hb, hm, hz]
  · intro v
    apply le_of_mul_le_mul_left (a := κ) _ hκ
    rw [← mul_assoc, iterate_diffusive_gradient_normalization hκ]
    by_cases hv : v = []
    · subst v
      have hb := hzero
      simp only [iterateAnalyticWeight, List.length_nil, Nat.mul_zero, Nat.add_zero,
        Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one, iterateSpatialWord]
      nlinarith only [hb, sq_nonneg B]
    · have hn : 1 ≤ v.length := by have ht := List.length_pos_iff.mpr hv; omega
      have hp := iterate_positive_order_radius_four hl hL hn
      have hw : 4 * ((v.length.factorial : ℝ) * l ^ v.length) ≤
          (v.length.factorial : ℝ) * L ^ v.length := by
        have ht := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg v.length.factorial)
        convert ht using 1
        ring
      have hsq : 16 * ((v.length.factorial : ℝ) * l ^ v.length) ^ 2 ≤
          ((v.length.factorial : ℝ) * L ^ v.length) ^ 2 := by
        have h0 : 0 ≤ (v.length.factorial : ℝ) * l ^ v.length := by positivity
        have h1 : 0 ≤ (v.length.factorial : ℝ) * L ^ v.length := by positivity
        nlinarith only [hw, h0, h1]
      have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg B)
      have hb := hgrad v hn
      have h0 : 0 ≤ B ^ 2 * ((v.length.factorial : ℝ) * L ^ v.length) ^ 2 := by positivity
      simp only [iterateAnalyticWeight, Nat.mul_zero, Nat.add_zero]
      nlinarith only [hm, hb, h0]

end AVenhance.Infra.Section4
