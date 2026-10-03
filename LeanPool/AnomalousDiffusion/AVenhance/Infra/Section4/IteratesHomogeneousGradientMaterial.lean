/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialGradientEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAnalyticErrorGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHomogeneousAnalyticMaterial

/-! # Iterates Homogeneous Gradient Material

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The homogeneous base's material-gradient energy uses two higher scalar
orders and actual velocity jets. -/
theorem iterate_homogeneous_gradient_material_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ (fun _ _ => 0) u₀ u)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) (a : ℕ)
    {B G r L C : ℝ} (hB : 0 ≤ B) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hκ : 0 < κ) (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hscale : B * r ≤ C * κ * L ^ 2)
    (hjet : ∀ t x (q : List (Fin 2)), 1 ≤ q.length → ∀ j,
      |iterateSpatialWord q (fun y => b t y j) x| ≤ B * (q.length.factorial : ℝ) * r ^ q.length)
    (hE : ∀ q : List (Fin 2), q.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord q (u t))) ≤
        G ^ 2 * (((q.length + a).factorial : ℝ) * L ^ q.length) ^ 2) :
    spaceTimeGradNormSq (fun t => spaceGrad
      (amnrMaterial b (fun s => iterateSpatialWord w (u s)) t)) ≤
      (8 + 544 * C ^ 2) * κ ^ 2 * G ^ 2 *
        (((w.length + 2 + a).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 := by
  have hz : (fun z : AmnrSpace => spaceGrad (iterateSpatialWord w (fun _ : Vec 2 => (0 : ℝ))) z.2) =
      fun _ => (0 : Vec 2) := by
    ext z j
    simp only [iterateSpatialWord_zero]
    unfold spaceGrad
    simp
  have hFc : ContinuousOn (fun z : AmnrSpace =>
      spaceGrad (iterateSpatialWord w (fun _ : Vec 2 => (0 : ℝ))) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by rw [hz]; exact continuousOn_const
  have hm := iterate_commuted_material_gradient_energy_bound hsol hb w hFc
  have hzero : spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord w (fun _ : Vec 2 => (0 : ℝ)))) = 0 := by
    unfold spaceTimeGradNormSq
    have hzpoint (t : ℝ) (x : Vec 2) := congrFun hz (t, x)
    simp_rw [hzpoint]
    simp [vecNormSq, vecDot]
  rw [hzero, mul_zero, add_zero] at hm
  have hl := iterate_word_laplacian_gradient_energy_bound hsol.1 w
    (G := G * ((w.length + 2 + a).factorial : ℝ) * L ^ (w.length + 2))
    (fun k => by
      simpa only [List.length_cons, Nat.add_assoc, Nat.reduceAdd, mul_pow, mul_assoc]
        using hE (k :: k :: w) (by simp only [List.length_cons]; omega))
  have he := iterate_analytic_material_error_gradient_energy_bound hb hsol.1 w a hL hg hjet
    (fun q hq => hE q (by omega))
  have hs := (sq_le_sq₀ (mul_nonneg hB hr) (by positivity)).mpr hscale
  have hf : ((w.length + 1 + a).factorial : ℝ) ≤ ((w.length + 2 + a).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : w.length + 1 + a ≤ w.length + 2 + a)
  have hw : L ^ 4 * (((w.length + 1 + a).factorial : ℝ) * L ^ w.length) ^ 2 ≤
      (((w.length + 2 + a).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 := by
    have ht := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (by positivity) (by positivity)).mpr
        (mul_le_mul_of_nonneg_right hf (by positivity : 0 ≤ L ^ w.length)))
      (by positivity : 0 ≤ L ^ 4)
    convert ht using 1; simp only [pow_add]; ring
  have h₁ := mul_le_mul_of_nonneg_right hs
    (by positivity : 0 ≤ 136 * G ^ 2 * (((w.length + 1 + a).factorial : ℝ) * L ^ w.length) ^ 2)
  have h₂ := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 136 * C ^ 2 * κ ^ 2 * G ^ 2)
  have he' : spaceTimeGradNormSq (fun t x => spaceGrad (fun y => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => u z.1 z.2) (t, y)) x) ≤
      136 * C ^ 2 * κ ^ 2 * G ^ 2 *
        (((w.length + 2 + a).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 := by
    nlinarith only [he, h₁, h₂]
  have h₃ := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 * κ ^ 2)
  have h₄ := mul_le_mul_of_nonneg_left he' (by norm_num : (0 : ℝ) ≤ 4)
  nlinarith only [hm, h₃, h₄]

end AVenhance.Infra.Section4
