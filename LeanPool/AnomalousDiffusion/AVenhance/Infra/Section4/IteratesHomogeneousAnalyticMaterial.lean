/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesScalarLaplacianEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAnalyticErrorEnergy

/-! Homogeneous material derivatives from actual analytic scalar energies. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The physical velocity-gradient scale is compared before any word or
factorial estimates; this is pure real algebra. -/
theorem iterate_material_velocity_scale {B r C κ L : ℝ}
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hC : 0 ≤ C) (hκ : 0 < κ) (hL : 0 < L)
    (hscale : B * r ≤ C * κ * L ^ 2) :
    B ^ 2 * (r / L) ^ 2 ≤ C ^ 2 * κ ^ 2 * L ^ 2 := by
  have hs := (sq_le_sq₀ (mul_nonneg hB hr) (by positivity)).mpr hscale
  calc
    _ = (B * r) ^ 2 / L ^ 2 := by ring
    _ ≤ (C * κ * L ^ 2) ^ 2 / L ^ 2 := div_le_div_of_nonneg_right hs (sq_nonneg L)
    _ = _ := by field_simp

/-- The actual homogeneous PDE bounds each material word using only actual
one-higher scalar gradients and velocity jets. No material bound is assumed. -/
theorem iterate_analytic_homogeneous_material_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ (fun _ _ => 0) u₀ u)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) (a : ℕ)
    {B G r L C : ℝ} (hB : 0 ≤ B) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hκ : 0 < κ) (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hscale : B * r ≤ C * κ * L ^ 2)
    (hjet : ∀ t x p, p ∈ (iterateSpatialSplits w).filter (fun p => decide (1 ≤ p.1.length)) → ∀ j,
      |iterateSpatialWord p.1 (fun y => b t y j) x| ≤ B * (p.1.length.factorial : ℝ) * r ^
          p.1.length)
    (hE : ∀ q : List (Fin 2), q.length ≤ w.length + 1 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord q (u t))) ≤
        G ^ 2 * (((q.length + a).factorial : ℝ) * L ^ q.length) ^ 2) :
    (∫ z in timeCube, (amnrMaterial b (fun t => iterateSpatialWord w (u t)) z.1 z.2) ^ 2) ≤
      (8 + 64 * C ^ 2) * κ ^ 2 * G ^ 2 *
        (((w.length + 1 + a).factorial : ℝ) * L ^ (w.length + 1)) ^ 2 := by
  have hmat := iterate_homogeneous_word_material_energy_bound hsol hb w
  have hLap := iterate_word_laplacian_energy_bound hsol.1 w
    (G := G * ((w.length + 1 + a).factorial : ℝ) * L ^ (w.length + 1))
    (fun k => by
      simpa only [List.length_cons, mul_pow, mul_assoc] using hE (k :: w) (by simp))
  have hErr := iterate_analytic_material_error_energy_bound hb hsol.1 w a hL hg hjet
    (fun p hp => hE p.2 (by
      have ho := iterateSpatialSplits_orders w (List.mem_filter.mp hp).1
      omega))
  have hscale' := iterate_material_velocity_scale hB hr hC hκ hL hscale
  have hfact : ((w.length + a).factorial : ℝ) ≤ ((w.length + 1 + a).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : w.length + a ≤ w.length + 1 + a)
  have hweight : L ^ 2 * (((w.length + a).factorial : ℝ) * L ^ w.length) ^ 2 ≤
      (((w.length + 1 + a).factorial : ℝ) * L ^ (w.length + 1)) ^ 2 := by
    have hf := (sq_le_sq₀ (by positivity) (by positivity)).mpr
      (mul_le_mul_of_nonneg_right hfact (by positivity : 0 ≤ L ^ w.length))
    have ht := mul_le_mul_of_nonneg_left hf (sq_nonneg L)
    convert ht using 1; simp only [pow_succ]; ring
  have h₁ := mul_le_mul_of_nonneg_right hscale'
    (by positivity : 0 ≤ 32 * G ^ 2 * (((w.length + a).factorial : ℝ) * L ^ w.length) ^ 2)
  have h₂ := mul_le_mul_of_nonneg_left hweight
    (by positivity : 0 ≤ 32 * C ^ 2 * κ ^ 2 * G ^ 2)
  have hErr' : (∫ z in timeCube, iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2)
      w (fun z => u z.1 z.2) z ^ 2) ≤
      32 * C ^ 2 * κ ^ 2 * G ^ 2 *
        (((w.length + 1 + a).factorial : ℝ) * L ^ (w.length + 1)) ^ 2 := by
    nlinarith only [hErr, h₁, h₂]
  have h₃ := mul_le_mul_of_nonneg_left hLap (by positivity : 0 ≤ 2 * κ ^ 2)
  nlinarith only [hmat, h₃, hErr']

end AVenhance.Infra.Section4
