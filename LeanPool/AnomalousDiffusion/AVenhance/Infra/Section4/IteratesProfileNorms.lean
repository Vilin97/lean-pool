/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoordinateProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesIndependentCoordinateNorms

/-! # Iterates Profile Norms

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

/-- Every gradient word is controlled, including the gradient-only base at zero. -/
theorem iterate_profile_gradient_norm {u : ℝ → Vec 2 → ℝ} {κ N L : ℝ} {i : ℕ}
    (hκ : 0 < κ) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hp : iterateCoordinateEnergyProfile u κ N L i) (w : List (Fin 2)) :
    Real.sqrt κ * Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u
        t)))) ≤
      N * iterateAnalyticWeight w.length i L := by
  have hg : 0 ≤ spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) := by
    apply integral_nonneg
    intro z
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hb := mul_le_mul_of_nonneg_left (hp.2 w) hκ.le
  rw [← mul_assoc, iterate_diffusive_gradient_normalization hκ] at hb
  apply (sq_le_sq₀ (by positivity) (mul_nonneg hN (iterateAnalyticWeight_nonneg _ _ hL))).mp
  rw [mul_pow, Real.sq_sqrt hκ.le, Real.sq_sqrt hg, mul_pow]
  exact hb

/-- Mixed profile norms are used only at positive scalar order in the base. -/
theorem iterate_profile_mixed_norm {u : ℝ → Vec 2 → ℝ} {κ N L : ℝ} {i : ℕ}
    (hκ : 0 < κ) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hp : iterateCoordinateEnergyProfile u κ N L i) (v w : List (Fin 2))
    (hvw : v.length = w.length) (hv : 1 ≤ v.length ∨ 1 ≤ i)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.sqrt (l2NormSq (iterateSpatialWord v (u s))) + Real.sqrt κ *
      Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t)))) ≤
      2 * N * iterateAnalyticWeight v.length i L := by
  have he := hp.1 v hv s hs hs1
  have hscalar : Real.sqrt (l2NormSq (iterateSpatialWord v (u s))) ≤
      N * iterateAnalyticWeight v.length i L := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨mul_nonneg hN (iterateAnalyticWeight_nonneg _ _ hL), by simpa only [mul_pow] using he⟩
  have hgrad := iterate_profile_gradient_norm hκ hN hL hp w
  rw [← hvw] at hgrad
  calc
    _ ≤ N * iterateAnalyticWeight v.length i L + N * iterateAnalyticWeight v.length i L :=
      add_le_add hscalar hgrad
    _ = _ := by ring

end AVenhance.Infra.Section4
