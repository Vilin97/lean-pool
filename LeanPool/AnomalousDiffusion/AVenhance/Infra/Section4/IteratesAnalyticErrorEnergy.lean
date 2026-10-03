/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesErrorEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesPositiveFactorials

/-! Actual squared material-error energy in analytic weights. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Positive analytic velocity jets and actual lower scalar gradient energies
 control the material error square with one squared radius gain. -/
theorem iterate_analytic_material_error_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) (a : ℕ)
    {B G r L : ℝ} (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hjet : ∀ t x p, p ∈ (iterateSpatialSplits w).filter (fun p => decide (1 ≤ p.1.length)) → ∀ j,
      |iterateSpatialWord p.1 (fun y => b t y j) x| ≤ B * (p.1.length.factorial : ℝ) * r ^
          p.1.length)
    (hE : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => decide (1 ≤ p.1.length)),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (v t))) ≤
        G ^ 2 * (((p.2.length + a).factorial : ℝ) * L ^ p.2.length) ^ 2) :
    (∫ z in timeCube, iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => v z.1 z.2) z ^ 2) ≤
      32 * B ^ 2 * G ^ 2 * (r / L) ^ 2 * (((w.length + a).factorial : ℝ) * L ^ w.length) ^ 2 := by
  have ht := iterate_material_error_energy_bound hb hv w
    (fun j => B * (j.factorial : ℝ) * r ^ j)
    (fun j => G ^ 2 * (((j + a).factorial : ℝ) * L ^ j) ^ 2) hjet hE
  have he : (8 * ∑ j ∈ Finset.range (w.length + 1), if 1 ≤ j then
      (Nat.choose w.length j : ℝ) ^ 2 * (2 : ℝ) ^ j * (B * (j.factorial : ℝ) * r ^ j) ^ 2 *
        (G ^ 2 * (((w.length - j + a).factorial : ℝ) * L ^ (w.length - j)) ^ 2) else 0) =
      8 * B ^ 2 * G ^ 2 * (∑ j ∈ Finset.range (w.length + 1), if 1 ≤ j then
        (Nat.choose w.length j : ℝ) ^ 2 * (2 : ℝ) ^ j * ((j.factorial : ℝ) * r ^ j) ^ 2 *
          (((w.length - j + a).factorial : ℝ) * L ^ (w.length - j)) ^ 2 else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : 1 ≤ j
    · simp only [hj, ite_true]; ring
    · simp [hj]
  rw [he] at ht
  have hs := mul_le_mul_of_nonneg_left
    (iterate_positive_factorial_profile_sum_le w.length a hL hg)
    (by positivity : 0 ≤ 8 * B ^ 2 * G ^ 2)
  exact ht.trans (by convert hs using 1; ring)

end AVenhance.Infra.Section4
