/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedVelocityEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesLinearFactorials

/-! The actual material commutator in analytic norm weights. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Analytic velocity jets and strictly lower scalar gradient energies give
 the geometric linear norm recurrence for the actual material error. -/
theorem iterate_terminal_analytic_material_error_bound
    {s : ℝ} (hs1 : s ≤ 1)
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ} {a : AmnrSpace → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (ha : ContinuousOn a (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) (i : ℕ) {B H G r L : ℝ}
    (hB : 0 ≤ B) (hH : 0 ≤ H) (hG : 0 ≤ G) (hr : 0 ≤ r)
    (hL : 0 < L) (hgain : r / L ≤ 1 / 2)
    (D : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n)
    (hjet : ∀ t x p, p ∈ (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty) → ∀ j,
      |iterateSpatialWord p.1 (fun y => b t y j) x| ≤
        B * (p.1.length.factorial : ℝ) * r ^ p.1.length)
    (hEa : (∫ z in timeCube, a z ^ 2) ≤
      (H * ((w.length + 2 * i - 1).factorial : ℝ) * L ^ (w.length + 1)) ^ 2)
    (hEv : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (v t))) ≤
        (G * ((p.2.length + 2 * i).factorial : ℝ) * L ^ p.2.length * D p.2.length) ^ 2) :
    |∫ z in iterateTruncatedCell s, a z * iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => v z.1 z.2) z| ≤
      2 * H * B * G * r * (((w.length + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2 *
        ∑ k ∈ Finset.range w.length, (1 / (2 : ℝ)) ^ k * D (w.length - 1 - k) := by
  have ht := iterate_truncated_material_error_linear_energy_bound hs1 hb hv ha w
    (fun j => B * (j.factorial : ℝ) * r ^ j)
    (fun j => G * ((j + 2 * i).factorial : ℝ) * L ^ j * D j)
    (fun _ => by positivity) (fun j => by have hd := hD j; positivity)
    (by positivity : 0 ≤ H * ((w.length + 2 * i - 1).factorial : ℝ) * L ^ (w.length + 1))
    hjet hEa hEv
  have hs := iterate_linear_material_series_le w.length i hr hL hgain D hD
  calc
    _ ≤ _ := ht
    _ = (2 * H * B * G) * (∑ k ∈ Finset.range w.length,
        (Nat.choose w.length (k + 1) : ℝ) * (((k + 1).factorial : ℝ) * r ^ (k + 1)) *
          (((w.length - (k + 1) + 2 * i).factorial : ℝ) * L ^ (w.length - (k + 1))) *
          (((w.length + 2 * i - 1).factorial : ℝ) * L ^ (w.length + 1)) *
          D (w.length - (k + 1))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * H * B * G)
      simpa only [mul_assoc] using hm

end AVenhance.Infra.Section4
