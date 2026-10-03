/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedMatrix

/-! Exact current diffusion transfer at every actual terminal time. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- Fubini lifts the periodic Laplacian transfer to the time cell. -/
theorem iterate_truncated_laplacian_pairing_transfer
    {s : ℝ} (hs1 : s ≤ 1)
    {a b : ℝ → Vec 2 → Vec 2} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (ha : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (a t))
    (hb : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (b t))
    (hap : ∀ t, 0 < t → IsZ2Periodic (a t))
    (hbp : ∀ t, 0 < t → IsZ2Periodic (b t))
    (hL : IntegrableOn (fun p : ℝ × Vec 2 => vecDot
      (fun i => spaceLap (fun y => a p.1 y i) p.2) ((Q p.1).mulVec (b p.1 p.2))) timeCube)
    (hR : IntegrableOn (fun p : ℝ × Vec 2 => vecDot (a p.1 p.2)
      ((Q p.1).mulVec (fun j => spaceLap (fun y => b p.1 y j) p.2))) timeCube) :
    (∫ p in iterateTruncatedCell s, vecDot (fun i => spaceLap (fun y => a p.1 y i) p.2)
      ((Q p.1).mulVec (b p.1 p.2))) =
    (∫ p in iterateTruncatedCell s, vecDot (a p.1 p.2)
      ((Q p.1).mulVec (fun j => spaceLap (fun y => b p.1 y j) p.2))) := by
  have hleft := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Vec 2)))
    (fun p : ℝ × Vec 2 => vecDot (fun i => spaceLap (fun y => a p.1 y i) p.2)
      ((Q p.1).mulVec (b p.1 p.2)))
    (by simpa only [iterateTruncatedCell, Measure.volume_eq_prod] using (hL.mono_set
        (iterateTruncatedCell_subset hs1)))
  have hright := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Vec 2)))
    (fun p : ℝ × Vec 2 => vecDot (a p.1 p.2)
      ((Q p.1).mulVec (fun j => spaceLap (fun y => b p.1 y j) p.2)))
    (by simpa only [iterateTruncatedCell, Measure.volume_eq_prod] using (hR.mono_set
        (iterateTruncatedCell_subset hs1)))
  simp only [← Measure.volume_eq_prod] at hleft hright
  unfold iterateTruncatedCell
  rw [hleft, hright]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  exact iterate_vector_laplacian_pairing_transfer (ha t ht.1) (hb t ht.1)
    (hap t ht.1) (hbp t ht.1) (Q t)

/-- Transfer the current diffusion derivatives before applying Young.
Only the preceding field's Laplacian energy occurs in the remainder. -/
theorem iterate_truncated_current_diffusion_pairing_bound
    {s : ℝ} (hs1 : s ≤ 1)
    {a b : ℝ → Vec 2 → Vec 2} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {κ D E : ℝ} (hκ : 0 < κ) (hQ : ∀ t i j, |Q t i j| ≤ D)
    (ha : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (a t))
    (hb : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (b t))
    (hap : ∀ t, 0 < t → IsZ2Periodic (a t))
    (hbp : ∀ t, 0 < t → IsZ2Periodic (b t))
    (hL : IntegrableOn (fun p : ℝ × Vec 2 => vecDot
      (fun i => spaceLap (fun y => a p.1 y i) p.2) ((Q p.1).mulVec (b p.1 p.2))) timeCube)
    (hR : IntegrableOn (fun p : ℝ × Vec 2 => vecDot (a p.1 p.2)
      ((Q p.1).mulVec (fun j => spaceLap (fun y => b p.1 y j) p.2))) timeCube)
    (haI : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (a p.1 p.2)) timeCube)
    (hbI : IntegrableOn (fun p : ℝ × Vec 2 =>
      vecNormSq (fun j => spaceLap (fun y => b p.1 y j) p.2)) timeCube)
    (hprevious : spaceTimeGradNormSq (fun t x j => spaceLap (fun y => b t y j) x) ≤ E) :
    κ * |∫ p in iterateTruncatedCell s, vecDot (fun i => spaceLap (fun y => a p.1 y i) p.2)
      ((Q p.1).mulVec (b p.1 p.2))| ≤
      κ / 24 * spaceTimeGradNormSq a + 24 * κ * D ^ 2 * E := by
  rw [iterate_truncated_laplacian_pairing_transfer hs1 ha hb hap hbp hL hR]
  have h := iterate_truncated_matrix_pairing_bound hs1
    (A := fun t _x => Q t) (a := a)
    (b := fun t x j => spaceLap (fun y => b t y j) x)
    (ρ := 1 / 24) (D := D) (by norm_num)
    (fun t _x i j => hQ t i j) haI hbI hR
  have hn : D ^ 2 / (1 / (24 : ℝ)) = 24 * D ^ 2 := by ring
  rw [hn] at h
  have ht := h.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hprevious (by positivity : 0 ≤ 24 * D ^ 2)) _)
  have hfinal := mul_le_mul_of_nonneg_left ht hκ.le
  convert hfinal using 1
  ring

end AVenhance.Infra.Section4
