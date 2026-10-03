/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedMatrix

/-! # Iterates Terminal Flow Pairing

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem iterate_terminal_flow_commutator_pairings_bound
    {s : ℝ} (hs1 : s ≤ 1)
    {flow a b : ℝ → Vec 2 → Vec 2} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {κ D B : ℝ} (hκ : 0 < κ)
    (hQ : ∀ t i j, |Q t i j| ≤ D)
    (hG : ∀ t x i j, |gradMatrix (flow t) x i j| ≤ B)
    (ha : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (a p.1 p.2)) timeCube)
    (hb : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (b p.1 p.2)) timeCube)
    (hp₁ : IntegrableOn (fun p : ℝ × Vec 2 => vecDot (a p.1 p.2)
      ((Q p.1).mulVec ((gradMatrix (flow p.1) p.2).mulVec (b p.1 p.2)))) timeCube)
    (hp₂ : IntegrableOn (fun p : ℝ × Vec 2 => vecDot
      ((gradMatrix (flow p.1) p.2).mulVec (a p.1 p.2))
      ((Q p.1).mulVec (b p.1 p.2))) timeCube) :
    |∫ p in iterateTruncatedCell s, vecDot (a p.1 p.2)
      ((Q p.1).mulVec ((gradMatrix (flow p.1) p.2).mulVec (b p.1 p.2)))| +
    |∫ p in iterateTruncatedCell s, vecDot ((gradMatrix (flow p.1) p.2).mulVec (a p.1 p.2))
      ((Q p.1).mulVec (b p.1 p.2))| ≤
      κ / 24 * spaceTimeGradNormSq a + 384 * D ^ 2 * B ^ 2 / κ * spaceTimeGradNormSq b := by
  let A₁ := fun t x => Q t * gradMatrix (flow t) x
  let A₂ := fun t x => (gradMatrix (flow t) x).transpose * Q t
  have he₁ : (fun p : ℝ × Vec 2 => vecDot (a p.1 p.2)
      ((A₁ p.1 p.2).mulVec (b p.1 p.2))) =
      (fun p => vecDot (a p.1 p.2)
        ((Q p.1).mulVec ((gradMatrix (flow p.1) p.2).mulVec (b p.1 p.2)))) := by
    funext p
    rw [Matrix.mulVec_mulVec]
  have he₂ : (fun p : ℝ × Vec 2 => vecDot (a p.1 p.2)
      ((A₂ p.1 p.2).mulVec (b p.1 p.2))) =
      (fun p => vecDot ((gradMatrix (flow p.1) p.2).mulVec (a p.1 p.2))
        ((Q p.1).mulVec (b p.1 p.2))) := by
    funext p
    dsimp [A₂]
    simp only [vecDot, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two]
    ring
  have hi₁ : IntegrableOn (fun p : ℝ × Vec 2 => vecDot (a p.1 p.2)
      ((A₁ p.1 p.2).mulVec (b p.1 p.2))) timeCube := by rw [he₁]; exact hp₁
  have hi₂ : IntegrableOn (fun p : ℝ × Vec 2 => vecDot (a p.1 p.2)
      ((A₂ p.1 p.2).mulVec (b p.1 p.2))) timeCube := by rw [he₂]; exact hp₂
  have hρ : 0 < κ / 48 := div_pos hκ (by norm_num)
  have h₁ := iterate_truncated_matrix_pairing_bound hs1
    (A := A₁) (a := a) (b := b) hρ
    (fun t x i j => iterate_matrix_product_entry_bound _ _ (hQ t) (hG t x) i j) ha hb hi₁
  have h₂ := iterate_truncated_matrix_pairing_bound hs1
    (A := A₂) (a := a) (b := b) hρ
    (fun t x i j => iterate_matrix_product_entry_bound _ _
      (fun i j => hG t x j i) (hQ t) i j) ha hb hi₂
  rw [he₁] at h₁
  rw [he₂] at h₂
  have h := add_le_add h₁ h₂
  convert h using 1
  field_simp
  ring

end AVenhance.Infra.Section4
