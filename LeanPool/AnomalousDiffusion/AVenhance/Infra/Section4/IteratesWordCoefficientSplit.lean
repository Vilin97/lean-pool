/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordSplitPrincipal

/-! The literal time-only K coefficient and the spatial flow correction
remain separate in every differentiated forcing. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- Positive-order spatial words annihilate a spatial constant. -/
theorem iterateSpatialWord_const (c : ℝ) (w : List (Fin 2)) :
    iterateSpatialWord w (fun _ : Vec 2 => c) =
      fun _ => if w = [] then c else 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [iterateSpatialWord, ih, List.cons_ne_nil, ↓reduceIte]
    funext x
    unfold spaceGrad
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply]

/-- A spatial constant matrix has no lower-order Leibniz flux. -/
theorem iterateLowerWordFlux_constant
    (B : Matrix (Fin 2) (Fin 2) ℝ) (v : Vec 2 → ℝ) (w : List (Fin 2)) :
    iterateLowerWordFlux (fun _ => B) v w = 0 := by
  funext x i
  unfold iterateLowerWordFlux
  apply Finset.sum_eq_zero
  intro j _
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  obtain ⟨_, hn⟩ := List.mem_filter.mp hp
  have hne : p.1 ≠ [] := by intro he; simp [he] at hn
  rw [iterateSpatialWord_const]
  simp only [ite_eq_right hne, zero_mul]

/-- Only the principal flux survives for the time-only coefficient. -/
theorem iterateWordFlux_constant
    (B : Matrix (Fin 2) (Fin 2) ℝ) (v : Vec 2 → ℝ) (w : List (Fin 2)) (x : Vec 2) :
    iterateWordFlux (fun _ => B) v w x =
      B.mulVec (spaceGrad (iterateSpatialWord w v) x) := by
  rw [iterateWordFlux_principal, iterateLowerWordFlux_constant]
  simp only [Pi.zero_apply, add_zero]

/-- The expanded flux is linear in its smooth matrix coefficient. -/
theorem iterateWordFlux_add
    {A B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hB : ContDiff ℝ (⊤ : ℕ∞) B)
    (v : Vec 2 → ℝ) (w : List (Fin 2)) (x : Vec 2) :
    iterateWordFlux (fun y => A y + B y) v w x =
      iterateWordFlux A v w x + iterateWordFlux B v w x := by
  funext i
  unfold iterateWordFlux
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hentry := iterateSpatialWord_linear
    (contDiff_pi.mp (contDiff_pi.mp hA i) j)
    (contDiff_pi.mp (contDiff_pi.mp hB i) j) 1
  simp only [one_mul] at hentry
  simp only [Matrix.add_apply, hentry]
  simp only [add_mul, List.sum_map_add]

/-- Exact forcing-flux decomposition for the literal iterate equation. -/
theorem iterateWordFlux_TForcing_coefficient {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm κprev t : ℝ)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (I.sMat hΦ m κm t))
    (v : Vec 2 → ℝ) (w : List (Fin 2)) (x : Vec 2) :
    iterateWordFlux (fun y => I.Kmat κm m t -
      κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t y) v w x =
      (I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec
        (spaceGrad (iterateSpatialWord w v) x) +
      iterateWordFlux (I.sMat hΦ m κm t) v w x := by
  rw [iterateWordFlux_add contDiff_const hs, iterateWordFlux_constant]

end AVenhance.Infra.Section4
