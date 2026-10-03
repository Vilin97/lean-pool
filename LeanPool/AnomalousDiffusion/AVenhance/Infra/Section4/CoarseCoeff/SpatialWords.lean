/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Regularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Representation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.CutoffAverage
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordCoefficientSplit

/-! # Spatial Words

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- A spatially constant factor commutes with every ordered derivative. -/
theorem iterateSpatialWord_const_mul {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (w : List (Fin 2)) :
    iterateSpatialWord w (fun x => c * f x) = fun x => c * iterateSpatialWord w f x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [iterateSpatialWord, ih]
    funext x
    unfold spaceGrad
    rw [fderiv_const_mul ((iterateSpatialWord_smooth hf w).differentiable (by simp) x) c]
    rfl

theorem coarseCoeff_word_add {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (w : List (Fin 2)) :
    iterateSpatialWord w (fun x => f x + g x) =
      fun x => iterateSpatialWord w f x + iterateSpatialWord w g x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [iterateSpatialWord, ih]
    funext x
    unfold spaceGrad
    change (fderiv ℝ (iterateSpatialWord w f + iterateSpatialWord w g) x) (basisVec i) = _
    rw [fderiv_add ((iterateSpatialWord_smooth hf w).differentiable (by simp) x)
      ((iterateSpatialWord_smooth hg w).differentiable (by simp) x)]
    rfl

/-- Ordered jets of either polynomial specialization: only the spatial
kernel is differentiated, never K or the time cutoff. -/
theorem coarseCoeffWindow_word_formula {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ}
    (hm : 1 ≤ m) (κ a b t : ℝ)
    (hflow : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t))
    (w : List (Fin 2)) (x : Vec 2) (i j : Fin 2) :
    iterateSpatialWord w (fun y => coarseCoeffWindow I hΦ m κ a b t y i j) x =
      ∑' l : ℤ, I.hatXiML m l t * iterateSpatialWord w
        (fun y => coarseCoeffPolynomial a b κ (I.Kmat κ m t) (I.flowGrad hΦ m l t y) i j) x := by
  classical
  let S := (I.hatXiML_support_finite hm t).toFinset
  have he (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => coarseCoeffPolynomial a b κ (I.Kmat κ m t) (I.flowGrad hΦ m l t y) i j) :=
    contDiff_pi.1 (contDiff_pi.1 (coarseCoeffPolynomial_contDiff a b κ
      (show ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => I.Kmat κ m t) from contDiff_const)
      (hflow l)) i) j
  have hrep : (fun y => coarseCoeffWindow I hΦ m κ a b t y i j) =
      fun y => ∑ l ∈ S, I.hatXiML m l t *
        coarseCoeffPolynomial a b κ (I.Kmat κ m t) (I.flowGrad hΦ m l t y) i j := by
    funext y
    rw [coarseCoeffWindow_eq_sum I hΦ hm]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rfl
  rw [hrep, iterateSpatialWord_sum S _ (fun l _ => contDiff_const.mul (he l))]
  rw [tsum_eq_sum (s := S) (fun l hl => by
    have hz : I.hatXiML m l t = 0 := by
      by_contra hn
      exact hl ((Set.Finite.mem_toFinset _).mpr hn)
    rw [hz, zero_mul])]
  apply Finset.sum_congr rfl
  intro l _
  exact congrFun (iterateSpatialWord_const_mul (he l) (I.hatXiML m l t) w) x

/-- Word bounds transfer from active polynomial kernels to their convex average. -/
theorem coarseCoeffWindow_word_entry_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ}
    (hm : 1 ≤ m) (κ a b t : ℝ)
    (hflow : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t))
    (w : List (Fin 2)) (x : Vec 2) {C : ℝ}
    (hG : ∀ l, I.hatXiML m l t ≠ 0 → ∀ i j,
      |iterateSpatialWord w (fun y =>
        coarseCoeffPolynomial a b κ (I.Kmat κ m t) (I.flowGrad hΦ m l t y) i j) x| ≤ C)
    (i j : Fin 2) :
    |iterateSpatialWord w (fun y => coarseCoeffWindow I hΦ m κ a b t y i j) x| ≤ C := by
  rw [coarseCoeffWindow_word_formula I hΦ hm κ a b t hflow]
  exact coarseCoeff_hatXi_average_abs_le I hm t _ (fun l hl => hG l hl i j)

end AVenhance.Infra.Section4
