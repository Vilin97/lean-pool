/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDivergenceAdd
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingFluxParts

/-! # Iterates Centered Remainder Formula

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- A time-only coefficient separates as its literal Hessian contraction
 before applying any forcing-energy estimate. -/
theorem iterate_word_constant_plus_matrix_forcing
    (B : Matrix (Fin 2) (Fin 2) ℝ) {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {v : Vec 2 → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (w : List (Fin 2)) (x : Vec 2) :
    iterateSpatialWord w (vecDiv (fun y => (B + A y).mulVec (spaceGrad v y))) x =
      (∑ j : Fin 2, ∑ k : Fin 2, B j k * iterateSpatialWord (j :: k :: w) v x) +
      iterateSpatialWord w (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x := by
  have hB : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => B.mulVec (spaceGrad (iterateSpatialWord w v) y)) := by
    apply contDiff_pi.mpr
    intro j
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ k : Fin 2,
      B j k * spaceGrad (iterateSpatialWord w v) y k)
    exact ContDiff.sum (fun k _ => contDiff_const.mul
      (contDiff_pi.mp (iterate_gradient_smooth (iterateSpatialWord_smooth hv w)) k))
  have he : iterateWordFlux (fun y => B + A y) v w =
      fun y => B.mulVec (spaceGrad (iterateSpatialWord w v) y) + iterateWordFlux A v w y := by
    funext y
    rw [iterateWordFlux_add contDiff_const hA, iterateWordFlux_constant]
  rw [iterateSpatialWord_matrix_forcing_divergence (contDiff_const.add hA) hv w,
    he, iterate_vecDiv_add hB (iterateWordFlux_smooth hA hv w),
    iterate_constant_matrix_divergence B (iterateSpatialWord_smooth hv w),
    iterateSpatialWord_matrix_forcing_divergence hA hv w]
  rfl

/-- The actual differentiated forcing is its centered Hessian contraction
 plus the actual mean/spatial remainder forcing. -/
theorem iterate_TForcing_word_centered_remainder {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm κprev t : ℝ) (v : ℝ → Vec 2 → ℝ)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (I.sMat hΦ m κm t))
    (hv : ContDiff ℝ (⊤ : ℕ∞) (v t)) (w : List (Fin 2)) (x : Vec 2) :
    iterateSpatialWord w (I.TForcing hΦ m κm κprev v t) x =
      (∑ j : Fin 2, ∑ k : Fin 2,
        (I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k) *
          iterateSpatialWord (j :: k :: w) (v t) x) +
      iterateSpatialWord w (vecDiv (fun y =>
        (timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          I.sMat hΦ m κm t y).mulVec (spaceGrad (v t) y))) x := by
  have he : (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      I.sMat hΦ m κm t y) =
      fun y => (I.Kmat κm m t - timeAvgMat (I.Kmat κm m)) +
        (timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          I.sMat hΦ m κm t y) := by funext y; abel
  change iterateSpatialWord w (vecDiv (fun y =>
    (I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      I.sMat hΦ m κm t y).mulVec (spaceGrad (v t) y))) x = _
  have he0 (y : Vec 2) : I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      I.sMat hΦ m κm t y = (I.Kmat κm m t - timeAvgMat (I.Kmat κm m)) +
        (timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          I.sMat hΦ m κm t y) := congrFun he y
  simp_rw [he0]
  exact iterate_word_constant_plus_matrix_forcing _ (contDiff_const.add hs) hv w x

end AVenhance.Infra.Section4
