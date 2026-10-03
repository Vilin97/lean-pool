/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCenteredRemainderFormula
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordDriftPairing

/-! # Iterates Centered Remainder Gradient

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- The actual forcing gradient retains the centered term separately from
 the small mean/spatial remainder at every spatial order. -/
theorem iterate_TForcing_word_gradient_centered_remainder {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm κprev t : ℝ) (v : ℝ → Vec 2 → ℝ)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (I.sMat hΦ m κm t))
    (hv : ContDiff ℝ (⊤ : ℕ∞) (v t)) (w : List (Fin 2)) (x : Vec 2) :
    spaceGrad (iterateSpatialWord w (I.TForcing hΦ m κm κprev v t)) x =
      spaceGrad (fun y => ∑ j : Fin 2, ∑ k : Fin 2,
        (I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k) *
          iterateSpatialWord (j :: k :: w) (v t) y) x +
      spaceGrad (iterateSpatialWord w (vecDiv (fun y =>
        (timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          I.sMat hΦ m κm t y).mulVec (spaceGrad (v t) y)))) x := by
  have he : iterateSpatialWord w (I.TForcing hΦ m κm κprev v t) = fun y =>
      (∑ j : Fin 2, ∑ k : Fin 2,
        (I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k) *
          iterateSpatialWord (j :: k :: w) (v t) y) +
      iterateSpatialWord w (vecDiv (fun z =>
        (timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          I.sMat hΦ m κm t z).mulVec (spaceGrad (v t) z))) y :=
    funext (iterate_TForcing_word_centered_remainder I hΦ m κm κprev t v hs hv w)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ j : Fin 2, ∑ k : Fin 2,
      (I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k) *
        iterateSpatialWord (j :: k :: w) (v t) y) :=
    ContDiff.sum (fun j _ => ContDiff.sum (fun k _ =>
      contDiff_const.mul (iterateSpatialWord_smooth hv (j :: k :: w))))
  have hR : ContDiff ℝ (⊤ : ℕ∞) (fun y =>
      timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) := contDiff_const.add hs
  have hr := iterate_divergence_smooth (iterateWordFlux_smooth hR hv w)
  rw [← iterateSpatialWord_matrix_forcing_divergence hR hv w] at hr
  rw [he]
  have hd := fderiv_fun_add (hc.differentiable (by simp)).differentiableAt
    (hr.differentiable (by simp)).differentiableAt (x := x)
  ext j
  exact congrArg (fun D : Vec 2 →L[ℝ] ℝ => D (basisVec j)) hd

end AVenhance.Infra.Section4
