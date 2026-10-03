/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingCoefficients

/-! # Iterates Mean Correction Regularity

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Every jet of the actual mean-plus-spatial correction is continuous up
 to the initial time under the conditional flow carrier. -/
theorem iterate_mean_correction_word_continuousOn {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm) (κprev : ℝ)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2)) (w : List (Fin 2)) :
    ContinuousOn (fun z : AmnrSpace => iterateMatrixWord
      (fun y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm z.1 y) w z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hs := iterate_sMat_matrixWord_joint_continuousOn I hΦ hm hκm
    (fun l => (hflow l).contDiffOn) w
  have hfs (t : ℝ) (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t) :=
    (hflow l).comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hsp (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (I.sMat hΦ m κm t) :=
    AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm κm t (hfs t)
  have hc : ContinuousOn (fun z : AmnrSpace =>
      (if w = [] then timeAvgMat (I.Kmat κm m) -
        κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) else 0) +
      iterateMatrixWord (I.sMat hΦ m κm z.1) w z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    split <;> exact continuousOn_const.add hs
  apply hc.congr
  intro z _
  exact iterateMatrixWord_constant_add (hsp z.1) _ w z.2

end AVenhance.Infra.Section4
