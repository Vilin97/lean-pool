/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoefficientContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFluxTimeEnergy

/-! Actual full forcing coefficient jets at every spatial order. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- A time-only coefficient contributes only at spatial order zero. -/
theorem iterateMatrixWord_constant_add
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (w : List (Fin 2)) (x : Vec 2) :
    iterateMatrixWord (fun y => B + A y) w x =
      (if w = [] then B else 0) + iterateMatrixWord A w x := by
  ext j k
  unfold iterateMatrixWord
  change iterateSpatialWord w (fun y => B j k + A y j k) x = _
  have he := iterateSpatialWord_linear (f := fun _ => B j k) contDiff_const
    (contDiff_pi.mp (contDiff_pi.mp hA j) k) 1 w
  simp only [one_mul] at he
  rw [he, iterateSpatialWord_const]
  split <;> rfl

/-- Every jet of the actual full TForcing coefficient is jointly continuous
up to zero, as a consequence of the conditional flow carrier. -/
theorem iterate_TForcing_coefficient_word_continuousOn {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm) (κprev : ℝ)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2)) (w : List (Fin 2)) :
    ContinuousOn (fun z : AmnrSpace => iterateMatrixWord
      (fun y => I.Kmat κm m z.1 - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm z.1 y) w z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hs := iterate_sMat_matrixWord_joint_continuousOn I hΦ hm hκm
    (fun l => (hflow l).contDiffOn) w
  have hfs (t : ℝ) (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t) :=
    (hflow l).comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hsp (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (I.sMat hΦ m κm t) :=
    AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm κm t (hfs t)
  have hc : Continuous (fun z : AmnrSpace =>
      I.Kmat κm m z.1 - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
    ((AVenhance.Infra.Section3.Kmat_contDiff I hm hκm).continuous.comp continuous_fst).sub
        continuous_const
  have hb : ContinuousOn (fun z : AmnrSpace =>
      (if w = [] then I.Kmat κm m z.1 - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) else 0) +
        iterateMatrixWord (I.sMat hΦ m κm z.1) w z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    split
    · exact hc.continuousOn.add hs
    · exact continuousOn_const.add hs
  apply hb.congr
  intro z _
  exact iterateMatrixWord_constant_add (hsp z.1) _ w z.2

end AVenhance.Infra.Section4
