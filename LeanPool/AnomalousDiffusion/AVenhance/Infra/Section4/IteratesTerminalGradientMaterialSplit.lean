/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesGradientMaterialMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedMatrix

/-! # Iterates Terminal Gradient Material Split

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Split a coordinatewise material gradient into its true material-gradient
pairing and the exact one-jet flow commutator on every terminal cell. -/
theorem iterate_terminal_gradient_material_pairing_split
    {b : ℝ → Vec 2 → Vec 2} {u v : ℝ → Vec 2 → ℝ}
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQc : ContinuousOn (fun z : AmnrSpace => Q z.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {s : ℝ} (hs1 : s ≤ 1) :
    (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
      ((Q z.1).mulVec (fun k => amnrMaterial b (fun t x => spaceGrad (v t) x k) z.1 z.2))) =
      (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
        ((Q z.1).mulVec (spaceGrad (amnrMaterial b v z.1) z.2))) -
      (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
        ((Q z.1).mulVec ((gradMatrix (b z.1) z.2).mulVec (spaceGrad (v z.1) z.2)))) := by
  have hgu := (iterate_word_gradient_smooth_up_to_initial hu []).continuousOn
  have hgv := (iterate_word_gradient_smooth_up_to_initial hv []).continuousOn
  have hBg := iterate_flow_gradient_matrix_continuousOn hb
  have hi := iterate_gradient_material_matrix_pairing_integrable hb hu hv hQc
  have hf := iterate_matrix_pairing_integrable
    (a := fun z => spaceGrad (u z.1) z.2) (b := fun z => spaceGrad (v z.1) z.2)
    (A := fun z => Q z.1 * gradMatrix (b z.1) z.2) hgu hgv (hQc.mul hBg)
  have hprod : (fun z : AmnrSpace => vecDot (spaceGrad (u z.1) z.2)
      ((Q z.1 * gradMatrix (b z.1) z.2).mulVec (spaceGrad (v z.1) z.2))) =
      fun z => vecDot (spaceGrad (u z.1) z.2)
        ((Q z.1).mulVec ((gradMatrix (b z.1) z.2).mulVec (spaceGrad (v z.1) z.2))) := by
    funext z
    rw [Matrix.mulVec_mulVec]
  rw [hprod] at hf
  have hmono : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩
  have he : (fun z : AmnrSpace => vecDot (spaceGrad (u z.1) z.2)
      ((Q z.1).mulVec (fun k => amnrMaterial b (fun t x => spaceGrad (v t) x k) z.1 z.2))) =ᵐ[
      volume.restrict (iterateTruncatedCell s)]
      (fun z => vecDot (spaceGrad (u z.1) z.2)
        ((Q z.1).mulVec (spaceGrad (amnrMaterial b v z.1) z.2)) -
        vecDot (spaceGrad (u z.1) z.2)
          ((Q z.1).mulVec ((gradMatrix (b z.1) z.2).mulVec (spaceGrad (v z.1) z.2)))) := by
    filter_upwards [ae_restrict_mem (iterateTruncatedCell_isOpen s).measurableSet] with z hz
    have hg : (fun k => amnrMaterial b (fun t x => spaceGrad (v t) x k) z.1 z.2) =
        spaceGrad (amnrMaterial b v z.1) z.2 -
          (gradMatrix (b z.1) z.2).mulVec (spaceGrad (v z.1) z.2) := by
      funext k
      exact iterate_material_gradient_commutator (hb.mono hmono) (hv.mono hmono) hz.1.1 z.2 k
    rw [hg]
    simp only [vecDot, Matrix.mulVec, dotProduct, Pi.sub_apply, Fin.sum_univ_two]
    ring
  rw [integral_congr_ae he]
  exact integral_sub (hi.mono_set (iterateTruncatedCell_subset hs1))
    (hf.mono_set (iterateTruncatedCell_subset hs1))

end AVenhance.Infra.Section4
