/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocitySmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHessianFactor
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedCell

/-! Actual drift-gradient transfer on the full time cell. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The differentiated material error transfers to the preceding Hessian
 over timeCube. Natural integrability follows from its explicit velocity sum. -/
theorem iterate_terminal_material_error_gradient_transfer
    {s : ℝ} (hs1 : s ≤ 1)
    {b : ℝ → Vec 2 → Vec 2} {u v : ℝ → Vec 2 → ℝ}
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQc : ContinuousOn Q (Set.Ici (0 : ℝ)))
    (hbp : ∀ t, 0 < t → IsZ2Periodic (b t))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t))
    (hvp : ∀ t, 0 < t → IsZ2Periodic (v t)) (w : List (Fin 2)) :
    (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (fun y => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => u z.1 z.2) (z.1, y)) z.2)
      ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) =
    -(∫ z in iterateTruncatedCell s, iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => u z.1 z.2) z *
      ∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k * spaceGrad (fun y => spaceGrad (v z.1) y k) z.2 j) := by
  let P := (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)
  let e := fun t x => iterateVelocitySplit P (b t) (u t) x
  have hes := iterateVelocitySplit_smooth_up_to_initial hb hu P
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => e z.1 z.2)
    (Set.Ici (0 : ℝ) ×ˢ Set.univ) at hes
  have hmono : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩
  have he (t : ℝ) (ht : 0 < t) : (fun x => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => u z.1 z.2) (t, x)) = e t := by
    funext x
    exact iterateWordMaterialError_lower_velocity (hb.mono hmono) (hu.mono hmono) ht w x
  have hleftEq : (fun z : AmnrSpace => vecDot (spaceGrad (fun y => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => u z.1 z.2) (z.1, y)) z.2)
      ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) =ᵐ[volume.restrict (iterateTruncatedCell s)]
      (fun z => vecDot (spaceGrad (e z.1) z.2) ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) := by
    apply (ae_restrict_mem (iterateTruncatedCell_isOpen s).measurableSet).mono
    intro z hz
    dsimp only
    rw [he z.1 hz.1.1]
  have hrightEq : (fun z : AmnrSpace => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => u z.1 z.2) z *
      ∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k * spaceGrad (fun y => spaceGrad (v z.1) y k) z.2 j) =ᵐ[
      volume.restrict (iterateTruncatedCell s)]
      (fun z => e z.1 z.2 * ∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k *
        spaceGrad (fun y => spaceGrad (v z.1) y k) z.2 j) := by
    apply (ae_restrict_mem (iterateTruncatedCell_isOpen s).measurableSet).mono
    intro z hz
    change iterateWordMaterialError _ w _ (z.1, z.2) * _ = _
    rw [congrFun (he z.1 hz.1.1) z.2]
  rw [integral_congr_ae hleftEq, integral_congr_ae hrightEq]
  have hqc : ContinuousOn (fun z : AmnrSpace => Q z.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    hQc.comp continuousOn_fst (fun _ hz => hz.1)
  have hl := iterate_matrix_pairing_integrable
    (iterate_word_gradient_smooth_up_to_initial hes []).continuousOn
    (iterate_word_gradient_smooth_up_to_initial hv []).continuousOn hqc
  have hr := iterate_timeCube_integrable_of_continuousOn
    (hes.continuousOn.mul (iterate_hessian_factor_continuousOn hv hQc []))
  have hlf := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Vec 2)))
    _ (by simpa only [iterateTruncatedCell, Measure.volume_eq_prod] using (hl.mono_set
        (iterateTruncatedCell_subset hs1)))
  have hrf := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Vec 2)))
    _ (by simpa only [iterateTruncatedCell, Measure.volume_eq_prod] using (hr.mono_set
        (iterateTruncatedCell_subset hs1)))
  simp only [← Measure.volume_eq_prod, iterateSpatialWord, Pi.mul_apply] at hlf hrf
  change (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (e z.1) z.2)
      ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) = _
  unfold iterateTruncatedCell
  rw [hlf, hrf, ← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hs {f : ℝ → Vec 2 → ℝ}
      (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => f z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ)) : ContDiff ℝ (⊤ : ℕ∞) (f t) :=
    hf.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
      (fun _ => ⟨ht.1.le, Set.mem_univ _⟩)
  have hbs : ContDiff ℝ (⊤ : ℕ∞) (b t) :=
    hb.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
      (fun _ => ⟨ht.1.le, Set.mem_univ _⟩)
  exact iterate_constant_matrix_pairing_ibp (hs hes) (hs hv)
    (iterateVelocitySplit_periodic hbs (hs hu) (hbp t ht.1) (hup t ht.1) P)
    (hvp t ht.1) (Q t)

end AVenhance.Infra.Section4
