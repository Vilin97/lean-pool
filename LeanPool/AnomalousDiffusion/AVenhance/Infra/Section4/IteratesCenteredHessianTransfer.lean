/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualHalfSquareBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedCell
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesC1SpatialContinuity

/-! # Iterates Centered Hessian Transfer

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The centered forcing gradient transfers to the exact Hessian half-square
pairing. This is the first-increment forcing term, with its original sign. -/
theorem iterate_centered_hessian_forcing_transfer {β : ℝ} (I : Ingredients β)
    (hN : 1 ≤ Nstar β)
    {m : ℕ} {κm : ℝ} (hm : 1 ≤ m) (hκm : 0 < κm)
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t)) (w : List (Fin 2))
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (fun y => ∑ j : Fin 2, ∑ k : Fin 2,
        (I.Kmat κm m z.1 j k - timeAvgMat (I.Kmat κm m) j k) *
          iterateSpatialWord (j :: k :: w) (u z.1) y) z.2)
      ((iterateKmatPrimitive I κm m z.1).mulVec
        (spaceGrad (iterateSpatialWord w (u z.1)) z.2))) =
      -(∫ t in 0..s, ∫ x in unitCube,
        (∑ j : Fin 2, ∑ k : Fin 2,
          (I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k) *
            iterateSpatialWord (j :: k :: w) (u t) x) *
        (∑ j : Fin 2, ∑ k : Fin 2, iterateKmatPrimitive I κm m t j k *
          iterateSpatialWord (j :: k :: w) (u t) x)) := by
  let F := fun t x => ∑ j : Fin 2, ∑ k : Fin 2,
    (I.Kmat κm m t j k - timeAvgMat (I.Kmat κm m) j k) *
      iterateSpatialWord (j :: k :: w) (u t) x
  have hK := ((AVenhance.Infra.Section3.Kmat_contDiff I hm hκm).of_le
    (by exact_mod_cast hN : (1 : WithTop ℕ∞) ≤ Nstar β)).comp
    (contDiff_fst : ContDiff ℝ 1 (fun z : AmnrSpace => z.1))
  have hF : ContDiffOn ℝ 1 (fun z : AmnrSpace => F z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    apply ContDiffOn.sum
    intro j _
    apply ContDiffOn.sum
    intro k _
    exact (((contDiff_pi.mp (contDiff_pi.mp hK j) k).contDiffOn).sub contDiffOn_const).mul
      ((iterateSpatialWord_smooth_up_to_initial hu (j :: k :: w)).of_le (by simp))
  have hQc : ContinuousOn (fun z : AmnrSpace => iterateKmatPrimitive I κm m z.1)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k
    exact (iterateKmatPrimitive_entry_joint_contDiff I hκm hm j k).continuous.continuousOn
  have hFg : ContinuousOn (fun z : AmnrSpace => spaceGrad (F z.1) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    apply continuousOn_pi.mpr
    intro j
    exact iterate_spatial_partial_continuous_up_to_initial hF j
  have hleft := iterate_matrix_pairing_continuousOn hFg
    (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn hQc
  change ContinuousOn (fun z : AmnrSpace => vecDot (spaceGrad (F z.1) z.2)
    ((iterateKmatPrimitive I κm m z.1).mulVec
      (spaceGrad (iterateSpatialWord w (u z.1)) z.2))) _ at hleft
  rw [iterate_truncated_integral_eq_interval hleft hs]
  have hslice (t : ℝ) (ht : 0 < t) : ContDiff ℝ (⊤ : ℕ∞) (u t) :=
    hu.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
      (fun _ => ⟨ht.le, Set.mem_univ _⟩)
  have he : (fun t => ∫ x in unitCube, vecDot (spaceGrad (F t) x)
      ((iterateKmatPrimitive I κm m t).mulVec
        (spaceGrad (iterateSpatialWord w (u t)) x))) =ᵐ[volume.restrict (Set.uIoc 0 s)]
      (fun t => -(∫ x in unitCube, F t x *
        (∑ j : Fin 2, ∑ k : Fin 2, iterateKmatPrimitive I κm m t j k *
          iterateSpatialWord (j :: k :: w) (u t) x))) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le hs] at ht
    have hFs : ContDiff ℝ (⊤ : ℕ∞) (F t) := by
      apply ContDiff.sum
      intro j _
      apply ContDiff.sum
      intro k _
      exact contDiff_const.mul (iterateSpatialWord_smooth (hslice t ht.1) (j :: k :: w))
    have hFp : IsZ2Periodic (F t) := by
      intro a x
      dsimp only [F]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [iterateSpatialWord_periodic (hslice t ht.1) (hup t ht.1) (j :: k :: w) a x]
    exact iterate_constant_matrix_pairing_ibp hFs
      (iterateSpatialWord_smooth (hslice t ht.1) w) hFp
      (iterateSpatialWord_periodic (hslice t ht.1) (hup t ht.1) w)
      (iterateKmatPrimitive I κm m t)
  rw [intervalIntegral.integral_congr_ae_restrict he, intervalIntegral.integral_neg]

end AVenhance.Infra.Section4
