/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedSpaceTime

/-! Discharge natural space-time integrability using the actual smooth scalar
carrier and continuity of the conditional coefficient jets. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Continuous nonnegative-time fields are integrable on the time cell. -/
theorem iterate_timeCube_integrable_of_continuousOn {f : AmnrSpace → ℝ}
    (hf : ContinuousOn f (Set.Ici (0 : ℝ) ×ˢ Set.univ)) : IntegrableOn f timeCube := by
  have hi := iterate_time_cell_integrable_of_continuousOn hf (by norm_num : (0 : ℝ) ≤ 1)
  rw [Measure.prod_restrict] at hi
  change IntegrableOn f (Set.uIoc 0 1 ×ˢ unitCube) at hi
  apply hi.mono_set
  intro z hz
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact ⟨⟨hz.1.1, hz.1.2.le⟩, hz.2⟩

/-- Joint smoothness of every actual spatial word gradient, including time zero. -/
theorem iterate_word_gradient_smooth_up_to_initial {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  apply contDiffOn_pi.mpr
  intro i
  exact iterate_spatial_partial_smooth_up_to_initial (iterateSpatialWord_smooth_up_to_initial hu
      w) i

/-- The actual smooth carrier supplies every word-gradient energy's integrability. -/
theorem iterate_word_gradient_energy_integrable {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    IntegrableOn (fun z : AmnrSpace =>
      vecNormSq (spaceGrad (iterateSpatialWord w (u z.1)) z.2)) timeCube := by
  have hg := (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn
  apply iterate_timeCube_integrable_of_continuousOn
  unfold vecNormSq vecDot
  exact continuousOn_finsetSum Finset.univ (fun i _ =>
    ((continuous_apply i).comp_continuousOn hg).mul ((continuous_apply i).comp_continuousOn hg))

/-- The specified actual flux is continuous when its coefficient jets are
continuous and its scalar has the smooth initial-time carrier. -/
theorem iterateSplitFlux_continuousOn_of_jets
    (P : List (List (Fin 2) × List (Fin 2)))
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → ℝ}
    (hA : ∀ p ∈ P, ContinuousOn
      (fun z : AmnrSpace => iterateMatrixWord (A z.1) p.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun z : AmnrSpace => iterateSplitFlux P (A z.1) (v z.1) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hterm (p : List (Fin 2) × List (Fin 2)) (hp : p ∈ P) :
      ContinuousOn (fun z : AmnrSpace => (iterateMatrixWord (A z.1) p.1 z.2).mulVec
        (spaceGrad (iterateSpatialWord p.2 (v z.1)) z.2))
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    have hg := (iterate_word_gradient_smooth_up_to_initial hv p.2).continuousOn
    apply continuousOn_pi.mpr
    intro i
    change ContinuousOn (fun z : AmnrSpace => ∑ j : Fin 2,
      iterateMatrixWord (A z.1) p.1 z.2 i j *
        spaceGrad (iterateSpatialWord p.2 (v z.1)) z.2 j) _
    exact continuousOn_finsetSum Finset.univ (fun j _ =>
      ((continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn (hA p hp))).mul
      ((continuous_apply j).comp_continuousOn hg))
  induction P with
  | nil =>
    have heq : (fun z : AmnrSpace => iterateSplitFlux [] (A z.1) (v z.1) z.2) = fun _ => 0 := by
      funext z i
      simp [iterateSplitFlux]
    rw [heq]
    exact continuousOn_const
  | cons p P ih =>
    have heq : (fun z : AmnrSpace => iterateSplitFlux (p :: P) (A z.1) (v z.1) z.2) =
        fun z => (iterateMatrixWord (A z.1) p.1 z.2).mulVec
          (spaceGrad (iterateSpatialWord p.2 (v z.1)) z.2) +
          iterateSplitFlux P (A z.1) (v z.1) z.2 := by
      funext z
      rw [iterateSplitFlux_eq_sum, List.map_cons, List.sum_cons, ← iterateSplitFlux_eq_sum]
    rw [heq]
    exact (hterm p List.mem_cons_self).add (ih
      (fun q hq => hA q (List.mem_cons_of_mem p hq))
      (fun q hq => hterm q (List.mem_cons_of_mem p hq)))

end AVenhance.Infra.Section4
