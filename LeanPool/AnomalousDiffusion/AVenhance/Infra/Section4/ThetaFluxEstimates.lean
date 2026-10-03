/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaCommutatorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaSpaceTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaIntegratedEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaEnergyLevels

/-! Space-time estimates for individual stream-form commutator terms. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped Topology

namespace AVenhance.Infra.Section4

/-- Closed time-space unit cell used for the temperature flux estimates. -/
def ThetaFluxEstimates.thetaFluxClosedCell : Set (ℝ × Vec 2) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem ThetaFluxEstimates.thetaFluxClosedCell_compact : IsCompact
    ThetaFluxEstimates.thetaFluxClosedCell := by
  apply IsCompact.prod isCompact_Icc
  simpa [ThetaFluxEstimates.thetaFluxClosedCell] using isCompact_univ_pi
    (fun _ : Fin 2 => isCompact_Icc)

theorem ThetaFluxEstimates.thetaFlux_timeCube_subset_closedCell :
    AVenhance.timeCube ⊆ ThetaFluxEstimates.thetaFluxClosedCell := by
  intro p hp
  rcases hp with ⟨ht, hx⟩
  refine ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, ?_⟩
  change ∀ i ∈ Set.univ, p.2 i ∈ Set.Icc (0 : ℝ) 1
  intro i hi
  have hxi := hx i hi
  exact ⟨le_of_lt hxi.1, le_of_lt hxi.2⟩

/-- Extend a nonnegative-time spatial derivative continuously to all joint
space-time points by clamping the time coordinate at zero. -/
noncomputable def thetaWordExtension (u : ℝ → Vec 2 → ℝ)
    (w : List (Fin 2)) (p : ℝ × Vec 2) : ℝ :=
  classicalWordDerivative w (u (max p.1 0)) p.2

theorem thetaWordExtension_continuous
    {u : ℝ → Vec 2 → ℝ} {w : List (Fin 2)}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    Continuous (thetaWordExtension u w) := by
  have hword := theta_classical_word_joint_contDiffOn_nonneg hu w
  have hmap : Continuous (fun p : ℝ × Vec 2 => (max p.1 0, p.2)) := by
    fun_prop
  have hmem : Set.MapsTo (fun p : ℝ × Vec 2 => (max p.1 0, p.2)) Set.univ
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro p hp
    exact ⟨le_max_right p.1 0, Set.mem_univ _⟩
  have hcont := hword.continuousOn.comp hmap.continuousOn hmem
  change ContinuousOn
    (fun p : ℝ × Vec 2 => classicalWordDerivative w (u (max p.1 0)) p.2)
    Set.univ at hcont
  exact continuousOn_univ.mp hcont

theorem thetaWordExtension_eq_slice
    {u : ℝ → Vec 2 → ℝ} {w : List (Fin 2)}
    (t : ℝ) (ht : 0 < t) (x : Vec 2) :
    thetaWordExtension u w (t, x) = classicalWordDerivative w (u t) x := by
  simp [thetaWordExtension, max_eq_left ht.le]

/-- Continuous joint representative of a component of the gradient of a
word derivative. -/
noncomputable def thetaWordGradientExtension (u : ℝ → Vec 2 → ℝ)
    (w : List (Fin 2)) (p : ℝ × Vec 2) : Vec 2 :=
  fun j => thetaWordExtension u (j :: w) p

theorem thetaWordGradientExtension_continuous
    {u : ℝ → Vec 2 → ℝ} {w : List (Fin 2)}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    Continuous (thetaWordGradientExtension u w) := by
  apply continuous_pi
  intro j
  exact thetaWordExtension_continuous hu

theorem thetaWordGradientExtension_eq_slice
    {u : ℝ → Vec 2 → ℝ} {w : List (Fin 2)}
    (t : ℝ) (ht : 0 < t) (x : Vec 2) :
    thetaWordGradientExtension u w (t, x) =
      AVenhance.spaceGrad (classicalWordDerivative w (u t)) x := by
  funext j
  change thetaWordExtension u (j :: w) (t, x) = _
  rw [thetaWordExtension_eq_slice t ht x]
  rfl

/-- The joint stream velocity formed from the gradient of a word derivative. -/
noncomputable def thetaStreamWordExtension (u : ℝ → Vec 2 → ℝ)
    (w : List (Fin 2)) (p : ℝ × Vec 2) : Vec 2 :=
  fun j => if j = 0 then -thetaWordExtension u (1 :: w) p
    else thetaWordExtension u (0 :: w) p

theorem thetaStreamWordExtension_continuous
    {u : ℝ → Vec 2 → ℝ} {w : List (Fin 2)}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    Continuous (thetaStreamWordExtension u w) := by
  apply continuous_pi
  intro j
  by_cases hj : j = 0
  · subst j
    change Continuous (fun p => -thetaWordExtension u (1 :: w) p)
    exact (thetaWordExtension_continuous (u := u) (w := 1 :: w) hu).neg
  · simpa [thetaStreamWordExtension, hj] using
      thetaWordExtension_continuous (u := u) (w := 0 :: w) hu

theorem thetaStreamWordExtension_eq_slice
    {u : ℝ → Vec 2 → ℝ} {w : List (Fin 2)}
    (t : ℝ) (ht : 0 < t) (x : Vec 2) :
    thetaStreamWordExtension u w (t, x) =
      AVenhance.streamVel (fun _ => classicalWordDerivative w (u t)) 0 x := by
  funext j
  fin_cases j
  · simp [thetaStreamWordExtension, thetaWordExtension_eq_slice t ht x,
      AVenhance.streamVel, AVenhance.sigmaMat,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, classicalWordDerivative,
    Classical.classicalWordDerivative]
  · simp [thetaStreamWordExtension, thetaWordExtension_eq_slice t ht x,
      AVenhance.streamVel, AVenhance.sigmaMat,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, classicalWordDerivative,
    Classical.classicalWordDerivative]

theorem ThetaFluxEstimates.thetaWord_gradient_energy_eq_components
    {u : ℝ → Vec 2 → ℝ} {w : List (Fin 2)}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    thetaWordSpaceTimeGradientEnergy u w =
      ∑ j : Fin 2, ∫ p in AVenhance.timeCube,
        (thetaWordExtension u (j :: w) p) ^ 2 := by
  unfold thetaWordSpaceTimeGradientEnergy
  calc
    (∫ p in AVenhance.timeCube,
        vecNormSq (AVenhance.spaceGrad (classicalWordDerivative w (u p.1)) p.2)) =
      ∫ p in AVenhance.timeCube,
        ∑ j : Fin 2, (thetaWordExtension u (j :: w) p) ^ 2 := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem
            (MeasurableSet.prod measurableSet_Ioo thetaTime_measurableSet_unitCube)] with p hp
          have ht : 0 < p.1 := hp.1.1
          rw [← thetaWordGradientExtension_eq_slice (u := u) (w := w) p.1 ht p.2]
          simp [thetaWordGradientExtension, Homogenization.vecNormSq,
            Homogenization.vecDot, Fin.sum_univ_two]
          ring
    _ = ∑ j : Fin 2, ∫ p in AVenhance.timeCube,
          (thetaWordExtension u (j :: w) p) ^ 2 := by
          rw [MeasureTheory.integral_finsetSum (s := Finset.univ) (f := fun j p =>
            (thetaWordExtension u (j :: w) p) ^ 2) (by
              intro j hj
              have hcont := (thetaWordExtension_continuous
                (u := u) (w := j :: w) hu).pow 2
              exact hcont.continuousOn.integrableOn_compact
                  ThetaFluxEstimates.thetaFluxClosedCell_compact
                |>.mono_set ThetaFluxEstimates.thetaFlux_timeCube_subset_closedCell)]

theorem thetaWordGradientExtension_energy_eq
    {u : ℝ → Vec 2 → ℝ} {w : List (Fin 2)}
    :
    thetaWordSpaceTimeGradientEnergy u w =
      ∫ p in AVenhance.timeCube,
        vecNormSq (thetaWordGradientExtension u w p) := by
  unfold thetaWordSpaceTimeGradientEnergy
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem
    (MeasurableSet.prod measurableSet_Ioo thetaTime_measurableSet_unitCube)] with p hp
  exact congrArg vecNormSq
    (thetaWordGradientExtension_eq_slice (u := u) (w := w) p.1 hp.1.1 p.2).symm

/-- A coordinate derivative obtained by inserting one direction into a word
is bounded in space-time L² by the full gradient energy of that word. -/
theorem theta_word_derivative_energy_le_gradient
    {u : ℝ → Vec 2 → ℝ} {right word : List (Fin 2)} {i : Fin 2}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hperm : word.Perm (i :: right)) :
    ∫ p in AVenhance.timeCube, (thetaWordExtension u word p) ^ 2 ≤
      thetaWordSpaceTimeGradientEnergy u right := by
  have hpoint (p : ℝ × Vec 2) (hp : p ∈ AVenhance.timeCube) :
      (thetaWordExtension u word p) ^ 2 ≤
        vecNormSq (thetaWordGradientExtension u right p) := by
    have ht : 0 < p.1 := hp.1.1
    have hθslice : ContDiff ℝ (⊤ : ℕ∞) (u p.1) := by
      have hθ := theta_classical_word_slice_contDiff_nonneg hu [] p.1 ht.le
      simpa [classicalWordDerivative,
        Classical.classicalWordDerivative] using hθ
    calc
      (thetaWordExtension u word p) ^ 2 =
          classicalWordDerivative word (u p.1) p.2 ^ 2 := by
        rw [thetaWordExtension_eq_slice p.1 ht p.2]
      _ ≤ vecNormSq
          (AVenhance.spaceGrad (classicalWordDerivative right (u p.1)) p.2) :=
        classicalWordDerivative_sq_le_gradient_of_perm
          word right i (u p.1) hθslice p.2 hperm
      _ = vecNormSq (thetaWordGradientExtension u right p) := by
        rw [thetaWordGradientExtension_eq_slice (u := u) (w := right) p.1 ht p.2]
  have hleftInt : IntegrableOn (fun p => (thetaWordExtension u word p) ^ 2)
      AVenhance.timeCube volume :=
    ((thetaWordExtension_continuous hu).pow 2).continuousOn.integrableOn_compact
      ThetaFluxEstimates.thetaFluxClosedCell_compact |>.mono_set
          ThetaFluxEstimates.thetaFlux_timeCube_subset_closedCell
  have hrightInt : IntegrableOn
      (fun p => vecNormSq (thetaWordGradientExtension u right p))
      AVenhance.timeCube volume := by
    have hc : Continuous (fun p =>
        vecNormSq (thetaWordGradientExtension u right p)) := by
      have heq : (fun p => vecNormSq (thetaWordGradientExtension u right p)) =
          fun p => ∑ j : Fin 2,
            (thetaWordGradientExtension u right p j) ^ 2 := by
        funext p
        simp [Homogenization.vecNormSq, Homogenization.vecDot, Fin.sum_univ_two]
        ring
      rw [heq]
      apply continuous_finsetSum
      intro j hj
      exact ((continuous_apply j).comp
        (thetaWordGradientExtension_continuous hu)).pow 2
    exact hc.continuousOn.integrableOn_compact ThetaFluxEstimates.thetaFluxClosedCell_compact
      |>.mono_set ThetaFluxEstimates.thetaFlux_timeCube_subset_closedCell
  have hmono := MeasureTheory.setIntegral_mono_on hleftInt hrightInt
    (MeasurableSet.prod measurableSet_Ioo thetaTime_measurableSet_unitCube) hpoint
  rw [thetaWordGradientExtension_energy_eq]
  exact hmono

end AVenhance.Infra.Section4
