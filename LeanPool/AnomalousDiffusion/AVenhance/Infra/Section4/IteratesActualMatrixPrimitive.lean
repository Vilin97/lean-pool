/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualPrimitiveFlat
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesGradientCoordinateMaterial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixPrimitiveAssembly

/-! # Iterates Actual Matrix Primitive

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Full matrix oscillatory flux identity for actual increments. The terminal
term and both differentiated material terms are assembled without norm loss. -/
theorem iterate_increment_matrix_primitive_pairing {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hm : 1 ≤ m) (hκm : 0 < κm) (i : ℕ) (hi : i + 1 ≤ Nstar β)
    (w : List (Fin 2)) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    let u := fun t => iterateSpatialWord w (iterateIncrement T (i + 1) t)
    let v := fun t => iterateSpatialWord w (iterateIncrement T i t)
    let b := streamVel (Φ (m - 1))
    let Q := iterateKmatPrimitive I κm m
    (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
      ((I.Kmat κm m z.1 - timeAvgMat (I.Kmat κm m)).mulVec (spaceGrad (v z.1) z.2))) =
      (∫ x in unitCube, vecDot (spaceGrad (u s) x) ((Q s).mulVec (spaceGrad (v s) x))) -
      (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
        ((Q z.1).mulVec (fun k => amnrMaterial b (fun t x => spaceGrad (v t) x k) z.1 z.2))) -
      (∫ z in iterateTruncatedCell s, vecDot
        (fun j => amnrMaterial b (fun t x => spaceGrad (u t) x j) z.1 z.2)
        ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) := by
  let u := fun t => iterateSpatialWord w (iterateIncrement T (i + 1) t)
  let v := fun t => iterateSpatialWord w (iterateIncrement T i t)
  let b := streamVel (Φ (m - 1))
  let Q := iterateKmatPrimitive I κm m
  have hu := iterateSpatialWord_smooth_up_to_initial
    (iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 hi) w
  have hv := iterateSpatialWord_smooth_up_to_initial
    (iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 (by omega : i ≤ Nstar β)) w
  obtain ⟨hφ, _⟩ := hΦ.2 m hm
  have hb : ContinuousOn (fun z : AmnrSpace => b z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.continuous.continuousOn
  have hq (j k : Fin 2) : ContinuousOn (fun z : AmnrSpace => Q z.1 j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (iterateKmatPrimitive_entry_joint_contDiff I hκm hm j k).continuous.continuousOn
  have hc (j k : Fin 2) : ContinuousOn (fun z : AmnrSpace =>
      I.Kmat κm m z.1 j k - timeAvgMat (I.Kmat κm m) j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    ((contDiff_pi.mp (contDiff_pi.mp (AVenhance.Infra.Section3.Kmat_contDiff I hm hκm) j)
        k).continuous.comp
      continuous_fst).continuousOn.sub continuousOn_const
  have hgu (j : Fin 2) := (iterate_spatial_partial_smooth_up_to_initial hu j).continuousOn
  have hgv (k : Fin 2) := (iterate_spatial_partial_smooth_up_to_initial hv k).continuousOn
  apply iterate_matrix_primitive_component_assembly
  · intro j k
    exact (iterate_truncated_cell_integrable (((hc j k).mul (hgu j)).mul (hgv k)) hs)
  · intro j k
    have huc : Continuous (fun x : Vec 2 => spaceGrad (u s) x j) :=
      (hgu j).comp_continuous (by fun_prop : Continuous (fun x : Vec 2 => (s, x)))
        (fun _ => ⟨hs, Set.mem_univ _⟩)
    have hvc : Continuous (fun x : Vec 2 => spaceGrad (v s) x k) :=
      (hgv k).comp_continuous (by fun_prop : Continuous (fun x : Vec 2 => (s, x)))
        (fun _ => ⟨hs, Set.mem_univ _⟩)
    exact iterate_unitCube_integrable_of_continuous ((continuous_const.mul huc).mul hvc)
  · intro j k
    exact (iterate_gradient_coordinate_material_pairing_integrable
      (u := u) (v := v) (q := fun t => Q t j k) hb hu hv (hq j k) j k).mono_set
      (iterateTruncatedCell_subset hs1)
  · intro j k
    have ht := (iterate_gradient_coordinate_material_pairing_integrable
      (u := v) (v := u) (q := fun t => Q t j k) hb hv hu (hq j k) k j).mono_set
      (iterateTruncatedCell_subset hs1)
    unfold IntegrableOn at ht
    convert ht using 1
    funext z
    ring
  · intro j k
    have hp := iterate_increment_gradient_primitive_flat_component I hΦ hT hθ hm hκm i hi w j k hs
        hs1
    dsimp only at hp
    change (∫ z in iterateTruncatedCell s,
      (I.Kmat κm m z.1 j k - timeAvgMat (I.Kmat κm m) j k) *
        spaceGrad (u z.1) z.2 j * spaceGrad (v z.1) z.2 k) = _
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hp

end AVenhance.Infra.Section4
