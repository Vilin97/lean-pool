/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualPrimitive
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCrossCell
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixIntegralSum

/-! # Iterates Actual Primitive Flat

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual scalar primitive identity on the terminal space-time cell;
all three component pairings have natural integrability. -/
theorem iterate_increment_gradient_primitive_flat_component {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hm : 1 ≤ m) (hκm : 0 < κm) (i : ℕ) (hi : i + 1 ≤ Nstar β)
    (w : List (Fin 2)) (j k : Fin 2) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    let u := fun t => iterateSpatialWord w (iterateIncrement T (i + 1) t)
    let v := fun t => iterateSpatialWord w (iterateIncrement T i t)
    let b := streamVel (Φ (m - 1))
    let q := fun t => iterateKmatPrimitive I κm m t j k
    (∫ z in iterateTruncatedCell s,
      (I.Kmat κm m z.1 j k - timeAvgMat (I.Kmat κm m) j k) *
        spaceGrad (u z.1) z.2 j * spaceGrad (v z.1) z.2 k) =
      (∫ x in unitCube, spaceGrad (u s) x j * (q s * spaceGrad (v s) x k)) -
      (∫ z in iterateTruncatedCell s, q z.1 * spaceGrad (u z.1) z.2 j *
        amnrMaterial b (fun t x => spaceGrad (v t) x k) z.1 z.2) -
      (∫ z in iterateTruncatedCell s, q z.1 * spaceGrad (v z.1) z.2 k *
        amnrMaterial b (fun t x => spaceGrad (u t) x j) z.1 z.2) := by
  dsimp only
  have hp := iterate_increment_material_primitive_pairing I hΦ hT hθ hm hκm i hi
    (j :: w) (k :: w) j k hs
  obtain ⟨hφ, _⟩ := hΦ.2 m hm
  have hb : ContinuousOn (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.continuous.continuousOn
  have hu := iterateSpatialWord_smooth_up_to_initial
    (iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 hi) (j :: w)
  have hv := iterateSpatialWord_smooth_up_to_initial
    (iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 (by omega : i ≤ Nstar β)) (k :: w)
  have hq : ContinuousOn (fun z : AmnrSpace => iterateKmatPrimitive I κm m z.1 j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (iterateKmatPrimitive_entry_joint_contDiff I hκm hm j k).continuous.continuousOn
  have hK : ContinuousOn (fun z : AmnrSpace =>
      I.Kmat κm m z.1 j k - timeAvgMat (I.Kmat κm m) j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    ((contDiff_pi.mp (contDiff_pi.mp (AVenhance.Infra.Section3.Kmat_contDiff I hm hκm) j)
        k).continuous.comp
      continuous_fst).continuousOn.sub continuousOn_const
  have hJ := iterate_timeCube_integrable_of_continuousOn ((hK.mul hu.continuousOn).mul
      hv.continuousOn)
  have hU := iterate_material_cross_timeCube_integrable
    (u := fun t x => iterateKmatPrimitive I κm m t j k *
      iterateSpatialWord (j :: w) (iterateIncrement T (i + 1) t) x)
    (v := fun t => iterateSpatialWord (k :: w) (iterateIncrement T i t))
    hb (hq.mul hu.continuousOn) (hv.of_le (by simp))
  have hV := iterate_material_cross_timeCube_integrable
    (u := fun t x => iterateKmatPrimitive I κm m t j k *
      iterateSpatialWord (k :: w) (iterateIncrement T i t) x)
    (v := fun t => iterateSpatialWord (j :: w) (iterateIncrement T (i + 1) t))
    hb (hq.mul hv.continuousOn) (hu.of_le (by simp))
  simp only [iterateSpatialWord] at hp hJ hU hV
  change IntegrableOn (fun z : AmnrSpace =>
    (I.Kmat κm m z.1 j k - timeAvgMat (I.Kmat κm m) j k) *
      spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2 j *
      spaceGrad (iterateSpatialWord w (iterateIncrement T i z.1)) z.2 k) timeCube at hJ
  rw [iterate_truncated_integral_eq_interval_of_integrable hJ hs hs1,
    iterate_truncated_integral_eq_interval_of_integrable hU hs hs1,
    iterate_truncated_integral_eq_interval_of_integrable hV hs hs1]
  exact hp

end AVenhance.Infra.Section4
