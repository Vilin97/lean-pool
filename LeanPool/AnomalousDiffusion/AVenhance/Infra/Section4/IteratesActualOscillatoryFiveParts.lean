/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualMatrixPrimitive
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalCurrentGradientSplit

/-! # Iterates Actual Oscillatory Five Parts

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Exact five-term oscillatory flux decomposition for the actual increment
sequence: terminal boundary, previous material, current material, and two flow
commutators. All endpoint and integrability issues have been discharged. -/
theorem iterate_increment_oscillatory_flux_five_parts {β : ℝ} (I : Ingredients β)
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
        ((Q z.1).mulVec (spaceGrad (amnrMaterial b v z.1) z.2))) -
      (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (amnrMaterial b u z.1) z.2)
        ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) +
      (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
        ((Q z.1).mulVec ((gradMatrix (b z.1) z.2).mulVec (spaceGrad (v z.1) z.2)))) +
      (∫ z in iterateTruncatedCell s, vecDot
        ((gradMatrix (b z.1) z.2).mulVec (spaceGrad (u z.1) z.2))
        ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) := by
  dsimp only
  obtain ⟨hφ, _⟩ := hΦ.2 m hm
  have hb : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.contDiffOn
  have hu := iterateSpatialWord_smooth_up_to_initial
    (iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 hi) w
  have hv := iterateSpatialWord_smooth_up_to_initial
    (iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 (by omega : i ≤ Nstar β)) w
  have hQc : ContinuousOn (fun z : AmnrSpace => iterateKmatPrimitive I κm m z.1)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k
    exact (iterateKmatPrimitive_entry_joint_contDiff I hκm hm j k).continuous.continuousOn
  have hp := iterate_increment_matrix_primitive_pairing I hΦ hT hθ hm hκm i hi w hs hs1
  have hvp := iterate_terminal_gradient_material_pairing_split
    (u := fun t => iterateSpatialWord w (iterateIncrement T (i + 1) t))
    (v := fun t => iterateSpatialWord w (iterateIncrement T i t))
    hb hu hv hQc hs1
  have hup := iterate_terminal_current_gradient_material_pairing_split
    (u := fun t => iterateSpatialWord w (iterateIncrement T (i + 1) t))
    (v := fun t => iterateSpatialWord w (iterateIncrement T i t))
    hb hu hv hQc hs1
  dsimp only at hp
  rw [hvp, hup] at hp
  linarith only [hp]

end AVenhance.Infra.Section4
