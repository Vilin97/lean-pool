/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordSolution
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergyIntegrability

/-! Exact terminal-time energy of actual differentiated increments.
The drift commutator and differentiated forcing retain their signed pairings. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Terminal-time energy identity for actual scalar forcing. Spatial forcing
regularity is derived from the classical equation and admissible stream. -/
theorem iterate_scalar_forced_time_energy_identity
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {u : ℝ → Vec 2 → ℝ}
    {u₀ : Vec 2 → ℝ} {F : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (hsol : IsClassicalSol (streamVel φ) κ F u₀ u)
    {T : ℝ} (hT : 0 ≤ T)
    (hI : Integrable (fun p : ℝ × Vec 2 => u p.1 p.2 * deriv (fun s => u s p.2) p.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)))
    (hG : IntervalIntegrable (fun t => ∫ x in unitCube, vecNormSq (spaceGrad (u t) x)) volume 0 T) :
    (l2NormSq (u T) - l2NormSq u₀) / 2 +
      κ * (∫ t in 0..T, ∫ x in unitCube, vecNormSq (spaceGrad (u t) x)) =
      ∫ t in 0..T, ∫ x in unitCube, u t x * F t x := by
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => streamVel φ z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.contDiffOn
  have he := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hT
    (fun t ht => iterate_classical_energy_pairing hφ hsol ht.1
      (iterate_classical_forcing_spatial_smooth hsol hb ht.1).continuous)
  have htime : IntervalIntegrable (fun t => ∫ x in unitCube,
      u t x * deriv (fun s => u s x) t) volume 0 T :=
    intervalIntegrable_iff.mpr hI.integral_prod_left
  rw [intervalIntegral.integral_add htime (hG.const_mul κ),
    intervalIntegral.integral_const_mul, iterate_classical_time_energy_pairing hsol hT hI] at he
  exact he

/-- Apply exact terminal-time energy to the actual spatial word. The right
side contains the differentiated original forcing minus the expanded drift
error, with the initial word trace retained. No energy recurrence is assumed. -/
theorem iterate_classical_word_time_energy_identity
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {u : ℝ → Vec 2 → ℝ}
    {u₀ : Vec 2 → ℝ} {F : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (hsol : IsClassicalSol (streamVel φ) κ F u₀ u)
    (w : List (Fin 2)) {T : ℝ} (hT : 0 ≤ T)
    (hI : Integrable (fun p : ℝ × Vec 2 => iterateSpatialWord w (u p.1) p.2 *
      deriv (fun s => iterateSpatialWord w (u s) p.2) p.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)))
    (hG : IntervalIntegrable (fun t => ∫ x in unitCube,
      vecNormSq (spaceGrad (iterateSpatialWord w (u t)) x)) volume 0 T) :
    (l2NormSq (iterateSpatialWord w (u T)) - l2NormSq (iterateSpatialWord w u₀)) / 2 +
      κ * (∫ t in 0..T, ∫ x in unitCube,
        vecNormSq (spaceGrad (iterateSpatialWord w (u t)) x)) =
      ∫ t in 0..T, ∫ x in unitCube, iterateSpatialWord w (u t) x *
        (iterateSpatialWord w (F t) x -
          iterateWordMaterialError (fun z : AmnrSpace => streamVel φ z.1 z.2) w
            (fun z => u z.1 z.2) (t, x)) := by
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => streamVel φ z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.contDiffOn
  exact iterate_scalar_forced_time_energy_identity hφ
    (iterate_classical_spatial_word_sol hsol hb w) hT hI hG

/-- Spatial words of zero initial data are identically zero. -/
theorem iterateSpatialWord_zero (w : List (Fin 2)) :
    iterateSpatialWord w (fun _ : Vec 2 => (0 : ℝ)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [iterateSpatialWord, ih, spaceGrad, fderiv_fun_const]
    rfl

/-- The actual smooth carrier supplies both natural integrability premises
of the all-order terminal-time energy identity. -/
theorem iterate_classical_word_time_energy_identity_of_smooth
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {u : ℝ → Vec 2 → ℝ}
    {u₀ : Vec 2 → ℝ} {F : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (hsol : IsClassicalSol (streamVel φ) κ F u₀ u)
    (w : List (Fin 2)) {T : ℝ} (hT : 0 ≤ T) :
    (l2NormSq (iterateSpatialWord w (u T)) - l2NormSq (iterateSpatialWord w u₀)) / 2 +
      κ * (∫ t in 0..T, ∫ x in unitCube,
        vecNormSq (spaceGrad (iterateSpatialWord w (u t)) x)) =
      ∫ t in 0..T, ∫ x in unitCube, iterateSpatialWord w (u t) x *
        (iterateSpatialWord w (F t) x -
          iterateWordMaterialError (fun z : AmnrSpace => streamVel φ z.1 z.2) w
            (fun z => u z.1 z.2) (t, x)) := by
  obtain ⟨hI, hG⟩ := iterate_smooth_energy_integrability
    (u := fun t => iterateSpatialWord w (u t))
    (iterateSpatialWord_smooth_up_to_initial hsol.1 w) hT
  exact iterate_classical_word_time_energy_identity hφ hsol w hT hI hG

end AVenhance.Infra.Section4
