/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaEnergyLevels
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaDifferentiatedEnergy

/-! The zero-amplitude branch, before any normalization by `‖θ₀‖₂`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section4

theorem ThetaZeroBounds.theta_zero_word_eq
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) (hκ : 0 < κ)
    (hsol : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ
      (fun _ _ => 0) (fun _ => 0) θ)
    (w : List (Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    classicalWordDerivative w (θ t) = (fun _ => 0) := by
  have hθ := theta_classical_solution_eq_zero_of_zero_data hφ hκ hsol rfl t ht
  rw [funext hθ]
  induction w with
  | nil => rfl
  | cons i w ih =>
      change (fun x => AVenhance.spaceGrad
        (classicalWordDerivative w (fun _ => 0)) x i) = fun _ => 0
      rw [ih]
      funext x
      simp [AVenhance.spaceGrad]

theorem theta_zero_word_spatial_energy_eq_zero
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) (hκ : 0 < κ)
    (hsol : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ
      (fun _ _ => 0) (fun _ => 0) θ)
    (w : List (Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    thetaWordSpatialEnergy θ w t = 0 := by
  simp [thetaWordSpatialEnergy, ThetaZeroBounds.theta_zero_word_eq hφ hκ hsol w ht]

theorem theta_zero_word_spacetime_gradient_energy_eq_zero
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) (hκ : 0 < κ)
    (hsol : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ
      (fun _ _ => 0) (fun _ => 0) θ)
    (w : List (Fin 2)) :
    thetaWordSpaceTimeGradientEnergy θ w = 0 := by
  unfold thetaWordSpaceTimeGradientEnergy
  calc
    (∫ p in AVenhance.timeCube,
        vecNormSq (AVenhance.spaceGrad
          (classicalWordDerivative w (θ p.1)) p.2)) =
      ∫ p in AVenhance.timeCube, (0 : ℝ) := by
        apply setIntegral_congr_fun
        · exact (measurableSet_Ioo.prod thetaTime_measurableSet_unitCube)
        intro p hp
        have ht : 0 ≤ p.1 := le_of_lt hp.1.1
        have hw := ThetaZeroBounds.theta_zero_word_eq hφ hκ hsol w ht
        change vecNormSq (AVenhance.spaceGrad
          (classicalWordDerivative w (θ p.1)) p.2) = 0
        rw [hw]
        simp [AVenhance.spaceGrad, vecNormSq, vecDot]
    _ = 0 := by simp

theorem theta_zero_energy_level_eq_zero
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ : ℝ → Vec 2 → ℝ} (n : ℕ)
    (hφ : AVenhance.IsAdmissibleStream φ) (hκ : 0 < κ)
    (hsol : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ
      (fun _ _ => 0) (fun _ => 0) θ) :
    thetaEnergyLevel θ κ n = 0 := by
  unfold thetaEnergyLevel
  apply Finset.sup'_eq_of_forall
  intro i hi
  have hsp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      thetaWordSpatialEnergy θ (thetaCoordinateWord i) t = 0 :=
    theta_zero_word_spatial_energy_eq_zero hφ hκ hsol _ ht.1
  have hsup : thetaWordSpatialEnergySup θ (thetaCoordinateWord i) = 0 := by
    unfold thetaWordSpatialEnergySup
    have hrange : Set.range (fun t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} =>
        thetaWordSpatialEnergy θ (thetaCoordinateWord i) t.1) = {0} := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        simp [hsp t.1 t.2]
      · intro hy
        have hy0 : y = 0 := by simpa using hy
        subst y
        refine ⟨⟨0, ⟨by norm_num, by norm_num⟩⟩, ?_⟩
        simp [hsp 0 ⟨by norm_num, by norm_num⟩]
    rw [hrange]
    simp
  rw [hsup, theta_zero_word_spacetime_gradient_energy_eq_zero hφ hκ hsol]
  simp

end AVenhance.Infra.Section4

end
