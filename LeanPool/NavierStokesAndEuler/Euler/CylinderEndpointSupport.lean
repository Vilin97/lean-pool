/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointForcing
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletSupport
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletMean

@[expose] public section

/-!
Spatial support and zero angular mean of the actual affine-terminal
cylinder inverse. Both properties are inherited from its genuine L²
terminal datum through the explicit forced reduction.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerLpCylinderPaths EulerTimeLp EulerCylinderAngleAverage

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

section Support

variable (S : Set Space) (hS : MeasurableSet S)

omit [CompleteSpace U] [CompleteSpace E] in
theorem frame_supported (u : CylinderL2 P U) (hu : u ∈ Supported P U S hS)
    (t : Icc (0 : ℝ) T) : D.frame P t u ∈ Supported P E S hS := by
  apply (spatialCutoff_fix P S hS _).2
  rw [← D.frame_cutoff P S hS,(spatialCutoff_fix P S hS u).1 hu]

omit [CompleteSpace U] [CompleteSpace E] in
theorem frameDerivative_supported (u : CylinderL2 P U) (hu : u ∈ Supported P U S hS)
    (t : Icc (0 : ℝ) T) : D.frameDerivative P t u ∈ Supported P E S hS := by
  apply (spatialCutoff_fix P S hS _).2
  rw [← D.frameDerivative_cutoff P S hS,(spatialCutoff_fix P S hS u).1 hu]

variable (Y : CylinderL2 P U) (hY : Y ∈ Supported P U S hS)

include hY

omit [CompleteSpace U] [CompleteSpace E] in
theorem endpointForcing_supported (t : Icc (0 : ℝ) T) :
    D.endpointForcing P Y t ∈ Supported P E S hS := by
  rw [D.endpointForcing_apply P Y t]
  exact (Supported P E S hS).smul_mem _
    (D.frameDerivative_supported P S hS _ ((Supported P U S hS).smul_mem _ hY) t)

theorem endpointCoordinate_supported (t : Icc (0 : ℝ) T) :
    D.endpointCoordinate P Y t ∈ Supported P U S hS := by
  rw [D.endpointCoordinate_eq_const_sub P Y t]
  exact (Supported P U S hS).sub_mem ((Supported P U S hS).smul_mem _ hY)
    (D.velocityPath_supported P S hS (D.endpointForcing P Y)
      (D.endpointForcing_supported P S hS Y hY) t)

theorem endpointAcceleration_supported (t : Icc (0 : ℝ) T) :
    D.endpointAcceleration P Y t ∈ Supported P U S hS := by
  rw [D.endpointAcceleration_eq_forced P Y,ContinuousMap.neg_apply]
  exact (Supported P U S hS).neg_mem
    (D.accelerationPath_supported P S hS (D.endpointForcing P Y)
      (D.endpointForcing_supported P S hS Y hY) t)

theorem endpointVelocity_supported (t : Icc (0 : ℝ) T) :
    D.endpointVelocity P Y t ∈ Supported P E S hS :=
  D.frame_supported P S hS _ (D.endpointCoordinate_supported P S hS Y hY t) t

theorem endpointDerivative_supported (t : Icc (0 : ℝ) T) :
    D.endpointDerivative P Y t ∈ Supported P E S hS :=
  (Supported P E S hS).add_mem
    (D.frameDerivative_supported P S hS _ (D.endpointCoordinate_supported P S hS Y hY t) t)
    (D.frame_supported P S hS _ (D.endpointAcceleration_supported P S hS Y hY t) t)

end Support

section Mean

variable (Y : CylinderL2 P U) (hY : average P Y = 0)

include hY

theorem endpointForcing_mean_zero (t : Icc (0 : ℝ) T) : average P (D.endpointForcing P Y t) = 0 :=
  by
  rw [D.endpointForcing_apply P Y t,map_smul]
  change (2 : ℝ) • average P (fullOperatorMap P (D.Q₁ t) (T⁻¹ • Y)) = 0
  rw [average_fullOperator,map_smul,hY,smul_zero,map_zero,smul_zero]

theorem endpointCoordinate_mean_zero (t : Icc (0 : ℝ) T) :
    average P (D.endpointCoordinate P Y t) = 0 := by
  rw [D.endpointCoordinate_eq_const_sub P Y t,map_sub,map_smul,hY,smul_zero,
    D.velocityPath_mean_zero P (D.endpointForcing P Y) (D.endpointForcing_mean_zero P Y hY)
      t,sub_zero]

theorem endpointAcceleration_mean_zero (t : Icc (0 : ℝ) T) :
    average P (D.endpointAcceleration P Y t) = 0 := by
  rw [D.endpointAcceleration_eq_forced P Y,ContinuousMap.neg_apply,map_neg,
    D.accelerationPath_mean_zero P (D.endpointForcing P Y) (D.endpointForcing_mean_zero P Y hY)
      t,neg_zero]

theorem endpointVelocity_mean_zero (t : Icc (0 : ℝ) T) :
    average P (D.endpointVelocity P Y t) = 0 := by
  change average P (fullOperatorMap P (D.Q t) (D.endpointCoordinate P Y t)) = 0
  rw [average_fullOperator,D.endpointCoordinate_mean_zero P Y hY t,map_zero]

theorem endpointDerivative_mean_zero (t : Icc (0 : ℝ) T) :
    average P (D.endpointDerivative P Y t) = 0 := by
  change average P (fullOperatorMap P (D.Q₁ t) (D.endpointCoordinate P Y t)+
    fullOperatorMap P (D.Q t) (D.endpointAcceleration P Y t)) = 0
  rw [map_add,average_fullOperator,average_fullOperator,
    D.endpointCoordinate_mean_zero P Y hY t,D.endpointAcceleration_mean_zero P Y hY t,
    map_zero,map_zero,add_zero]

end Mean

end EulerCylinderDirichlet.Coefficients
