/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearFlow

/-! # Pointwise energy calculus for the viscous shear -/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic
open CKN.ShearCalculus


namespace CKN

/-- The kinetic-energy density of the shear. -/
@[expose]
noncomputable def shearEnergy (z : Vec3 × ℝ) : ℝ := shearAmplitude z * shearAmplitude z

/-- The cubic scalar transport factor. -/
@[expose]
noncomputable def shearTransport (z : Vec3 × ℝ) : ℝ := shearEnergy z * shearAmplitude z

/-- Smoothness of the energy density. -/
theorem shearEnergy_smooth : ContDiff ℝ (⊤ : ℕ∞) shearEnergy :=
  shearAmplitude_smooth.mul shearAmplitude_smooth

/-- Smoothness of the cubic transport factor. -/
theorem shearTransport_smooth : ContDiff ℝ (⊤ : ℕ∞) shearTransport :=
  shearEnergy_smooth.mul shearAmplitude_smooth

/-- The energy has no derivative along the flow direction. -/
theorem shearEnergy_spatial (z : Vec3 × ℝ) (j : Fin 3) :
    spatialPartial shearEnergy j z =
      if j = 1 then 2 * (shearAmplitude z * shearSlope z) else 0 := by
  change spatialPartial (fun w : Vec3 × ℝ => shearAmplitude w * shearAmplitude w) j z = _
  rw [spatial_mul shearAmplitude_smooth shearAmplitude_smooth]
  rw [shearAmplitude_spatial]
  by_cases hj : j = 1
  · simp only [hj, ite_true]
    ring
  · simp [hj]

/-- Time derivative of the energy density. -/
theorem shearEnergy_time (z : Vec3 × ℝ) :
    timePartial shearEnergy z = -2 * shearEnergy z := by
  change timePartial (fun w : Vec3 × ℝ => shearAmplitude w * shearAmplitude w) z = _
  rw [time_mul shearAmplitude_smooth shearAmplitude_smooth, shearAmplitude_time]
  unfold shearEnergy
  ring

/-- The cubic transport also has zero flow-direction derivative. -/
theorem shearTransport_spatial_zero (z : Vec3 × ℝ) :
    spatialPartial shearTransport 0 z = 0 := by
  change spatialPartial (fun w : Vec3 × ℝ => shearEnergy w * shearAmplitude w) 0 z = _
  rw [spatial_mul shearEnergy_smooth shearAmplitude_smooth,
    shearEnergy_spatial, shearAmplitude_spatial]
  norm_num

/-- Second spatial derivatives of the energy density. -/
theorem shearEnergy_second (z : Vec3 × ℝ) (j : Fin 3) :
    spatialPartial (fun w : Vec3 × ℝ => spatialPartial shearEnergy j w) j z =
      if j = 1 then 2 * (shearSlope z * shearSlope z - shearEnergy z) else 0 := by
  have he : (fun w : Vec3 × ℝ => spatialPartial shearEnergy j w) =
      (fun w : Vec3 × ℝ => if j = 1 then 2 * (shearAmplitude w * shearSlope w) else 0) := by
    funext w
    exact shearEnergy_spatial w j
  rw [he]
  by_cases hj : j = 1
  · subst j
    simp only [ite_true]
    rw [spatial_mul contDiff_const (shearAmplitude_smooth.mul shearSlope_smooth),
      spatial_mul shearAmplitude_smooth shearSlope_smooth,
      shearAmplitude_spatial, shearSlope_spatial]
    simp only [spatialPartial, fderiv_const_apply, zero_apply, zero_mul,
      zero_add, ite_true]
    unfold shearEnergy
    ring
  · simp [hj, spatialPartial]

/-- The squared Euclidean speed is the scalar energy. -/
theorem shearFlow_energy (z : ParabolicPoint) :
    vec3EuclideanNorm (shearFlow z) ^ 2 = shearEnergy z := by
  unfold vec3EuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _hi => sq_nonneg _)]
  simp [shearFlow, shearEnergy, shearAmplitude, pow_two]

/-- The squared gradient density is the squared transverse slope. -/
theorem shearFlow_gradientSq (z : ParabolicPoint) :
    spatialGradientSq shearFlow shearFlowGrad z = shearSlope z * shearSlope z := by
  simp [spatialGradientSq, shearFlowGrad, Fin.sum_univ_three, shearSlope, pow_two]

end CKN
