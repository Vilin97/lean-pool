/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseSourceCoefficientPath

/-! Uniform label difference estimates from genuine coefficient derivatives. -/

@[expose] public section


noncomputable section

namespace EulerPacketActivationHistory
open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseSourceCoefficientPath
open scoped BoundedContinuousFunction

section Coefficients

variable {T : ℝ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cache the standard `NormedAddCommGroup (Space →ᵇ V)` instance to shorten typeclass
synthesis. -/
local instance instPacketCoefficientLipschitz1 : NormedAddCommGroup (Space →ᵇ V) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ V)` instance to shorten typeclass synthesis. -/
local instance instPacketCoefficientLipschitz2 : NormedSpace ℝ (Space →ᵇ V) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,Space →ᵇ V)` instance to shorten
typeclass synthesis. -/
local instance instPacketCoefficientLipschitz3 : NormedAddCommGroup C(Icc (0 : ℝ) T,Space →ᵇ V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,Space →ᵇ V)` instance to shorten typeclass
synthesis. -/
local instance instPacketCoefficientLipschitz4 : NormedSpace ℝ C(Icc (0 : ℝ) T,Space →ᵇ V) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instPacketCoefficientLipschitz5 : NormedAddCommGroup (Space →L[ℝ] V) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instPacketCoefficientLipschitz6 : NormedSpace ℝ (Space →L[ℝ] V) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ (Space →L[ℝ] V))` instance to shorten
typeclass synthesis. -/
local instance instPacketCoefficientLipschitz7 : NormedAddCommGroup (Space →ᵇ (Space →L[ℝ] V)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ (Space →L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instPacketCoefficientLipschitz8 : NormedSpace ℝ (Space →ᵇ (Space →L[ℝ] V)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,Space →ᵇ (Space →L[ℝ] V))` instance
to shorten typeclass synthesis. -/
local instance instPacketCoefficientLipschitz9 : NormedAddCommGroup C(Icc (0 : ℝ) T,Space →ᵇ (Space
    →L[ℝ] V)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,Space →ᵇ (Space →L[ℝ] V))` instance to
shorten typeclass synthesis. -/
local instance instPacketCoefficientLipschitz10 : NormedSpace ℝ C(Icc (0 : ℝ) T,Space →ᵇ (Space
    →L[ℝ] V)) := inferInstance

theorem coefficient_label_norm (A : SmoothCoefficientPath (Icc (0 : ℝ) T) V) (x : Space) :
    ‖pathEvaluation x A.field‖ ≤ ‖A.field‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  exact ((A.field t).norm_coe_le_norm x).trans (A.field.norm_coe_le_norm t)

theorem coefficient_difference (A : SmoothCoefficientPath (Icc (0 : ℝ) T) V)
    (t : Icc (0 : ℝ) T) (x y : Space) :
    ‖A.field t x-A.field t y‖ ≤ ‖A.derivative.field‖*‖x-y‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (s := Set.univ) (fun z _ => (A.smooth t).differentiable (by simp) z)
    (fun z _ => ?_) (convex_univ : Convex ℝ (Set.univ : Set Space)) (mem_univ y) (mem_univ x)
  rw [← A.derivativeField_eq]
  exact ((A.derivative.field t).norm_coe_le_norm z).trans (A.derivative.field.norm_coe_le_norm t)

theorem coefficient_label_difference (A : SmoothCoefficientPath (Icc (0 : ℝ) T) V)
    (x y : Space) :
    ‖pathEvaluation x A.field-pathEvaluation y A.field‖ ≤ ‖A.derivative.field‖*‖x-y‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro t
  exact coefficient_difference A t x y

end Coefficients

end EulerPacketActivationHistory
