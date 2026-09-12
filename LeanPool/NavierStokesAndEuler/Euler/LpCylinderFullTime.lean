/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular
import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldTimeDerivative
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Genuine time derivatives for the full-cylinder rectangular products. -/

@[expose] public section


noncomputable section

namespace EulerLpCylinderRectangular

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerVolterraConvolution
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (T : ℝ) (hT : 0 ≤ T)
  (A A₁ : C(Icc (0 : ℝ) T, Space →ᵇ E →L[ℝ] F))

/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderFullTime1 : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderFullTime2 : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ E →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderFullTime3 : NormedAddCommGroup (Space →ᵇ E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ E →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderFullTime4 : NormedSpace ℝ (Space →ᵇ E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P E)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderFullTime5 : NormedAddCommGroup (CylinderL2 P E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P E)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderFullTime6 : NormedSpace ℝ (CylinderL2 P E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P F)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderFullTime7 : NormedAddCommGroup (CylinderL2 P F) := inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P F)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderFullTime8 : NormedSpace ℝ (CylinderL2 P F) := inferInstance

variable
  (hA : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath T hT A s x)
      (extendPath T hT A₁ t x) (Icc (0 : ℝ) T) t)

include hA

theorem fullPath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (fullPathMap P A))
      (fullPathMap P A₁ t) (Icc (0 : ℝ) T) t := by
  have hfield := EulerBoundedFieldTimeDerivative.hasDerivWithinAt T hT A A₁ hA t t.property
  have hlinear : HasFDerivAt
      (fun B : Space →ᵇ E →L[ℝ] F => fullOperatorMap P B)
      (fullOperatorMap P) (extendPath T hT A t) :=
    (fullOperatorMap P).hasFDerivAt
  have hd := hlinear.comp_hasDerivWithinAt (t : ℝ) hfield
  change HasDerivWithinAt (fun s => fullOperatorMap P (A (projIcc 0 T hT s)))
    (fullOperatorMap P (A₁ t)) (Icc (0 : ℝ) T) t
  change HasDerivWithinAt (fun s => fullOperatorMap P (A (projIcc 0 T hT s)))
    (fullOperatorMap P (A₁ (projIcc 0 T hT t))) (Icc (0 : ℝ) T) t at hd
  rwa [projIcc_of_mem hT t.property] at hd

theorem fullProduct_hasDerivWithinAt
    (u u₁ : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hu : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT u) (u₁ t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (fullMultiplierMap P A u))
      (fullMultiplierMap P A₁ u t + fullMultiplierMap P A u₁ t)
      (Icc (0 : ℝ) T) t := by
  have hd := (fullPath_hasDerivWithinAt P T hT A A₁ hA t).clm_apply (hu t)
  change HasDerivWithinAt
    (fun s => fullOperatorMap P (A (projIcc 0 T hT s)) (u (projIcc 0 T hT s)))
    (fullOperatorMap P (A₁ t) (u t) + fullOperatorMap P (A t) (u₁ t))
    (Icc (0 : ℝ) T) t
  change HasDerivWithinAt
    (fun s => fullOperatorMap P (A (projIcc 0 T hT s)) (u (projIcc 0 T hT s)))
    (fullOperatorMap P (A₁ t) (u (projIcc 0 T hT t)) +
      fullOperatorMap P (A (projIcc 0 T hT t)) (u₁ t))
    (Icc (0 : ℝ) T) t at hd
  rwa [projIcc_of_mem hT t.property] at hd

end EulerLpCylinderRectangular
