/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficients

@[expose] public section

/-!
# Actual coefficient time derivatives on the cylinder

The rectangular multipliers agree with the square operators used in the
constructed Duhamel evolution. Literal within-time derivatives of the
coefficient fields induce true operator-path derivatives and product rules.
-/

noncomputable section

namespace EulerLpCylinderRectangular

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderCoefficients
  EulerVolterraConvolution
open scoped BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]

section Square

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (S : Set Space) (hS : MeasurableSet S)

/-- The two literal constructions are the same actual supported L² operator. -/
theorem supportedOperator_eq_square (A : Space →ᵇ V →L[ℝ] V) :
    supportedOperatorMap period S hS A = liftedOperator period S hS A := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period A)
      (u : CylinderL2 period V),
    EulerLpSupportedMultiplier.full_ae (liftMeasure period) (fieldLift period A)
      (u : CylinderL2 period V)] with x hl hr
  exact hl.trans hr.symm

theorem supportedPath_eq_square (T : ℝ) (A : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V)) :
    supportedPathMap period S hS A = liftedOperatorPath period S hS T A := by
  apply ContinuousMap.ext
  intro t
  exact supportedOperator_eq_square period S hS (A t)

end Square

section Time

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (A A₁ : C(Icc (0 : ℝ) T,Space →ᵇ E →L[ℝ] F))

private local instance : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (Supported period E S hS) := inferInstance
private local instance : NormedSpace ℝ (Supported period E S hS) := inferInstance
private local instance : NormedAddCommGroup (Supported period F S hS) := inferInstance
private local instance : NormedSpace ℝ (Supported period F S hS) := inferInstance
private local instance : NormedAddCommGroup (Supported period E S hS →L[ℝ] Supported period F S hS)
  := inferInstance
private local instance : NormedSpace ℝ (Supported period E S hS →L[ℝ] Supported period F S hS) :=
  inferInstance

variable (hA : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
  HasDerivWithinAt (fun s => extendPath T hT A s x)
    (extendPath T hT A₁ t x) (Icc (0 : ℝ) T) t)

include hA in
/-- The true derivative of the actual supported coefficient operator. -/
theorem supportedPath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (supportedPathMap period S hS A))
      (supportedPathMap period S hS A₁ t) (Icc (0 : ℝ) T) t := by
  have hfield := EulerBoundedFieldTimeDerivative.hasDerivWithinAt T hT A A₁ hA t t.property
  have hlinear : HasFDerivAt
      (fun B : Space →ᵇ E →L[ℝ] F => supportedOperatorMap period S hS B)
      (supportedOperatorMap period S hS) (extendPath T hT A t) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Space →ᵇ E →L[ℝ] F)
      (F := Supported period E S hS →L[ℝ] Supported period F S hS)
      (supportedOperatorMap period S hS)
  have hd := hlinear.comp_hasDerivWithinAt (t : ℝ) hfield
  change HasDerivWithinAt (fun s => supportedOperatorMap period S hS (A (projIcc 0 T hT s)))
    (supportedOperatorMap period S hS (A₁ t)) (Icc (0 : ℝ) T) t
  change HasDerivWithinAt (fun s => supportedOperatorMap period S hS (A (projIcc 0 T hT s)))
    (supportedOperatorMap period S hS (A₁ (projIcc 0 T hT t))) (Icc (0 : ℝ) T) t at hd
  rwa [projIcc_of_mem hT t.property] at hd

include hA in
/-- The product rule is a genuine within-time statement, including the interval endpoints. -/
theorem supportedProduct_hasDerivWithinAt
    (u u₁ : C(Icc (0 : ℝ) T,Supported period E S hS))
    (hu : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT u) (u₁ t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (supportedMultiplierMap period S hS A u))
      (supportedMultiplierMap period S hS A₁ u t + supportedMultiplierMap period S hS A u₁ t)
      (Icc (0 : ℝ) T) t := by
  have hd := (supportedPath_hasDerivWithinAt period S hS T hT A A₁ hA t).clm_apply (hu t)
  dsimp only [extendPath] at hd
  simp only [projIcc_of_mem hT t.property] at hd
  exact hd

end Time

end EulerLpCylinderRectangular
