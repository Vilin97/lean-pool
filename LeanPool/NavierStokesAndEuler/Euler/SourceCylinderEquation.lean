/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderForward
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderForcing
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficientTime
import LeanPool.NavierStokesAndEuler.Euler.TransverseNormalResidual

/-!
# The actual source forward equation on cylinder L²

The coordinate path is the constructed Duhamel integral with the genuine
Gram-projected forcing. Its physical velocity has the true within-time
derivative. The projected equation and normal pressure balance are derived
on the actual L² representatives, not assumed as properties of a solver.
-/

@[expose] public section


noncomputable section

namespace EulerSourceCylinderEquation

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
    EulerLiftedGradientSpace
  EulerMeanCoefficients EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderCoefficients
  EulerLpCylinderRectangular EulerSourceForwardCoefficient EulerSourceCylinderForcing
  EulerSourceCylinderForward EulerLinearDuhamel EulerTransverseGramInverse
      EulerTransverseNormalResidual
  EulerVolterraConvolution
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported period E S hS)) (a₀ : Supported period U S hS)

/-- Cache the standard `NormedAddCommGroup (Supported period U S hS)` instance to shorten
typeclass synthesis. -/
local instance instSourceCylinderEquation1 : NormedAddCommGroup (Supported period U S hS) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Supported period U S hS)` instance to shorten typeclass
synthesis. -/
local instance instSourceCylinderEquation2 : NormedSpace ℝ (Supported period U S hS) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Supported period E S hS)` instance to shorten
typeclass synthesis. -/
local instance instSourceCylinderEquation3 : NormedAddCommGroup (Supported period E S hS) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Supported period E S hS)` instance to shorten typeclass
synthesis. -/
local instance instSourceCylinderEquation4 : NormedSpace ℝ (Supported period E S hS) :=
    inferInstance

/-- The actual unnormalized coordinate solution; no regularity of a profile g is needed. -/
def coordinates : C(Icc (0 : ℝ) T,Supported period U S hS) :=
  (evolution period T hT Q Q₁ c hc hQ S hS).solution (projectedForcing period S hS Q c hc hQ f) a₀

/-- Its actual ordinary right side. -/
def coordinateDerivative : C(Icc (0 : ℝ) T,Supported period U S hS) :=
  supportedMultiplierMap period S hS (sourceGenerator Q Q₁ c hc hQ)
    (coordinates period S hS T hT Q Q₁ c hc hQ f a₀) + projectedForcing period S hS Q c hc hQ f

/-- The physical transverse velocity A=Q a. -/
def velocity : C(Icc (0 : ℝ) T,Supported period E S hS) :=
  physicalVelocity period S hS Q (coordinates period S hS T hT Q Q₁ c hc hQ f a₀)

/-- Its literal product-rule expression, proved below to be the time derivative. -/
def velocityDerivative : C(Icc (0 : ℝ) T,Supported period E S hS) :=
  supportedMultiplierMap period S hS Q₁.field (coordinates period S hS T hT Q Q₁ c hc hQ f a₀) +
    supportedMultiplierMap period S hS Q.field (coordinateDerivative period S hS T hT Q Q₁ c hc hQ
        f a₀)

@[simp] theorem coordinates_initial :
    coordinates period S hS T hT Q Q₁ c hc hQ f a₀ ⟨0,le_rfl,hT⟩ = a₀ :=
  (evolution period T hT Q Q₁ c hc hQ S hS).solution_initial _ _

/-- The coordinate equation has its true derivative on the closed time interval. -/
theorem coordinates_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (coordinates period S hS T hT Q Q₁ c hc hQ f a₀))
      (coordinateDerivative period S hS T hT Q Q₁ c hc hQ f a₀ t) (Icc (0 : ℝ) T) t := by
  have hd := (evolution period T hT Q Q₁ c hc hQ S hS).solution_derivative
    (projectedForcing period S hS Q c hc hQ f) a₀ t
  have hB := congrArg (fun A => A t)
    (supportedPath_eq_square period S hS T (sourceGenerator Q Q₁ c hc hQ))
  change supportedOperatorMap period S hS (sourceGenerator Q Q₁ c hc hQ t) =
    liftedOperatorPath period S hS T (sourceGenerator Q Q₁ c hc hQ) t at hB
  change HasDerivWithinAt _
    (liftedOperatorPath period S hS T (sourceGenerator Q Q₁ c hc hQ) t
      (coordinates period S hS T hT Q Q₁ c hc hQ f a₀ t) +
      projectedForcing period S hS Q c hc hQ f t) (Icc (0 : ℝ) T) t at hd
  rw [← hB] at hd
  apply hd.congr_of_mem _ t.property
  intro s hs
  simp only [extendPath,projIcc_of_mem hT hs]
  rfl

/-- Literal coefficient time derivatives induce the genuine physical time derivative. -/
theorem velocity_hasDerivWithinAt
    (hQt : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath T hT Q.field s x)
        (extendPath T hT Q₁.field t x) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (velocity period S hS T hT Q Q₁ c hc hQ f a₀))
      (velocityDerivative period S hS T hT Q Q₁ c hc hQ f a₀ t) (Icc (0 : ℝ) T) t :=
  supportedProduct_hasDerivWithinAt period S hS T hT Q.field Q₁.field hQt
    (coordinates period S hS T hT Q Q₁ c hc hQ f a₀)
    (coordinateDerivative period S hS T hT Q Q₁ c hc hQ f a₀)
    (coordinates_hasDerivWithinAt period S hS T hT Q Q₁ c hc hQ f a₀) t

/-- The genuine L² representatives satisfy the projected source equation (12). -/
theorem coordinate_equation_ae (t : Icc (0 : ℝ) T) :
    ∀ᵐ x ∂liftMeasure period,
      gram (Q.field t x.1) ((coordinateDerivative period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2
          period U) x) =
        (Q.field t x.1).adjoint ((f t : CylinderL2 period E) x - (2 : ℝ) •
          Q₁.field t x.1 ((coordinates period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period U)
              x)) := by
  let u := coordinates period S hS T hT Q Q₁ c hc hQ f a₀ t
  let B := sourceGenerator Q Q₁ c hc hQ t
  let P := sourceForcing Q c hc hQ t
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period B) (u :
      CylinderL2 period U),
    EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period P) (f t : CylinderL2 period
        E),
    Lp.coeFn_add (fullOperatorMap period B (u : CylinderL2 period U))
      (fullOperatorMap period P (f t : CylinderL2 period E))] with x hB hP hs
  change gram (Q.field t x.1)
      ((fullOperatorMap period B (u : CylinderL2 period U) +
        fullOperatorMap period P (f t : CylinderL2 period E)) x) = _
  rw [hs]
  simp only [Pi.add_apply,fullOperatorMap_apply]
  rw [hB,hP]
  change gram (Q.field t x.1) ((-2 : ℝ) • gramInverse (Q.field t x.1) c hc (hQ t x.1)
      ((Q.field t x.1).adjoint (Q₁.field t x.1 ((u : CylinderL2 period U) x))) +
    gramInverse (Q.field t x.1) c hc (hQ t x.1) ((Q.field t x.1).adjoint ((f t : CylinderL2 period
        E) x))) = _
  rw [map_add,map_smul,gram_inverse_apply,gram_inverse_apply,map_sub,map_smul]
  module

/-- The physical velocity's representative is exactly Q times the solved coordinate. -/
theorem velocity_ae (t : Icc (0 : ℝ) T) :
    (velocity period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period E) =ᵐ[liftMeasure period]
      fun x => Q.field t x.1 ((coordinates period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period
          U) x) :=
  EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period (Q.field t)) _

theorem velocityDerivative_ae (t : Icc (0 : ℝ) T) :
    (velocityDerivative period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period E) =ᵐ[liftMeasure
        period]
      fun x => Q₁.field t x.1 ((coordinates period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2
          period U) x) +
        Q.field t x.1 ((coordinateDerivative period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2
            period U) x) := by
  let u := coordinates period S hS T hT Q Q₁ c hc hQ f a₀ t
  let a := coordinateDerivative period S hS T hT Q Q₁ c hc hQ f a₀ t
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period (Q₁.field t))
      (u : CylinderL2 period U),
    EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period (Q.field t)) (a :
        CylinderL2 period U),
    Lp.coeFn_add (fullOperatorMap period (Q₁.field t) (u : CylinderL2 period U))
      (fullOperatorMap period (Q.field t) (a : CylinderL2 period U))] with x h₁ h₂ hs
  exact hs.trans (congrArg₂ (·+·) h₁ h₂)

/-- Equation (11)'s literal normal residual follows from the actual coordinate solve. -/
theorem velocity_balance_ae
    (M : Icc (0 : ℝ) T → Space → E →L[ℝ] E) (m : Icc (0 : ℝ) T → Space → E)
    (hm : ∀ t x, m t x ≠ 0)
    (hTangent : ∀ t x v, ⟪m t x, Q.field t x v⟫_ℝ = 0)
    (hRange : ∀ t x η, ⟪m t x, η⟫_ℝ = 0 → ∃ v, Q.field t x v = η)
    (hFlow : ∀ t x, Q₁.field t x = (M t x).comp (Q.field t x))
    (t : Icc (0 : ℝ) T) :
    ∀ᵐ x ∂liftMeasure period,
      (velocityDerivative period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period E) x +
        M t x.1 ((velocity period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period E) x) +
        ((⟪m t x.1,(f t : CylinderL2 period E) x⟫_ℝ - 2*⟪m t x.1,
          M t x.1 ((velocity period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period E) x)⟫_ℝ) /
            ‖m t x.1‖^2) • m t x.1 = (f t : CylinderL2 period E) x := by
  filter_upwards [coordinate_equation_ae period S hS T hT Q Q₁ c hc hQ f a₀ t,
    velocity_ae period S hS T hT Q Q₁ c hc hQ f a₀ t,
    velocityDerivative_ae period S hS T hT Q Q₁ c hc hQ f a₀ t] with x he hv hd
  rw [hv,hd]
  exact physical_velocity_balance (Q.field t x.1) (Q₁.field t x.1) (M t x.1) (m t x.1)
    (hm t x.1) (hTangent t x.1) (hRange t x.1) (hFlow t x.1) _ _ _ he

end EulerSourceCylinderEquation
