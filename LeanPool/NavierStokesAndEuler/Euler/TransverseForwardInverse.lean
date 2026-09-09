/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelOperator
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramPath
public import LeanPool.NavierStokesAndEuler.Euler.TransverseNormalResidual

@[expose] public section

/-!
# The actual forward transverse initial value problem

The matrix coefficient in source equation (12) is formed using the genuinely
constructed Gram inverse. Given the homogeneous evolution assumed in (H3),
Duhamel's integral constructs the forced coordinate and physical velocity.
The coordinate equation, tangency, initial trace and physical pressure balance
are proved at every time, including within-interval endpoint derivatives.
-/

noncomputable section


namespace EulerTransverseForwardInverse

open Set InnerProductSpace ContinuousLinearMap EulerVolterraConvolution
  EulerTransverseGramInverse EulerTransverseGramPath EulerTransverseNormalResidual
  EulerContinuousTimeIntegral EulerLinearDuhamel

variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T,V →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c*‖v‖^2 ≤ ‖Q t v‖^2)

/-- The actual ordinary coefficient `-2 K⁻¹ Q* Q₁` in equation (12). -/
def generator : C(Icc (0 : ℝ) T,V →L[ℝ] V) :=
  ⟨fun t => (-2 : ℝ) • (gramInversePath T Q c hc hQ t).comp ((Q t).adjoint.comp (Q₁ t)),
    ((gramInversePath T Q c hc hQ).continuous.clm_comp
      ((adjointPath T Q).continuous.clm_comp Q₁.continuous)).const_smul (-2 : ℝ)⟩

/-- The actual projected forcing `K⁻¹ Q* f`, as a bounded continuous-path map. -/
def forcingOperator : C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,V) :=
  multiplier (frameLeftInversePath T Q c hc hQ)

variable (U : Evolution T hT (generator T Q Q₁ c hc hQ))

/-- The forward coordinate is the actual forced Duhamel path. -/
def coordinates (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) : C(Icc (0 : ℝ) T,V) :=
  U.solution (forcingOperator T Q c hc hQ f) a₀

/-- Its derivative is the literal ordinary right hand side. -/
def coordinateDerivative (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) : C(Icc (0 : ℝ) T,V) :=
  multiplier (generator T Q Q₁ c hc hQ) (coordinates T hT Q Q₁ c hc hQ U f a₀) +
    forcingOperator T Q c hc hQ f

/-- The physical velocity `A=Qa` is an actual continuous path. -/
def velocity (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) : C(Icc (0 : ℝ) T,E) :=
  multiplier Q (coordinates T hT Q Q₁ c hc hQ U f a₀)

/-- The physical time derivative, with the literal product-rule expression. -/
def velocityDerivative (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) : C(Icc (0 : ℝ) T,E) :=
  multiplier Q₁ (coordinates T hT Q Q₁ c hc hQ U f a₀) +
    multiplier Q (coordinateDerivative T hT Q Q₁ c hc hQ U f a₀)

/-- The constructed coordinate attains the prescribed initial datum. -/
@[simp] theorem coordinates_initial (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) :
    coordinates T hT Q Q₁ c hc hQ U f a₀ ⟨0,le_rfl,hT⟩ = a₀ :=
  U.solution_initial _ _

/-- The actual initial physical velocity is `Q(0)a₀`. -/
@[simp] theorem velocity_initial (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) :
    velocity T hT Q Q₁ c hc hQ U f a₀ ⟨0,le_rfl,hT⟩ = Q ⟨0,le_rfl,hT⟩ a₀ := by
  change Q ⟨0,le_rfl,hT⟩ (coordinates T hT Q Q₁ c hc hQ U f a₀ ⟨0,le_rfl,hT⟩) = _
  rw [coordinates_initial]

/-- Every-time coordinate differentiability follows from the actual integral,
not from an assumed derivative representative. -/
theorem coordinates_hasDerivWithinAt (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (coordinates T hT Q Q₁ c hc hQ U f a₀))
      (coordinateDerivative T hT Q Q₁ c hc hQ U f a₀ t) (Icc (0 : ℝ) T) t := by
  have hd := U.solution_derivative (forcingOperator T Q c hc hQ f) a₀ t
  apply hd.congr_of_mem _ t.property
  intro s hs
  simp only [extendPath, projIcc_of_mem hT hs]
  rfl

/-- The constructed derivative satisfies the literal projected equation (12). -/
theorem coordinate_equation (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) (t : Icc (0 : ℝ) T) :
    gram (Q t) (coordinateDerivative T hT Q Q₁ c hc hQ U f a₀ t) =
      (Q t).adjoint (f t - (2 : ℝ) • Q₁ t (coordinates T hT Q Q₁ c hc hQ U f a₀ t)) := by
  change gram (Q t) ((-2 : ℝ) • gramInverse (Q t) c hc (hQ t)
      ((Q t).adjoint (Q₁ t (coordinates T hT Q Q₁ c hc hQ U f a₀ t))) +
      gramInverse (Q t) c hc (hQ t) ((Q t).adjoint (f t))) = _
  rw [map_add, map_smul, gram_inverse_apply, gram_inverse_apply, map_sub, map_smul]
  module

/-- Physical velocity is tangent at every time because it lies in the frame range. -/
theorem velocity_tangent (m : Icc (0 : ℝ) T → E)
    (hTangent : ∀ t v, ⟪m t,Q t v⟫_ℝ = 0)
    (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) (t : Icc (0 : ℝ) T) :
    ⟪m t,velocity T hT Q Q₁ c hc hQ U f a₀ t⟫_ℝ = 0 :=
  hTangent t _

/-- The physical product-rule expression is its actual every-time derivative. -/
theorem velocity_hasDerivWithinAt
    (hQd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (velocity T hT Q Q₁ c hc hQ U f a₀))
      (velocityDerivative T hT Q Q₁ c hc hQ U f a₀ t) (Icc (0 : ℝ) T) t := by
  have hd := (hQd t).clm_apply (coordinates_hasDerivWithinAt T hT Q Q₁ c hc hQ U f a₀ t)
  convert hd using 1
  · rfl
  · simp only [extendPath, projIcc_of_mem hT t.property]
    rfl

/-- The literal normal pressure coefficient in source equation (11). -/
def pressureCoefficient (M : Icc (0 : ℝ) T → E →L[ℝ] E) (m : Icc (0 : ℝ) T → E)
    (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) (t : Icc (0 : ℝ) T) : ℝ :=
  (⟪m t,f t⟫_ℝ - 2*⟪m t,M t (velocity T hT Q Q₁ c hc hQ U f a₀ t)⟫_ℝ) / ‖m t‖^2

/-- The actual forward velocity and explicit normal pressure residual satisfy
source equation (11) at every time. -/
theorem velocity_balance (M : Icc (0 : ℝ) T → E →L[ℝ] E) (m : Icc (0 : ℝ) T → E)
    (hm : ∀ t, m t ≠ 0) (hTangent : ∀ t v, ⟪m t,Q t v⟫_ℝ = 0)
    (hRange : ∀ t η, ⟪m t,η⟫_ℝ = 0 → ∃ v, Q t v = η)
    (hflow : ∀ t, Q₁ t = (M t).comp (Q t))
    (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) (t : Icc (0 : ℝ) T) :
    velocityDerivative T hT Q Q₁ c hc hQ U f a₀ t +
      M t (velocity T hT Q Q₁ c hc hQ U f a₀ t) +
      pressureCoefficient T hT Q Q₁ c hc hQ U M m f a₀ t • m t = f t :=
  physical_velocity_balance (Q t) (Q₁ t) (M t) (m t) (hm t) (hTangent t) (hRange t)
    (hflow t) _ _ (f t) (coordinate_equation T hT Q Q₁ c hc hQ U f a₀ t)

/-- The full coordinate solution depends bounded-linearly on initial datum and forcing. -/
def coordinatesOperator : (V × C(Icc (0 : ℝ) T,E)) →L[ℝ] C(Icc (0 : ℝ) T,V) :=
  U.initialOperator.comp (ContinuousLinearMap.fst ℝ V C(Icc (0 : ℝ) T,E)) +
    U.forcingOperator.comp ((forcingOperator T Q c hc hQ).comp
      (ContinuousLinearMap.snd ℝ V C(Icc (0 : ℝ) T,E)))

/-- The bounded linear data map is exactly the constructed coordinate path. -/
theorem coordinatesOperator_apply (f : C(Icc (0 : ℝ) T,E)) (a₀ : V) :
    coordinatesOperator T hT Q Q₁ c hc hQ U (a₀,f) = coordinates T hT Q Q₁ c hc hQ U f a₀ :=
  (U.solution_eq_operators _ _).symm

/-- The physical forward inverse is an actual bounded linear map in its data. -/
def velocityOperator : (V × C(Icc (0 : ℝ) T,E)) →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  (multiplier Q).comp (coordinatesOperator T hT Q Q₁ c hc hQ U)

/-- Zero data give the zero path; this is the pointwise support-preservation mechanism. -/
theorem velocity_zero : velocity T hT Q Q₁ c hc hQ U 0 0 = 0 := by
  have hz := (coordinatesOperator T hT Q Q₁ c hc hQ U).map_zero
  rw [show (0 : V × C(Icc (0 : ℝ) T,E)) = (0,0) from rfl, coordinatesOperator_apply] at hz
  change multiplier Q (coordinates T hT Q Q₁ c hc hQ U 0 0) = 0
  rw [hz, map_zero]

end EulerTransverseForwardInverse
