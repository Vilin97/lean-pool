/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureMean
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarClassical
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarPrimitive
import LeanPool.NavierStokesAndEuler.Euler.CylinderRawSupport
import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarRepresentative

/-!
# The actual normalized pressure in the transverse forward equation

The scalar L² primitive and the literal periodic integral are identified.
Its angular derivative closes equation (11) for the constructed physical
field. The pressure is smooth in the cylinder variables, has zero angular
mean, and retains the same spatial support.
-/

@[expose] public section


noncomputable section

namespace EulerSourceCylinderEquation

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerCylinderScalarPrimitive
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported P Space S hS)) (a₀ : Supported P U S hS)
  (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖ ^ 2)

/-- The actual bounded angular inverse applied to the solved scalar source. -/
def pressurePath : C(Icc (0 : ℝ) T,CylinderL2 P ℝ) :=
  pathPrimitive P (includePath P S hS
    (pressureSource P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm))

theorem pressurePath_contDiff (hSc : IsCompact S)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (includePath P S hS f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a (a₀ : CylinderL2 P U))) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a
      (pressurePath P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm)) :=
  pathPrimitive_orbit_contDiff P _
    (pressureSource_contDiff P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm hSc hf ha₀)

end EulerSourceCylinderEquation

namespace EulerSourceCylinderClassical

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerSourceCylinderEquation EulerCylinderSmoothOrbit EulerCylinderAngleAverage
  EulerCylinderScalarPrimitive EulerMetricTransport
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (hSc : IsCompact S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported P Space S hS)) (a₀ : Supported P U S hS)
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (includePath P S hS f)))
  (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a (a₀ : CylinderL2 P U)))
  (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖ ^ 2)
  (hf₀ : ∀ t, average P (f t : CylinderL2 P Space) = 0)
  (ha₀zero : average P (a₀ : CylinderL2 P U) = 0)

/-- The literal normalized periodic pressure for the actual forward solution. -/
def pressureField (t : Icc (0 : ℝ) T) : LiftDomain P → ℝ :=
  classicalPrimitive P
    (normalResidual P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t)
    (normalResidual_continuous P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m
      (normal_ne_zero_of_lower T m cm hcm hm) t)
    (normalResidual_mean_zero P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t)

theorem pressureField_ae (t : Icc (0 : ℝ) T) :
    (pressurePath P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t : LiftDomain P → ℝ) =ᵐ[liftMeasure
        P]
      pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t :=
  primitive_ae_constructed P _
    (pressureSource_slice_contDiff P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm hSc hf ha₀ t)
    _ (normalResidual_continuous P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m
      (normal_ne_zero_of_lower T m cm hcm hm) t)
    (pressureSource_ae_normalResidual P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm t)
    (normalResidual_mean_zero P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t)

/-- The derivative is genuine at every real angle, including period endpoints. -/
theorem pressureField_angle (t : Icc (0 : ℝ) T) (y : Space) (θ : ℝ) :
    HasDerivAt (fun s : ℝ =>
      pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t (y,(s :
          AddCircle P)))
      (normalResidual P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t (y,(θ : AddCircle P))) θ :=
  classicalPrimitive_angle P _ _ _ y θ

theorem pressureField_mean_zero (t : Icc (0 : ℝ) T) (y : Space) :
    (∫ θ in (0 : ℝ)..P,
      pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t (y,(θ :
          AddCircle P))) = 0 :=
  classicalPrimitive_mean_zero P _ _ _ y

theorem pressureField_smooth (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P
      (pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t) x) :=
  classicalPrimitive_smooth P _ _ _
    (normalResidual_smooth P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m
      (normal_ne_zero_of_lower T m cm hcm hm) t) x

theorem pressureField_continuous (t : Icc (0 : ℝ) T) :
    Continuous (pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t)
        :=
  smoothField_continuous P _
    (pressureField_smooth P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t)

theorem normalResidual_zero_outside (t : Icc (0 : ℝ) T) (y : Space) (hy : y ∉ S)
    (θ : AddCircle P) :
    normalResidual P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t (y,θ) = 0 := by
  have hforce : pointField P (includePath P S hS f) hf t (y,θ) = 0 := by
    rw [pointField_eq_representative]
    exact representative_zero_outside P S hS hSc.isClosed _ _ (f t).property (y,θ) hy
  have hv : field P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t (y,θ) = 0 := by
    by_contra h
    exact hy (field_tsupport_subset P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t (subset_closure h))
  simp only [normalResidual, hforce, hv, map_zero, inner_zero_right, mul_zero, sub_self, zero_div]

theorem pressureField_zero_outside (t : Icc (0 : ℝ) T) (y : Space) (hy : y ∉ S)
    (θ : AddCircle P) :
    pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t (y,θ) = 0 :=
  classicalPrimitive_zero P _ _ _ y
    (normalResidual_zero_outside P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t y hy) θ

theorem pressureField_tsupport_subset (t : Icc (0 : ℝ) T) :
    tsupport (pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t) ⊆
      spatialSet P S := by
  apply closure_minimal _ (hSc.isClosed.preimage continuous_fst)
  intro x hx
  by_contra hn
  exact hx (pressureField_zero_outside P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm
    hf₀ ha₀zero t x.1 hn x.2)

theorem pressureField_hasCompactSupport (t : Icc (0 : ℝ) T) :
    HasCompactSupport (pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀
        ha₀zero t) := by
  have hcompact : IsCompact (spatialSet P S) := by
    have he : spatialSet P S = S ×ˢ (univ : Set (AddCircle P)) := by
      ext x
      simp only [spatialSet,mem_preimage,mem_prod,mem_univ,and_true]
    rw [he]
    exact hSc.prod isCompact_univ
  exact hcompact.of_isClosed_subset (isClosed_tsupport _)
    (pressureField_tsupport_subset P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀
        ha₀zero t)

/-- Equation (11) with the actual angular derivative of the normalized pressure. -/
theorem field_pressure_equation
    (hTangent : ∀ t x v, ⟪m.field t x, Q.field t x v⟫_ℝ = 0)
    (hRange : ∀ t x η, ⟪m.field t x, η⟫_ℝ = 0 → ∃ v, Q.field t x v = η)
    (hFlow : ∀ t x, Q₁.field t x = (M.field t x).comp (Q.field t x))
    (t : Icc (0 : ℝ) T) (y : Space) (θ : ℝ) :
    derivativeField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t (y,(θ : AddCircle P)) +
      M.field t y (field P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t (y,(θ : AddCircle P))) +
      deriv (fun s : ℝ => pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm
        hf₀ ha₀zero t (y,(s : AddCircle P))) θ • m.field t y =
      pointField P (includePath P S hS f) hf t (y,(θ : AddCircle P)) := by
  rw [(pressureField_angle P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t y
      θ).deriv]
  exact field_balance P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m
    (normal_ne_zero_of_lower T m cm hcm hm) hTangent hRange hFlow t (y,(θ : AddCircle P))

end EulerSourceCylinderClassical
