/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarClassical
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarPrimitive
import LeanPool.NavierStokesAndEuler.Euler.CylinderRawSupport
import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverage
import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarAverage
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderMeanZero
public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderEquation
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficients
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRegularForward

/-!
# The actual normalized pressure in the transverse forward equation

The scalar L² primitive and the literal periodic integral are identified.
Its angular derivative closes equation (11) for the constructed physical
field. The pressure is smooth in the cylinder variables, has zero angular
mean, and retains the same spatial support.
-/

section

/-!
# Genuine mixed regularity of the solved physical forward fields

The actual coordinate solve and its ordinary right side have smooth mixed
translation orbits. Applying the physical frame then gives this same
regularity for the velocity and its true time derivative. These statements
are proved from the data, not included in the solution interface.
-/

section

/-! Actual unnormalized forward solutions have smooth mixed translation orbits. -/

@[expose] public section

noncomputable section

namespace EulerLpCylinderRegularForward

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderCoefficients
  EulerMeanCoefficients EulerLinearDuhamel EulerContinuousTimeWeight
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (T : ℝ) (hT : 0 ≤ T) (S : Set Space) (hS : MeasurableSet S) (hSc : IsCompact S)
  (B : C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))
  (f : C(Icc (0 : ℝ) T, Supported period V S hS)) (a₀ : Supported period V S hS)

include hSc hB in
/-- The constructed unnormalized path is genuinely smooth in all covering parameters.
This qualitative statement needs no propagator bound or smoothness of a time profile. -/
theorem unweighted_solution_contDiff
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period V))) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      ((constructedEvolution period S hS T hT B).solution f a₀))) := by
  let g : C(Icc (0 : ℝ) T,ℝ) := 1
  have hg : ∀ t, 0 < g t := fun _ => zero_lt_one
  have hw : weight g f = f := by
    apply ContinuousMap.ext
    intro t
    change (1 : ℝ) • f t = f t
    exact one_smul ℝ (f t)
  have he : (constructedEvolution period S hS T hT B).weightedSolution g hg f a₀ =
      (constructedEvolution period S hS T hT B).solution f a₀ := by
    change normalize g hg ((constructedEvolution period S hS T hT B).solution (weight g f) a₀) = _
    rw [hw]
    apply ContinuousMap.ext
    intro t
    change (1 : ℝ)⁻¹ • ((constructedEvolution period S hS T hT B).solution f a₀ t) =
      (constructedEvolution period S hS T hT B).solution f a₀ t
    rw [inv_one,one_smul]
  have h := source_solution_contDiff period T hT univ MeasurableSet.univ B hB
    S hS hSc isOpen_univ (subset_univ S) g hg f a₀ hf ha₀
  rwa [he] at h

end EulerLpCylinderRegularForward

end
end

end

@[expose] public section

noncomputable section

namespace EulerSourceCylinderEquation

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerSourceForwardCoefficient EulerSourceCylinderForcing
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (hSc : IsCompact S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported period E S hS)) (a₀ : Supported period U S hS)
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
  (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period U)))

include hSc hf ha₀

theorem coordinates_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (coordinates period S hS T hT Q Q₁ c hc hQ f a₀))) :=
  EulerLpCylinderRegularForward.unweighted_solution_contDiff period T hT S hS hSc
    (sourceGenerator Q Q₁ c hc hQ) (sourceGenerator_translation_contDiff Q Q₁ c hc hQ)
    (projectedForcing period S hS Q c hc hQ f) a₀
    (projectedForcing_contDiff period S hS Q c hc hQ f hf) ha₀

theorem coordinateDerivative_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (coordinateDerivative period S hS T hT Q Q₁ c hc hQ f a₀))) := by
  have hu := coordinates_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀
  have hp := supported_product_orbit_contDiff period (sourceGenerator Q Q₁ c hc hQ)
    (sourceGenerator_translation_contDiff Q Q₁ c hc hQ) S hS
    (coordinates period S hS T hT Q Q₁ c hc hQ f a₀) hu
  have hpf := projectedForcing_contDiff period S hS Q c hc hQ f hf
  simpa only [coordinateDerivative,map_add] using hp.add hpf

theorem velocity_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (velocity period S hS T hT Q Q₁ c hc hQ f a₀))) :=
  physicalVelocity_contDiff period S hS Q (coordinates period S hS T hT Q Q₁ c hc hQ f a₀)
    (coordinates_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀)

theorem velocityDerivative_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (velocityDerivative period S hS T hT Q Q₁ c hc hQ f a₀))) := by
  have hu := coordinates_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀
  have ha := coordinateDerivative_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀
  have h₁ := supported_product_orbit_contDiff period Q₁.field Q₁.translation_contDiff S hS
    (coordinates period S hS T hT Q Q₁ c hc hQ f a₀) hu
  have h₂ := supported_product_orbit_contDiff period Q.field Q.translation_contDiff S hS
    (coordinateDerivative period S hS T hT Q Q₁ c hc hQ f a₀) ha
  simpa only [velocityDerivative,map_add] using h₁.add h₂

end EulerSourceCylinderEquation

end
end

end

section

/-!
# The actual pointwise forward equation

The L² coordinate equation and normal balance hold for the reconstructed
smooth field at every cylinder point. The scalar normal residual is the
literal source expression; its angular primitive will supply the pressure.
-/

section

/-!
# The solved forward field as an actual smooth cylinder field

The representative is recovered by bounded H3 evaluation of the genuine
L² solution. It is jointly continuous, spatially and angularly smooth,
compactly supported, and has the true pointwise within-time derivative.
-/

@[expose] public section

noncomputable section

namespace EulerSourceCylinderClassical

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerMeanCoefficients EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerSourceCylinderEquation EulerCylinderSmoothOrbit EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (hSc : IsCompact S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported period Space S hS)) (a₀ : Supported period U S hS)
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
  (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period U)))

/-- The actual physical field, reconstructed from the solved L² class. -/
def field (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Space :=
  pointField period (includePath period S hS (velocity period S hS T hT Q Q₁ c hc hQ f a₀))
    (velocity_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀) t x

/-- The reconstructed actual product-rule time derivative. -/
def derivativeField (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Space :=
  pointField period (includePath period S hS (velocityDerivative period S hS T hT Q Q₁ c hc hQ f
      a₀))
    (velocityDerivative_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀) t x

theorem field_joint_continuous :
    Continuous (fun z : Icc (0 : ℝ) T × LiftDomain period =>
      field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ z.1 z.2) :=
  pointField_joint_continuous period _ _

theorem field_smooth (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t) x)
        :=
  pointField_smooth period _ _ t x

theorem derivativeField_smooth (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (derivativeField period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf
        ha₀ t) x) :=
  pointField_smooth period _ _ t x

theorem field_ae (t : Icc (0 : ℝ) T) :
    (velocity period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period Space) =ᵐ[liftMeasure period]
      field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t :=
  pointField_ae period (includePath period S hS (velocity period S hS T hT Q Q₁ c hc hQ f a₀))
    (velocity_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀) t

theorem derivativeField_ae (t : Icc (0 : ℝ) T) :
    (velocityDerivative period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period Space)
        =ᵐ[liftMeasure period]
      derivativeField period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t :=
  pointField_ae period (includePath period S hS (velocityDerivative period S hS T hT Q Q₁ c hc hQ f
      a₀))
    (velocityDerivative_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀) t

theorem field_tsupport_subset (t : Icc (0 : ℝ) T) :
    tsupport (field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t) ⊆ spatialSet period S := by
  change tsupport (pointField period _ _ t) ⊆ _
  rw [pointField_eq_representative]
  exact representative_tsupport_subset period S hS hSc.isClosed _ _
    (velocity period S hS T hT Q Q₁ c hc hQ f a₀ t).property

theorem field_hasCompactSupport (t : Icc (0 : ℝ) T) :
    HasCompactSupport (field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t) := by
  change HasCompactSupport (pointField period _ _ t)
  rw [pointField_eq_representative]
  exact representative_hasCompactSupport period S hS hSc _ _
    (velocity period S hS T hT Q Q₁ c hc hQ f a₀ t).property

/-- Inclusion in full cylinder L² preserves the already proved time derivative. -/
theorem fullVelocity_hasDerivWithinAt
    (hQt : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath T hT Q.field s x)
        (extendPath T hT Q₁.field t x) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (includePath period S hS
      (velocity period S hS T hT Q Q₁ c hc hQ f a₀)))
      (includePath period S hS (velocityDerivative period S hS T hT Q Q₁ c hc hQ f a₀) t)
      (Icc (0 : ℝ) T) t := by
  let L : Supported period Space S hS →L[ℝ] LiftL2 period := (Supported period Space S hS).subtypeL
  exact L.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (velocity_hasDerivWithinAt period S hS T hT Q Q₁ c hc hQ f a₀ hQt t)

/-- No global time extension is assumed: the true time derivative holds within
the closed source interval, at every cylinder point. -/
theorem field_hasDerivWithinAt
    (hQt : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath T hT Q.field s x)
        (extendPath T hT Q₁.field t x) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    HasDerivWithinAt (fun s => field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ (projIcc 0 T hT
        s) x)
      (derivativeField period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t x) (Icc (0 : ℝ) T) t :=
  pointField_hasDerivWithinAt period T hT
    (includePath period S hS (velocity period S hS T hT Q Q₁ c hc hQ f a₀))
    (includePath period S hS (velocityDerivative period S hS T hT Q Q₁ c hc hQ f a₀))
    (velocity_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀)
    (velocityDerivative_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀)
    (fullVelocity_hasDerivWithinAt period S hS T hT Q Q₁ c hc hQ f a₀ hQt) t x

end EulerSourceCylinderClassical

end
end

end

@[expose] public section

noncomputable section

namespace EulerSourceCylinderClassical

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
    EulerLiftedGradientSpace
  EulerMetricTransport EulerMeanCoefficients EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerSourceCylinderEquation EulerCylinderSmoothOrbit EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (hSc : IsCompact S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported period Space S hS)) (a₀ : Supported period U S hS)
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
  (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period U)))
  (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)

/-- The source's literal scalar normal pressure residual. -/
def normalResidual (t : Icc (0 : ℝ) T) (x : LiftDomain period) : ℝ :=
  (⟪m.field t x.1,pointField period (includePath period S hS f) hf t x⟫_ℝ -
    2*⟪m.field t x.1,M.field t x.1 (field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t x)⟫_ℝ) /
      ‖m.field t x.1‖^2

theorem normalResidual_continuous (hm : ∀ t x, m.field t x ≠ 0) (t : Icc (0 : ℝ) T) :
    Continuous (normalResidual period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t) := by
  have hA := smoothField_continuous period _ (field_smooth period S hS hSc T hT Q Q₁ c hc hQ f a₀
      hf ha₀ t)
  have hF := smoothField_continuous period _ (pointField_smooth period (includePath period S hS f)
      hf t)
  have hM : Continuous (fun x : LiftDomain period => M.field t x.1) := (M.field t).continuous.comp
      continuous_fst
  have hm' : Continuous (fun x : LiftDomain period => m.field t x.1) := (m.field t).continuous.comp
      continuous_fst
  exact ((hm'.inner hF).sub (continuous_const.mul (hm'.inner (hM.clm_apply hA)))).div
    (hm'.norm.pow 2) (fun x => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hm t x.1)))

/-- The literal scalar pressure source is smooth in every spatial and angular variable. -/
theorem normalResidual_smooth (hm : ∀ t x, m.field t x ≠ 0)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period
      (normalResidual period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t) x) := by
  have hp : ContDiff ℝ ∞ (fun h : LiftTangent => x.1+h.1) := contDiff_const.add contDiff_fst
  have hm' : ContDiff ℝ ∞ (fun h : LiftTangent => m.field t (x.1+h.1)) := (m.smooth t).comp hp
  have hM : ContDiff ℝ ∞ (fun h : LiftTangent => M.field t (x.1+h.1)) := (M.smooth t).comp hp
  have hA := field_smooth period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t x
  have hF := pointField_smooth period (includePath period S hS f) hf t x
  have hd : ∀ h : LiftTangent, ⟪m.field t (x.1+h.1),m.field t (x.1+h.1)⟫_ℝ ≠ 0 := by
    intro h
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hm t (x.1+h.1)))
  have h := ((hm'.inner ℝ hF).sub ((contDiff_const (c := (2 : ℝ))).mul
    (hm'.inner ℝ (hM.clm_apply hA)))).div (hm'.inner ℝ hm') hd
  convert h using 1 <;> first
    | rfl
    | (funext z; simp only [localFieldLift,normalResidual,real_inner_self_eq_norm_sq,Pi.div_apply])

/-- Pointwise tangency follows from the actual frame representation and continuity. -/
theorem field_tangent
    (hTangent : ∀ t x v, ⟪m.field t x, Q.field t x v⟫_ℝ = 0)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ⟪m.field t x.1,field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t x⟫_ℝ = 0 := by
  have hae : (fun y : LiftDomain period => ⟪m.field t y.1,
      field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t y⟫_ℝ) =ᵐ[liftMeasure period] (fun _ =>
          0) := by
    filter_upwards [velocity_ae period S hS T hT Q Q₁ c hc hQ f a₀ t,
      field_ae period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t] with y hq ha
    rw [← ha,hq]
    exact hTangent t y.1 _
  exact congrFun (Measure.eq_of_ae_eq hae
    (((m.field t).continuous.comp continuous_fst).inner (smoothField_continuous period _
      (field_smooth period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t))) continuous_const) x

/-- Equation (11) before angular integration holds at every cylinder point. -/
theorem field_balance (hm : ∀ t x, m.field t x ≠ 0)
    (hTangent : ∀ t x v, ⟪m.field t x, Q.field t x v⟫_ℝ = 0)
    (hRange : ∀ t x η, ⟪m.field t x, η⟫_ℝ = 0 → ∃ v, Q.field t x v = η)
    (hFlow : ∀ t x, Q₁.field t x = (M.field t x).comp (Q.field t x))
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    derivativeField period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t x +
      M.field t x.1 (field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t x) +
      normalResidual period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t x • m.field t x.1 =
        pointField period (includePath period S hS f) hf t x := by
  have hae : (fun y : LiftDomain period =>
      derivativeField period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t y +
      M.field t y.1 (field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t y) +
      normalResidual period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t y • m.field t y.1)
          =ᵐ[liftMeasure period]
        pointField period (includePath period S hS f) hf t := by
    filter_upwards [velocity_balance_ae period S hS T hT Q Q₁ c hc hQ f a₀
        (fun s y => M.field s y) (fun s y => m.field s y) hm hTangent hRange hFlow t,
      field_ae period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t,
      derivativeField_ae period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t,
      pointField_ae period (includePath period S hS f) hf t] with y he ha hd hforce
    change (f t : CylinderL2 period Space) y = pointField period (includePath period S hS f) hf t y
        at hforce
    rw [ha,hd,hforce] at he
    exact he
  have hA := smoothField_continuous period _ (field_smooth period S hS hSc T hT Q Q₁ c hc hQ f a₀
      hf ha₀ t)
  have hD := smoothField_continuous period _ (derivativeField_smooth period S hS hSc T hT Q Q₁ c hc
      hQ f a₀ hf ha₀ t)
  have hF := smoothField_continuous period _ (pointField_smooth period (includePath period S hS f)
      hf t)
  have hM : Continuous (fun y : LiftDomain period => M.field t y.1) := (M.field t).continuous.comp
      continuous_fst
  have hm' : Continuous (fun y : LiftDomain period => m.field t y.1) := (m.field t).continuous.comp
      continuous_fst
  exact congrFun (Measure.eq_of_ae_eq hae ((hD.add (hM.clm_apply hA)).add
    ((normalResidual_continuous period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m hm t).smul hm'))
        hF) x

end EulerSourceCylinderClassical

end
end

end

section

/-!
# The solved normal pressure source has zero angular mean

The zero mode is proved for the actual Duhamel solution and then transferred
to its continuous scalar representative. No zero-mean condition on the
solution or on its pressure residual is assumed.
-/

section

/-!
# The actual scalar pressure source on cylinder L²

The normal functional is constructed from the positive one-column Gram
matrix. Applying it to f−2MA gives a genuine scalar L² path, with the literal
normal residual as representative and genuine smooth mixed translation orbit.
-/

@[expose] public section

noncomputable section

namespace EulerSourceCylinderEquation

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
      EulerLpCylinderRectangular
  EulerSourceNormalCoefficient
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported period Space S hS)) (a₀ : Supported period U S hS)
  (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖ ^ 2)

/-- A genuine supported scalar path representing the right side of ∂θπ in (11). -/
def pressureSource : C(Icc (0 : ℝ) T,Supported period ℝ S hS) :=
  supportedMultiplierMap period S hS (normalFunctional m cm hcm hm)
    (f - (2 : ℝ) • supportedMultiplierMap period S hS M.field
      (velocity period S hS T hT Q Q₁ c hc hQ f a₀))

/-- The pressure source is precisely the manuscript's scalar quotient. -/
theorem pressureSource_ae (t : Icc (0 : ℝ) T) :
    (pressureSource period S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t : CylinderL2 period ℝ)
        =ᵐ[liftMeasure period]
      fun x => (⟪m.field t x.1,(f t : CylinderL2 period Space) x⟫_ℝ -
        2*⟪m.field t x.1,M.field t x.1
          ((velocity period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period Space) x)⟫_ℝ) /
              ‖m.field t x.1‖^2 := by
  let v := velocity period S hS T hT Q Q₁ c hc hQ f a₀ t
  let w := supportedOperatorMap period S hS (M.field t) v
  let r : Supported period Space S hS := f t - (2 : ℝ) • w
  let N := normalFunctional m cm hcm hm t
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period N) (r :
      CylinderL2 period Space),
    EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period (M.field t)) (v :
        CylinderL2 period Space),
    Lp.coeFn_sub (f t : CylinderL2 period Space) ((2 : ℝ) • (w : CylinderL2 period Space)),
    Lp.coeFn_smul (2 : ℝ) (w : CylinderL2 period Space)] with x hn hM hr hs
  change (EulerLpOperatorField.full (liftMeasure period) (fieldLift period N) (r : CylinderL2
      period Space)) x = _
  rw [hn]
  change normalFunctional m cm hcm hm t x.1 ((r : CylinderL2 period Space) x) = _
  rw [normalFunctional_apply]
  change (⟪m.field t x.1,((f t : CylinderL2 period Space) - (2 : ℝ) • (w : CylinderL2 period
      Space)) x⟫_ℝ) / _ = _
  rw [hr]
  simp only [Pi.sub_apply]
  rw [hs]
  simp only [Pi.smul_apply]
  change (⟪m.field t x.1,(f t : CylinderL2 period Space) x - (2 : ℝ) •
    (EulerLpOperatorField.full (liftMeasure period) (fieldLift period (M.field t)) (v : CylinderL2
        period Space)) x⟫_ℝ) / _ = _
  rw [hM,inner_sub_right,inner_smul_right]
  rfl

/-- The actual scalar pressure source inherits genuine mixed regularity from the solve. -/
theorem pressureSource_contDiff (hSc : IsCompact S)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period U))) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (pressureSource period S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm))) := by
  let v : C(Icc (0 : ℝ) T,Supported period Space S hS) :=
    velocity period S hS T hT Q Q₁ c hc hQ f a₀
  let w : C(Icc (0 : ℝ) T,Supported period Space S hS) :=
    supportedMultiplierMap (K := Icc (0 : ℝ) T) (E := Space) (F := Space) period S hS M.field v
  have hv := velocity_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀
  have hw := supported_product_orbit_contDiff period M.field M.translation_contDiff S hS v hv
  let r : C(Icc (0 : ℝ) T,Supported period Space S hS) := f - (2 : ℝ) • w
  have hr : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a
      (includePath period S hS r)) := by
    simpa only [r,map_sub,map_smul] using hf.sub (hw.const_smul (2 : ℝ))
  exact supported_product_orbit_contDiff period (normalFunctional m cm hcm hm)
    (normalFunctional_translation_contDiff m cm hcm hm) S hS r hr

end EulerSourceCylinderEquation

end
end

end

@[expose] public section

noncomputable section

namespace EulerSourceCylinderEquation

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpCylinderRectangular EulerSourceNormalCoefficient EulerCylinderAngleAverage
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

theorem pressureSource_average_zero
    (hf₀ : ∀ t, average P (f t : CylinderL2 P Space) = 0)
    (ha₀ : average P (a₀ : CylinderL2 P U) = 0) (t : Icc (0 : ℝ) T) :
    average P (pressureSource P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t :
      CylinderL2 P ℝ) = 0 := by
  change average P (fullOperatorMap P (normalFunctional m cm hcm hm t)
    ((f t : CylinderL2 P Space) - (2 : ℝ) • fullOperatorMap P (M.field t)
      (velocity P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P Space))) = 0
  rw [average_fullOperator, map_sub, map_smul, average_fullOperator,
    velocity_average_zero P S hS T hT Q Q₁ c hc hQ f a₀ hf₀ ha₀ t,
    hf₀ t, map_zero, smul_zero, sub_self, map_zero]

theorem pressureSource_slice_contDiff (hSc : IsCompact S)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (includePath P S hS f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a (a₀ : CylinderL2 P U)))
    (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun a : LiftTangent => translate P a
      (pressureSource P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t : CylinderL2 P ℝ)) := by
  exact (ContinuousMap.evalCLM ℝ t : C(Icc (0 : ℝ) T,CylinderL2 P ℝ) →L[ℝ]
    CylinderL2 P ℝ).contDiff.comp
      (pressureSource_contDiff P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm hSc hf ha₀)

end EulerSourceCylinderEquation

namespace EulerSourceCylinderClassical

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerSourceCylinderEquation EulerCylinderSmoothOrbit EulerCylinderAngleAverage
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

omit [Fact (0 < P)] in
include hcm hm in
theorem normal_ne_zero_of_lower (t : Icc (0 : ℝ) T) (x : Space) :
    m.field t x ≠ 0 := by
  intro he
  have h := hm t x
  rw [he, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  exact (not_le_of_gt hcm) h

/-- The actual scalar L² class represents the literal normal quotient. -/
theorem pressureSource_ae_normalResidual (t : Icc (0 : ℝ) T) :
    (pressureSource P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t : CylinderL2 P ℝ) =ᵐ[liftMeasure
        P]
      normalResidual P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t := by
  filter_upwards [pressureSource_ae P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t,
    field_ae P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t,
    pointField_ae P (includePath P S hS f) hf t] with x hs hv hforce
  change (f t : CylinderL2 P Space) x = pointField P (includePath P S hS f) hf t x at hforce
  rw [hs, hv, hforce]
  rfl

include hcm hm in
/-- Zero mean of the forcing and initial coordinate implies zero mean of the
literal pressure source of the constructed solution. -/
theorem normalResidual_mean_zero
    (hf₀ : ∀ t, average P (f t : CylinderL2 P Space) = 0)
    (ha₀zero : average P (a₀ : CylinderL2 P U) = 0)
    (t : Icc (0 : ℝ) T) (y : Space) :
    (∫ s in (0 : ℝ)..P,
      normalResidual P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t (y,(s : AddCircle P))) = 0 := by
  exact EulerCylinderScalarPrimitive.scalar_mean_zero P
    (pressureSource P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t)
    (pressureSource_slice_contDiff P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm hSc hf ha₀ t)
    (normalResidual P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t)
    (normalResidual_continuous P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m
      (normal_ne_zero_of_lower T m cm hcm hm) t)
    (pressureSource_ae_normalResidual P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm t)
    (pressureSource_average_zero P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm hf₀ ha₀zero t) y

end EulerSourceCylinderClassical

end
end

end

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
