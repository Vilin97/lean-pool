/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketForcing
import LeanPool.NavierStokesAndEuler.Euler.MeanPathTimeDerivative
public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPressure
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath
public import LeanPool.NavierStokesAndEuler.Euler.CanonicalGraphPotential
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientTime
public import LeanPool.NavierStokesAndEuler.Euler.MeanSmoothRepresentative
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientFrame
import LeanPool.NavierStokesAndEuler.Euler.MeanPathSpatialRepresentative
import LeanPool.NavierStokesAndEuler.Euler.MeanPressurePotential

/-!
# A concrete raw-field provider for the mean packet equation

A raw forcing is supplied only through its literal smooth L² slices. The
returned velocity and normalized scalar pressure are constructed by the
actual source variational solve and its genuine classical representatives.
The function is total on raw fields; its PDE contract is proved precisely on
the admissible domain, without a smooth time extension across endpoints.
-/

section

/-!
# A normalized scalar pressure for the actual mean solution

The radial integral is applied to the real F-adjoint pressure force, whose
closed-gradient-space membership was proved from the actual Gram equation.
The resulting scalar is spatially smooth, normalized at zero, and gives the
pointwise physical equation. No scalar potential or pressure time derivative
is assumed.
-/

@[expose] public section

noncomputable section

namespace EulerMeanScalarPressure

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanSmoothRepresentative EulerMeanCoefficients
  EulerMeanTimeContinuousTranslation EulerMeanVariationalInverse EulerMeanPressure
  EulerCanonicalGraphPotential EulerTimeLp EulerVolterraConvolution
open scoped ContDiff

/-- The canonical smooth spatial representative of an actual continuous L² path. -/
def pathRepresentative (T : ℝ) (p : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (t : Icc (0 : ℝ) T) : Space → Space :=
  representative (p t) (pathTranslation_evaluation_contDiff T p hp t)

theorem pathRepresentative_smooth (T : ℝ) (p : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (pathRepresentative T p hp t) := representative_smooth _ _

theorem pathRepresentative_ae (T : ℝ) (p : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) (t : Icc (0 : ℝ) T) :
    (p t : Space → Space) =ᵐ[volume] pathRepresentative T p hp t := representative_ae _ _

theorem pathRepresentative_continuous (T : ℝ) (p : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) :
    Continuous (fun z : Icc (0 : ℝ) T × Space => pathRepresentative T p hp z.1 z.2) :=
  path_representative_joint_continuous T p hp

/-- An actual L² equation between continuous spatial representatives holds everywhere. -/
theorem representative_equation (B D R f : L2)
    (hB : SmoothOrbit B) (hD : SmoothOrbit D) (hR : SmoothOrbit R) (hf : SmoothOrbit f)
    (M : Field) (heq : D + multiplier M B + R = f) (x : Space) :
    representative D hD x+M x (representative B hB x)+representative R hR x =
      representative f hf x := by
  have hae : (fun y => representative D hD y+M y (representative B hB y)+representative R hR y)
      =ᵐ[volume] representative f hf := by
    filter_upwards [representative_ae B hB, representative_ae D hD, representative_ae R hR,
      representative_ae f hf, multiplier_ae M B, Lp.coeFn_add D (multiplier M B),
      Lp.coeFn_add (D+multiplier M B) R] with y hby hdy hry hfy hmy hsum hsum2
    have hy := congrArg (fun z : L2 => z y) heq
    rw [hsum2] at hy
    simp only [Pi.add_apply] at hy
    rw [hsum] at hy
    simpa only [Pi.add_apply, hmy, hby, hdy, hry, hfy] using hy
  exact congrFun (Measure.eq_of_ae_eq hae
    (((representative_smooth D hD).continuous.add
      (M.continuous.clm_apply (representative_smooth B hB).continuous)).add
        (representative_smooth R hR).continuous)
    (representative_smooth f hf).continuous) x

theorem pathRepresentative_equation (T : ℝ)
    (B D R f : C(Icc (0 : ℝ) T, L2))
    (hB : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a B))
    (hD : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a D))
    (hR : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a R))
    (hf : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a f))
    (M : C(Icc (0 : ℝ) T,Field))
    (heq : ∀ t, D t+multiplier (M t) (B t)+R t=f t)
    (t : Icc (0 : ℝ) T) (x : Space) :
    pathRepresentative T D hD t x+M t x (pathRepresentative T B hB t x) +
      pathRepresentative T R hR t x = pathRepresentative T f hf t x :=
  representative_equation (B t) (D t) (R t) (f t)
    (pathTranslation_evaluation_contDiff T B hB t) (pathTranslation_evaluation_contDiff T D hD t)
    (pathTranslation_evaluation_contDiff T R hR t) (pathTranslation_evaluation_contDiff T f hf t)
    (M t) (heq t) x

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv (operatorPath T F.field) (operatorPath T F₁.field) A L u f)
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T (operatorPath T F.field) t v‖ ^ 2)
  (fC : C(Icc (0 : ℝ) T, L2))
  (hR : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a (s.pressurePath c hc hLower fC)))

/-- The concrete normalized scalar mean pressure, constructed by a radial integral. -/
def pressureScalar (t : Icc (0 : ℝ) T) : Space → ℝ :=
  radialPotential (fun x => (F.field t x).adjoint
    (pathRepresentative T (s.pressurePath c hc hLower fC) hR t x))

/-- Spatial smoothness, normalization, and exact gradient of the constructed pressure. -/
theorem pressureScalar_spec (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (pressureScalar T hT F F₁ FInv s c hc hLower fC hR t) ∧
    pressureScalar T hT F F₁ FInv s c hc hLower fC hR t 0 = 0 ∧
    ∀ x, gradient (pressureScalar T hT F F₁ FInv s c hc hLower fC hR t) x =
      (F.field t x).adjoint (pathRepresentative T (s.pressurePath c hc hLower fC) hR t x) := by
  have hAdj : ContDiff ℝ ∞ (fun x : Space => (F.field t x).adjoint) :=
    (EulerTransverseGramInverse.realAdjoint (U := Space) (E := Space)).contDiff.comp (F.smooth t)
  exact weighted_pressure_has_potential (F.field t) (adjointField (F.field t)) (fun _ => rfl)
    (s.pressurePath c hc hLower fC t) (s.pressurePath_gradient c hc hLower fC t)
    (pathRepresentative T (s.pressurePath c hc hLower fC) hR t)
    (pathRepresentative_ae T _ hR t) (hAdj.clm_apply (pathRepresentative_smooth T _ hR t))

/-- The source mean pressure has no angular dependence. -/
def pressureProfile (t : Icc (0 : ℝ) T) (x : Space) (_θ : ℝ) : ℝ :=
  pressureScalar T hT F F₁ FInv s c hc hLower fC hR t x

theorem pressureProfile_angle_derivative (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    HasDerivAt (pressureProfile T hT F F₁ FInv s c hc hLower fC hR t x) 0 θ :=
  hasDerivAt_const θ _

/-- The physical pressure force is exactly the actual residual, because the
inverse-transpose cancels the transpose of the given frame. -/
theorem pressureScalar_physicalGradient
    (Finv : C(Icc (0 : ℝ) T, Field))
    (hFinv : ∀ t x v, F.field t x (Finv t x v) = v)
    (t : Icc (0 : ℝ) T) (x : Space) :
    (Finv t x).adjoint (gradient (pressureScalar T hT F F₁ FInv s c hc hLower fC hR t) x) =
      pathRepresentative T (s.pressurePath c hc hLower fC) hR t x := by
  rw [(pressureScalar_spec T hT F F₁ FInv s c hc hLower fC hR t).2.2 x]
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left, adjoint_inner_left, hFinv]

/-- The constructed pressure gives the literal pointwise source equation. -/
theorem pressureScalar_equation
    (hTpos : 0 < T)
    (hFTime : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT (operatorPath T F.field))
        (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
    (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
    (hMF : ∀ t x v, F₁.field t x v = M.field t x (F.field t x v))
    (Finv : C(Icc (0 : ℝ) T,Field)) (hFinv : ∀ t x v, F.field t x (Finv t x v) = v)
    (hB : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a s.continuousVelocity))
    (hD : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a (s.classicalPhysicalDerivative c hc
        hLower fC)))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC))
    (t : Icc (0 : ℝ) T) (x : Space) :
    pathRepresentative T (s.classicalPhysicalDerivative c hc hLower fC) hD t x +
      M.field t x (pathRepresentative T s.continuousVelocity hB t x) +
      (Finv t x).adjoint (gradient (pressureScalar T hT F F₁ FInv s c hc hLower fC hR t) x) =
        pathRepresentative T fC hfC t x := by
  rw [pressureScalar_physicalGradient T hT F F₁ FInv s c hc hLower fC hR Finv hFinv t x]
  exact pathRepresentative_equation T s.continuousVelocity
    (s.classicalPhysicalDerivative c hc hLower fC) (s.pressurePath c hc hLower fC) fC
    hB hD hR hfC M.field
    (s.pressurePath_equation c hc hLower fC hTpos hFTime (operatorPath T M.field)
      (operatorPath_comp T M.field F.field F₁.field hMF)) t x

end EulerMeanScalarPressure

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanVariationalInverse EulerMeanScalarPressure
  EulerMeanSmoothRepresentative EulerMeanTimeContinuousTranslation
  EulerMeanPathTimeDerivative EulerTimeLp EulerVolterraConvolution
  EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

namespace Data

/-- A continuous closed-interval retraction, used only to define the raw field outside its domain.
-/
def clamp (D : Data) (t : ℝ) : Icc (0 : ℝ) D.T := projIcc 0 D.T D.T_pos.le t

@[simp] theorem clamp_coe (D : Data) (t : Icc (0 : ℝ) D.T) : D.clamp t = t :=
  projIcc_of_mem D.T_pos.le t.property

/-- Inverse Frame, given by `D.FInv (D.clamp z.1) z.2.1`. -/
def inverseFrame (D : Data) (z : Domain) : Space →L[ℝ] Space :=
  D.FInv (D.clamp z.1) z.2.1

/-- Strain, given by `D.M.field (D.clamp z.1) z.2.1`. -/
def strain (D : Data) (z : Domain) : Space →L[ℝ] Space :=
  D.M.field (D.clamp z.1) z.2.1

end Data

namespace Forcing

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

/-- Literal velocity returned by the genuine mean inverse. -/
def vector : VectorField := fun z =>
  pathRepresentative D.T G.velocityPath G.velocityPath_orbit (D.clamp z.1) z.2.1

/-- Literal continuous time derivative of the velocity on the source interval. -/
def vectorDerivative : VectorField := fun z =>
  pathRepresentative D.T G.derivativePath G.derivativePath_orbit (D.clamp z.1) z.2.1

/-- The normalized scalar pressure returned by the actual radial construction. -/
def scalar : ScalarField := fun z =>
  pressureScalar D.T D.T_pos.le D.F D.F₁ D.opInv G.solution
    D.frameLower D.frameLower_pos D.frame_lower G.path G.pressureForcePath_orbit
    (D.clamp z.1) z.2.1

/-- The representative of the prescribed forcing is the original raw field, pointwise. -/
theorem forcingRepresentative_eq (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    pathRepresentative D.T G.path G.path_orbit t x = raw (t,(x,θ)) := by
  have hrep : (G.path t : Space → Space) =ᵐ[volume] (G.slices t).field := by
    rw [G.path_eq]
    exact (G.slices t).toLp_ae
  have he := representative_unique (G.path t)
    (pathTranslation_evaluation_contDiff D.T G.path G.path_orbit t) (G.slices t).field
    (G.slices t).smooth.continuous hrep
  exact (congrFun he x).trans (G.raw_eq t x θ).symm

theorem vector_angle_independent (t : ℝ) (x : Space) (θ η : ℝ) :
    G.vector (t,(x,θ)) = G.vector (t,(x,η)) := rfl

theorem scalar_angle_independent (t : ℝ) (x : Space) (θ η : ℝ) :
    G.scalar (t,(x,θ)) = G.scalar (t,(x,η)) := rfl

theorem scalar_normalized (t θ : ℝ) : G.scalar (t,(0,θ)) = 0 :=
  (pressureScalar_spec D.T D.T_pos.le D.F D.F₁ D.opInv G.solution
    D.frameLower D.frameLower_pos D.frame_lower G.path G.pressureForcePath_orbit (D.clamp t)).2.1

/-- Actual spatial and angular regularity at every time. -/
theorem vector_spatial_smooth (t : ℝ) : ContDiff ℝ ∞ (fun y : Space × ℝ => G.vector (t,y)) :=
  (pathRepresentative_smooth D.T G.velocityPath G.velocityPath_orbit (D.clamp t)).comp contDiff_fst

theorem vectorDerivative_spatial_smooth (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Space × ℝ => G.vectorDerivative (t,y)) :=
  (pathRepresentative_smooth D.T G.derivativePath G.derivativePath_orbit (D.clamp t)).comp
      contDiff_fst

theorem scalar_spatial_smooth (t : ℝ) : ContDiff ℝ ∞ (fun y : Space × ℝ => G.scalar (t,y)) :=
  (pressureScalar_spec D.T D.T_pos.le D.F D.F₁ D.opInv G.solution
    D.frameLower D.frameLower_pos D.frame_lower G.path G.pressureForcePath_orbit (D.clamp
        t)).1.comp contDiff_fst

/-- The returned velocity has the genuine within-time derivative at both endpoints too. -/
theorem vector_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivWithinAt (fun r => G.vector (r,(x,θ))) (G.vectorDerivative (t,(x,θ)))
      (Icc (0 : ℝ) D.T) t := by
  have ht := representative_hasDerivWithinAt D.T D.T_pos.le G.velocityPath G.derivativePath
    G.velocityPath_time G.velocityPath_orbit G.derivativePath_orbit t x
  simpa only [vector, vectorDerivative, pathRepresentative, Data.clamp, extendPath,
    projIcc_of_mem D.T_pos.le t.property] using ht

/-- The genuine raw mean equation, with the normalized actual scalar pressure. -/
theorem equation (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.vectorDerivative (t,(x,θ))+D.strain (t,(x,θ)) (G.vector (t,(x,θ))) +
      (D.inverseFrame (t,(x,θ))).adjoint (gradient (fun y => G.scalar (t,(y,θ))) x) = raw (t,(x,θ))
          := by
  have hp := pressureScalar_equation D.T D.T_pos.le D.F D.F₁ D.opInv G.solution
    D.frameLower D.frameLower_pos D.frame_lower G.path G.pressureForcePath_orbit
    D.T_pos D.opF_time D.M D.strain_equation D.FInv D.inverse_right
    G.velocityPath_orbit G.derivativePath_orbit G.path_orbit t x
  have hp := hp.trans (G.forcingRepresentative_eq t x θ)
  simpa only [vector, vectorDerivative, scalar, Data.strain, Data.inverseFrame, Data.clamp_coe]
      using hp

end Forcing

/-- A total raw-field operator whose correctness is required on the proved admissible domain. -/
def meanSolve (D : Data) (raw : VectorField) : VectorField × ScalarField := by
  classical
  exact if h : Nonempty (Forcing D raw) then
    let G := Classical.choice h
    (G.vector,G.scalar)
  else (0,0)

theorem meanSolve_of_admissible (D : Data) (raw : VectorField) (h : Nonempty (Forcing D raw)) :
    meanSolve D raw = ((Classical.choice h).vector,(Classical.choice h).scalar) := by
  simp only [meanSolve, dite_eq_left h]

/-- The total provider is backed by an actual source solve on every admissible input. -/
theorem meanSolve_contract (D : Data) (raw : VectorField) (h : Nonempty (Forcing D raw)) :
    ∃ bt : VectorField,
      (∀ (t : Icc (0 : ℝ) D.T) x θ,
        HasDerivWithinAt (fun r => (meanSolve D raw).1 (r,(x,θ))) (bt (t,(x,θ))) (Icc (0 : ℝ) D.T)
            t) ∧
      (∀ (t : Icc (0 : ℝ) D.T) x θ,
        bt (t,(x,θ))+D.strain (t,(x,θ)) ((meanSolve D raw).1 (t,(x,θ))) +
          (D.inverseFrame (t,(x,θ))).adjoint
            (gradient (fun y => (meanSolve D raw).2 (t,(y,θ))) x) = raw (t,(x,θ))) ∧
      (∀ t, ContDiff ℝ ∞ (fun y : Space × ℝ => (meanSolve D raw).1 (t,y))) ∧
      (∀ t, ContDiff ℝ ∞ (fun y : Space × ℝ => (meanSolve D raw).2 (t,y))) ∧
      (∀ t θ, (meanSolve D raw).2 (t,(0,θ)) = 0) := by
  rw [meanSolve_of_admissible D raw h]
  exact ⟨(Classical.choice h).vectorDerivative, (Classical.choice h).vector_hasDerivWithinAt,
    (Classical.choice h).equation, (Classical.choice h).vector_spatial_smooth,
    (Classical.choice h).scalar_spatial_smooth, (Classical.choice h).scalar_normalized⟩

end EulerMeanPacketProvider
