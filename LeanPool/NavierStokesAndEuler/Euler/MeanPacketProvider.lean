/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketForcing
public import LeanPool.NavierStokesAndEuler.Euler.MeanPathTimeDerivative

@[expose] public section

/-!
# A concrete raw-field provider for the mean packet equation

A raw forcing is supplied only through its literal smooth L² slices. The
returned velocity and normalized scalar pressure are constructed by the
actual source variational solve and its genuine classical representatives.
The function is total on raw fields; its PDE contract is proved precisely on
the admissible domain, without a smooth time extension across endpoints.
-/

noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanVariationalInverse EulerMeanScalarPressure
  EulerMeanSmoothRepresentative EulerMeanTimeContinuousTranslation
  EulerMeanPathTimeDerivative EulerTimeLp EulerVolterraConvolution
  EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

namespace Data

/-- A continuous closed-interval retraction, used only to define the raw field outside its domain. -/
def clamp (D : Data) (t : ℝ) : Icc (0 : ℝ) D.T := projIcc 0 D.T D.T_pos.le t

@[simp] theorem clamp_coe (D : Data) (t : Icc (0 : ℝ) D.T) : D.clamp t = t :=
  projIcc_of_mem D.T_pos.le t.property

def inverseFrame (D : Data) (z : Domain) : Space →L[ℝ] Space :=
  D.FInv (D.clamp z.1) z.2.1

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
    G.vectorDerivative (t,(x,θ))+D.strain (t,(x,θ)) (G.vector (t,(x,θ)))+
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
        bt (t,(x,θ))+D.strain (t,(x,θ)) ((meanSolve D raw).1 (t,(x,θ)))+
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
