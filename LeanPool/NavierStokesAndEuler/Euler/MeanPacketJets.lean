/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketConstraints

@[expose] public section

/-! The concrete mean inverse in the literal jets used by the packet recursion. -/

noncomputable section

namespace EulerMeanPacketProvider

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanScalarPressure
  EulerMeanVariationalInverse EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

/-- The pressure jet is the ordinary spatial derivative at fixed time and angle. -/
theorem pressureJet_spatial_derivative (p : ScalarField) (t : ℝ) (x : Space) (θ : ℝ)
    (hp : DifferentiableAt ℝ (fun y : Space × ℝ => p (t,y)) (x,θ)) :
    (pressureJet p (t,(x,θ))).2.comp spatialInjection =
      fderiv ℝ (fun y : Space => p (t,(y,θ))) x := by
  have hi : HasFDerivAt (fun y : Space => (y,θ))
      ((ContinuousLinearMap.id ℝ Space).prod (0 : Space →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const θ x)
  have hd := hp.hasFDerivAt.comp x hi
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, pressureJet_space]
  have he := congrArg (fun A : Space →L[ℝ] ℝ => A v) hd.fderiv
  simpa only [Function.comp_def, comp_apply, prod_apply, id_apply, zero_apply] using he.symm

theorem slowPressure_pressureJet (FInv : Space →L[ℝ] Space)
    (p : ScalarField) (t : ℝ) (x : Space) (θ : ℝ)
    (hp : DifferentiableAt ℝ (fun y : Space × ℝ => p (t,y)) (x,θ)) :
    slowPressure FInv (pressureJet p (t,(x,θ))) =
      FInv.adjoint (gradient (fun y => p (t,(y,θ))) x) := by
  change FInv.adjoint ((toDual ℝ Space).symm ((pressureJet p (t,(x,θ))).2.comp spatialInjection)) =
    _
  rw [pressureJet_spatial_derivative p t x θ hp]
  rfl

namespace Forcing

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

theorem slicedJet_time (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    (slicedJet (Icc (0 : ℝ) D.T) G.vector (t,(x,θ))).2 timeDirection =
      G.vectorDerivative (t,(x,θ)) :=
  slicedJet_time_eq _ _ _ _ ((uniqueDiffOn_Icc D.T_pos) _ t.property)
    (G.vector_hasDerivWithinAt t x θ)

/-- This is exactly the pointwise mean equation required by the grade recursion. -/
theorem jet_equation (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    linearPart (D.strain (t,(x,θ))) (slicedJet (Icc (0 : ℝ) D.T) G.vector (t,(x,θ)))+
      slowPressure (D.inverseFrame (t,(x,θ))) (pressureJet G.scalar (t,(x,θ))) =
        raw (t,(x,θ)) := by
  change (slicedJet (Icc (0 : ℝ) D.T) G.vector (t,(x,θ))).2 timeDirection+
    D.strain (t,(x,θ)) (G.vector (t,(x,θ)))+_ = _
  rw [G.slicedJet_time, slowPressure_pressureJet _ G.scalar t x θ
    ((G.scalar_spatial_smooth t).differentiable (by simp) (x,θ))]
  exact G.equation t x θ

theorem vector_angle_jet (t : ℝ) (x : Space) (θ : ℝ) :
    (slicedJet (Icc (0 : ℝ) D.T) G.vector (t,(x,θ))).2 angleDirection = 0 := by
  rw [EulerPacketPointJets.slicedJet_angle]
  have hfst : HasFDerivAt (Prod.fst : Space × ℝ → Space)
      (ContinuousLinearMap.fst ℝ Space ℝ) (x,θ) := hasFDerivAt_fst
  have hd := ((pathRepresentative_smooth D.T G.velocityPath G.velocityPath_orbit (D.clamp
    t)).differentiable
    (by simp) x).hasFDerivAt.comp (x,θ) hfst
  change (fderiv ℝ (fun y : Space × ℝ =>
    pathRepresentative D.T G.velocityPath G.velocityPath_orbit (D.clamp t) y.1) (x,θ)) (0,1) = 0
  have he := congrArg (fun A : (Space × ℝ) →L[ℝ] Space => A (0,1)) hd.fderiv
  simpa only [Function.comp_def, comp_apply, ContinuousLinearMap.coe_fst', map_zero] using he

theorem scalar_angle_jet (t : ℝ) (x : Space) (θ : ℝ) :
    (pressureJet G.scalar (t,(x,θ))).2 angleDirection = 0 := by
  rw [pressureJet_angle]
  have hs := (pressureScalar_spec D.T D.T_pos.le D.F D.F₁ D.opInv G.solution
    D.frameLower D.frameLower_pos D.frame_lower G.path G.pressureForcePath_orbit (D.clamp t)).1
  have hfst : HasFDerivAt (Prod.fst : Space × ℝ → Space)
      (ContinuousLinearMap.fst ℝ Space ℝ) (x,θ) := hasFDerivAt_fst
  have hd := (hs.differentiable (by simp) x).hasFDerivAt.comp (x,θ) hfst
  change (fderiv ℝ (fun y : Space × ℝ =>
    pressureScalar D.T D.T_pos.le D.F D.F₁ D.opInv G.solution D.frameLower D.frameLower_pos
      D.frame_lower G.path G.pressureForcePath_orbit (D.clamp t) y.1) (x,θ)) (0,1) = 0
  have he := congrArg (fun A : (Space × ℝ) →L[ℝ] ℝ => A (0,1)) hd.fderiv
  simpa only [Function.comp_def, comp_apply, ContinuousLinearMap.coe_fst', map_zero] using he

end Forcing

/-- The total operator discharges the literal packet mean-jet interface on admissible inputs. -/
theorem meanSolve_jet_equation (D : Data) (raw : VectorField) (h : Nonempty (Forcing D raw))
    (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    linearPart (D.strain (t,(x,θ))) (slicedJet (Icc (0 : ℝ) D.T) (meanSolve D raw).1 (t,(x,θ)))+
      slowPressure (D.inverseFrame (t,(x,θ))) (pressureJet (meanSolve D raw).2 (t,(x,θ))) =
        raw (t,(x,θ)) := by
  rw [meanSolve_of_admissible D raw h]
  exact (Classical.choice h).jet_equation t x θ

end EulerMeanPacketProvider
