/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketReflection

@[expose] public section

/-! Odd velocity and even normalized pressure for the actual mean provider. -/

noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanCoefficients EulerMeanVariationalInverse EulerMeanScalarPressure
  EulerMeanSmoothRepresentative EulerMeanTimeContinuousTranslation EulerMeanTimeReflection
  EulerMeanFixedReflection EulerCanonicalGraphPotential EulerVolterraConvolution
  EulerPacketProfileRecursion
open scoped ContDiff

/-- Oddness of an actual L² class transfers to its unique smooth representative. -/
theorem representative_odd_of_reflection (u : L2) (hs : SmoothOrbit u)
    (hu : reflection u = -u) (x : Space) : representative u hs (-x) = -representative u hs x := by
  have hae : (fun y => representative u hs (-y)) =ᵐ[volume] (fun y => -representative u hs y) := by
    filter_upwards [reflection_ae u, Lp.coeFn_neg u,
      measurePreserving_reflection.quasiMeasurePreserving.ae (representative_ae u hs),
      representative_ae u hs] with y h₁ h₂ h₃ h₄
    have he := congrArg (fun z : L2 => z y) hu
    rw [h₁, h₂] at he
    simpa only [Pi.neg_apply, h₃, h₄] using he
  exact congrFun (Measure.eq_of_ae_eq hae
    ((representative_smooth u hs).continuous.comp continuous_neg)
    (representative_smooth u hs).continuous.neg) x

namespace Forcing

variable {D : Data} {raw : VectorField} (G : Forcing D raw)
  (hD : EvenData D)
  (hodd : ∀ (t : Icc (0 : ℝ) D.T) x, raw (t,(-x,0)) = -raw (t,(x,0)))

include hD hodd in
theorem velocityPath_reflection (t : Icc (0 : ℝ) D.T) :
    reflection (G.velocityPath t) = -(G.velocityPath t) := by
  have hv := congrArg (fun v : solenoidalSpace => (v : L2))
    (G.coordinate_velocity_reflection hodd hD t)
  change reflection (G.solution.velocity t : L2) = -(G.solution.velocity t : L2) at hv
  have he : G.velocityPath t = D.opF t (G.solution.velocity t : L2) := by
    simpa only [StrongMeanEvolution.physicalPath, extendPath, projIcc_of_mem D.T_pos.le t.property]
      using G.solution.continuousVelocity_eq_physicalPath D.T_pos D.opF_time t
  rw [he]
  exact (multiplier_reflection_of_even (D.F.field t) (hD.frame t) (G.solution.velocity t :
    L2)).symm.trans
    ((congrArg (multiplier (D.F.field t)) hv).trans
      ((multiplier (D.F.field t)).map_neg (G.solution.velocity t : L2)))

include hD hodd in
/-- The actual raw velocity is odd at every time; its exterior definition uses the same retraction. -/
theorem vector_odd (t : ℝ) (x : Space) (θ : ℝ) :
    G.vector (t,(-x,θ)) = -G.vector (t,(x,θ)) :=
  representative_odd_of_reflection (G.velocityPath (D.clamp t))
    (pathTranslation_evaluation_contDiff D.T G.velocityPath G.velocityPath_orbit (D.clamp t))
    (G.velocityPath_reflection hD hodd (D.clamp t)) x

include hD hodd in
/-- Actual within-time derivatives preserve the odd velocity parity at both endpoints. -/
theorem vectorDerivative_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.vectorDerivative (t,(-x,θ)) = -G.vectorDerivative (t,(x,θ)) := by
  have h₁ := G.vector_hasDerivWithinAt t (-x) θ
  have h₂ := (G.vector_hasDerivWithinAt t x θ).neg
  have he : (fun r => G.vector (r,(-x,θ))) = fun r => -G.vector (r,(x,θ)) :=
    funext (fun r => G.vector_odd hD hodd r x θ)
  rw [he] at h₁
  have hs := (uniqueDiffOn_Icc D.T_pos) (t : ℝ) t.property
  exact (h₁.derivWithin hs).symm.trans (h₂.derivWithin hs)

/-- The pressure-force representative satisfies the already constructed physical equation. -/
theorem pressureRepresentative_equation (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.vectorDerivative (t,(x,θ))+D.M.field t x (G.vector (t,(x,θ)))+
      pathRepresentative D.T G.pressureForcePath G.pressureForcePath_orbit t x = raw (t,(x,θ)) := by
  have he := pathRepresentative_equation D.T G.velocityPath G.derivativePath G.pressureForcePath
    G.path
    G.velocityPath_orbit G.derivativePath_orbit G.pressureForcePath_orbit G.path_orbit D.M.field
    (G.solution.pressurePath_equation D.frameLower D.frameLower_pos D.frame_lower G.path
      D.T_pos D.opF_time D.opM D.opStrain_eq) t x
  rw [G.forcingRepresentative_eq t x θ] at he
  simpa only [vectorDerivative, vector, Data.clamp_coe] using he

include hD hodd in
theorem pressureRepresentative_odd (t : Icc (0 : ℝ) D.T) (x : Space) :
    pathRepresentative D.T G.pressureForcePath G.pressureForcePath_orbit t (-x) =
      -pathRepresentative D.T G.pressureForcePath G.pressureForcePath_orbit t x := by
  have hp := G.pressureRepresentative_equation t x 0
  have hn := G.pressureRepresentative_equation t (-x) 0
  rw [G.vectorDerivative_odd hD hodd, G.vector_odd hD hodd, hD.strain t x, map_neg, hodd t x] at hn
  have hn' : -(G.vectorDerivative (t,(x,0))+D.M.field t x (G.vector (t,(x,0))))+
      pathRepresentative D.T G.pressureForcePath G.pressureForcePath_orbit t (-x) = -raw (t,(x,0))
        := by
    simpa only [neg_add] using hn
  apply add_left_cancel (a := -(G.vectorDerivative (t,(x,0))+D.M.field t x (G.vector (t,(x,0)))))
  exact hn'.trans ((congrArg Neg.neg hp).symm.trans (neg_add _ _))

include hD hodd in
/-- Canonical radial normalization makes the actual scalar pressure even. -/
theorem scalar_even (t : ℝ) (x : Space) (θ : ℝ) : G.scalar (t,(-x,θ)) = G.scalar (t,(x,θ)) := by
  let V : Space → Space := fun y => (D.F.field (D.clamp t) y).adjoint
    (pathRepresentative D.T G.pressureForcePath G.pressureForcePath_orbit (D.clamp t) y)
  have hV (y : Space) : V (-y) = -V y := by
    change (D.F.field (D.clamp t) (-y)).adjoint
      (pathRepresentative D.T G.pressureForcePath G.pressureForcePath_orbit (D.clamp t) (-y)) = _
    rw [hD.frame (D.clamp t) y, G.pressureRepresentative_odd hD hodd, map_neg]
  change radialPotential V (-x) = radialPotential V x
  simp only [radialPotential, smul_neg, hV, inner_neg_neg]

end Forcing

theorem meanSolve_odd (D : Data) (hD : EvenData D) (raw : VectorField)
    (h : Nonempty (Forcing D raw))
    (hodd : ∀ (t : Icc (0 : ℝ) D.T) x, raw (t,(-x,0)) = -raw (t,(x,0)))
    (t : ℝ) (x : Space) (θ : ℝ) :
    (meanSolve D raw).1 (t,(-x,-θ)) = -(meanSolve D raw).1 (t,(x,θ)) := by
  rw [meanSolve_of_admissible D raw h]
  exact (Classical.choice h).vector_odd hD hodd t x (-θ)

theorem meanSolve_even (D : Data) (hD : EvenData D) (raw : VectorField)
    (h : Nonempty (Forcing D raw))
    (hodd : ∀ (t : Icc (0 : ℝ) D.T) x, raw (t,(-x,0)) = -raw (t,(x,0)))
    (t : ℝ) (x : Space) (θ : ℝ) :
    (meanSolve D raw).2 (t,(-x,-θ)) = (meanSolve D raw).2 (t,(x,θ)) := by
  rw [meanSolve_of_admissible D raw h]
  exact (Classical.choice h).scalar_even hD hodd t x (-θ)

end EulerMeanPacketProvider
