/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanOperatorReflection
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketForcing
public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceFixedInverse
import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryReflection
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedReflection
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketProvider
import LeanPool.NavierStokesAndEuler.Euler.MeanSourceSpatialRegularity

/-!
# Actual reflection symmetry of the mean packet solve

Even source matrices and an odd forcing commute through the complete mean
form, including its localized initial boundary operator. The odd coordinate
velocity follows from uniqueness of the constructed inverse.
-/

@[expose] public section


noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic
  EulerMeanSourceInverse EulerMeanVariationalInverse EulerMeanSourceFixedInverse
  EulerMeanFixedSpaceInverse EulerMeanFixedReflection EulerMeanTimeReflection
  EulerMeanScalarPressure EulerTimeLp EulerVolterraConvolution EulerCoerciveProjection
  EulerPacketProfileRecursion
open scoped NNReal ContDiff

/-- These are literal parity assumptions on the prescribed source coefficients. -/
structure EvenData (D : Data) : Prop where
  frame : ∀ t x, D.F.field t (-x) = D.F.field t x
  frameDerivative : ∀ t x, D.F₁.field t (-x) = D.F₁.field t x
  curvature : ∀ t x, D.H.field t (-x) = D.H.field t x
  initialStrain : ∀ x, D.M0.field (-x) = D.M0.field x
  strain : ∀ t x, D.M.field t (-x) = D.M.field t x

/-- Actual pointwise multiplication by an even matrix field commutes with reflection. -/
theorem multiplier_reflection_of_even (A : Field) (hA : ∀ x, A (-x) = A x) :
    ReflectionInvariant (multiplier A) := by
  intro u
  apply Lp.ext
  filter_upwards [multiplier_ae A (reflection u), reflection_ae u,
    reflection_ae (multiplier A u),
    measurePreserving_reflection.quasiMeasurePreserving.ae (multiplier_ae A u)] with x hm hr hmr hrm
  rw [hm, hr, hmr, hrm, hA x]

namespace Data

variable (D : Data)

/-- The actual source coordinate solve as a bounded linear operator. -/
def coordinateSolver : TimeLp D.T L2 →L[ℝ] TimeLp D.T solenoidalSpace :=
  sourceCoordinateSolver D.T D.T_pos.le D.ℓ D.ℓ_pos D.F D.F₁ D.H D.M0 D.opInv
    D.Be D.Bc D.L D.r D.Be_nonneg D.Bc_nonneg D.L_lower D.r_nonneg D.r_le_quarter
    D.exterior_lower D.core_lower D.opInv_left D.opF_time D.K D.K_nonneg D.opInv_initial
    D.curvature_upper D.small

theorem coordinateSolver_reflection (hD : EvenData D) (f : TimeLp D.T L2) :
    timeSolenoidalReflection D.T (D.coordinateSolver f) = D.coordinateSolver (timeReflection D.T f)
        := by
  exact coerciveSolution_reflection D.T D.T_pos.le D.opF D.opF₁ D.opH
    (multiplier D.M0.field) (boundaryOperator (scaledCutoff D.ℓ D.ℓ_pos)) D.L
    (fun t => multiplier_reflection_of_even (D.F.field t) (hD.frame t))
    (fun t => multiplier_reflection_of_even (D.F₁.field t) (hD.frameDerivative t))
    (fun t => multiplier_reflection_of_even (D.H.field t) (hD.curvature t))
    (multiplier_reflection_of_even D.M0.field hD.initialStrain)
    (fun u => (scaledBoundaryOperator_reflection D.ℓ D.ℓ_pos u).symm)
    (sourceFixedCoercivity D.T D.F D.F₁ D.opInv)
    (sourceFixedCoercivity_pos D.T D.T_pos.le D.F D.F₁ D.opInv)
    (sourceFixedForm_coercive D.T D.T_pos.le D.ℓ D.ℓ_pos D.F D.F₁ D.H D.M0 D.opInv
      D.Be D.Bc D.L D.r D.Be_nonneg D.Bc_nonneg D.L_lower D.r_nonneg D.r_le_quarter
      D.exterior_lower D.core_lower D.opInv_left D.opF_time D.K D.K_nonneg D.opInv_initial
      D.curvature_upper D.small) f

end Data

namespace Forcing

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

theorem velocityLp_eq_coordinateSolver : G.solution.velocityLp = D.coordinateSolver G.lp :=
  EulerMeanSourceSpatialRegularity.velocity_eq_sourceCoordinates D.T D.T_pos.le D.ℓ D.ℓ_pos
    D.F D.F₁ D.H D.M0 D.opInv D.Be D.Bc D.L D.r D.Be_nonneg D.Bc_nonneg D.L_lower
    D.r_nonneg D.r_le_quarter D.exterior_lower D.core_lower D.opInv_left D.opF_time D.opInv_right
    D.K D.K_nonneg D.opInv_initial D.curvature_upper D.small G.lp G.solution

variable (hodd : ∀ (t : Icc (0 : ℝ) D.T) x, raw (t, (-x, 0)) = -raw (t, (x, 0)))

include hodd in
theorem path_reflection (t : Icc (0 : ℝ) D.T) : reflection (G.path t) = -(G.path t) := by
  apply Lp.ext
  filter_upwards [reflection_ae (G.path t),
    measurePreserving_reflection.quasiMeasurePreserving.ae
      (pathRepresentative_ae D.T G.path G.path_orbit t),
    pathRepresentative_ae D.T G.path G.path_orbit t, Lp.coeFn_neg (G.path t)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, G.forcingRepresentative_eq t (-x) 0, hodd t x, h₄]
  change -raw (t,(x,0)) = -(G.path t x)
  rw [h₃, G.forcingRepresentative_eq t x 0]

include hodd in
theorem lp_reflection : timeReflection D.T G.lp = -G.lp := by
  apply Lp.ext
  filter_upwards [timeReflection_ae D.T G.lp, G.lp_rep, Lp.coeFn_neg G.lp] with t h₁ h₂ h₃
  rw [h₁, h₂]
  change reflection (G.path (projIcc 0 D.T D.T_pos.le t)) = _
  rw [G.path_reflection hodd]
  exact (congrArg Neg.neg h₂).symm.trans h₃.symm

include hodd in
theorem velocityLp_reflection (hD : EvenData D) :
    timeSolenoidalReflection D.T G.solution.velocityLp = -G.solution.velocityLp :=
  (congrArg (timeSolenoidalReflection D.T) G.velocityLp_eq_coordinateSolver).trans
    ((D.coordinateSolver_reflection hD G.lp).trans
      ((congrArg D.coordinateSolver (G.lp_reflection hodd)).trans
        ((D.coordinateSolver.map_neg G.lp).trans
          (congrArg Neg.neg G.velocityLp_eq_coordinateSolver).symm)))

include hodd in
/-- Oddness of the actual L² solve holds pointwise for its continuous time representative. -/
theorem coordinate_velocity_reflection (hD : EvenData D) (t : Icc (0 : ℝ) D.T) :
    solenoidalReflection (G.solution.velocity t) = -G.solution.velocity t := by
  have hae : (fun r => solenoidalReflection (G.solution.velocity r)) =ᵐ[timeMeasure D.T]
      (fun r => -G.solution.velocity r) := by
    filter_upwards [timeSolenoidalReflection_ae D.T G.solution.velocityLp,
      G.solution.velocity_ae, Lp.coeFn_neg G.solution.velocityLp] with r h₁ h₂ h₃
    have he := congrArg (fun z : TimeLp D.T solenoidalSpace => z r) (G.velocityLp_reflection hodd
        hD)
    exact (congrArg solenoidalReflection h₂).symm.trans
      (h₁.symm.trans (he.trans (h₃.trans (congrArg Neg.neg h₂))))
  have hc : ContinuousOn G.solution.velocity (Icc (0 : ℝ) D.T) := by
    simpa only [uIcc_of_le D.T_pos.le] using G.solution.velocity_ac.continuousOn
  exact Measure.eqOn_Icc_of_ae_eq volume D.T_pos.ne hae
    (solenoidalReflection.continuous.comp_continuousOn hc) hc.neg t.property

end Forcing

end EulerMeanPacketProvider
