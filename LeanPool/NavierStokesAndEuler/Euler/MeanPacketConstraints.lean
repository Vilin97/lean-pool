/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketProvider
import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryPhysicalSupport
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints

/-!
# Classical constraints of the actual mean packet provider

The inverse-frame velocity is the smooth representative of the constructed
ordinary solenoidal coordinate velocity. Its divergence therefore vanishes
pointwise. The actual initial boundary condition supplies compact support.
-/

@[expose] public section


noncomputable section

namespace EulerMeanPacketProvider.Forcing

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanVariationalInverse EulerMeanScalarPressure
  EulerMeanSmoothRepresentative EulerMeanTimeContinuousTranslation EulerMeanCoordinatePath
  EulerMeanTimeTranslation EulerMeanClassical EulerVolterraConvolution EulerPacketPointJets
  EulerPacketProfileRecursion
open scoped ContDiff

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

/-- The actual solenoidal coordinate velocity, regarded in ordinary L². -/
def coordinateOrdinaryPath : C(Icc (0 : ℝ) D.T,L2) :=
  (solenoidalSpace.subtypeL.compLeftContinuous ℝ (Icc (0 : ℝ) D.T))
    G.solution.coordinateVelocityPath

@[simp] theorem coordinateOrdinaryPath_apply (t : Icc (0 : ℝ) D.T) :
    G.coordinateOrdinaryPath t = (G.solution.velocity t : L2) := rfl

theorem coordinateOrdinaryPath_orbit :
    ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a G.coordinateOrdinaryPath) := by
  let J : C(Icc (0 : ℝ) D.T,solenoidalSpace) →L[ℝ] C(Icc (0 : ℝ) D.T,L2) :=
    solenoidalSpace.subtypeL.compLeftContinuous ℝ (Icc (0 : ℝ) D.T)
  have hJ := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) D.T,solenoidalSpace)) (F := C(Icc (0 : ℝ) D.T,L2)) J
  exact hJ.comp G.coordinatePath_orbit

/-- The inverse-frame field is the actual solenoidal coordinate class. -/
theorem inverse_velocityPath (t : Icc (0 : ℝ) D.T) :
    D.opInv t (G.velocityPath t) = G.coordinateOrdinaryPath t := by
  exact (congrArg (D.opInv t)
    (G.solution.continuousVelocity_eq_physicalPath D.T_pos D.opF_time t)).trans
      ((congrArg (fun r : Icc (0 : ℝ) D.T =>
        D.opInv t (D.opF r (G.solution.velocity t : L2)))
        (projIcc_of_mem D.T_pos.le t.property)).trans
          (D.opInv_left t (G.solution.velocity t : L2)))

/-- This equality identifies the raw inverse-frame velocity pointwise. -/
theorem inverse_vector_eq_coordinate (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    D.inverseFrame (t,(x,θ)) (G.vector (t,(x,θ))) =
      pathRepresentative D.T G.coordinateOrdinaryPath G.coordinateOrdinaryPath_orbit t x := by
  have hae : (fun y => D.FInv t y (pathRepresentative D.T G.velocityPath G.velocityPath_orbit t y))
      =ᵐ[volume] pathRepresentative D.T G.coordinateOrdinaryPath G.coordinateOrdinaryPath_orbit t
          := by
    filter_upwards [pathRepresentative_ae D.T G.velocityPath G.velocityPath_orbit t,
      pathRepresentative_ae D.T G.coordinateOrdinaryPath G.coordinateOrdinaryPath_orbit t,
      multiplier_ae (D.FInv t) (G.velocityPath t)] with y hB hv hM
    have he := congrArg (fun z : L2 => z y) (G.inverse_velocityPath t)
    change multiplier (D.FInv t) (G.velocityPath t) y = G.coordinateOrdinaryPath t y at he
    rw [hM, hB, hv] at he
    exact he
  have he := congrFun (Measure.eq_of_ae_eq hae
    ((D.FInv t).continuous.clm_apply
      (pathRepresentative_smooth D.T G.velocityPath G.velocityPath_orbit t).continuous)
    (pathRepresentative_smooth D.T G.coordinateOrdinaryPath G.coordinateOrdinaryPath_orbit
        t).continuous) x
  simpa only [Data.inverseFrame, vector, Data.clamp_coe] using he

/-- The source's divergence constraint holds as an ordinary pointwise derivative. -/
theorem inverse_vector_divergence (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    divergence
      (fun y => D.inverseFrame (t,(y,θ)) (G.vector (t,(y,θ)))) x = 0 := by
  have he : (fun y => D.inverseFrame (t,(y,θ)) (G.vector (t,(y,θ)))) =
      pathRepresentative D.T G.coordinateOrdinaryPath G.coordinateOrdinaryPath_orbit t :=
    funext (fun y => G.inverse_vector_eq_coordinate t y θ)
  rw [he]
  exact representative_divergence (G.coordinateOrdinaryPath t) (G.solution.velocity t).property
    (pathTranslation_evaluation_contDiff D.T G.coordinateOrdinaryPath
        G.coordinateOrdinaryPath_orbit t) x

theorem inverse_vector_smooth (t : Icc (0 : ℝ) D.T) (θ : ℝ) :
    ContDiff ℝ ∞ (fun y => D.inverseFrame (t,(y,θ)) (G.vector (t,(y,θ)))) := by
  have he : (fun y => D.inverseFrame (t,(y,θ)) (G.vector (t,(y,θ)))) =
      pathRepresentative D.T G.coordinateOrdinaryPath G.coordinateOrdinaryPath_orbit t :=
    funext (fun y => G.inverse_vector_eq_coordinate t y θ)
  rw [he]
  exact pathRepresentative_smooth D.T G.coordinateOrdinaryPath G.coordinateOrdinaryPath_orbit t

/-- The initial raw velocity is the actual localized boundary value. -/
theorem initial_vector_ae (θ : ℝ) :
    (fun x => G.vector (0,(x,θ))) =ᵐ[volume]
      (D.L • boundaryOperator (scaledCutoff D.ℓ D.ℓ_pos) (G.solution.label 0 : L2) : L2) := by
  let t₀ : Icc (0 : ℝ) D.T := ⟨0, le_rfl, D.T_pos.le⟩
  have hr := (pathRepresentative_ae D.T G.velocityPath G.velocityPath_orbit t₀).symm
  have hi : G.velocityPath t₀ =
      D.L • boundaryOperator (scaledCutoff D.ℓ D.ℓ_pos) (G.solution.label 0 : L2) :=
    (G.solution.continuousVelocity_eq_physicalPath D.T_pos D.opF_time t₀).trans
      (G.solution.physicalPath_initial D.opF_initial)
  rw [hi] at hr
  simpa only [vector, Data.clamp, projIcc_of_mem D.T_pos.le (show (0 : ℝ) ∈ Icc 0 D.T from
    ⟨le_rfl, D.T_pos.le⟩), t₀] using hr

/-- The initial support is contained in the source's scaled radius-two ball. -/
theorem initial_vector_support (θ : ℝ) :
    tsupport (fun x => G.vector (0,(x,θ))) ⊆ {x : Space | ‖D.ℓ • x‖ ≤ 2} :=
  scaledBoundary_continuous_support D.ℓ D.ℓ_pos D.L (G.solution.label 0 : L2)
    (fun x => G.vector (0,(x,θ)))
    ((G.vector_spatial_smooth 0).continuous.comp (continuous_id.prodMk continuous_const))
    (G.initial_vector_ae θ)

theorem initial_vector_compact (θ : ℝ) : HasCompactSupport (fun x => G.vector (0,(x,θ))) :=
  scaledBoundary_continuous_compact D.ℓ D.ℓ_pos D.L (G.solution.label 0 : L2)
    (fun x => G.vector (0,(x,θ)))
    ((G.vector_spatial_smooth 0).continuous.comp (continuous_id.prodMk continuous_const))
    (G.initial_vector_ae θ)

/-- The time-space representative is jointly continuous on the actual interval. -/
theorem vector_joint_continuous :
    Continuous (fun z : Icc (0 : ℝ) D.T × (Space × ℝ) => G.vector (z.1,z.2)) := by
  have hmap : Continuous (fun z : Icc (0 : ℝ) D.T × (Space × ℝ) => (z.1,z.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hc := (pathRepresentative_continuous D.T G.velocityPath G.velocityPath_orbit).comp hmap
  simpa only [vector, Data.clamp_coe, Function.comp_def] using hc

end EulerMeanPacketProvider.Forcing
