/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryAdvectionLimit
import LeanPool.NavierStokesAndEuler.Euler.MeanPressurePotential
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryStrongTime

/-! A common-interval Euler limit constructed from genuine smooth Euler
evolutions. The only compactness inputs are actual uniform Sobolev
bounds and L² Cauchy convergence. The nonlinear term, pressure, and
time equation are all recovered in the proof. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral
open scoped ContDiff Topology

namespace SmoothLimitData

variable {T : ℝ} {hT : 0 ≤ T} {V : ℕ → Evolution T hT}
  (L : SmoothLimitData (fun k => (V k).velocity) (fun k => (V k).velocity_continuous))

theorem field_mem_solenoidal (t : Icc (0 : ℝ) T) : (L.field t).toLp ∈ solenoidalSpace :=
  gradientSpace.isClosed_orthogonal.mem_of_tendsto (L.toLp_convergence t)
    (Eventually.of_forall (fun k => (V k).solenoidal t))

theorem field_integral_equation (hpos : 0 < T) (M : ℝ)
    (hb : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M) (t : Icc (0 : ℝ) T) :
    (L.field t).toLp=(L.field ⟨0,le_rfl,hT⟩).toLp +
      integral T hT (projectedRhsPath L.field L.field_continuous) t := by
  have hg := L.projectedRhsPath_convergence hT M hb
  have hi := (ContinuousMap.evalCLM ℝ t).continuous.tendsto
    (integral T hT (projectedRhsPath L.field L.field_continuous)) |>.comp
      (((integral (E := L2) T hT).continuous.tendsto _).comp hg)
  have hsum := (L.toLp_convergence ⟨0,le_rfl,hT⟩).add hi
  have he (k : ℕ) : ((V k).velocity t).toLp=((V k).velocity ⟨0,le_rfl,hT⟩).toLp +
      integral T hT (projectedRhsPath (V k).velocity (V k).velocity_continuous) t := by
    have h := congrArg (fun p : C(Icc (0 : ℝ) T,L2) => p t) ((V k).velocity_integral_equation hpos)
    simpa only [Evolution.velocityPath_apply,ContinuousMap.add_apply,ContinuousMap.const_apply,
      Evolution.projectedPath,projectedRhsPath] using h
  exact tendsto_nhds_unique (L.toLp_convergence t) (hsum.congr (fun k => (he k).symm))

theorem field_hasDerivWithinAt (hpos : 0 < T) (M : ℝ)
    (hb : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r => (L.field (projIcc 0 T hT r)).toLp)
      (projectedRhs (L.field t)).toLp (Icc (0 : ℝ) T) t := by
  have he : (fun r => (L.field (projIcc 0 T hT r)).toLp) =
      fun r => (L.field ⟨0,le_rfl,hT⟩).toLp +
        extendPath T hT (integral T hT (projectedRhsPath L.field L.field_continuous)) r := by
    funext r
    exact L.field_integral_equation hpos M hb (projIcc 0 T hT r)
  rw [he]
  exact (integral_hasDerivWithinAt T hT (projectedRhsPath L.field L.field_continuous) t).const_add _

/-- To evolution, bundling `velocity`, `pressureForce`, `velocity_continuous`,
`pressure_continuous` and the required compatibility proofs. -/
def toEvolution (hpos : 0 < T) (M : ℝ)
    (hb : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M) : Evolution T hT where
  velocity := L.field
  pressureForce t := pressureField (L.field t)
  velocity_continuous := L.field_continuous
  pressure_continuous := pressureField_continuous L.field L.field_continuous
  solenoidal := L.field_mem_solenoidal
  gradient t := pressureField_mem_gradient (L.field t)
  time_law t ht x := by
    have hd : ∀ r (hr : r ∈ Ioo 0 T),
        HasDerivAt (fun s => (L.field (projIcc 0 T hT s)).toLp)
          (projectedRhs (L.field ⟨r,hr.1.le,hr.2.le⟩)).toLp r := by
      intro r hr
      exact (L.field_hasDerivWithinAt hpos M hb ⟨r,hr.1.le,hr.2.le⟩).hasDerivAt
        (Icc_mem_nhds hr.1 hr.2)
    have h := pointwise_derivative_of_l2 T hT L.field (fun s => projectedRhs (L.field s))
      L.field_continuous (projectedRhs_continuous L.field L.field_continuous) hd
      ⟨t,ht.1.le,ht.2.le⟩ x
    simpa only [projectedRhs_field] using h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end SmoothLimitData

variable {T : ℝ} {hT : 0 ≤ T}

/-- Euler limit data, given by `smoothLimitData hT (fun k => (V k).velocity) (fun k => (V
k).velocity_continuous) hb h0`. -/
def eulerLimitData (V : ℕ → Evolution T hT)
    (hb : ∀ q, ∃ M : ℝ, ∀ k t, tensorNorm q ((V k).velocity t) ≤ M)
    (h0 : CauchySeq (fun k => fieldPath (V k).velocity (V k).velocity_continuous)) :
    SmoothLimitData (fun k => (V k).velocity) (fun k => (V k).velocity_continuous) :=
  smoothLimitData hT (fun k => (V k).velocity) (fun k => (V k).velocity_continuous) hb h0

/-- Limit evolution, given by `(eulerLimitData V hb h0).toEvolution hpos (Classical.choose (hb
3)) (Classical.choose_spec (hb 3))`. -/
def limitEvolution (V : ℕ → Evolution T hT) (hpos : 0 < T)
    (hb : ∀ q, ∃ M : ℝ, ∀ k t, tensorNorm q ((V k).velocity t) ≤ M)
    (h0 : CauchySeq (fun k => fieldPath (V k).velocity (V k).velocity_continuous)) : Evolution T hT
        :=
  (eulerLimitData V hb h0).toEvolution hpos (Classical.choose (hb 3)) (Classical.choose_spec (hb 3))

theorem limitEvolution_jet_convergence (V : ℕ → Evolution T hT) (hpos : 0 < T)
    (hb : ∀ q, ∃ M : ℝ, ∀ k t, tensorNorm q ((V k).velocity t) ≤ M)
    (h0 : CauchySeq (fun k => fieldPath (V k).velocity (V k).velocity_continuous)) (q : ℕ) :
    Tendsto (fun k => jetPath (V k).velocity (V k).velocity_continuous q) atTop
      (𝓝 (jetPath (limitEvolution V hpos hb h0).velocity
        (limitEvolution V hpos hb h0).velocity_continuous q)) :=
  (eulerLimitData V hb h0).jetPath_convergence q

theorem limitEvolution_initial (V : ℕ → Evolution T hT) (hpos : 0 < T)
    (hb : ∀ q, ∃ M : ℝ, ∀ k t, tensorNorm q ((V k).velocity t) ≤ M)
    (h0 : CauchySeq (fun k => fieldPath (V k).velocity (V k).velocity_continuous))
    (u0 : L2) (hu0 : Tendsto (fun k => ((V k).velocity ⟨0, le_rfl, hT⟩).toLp) atTop (𝓝 u0)) :
    ((limitEvolution V hpos hb h0).velocity ⟨0,le_rfl,hT⟩).toLp=u0 :=
  tendsto_nhds_unique ((eulerLimitData V hb h0).toLp_convergence ⟨0,le_rfl,hT⟩) hu0

theorem limitEvolution_bound (V : ℕ → Evolution T hT) (hpos : 0 < T)
    (hb : ∀ q, ∃ M : ℝ, ∀ k t, tensorNorm q ((V k).velocity t) ≤ M)
    (h0 : CauchySeq (fun k => fieldPath (V k).velocity (V k).velocity_continuous))
    (q : ℕ) (M : ℝ) (hM : ∀ k t, tensorNorm q ((V k).velocity t) ≤ M) (t : Icc (0 : ℝ) T) :
    tensorNorm q ((limitEvolution V hpos hb h0).velocity t) ≤ M :=
  (eulerLimitData V hb h0).tensorNorm_bound q M hM t

namespace Evolution

/-- Scalar pressure, given by `EulerCanonicalGraphPotential.radialPotential (U.pressureForce
t).field`. -/
def scalarPressure (U : Evolution T hT) (t : Icc (0 : ℝ) T) : Space → ℝ :=
  EulerCanonicalGraphPotential.radialPotential (U.pressureForce t).field

theorem scalarPressure_spec (U : Evolution T hT) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (U.scalarPressure t) ∧ U.scalarPressure t 0=0 ∧
      ∀ x, _root_.gradient (U.scalarPressure t) x=(U.pressureForce t).field x :=
  EulerMeanPressure.gradientSpace_radial_potential (U.pressureForce t).toLp (U.gradient t)
    (U.pressureForce t).field (U.pressureForce t).toLp_ae (U.pressureForce t).smooth

end Evolution
end EulerOrdinarySobolev
