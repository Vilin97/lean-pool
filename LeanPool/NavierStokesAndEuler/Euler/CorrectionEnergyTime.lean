/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordValueIdentity
public import LeanPool.NavierStokesAndEuler.Euler.RegularizedMetricPaths
public import LeanPool.NavierStokesAndEuler.Euler.EnergyWordCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionForcing
public import LeanPool.NavierStokesAndEuler.Euler.TimeCorrectionSource
public import LeanPool.NavierStokesAndEuler.Euler.TransportL2Time
import LeanPool.NavierStokesAndEuler.Euler.ProjectedForcingFields
import LeanPool.NavierStokesAndEuler.Euler.RegularizedForcingRepresentative
import LeanPool.NavierStokesAndEuler.Euler.TimeCorrectionStrongIdentity

/-! Constructed nonlinear time fields and their exact full-order metric forcing for the Euler
correction. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionEnergyTime

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSpatialSobolevInverse EulerCorrectionOperators EulerTimeCorrectionSource
  EulerTimeCorrectionStrongIdentity EulerSobolevWordValueIdentity EulerTimeLp
      EulerVolterraConvolution
  EulerRegularizedEnergyFamily EulerRegularizedForcingRepresentative EulerRegularizedMetricPaths
  EulerRegularizedTopBlocks EulerTransportL2Time EulerWeightedForcingTime EulerSobolevEnergyPaths
  EulerEnergyWordCoordinates  EulerGevreyCorrectionForcing
  EulerGevreyMetricComparison EulerBaseWordMetric EulerSobolevTransport
      EulerSobolevCoefficientPressure
  EulerMildTopWord EulerFiniteMetricEnergy EulerWeightedCylinderEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A local concrete normed-group instance for the actual cylinder Sobolev scale. -/
local instance correctionTimeGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance

/-- A local concrete real normed-space instance for the actual cylinder Sobolev scale. -/
local instance correctionTimeSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual continuous background-plus-error velocity at the energy level. -/
def velocityPath {q : ℕ} {T : ℝ} (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, SobolevSpace period
        (q+1))
        :=
  (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) D.approximation + e

/-- The actual continuous order-zero source along the original energy-level solution. -/
def lowerOrderPath {q : ℕ} (hq : 6 ≤ q + 1) {T : ℝ} (D : CorrectionData period (q + 1) (Icc (0 : ℝ)
    T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, SobolevSpace period
        (q+1))
        :=
  orderZeroPath period hq T (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    D.linear.operatorPath (fun i => (D.quadratic i).operatorPath) D.approximation D.residual e

/-- The genuine full energy-order nonlinear raw time field, constructed using maximal regularity. -/
def rawTime {q : ℕ} (hq : 6 ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 +
        q))) :
    TimeLp T (SobolevSpace period (q+1)) :=
  rawSourceTime period hq T hT (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    D.linear.operatorPath (fun i => (D.quadratic i).operatorPath) D.approximation D.residual e
    (reindexMaximalTime period q T U)

/-- The actual full energy-order projected nonlinear forcing belongs to Bochner L² time. -/
def sourceTime {q : ℕ} (hq : 6 ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 +
        q))) :
    TimeLp T (SobolevSpace period (q+1)) :=
  projectedTime period T hT D.metric D.κ D.direction D.coercivity D.coercivity_pos D.metric_pos
    (rawTime period hq T hT D e U)

/-- The actual signed coercive pressure has full energy-order Bochner regularity. -/
def signedPressureTime {q : ℕ} (hq : 6 ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 +
        q))) :
    TimeLp T (SobolevSpace period (q+1)) :=
  pressureTime period T hT D.metric D.κ D.direction D.coercivity D.coercivity_pos D.metric_pos
    (rawTime period hq T hT D e U)

/-- The actual limiting weighted word forcing constructed from the genuine correction time fields.
-/
def weightedCorrectionForcing {q : ℕ} (hq : 6 ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (R : C(Icc (0 : ℝ) T, ℝ))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 +
        q))) :
        TimeLp T ℝ :=
  weightedForcingTime T hT (fun I : ExternalWord N => gevreyWeightPath T R I.1.val)
    (forcingFamilyTime period energyLength energyWord (energyLength_le hN) T hT
      (transportL2Path period (by omega : 3 ≤ q+1) D.κ D.direction T (velocityPath period D e))
      (metricOperatorPath period T D.metric.coefficient hG) U
      (sourceTime period hq T hT D e U) (signedPressureTime period hq T hT D e U))

/-- The seven literal spatial correction terms evaluated on an actual higher Sobolev representative.
-/
def correctionArray {q : ℕ} (hq : 6 ≤ q + 1) {T : ℝ}
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (K6 : ∀ t, CoefficientJet period standardDirection 6 (D.metric.coefficient t))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (V : SobolevSpace period ((q + 1) + 1)) (τ : Icc (0 : ℝ) T) : ExternalWord N → BaseWord 6 →
        LiftL2
        period :=
  let f := lowerOrderPath period hq D e τ
  correctionForcing period hq (D.metric.jet τ) (K6 τ) N hN (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    (D.approximation τ+V) V f
    (pressureSobolevOperator period (D.metric.jet τ) D.κ D.direction D.coercivity D.coercivity_pos
        (D.metric_pos τ) f)
    (pressureSobolevOperator period (D.metric.jet τ) D.κ D.direction D.coercivity D.coercivity_pos
        (D.metric_pos τ)
      (transportBilinear period hq (velocityComponents D.κ D.direction)
        (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) (D.approximation
            τ+V) V))

/-- The constructed actual weighted time forcing is exactly the seven genuine correction terms
almost everywhere. -/
theorem weightedCorrectionForcing_ae {q : ℕ} (hq : 6 ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (K6 : ∀ t, CoefficientJet period standardDirection 6 (D.metric.coefficient t))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (R : C(Icc (0 : ℝ) T, ℝ))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e)) Filter.atTop
        (𝓝 U)) :
    (weightedCorrectionForcing period hq T hT D hG N hN R e U : ℝ → ℝ) =ᵐ[timeMeasure T]
      fun t => weightedForcingSum (R (projIcc 0 T hT t)) (fun I : ExternalWord N => I.1.val)
        (correctionArray period hq D K6 N hN e (reindexMaximalTime period q T U t) (projIcc 0 T hT
            t)) := by
  let V := reindexMaximalTime period q T U
  let A := transportL2Path period (by omega : 3 ≤ q+1) D.κ D.direction T (velocityPath period D e)
  let G := metricOperatorPath period T D.metric.coefficient hG
  let F := sourceTime period hq T hT D e U
  let P := signedPressureTime period hq T hT D e U
  let raw := rawTime period hq T hT D e U
  have hV := reindexMaximalTime_restriction period T hT e U hU
  have hr := rawSourceTime_transport_ae period hq T hT (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    D.linear.operatorPath (fun i => (D.quadratic i).operatorPath) D.approximation D.residual e V hV
  have hv := transport_velocity_value_ae period T hT D.approximation e V hV
  filter_upwards [weighted_forcing_ae period energyLength energyWord (energyLength_le hN) T hT
      (fun I : ExternalWord N => gevreyWeightPath T R I.1.val) A G U F P,
    hr, hv, reindexMaximalTime_value period q T U,
    projectedTime_ae period T hT D.metric D.κ D.direction D.coercivity D.coercivity_pos
        D.metric_pos raw,
    pressureTime_ae period T hT D.metric D.κ D.direction D.coercivity D.coercivity_pos D.metric_pos
        raw]
    with t hweight hraw hvel hVU hF hP
  change weightedForcingTime T hT _ (forcingFamilyTime period energyLength energyWord
      (energyLength_le hN) T hT A G U F P) t = _
  rw [hweight]
  apply Finset.sum_congr rfl
  intro I _
  apply congrArg (fun v : BaseWord 6 → LiftL2 period => EulerPacketWeights.weight (R (projIcc 0 T
      hT t)) I.1.val * familyNorm v)
  funext a
  let τ := projIcc 0 T hT t
  change word period (F t) (energyLength_le hN I a) (energyWord I a) +
    transportL2Path period (by omega : 3 ≤ q+1) D.κ D.direction T (velocityPath period D e) τ
      (boundedWordBlock period 1 (energyLength I a) (by
          have := energyLength_le hN I a; omega) (energyWord I a) (U t)) +
    (D.metric.coefficient τ).operator (word period (P t) (energyLength_le hN I a) (energyWord I a))
        = _
  rw [transportL2Path_apply]
  exact EulerProjectedForcingFields.forcing_word_of_actual_fields period hq (D.metric.jet τ) (K6 τ)
      N hN
    D.κ D.direction D.coercivity D.coercivity_pos (D.metric_pos τ)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    (velocityPath period D e τ) (D.approximation τ+V t) (V t) (U t) hvel hVU.symm
    (lowerOrderPath period hq D e τ) (raw t) (F t) (P t) hraw hF hP I a
    (by have := energyLength_le hN I a; omega)

end EulerCorrectionEnergyTime
