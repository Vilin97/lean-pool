/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyMajorants
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpSubintervalBound
import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyRestriction
import LeanPool.NavierStokesAndEuler.Euler.MildMajorantEnergy
import LeanPool.NavierStokesAndEuler.Euler.SobolevMaximalRegularity

/-! Actual nonlinear correction mild solutions obey the full-order continuous scalar integral energy
estimate. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionMildEnergy

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionEnergyRestriction EulerCorrectionEnergyTime EulerCorrectionEnergyData
      EulerCorrectionEnergyMajorants
  EulerEnergyMetricPaths EulerGevreyMetricEstimate EulerMildMajorantEnergy
      EulerEnergyWordCoordinates
  EulerTimeLpSubintervalBound EulerTimeLp EulerVolterraConvolution EulerSobolevHeat
      EulerSobolevMaximalRegularity
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual continuous scalar right-hand side of the nonlinear correction energy estimate. -/
def correctionRhs {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) (hN : N + 6 ≤ q + 1) {hT : 0 ≤ T} (K : MetricBudget period
        T hT
        D)
    (Rdot : C(Icc (0 : ℝ) T, ℝ)) (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ)
        T, ℝ) :=
  scalarEnergyRhs T (growthPath period S hN K e) (radiusLossPath R Rdot S.radius_pos)
    (ContinuousMap.const _ (K.multiplier period))
    (energyPath period N hN T R (K.operatorPath period) e)
    (lossPath period N hN T R (K.operatorPath period) e) (forcingMajorant period S hN K e)

/-- The actual nonlinear lower mild equation yields the full energy-order scalar integral bound on
every subinterval.
Maximal regularity, the higher nonlinear source, the pressure, and their constraints are all
constructed or proved inside the argument. -/
theorem correction_mild_integral {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hGq : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hLq : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQq : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (R Rdot : C(Icc (0 : ℝ) T, ℝ))
    (S : SpatialBudget period (by omega : 6 ≤ q + 1) D N R) (K : MetricBudget period T hT D)
    (hRd : ∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT R) (extendPath T hT Rdot t) t)
    (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (e₀ : SobolevSpace period (q + 1))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      e t = heatOperator period (q+1) (2*ν*t.val).toNNReal e₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
          (extendPath T hT (forcingPath period hq (lowerData period D KG KL KQ hGq hLq hQq) e)
              (t.val-r)))
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (he : ∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction)
    (s t : ℝ) (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    energyPath period N hN T R (K.operatorPath period) e ⟨t,h0s.trans hst,htT⟩ -
      energyPath period N hN T R (K.operatorPath period) e ⟨s,h0s,hst.trans htT⟩ ≤
      ∫ r in s..t, extendPath T hT (correctionRhs period S hN K Rdot e) r := by
  let Dlow := lowerData period D KG KL KQ hGq hLq hQq
  let f := forcingPath period hq Dlow e
  let p := pressurePath period hq Dlow e
  obtain ⟨U,hU⟩ := exists_maximal_mild_limit period ν hν T hT e₀ f e hsol
  let F := sourceTime period (by omega : 6 ≤ q+1) T hT D e U
  let P := signedPressureTime period (by omega : 6 ≤ q+1) T hT D e U
  let X := energyPath period N hN T R (K.operatorPath period) e
  let Y := lossPath period N hN T R (K.operatorPath period) e
  let k : C(Icc (0 : ℝ) T, ℝ) := ContinuousMap.const _ (K.multiplier period)
  have hF := sourceTime_restriction period hq T hT D KG KL KQ hGq hLq hQq e U hU
  have hP := signedPressureTime_restriction period hq T hT D KG KL KQ hGq hLq hQq e U hU
  have henergy := mild_majorized_energy_subinterval period (by omega : 3 ≤ q+1) T hT s t h0s hst htT
    energyLength energyWord (energyLength_le hN) (fun I : EulerGevreyMetricComparison.ExternalWord
        N => I.1.val)
    ν hν D.κ D.direction K.c K.c_pos R Rdot S.radius_pos hRd K.metric D.metric.coefficient
    K.continuous hG K.derivative K.hasDeriv K.symmetric K.coercive K.inverse
    (fun τ => metricVelocityBound period K.c S.B0 (X τ)) (velocityPath period D e) e e₀ f p hsol he
    (pressurePath_gradient period hq Dlow e)
    (velocity_divergenceFree period D e hz he) (velocity_bound period S hN K e)
    U F P hU hF hP (growthPath period S hN K e) (radiusLossPath R Rdot S.radius_pos) k
    (growthPath_bound period S hN K e ν hν1) (fun _ => rfl)
    (fun τ => div_le_div_of_nonneg_right (K.bound_le τ) K.c_pos.le)
  have hforce := forcingMajorant_bound period S hN K hG e U hU
  have hk : ∀ τ, 0 ≤ k τ := fun _ => (K.constants_nonneg period S.B0 S.B0_nonneg).2.2
  exact scalar_rhs_subinterval T hT s t h0s hst htT
    (growthPath period S hN K e) (radiusLossPath R Rdot S.radius_pos) k X Y
    (forcingMajorant period S hN K e) hk
    (weightedCorrectionForcing period (by omega : 6 ≤ q+1) T hT D hG N hN R e U) hforce henergy

end EulerCorrectionMildEnergy
