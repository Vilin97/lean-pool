/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyTime
public import LeanPool.NavierStokesAndEuler.Euler.EnergyMetricPaths
public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricForcing

@[expose] public section

/-! The actual nonlinear Bochner forcing is bounded by a continuous metric-energy polynomial, with
  constants independent of the external cutoff. -/

noncomputable section

namespace EulerCorrectionEnergyBound

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerCorrectionEnergyTime
    EulerEnergyMetricPaths
  EulerGevreyMetricEstimate EulerGevreyCorrectionBound EulerH6Pressure EulerSobolevGevreyOperators
  EulerSobolevTransportCommutator EulerSobolevTransport EulerH6Nonlinear
    EulerGevreyMetricComparison EulerTimeLp EulerVolterraConvolution EulerSobolevWordValueIdentity
  EulerRegularizedTopBlocks EulerGevreyOrderZero EulerTimeCorrectionSource
    EulerWeightedCylinderEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A local concrete normed-group instance for the actual Sobolev energy scale. -/
local instance boundTimeGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance

/-- A local concrete real normed-space instance for the actual Sobolev energy scale. -/
local instance boundTimeSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The explicit scalar majorant for the genuine seven-term nonlinear metric forcing. -/
def forcingPolynomial (B M B0 B1 A0 A2 residual cM Rc ρ X Y : ℝ) : ℝ :=
  sourceConstant B M*residual+
    ((sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period
      3*B0)+transportConstant period B M*B0)*
      metricAmplification cM)*X+
    ((sourceConstant B M*A2*productConstant period 3+transportConstant period B
      M)*(metricAmplification cM)^2)*X^2+
    ((lossConstant period M*(ρ⁻¹+Rc))*(metricAmplification cM)^2)*(B0+X)*Y

/-- The literal spatial correction array has the actual metric polynomial bound for every valid higher representative. -/
theorem correctionArray_bound {q : ℕ} (hq : 6 ≤ q+1) {T : ℝ}
    (D : CorrectionData period (q+1) (Icc (0 : ℝ) T))
    (K6 : ∀ t, CoefficientJet period standardDirection 6 (D.metric.coefficient t))
    (N : ℕ) (hN : N+6 ≤ q+1) (τ : Icc (0 : ℝ) T)
    (ρ Rc M B : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M) (hB : 0 ≤ B)
    (hbase5 : (EulerH6Pressure.CoefficientJet.restrict (D.metric.jet τ) 5 (by
      omega)).pressureConstant D.coercivity ≤ M)
    (hbase6 : (EulerH6Pressure.CoefficientJet.restrict (D.metric.jet τ) 6 hq).pressureConstant
      D.coercivity ≤ M)
    (hsmall : 4*M*(ρ*Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period (D.metric.jet τ) 6 l ≤ Rc^l*(l.factorial
      : ℝ)^2)
    (hG : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period (D.metric.jet τ) r ≤ B)
    (hG0 : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period (K6 τ) r ≤ B)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q+1))) (V : SobolevSpace period ((q+1)+1))
    (hV : truncateOperator period (q+1) V = e τ)
    (B0 B1 A0 A2 residual : ℝ) (hA2 : 0 ≤ A2)
    (hz : weightedNorm period 6 N ρ (D.approximation τ) ≤ B0)
    (hdz : (∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator period (q+1) i
      (D.approximation τ))) ≤ B1)
    (hC0 : weightedCoefficient period (D.linear.jet τ) 6 N ρ ≤ A0)
    (hC : (∑ i : Fin 3, weightedCoefficient period ((D.quadratic i).jet τ) 6 N ρ) ≤ A2)
    (hr : weightedNorm period 6 N ρ (D.residual τ) ≤ residual)
    (KM : LiftL2 period →L[ℝ] LiftL2 period) (cM : ℝ) (hcM : 0 < cM)
    (hKM : ∀ v, cM^2*‖v‖^2 ≤ ⟪KM v,v⟫_ℝ) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val)
      (correctionArray period hq D K6 N hN e V τ) ≤
      forcingPolynomial period B M B0 B1 A0 A2 residual cM Rc ρ
        (energyNorm period N (by omega : N+6 ≤ (q+1)+1) ρ KM V)
        (energyLoss period N (by omega : N+6 ≤ (q+1)+1) ρ KM V) := by
  have h := correctionForcing_metric period hq (D.metric.jet τ) (K6 τ) D.κ D.direction D.coercivity
    D.coercivity_pos (D.metric_pos τ) N hN ρ Rc M B hρ hRc hM hB hbase5 hbase6 hsmall hcoeff hG hG0
    (velocityComponents D.κ D.direction) (velocityComponents_norm D.κ D.direction D.scale_bound
      D.direction_bound)
    (D.linear.coefficient τ) (D.linear.jet τ) (fun i => (D.quadratic i).coefficient τ) (fun i =>
      (D.quadratic i).jet τ)
    (D.approximation τ) V (D.residual τ) B0 B1 A0 A2 residual hA2 hz hdz hC0 hC hr KM cM hcM hKM
  simpa only [correctionArray, lowerOrderPath, orderZeroPath, ContinuousMap.coe_mk,
    CoefficientPath.operatorPath, EulerGevreyPressureTransport.transportPressure, hV,
    forcingPolynomial] using h

/-- The literal polynomial majorant is continuous along the positive radius and actual continuous metric energies. -/
def forcingBoundPath {q : ℕ} (N : ℕ) (hN : N+6 ≤ q+1) (T : ℝ)
    (R : C(Icc (0 : ℝ) T, ℝ)) (hR : ∀ t, 0 < R t)
    (K : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (B M B0 B1 A0 A2 residual cM Rc : ℝ) : C(Icc (0 : ℝ) T, ℝ) := by
  let X := energyPath period N hN T R K e
  let Y := lossPath period N hN T R K e
  refine ⟨fun t => forcingPolynomial period B M B0 B1 A0 A2 residual cM Rc (R t) (X t) (Y t), ?_⟩
  have hi : Continuous (fun t => (R t)⁻¹) := R.continuous.inv₀ (fun t => (hR t).ne')
  unfold forcingPolynomial
  fun_prop

/-- The actual constructed full-order Bochner forcing obeys the continuous spatial majorant almost everywhere. -/
theorem weightedCorrectionForcing_bound {q : ℕ} (hq : 6 ≤ q+1) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q+1) (Icc (0 : ℝ) T))
    (hGc : Continuous (fun t => (D.metric.coefficient t).operator))
    (K6 : ∀ t, CoefficientJet period standardDirection 6 (D.metric.coefficient t))
    (N : ℕ) (hN : N+6 ≤ q+1) (R : C(Icc (0 : ℝ) T, ℝ)) (hR : ∀ t, 0 < R t)
    (Rc M B : ℝ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M) (hB : 0 ≤ B)
    (hbase5 : ∀ t, (EulerH6Pressure.CoefficientJet.restrict (D.metric.jet t) 5 (by
      omega)).pressureConstant D.coercivity ≤ M)
    (hbase6 : ∀ t, (EulerH6Pressure.CoefficientJet.restrict (D.metric.jet t) 6 hq).pressureConstant
      D.coercivity ≤ M)
    (hsmall : ∀ t, 4*M*(R t*Rc) ≤ 1)
    (hcoeff : ∀ t l, 1 ≤ l → l ≤ N → coefficientBlock period (D.metric.jet t) 6 l ≤
      Rc^l*(l.factorial : ℝ)^2)
    (hG : ∀ t r, r ≤ 6 → EulerJetProductBounds.boundLevel period (D.metric.jet t) r ≤ B)
    (hG0 : ∀ t r, r ≤ 6 → EulerJetProductBounds.boundLevel period (K6 t) r ≤ B)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q+1))) (U : TimeLp T (SobolevSpace period (2+q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e)) Filter.atTop
      (𝓝 U))
    (B0 B1 A0 A2 residual : ℝ) (hA2 : 0 ≤ A2)
    (hz : ∀ t, weightedNorm period 6 N (R t) (D.approximation t) ≤ B0)
    (hdz : ∀ t, (∑ i : Fin 4, weightedNorm period 6 N (R t) (derivativeOperator period (q+1) i
      (D.approximation t))) ≤ B1)
    (hC0 : ∀ t, weightedCoefficient period (D.linear.jet t) 6 N (R t) ≤ A0)
    (hC : ∀ t, (∑ i : Fin 3, weightedCoefficient period ((D.quadratic i).jet t) 6 N (R t)) ≤ A2)
    (hr : ∀ t, weightedNorm period 6 N (R t) (D.residual t) ≤ residual)
    (K : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period)) (cM : ℝ) (hcM : 0 < cM)
    (hKM : ∀ t v, cM^2*‖v‖^2 ≤ ⟪K t v,v⟫_ℝ) :
    (weightedCorrectionForcing period hq T hT D hGc N hN R e U : ℝ → ℝ) ≤ᵐ[timeMeasure T]
      extendPath T hT (forcingBoundPath period N hN T R hR K e B M B0 B1 A0 A2 residual cM Rc) := by
  filter_upwards [weightedCorrectionForcing_ae period hq T hT D hGc K6 N hN R e U hU,
    reindexMaximalTime_restriction period T hT e U hU,
    maximal_metric_paths period N hN T hT R K e U hU] with t hforce hv hmetric
  let τ := projIcc 0 T hT t
  have h := correctionArray_bound period hq D K6 N hN τ (R τ) Rc M B (hR τ) hRc hM hB
    (hbase5 τ) (hbase6 τ) (hsmall τ) (hcoeff τ) (hG τ) (hG0 τ) e
    (reindexMaximalTime period q T U t) hv B0 B1 A0 A2 residual hA2 (hz τ) (hdz τ) (hC0 τ) (hC τ)
      (hr τ)
    (K τ) cM hcM (hKM τ)
  rw [hmetric.1, hmetric.2] at h
  exact hforce.le.trans h

end EulerCorrectionEnergyBound
