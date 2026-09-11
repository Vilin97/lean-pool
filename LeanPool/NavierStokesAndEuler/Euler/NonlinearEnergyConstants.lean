/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.Euler.GevreyGrowthCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyTime
public import LeanPool.NavierStokesAndEuler.Euler.EnergyMetricPaths
public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionBound
public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricEstimate
public import LeanPool.NavierStokesAndEuler.Euler.GevreyOrderZero
import LeanPool.NavierStokesAndEuler.Euler.GevreyNonlinearEstimate

/-! One explicit cutoff-independent scalar constant absorbs the actual metric growth and nonlinear
forcing coefficients. -/

section

/-! The actual nonlinear Bochner forcing is bounded by a continuous metric-energy polynomial, with
constants independent of the external cutoff. -/

section

/-! The actual complete Euler forcing estimate in metric-energy variables. -/

@[expose] public section

noncomputable section

namespace EulerGevreyMetricEstimate

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerSobolevGevreyOperators
      EulerGevreyCorrectionForcing
  EulerH6Nonlinear EulerSobolevTransportCommutator EulerGevreyPressureTransport
      EulerSobolevCoefficientPressure
  EulerGevreyMetricComparison EulerWeightedCylinderEnergy
      EulerGevreyOrderZero
  EulerGevreyCorrectionBound EulerGevreyNonlinearEstimate

variable (period : ℝ) [Fact (0 < period)]

/-- The complete actual correction forcing has the metric polynomial bound used in the
shrinking-radius energy argument. -/
theorem correctionForcing_metric {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (KG : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (KG0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M B : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M) (hB : 0 ≤ B)
    (hbase5 : (EulerH6Pressure.CoefficientJet.restrict KG 5 (by omega)).pressureConstant c ≤ M)
    (hbase6 : (EulerH6Pressure.CoefficientJet.restrict KG 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period KG 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (hG : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period KG r ≤ B)
    (hG0 : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period KG0 r ≤ B)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : SmoothCoefficient period) (K0 : EulerSpatialSobolevInverse.CoefficientJet period
        standardDirection s C0)
    (C : Fin 3 → SmoothCoefficient period)
    (K : ∀ i, EulerSpatialSobolevInverse.CoefficientJet period standardDirection s (C i))
    (z e : SobolevSpace period (s + 1)) (r : SobolevSpace period s)
    (B0 B1 A0 A2 R : ℝ) (hA2 : 0 ≤ A2)
    (hz : weightedNorm period 6 N ρ z ≤ B0)
    (hdz : (∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator period s i z)) ≤ B1)
    (hC0 : weightedCoefficient period K0 6 N ρ ≤ A0)
    (hC : (∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ) ≤ A2)
    (hr : weightedNorm period 6 N ρ r ≤ R)
    (KM : LiftL2 period →L[ℝ] LiftL2 period) (cM : ℝ) (hcM : 0 < cM)
    (hKM : ∀ v, cM ^ 2 * ‖v‖ ^ 2 ≤ ⟪KM v, v⟫_ℝ) :
    let f := orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
      (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val)
      (correctionForcing period hs KG KG0 N hN L hL (z+e) e f
        (pressureSobolevOperator period KG κ m c hc hpos f) (transportPressure period hs KG κ m c
            hc hpos L hL (z+e) e)) ≤
      sourceConstant B M*R +
      ((sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period
          3*B0)+transportConstant period B M*B0) *
        metricAmplification cM)*energyNorm period N (by omega : N+6 ≤ s+1) ρ KM e +
      ((sourceConstant B M*A2*productConstant period 3+transportConstant period B
          M)*(metricAmplification cM)^2) *
        (energyNorm period N (by omega : N+6 ≤ s+1) ρ KM e)^2 +
      ((lossConstant period M*(ρ⁻¹+Rc))*(metricAmplification cM)^2) *
        (B0+energyNorm period N (by omega : N+6 ≤ s+1) ρ KM e) *
        energyLoss period N (by omega : N+6 ≤ s+1) ρ KM e := by
  let f := orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
    (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)
  have h := correctionForcing_polynomial period hs KG KG0 κ m c hc hpos N hN ρ Rc M B hρ hRc hM hB
    hbase5 hbase6 hsmall hcoeff hG hG0 L hL C0 K0 C K z e r B0 B1 A0 A2 R hA2 hz hdz hC0 hC hr
  have hM0 : 0 ≤ M := by linarith
  have hP := productConstant_nonneg period 3
  have hb0 : 0 ≤ B0 := (weightedNorm_nonneg period 6 N ρ hρ z).trans hz
  have hb1 : 0 ≤ B1 := (Finset.sum_nonneg (fun i _ =>
    weightedNorm_nonneg period 6 N ρ hρ (derivativeOperator period s i z))).trans hdz
  have ha0 : 0 ≤ A0 := (weightedCoefficient_nonneg period K0 6 N ρ hρ).trans hC0
  have hsf := sourceConstant_nonneg hB hM0
  have htf := transportConstant_nonneg period hB hM0
  have hlf := lossConstant_nonneg period hM0
  have hlin : 0 ≤ sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period
      3*B0) +
      transportConstant period B M*B0 := by positivity
  have hquad : 0 ≤ sourceConstant B M*A2*productConstant period 3+transportConstant period B M := by
      positivity
  exact metric_polynomial_conversion (sourceConstant B M)
    (sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period
        3*B0)+transportConstant period B M*B0)
    (sourceConstant B M*A2*productConstant period 3+transportConstant period B M)
    (lossConstant period M*(ρ⁻¹+Rc)) R B0 (metricAmplification cM)
    (weightedNorm period 6 N ρ e) (weightedLoss period 6 N ρ e)
    (energyNorm period N (by
        omega : N+6 ≤ s+1) ρ KM e) (energyLoss period N (by omega : N+6 ≤ s+1) ρ KM e) _
    hlin hquad (mul_nonneg hlf (add_nonneg (inv_nonneg.mpr hρ.le) hRc)) hb0
        (metricAmplification_one_le hcM)
    (weightedNorm_nonneg period 6 N ρ hρ e) (weightedLoss_nonneg period 6 N ρ hρ e)
    (energyNorm_nonneg period N (by omega : N+6 ≤ s+1) ρ hρ KM e)
    (weightedNorm_le_energy period N (by omega : N+6 ≤ s+1) ρ hρ KM e cM hcM hKM)
    (weightedLoss_le_energy period N (by omega : N+6 ≤ s+1) ρ hρ KM e cM hcM hKM) h

end EulerGevreyMetricEstimate

end
end

end

@[expose] public section

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
  sourceConstant B M*residual +
    ((sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period
        3*B0)+transportConstant period B M*B0) *
      metricAmplification cM)*X +
    ((sourceConstant B M*A2*productConstant period 3+transportConstant period B
        M)*(metricAmplification cM)^2)*X^2 +
    ((lossConstant period M*(ρ⁻¹+Rc))*(metricAmplification cM)^2)*(B0+X)*Y

/-- The literal spatial correction array has the actual metric polynomial bound for every valid
higher representative. -/
theorem correctionArray_bound {q : ℕ} (hq : 6 ≤ q + 1) {T : ℝ}
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (K6 : ∀ t, CoefficientJet period standardDirection 6 (D.metric.coefficient t))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (τ : Icc (0 : ℝ) T)
    (ρ Rc M B : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M) (hB : 0 ≤ B)
    (hbase5 : (EulerH6Pressure.CoefficientJet.restrict (D.metric.jet τ) 5 (by
        omega)).pressureConstant D.coercivity ≤ M)
    (hbase6 : (EulerH6Pressure.CoefficientJet.restrict (D.metric.jet τ) 6 hq).pressureConstant
        D.coercivity ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period (D.metric.jet τ) 6 l ≤ Rc ^
        l * (l.factorial
        : ℝ) ^ 2)
    (hG : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period (D.metric.jet τ) r ≤ B)
    (hG0 : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period (K6 τ) r ≤ B)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (V : SobolevSpace period ((q + 1) + 1))
    (hV : truncateOperator period (q + 1) V = e τ)
    (B0 B1 A0 A2 residual : ℝ) (hA2 : 0 ≤ A2)
    (hz : weightedNorm period 6 N ρ (D.approximation τ) ≤ B0)
    (hdz : (∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator period (q + 1) i
        (D.approximation τ))) ≤ B1)
    (hC0 : weightedCoefficient period (D.linear.jet τ) 6 N ρ ≤ A0)
    (hC : (∑ i : Fin 3, weightedCoefficient period ((D.quadratic i).jet τ) 6 N ρ) ≤ A2)
    (hr : weightedNorm period 6 N ρ (D.residual τ) ≤ residual)
    (KM : LiftL2 period →L[ℝ] LiftL2 period) (cM : ℝ) (hcM : 0 < cM)
    (hKM : ∀ v, cM ^ 2 * ‖v‖ ^ 2 ≤ ⟪KM v, v⟫_ℝ) :
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

/-- The literal polynomial majorant is continuous along the positive radius and actual continuous
metric energies. -/
def forcingBoundPath {q : ℕ} (N : ℕ) (hN : N + 6 ≤ q + 1) (T : ℝ)
    (R : C(Icc (0 : ℝ) T, ℝ)) (hR : ∀ t, 0 < R t)
    (K : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (B M B0 B1 A0 A2 residual cM Rc : ℝ) : C(Icc (0 : ℝ) T, ℝ) := by
  let X := energyPath period N hN T R K e
  let Y := lossPath period N hN T R K e
  refine ⟨fun t => forcingPolynomial period B M B0 B1 A0 A2 residual cM Rc (R t) (X t) (Y t), ?_⟩
  have hi : Continuous (fun t => (R t)⁻¹) := R.continuous.inv₀ (fun t => (hR t).ne')
  unfold forcingPolynomial
  fun_prop

/-- The actual constructed full-order Bochner forcing obeys the continuous spatial majorant almost
everywhere. -/
theorem weightedCorrectionForcing_bound {q : ℕ} (hq : 6 ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (hGc : Continuous (fun t => (D.metric.coefficient t).operator))
    (K6 : ∀ t, CoefficientJet period standardDirection 6 (D.metric.coefficient t))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (R : C(Icc (0 : ℝ) T, ℝ)) (hR : ∀ t, 0 < R t)
    (Rc M B : ℝ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M) (hB : 0 ≤ B)
    (hbase5 : ∀ t, (EulerH6Pressure.CoefficientJet.restrict (D.metric.jet t) 5 (by
        omega)).pressureConstant D.coercivity ≤ M)
    (hbase6 : ∀ t, (EulerH6Pressure.CoefficientJet.restrict (D.metric.jet t) 6 hq).pressureConstant
        D.coercivity ≤ M)
    (hsmall : ∀ t, 4 * M * (R t * Rc) ≤ 1)
    (hcoeff : ∀ t l, 1 ≤ l → l ≤ N → coefficientBlock period (D.metric.jet t) 6 l ≤
        Rc ^ l * (l.factorial : ℝ) ^ 2)
    (hG : ∀ t r, r ≤ 6 → EulerJetProductBounds.boundLevel period (D.metric.jet t) r ≤ B)
    (hG0 : ∀ t r, r ≤ 6 → EulerJetProductBounds.boundLevel period (K6 t) r ≤ B)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e)) Filter.atTop
        (𝓝 U))
    (B0 B1 A0 A2 residual : ℝ) (hA2 : 0 ≤ A2)
    (hz : ∀ t, weightedNorm period 6 N (R t) (D.approximation t) ≤ B0)
    (hdz : ∀ t, (∑ i : Fin 4, weightedNorm period 6 N (R t) (derivativeOperator period (q + 1) i
        (D.approximation t))) ≤ B1)
    (hC0 : ∀ t, weightedCoefficient period (D.linear.jet t) 6 N (R t) ≤ A0)
    (hC : ∀ t, (∑ i : Fin 3, weightedCoefficient period ((D.quadratic i).jet t) 6 N (R t)) ≤ A2)
    (hr : ∀ t, weightedNorm period 6 N (R t) (D.residual t) ≤ residual)
    (K : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period)) (cM : ℝ) (hcM : 0 < cM)
    (hKM : ∀ t v, cM ^ 2 * ‖v‖ ^ 2 ≤ ⟪K t v, v⟫_ℝ) :
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerNonlinearEnergyConstants

open EulerCorrectionEnergyBound EulerGevreyCorrectionBound EulerGevreyMetricEstimate
  EulerGevreyGrowthCoefficient EulerH6Nonlinear

variable (period : ℝ) [Fact (0 < period)]

/-- The fixed coefficient of the metric-linear part of the actual nonlinear forcing. -/
def linearCoefficient (B M B0 B1 A0 A2 c : ℝ) : ℝ :=
  (sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period 3*B0) +
    transportConstant period B M*B0)*metricAmplification c

/-- The fixed coefficient of the metric-quadratic part of the actual nonlinear forcing. -/
def quadraticCoefficient (B M A2 c : ℝ) : ℝ :=
  (sourceConstant B M*A2*productConstant period 3+transportConstant period B
      M)*(metricAmplification c)^2

/-- The fixed coefficient of the single derivative-loss factor in the actual nonlinear forcing. -/
def lossCoefficient (M c : ℝ) : ℝ := lossConstant period M*(metricAmplification c)^2

/-- One explicit constant independent of the external cutoff controls all actual scalar energy
coefficients. -/
def energyConstant (g0 g1 k B M B0 B1 A0 A2 c : ℝ) : ℝ :=
  1+g0+g1+k*sourceConstant B M+k*linearCoefficient period B M B0 B1 A0 A2 c +
    k*quadraticCoefficient period B M A2 c+k*lossCoefficient period M c

/-- The three actual nonlinear forcing coefficients are nonnegative under their genuine norm
budgets. -/
theorem coefficients_nonneg (B M B0 B1 A0 A2 c : ℝ)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hA0 : 0 ≤ A0) (hA2 : 0 ≤ A2) (hc : 0 <
        c) :
    0 ≤ linearCoefficient period B M B0 B1 A0 A2 c ∧
      0 ≤ quadraticCoefficient period B M A2 c ∧ 0 ≤ lossCoefficient period M c := by
  have hs := sourceConstant_nonneg hB hM
  have ht := transportConstant_nonneg period hB hM
  have hl := lossConstant_nonneg period hM
  have hp := productConstant_nonneg period 3
  have hm : 0 ≤ metricAmplification c := (by
      norm_num : (0 : ℝ) ≤ 1).trans (metricAmplification_one_le hc)
  unfold linearCoefficient quadraticCoefficient lossCoefficient
  constructor
  · positivity
  constructor <;> positivity

/-- The actual combined energy constant is strictly positive. -/
theorem energyConstant_pos (g0 g1 k B M B0 B1 A0 A2 c : ℝ)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hk : 0 ≤ k) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hA0 : 0 ≤ A0) (hA2 : 0 ≤ A2) (hc : 0 < c) :
    0 < energyConstant period g0 g1 k B M B0 B1 A0 A2 c := by
  obtain ⟨hl,hq,hd⟩ := coefficients_nonneg period B M B0 B1 A0 A2 c hB hM hB0 hB1 hA0 hA2 hc
  have hs := sourceConstant_nonneg hB hM
  unfold energyConstant
  positivity

/-- The actual polynomial energy right-hand side has precisely the source's shrinking-radius form
with the explicit constant. -/
theorem actual_scalar_bound (g0 g1 k B M B0 B1 A0 A2 c Rc ρ residual X Y b : ℝ)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hk : 0 ≤ k) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hA0 : 0 ≤ A0) (hA2 : 0 ≤ A2) (hc : 0 < c)
    (hRc : 0 ≤ Rc) (hρ : 0 < ρ) (hr : 0 ≤ residual) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    let C := energyConstant period g0 g1 k B M B0 B1 A0 A2 c
    (g0+g1*X)*X+b*Y+k*forcingPolynomial period B M B0 B1 A0 A2 residual c Rc ρ X Y ≤
      C*(X+X^2+residual)+(b+C*(ρ⁻¹+Rc)*(B0+X))*Y := by
  obtain ⟨hl,hq,hd⟩ := coefficients_nonneg period B M B0 B1 A0 A2 c hB hM hB0 hB1 hA0 hA2 hc
  have hs := sourceConstant_nonneg hB hM
  have h := absorb_scalar_coefficients g0 g1 (k*sourceConstant B M)
    (k*linearCoefficient period B M B0 B1 A0 A2 c) (k*quadraticCoefficient period B M A2 c)
    (k*lossCoefficient period M c) residual X Y B0 (ρ⁻¹+Rc)
    (energyConstant period g0 g1 k B M B0 B1 A0 A2 c)
    hg0 hg1 (mul_nonneg hk hs) (mul_nonneg hk hl) (mul_nonneg hk hq) (mul_nonneg hk hd)
    hr hX hY hB0 (add_nonneg (inv_nonneg.mpr hρ.le) hRc) (le_refl _) b
  calc
    _ = (g0+g1*X)*X+b*Y+((k*sourceConstant B M)*residual +
        (k*linearCoefficient period B M B0 B1 A0 A2 c)*X +
        (k*quadraticCoefficient period B M A2 c)*X^2+(k*lossCoefficient period M
            c)*(ρ⁻¹+Rc)*(B0+X)*Y) := by
      unfold forcingPolynomial linearCoefficient quadraticCoefficient lossCoefficient
      ring
    _ ≤ _ := h

end EulerNonlinearEnergyConstants
