/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.DriftNonlinearEstimate
public import LeanPool.NavierStokesAndEuler.Euler.DriftEnergyConstants

@[expose] public section

/-! The actual correction forcing in metric energy with distinct full-background and small-drift
  budgets. -/

noncomputable section

namespace EulerDriftMetricForcing

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerSobolevGevreyOperators
    EulerGevreyCorrectionForcing
  EulerH6Nonlinear EulerSobolevTransportCommutator EulerGevreyPressureTransport
    EulerSobolevCoefficientPressure
  EulerGevreyMetricComparison EulerWeightedCylinderEnergy EulerGevreyRestriction
    EulerGevreyOrderZero
  EulerGevreyCorrectionBound EulerGevreyMetricEstimate EulerSobolevDriftNorm EulerFunctionalVelocity

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine seven-term correction forcing obeys the metric polynomial retaining the small drift envelope. -/
theorem correctionForcing_metric {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (KG : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (KG0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ)
    (N : ℕ) (hN : N+6 ≤ s) (ρ Rc M B : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M) (hB : 0 ≤ B)
    (hbase5 : (EulerH6Pressure.CoefficientJet.restrict KG 5 (by omega)).pressureConstant c ≤ M)
    (hbase6 : (EulerH6Pressure.CoefficientJet.restrict KG 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4*M*(ρ*Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period KG 6 l ≤ Rc^l*(l.factorial : ℝ)^2)
    (hG : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period KG r ≤ B)
    (hG0 : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period KG0 r ≤ B)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : SmoothCoefficient period) (K0 : EulerSpatialSobolevInverse.CoefficientJet period
      standardDirection s C0)
    (C : Fin 3 → SmoothCoefficient period)
    (K : ∀ i, EulerSpatialSobolevInverse.CoefficientJet period standardDirection s (C i))
    (z e : SobolevSpace period (s+1)) (r : SobolevSpace period s)
    (Z0 B0 B1 A0 A2 R : ℝ) (hA2 : 0 ≤ A2)
    (hz : weightedNorm period 6 N ρ z ≤ Z0)
    (hb : weightedDriftNorm period 6 N ρ (velocityMap L) z ≤ B0)
    (hdz : (∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator period s i z)) ≤ B1)
    (hC0 : weightedCoefficient period K0 6 N ρ ≤ A0)
    (hC : (∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ) ≤ A2)
    (hr : weightedNorm period 6 N ρ r ≤ R)
    (KM : LiftL2 period →L[ℝ] LiftL2 period) (cM : ℝ) (hcM : 0 < cM)
    (hKM : ∀ v, cM^2*‖v‖^2 ≤ ⟪KM v,v⟫_ℝ) :
    let f := orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
      (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val)
      (correctionForcing period hs KG KG0 N hN L hL (z+e) e f
        (pressureSobolevOperator period KG κ m c hc hpos f) (transportPressure period hs KG κ m c
          hc hpos L hL (z+e) e)) ≤
      EulerDriftEnergyConstants.forcingPolynomial period B M Z0 B0 B1 A0 A2 R cM Rc ρ
        (energyNorm period N (by omega : N+6 ≤ s+1) ρ KM e)
        (energyLoss period N (by omega : N+6 ≤ s+1) ρ KM e) := by
  let f := orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
    (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)
  have h := EulerDriftNonlinearEstimate.correctionForcing_polynomial period hs KG KG0 κ m c hc hpos
    N hN ρ Rc M B hρ hRc hM hB
    hbase5 hbase6 hsmall hcoeff hG hG0 L hL C0 K0 C K z e r Z0 B0 B1 A0 A2 R hA2 hz hb hdz hC0 hC hr
  have hM0 : 0 ≤ M := by linarith
  have hP := productConstant_nonneg period 3
  have hz0 : 0 ≤ Z0 := (weightedNorm_nonneg period 6 N ρ hρ z).trans hz
  have hb0 : 0 ≤ B0 := (weightedDriftNorm_nonneg period 6 N ρ hρ (velocityMap L) z).trans hb
  have hb1 : 0 ≤ B1 := (Finset.sum_nonneg (fun i _ =>
    weightedNorm_nonneg period 6 N ρ hρ (derivativeOperator period s i z))).trans hdz
  have ha0 : 0 ≤ A0 := (weightedCoefficient_nonneg period K0 6 N ρ hρ).trans hC0
  have hsf := sourceConstant_nonneg hB hM0
  have htf := transportConstant_nonneg period hB hM0
  have hlf := lossConstant_nonneg period hM0
  have hlin : 0 ≤ sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period
    3*Z0)+
      transportConstant period B M*Z0 := by positivity
  have hquad : 0 ≤ sourceConstant B M*A2*productConstant period 3+transportConstant period B M :=
    by positivity
  have hconv := metric_polynomial_conversion (sourceConstant B M)
    (sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period
      3*Z0)+transportConstant period B M*Z0)
    (sourceConstant B M*A2*productConstant period 3+transportConstant period B M)
    (lossConstant period M*(ρ⁻¹+Rc)) R B0 (metricAmplification cM)
    (weightedNorm period 6 N ρ e) (weightedLoss period 6 N ρ e)
    (energyNorm period N (by omega : N+6 ≤ s+1) ρ KM e) (energyLoss period N (by omega : N+6 ≤ s+1)
      ρ KM e) _
    hlin hquad (mul_nonneg hlf (add_nonneg (inv_nonneg.mpr hρ.le) hRc)) hb0
      (metricAmplification_one_le hcM)
    (weightedNorm_nonneg period 6 N ρ hρ e) (weightedLoss_nonneg period 6 N ρ hρ e)
    (energyNorm_nonneg period N (by omega : N+6 ≤ s+1) ρ hρ KM e)
    (weightedNorm_le_energy period N (by omega : N+6 ≤ s+1) ρ hρ KM e cM hcM hKM)
    (weightedLoss_le_energy period N (by omega : N+6 ≤ s+1) ρ hρ KM e cM hcM hKM) h

  simpa only [EulerDriftEnergyConstants.forcingPolynomial,
    EulerNonlinearEnergyConstants.linearCoefficient,
      EulerNonlinearEnergyConstants.quadraticCoefficient,
    EulerNonlinearEnergyConstants.lossCoefficient, mul_assoc, mul_left_comm, mul_comm] using hconv

end EulerDriftMetricForcing
