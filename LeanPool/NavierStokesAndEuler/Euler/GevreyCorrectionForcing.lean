/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyForcingComponents
public import LeanPool.NavierStokesAndEuler.Euler.GevreyBaseTransport
import LeanPool.NavierStokesAndEuler.Euler.GevreyPressureComplete
import LeanPool.NavierStokesAndEuler.Euler.WeightedForcingAlgebra

/-! The actual differentiated correction forcing and its cutoff-independent nonlinear bound. -/

@[expose] public section


noncomputable section

namespace EulerGevreyCorrectionForcing

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerPacketWeights EulerSobolevGevreyOperators
  EulerBaseWordMetric EulerFiniteMetricEnergy EulerWeightedCylinderEnergy
      EulerGevreyMetricComparison
  EulerSobolevWordLevel EulerSobolevTransportCommutator EulerGevreyPressureEnergy
      EulerBasePressureCommutator
  EulerGevreyBaseTransport EulerGevreyForcingComponents EulerWeightedForcingAlgebra
  EulerGevreyPressureTransport EulerSobolevCoefficientPressure EulerH6Nonlinear EulerBaseTransportL2

variable (period : ℝ) [Fact (0 < period)]

/-- The seven literal commutator/source terms after external and base differentiation of equation
(17).
The two pressure arguments are the positive projected inverses; the PDE pressure has the opposite
sign. -/
def correctionForcing {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) (f p0 p1 : SobolevSpace period s) : ExternalWord N →
        BaseWord
        6 → LiftL2 period :=
  -energyValues period 6 N hN f + -externalTransportForcing period hs N hN L hL u v +
    -baseTransportForcing period N hN L hL u v + externalPressureForcing period K N hN p0 +
    basePressureForcing period K0 N hN p0 + externalPressureForcing period K N hN p1 +
    basePressureForcing period K0 N hN p1

/-- The triangle inequality for seven actual forcing arrays has coefficient one. -/
theorem forcing_seven_le {α β H : Type*} [Fintype α] [Fintype β] [NormedAddCommGroup H]
    (ρ : ℝ) (hρ : 0 < ρ) (order : α → ℕ) (a b c d e f g : α → β → H) :
    weightedForcingSum ρ order (a+b+c+d+e+f+g) ≤ weightedForcingSum ρ order a + weightedForcingSum
        ρ order b +
      weightedForcingSum ρ order c + weightedForcingSum ρ order d + weightedForcingSum ρ order e +
      weightedForcingSum ρ order f + weightedForcingSum ρ order g := by
  have h1 := weightedForcingSum_add_le ρ hρ order a b
  have h2 := weightedForcingSum_add_le ρ hρ order (a+b) c
  have h3 := weightedForcingSum_add_le ρ hρ order (a+b+c) d
  have h4 := weightedForcingSum_add_le ρ hρ order (a+b+c+d) e
  have h5 := weightedForcingSum_add_le ρ hρ order (a+b+c+d+e) f
  have h6 := weightedForcingSum_add_le ρ hρ order (a+b+c+d+e+f) g
  linarith

/-- All actual forcing components satisfy their derived bounds on finite Sobolev fields. -/
theorem correctionForcing_raw_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) (f p0 p1 : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (correctionForcing period hs K K0 N hN
        L hL u v f p0 p1) ≤
      weightedNorm period 6 N ρ f + (4*productConstant period 3)*ρ⁻¹*weightedNorm period 6 N ρ
          u*weightedLoss period 6 N ρ v +
      (5461*baseTransportConstant period)*weightedNorm period 6 N ρ u*weightedNorm period 6 N ρ v +
      externalPressureNorm period K N ρ p0 + basePressureNorm period K0 N hN ρ p0 +
      externalPressureNorm period K N ρ p1 + basePressureNorm period K0 N hN ρ p1 := by
  have h := forcing_seven_le ρ hρ (fun I : ExternalWord N => I.1.val)
    (-energyValues period 6 N hN f) (-externalTransportForcing period hs N hN L hL u v)
    (-baseTransportForcing period N hN L hL u v) (externalPressureForcing period K N hN p0)
    (basePressureForcing period K0 N hN p0) (externalPressureForcing period K N hN p1)
    (basePressureForcing period K0 N hN p1)
  simp only [weightedForcingSum_neg] at h
  have hS := sourceForcing_weighted_bound period N hN ρ hρ f
  have hE := (externalTransportForcing_bound period hs N hN ρ hρ L hL u v).trans
    (weightedCommutator_bound period hs N hN ρ hρ L hL u v)
  have hB := baseTransportForcing_weighted_bound period N hN ρ hρ L hL u v
  have hP0 := externalPressureForcing_bound period K N hN ρ hρ p0
  have hQ0 := basePressureForcing_bound period K0 N hN ρ hρ p0
  have hP1 := externalPressureForcing_bound period K N hN ρ hρ p1
  have hQ1 := basePressureForcing_bound period K0 N hN ρ hρ p1
  exact h.trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hS hE) hB)
      hP0) hQ0) hP1) hQ1)

/-- The full actual forcing with both genuine projected pressure solves obeys the spatial part of
equation (19).
Every velocity derivative in the bound lies at or below the chosen cutoff. -/
theorem correctionForcing_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase5 : (EulerH6Pressure.CoefficientJet.restrict K 5 (by omega)).pressureConstant c ≤ M)
    (hbase6 : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) (f : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val)
      (correctionForcing period hs K K0 N hN L hL u v f
        (pressureSobolevOperator period K κ m c hc hpos f) (transportPressure period hs K κ m c hc
            hpos L hL u v)) ≤
      (1+2*M*(weightedCoefficient period K 6 N ρ + 448*baseCoefficientSum period K0))*weightedNorm
          period 6 N ρ f +
      (5461*baseTransportConstant period + (448*baseCoefficientSum period
          K0)*(8*M*(5460*lowerProductConstant period 3))) *
        weightedNorm period 6 N ρ u*weightedNorm period 6 N ρ v +
      ((4*productConstant period 3)*ρ⁻¹ + 32*Rc*M*productConstant period 3) *
        weightedNorm period 6 N ρ u*weightedLoss period 6 N ρ v := by
  let p0 := pressureSobolevOperator period K κ m c hc hpos f
  let p1 := transportPressure period hs K κ m c hc hpos L hL u v
  have h := correctionForcing_raw_bound period hs K K0 N hN ρ hρ L hL u v f p0 p1
  have hp0 := source_pressure_commutators period K K0 κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase6
      hsmall hcoeff f
  have hp1e := nonlinear_externalPressure_bound_all period hs K κ m c hc hpos N hN ρ Rc M hρ hRc hM
      hbase6 hsmall hcoeff L hL u v
  have hp1b := nonlinear_basePressure_bound period hs K K0 κ m c hc hpos N hN ρ Rc M hρ hRc hM
      hbase5 hsmall hcoeff L hL u v
  change externalPressureNorm period K N ρ p0 + basePressureNorm period K0 N hN ρ p0 ≤ _ at hp0
  change externalPressureNorm period K N ρ p1 ≤ _ at hp1e
  change basePressureNorm period K0 N hN ρ p1 ≤ _ at hp1b
  nlinarith only [h, hp0, hp1e, hp1b]

end EulerGevreyCorrectionForcing
