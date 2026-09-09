/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevDriftTransport
public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionBound

@[expose] public section

/-! Actual nonlinear correction forcing with distinct full-velocity and drift factors. -/

noncomputable section

namespace EulerDriftCorrectionForcing

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerPacketWeights EulerSobolevGevreyOperators
  EulerBaseWordMetric EulerFiniteMetricEnergy EulerWeightedCylinderEnergy
    EulerGevreyMetricComparison
  EulerSobolevWordLevel EulerSobolevTransportCommutator EulerGevreyPressureEnergy
    EulerBasePressureCommutator
  EulerGevreyBaseTransport EulerGevreyForcingComponents EulerWeightedForcingAlgebra
  EulerGevreyPressureTransport EulerSobolevCoefficientPressure EulerH6Nonlinear EulerBaseTransportL2
  EulerGevreyCorrectionForcing EulerGevreyCorrectionBound EulerGevreyUniformConstants
  EulerSobolevDriftNorm EulerSobolevDriftTransport EulerFunctionalVelocity

variable (period : ℝ) [Fact (0 < period)]

/-- The nonlinear external pressure commutator keeps the actual drift norm at positive cutoff. -/
theorem nonlinear_externalPressure_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ)
    (N : ℕ) (hN : (N+1)+6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4*M*(ρ*Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N+1 → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) :
    externalPressureNorm period K (N+1) ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (8*Rc*M*productConstant period 3)*weightedDriftNorm period 6 (N+1) ρ (velocityMap L)
        u*weightedLoss period 6 (N+1) ρ v := by
  have hhalf : ρ*Rc ≤ 1/2 := by nlinarith [mul_nonneg hρ.le hRc]
  have hcN : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2 :=
    fun l hl hn => hcoeff l hl (by omega)
  have hp := transportPressure_shifted_drift period hs K κ m c hc hpos N (by omega) ρ Rc M hρ hRc
    hM hbase hsmall hcN L hL u v
  exact (externalPressureNorm_shifted period K N hN ρ Rc hρ hRc hhalf hcoeff _).trans
    ((mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hRc)).trans_eq (by ring))

/-- The sharp external pressure bound also includes zero cutoff. -/
theorem nonlinear_externalPressure_bound_all {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ)
    (N : ℕ) (hN : N+6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4*M*(ρ*Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) :
    externalPressureNorm period K N ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (8*Rc*M*productConstant period 3)*weightedDriftNorm period 6 N ρ (velocityMap L)
        u*weightedLoss period 6 N ρ v := by
  cases N with
  | zero => simp [externalPressureNorm, weightedLoss, commutatorBlock_zero]
  | succ N => exact nonlinear_externalPressure_bound period hs K κ m c hc hpos N hN ρ Rc M hρ hRc
    hM hbase hsmall hcoeff L hL u v


/-- Seven actual forcing arrays retain the sharp drift commutator factor. -/
theorem correctionForcing_raw_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (f p0 p1 : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (correctionForcing period hs K K0 N hN
      L hL u v f p0 p1) ≤
      weightedNorm period 6 N ρ f + (productConstant period 3)*ρ⁻¹*weightedDriftNorm period 6 N ρ
        (velocityMap L) u*weightedLoss period 6 N ρ v +
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
    (weightedCommutator_drift_bound period hs N hN ρ hρ L hL u v)
  have hB := baseTransportForcing_weighted_bound period N hN ρ hρ L hL u v
  have hP0 := externalPressureForcing_bound period K N hN ρ hρ p0
  have hQ0 := basePressureForcing_bound period K0 N hN ρ hρ p0
  have hP1 := externalPressureForcing_bound period K N hN ρ hρ p1
  have hQ1 := basePressureForcing_bound period K0 N hN ρ hρ p1
  exact h.trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hS hE) hB)
    hP0) hQ0) hP1) hQ1)

/-- The full actual forcing with both genuine projected pressure solves obeys the spatial part of equation (19).
Every velocity derivative in the bound lies at or below the chosen cutoff. -/
theorem correctionForcing_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ)
    (N : ℕ) (hN : N+6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase5 : (EulerH6Pressure.CoefficientJet.restrict K 5 (by omega)).pressureConstant c ≤ M)
    (hbase6 : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4*M*(ρ*Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (f : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val)
      (correctionForcing period hs K K0 N hN L hL u v f
        (pressureSobolevOperator period K κ m c hc hpos f) (transportPressure period hs K κ m c hc
          hpos L hL u v)) ≤
      (1+2*M*(weightedCoefficient period K 6 N ρ + 448*baseCoefficientSum period K0))*weightedNorm
        period 6 N ρ f +
      (5461*baseTransportConstant period + (448*baseCoefficientSum period
        K0)*(8*M*(5460*lowerProductConstant period 3)))*
        weightedNorm period 6 N ρ u*weightedNorm period 6 N ρ v +
      ((productConstant period 3)*ρ⁻¹ + 8*Rc*M*productConstant period 3)*
        weightedDriftNorm period 6 N ρ (velocityMap L) u*weightedLoss period 6 N ρ v := by
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

/-- Uniform fixed-base constants preserve the separate drift norm. -/
theorem correctionForcing_uniform_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ)
    (N : ℕ) (hN : N+6 ≤ s) (ρ Rc M B : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase5 : (EulerH6Pressure.CoefficientJet.restrict K 5 (by omega)).pressureConstant c ≤ M)
    (hbase6 : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4*M*(ρ*Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2)
    (hB : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period K r ≤ B)
    (hB0 : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period K0 r ≤ B)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (f : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val)
      (correctionForcing period hs K K0 N hN L hL u v f
        (pressureSobolevOperator period K κ m c hc hpos f) (transportPressure period hs K κ m c hc
          hpos L hL u v)) ≤
      sourceConstant B M*weightedNorm period 6 N ρ f +
        transportConstant period B M*weightedNorm period 6 N ρ u*weightedNorm period 6 N ρ v +
        (productConstant period 3*ρ⁻¹+8*Rc*M*productConstant period 3)*weightedDriftNorm period 6 N
          ρ (velocityMap L) u*weightedLoss period 6 N ρ v := by
  have hhalf : ρ*Rc ≤ 1/2 := by nlinarith [mul_nonneg hρ.le hRc]
  have hw := weightedCoefficient_uniform period K N ρ Rc B hρ hRc hhalf hB hcoeff
  have hb := baseCoefficientSum_le period K0 B hB0
  have hM0 : 0 ≤ M := by linarith
  have hsf : 1+2*M*(weightedCoefficient period K 6 N ρ+448*baseCoefficientSum period K0) ≤
    sourceConstant B M := by
    have h := add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_left
      (add_le_add hw (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 448)))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM0))
    exact h.trans_eq (by unfold sourceConstant; ring)
  have htf : 5461*baseTransportConstant period+(448*baseCoefficientSum period
    K0)*(8*M*(5460*lowerProductConstant period 3)) ≤
      transportConstant period B M := by
    have hp : 0 ≤ 8*M*(5460*lowerProductConstant period 3) :=
      mul_nonneg (mul_nonneg (by norm_num) hM0) (mul_nonneg (by norm_num)
        (lowerProductConstant_nonneg period 3))
    have h := add_le_add (le_refl (5461*baseTransportConstant period)) (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 448)) hp)
    exact h.trans_eq (by unfold transportConstant; ring)
  have h := correctionForcing_bound period hs K K0 κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase5
    hbase6 hsmall hcoeff L hL u v f
  exact h.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right hsf (weightedNorm_nonneg period 6 N ρ hρ f))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htf (weightedNorm_nonneg period 6 N ρ
      hρ u))
      (weightedNorm_nonneg period 6 N ρ hρ v)))
    (le_refl _))

end EulerDriftCorrectionForcing
