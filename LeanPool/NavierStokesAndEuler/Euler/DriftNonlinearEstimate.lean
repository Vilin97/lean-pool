/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionBound
public import LeanPool.NavierStokesAndEuler.Euler.GevreyOrderZero
public import LeanPool.NavierStokesAndEuler.Euler.SobolevDriftNorm
import LeanPool.NavierStokesAndEuler.Euler.DriftCorrectionForcing
import LeanPool.NavierStokesAndEuler.Euler.GevreyNonlinearEstimate

/-! Actual nonlinear forcing with separate full-background and drift envelopes. -/

@[expose] public section


noncomputable section

namespace EulerDriftNonlinearEstimate

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerSobolevGevreyOperators
      EulerGevreyCorrectionForcing
  EulerH6Nonlinear EulerSobolevTransportCommutator EulerGevreyPressureTransport
      EulerSobolevCoefficientPressure
  EulerGevreyMetricComparison EulerWeightedCylinderEnergy
      EulerGevreyOrderZero
  EulerGevreyCorrectionBound EulerGevreyNonlinearEstimate EulerSobolevDriftNorm
      EulerFunctionalVelocity

/-- The factor four is spent only on the correction drift, recovering the original uniform loss
constant. -/
theorem drift_loss_absorption (P M Rc ρ B E Y D : ℝ)
    (hP : 0 ≤ P) (hM : 0 ≤ M) (hRc : 0 ≤ Rc) (hρ : 0 < ρ)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hY : 0 ≤ Y) (hD : D ≤ 4 * (B + E)) :
    (P*ρ⁻¹+8*Rc*M*P)*D*Y ≤ ((4+32*M)*P)*(ρ⁻¹+Rc)*(B+E)*Y := by
  have ha : 0 ≤ P*ρ⁻¹+8*Rc*M*P := by positivity
  have hc : 4*(P*ρ⁻¹+8*Rc*M*P) ≤ ((4+32*M)*P)*(ρ⁻¹+Rc) := by
    have h1 := mul_nonneg hP hRc
    have h2 := mul_nonneg (mul_nonneg hM hP) (inv_nonneg.mpr hρ.le)
    nlinarith only [h1,h2]
  calc
    _ ≤ (P*ρ⁻¹+8*Rc*M*P)*(4*(B+E))*Y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD ha) hY
    _ = (4*(P*ρ⁻¹+8*Rc*M*P))*(B+E)*Y := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (add_nonneg hB hE)) hY

/-- Scalar assembly keeps the independent full-velocity and drift envelopes in their respective
terms. -/
theorem polynomial_assembly (S T D Z B P B1 A0 A2 R E Y V F H : ℝ)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hV : V ≤ Z + E) (hF : F ≤ R + (P * B1 + A0 + 2 * A2 * P * Z) * E + A2 * P * E ^ 2)
    (hH : H ≤ S * F + T * V * E + D * (B + E) * Y) :
    H ≤ S*R+(S*(P*B1+A0+2*A2*P*Z)+T*Z)*E+(S*A2*P+T)*E^2+D*(B+E)*Y := by
  have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hF hS)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV hT) hE)) (le_refl (D*(B+E)*Y))
  exact hH.trans (h.trans_eq (by ring))

variable (period : ℝ) [Fact (0 < period)]

/-- The literal seven-term Euler forcing has a scalar bound preserving the actual small background
drift. -/
theorem correctionForcing_polynomial {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
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
    (Z0 B0 B1 A0 A2 R : ℝ) (hA2 : 0 ≤ A2)
    (hz : weightedNorm period 6 N ρ z ≤ Z0)
    (hb : weightedDriftNorm period 6 N ρ (velocityMap L) z ≤ B0)
    (hdz : (∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator period s i z)) ≤ B1)
    (hC0 : weightedCoefficient period K0 6 N ρ ≤ A0)
    (hC : (∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ) ≤ A2)
    (hr : weightedNorm period 6 N ρ r ≤ R) :
    let f := orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
      (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val)
      (correctionForcing period hs KG KG0 N hN L hL (z+e) e f
        (pressureSobolevOperator period KG κ m c hc hpos f) (transportPressure period hs KG κ m c
            hc hpos L hL (z+e) e)) ≤
      sourceConstant B M*R +
      (sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period
          3*Z0)+transportConstant period B M*Z0) *
        weightedNorm period 6 N ρ e +
      (sourceConstant B M*A2*productConstant period 3+transportConstant period B M)*(weightedNorm
          period 6 N ρ e)^2 +
      lossConstant period M*(ρ⁻¹+Rc)*(B0+weightedNorm period 6 N ρ e)*weightedLoss period 6 N ρ e
          := by
  let f := orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
    (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)
  have hf := orderZeroSource_uniform period hs N hN ρ hρ L hL C0 K0 C K z e r Z0 B1 A0 A2 R hA2 hz
      hdz hC0 hC hr
  have hv := (weightedNorm_add_le period 6 N (by omega : N+6 ≤ s+1) ρ hρ z e).trans
    (add_le_add hz (le_refl (weightedNorm period 6 N ρ e)))
  have hB0 : 0 ≤ B0 := (weightedDriftNorm_nonneg period 6 N ρ hρ (velocityMap L) z).trans hb
  have heD := weightedDriftNorm_velocityMap_le period 6 N ρ hρ L hL e
  have hD : weightedDriftNorm period 6 N ρ (velocityMap L) (z+e) ≤
      4*(B0+weightedNorm period 6 N ρ e) := by
    have h := (weightedDriftNorm_add_le period 6 N (by
        omega : N+6 ≤ s+1) ρ hρ (velocityMap L) z e).trans
      (add_le_add hb heD)
    nlinarith only [h,hB0]
  have hraw := EulerDriftCorrectionForcing.correctionForcing_uniform_bound period hs KG KG0 κ m c
      hc hpos
    N hN ρ Rc M B hρ hRc hM hbase5 hbase6 hsmall hcoeff hG hG0 L hL (z+e) e f
  have hloss : (productConstant period 3*ρ⁻¹+8*Rc*M*productConstant period 3) *
      weightedDriftNorm period 6 N ρ (velocityMap L) (z+e)*weightedLoss period 6 N ρ e ≤
      lossConstant period M*(ρ⁻¹+Rc)*(B0+weightedNorm period 6 N ρ e)*weightedLoss period 6 N ρ e
          := by
    simpa only [lossConstant] using drift_loss_absorption (productConstant period 3) M Rc ρ B0
      (weightedNorm period 6 N ρ e) (weightedLoss period 6 N ρ e)
      (weightedDriftNorm period 6 N ρ (velocityMap L) (z+e))
      (productConstant_nonneg period 3) (by linarith) hRc hρ hB0
      (weightedNorm_nonneg period 6 N ρ hρ e) (weightedLoss_nonneg period 6 N ρ hρ e) hD
  have h := hraw.trans (add_le_add (le_refl _) hloss)
  exact polynomial_assembly (sourceConstant B M) (transportConstant period B M)
    (lossConstant period M*(ρ⁻¹+Rc)) Z0 B0 (productConstant period 3) B1 A0 A2 R
    (weightedNorm period 6 N ρ e) (weightedLoss period 6 N ρ e) (weightedNorm period 6 N ρ (z+e))
    (weightedNorm period 6 N ρ f) _
    (sourceConstant_nonneg hB (by linarith)) (transportConstant_nonneg period hB (by linarith))
    (weightedNorm_nonneg period 6 N ρ hρ e) hv hf h

end EulerDriftNonlinearEstimate
