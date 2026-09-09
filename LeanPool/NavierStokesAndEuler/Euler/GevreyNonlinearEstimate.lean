/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionBound

@[expose] public section

/-! The scalar polynomial majorant derived from the actual nonlinear Euler correction forcing. -/

noncomputable section

namespace EulerGevreyNonlinearEstimate

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerSobolevGevreyOperators
    EulerGevreyCorrectionForcing
  EulerH6Nonlinear EulerSobolevTransportCommutator EulerGevreyPressureTransport
    EulerSobolevCoefficientPressure
  EulerGevreyMetricComparison EulerWeightedCylinderEnergy EulerGevreyRestriction
    EulerGevreyOrderZero
  EulerGevreyCorrectionBound

variable (period : ℝ) [Fact (0 < period)]

/-- Uniform bounds on the actual background and coefficient paths give the source's residual-linear-quadratic majorant. -/
theorem orderZeroSource_uniform {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N+6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : SmoothCoefficient period) (K0 : EulerSpatialSobolevInverse.CoefficientJet period
      standardDirection s C0)
    (C : Fin 3 → SmoothCoefficient period)
    (K : ∀ i, EulerSpatialSobolevInverse.CoefficientJet period standardDirection s (C i))
    (z e : SobolevSpace period (s+1)) (r : SobolevSpace period s)
    (B0 B1 A0 A2 R : ℝ) (hA2 : 0 ≤ A2)
    (hB0 : weightedNorm period 6 N ρ z ≤ B0)
    (hB1 : (∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator period s i z)) ≤ B1)
    (hA0 : weightedCoefficient period K0 6 N ρ ≤ A0)
    (hA : (∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ) ≤ A2)
    (hR : weightedNorm period 6 N ρ r ≤ R) :
    weightedNorm period 6 N ρ (orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
      (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)) ≤
      R+(productConstant period 3*B1+A0+2*A2*productConstant period 3*B0)*weightedNorm period 6 N ρ
        e+
        A2*productConstant period 3*(weightedNorm period 6 N ρ e)^2 := by
  have h := orderZeroSource_bound period hs N hN ρ hρ L hL C0 K0 C K z r (truncateOperator period s
    e)
  simp only [weightedNorm_truncate period 6 N hN ρ] at h
  have hP := productConstant_nonneg period 3
  have hE := weightedNorm_nonneg period 6 N ρ hρ e
  have hZ := weightedNorm_nonneg period 6 N ρ hρ z
  have hquad := mul_le_mul_of_nonneg_right hA hP
  have hcross := mul_le_mul hquad hB0 hZ (mul_nonneg hA2 hP)
  have hlin := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hB1 hP) hA0)
    (mul_le_mul_of_nonneg_left hcross (by norm_num : (0 : ℝ) ≤ 2))
  have hlin' : productConstant period 3*(∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator
    period s i z))+
      weightedCoefficient period K0 6 N ρ+
      2*(∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ)*productConstant period 3*weightedNorm
        period 6 N ρ z ≤
      productConstant period 3*B1+A0+2*A2*productConstant period 3*B0 := by
    nlinarith only [hlin]
  exact h.trans (add_le_add (add_le_add hR (mul_le_mul_of_nonneg_right hlin' hE))
    (mul_le_mul_of_nonneg_right hquad (sq_nonneg _)))

/-- The exact scalar assembly of the three already proved nonlinear forcing estimates. -/
theorem polynomial_assembly (S T D B P B1 A0 A2 R E Y V F H : ℝ)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hD : 0 ≤ D) (hE : 0 ≤ E) (hY : 0 ≤ Y)
    (hV : V ≤ B+E) (hF : F ≤ R+(P*B1+A0+2*A2*P*B)*E+A2*P*E^2)
    (hH : H ≤ S*F+T*V*E+D*V*Y) :
    H ≤ S*R+(S*(P*B1+A0+2*A2*P*B)+T*B)*E+(S*A2*P+T)*E^2+D*(B+E)*Y := by
  have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hF hS)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV hT) hE))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV hD) hY)
  exact hH.trans (h.trans_eq (by ring))

/-- All literal forcing terms of the Euler correction have the source's scalar nonlinear majorant.
Every norm and pressure in the left side is the actual constructed Sobolev object. -/
theorem correctionForcing_polynomial {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
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
    (B0 B1 A0 A2 R : ℝ) (hA2 : 0 ≤ A2)
    (hz : weightedNorm period 6 N ρ z ≤ B0)
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
      sourceConstant B M*R+
      (sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period
        3*B0)+transportConstant period B M*B0)*
        weightedNorm period 6 N ρ e+
      (sourceConstant B M*A2*productConstant period 3+transportConstant period B M)*(weightedNorm
        period 6 N ρ e)^2+
      lossConstant period M*(ρ⁻¹+Rc)*(B0+weightedNorm period 6 N ρ e)*weightedLoss period 6 N ρ e
        := by
  let f := orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
    (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)
  have hf := orderZeroSource_uniform period hs N hN ρ hρ L hL C0 K0 C K z e r B0 B1 A0 A2 R hA2 hz
    hdz hC0 hC hr
  have hv := (weightedNorm_add_le period 6 N (by omega : N+6 ≤ s+1) ρ hρ z e).trans
    (add_le_add hz (le_refl (weightedNorm period 6 N ρ e)))
  have h := correctionForcing_uniform_bound period hs KG KG0 κ m c hc hpos N hN ρ Rc M B hρ hRc hM
    hbase5 hbase6 hsmall hcoeff hG hG0 L hL (z+e) e f
  exact polynomial_assembly (sourceConstant B M) (transportConstant period B M)
    (lossConstant period M*(ρ⁻¹+Rc)) B0 (productConstant period 3) B1 A0 A2 R
    (weightedNorm period 6 N ρ e) (weightedLoss period 6 N ρ e) (weightedNorm period 6 N ρ (z+e))
    (weightedNorm period 6 N ρ f) _
    (sourceConstant_nonneg hB (by linarith)) (transportConstant_nonneg period hB (by linarith))
    (mul_nonneg (lossConstant_nonneg period (by linarith)) (add_nonneg (inv_nonneg.mpr hρ.le) hRc))
    (weightedNorm_nonneg period 6 N ρ hρ e) (weightedLoss_nonneg period 6 N ρ hρ e) hv hf h

end EulerGevreyNonlinearEstimate
