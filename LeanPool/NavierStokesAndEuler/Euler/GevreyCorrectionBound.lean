/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyUniformConstants
public import LeanPool.NavierStokesAndEuler.Euler.GevreyRestriction

@[expose] public section

/-! The actual nonlinear correction forcing with explicit constants independent of the derivative
  cutoff. -/

noncomputable section

namespace EulerGevreyCorrectionBound

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerSobolevGevreyOperators
    EulerGevreyCorrectionForcing
  EulerBasePressureCommutator EulerBaseTransportL2 EulerH6Nonlinear EulerSobolevTransportCommutator
  EulerGevreyPressureTransport EulerSobolevCoefficientPressure EulerGevreyUniformConstants
  EulerGevreyMetricComparison EulerWeightedCylinderEnergy EulerGevreyRestriction
    EulerGevreyOrderZero

variable (period : ℝ) [Fact (0 < period)]

/-- The coefficient multiplying the actual order-zero forcing. -/
def sourceConstant (B M : ℝ) : ℝ := 1+2*M*(3136*B+1)

/-- The coefficient for actual base transport and the lower-order nonlinear pressure commutator. -/
def transportConstant (B M : ℝ) : ℝ :=
  5461*baseTransportConstant period + 2688*B*(8*M*(5460*lowerProductConstant period 3))

/-- The coefficient for the actual external radius loss. -/
def lossConstant (M : ℝ) : ℝ := (4+32*M)*productConstant period 3

omit [Fact (0 < period)] in
theorem sourceConstant_nonneg {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M) : 0 ≤ sourceConstant B M := by
  unfold sourceConstant
  positivity

theorem transportConstant_nonneg {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M) : 0 ≤ transportConstant period
  B M := by
  unfold transportConstant
  exact add_nonneg (mul_nonneg (by norm_num) (baseTransportConstant_nonneg period))
    (mul_nonneg (mul_nonneg (by norm_num) hB)
      (mul_nonneg (mul_nonneg (by norm_num) hM) (mul_nonneg (by norm_num)
        (lowerProductConstant_nonneg period 3))))

theorem lossConstant_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ lossConstant period M :=
  mul_nonneg (by linarith) (productConstant_nonneg period 3)

/-- The actual full forcing is bounded with constants depending only on fixed base coefficient bounds and the fixed inverse majorant. -/
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
        lossConstant period M*(ρ⁻¹+Rc)*weightedNorm period 6 N ρ u*weightedLoss period 6 N ρ v := by
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
  have hlf : (4*productConstant period 3)*ρ⁻¹+32*Rc*M*productConstant period 3 ≤ lossConstant
    period M*(ρ⁻¹+Rc) := by
    have h1 := mul_nonneg (productConstant_nonneg period 3) hRc
    have h2 := mul_nonneg (mul_nonneg hM0 (productConstant_nonneg period 3)) (inv_nonneg.mpr hρ.le)
    unfold lossConstant
    nlinarith only [h1,h2]
  have h := correctionForcing_bound period hs K K0 κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase5
    hbase6 hsmall hcoeff L hL u v f
  exact h.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right hsf (weightedNorm_nonneg period 6 N ρ hρ f))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htf (weightedNorm_nonneg period 6 N ρ
      hρ u))
      (weightedNorm_nonneg period 6 N ρ hρ v)))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlf (weightedNorm_nonneg period 6 N ρ
      hρ u))
      (weightedLoss_nonneg period 6 N ρ hρ v)))

end EulerGevreyCorrectionBound
