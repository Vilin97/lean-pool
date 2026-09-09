/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiveCostPolynomial

/-! Uniform, explicit frequency guards for the actual packet correction.
A single polynomial source bound suffices simultaneously for all five
requirements. No eventual threshold is hidden in this statement. -/

@[expose] public section


noncomputable section

namespace EulerPacketFiveCost

open EulerPacketCorrectionConstants EulerPacketCorrectionCoefficients
  EulerPacketCorrectionScalar EulerPacketCoarseMajorant EulerPacketCylinderField
  EulerGevreyCorrectionBound EulerH6Nonlinear EulerCylinderSobolevSpace

variable (P : ℝ) [Fact (0 < P)]

theorem growthEnvelope_nonneg (X : ℝ) (hX : 0 ≤ X) : 0 ≤ growthEnvelope P X := by
  have hv := velocity_nonneg X X X hX hX
  have hp := productConstant_nonneg P 3
  have hs := sourceConstant_nonneg hX hX
  have ht := transportConstant_nonneg P hX hX
  have hl := lossConstant_nonneg P hX
  have he := sobolevEmbeddingConstant_nonneg P 6
  unfold growthEnvelope rawGrowth
  dsimp only
  positivity

theorem fiveEnvelope_components (X : ℝ) (hX : 0 ≤ X) :
    tailPolynomialConstant X X X ≤ fiveEnvelope P X ∧
    X ≤ fiveEnvelope P X ∧
    12*growthEnvelope P X*X ≤ fiveEnvelope P X ∧
    8*growthEnvelope P X*X*drift X X X*inverseRadiusEnvelope X ≤ fiveEnvelope P X ∧
    8*growthEnvelope P X*X*inverseRadiusEnvelope X ≤ fiveEnvelope P X := by
  have ht := tailPolynomialConstant_nonneg X X X hX
  have hg := growthEnvelope_nonneg P X hX
  have hd := drift_nonneg X X X hX hX
  have hi : 0 ≤ inverseRadiusEnvelope X := by unfold inverseRadiusEnvelope; positivity
  have h₁ : 0 ≤ 12*growthEnvelope P X*X := by positivity
  have h₂ : 0 ≤ 8*growthEnvelope P X*X*drift X X X*inverseRadiusEnvelope X := by positivity
  have h₃ : 0 ≤ 8*growthEnvelope P X*X*inverseRadiusEnvelope X := by positivity
  unfold fiveEnvelope
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (Kc : CorrectionCoefficientBudget D P)
  (R H C CT X : ℝ) (hX : 1 ≤ X)
  (hR : 0 ≤ R) (hH : 0 ≤ H) (hC : 0 ≤ C)
  (hRX : R ≤ X) (hHX : H ≤ X) (hCX : C ≤ X) (hCTX : CT ≤ X)
  (hi : D.inverseBound ≤ X) (hm : inverseMetricBound D ≤ X)
  (hf : inverseMetricFirstBound D ≤ X) (ht : inverseMetricTimeBound D ≤ X)
  (hB : Kc.B ≤ X) (hM : Kc.M ≤ X) (hA0 : Kc.A0 ≤ X) (hA2 : Kc.A2 ≤ X)
  (hRc : Kc.Rc ≤ X) (hT : D.T ≤ X)

include hX hR hH hC hRX hHX hCX hCTX hi hm hf ht hB hM hA0 hA2 hRc hT

theorem five_costs_bound :
    tailPolynomialConstant R H CT ≤ costConstant P*X^(costPower P) ∧
    C ≤ costConstant P*X^(costPower P) ∧
    12*growth D P Kc R H C*D.T ≤ costConstant P*X^(costPower P) ∧
    8*growth D P Kc R H C*D.T*drift R H C/initialRadius R Kc.M Kc.Rc ≤ costConstant P*X^(costPower
        P) ∧
    8*growth D P Kc R H C*D.T/initialRadius R Kc.M Kc.Rc ≤ costConstant P*X^(costPower P) := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hT0 : 0 ≤ D.T := D.T_pos.le
  have hg := growth_le_envelope P D Kc R H C X hR hH hC hRX hHX hCX hi hm hf ht hB hM hA0 hA2
  have hgp := (growth_pos D P Kc R H C hR hC).le
  have hgX := growthEnvelope_nonneg P X hX0
  have hd := drift_mono hR hH hC hRX hHX hCX
  have hdp := drift_nonneg R H C hR hC
  have hdX := drift_nonneg X X X hX0 hX0
  have hρ := (initialRadius_bounds R Kc.M Kc.Rc hR (zero_le_one.trans Kc.M_one_le) Kc.Rc_nonneg).1
  have hiR : (initialRadius R Kc.M Kc.Rc)⁻¹ ≤ inverseRadiusEnvelope X := by
    simp only [initialRadius,one_div,inv_inv]
    unfold inverseRadiusEnvelope
    have hprod := mul_le_mul hM hRc Kc.Rc_nonneg hX0
    nlinarith
  have hp := fiveEnvelope_power P X hX
  obtain ⟨hc₁,hc₂,hc₃,hc₄,hc₅⟩ := fiveEnvelope_components P X hX0
  refine ⟨?_,hCX.trans (hc₂.trans hp),?_,?_,?_⟩
  · apply le_trans _ (hc₁.trans hp)
    unfold tailPolynomialConstant
    gcongr
  · apply le_trans _ (hc₃.trans hp)
    gcongr
  · apply le_trans _ (hc₄.trans hp)
    rw [div_eq_mul_inv]
    gcongr
  · apply le_trans _ (hc₅.trans hp)
    rw [div_eq_mul_inv]
    gcongr

/-- The literal source frequency assumptions follow from one explicit
polynomial comparison; the threshold does not depend on a chosen parent. -/
theorem frequency_guards (k : ℝ)
    (hbudget : costConstant P * X ^ (costPower P) ≤ EulerPacketSourceFrequency.smallPower k) :
    tailPolynomialConstant R H CT ≤ EulerPacketSourceFrequency.smallPower k ∧
    C ≤ EulerPacketSourceFrequency.smallPower k ∧
    12*growth D P Kc R H C*D.T ≤ EulerPacketSourceFrequency.smallPower k ∧
    8*growth D P Kc R H C*D.T*drift R H C/initialRadius R Kc.M Kc.Rc ≤
        EulerPacketSourceFrequency.smallPower k ∧
    8*growth D P Kc R H C*D.T/initialRadius R Kc.M Kc.Rc ≤ EulerPacketSourceFrequency.smallPower k
        := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := five_costs_bound P D Kc R H C CT X hX hR hH hC
    hRX hHX hCX hCTX hi hm hf ht hB hM hA0 hA2 hRc hT
  exact ⟨h₁.trans hbudget,h₂.trans hbudget,h₃.trans hbudget,h₄.trans hbudget,h₅.trans hbudget⟩

end EulerPacketFiveCost
