/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionPrimitivePolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionMetricBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketParentCoefficientBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketMatrixCoefficientGevrey
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCoefficientGevrey

/-! The polynomial primitive envelope applies to the constructed correction
coefficients, using only the original deformation and inverse-deformation jets. -/

section

/-! Quantitative bounds for the actual inverse metric and its first spatial
and time derivatives, from the prescribed deformation jets. -/

@[expose] public section

noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set EulerSmoothLimit EulerMeanCoefficients EulerPacketCylinderField
  EulerAllOrderCorrectionData EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (R C0 C1 : ℝ) (hR : 0 ≤ R) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
  (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C0 * majorant R
      0
      n)
  (hF1 : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C1 * majorant
      R
      0 n)

include hR hC0 hF in
theorem inverseMetricCoefficient_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (inverseMetricCoefficient D).path) a‖ ≤
      (3*C0*C0)*majorant R 0 n := by
  have hf := frameCoefficient_bound D R C0 hR hC0 hF
  exact MatrixCoefficient.comp_bound (frameCoefficient D).adjoint (frameCoefficient D)
    R C0 C0 hR hC0 hC0 ((frameCoefficient D).adjoint_bound R C0 hf) hf n a

include hR hC0 hF in
theorem inverseMetricFirstBound_le_source : inverseMetricFirstBound D ≤ 3*C0*C0*R := by
  have h := inverseMetricCoefficient_bound D R C0 hR hC0 hF 1 0
  simpa only [inverseMetricFirstBound,majorant,Nat.add_zero,Nat.factorial_one,
    Nat.cast_one,pow_one,one_pow,mul_one] using h

include hC0 hF in
theorem framePath_norm_le_source : ‖D.F.field‖ ≤ C0 := by
  apply (ContinuousMap.norm_le _ hC0).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le hC0).mpr
  intro x
  simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
    Nat.cast_one,pow_zero,one_pow,mul_one] using hF 0 t x

include hC1 hF1 in
theorem frameTimePath_norm_le_source : ‖D.F₁.field‖ ≤ C1 := by
  apply (ContinuousMap.norm_le _ hC1).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le hC1).mpr
  intro x
  simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
    Nat.cast_one,pow_zero,one_pow,mul_one] using hF1 0 t x

include hC0 hF in
theorem inverseMetricBound_le_source : inverseMetricBound D ≤ C0^2 := by
  have h0 := framePath_norm_le_source D R C0 hC0 hF
  exact (inverseMetricBound_le D).trans (pow_le_pow_left₀ (norm_nonneg _) h0 2)

include hC0 hC1 hF hF1 in
theorem inverseMetricTimeBound_le_source : inverseMetricTimeBound D ≤ 2*C0*C1 := by
  have h0 := framePath_norm_le_source D R C0 hC0 hF
  have h1 := frameTimePath_norm_le_source D R C1 hC1 hF1
  exact (inverseMetricTimeBound_le D).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left h0 (by norm_num)) h1 (norm_nonneg _) (by positivity))

include hR hC0 hF in
theorem sourceMetricBudget_first_le_source (P : ℝ) [Fact (0 < P)]
    (κ : ℝ) (hκ : |κ| ≤ 1) (Z G : FieldTower P D.T) (q : ℕ) :
    (sourceMetricBudget D P κ hκ Z G q).first ≤ 3*C0*C0*R :=
  inverseMetricFirstBound_le_source D R C0 hR hC0 hF

end EulerPacketCorrectionCoefficients

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCorrectionPrimitive

open Set EulerParameterWordGevrey EulerCoefficientJetPressureBounds
  EulerPacketCorrectionCoefficients EulerCoefficientPath EulerPacketCylinderField
  EulerSmoothLimit EulerGevrey EulerPacketCofactor EulerCylinderPathProduct
open scoped BoundedContinuousFunction

theorem correction_envelopes (c R C0 C1 CI X : ℝ)
    (hc : 0 < c) (hR : 0 ≤ R) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hCI : 0 ≤ CI)
    (hRX : R ≤ X) (hC0X : C0 ≤ X) (hC1X : C1 ≤ X) (hCIX : CI ≤ X)
    (hci : c⁻¹ ≤ (1 + X) ^ 2) :
    correctionCoefficientRadius R CI ≤ radiusEnvelope X ∧
    correctionPressureEnvelope c R CI ≤ pressureEnvelope X ∧
    correctionMetricEnvelope R CI ≤ metricEnvelope X ∧
    correctionLinearEnvelope R C1 CI ≤ linearEnvelope X ∧
    correctionQuadraticEnvelope R C0 CI ≤ quadraticEnvelope X := by
  have hX : 0 ≤ X := hR.trans hRX
  have hm : correctionMetricEnvelope R CI ≤ metricEnvelope X := by
    apply sobolevCoefficientAmplitude_mono_all 6 (by positivity) (by positivity)
      (by gcongr)
    gcongr
  have hm0 : 0 ≤ correctionMetricEnvelope R CI :=
    sobolevCoefficientAmplitude_nonneg 6 (4*R) (3*CI*CI) (by positivity) (by positivity)
  have hmX : 0 ≤ metricEnvelope X := hm0.trans hm
  have hl : correctionLinearEnvelope R C1 CI ≤ linearEnvelope X := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply sobolevCoefficientAmplitude_mono_all 6 (by positivity) (by positivity) (by gcongr)
    gcongr
  have hq : correctionQuadraticEnvelope R C0 CI ≤ quadraticEnvelope X := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 6)
    apply sobolevCoefficientAmplitude_mono_all 6 (by positivity) (by positivity) (by gcongr)
    gcongr
  have hr : sobolevCoefficientRadius (Fin 4) (4*R) ≤ 64*X := by
    simp only [sobolevCoefficientRadius,Fintype.card_fin,Nat.cast_ofNat,
      max_eq_right (by norm_num : (1 : ℝ) ≤ 4)]
    nlinarith
  have hr0 : 0 ≤ sobolevCoefficientRadius (Fin 4) (4*R) :=
    sobolevCoefficientRadius_nonneg (4*R) (by positivity)
  have hn : normalizedCoefficientRadius 6 (4*R) (3*CI*CI) ≤
      (1+metricEnvelope X)*(64*X) := by
    apply mul_le_mul _ hr hr0 (by positivity)
    apply max_le
    · linarith
    · exact hm.trans (by linarith)
  have hrad : correctionCoefficientRadius R CI ≤ radiusEnvelope X := by
    have hprod : 0 ≤ (1+metricEnvelope X)*(64*X) := by positivity
    have h64 : 0 ≤ 64*X := by positivity
    unfold correctionCoefficientRadius radiusEnvelope
    apply max_le
    · linarith
    · apply max_le
      · exact hn.trans (by linarith)
      · exact hr.trans (by linarith)
  have hp5 : pressureCost c (correctionMetricEnvelope R CI) 5 ≤
      pressureCost ((1+X)^2)⁻¹ (metricEnvelope X) 5 :=
    pressureCost_mono hc (by positivity) hm0 (by simpa only [inv_inv] using hci) hm 5
  have hp6 : pressureCost c (correctionMetricEnvelope R CI) 6 ≤
      pressureCost ((1+X)^2)⁻¹ (metricEnvelope X) 6 :=
    pressureCost_mono hc (by positivity) hm0 (by simpa only [inv_inv] using hci) hm 6
  have hp50 := pressureCost_nonneg ((1+X)^2)⁻¹ (metricEnvelope X) (by positivity) hmX 5
  have hp60 := pressureCost_nonneg ((1+X)^2)⁻¹ (metricEnvelope X) (by positivity) hmX 6
  have hp : correctionPressureEnvelope c R CI ≤ pressureEnvelope X := by
    unfold correctionPressureEnvelope pressureEnvelope
    exact max_le (by linarith) (max_le (by linarith) (by linarith))
  exact ⟨hrad,hp,hm,hl,hq⟩

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]

/-- Correction bounds data, collecting `inverse`, `metric`, `first`, `time`, `radius`,
`pressure` and their compatibility conditions. -/
structure CorrectionBounds (Kc : CorrectionCoefficientBudget D P) (X : ℝ) : Prop where
  inverse : D.inverseBound ≤ X
  metric : inverseMetricBound D ≤ X
  first : inverseMetricFirstBound D ≤ X
  time : inverseMetricTimeBound D ≤ X
  radius : Kc.Rc ≤ X
  pressure : Kc.M ≤ X
  base : Kc.B ≤ X
  linear : Kc.A0 ≤ X
  quadratic : Kc.A2 ≤ X

theorem CorrectionBounds.mono {Kc : CorrectionCoefficientBudget D P} {X Y : ℝ}
    (h : CorrectionBounds D P Kc X) (hXY : X ≤ Y) : CorrectionBounds D P Kc Y :=
  ⟨h.inverse.trans hXY,h.metric.trans hXY,h.first.trans hXY,h.time.trans hXY,
    h.radius.trans hXY,h.pressure.trans hXY,h.base.trans hXY,h.linear.trans hXY,h.quadratic.trans
        hXY⟩

variable (R C0 C1 CI : ℝ) (hR : 0 ≤ R) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hCI : 0 ≤ CI)
  (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C0 * majorant R
      0
      n)
  (hF1 : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C1 * majorant
      R
      0 n)
  (hFI : ∀ n t x, ‖iteratedFDeriv ℝ n (D.FInv.field t : Space → Space →L[ℝ] Space) x‖ ≤ CI *
      majorant
      R 0 n)

include hR hC0 hC1 hCI hF hF1 hFI

theorem correctionBudget_bounds (X : ℝ) (hX : 1 ≤ X)
    (hRX : R ≤ X) (hC0X : C0 ≤ X) (hC1X : C1 ≤ X) (hCIX : CI ≤ X) :
    CorrectionBounds D P (correctionCoefficientBudget D P R C0 C1 CI hR hC0 hC1 hCI hF hF1 hFI)
      (primitiveEnvelope P X) := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hF0 : ∀ t x, ‖D.F.field t x‖ ≤ C0 := by
    intro t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using hF 0 t x
  have hsum : 1+C0 ≤ 1+X := by gcongr
  have hci := (D.normalLower_inv_le_of_frame C0 hC0 hF0).trans
    (pow_le_pow_left₀ (by positivity) hsum 2)
  obtain ⟨hr,hp,hb,hl,hq⟩ := correction_envelopes D.normalLower R C0 C1 CI X
    D.normalLower_pos hR hC0 hC1 hCI hRX hC0X hC1X hCIX hci
  obtain ⟨_,hiX,hmX,hfX,htX,hbX,hlX,hqX,hrX,hpX,_,_⟩ := primitive_components P X hX0
  have hi : D.inverseBound ≤ 1+X := by
    change 1+‖D.FInv.field‖ ≤ 1+X
    have hn := (coefficientPath_norm_le_of_gevrey D.FInv R CI hCI hFI).trans hCIX
    linarith
  have hm : inverseMetricBound D ≤ X^2 :=
    (inverseMetricBound_le_source D R C0 hC0 hF).trans (pow_le_pow_left₀ hC0 hC0X 2)
  have hf : inverseMetricFirstBound D ≤ 3*X*X*X := by
    apply (inverseMetricFirstBound_le_source D R C0 hR hC0 hF).trans
    gcongr
  have ht : inverseMetricTimeBound D ≤ 2*X*X := by
    apply (inverseMetricTimeBound_le_source D R C0 C1 hC0 hC1 hF hF1).trans
    gcongr
  exact ⟨hi.trans hiX,hm.trans hmX,hf.trans hfX,ht.trans htX,
    hr.trans hrX,hp.trans hpX,hb.trans hbX,hl.trans hlX,hq.trans hqX⟩

end EulerPacketCorrectionPrimitive

namespace EulerPacketCylinderField.CoefficientBudget

open EulerPacketCorrectionPrimitive EulerParameterWordGevrey EulerCylinderPathProduct

variable {P T : ℝ} [Fact (0 < P)] {O : EulerPacketProfileRecursion.Operators}
  {C : CoefficientData P T O} (B : CoefficientBudget C)

theorem primitive_bound (X : ℝ) (hX : 0 ≤ X) (hR : B.Rc ≤ X) (hC : B.amplitude ≤ X) :
    B.multiplierCost ≤ primitiveEnvelope P X ∧ B.termCost ≤ primitiveEnvelope P X := by
  have hb : B.multiplierCost ≤ multiplierEnvelope X :=
    mul_le_mul_of_nonneg_left
      (sobolevCoefficientAmplitude_mono_all 6 B.Rc_nonneg B.amplitude_nonneg hR hC) (by norm_num)
  have hc := productBlockConstant_nonneg P
  have ht : B.termCost ≤ termEnvelope P X := by
    unfold termCost slowCost termEnvelope
    gcongr
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hmX,htX⟩ := primitive_components P X hX
  exact ⟨hb.trans hmX,ht.trans htX⟩

end EulerPacketCylinderField.CoefficientBudget
