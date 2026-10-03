/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseHistoryPolynomialCost

/-! The actual zeroth-order history costs are bounded by fixed scalar
polynomials in the parent coefficient bounds and reciprocal horizon. -/

@[expose] public section


noncomputable section

namespace EulerTransverseHistoryBounds

open EulerPacketParentMeanCoercivity

/-- Scalar transport, given by `1+((2*(c⁻¹)^2*q^2*q1+c⁻¹*q1)*T+c⁻¹*q)`. -/
def scalarTransport (T c q q1 : ℝ) : ℝ :=
  1+((2*(c⁻¹)^2*q^2*q1+c⁻¹*q1)*T+c⁻¹*q)

theorem historyDifferenceCost_le_parentEnvelope
    (T c q q1 h Ti C C1 CH R : ℝ)
    (hT : 0 < T) (hT1 : T ≤ 1) (hTi : T⁻¹ ≤ Ti) (hc : 0 < c)
    (hci : c⁻¹ ≤ gramInverseEnvelope C)
    (hq0 : 0 ≤ q) (hq10 : 0 ≤ q1) (hh0 : 0 ≤ h)
    (hC : 0 ≤ C) (hC1 : 0 ≤ C1) (hCH : 0 ≤ CH) (hR : 0 ≤ R)
    (hq : q ≤ C) (hq1 : q1 ≤ C1) (hh : h ≤ CH) :
    historyDifferenceCost T c q q1 (T*q1+q) (1+T^2*h)
      (scalarTransport T c q q1) (C*R) (C1*R) (CH*R) ≤
        parentDifferenceEnvelope Ti C C1 CH R := by
  have hT0 := hT.le
  have hci0 := (inv_pos.mpr hc).le
  have hTi0 := (inv_pos.mpr hT).le.trans hTi
  have hGram : 0 ≤ gramInverseEnvelope C := by unfold gramInverseEnvelope; positivity
  have h2q : 0 ≤ 2*(c⁻¹)^2*q^2 := mul_nonneg (mul_nonneg zero_le_two (sq_nonneg _)) (sq_nonneg _)
  have hTr : 0 ≤ scalarTransport T c q q1 := add_nonneg zero_le_one
    (add_nonneg (mul_nonneg (add_nonneg (mul_nonneg h2q hq10) (mul_nonneg hci0 hq10)) hT0)
      (mul_nonneg hci0 hq0))
  have hd0 : 0 ≤ T*q1+q := add_nonneg (mul_nonneg hT0 hq10) hq0
  have ha0 : 0 ≤ 1+T^2*h := add_nonneg zero_le_one (mul_nonneg (sq_nonneg T) hh0)
  have hd : T*q1+q ≤ C1+C := by
    calc
      _ ≤ 1*C1+C := add_le_add (mul_le_mul hT1 hq1 hq10 (by norm_num)) hq
      _ = _ := by ring
  have ha : 1+T^2*h ≤ 1+CH := by
    apply add_le_add (le_refl (1 : ℝ))
    calc
      _ ≤ 1*CH := mul_le_mul (pow_le_one₀ hT0 hT1) hh hh0 (by norm_num)
      _ = _ := one_mul CH
  have hr : scalarTransport T c q q1 ≤ transportEnvelope C C1 := by
    unfold scalarTransport transportEnvelope
    calc
      _ ≤ 1+((2*(gramInverseEnvelope C)^2*C^2*C1+gramInverseEnvelope C*C1)*1 +
          gramInverseEnvelope C*C) := by
        have hG2 : 0 ≤ 2*(gramInverseEnvelope C)^2 := mul_nonneg zero_le_two (sq_nonneg _)
        have hsq := mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hci0 hci 2)
          zero_le_two) (pow_le_pow_left₀ hq0 hq 2) (sq_nonneg q) hG2
        have hlead := mul_le_mul hsq hq1 hq10 (mul_nonneg hG2 (sq_nonneg C))
        refine add_le_add le_rfl (add_le_add (mul_le_mul (add_le_add hlead
          (mul_le_mul hci hq1 hq10 hGram)) hT1 hT0 ?_) (mul_le_mul hci hq hq0 hGram))
        exact add_nonneg (mul_nonneg (mul_nonneg hG2 (sq_nonneg C)) hC1) (mul_nonneg hGram hC1)
      _ = _ := by ring
  apply (historyDifferenceCost_le_envelope T c Ti (gramInverseEnvelope C) q q1
    (T*q1+q) (1+T^2*h) (scalarTransport T c q q1) (C*R) (C1*R) (CH*R)
    hT hT1 hTi hc hci hq0 hq10 hd0 ha0 hTr
    (mul_nonneg hC hR) (mul_nonneg hC1 hR) (mul_nonneg hCH hR)).trans
  exact differenceEnvelope_mono hTi0 hGram hq0 hq10 hd0 ha0 hTr
    (mul_nonneg hC hR) (mul_nonneg hC1 hR) (mul_nonneg hCH hR)
    le_rfl le_rfl hq hq1 hd ha hr le_rfl le_rfl le_rfl

theorem parentDifferenceEnvelope_mono
    {Ti C C1 CH R Ti' C' C1' CH' R' : ℝ}
    (hTi : 0 ≤ Ti) (hC : 0 ≤ C) (hC1 : 0 ≤ C1) (hCH : 0 ≤ CH) (hR : 0 ≤ R)
    (hTi' : Ti ≤ Ti') (hC' : C ≤ C') (hC1' : C1 ≤ C1') (hCH' : CH ≤ CH') (hR' : R ≤ R') :
    parentDifferenceEnvelope Ti C C1 CH R ≤ parentDifferenceEnvelope Ti' C' C1' CH' R' := by
  have hTi0 := hTi.trans hTi'
  have hC0 := hC.trans hC'
  have hC10 := hC1.trans hC1'
  have hCH0 := hCH.trans hCH'
  have hR0 := hR.trans hR'
  have hg0 : 0 ≤ gramInverseEnvelope C := sq_nonneg _
  have hg : gramInverseEnvelope C ≤ gramInverseEnvelope C' :=
    pow_le_pow_left₀ (add_nonneg (mul_nonneg zero_le_three (sq_nonneg C)) zero_le_one)
      (add_le_add_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC hC' 2) zero_le_three) 1) 2
  have hg0' := hg0.trans hg
  have h2g := mul_nonneg (zero_le_two (α := ℝ)) (sq_nonneg (gramInverseEnvelope C'))
  unfold parentDifferenceEnvelope
  apply differenceEnvelope_mono hTi hg0 hC hC1
    (add_nonneg hC1 hC) (add_nonneg zero_le_one hCH) (transportEnvelope_nonneg C C1 hC hC1)
    (mul_nonneg hC hR) (mul_nonneg hC1 hR) (mul_nonneg hCH hR)
  · exact hTi'
  · exact hg
  · exact hC'
  · exact hC1'
  · exact add_le_add hC1' hC'
  · exact add_le_add (le_refl (1 : ℝ)) hCH'
  · exact add_le_add (add_le_add_right (add_le_add (mul_le_mul (mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0 hg 2) zero_le_two)
      (pow_le_pow_left₀ hC hC' 2) (sq_nonneg C) h2g) hC1' hC1
      (mul_nonneg h2g (sq_nonneg C'))) (mul_le_mul hg hC1' hC1 hg0')) 1) (mul_le_mul hg hC' hC hg0')
  · exact mul_le_mul hC' hR' hR hC0
  · exact mul_le_mul hC1' hR' hR hC10
  · exact mul_le_mul hCH' hR' hR hCH0

end EulerTransverseHistoryBounds
