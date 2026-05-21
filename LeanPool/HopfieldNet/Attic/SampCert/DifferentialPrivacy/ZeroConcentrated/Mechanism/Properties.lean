/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Code

/-!
# ``privNoisedQuery`` Implementation

This file proves differential privacy for ``privNoisedQuery``.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang


/--
The zCDP mechanism with bounded sensitivity satisfies the bound for ``(Δε₂/ε₁)^2``-zCDP.
-/
theorem privNoisedQuery_zCDPBound (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  zCDPBound (privNoisedQuery query Δ ε₁ ε₂) ((ε₁ : NNReal) / ε₂) := by
  simp [zCDPBound, privNoisedQuery]
  intros α h1 l₁ l₂ h2
  have A := @discrete_GaussianGenSample_ZeroConcentrated α h1 (Δ * ε₂) ε₁ (query l₁) (query l₂)
  apply le_trans A
  clear A

  -- Turn it into an equality ASAP
  rw [sensitivity] at bounded_sensitivity
  have bounded_sensitivity := bounded_sensitivity l₁ l₂ h2
  have X :
    (ENNReal.ofReal α *
      (ENNReal.ofReal ((query l₁ - query l₂).cast ^ OfNat.ofNat 2) /
        (OfNat.ofNat 2 * (ofNNReal (NNReal.ofPNat (Δ * ε₂)) / ofNNReal (NNReal.ofPNat ε₁)) ^ OfNat.ofNat 2))) ≤
  (ENNReal.ofReal α *
      (ENNReal.ofReal (Δ ^ OfNat.ofNat 2) /
        (OfNat.ofNat 2 * (ofNNReal (NNReal.ofPNat (Δ * ε₂)) / ofNNReal (NNReal.ofPNat ε₁)) ^ OfNat.ofNat 2))) := by
      refine (ENNReal.mul_le_mul_left ?G1 ?G2).mpr ?G3
      case G1 =>
        intro HK
        simp_all
        linarith
      case G2 => exact ofReal_ne_top
      refine ENNReal.div_le_div ?G4 ?G5
      case G5 => rfl
      apply ofReal_le_ofReal
      refine sq_le_sq.mpr ?G4.h.a
      simp only [NNReal.ofPNat, Nonneg.mk_natCast]
      rw [NNReal.abs_eq]
      have X1 : NNReal.toReal ((query l₁ - query l₂).natAbs).cast ≤ NNReal.toReal Δ.val.cast := by
        simp
        apply bounded_sensitivity
      apply (le_trans _ X1)
      clear X1
      generalize HW : (query l₁ - query l₂) = W
      rw [NNReal.coe_natCast]
      rw [natAbs]
      split <;> simp_all
      rw [abs_le]
      apply And.intro
      · linarith
      · linarith
  apply le_trans
  · apply X
  clear X
  apply Eq.le
  rw [ENNReal.ofReal_mul ?G1]
  case G1 =>
    simp
    apply div_nonneg
    · apply sq_nonneg
    · apply sq_nonneg
  rw [ENNReal.ofReal_mul ?G1]
  case G1 => simp
  rw [mul_comm]
  congr
  repeat rw [division_def]
  rw [ENNReal.mul_inv ?G1 ?G2]
  case G1 => left ; simp
  case G2 => left ; simp
  simp
  rw [mul_comm]
  repeat rw [mul_assoc]
  congr
  · rw [ENNReal.ofReal_inv_of_pos ?G1]
    case G1 => simp
    congr
    rw [ENNReal.ofReal]
    simp
  ring_nf
  rw [ENNReal.mul_inv ?G1 ?G2]
  case G1 =>
    left
    apply ENNReal.pow_ne_zero
    apply coe_ne_zero.mpr
    rw [HMul.hMul]
    rw [instHMul]
    simp only [ne_eq, Nat.cast_eq_zero]
    cases ε₂
    cases Δ
    rw [Mul.mul]
    rw [instPNatMul]
    rw [Positive.instMulSubtypeLtOfNat_mathlib]
    simp
    aesop
  case G2 =>
    left
    exact Ne.symm (ne_of_beq_false rfl)
  rw [ENNReal.ofReal_mul ?G1]
  case G1 => apply sq_nonneg
  rw [mul_assoc]
  rw [mul_comm]
  rw [mul_assoc]
  congr
  · rw [ENNReal.inv_pow]
    rw [ENNReal.ofReal_pow ?G1]
    case G1 => exact NNReal.zero_le_coe
    congr
    rw [InvolutiveInv.inv_inv]
    rw [ENNReal.ofReal]
    simp
  · rcases Δ with ⟨ Δ', HΔ ⟩
    rcases ε₂ with ⟨ ε₂', Hε₂ ⟩
    simp
    conv =>
      enter [1, 2, 1, 1, 1]
      rw [HMul.hMul]
      rw [instHMul]
      simp
      rw [Mul.mul]
      rw [instPNatMul]
      rw [Positive.instMulSubtypeLtOfNat_mathlib]
      simp
    rw [ENNReal.inv_pow]
    rw [<- ENNReal.rpow_neg_one]
    rw [← ENNReal.rpow_mul_natCast]
    rw [ENNReal.ofReal]
    rw [ENNReal.coe_rpow_of_ne_zero ?G1]
    case G1 =>
      apply NNReal.coe_ne_zero.mp
      simp
      aesop
    rw [<- ENNReal.coe_mul]
    rw [ENNReal.ofReal]
    congr
    simp
    rw [NNReal.rpow_neg]
    rw [NNReal.mul_rpow]
    simp
    have X : (0 : NNReal) < (Δ'.cast * Δ'.cast) := by
      simp
      intro HK
      rw [HK] at HΔ
      simp at HΔ
    have COE1 : (NNReal.toReal Δ'.cast ^ OfNat.ofNat 2).toNNReal  = (Δ'.cast ^ OfNat.ofNat 2) := by
      simp
      rw [Real.toNNReal]
      -- Only rewriting sq because it's so hard to factor out terms with implicit coercions
      rw [sq]
      rw [sq]
      conv =>
        rhs
        rw [<- @max_eq_left_of_lt _ _ (Δ'.cast * Δ'.cast) 0 X]
      congr
    rw [COE1]
    generalize HA : ((Δ'.cast ^ OfNat.ofNat 2) : NNReal) = A
    rw [mul_comm]
    rw [mul_assoc]
    rw [inv_mul_cancel ?G1]
    case G1 =>
      intro HK
      rw [HK] at HA
      simp at HA
      rw [HA] at HΔ
      simp at HΔ
    clear A HA
    simp
    rw [Real.toNNReal_inv]
    congr
    rw [Real.toNNReal_pow ?G1]
    case G1 => exact NNReal.zero_le_coe
    congr
    simp only [Real.toNNReal_coe]

lemma discrete_gaussian_shift {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (τ x : ℤ) :
  discrete_gaussian σ μ (x - τ) = discrete_gaussian σ (μ + τ) (x) := by
  simp [discrete_gaussian]
  congr 1
  · simp [gauss_term_ℝ]
    congr 3
    ring_nf
  · rw [shifted_gauss_sum h]

/--
privNoisedQuery preserves absolute continuity between neighbours
-/
def privNoisedQuery_AC (query : List T -> ℤ) (Δ ε₁ ε₂ : ℕ+) : ACNeighbour (privNoisedQuery query Δ ε₁ ε₂) := by
  rw [ACNeighbour]
  intro l₁ l₂ _
  rw [AbsCts]
  intro n Hk
  exfalso
  simp [privNoisedQuery, DiscreteGaussianGenPMF, DiscreteGaussianGenSample, DFunLike.coe] at Hk
  have Hk := Hk (n - query l₂)
  simp at Hk
  have X := @discrete_gaussian_pos (Δ.val.cast * ε₂.val.cast / ε₁.val.cast) ?G1 0 (n - query l₂)
  case G1 =>
    cases Δ
    cases ε₁
    cases ε₂
    aesop
  simp at *
  linarith

/--
The zCDP mechanism is ``(Δε₂/ε₁)^2``-zCDP.
-/
theorem privNoisedQuery_zCDP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  zCDP (privNoisedQuery query Δ ε₁ ε₂) ((ε₁ : NNReal) / ε₂) := by
  simp [zCDP]
  apply And.intro
  · exact privNoisedQuery_AC query Δ ε₁ ε₂
  · apply privNoisedQuery_zCDPBound
    exact bounded_sensitivity


end SLang
