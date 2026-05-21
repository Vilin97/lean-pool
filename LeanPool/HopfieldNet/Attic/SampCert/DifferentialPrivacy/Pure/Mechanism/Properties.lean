/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Pure.DP
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Pure.Mechanism.Code
import LeanPool.HopfieldNet.SampCert.Samplers.LaplaceGen.Basic

/-!
# Properties of ``privNoisedQueryPure``

This file proves pure differential privacy for ``privNoisedQueryPure``.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

lemma natAbs_to_abs (a b : ℤ) :
  (a - b).natAbs = |(a : ℝ) - (b : ℝ)| := by
  rw [Int.cast_natAbs]
  simp only [cast_abs, Int.cast_sub]

lemma normalizing_constant_nonzero (ε₁ ε₂ Δ : ℕ+) :
  (rexp (ε₁ / (Δ * ε₂)) - 1) / (rexp (ε₁ / (Δ * ε₂)) + 1) ≠ 0 := by
  field_simp
  intro h
  have A : 0 < (ε₁ : ℝ) / (Δ * ε₂) := by
    simp
  have B : rexp 0 < rexp ((ε₁ : ℝ) / (Δ * ε₂)) := by
    exact exp_lt_exp.mpr A
  rw [exp_zero] at B
  rw [@sub_eq_zero] at h
  have C : 1 ≠ rexp ((ε₁ : ℝ) / (Δ * ε₂)) := by
    exact _root_.ne_of_lt B
  rw [h] at C
  contradiction

/--
Differential privacy bound for a ``privNoisedQueryPure``
-/
theorem privNoisedQueryPure_DP_bound (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  DP (privNoisedQueryPure query Δ ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  intros l₁ l₂ neighbours x
  simp [privNoisedQueryPure]
  simp [DiscreteLaplaceGenSamplePMF]
  simp [DFunLike.coe, PMF.instFunLike]
  rw [← ENNReal.ofReal_div_of_pos]
  · apply ofReal_le_ofReal
    rw [division_def]
    rw [mul_inv]
    rw [← mul_assoc]
    conv =>
      left
      left
      rw [mul_assoc]
      right
      rw [mul_comm]
    conv =>
      left
      left
      rw [← mul_assoc]
      left
      rw [mul_inv_cancel (normalizing_constant_nonzero ε₁ ε₂ Δ)]
    simp only [one_mul]
    rw [← division_def]
    rw [← exp_sub]
    simp only [sub_neg_eq_add, exp_le_exp]
    rw [neg_div']
    rw [div_add_div_same]
    rw [division_def]
    apply (mul_inv_le_iff' _).mpr
    · have B : (ε₁ : ℝ) / ε₂ * (Δ * ε₂ / ε₁) = Δ := by
        ring_nf
        simp
        field_simp
      rw [B]
      clear B

      rw [add_comm]
      ring_nf
      -- Triangle inequality
      have C := @abs_sub_abs_le_abs_sub ℝ _ ((x : ℝ) - (query l₂)) ((x : ℝ) - (query l₁))
      apply le_trans C
      clear C
      simp

      simp [sensitivity] at bounded_sensitivity
      replace bounded_sensitivity := bounded_sensitivity l₁ l₂ neighbours

      rw [← natAbs_to_abs]
      exact Nat.cast_le.mpr bounded_sensitivity

    · simp
  · rw [_root_.mul_pos_iff]
    left
    constructor
    · rw [_root_.div_pos_iff]
      left
      have A : 1 < rexp ((ε₁ : ℝ) / (Δ * ε₂)) := by
        rw [← exp_zero]
        apply exp_lt_exp.mpr
        simp
      constructor
      · simp [A]
      · apply @lt_trans _ _ _ 2 _
        · simp
        · rw [← one_add_one_eq_two]
          exact (add_lt_add_iff_right 1).mpr A
    · apply exp_pos


/--
Laplace noising mechanism ``privNoisedQueryPure`` produces a pure ``ε₁/ε₂``-DP mechanism from a Δ-sensitive query.
-/
theorem privNoisedQueryPure_DP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  PureDP (privNoisedQueryPure query Δ ε₁ ε₂) ((ε₁ : NNReal) / ε₂) := by
  simp [PureDP]
  apply privNoisedQueryPure_DP_bound
  apply bounded_sensitivity

end SLang
