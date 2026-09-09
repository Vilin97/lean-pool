/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketMomentumExpansion

@[expose] public section

/-! Bounds for the surviving grades of the actual finite packet residual. -/

noncomputable section

namespace EulerPacketTailBound

open Finset

theorem sum_geometric_le_two (q : ℝ) (hq : 0 ≤ q) (hqhalf : q ≤ 1/2) (N : ℕ) :
    (∑ i ∈ range N, q^i) ≤ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ']
      simp only [pow_succ, pow_zero]
      rw [← sum_mul]
      have h := mul_le_mul_of_nonneg_right ih hq
      linarith

theorem sum_geometric_Ico_le (q : ℝ) (hq : 0 ≤ q) (hqhalf : q ≤ 1/2) (a b : ℕ) :
    (∑ i ∈ Ico a b, q^i) ≤ 2*q^a := by
  rw [sum_Ico_eq_sum_range]
  simp only [pow_add]
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left (sum_geometric_le_two q hq hqhalf (b-a))
    (pow_nonneg hq a)).trans_eq (mul_comm _ _)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finite_tail_norm_le (κ B : ℝ) (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hsmall : κ*B ≤ 1/2) (N : ℕ) (c : ℕ → E)
    (hc : ∀ n ∈ Ico (N+1) (2*N+3), ‖c n‖ ≤ B^(n+1)) :
    ‖∑ n ∈ Ico (N+1) (2*N+3), κ^n • c n‖ ≤ 2*B*(κ*B)^(N+1) := by
  calc
    _ ≤ ∑ n ∈ Ico (N+1) (2*N+3), ‖κ^n • c n‖ := norm_sum_le _ _
    _ = ∑ n ∈ Ico (N+1) (2*N+3), κ^n*‖c n‖ := by
      simp only [norm_smul, norm_pow, Real.norm_of_nonneg hκ]
    _ ≤ ∑ n ∈ Ico (N+1) (2*N+3), κ^n*B^(n+1) :=
      sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hc n hn) (pow_nonneg hκ n))
    _ = B*(∑ n ∈ Ico (N+1) (2*N+3), (κ*B)^n) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      simp only [pow_succ, mul_pow]
      ring
    _ ≤ B*(2*(κ*B)^(N+1)) := mul_le_mul_of_nonneg_left
      (sum_geometric_Ico_le (κ*B) (mul_nonneg hκ hB) hsmall (N+1) (2*N+3)) hB
    _ = _ := by ring

/-- Includes the source's final k times inverse-frame normalization. -/
theorem normalized_tail_norm_le (k B C : ℝ) (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hsmall : B/k ≤ 1/2) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ C) (N : ℕ) (c : ℕ → E)
    (hc : ∀ n ∈ Ico (N+1) (2*N+3), ‖c n‖ ≤ B^(n+1)) :
    ‖k • L (∑ n ∈ Ico (N+1) (2*N+3), (k⁻¹)^n • c n)‖ ≤
      2*C*k*B*(B/k)^(N+1) := by
  have hC : 0 ≤ C := (norm_nonneg L).trans hL
  have hq : k⁻¹*B=B/k := by ring
  have htail := finite_tail_norm_le k⁻¹ B (inv_nonneg.mpr hk) hB
    (by simpa only [hq] using hsmall) N c hc
  rw [hq] at htail
  rw [norm_smul, Real.norm_of_nonneg hk]
  calc
    _ ≤ k*(C*‖∑ n ∈ Ico (N+1) (2*N+3), (k⁻¹)^n • c n‖) :=
      mul_le_mul_of_nonneg_left ((L.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _))) hk
    _ ≤ k*(C*(2*B*(B/k)^(N+1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail hC) hk
    _ = _ := by ring

end EulerPacketTailBound
