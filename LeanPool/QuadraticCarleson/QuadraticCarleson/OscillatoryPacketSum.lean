/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleMainTerm
import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleOperatorAction

/-!
# The oscillatory packet sum in the negative endpoint example

This file bounds the contribution of the packets to the left of an admissible
observation point.  The exact lower edge of the paper's exponent window turns
the two-fold oscillatory estimate into a geometric series.
-/

open Finset Set

namespace QuadraticCarleson


private theorem offSupportOscillatoryConstant_nonneg :
    0 ≤ offSupportOscillatoryConstant := by
  unfold offSupportOscillatoryConstant
  positivity

private theorem sum_Icc_quarter_pow_tsub_le_two (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 k, ((1 / 4 : ℝ) ^ (k - j)) ≤ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    have hrewrite :
        (∑ j ∈ Finset.Icc 1 k, (1 / 4 : ℝ) ^ (k + 1 - j)) =
          (1 / 4 : ℝ) * ∑ j ∈ Finset.Icc 1 k, (1 / 4 : ℝ) ^ (k - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
      rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]
      ring
    rw [hrewrite]
    norm_num [Nat.add_sub_cancel]
    nlinarith

private theorem four_pow_eq_two_pow_twice (m : ℕ) :
    (4 : ℝ) ^ m = (2 : ℝ) ^ (m * 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    rw [show (m + 1) * 2 = m * 2 + 2 by omega, pow_add]
    norm_num

private theorem oscillatory_packet_term_norm_le
    {N n : ℕ} {L A τ : ℝ} {k : ℤ}
    (hN : 100 ≤ N) (hkn : (k, n) ∈ paperMainTermIndices N L)
    (hA : 0 < A) (hLA : (2 : ℝ) ^ L = A)
    (hτ : (1 : ℝ) / 4 ≤ τ) {j : ℕ} (hj : j ∈ Finset.Icc 1 k.toNat) :
    ‖offSupportKernelAction ((2 : ℝ) ^ n) (j : ℝ) (packetScale N j)
        ((k : ℝ) + τ)‖ ≤
      (64 * offSupportOscillatoryConstant / A ^ 2) *
        (1 / 4 : ℝ) ^ (k.toNat - j) := by
  obtain ⟨hk, hnlo, _⟩ := mem_paperMainTermIndices.mp hkn
  have hkpos : 0 < k := paperBohrIndices_pos (by omega) hk
  have hkcast : (k.toNat : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hkpos.le
  have hjone : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k.toNat := (Finset.mem_Icc.mp hj).2
  have hNj : 2 ≤ N * j := by
    calc
      2 ≤ 100 * 1 := by norm_num
      _ ≤ N * j := Nat.mul_le_mul hN hjone
  have hscale : packetScale N j ≤ (1 : ℝ) / 4 := by
    unfold packetScale
    calc
      (2 : ℝ) ^ (-((N * j : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (-2 : ℤ) := by
        apply zpow_le_zpow_right₀ (by norm_num)
        exact neg_le_neg (by exact_mod_cast hNj : (2 : ℤ) ≤ (N * j : ℕ))
      _ = (1 : ℝ) / 4 := by norm_num
  have hjkR : (j : ℝ) ≤ k := by
    rw [← hkcast]
    exact_mod_cast hjk
  have hdistpos : 0 < (k : ℝ) + τ - j := by
    linarith
  have houtside : (k : ℝ) + τ ∉
      Icc ((j : ℝ) - packetScale N j / 2)
        ((j : ℝ) + packetScale N j / 2) := by
    intro hx
    linarith [hx.2]
  have hraw := offSupportKernelAction_oscillatory_norm_le
    (modulation := (2 : ℝ) ^ n) (s := (j : ℝ))
    (t := packetScale N j) (x := (k : ℝ) + τ)
    (pow_pos (by norm_num) n) (packetScale_pos N j) houtside
  have hscaleR : packetScale N j =
      (2 : ℝ) ^ (-(N * j : ℝ)) := by
    unfold packetScale
    rw [← Real.rpow_intCast]
    congr 2
    norm_num
  have hlambdaR : (2 : ℝ) ^ n = (2 : ℝ) ^ (n : ℝ) := by
    exact (Real.rpow_natCast 2 n).symm
  have hexp : L + (N * (k.toNat - j) : ℕ) ≤
      (n : ℝ) - (N * j : ℕ) := by
    have hsubR : ((k.toNat - j : ℕ) : ℝ) = (k.toNat : ℝ) - j := by
      exact Nat.cast_sub hjk
    push_cast at hnlo ⊢
    rw [hkcast] at hsubR
    nlinarith
  have hprod : A * (2 : ℝ) ^ (N * (k.toNat - j)) ≤
      (2 : ℝ) ^ n * packetScale N j := by
    rw [hlambdaR, hscaleR, ← hLA]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      simpa only [Nat.cast_mul, sub_eq_add_neg] using hexp)
  have hprodpos : 0 < A * (2 : ℝ) ^ (N * (k.toNat - j)) := by positivity
  have hdist : (1 : ℝ) / 4 ≤ |(k : ℝ) + τ - j| := by
    rw [abs_of_pos hdistpos]
    linarith
  have hden :
      A ^ 2 * (4 : ℝ) ^ (N * (k.toNat - j)) * ((1 : ℝ) / 4) ^ 3 ≤
        ((2 : ℝ) ^ n) ^ 2 * (packetScale N j) ^ 2 *
          |(k : ℝ) + τ - j| ^ 3 := by
    have hsq : (A * (2 : ℝ) ^ (N * (k.toNat - j))) ^ 2 ≤
        ((2 : ℝ) ^ n * packetScale N j) ^ 2 := by nlinarith
    have hcube : ((1 : ℝ) / 4) ^ 3 ≤
        |(k : ℝ) + τ - j| ^ 3 := by
      exact pow_le_pow_left₀ (by positivity) hdist 3
    have hmul := mul_le_mul hsq hcube (by positivity) (by positivity)
    rw [four_pow_eq_two_pow_twice]
    simpa only [mul_pow, ← pow_mul, Nat.reducePow, mul_comm] using hmul
  have hfrac :
      offSupportOscillatoryConstant /
          (((2 : ℝ) ^ n) ^ 2 * (packetScale N j) ^ 2 *
            |(k : ℝ) + τ - j| ^ 3) ≤
        offSupportOscillatoryConstant /
          (A ^ 2 * (4 : ℝ) ^ (N * (k.toNat - j)) * ((1 : ℝ) / 4) ^ 3) := by
    exact div_le_div_of_nonneg_left offSupportOscillatoryConstant_nonneg
      (by positivity) hden
  have hgeom : (4 : ℝ) ^ (k.toNat - j) ≤
      (4 : ℝ) ^ (N * (k.toNat - j)) := by
    apply pow_le_pow_right₀ (by norm_num)
    simpa only [one_mul] using Nat.mul_le_mul_right (k.toNat - j) (by omega : 1 ≤ N)
  have hgeomdiv :
      offSupportOscillatoryConstant * 64 / A ^ 2 /
          (4 : ℝ) ^ (N * (k.toNat - j)) ≤
        offSupportOscillatoryConstant * 64 / A ^ 2 /
          (4 : ℝ) ^ (k.toNat - j) := by
    have hcoef : 0 ≤ offSupportOscillatoryConstant * 64 / A ^ 2 :=
      div_nonneg (mul_nonneg offSupportOscillatoryConstant_nonneg (by norm_num))
        (sq_nonneg A)
    exact div_le_div_of_nonneg_left hcoef (by positivity) hgeom
  calc
    _ ≤ offSupportOscillatoryConstant /
        (((2 : ℝ) ^ n) ^ 2 * (packetScale N j) ^ 2 *
          |(k : ℝ) + τ - j| ^ 3) := hraw
    _ ≤ offSupportOscillatoryConstant /
        (A ^ 2 * (4 : ℝ) ^ (N * (k.toNat - j)) * ((1 : ℝ) / 4) ^ 3) := hfrac
    _ ≤ (64 * offSupportOscillatoryConstant / A ^ 2) *
        (1 / 4 : ℝ) ^ (k.toNat - j) := by
      calc
        _ = offSupportOscillatoryConstant * 64 / A ^ 2 /
            (4 : ℝ) ^ (N * (k.toNat - j)) := by field_simp; ring
        _ ≤ offSupportOscillatoryConstant * 64 / A ^ 2 /
            (4 : ℝ) ^ (k.toNat - j) := hgeomdiv
        _ = _ := by
          rw [one_div_pow]
          field_simp

/-- The packets with indices `1 ≤ j ≤ k` are in the oscillatory regime at
`x = k + τ`.  The exact lower exponent-window inequality gives geometric
decay as `j` moves left from `k`; after the counterexample normalization their
total contribution is `O(1 / (N A²))`, uniformly in the witness `(k,n)`.

The harmless explicit factor `128` consists of `64`, coming from
`|x-j| ≥ τ ≥ 1/4`, and the finite geometric-series bound `2`. -/
theorem paperOscillatoryPacketSum_norm_le
    {N n : ℕ} {L A τ : ℝ} {k : ℤ}
    (hN : 100 ≤ N) (hkn : (k, n) ∈ paperMainTermIndices N L)
    (hA : 0 < A) (hLA : (2 : ℝ) ^ L = A)
    (hτ : τ ∈ Set.Ico ((1 : ℝ) / 4) (1 / 2)) :
    ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.Icc 1 k.toNat,
        offSupportKernelAction ((2 : ℝ) ^ n) (j : ℝ) (packetScale N j)
          ((k : ℝ) + τ)‖ ≤
      128 * offSupportOscillatoryConstant / ((N : ℝ) * A ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcoef : 0 ≤ 64 * offSupportOscillatoryConstant / A ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) offSupportOscillatoryConstant_nonneg)
      (sq_nonneg A)
  have hsum :
      ‖∑ j ∈ Finset.Icc 1 k.toNat,
          offSupportKernelAction ((2 : ℝ) ^ n) (j : ℝ) (packetScale N j)
            ((k : ℝ) + τ)‖ ≤
        ∑ j ∈ Finset.Icc 1 k.toNat,
          (64 * offSupportOscillatoryConstant / A ^ 2) *
            (1 / 4 : ℝ) ^ (k.toNat - j) := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 k.toNat,
          ‖offSupportKernelAction ((2 : ℝ) ^ n) (j : ℝ) (packetScale N j)
            ((k : ℝ) + τ)‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        exact oscillatory_packet_term_norm_le hN hkn hA hLA hτ.1 hj
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hNr]
  calc
    (N : ℝ)⁻¹ *
        ‖∑ j ∈ Finset.Icc 1 k.toNat,
          offSupportKernelAction ((2 : ℝ) ^ n) (j : ℝ) (packetScale N j)
            ((k : ℝ) + τ)‖ ≤
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 k.toNat,
        (64 * offSupportOscillatoryConstant / A ^ 2) *
          (1 / 4 : ℝ) ^ (k.toNat - j) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNr.le)
    _ = (N : ℝ)⁻¹ * (64 * offSupportOscillatoryConstant / A ^ 2) *
        ∑ j ∈ Finset.Icc 1 k.toNat,
          (1 / 4 : ℝ) ^ (k.toNat - j) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (N : ℝ)⁻¹ * (64 * offSupportOscillatoryConstant / A ^ 2) * 2 := by
      exact mul_le_mul_of_nonneg_left
        (sum_Icc_quarter_pow_tsub_le_two k.toNat)
        (mul_nonneg (inv_nonneg.mpr hNr.le) hcoef)
    _ = 128 * offSupportOscillatoryConstant / ((N : ℝ) * A ^ 2) := by
      field_simp [ne_of_gt hNr, ne_of_gt hA]
      ring

end QuadraticCarleson
