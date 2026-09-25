/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.Geometry

/-! # Geometric -/

@[expose] public section

namespace Homogenization

noncomputable section

theorem geometricWeight_one_shift {s : ℝ} (h n : ℕ) :
    geometricWeight s 1 n =
      Real.rpow (3 : ℝ) (s * (h : ℝ)) * geometricWeight s 1 (n + h) := by
  rw [geometricWeight_one_eq, geometricWeight_one_eq]
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hpow :
      Real.rpow (3 : ℝ) (s * (h : ℝ)) *
          Real.rpow (3 : ℝ) (-s * ((n + h : ℕ) : ℝ)) =
        Real.rpow (3 : ℝ) (-s * (n : ℝ)) := by
    have hexp :
        -s * (n : ℝ) = s * (h : ℝ) + -s * ((n + h : ℕ) : ℝ) := by
      norm_num
      ring
    calc
      Real.rpow (3 : ℝ) (s * (h : ℝ)) *
          Real.rpow (3 : ℝ) (-s * ((n + h : ℕ) : ℝ)) =
        Real.rpow (3 : ℝ) (s * (h : ℝ) + -s * ((n + h : ℕ) : ℝ)) := by
          simpa using (Real.rpow_add h3 (s * (h : ℝ)) (-s * ((n + h : ℕ) : ℝ))).symm
      _ = Real.rpow (3 : ℝ) (-s * (n : ℝ)) := by rw [hexp]
  calc
    geometricDiscount s 1 * Real.rpow (3 : ℝ) (-s * (n : ℝ)) =
        geometricDiscount s 1 *
          (Real.rpow (3 : ℝ) (s * (h : ℝ)) * Real.rpow (3 : ℝ) (-s * ((n + h : ℕ) : ℝ))) := by
      rw [hpow]
    _ = Real.rpow (3 : ℝ) (s * (h : ℝ)) *
          (geometricDiscount s 1 * Real.rpow (3 : ℝ) (-s * ((n + h : ℕ) : ℝ))) := by ring

theorem rpow_neg_mul_nat_succ_eq (s : ℝ) (n : ℕ) :
    Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) =
      Real.rpow (3 : ℝ) (-s) * Real.rpow (3 : ℝ) (-s * (n : ℝ)) := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hexp : -s * ((n + 1 : ℕ) : ℝ) = -s + -s * (n : ℝ) := by
    calc
      -s * ((n + 1 : ℕ) : ℝ) = -s * ((n : ℝ) + 1) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = -s + -s * (n : ℝ) := by ring
  calc
    Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) =
        Real.rpow (3 : ℝ) (-s + -s * (n : ℝ)) := by rw [hexp]
    _ = Real.rpow (3 : ℝ) (-s) * Real.rpow (3 : ℝ) (-s * (n : ℝ)) := by
          simpa using (Real.rpow_add h3 (-s) (-s * (n : ℝ)))

theorem summable_rpow_neg_s_nat_mul_of_summable_geometricWeight_one
    {H : ℕ → ℝ} {s : ℝ} (hs : 0 < s)
    (hsum : Summable (fun n : ℕ => geometricWeight s 1 n * H n)) :
    Summable (fun n : ℕ => Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n) := by
  have hdisc_ne : geometricDiscount s 1 ≠ 0 := (geometricDiscount_pos (by simpa using hs)).ne'
  have hEq :
      (fun n : ℕ => geometricWeight s 1 n * H n) =
        fun n : ℕ => geometricDiscount s 1 * (Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n) := by
    funext n
    rw [geometricWeight_one_eq]
    ring
  rw [hEq] at hsum
  exact (summable_mul_left_iff hdisc_ne).mp hsum

theorem summable_rpow_neg_s_nat_succ_mul_sub_of_summable_geometricWeight_one
    {H : ℕ → ℝ} {s : ℝ} (hs : 0 < s)
    (hsum : Summable (fun n : ℕ => geometricWeight s 1 n * H n)) :
    Summable (fun n : ℕ =>
      Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * (H (n + 1) - H n)) := by
  let r : ℝ := Real.rpow (3 : ℝ) (-s)
  let A : ℕ → ℝ := fun n => Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n
  have hA : Summable A := summable_rpow_neg_s_nat_mul_of_summable_geometricWeight_one hs hsum
  have hA1 : Summable (fun n : ℕ => A (n + 1)) := (summable_nat_add_iff 1).2 hA
  have hrA : Summable (fun n : ℕ => r * A n) := hA.mul_left r
  have hEq :
      (fun n : ℕ => Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * (H (n + 1) - H n)) =
        fun n : ℕ => A (n + 1) - r * A n := by
    funext n
    calc
      Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * (H (n + 1) - H n) =
          Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * H (n + 1) -
            Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * H n := by
              ring
      _ = A (n + 1) - r * A n := by
            dsimp [A, r]
            congr 1
            calc
              Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * H n =
                  (Real.rpow (3 : ℝ) (-s) * Real.rpow (3 : ℝ) (-s * (n : ℝ))) * H n := by
                    exact congrArg (fun x : ℝ => x * H n) (rpow_neg_mul_nat_succ_eq s n)
              _ = Real.rpow (3 : ℝ) (-s) * (Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n) := by
                    ring
  rw [hEq]
  exact hA1.sub hrA

theorem tsum_geometricWeight_one_eq_zero_add_tsum_rpow_neg_s_nat_succ_mul_sub
    {H : ℕ → ℝ} {s : ℝ} (hs : 0 < s)
    (hsum : Summable (fun n : ℕ => geometricWeight s 1 n * H n)) :
    ∑' n : ℕ, geometricWeight s 1 n * H n =
      H 0 +
        ∑' n : ℕ, Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * (H (n + 1) - H n) := by
  let r : ℝ := Real.rpow (3 : ℝ) (-s)
  let A : ℕ → ℝ := fun n => Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n
  have hA : Summable A := summable_rpow_neg_s_nat_mul_of_summable_geometricWeight_one hs hsum
  have hA1 : Summable (fun n : ℕ => A (n + 1)) := (summable_nat_add_iff 1).2 hA
  have hrA : Summable (fun n : ℕ => r * A n) := hA.mul_left r
  have hWeight :
      ∑' n : ℕ, geometricWeight s 1 n * H n =
        geometricDiscount s 1 * ∑' n : ℕ, A n := by
    have hEq :
        (fun n : ℕ => geometricWeight s 1 n * H n) =
          fun n : ℕ => geometricDiscount s 1 * A n := by
      funext n
      rw [geometricWeight_one_eq]
      dsimp [A]
      ring
    rw [hEq, tsum_mul_left]
  have hTail :
      ∑' n : ℕ, A (n + 1) = ∑' n : ℕ, A n - A 0 := by
    have hsplit := hA.sum_add_tsum_nat_add 1
    have hsplit' : A 0 + ∑' n : ℕ, A (n + 1) = ∑' n : ℕ, A n := by
      simpa using hsplit
    linarith
  have hDiff :
      ∑' n : ℕ, Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * (H (n + 1) - H n) =
        ∑' n : ℕ, A (n + 1) - ∑' n : ℕ, r * A n := by
    have hEq :
        (fun n : ℕ => Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * (H (n + 1) - H n)) =
          fun n : ℕ => A (n + 1) - r * A n := by
      funext n
      calc
        Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * (H (n + 1) - H n) =
            Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * H (n + 1) -
              Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * H n := by
                ring
        _ = A (n + 1) - r * A n := by
              dsimp [A, r]
              congr 1
              calc
                Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * H n =
                    (Real.rpow (3 : ℝ) (-s) * Real.rpow (3 : ℝ) (-s * (n : ℝ))) * H n := by
                      exact congrArg (fun x : ℝ => x * H n) (rpow_neg_mul_nat_succ_eq s n)
                _ = Real.rpow (3 : ℝ) (-s) * (Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n) := by
                      ring
    rw [hEq]
    exact (HasSum.sub hA1.hasSum hrA.hasSum).tsum_eq
  have hA0 : A 0 = H 0 := by
    dsimp [A]
    simp
  calc
    ∑' n : ℕ, geometricWeight s 1 n * H n = geometricDiscount s 1 * ∑' n : ℕ, A n := hWeight
    _ = H 0 + (∑' n : ℕ, A (n + 1) - ∑' n : ℕ, r * A n) := by
          rw [geometricDiscount_one_eq, tsum_mul_left, hTail]
          dsimp [r]
          linarith
    _ =
        H 0 +
          ∑' n : ℕ, Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * (H (n + 1) - H n) := by
            rw [hDiff]

theorem tsum_geometricWeight_one_le_of_monotone {H : ℕ → ℝ}
    (hmono : Monotone H) (hnonneg : ∀ n : ℕ, 0 ≤ H n)
    {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (hsum_t : Summable (fun n : ℕ => geometricWeight t 1 n * H n)) :
    ∑' n : ℕ, geometricWeight s 1 n * H n ≤
      ∑' n : ℕ, geometricWeight t 1 n * H n := by
  let C : ℝ := geometricDiscount s 1 / geometricDiscount t 1
  have hs : 0 < s := lt_trans ht hts
  have hdisc_t_pos : 0 < geometricDiscount t 1 := by
    exact geometricDiscount_pos (by simpa using ht)
  have hdisc_s_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs)
  have hsum_s : Summable (fun n : ℕ => geometricWeight s 1 n * H n) := by
    have hscaled : Summable (fun n : ℕ => C * (geometricWeight t 1 n * H n)) := hsum_t.mul_left C
    refine Summable.of_nonneg_of_le ?_ ?_ hscaled
    · intro n
      exact mul_nonneg (geometricWeight_nonneg n (by simpa using hs.le)) (hnonneg n)
    · intro n
      have hpow :
          Real.rpow (3 : ℝ) (-s * (n : ℝ)) ≤ Real.rpow (3 : ℝ) (-t * (n : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ)) ?_
        nlinarith
      calc
        geometricWeight s 1 n * H n
            = geometricDiscount s 1 * (Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n) := by
                rw [geometricWeight_one_eq]
                ring
        _ ≤ geometricDiscount s 1 * (Real.rpow (3 : ℝ) (-t * (n : ℝ)) * H n) := by
              refine mul_le_mul_of_nonneg_left ?_ hdisc_s_pos.le
              exact mul_le_mul_of_nonneg_right hpow (hnonneg n)
        _ = C * (geometricWeight t 1 n * H n) := by
              dsimp [C]
              rw [geometricWeight_one_eq]
              field_simp [hdisc_t_pos.ne']
              simp [mul_comm]
  let deltaS : ℕ → ℝ := fun n =>
    Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) * (H (n + 1) - H n)
  let deltaT : ℕ → ℝ := fun n =>
    Real.rpow (3 : ℝ) (-t * ((n + 1 : ℕ) : ℝ)) * (H (n + 1) - H n)
  have hdeltaT_nonneg : ∀ n : ℕ, 0 ≤ deltaT n := by
    intro n
    dsimp [deltaT]
    refine mul_nonneg ?_ ?_
    · exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    · exact sub_nonneg.mpr (hmono (Nat.le_succ n))
  have hdeltaS_nonneg : ∀ n : ℕ, 0 ≤ deltaS n := by
    intro n
    dsimp [deltaS]
    refine mul_nonneg ?_ ?_
    · exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    · exact sub_nonneg.mpr (hmono (Nat.le_succ n))
  have hdeltaLe : ∀ n : ℕ, deltaS n ≤ deltaT n := by
    intro n
    dsimp [deltaS, deltaT]
    have hpow :
        Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) ≤
          Real.rpow (3 : ℝ) (-t * ((n + 1 : ℕ) : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ)) ?_
      nlinarith
    exact mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr (hmono (Nat.le_succ n)))
  have hdeltaT_summable :
      Summable deltaT := by
    dsimp [deltaT]
    exact summable_rpow_neg_s_nat_succ_mul_sub_of_summable_geometricWeight_one ht hsum_t
  have hdeltaS_summable :
      Summable deltaS := by
    refine Summable.of_nonneg_of_le hdeltaS_nonneg hdeltaLe hdeltaT_summable
  have hdeltaSumLe :
      ∑' n : ℕ, deltaS n ≤ ∑' n : ℕ, deltaT n :=
    Summable.tsum_le_tsum hdeltaLe hdeltaS_summable hdeltaT_summable
  calc
    ∑' n : ℕ, geometricWeight s 1 n * H n =
        H 0 + ∑' n : ℕ, deltaS n := by
          dsimp [deltaS]
          exact tsum_geometricWeight_one_eq_zero_add_tsum_rpow_neg_s_nat_succ_mul_sub hs hsum_s
    _ ≤ H 0 + ∑' n : ℕ, deltaT n := by
          linarith
    _ = ∑' n : ℕ, geometricWeight t 1 n * H n := by
          dsimp [deltaT]
          symm
          exact tsum_geometricWeight_one_eq_zero_add_tsum_rpow_neg_s_nat_succ_mul_sub ht hsum_t

theorem geometricDiscount_eq_mul_one (s q : ℝ) :
    geometricDiscount s q = geometricDiscount (s * q) 1 := by
  unfold geometricDiscount
  congr 2
  ring

theorem geometricWeight_eq_mul_one (s q : ℝ) (n : ℕ) :
    geometricWeight s q n = geometricWeight (s * q) 1 n := by
  unfold geometricWeight
  rw [geometricDiscount_eq_mul_one]
  congr 2
  ring

theorem summable_geometricWeight {s q : ℝ} (hsq : 0 < s * q) :
    Summable (fun n : ℕ => geometricWeight s q n) := by
  simpa [geometricWeight_eq_mul_one, mul_assoc, mul_left_comm, mul_comm] using
    summable_geometricWeight_one (s := s * q) hsq

theorem tsum_geometricWeight_eq_one {s q : ℝ} (hsq : 0 < s * q) :
    ∑' n : ℕ, geometricWeight s q n = 1 := by
  simpa [geometricWeight_eq_mul_one, mul_assoc, mul_left_comm, mul_comm] using
    tsum_geometricWeight_one_eq_one (s := s * q) hsq

theorem geometricWeight_shift {s q : ℝ} (h n : ℕ) :
    geometricWeight s q n =
      Real.rpow (3 : ℝ) (s * q * (h : ℝ)) * geometricWeight s q (n + h) := by
  simpa [geometricWeight_eq_mul_one, mul_assoc, mul_left_comm, mul_comm] using
    (geometricWeight_one_shift (s := s * q) h n)

theorem summable_geometricWeight_mul_of_nonneg_of_le {H : ℕ → ℝ} {s q C : ℝ}
    (hsq : 0 < s * q) (hnonneg : ∀ n : ℕ, 0 ≤ H n) (hbound : ∀ n : ℕ, H n ≤ C) :
    Summable (fun n : ℕ => geometricWeight s q n * H n) := by
  have hC_nonneg : 0 ≤ C := by
    exact le_trans (hnonneg 0) (hbound 0)
  have hscaled : Summable (fun n : ℕ => C * geometricWeight s q n) :=
    (summable_geometricWeight hsq).mul_left C
  refine Summable.of_nonneg_of_le ?_ ?_ hscaled
  · intro n
    exact mul_nonneg (geometricWeight_nonneg n hsq.le) (hnonneg n)
  · intro n
    calc
      geometricWeight s q n * H n ≤ geometricWeight s q n * C := by
        exact mul_le_mul_of_nonneg_left (hbound n) (geometricWeight_nonneg n hsq.le)
      _ = C * geometricWeight s q n := by ring

theorem summable_geometricWeight_of_lt {H : ℕ → ℝ}
    (hnonneg : ∀ n : ℕ, 0 ≤ H n) {q t s : ℝ} (hq : 0 < q) (ht : 0 < t) (hts : t < s)
    (hsum_t : Summable (fun n : ℕ => geometricWeight t q n * H n)) :
    Summable (fun n : ℕ => geometricWeight s q n * H n) := by
  have htq : 0 < t * q := mul_pos ht hq
  have hsq : 0 < s * q := mul_pos (lt_trans ht hts) hq
  have hstq : t * q < s * q := by
    exact mul_lt_mul_of_pos_right hts hq
  simpa [geometricWeight_eq_mul_one, mul_assoc, mul_left_comm, mul_comm] using
    (summable_geometricWeight_one_of_lt hnonneg htq hstq (by
      simpa [geometricWeight_eq_mul_one, mul_assoc, mul_left_comm, mul_comm] using hsum_t))

theorem tsum_geometricWeight_le_of_monotone {H : ℕ → ℝ}
    (hmono : Monotone H) (hnonneg : ∀ n : ℕ, 0 ≤ H n)
    {q t s : ℝ} (hq : 0 < q) (ht : 0 < t) (hts : t < s)
    (hsum_t : Summable (fun n : ℕ => geometricWeight t q n * H n)) :
    ∑' n : ℕ, geometricWeight s q n * H n ≤
      ∑' n : ℕ, geometricWeight t q n * H n := by
  have htq : 0 < t * q := mul_pos ht hq
  have hsq : 0 < s * q := mul_pos (lt_trans ht hts) hq
  have hstq : t * q < s * q := by
    exact mul_lt_mul_of_pos_right hts hq
  simpa [geometricWeight_eq_mul_one, mul_assoc, mul_left_comm, mul_comm] using
    (tsum_geometricWeight_one_le_of_monotone
      (H := H) hmono hnonneg htq hstq (by
        simpa [geometricWeight_eq_mul_one, mul_assoc, mul_left_comm, mul_comm] using hsum_t))

theorem self_le_tsum_geometricWeight_of_monotone {H : ℕ → ℝ}
    (hmono : Monotone H) {s q : ℝ} (hsq : 0 < s * q)
    (hsum : Summable (fun n : ℕ => geometricWeight s q n * H n)) :
    H 0 ≤ ∑' n : ℕ, geometricWeight s q n * H n := by
  have hsum' :
      Summable (fun n : ℕ => geometricWeight (s * q) 1 n * H n) := by
    simpa [geometricWeight_eq_mul_one, mul_assoc, mul_left_comm, mul_comm] using hsum
  have hdecomp :=
    tsum_geometricWeight_one_eq_zero_add_tsum_rpow_neg_s_nat_succ_mul_sub
      (H := H) (s := s * q) hsq hsum'
  have htail_nonneg :
      0 ≤
        ∑' n : ℕ,
          Real.rpow (3 : ℝ) (-(s * q) * ((n + 1 : ℕ) : ℝ)) * (H (n + 1) - H n) := by
    refine tsum_nonneg ?_
    intro n
    refine mul_nonneg ?_ ?_
    · exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    · exact sub_nonneg.mpr (hmono (Nat.le_succ n))
  have hdecomp' :
      ∑' n : ℕ, geometricWeight s q n * H n =
        H 0 +
          ∑' n : ℕ,
            Real.rpow (3 : ℝ) (-(s * q) * ((n + 1 : ℕ) : ℝ)) * (H (n + 1) - H n) := by
    simpa [geometricWeight_eq_mul_one, mul_assoc, mul_left_comm, mul_comm] using hdecomp
  linarith [htail_nonneg]

private theorem rpow_le_rpow_tsum_mul_of_nonneg {f : ℕ → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hf_nonneg : ∀ n, 0 ≤ f n) (hf_sum : Summable f) :
    ∀ n, Real.rpow (f n) p ≤ Real.rpow (∑' k : ℕ, f k) (p - 1) * f n := by
  let S : ℝ := ∑' k : ℕ, f k
  have hterm_le : ∀ n, f n ≤ S := by
    intro n
    have hsingle : f n ≤ ∑ i ∈ Finset.range (n + 1), f i := by
      exact Finset.single_le_sum (fun i _ => hf_nonneg i) (Finset.mem_range.mpr (Nat.lt_succ_self n))
    have hprefix :
        ∑ i ∈ Finset.range (n + 1), f i ≤ S := by
      simpa [S] using hf_sum.sum_le_tsum (Finset.range (n + 1))
        (fun i _ => hf_nonneg i)
    exact hsingle.trans hprefix
  intro n
  have hpow_le :
      Real.rpow (f n) (p - 1) ≤ Real.rpow S (p - 1) := by
    refine Real.rpow_le_rpow (hf_nonneg n) (hterm_le n) ?_
    linarith
  calc
    Real.rpow (f n) p = Real.rpow (f n) ((p - 1) + 1) := by ring_nf
    _ = Real.rpow (f n) (p - 1) * Real.rpow (f n) 1 := by
          exact Real.rpow_add_of_nonneg (hf_nonneg n) (sub_nonneg.mpr hp) zero_le_one
    _ = Real.rpow (f n) (p - 1) * f n := by simp
    _ ≤ Real.rpow S (p - 1) * f n := by
          exact mul_le_mul_of_nonneg_right hpow_le (hf_nonneg n)

theorem summable_rpow_of_nonneg_of_one_le {f : ℕ → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hf_nonneg : ∀ n, 0 ≤ f n) (hf_sum : Summable f) :
    Summable (fun n => Real.rpow (f n) p) := by
  let S : ℝ := ∑' k : ℕ, f k
  have hscaled : Summable (fun n => Real.rpow S (p - 1) * f n) := hf_sum.mul_left _
  refine Summable.of_nonneg_of_le ?_ ?_ hscaled
  · intro n
    exact Real.rpow_nonneg (hf_nonneg n) p
  · exact rpow_le_rpow_tsum_mul_of_nonneg hp hf_nonneg hf_sum

theorem tsum_rpow_le_rpow_tsum_of_nonneg {f : ℕ → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hf_nonneg : ∀ n, 0 ≤ f n) (hf_sum : Summable f) :
    ∑' n, Real.rpow (f n) p ≤ Real.rpow (∑' n, f n) p := by
  let S : ℝ := ∑' n, f n
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg hf_nonneg
  have hrpow_sum : Summable (fun n => Real.rpow (f n) p) :=
    summable_rpow_of_nonneg_of_one_le hp hf_nonneg hf_sum
  have hscaled : Summable (fun n => Real.rpow S (p - 1) * f n) := hf_sum.mul_left _
  have hle :
      ∑' n, Real.rpow (f n) p ≤ ∑' n, Real.rpow S (p - 1) * f n :=
    Summable.tsum_le_tsum (rpow_le_rpow_tsum_mul_of_nonneg hp hf_nonneg hf_sum) hrpow_sum hscaled
  calc
    ∑' n, Real.rpow (f n) p ≤ ∑' n, Real.rpow S (p - 1) * f n := hle
    _ = Real.rpow S (p - 1) * S := by
          simpa [S] using (Summable.tsum_mul_left (Real.rpow S (p - 1)) hf_sum)
    _ = Real.rpow S p := by
          calc
            Real.rpow S (p - 1) * S = Real.rpow S (p - 1) * Real.rpow S 1 := by
              simp
            _ = Real.rpow S ((p - 1) + 1) := by
                  symm
                  exact Real.rpow_add_of_nonneg hS_nonneg (sub_nonneg.mpr hp) zero_le_one
            _ = Real.rpow S p := by ring_nf

@[simp] theorem multiscale_ellipticity_LambdaSq_finite_eq {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (a : CoeffField d) :
    LambdaSq Q s (.finite q) a = LambdaSqFinite Q s q a := rfl

@[simp] theorem multiscale_ellipticity_LambdaSq_infinity_eq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) :
    LambdaSq Q s .infinity a = LambdaSqInfinity Q s a := rfl

@[simp] theorem multiscale_ellipticity_lambdaSq_finite_eq {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (a : CoeffField d) :
    lambdaSq Q s (.finite q) a = lambdaSqFinite Q s q a := rfl

@[simp] theorem multiscale_ellipticity_lambdaSq_infinity_eq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) :
    lambdaSq Q s .infinity a = lambdaSqInfinity Q s a := rfl

@[simp] theorem scaleResponseAtScale_finite_eq {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (p : ℝ) (a : CoeffField d) (a0 : Mat d) :
    scaleResponseAtScale Q k (.finite p) a a0 =
      Real.rpow
        (finsetAverage (descendantsAtScale Q k)
          (fun R => Real.rpow (normalizedBlockResponseMax R a a0) (p / 2)))
        (1 / p) := rfl

@[simp] theorem scaleResponseAtScale_infinity_eq {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (a : CoeffField d) (a0 : Mat d) :
    scaleResponseAtScale Q k .infinity a a0 =
      Real.rpow (maxDescendantNormalizedBlockResponseAtScale Q k a a0) (1 / 2) := rfl


end

end Homogenization
