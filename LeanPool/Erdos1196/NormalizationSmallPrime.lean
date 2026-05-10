/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc.
-/
import LeanPool.Erdos1196.NormalizationCore
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Small-prime bounds for the normalization constant

This file isolates the contribution to `B_x` coming from divisors `q < Y`.
Its main theorem shows that this part is summable and contributes only `O(1 / log x)` for fixed
`Y`.

## Main statements

* `summable_normalizationSmallPrimePart_and_tsum_le`
-/

open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

/-- The natural-number kernel in the small-prime tail. -/
noncomputable def smallPrimeTailTerm (q m : ℕ) : ℝ :=
  1 / ((m : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)

/-- The corresponding real-variable kernel used for integral comparison. -/
noncomputable def smallPrimeKernel (q : ℕ) (t : ℝ) : ℝ :=
  1 / (t * (Real.log (t * q)) ^ 2)

/-- The natural small-prime tail summand is always nonnegative. -/
private lemma smallPrimeTailTerm_nonneg (q m : ℕ) : 0 ≤ smallPrimeTailTerm q m := by
  dsimp [smallPrimeTailTerm]
  positivity

/-- The real kernel is nonnegative once `t q > 1`. -/
private lemma smallPrimeKernel_nonneg {q : ℕ} {t : ℝ} (htq : 1 < t * q) :
    0 ≤ smallPrimeKernel q t := by
  have ht : 0 < t := by
    have hq : (0 : ℝ) ≤ q := by positivity
    nlinarith
  have hlog : 0 < Real.log (t * q) := Real.log_pos htq
  dsimp [smallPrimeKernel]
  positivity

/-- The real kernel is antitone on the tail where the logarithm is positive. -/
private lemma smallPrimeKernel_antitoneOn {q : ℕ} (hq : 0 < q) {a : ℝ} (ha : 1 < a * q) :
    AntitoneOn (smallPrimeKernel q) (Set.Ici a) := by
  intro s hs t ht hst
  have hs' : a ≤ s := hs
  have ht' : a ≤ t := ht
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have has : a * q ≤ s * q := by
    gcongr
  have hat : a * q ≤ t * q := by
    gcongr
  have hsq_gt_one : 1 < s * q := lt_of_lt_of_le ha has
  have htq_gt_one : 1 < t * q := lt_of_lt_of_le ha hat
  have htpos : 0 < t := by nlinarith
  have hmul : s * q ≤ t * q := by gcongr
  have hlog_le : Real.log (s * q) ≤ Real.log (t * q) := by
    exact Real.log_le_log (by positivity) hmul
  have hlog_sq_le : (Real.log (s * q)) ^ 2 ≤ (Real.log (t * q)) ^ 2 := by
    nlinarith [hlog_le, Real.log_pos hsq_gt_one, Real.log_pos htq_gt_one]
  have hden_le : s * (Real.log (s * q)) ^ 2 ≤ t * (Real.log (t * q)) ^ 2 := by
    exact mul_le_mul hst hlog_sq_le (sq_nonneg _) (le_of_lt htpos)
  have hsden_pos : 0 < s * (Real.log (s * q)) ^ 2 := by
    have hspos : 0 < s := by nlinarith
    have hslogpos : 0 < Real.log (s * q) := Real.log_pos hsq_gt_one
    positivity
  exact one_div_le_one_div_of_le hsden_pos hden_le

/-- The shifted kernel tail is summable, and its total mass is bounded by the corresponding
logarithmic integral at the starting point. -/
private lemma summable_smallPrimeKernel_shift_and_tsum_le {q N : ℕ} (hq : 0 < q)
    (hNq : 1 < (N : ℝ) * q) :
    Summable (fun n : ℕ => smallPrimeKernel q (N + n + 1)) ∧
      ∑' n : ℕ, smallPrimeKernel q (N + n + 1) ≤ 1 / Real.log ((N : ℝ) * q) := by
  let g : ℕ → ℝ := fun n => smallPrimeKernel q (N + n + 1)
  have hkernel_eq :
      smallPrimeKernel q = fun t : ℝ => t⁻¹ * (Real.log (t * q) ^ 2)⁻¹ := by
    funext t
    simp [smallPrimeKernel, div_eq_mul_inv, mul_left_comm, mul_comm]
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    have hmul : (N : ℝ) * q ≤ (((N + n + 1 : ℕ) : ℝ) * q) := by
      gcongr
      exact_mod_cast Nat.le_add_right N (n + 1)
    have hgt : 1 < (((N + n + 1 : ℕ) : ℝ) * q) := lt_of_lt_of_le hNq hmul
    exact smallPrimeKernel_nonneg (by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hgt)
  have hbound : ∀ n, (∑ i ∈ Finset.range n, g i) ≤ 1 / Real.log ((N : ℝ) * q) := by
    intro n
    have hanti : AntitoneOn (smallPrimeKernel q) (Set.Icc (N : ℝ) (N + n)) :=
      (smallPrimeKernel_antitoneOn hq hNq).mono Set.Icc_subset_Ici_self
    have hIoi : MeasureTheory.IntegrableOn (smallPrimeKernel q) (Set.Ioi (N : ℝ)) := by
      rw [hkernel_eq]
      simpa [div_eq_mul_inv, mul_left_comm, mul_comm] using
        (integrableOn_Ioi_inv_log_sq (c := (q : ℝ)) (y := (N : ℝ))
          (by exact_mod_cast hq) (by simpa [mul_comm] using hNq))
    have hnonneg :
        0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (N : ℝ))] smallPrimeKernel q := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hxN : (N : ℝ) < x := hx
      have hmul : (N : ℝ) * q < x * q := by
        gcongr
      exact smallPrimeKernel_nonneg (lt_trans hNq hmul)
    have hNn : (N : ℝ) ≤ (N : ℝ) + n := by
      exact_mod_cast Nat.le_add_right N n
    calc
      ∑ i ∈ Finset.range n, g i
        = ∑ i ∈ Finset.range n, smallPrimeKernel q (N + (i + 1 : ℕ)) := by
            grind only
      _ ≤ ∫ x in (N : ℝ)..N + n, smallPrimeKernel q x := by
            exact AntitoneOn.sum_le_integral hanti
      _ ≤ ∫ x in Set.Ioi (N : ℝ), smallPrimeKernel q x := by
            rw [intervalIntegral.integral_of_le hNn]
            exact MeasureTheory.integral_mono_measure
              (MeasureTheory.Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl) hnonneg hIoi
      _ = 1 / Real.log ((N : ℝ) * q) := by
            rw [hkernel_eq]
            simpa [div_eq_mul_inv, mul_left_comm, mul_comm] using
              (integral_Ioi_inv_log_sq (c := (q : ℝ)) (y := (N : ℝ))
                (by exact_mod_cast hq) (by simpa [mul_comm] using hNq))
  refine ⟨summable_of_sum_range_le (f := g) (c := 1 / Real.log ((N : ℝ) * q)) hg_nonneg hbound, ?_⟩
  exact Real.tsum_le_of_sum_range_le hg_nonneg hbound

/-- Splitting the first active index from the small-prime prefix rewrites it as a head term plus
the shifted kernel tail. -/
private lemma sum_range_smallPrimeTail_eq_head_add {q M N : ℕ} (hMN : M < N) :
    ∑ m ∈ Finset.range N, (if M ≤ m then smallPrimeTailTerm q m else 0) =
      smallPrimeTailTerm q M +
        ∑ n ∈ Finset.range (N - (M + 1)), smallPrimeKernel q (M + n + 1) := by
  have hdecomp :
      ∑ m ∈ Finset.range N, (if M ≤ m then smallPrimeTailTerm q m else 0) =
        smallPrimeTailTerm q M + ∑ m ∈ Finset.Ico (M + 1) N, smallPrimeTailTerm q m := by
    have hsplit :
        ∑ m ∈ Finset.range N, (if M ≤ m then smallPrimeTailTerm q m else 0) =
          (∑ m ∈ Finset.range (M + 1), (if M ≤ m then smallPrimeTailTerm q m else 0)) +
            ∑ m ∈ Finset.Ico (M + 1) N, (if M ≤ m then smallPrimeTailTerm q m else 0) := by
      symm
      exact Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hMN)
    rw [hsplit, Finset.sum_range_succ]
    have hzero : ∑ m ∈ Finset.range M, (if M ≤ m then smallPrimeTailTerm q m else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      grind only [= Finset.mem_range]
    have hIco :
        ∑ m ∈ Finset.Ico (M + 1) N, (if M ≤ m then smallPrimeTailTerm q m else 0) =
          ∑ m ∈ Finset.Ico (M + 1) N, smallPrimeTailTerm q m := by
      refine Finset.sum_congr rfl ?_
      grind only [= Finset.mem_Ico]
    simp_all
  have hreindex :
      ∑ m ∈ Finset.Ico (M + 1) N, smallPrimeTailTerm q m =
        ∑ n ∈ Finset.range (N - (M + 1)), smallPrimeKernel q (M + n + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [smallPrimeTailTerm, smallPrimeKernel, Nat.cast_add, Nat.cast_one,
      add_assoc, add_left_comm, add_comm, mul_add, mul_add, mul_comm]
  rw [hdecomp, hreindex]

/--
Every finite prefix of the small-prime tail is bounded by `2 / log x` once `x ≥ 3`. This is the
monotone integral comparison specialized to the exact cutoff `x ⌈/⌉ q`.
-/
lemma sum_range_smallPrimeTail_le_two_inv_log {x q N : ℕ} (hx : 3 ≤ x) (hq : 0 < q) :
    ∑ m ∈ Finset.range N, (if x ⌈/⌉ q ≤ m then smallPrimeTailTerm q m else 0) ≤
      2 / Real.log (x : ℝ) := by
  let M := x ⌈/⌉ q
  have hxq : x ≤ q * M := by
    simpa [M, Nat.mul_comm] using le_smul_ceilDiv hq
  have hx_log_pos : 0 < Real.log (x : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hx))
  have hMq_ge_x : (x : ℝ) ≤ (M : ℝ) * q := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hxq)
  have hMq_gt_one : 1 < (M : ℝ) * q := by
    have hx_one : (1 : ℝ) < x := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hx)
    exact lt_of_lt_of_le hx_one hMq_ge_x
  have hlog_mono : Real.log (x : ℝ) ≤ Real.log ((M : ℝ) * q) := by
    exact Real.log_le_log (by positivity) hMq_ge_x
  have htail := summable_smallPrimeKernel_shift_and_tsum_le (q := q) (N := M) hq hMq_gt_one
  have hkernel_nonneg : ∀ n : ℕ, 0 ≤ smallPrimeKernel q (M + n + 1) := by
    intro n
    have hmul :
        (M : ℝ) * q ≤ (((M + n + 1 : ℕ) : ℝ) * q) := by
      gcongr
      exact_mod_cast Nat.le_add_right M (n + 1)
    have hgt : 1 < (((M + n + 1 : ℕ) : ℝ) * q) := lt_of_lt_of_le hMq_gt_one hmul
    exact smallPrimeKernel_nonneg (by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hgt)
  by_cases hMN : M < N
  · have hhead :
        smallPrimeTailTerm q M ≤ 1 / Real.log (x : ℝ) := by
      have hMpos : 0 < M := by
        by_contra hMpos
        have hM0 : M = 0 := Nat.eq_zero_of_not_pos hMpos
        rw [hM0, Nat.mul_zero] at hxq
        omega
      have hlogMq_ge_one : 1 ≤ Real.log ((M : ℝ) * q) := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) <|
          le_trans Real.exp_one_lt_three.le <| le_trans (by exact_mod_cast hx) hMq_ge_x
      have hden :
          Real.log (x : ℝ) ≤ (M : ℝ) * (Real.log ((M : ℝ) * q)) ^ 2 := by
        have hM_ge_one : (1 : ℝ) ≤ M := by exact_mod_cast Nat.succ_le_of_lt hMpos
        nlinarith
      dsimp [smallPrimeTailTerm, M]
      simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using
        (one_div_le_one_div_of_le hx_log_pos hden)
    have hshift_le :
        ∑' n : ℕ, smallPrimeKernel q (M + n + 1) ≤ 1 / Real.log (x : ℝ) := by
      exact htail.2.trans <| one_div_le_one_div_of_le hx_log_pos hlog_mono
    have hprefix :
        ∑ m ∈ Finset.range N, (if M ≤ m then smallPrimeTailTerm q m else 0) ≤
          smallPrimeTailTerm q M + ∑' n : ℕ, smallPrimeKernel q (M + n + 1) := by
      calc
        ∑ m ∈ Finset.range N, (if M ≤ m then smallPrimeTailTerm q m else 0)
          = smallPrimeTailTerm q M +
              ∑ n ∈ Finset.range (N - (M + 1)), smallPrimeKernel q (M + n + 1) := by
                exact sum_range_smallPrimeTail_eq_head_add hMN
        _ ≤ smallPrimeTailTerm q M + ∑' n : ℕ, smallPrimeKernel q (M + n + 1) := by
              gcongr
              exact htail.1.sum_le_tsum _ (fun n _ => hkernel_nonneg n)
    calc
      ∑ m ∈ Finset.range N, (if x ⌈/⌉ q ≤ m then smallPrimeTailTerm q m else 0)
        ≤ smallPrimeTailTerm q M + ∑' n : ℕ, smallPrimeKernel q (M + n + 1) := by
            simpa [M] using hprefix
      _ ≤ 1 / Real.log (x : ℝ) + 1 / Real.log (x : ℝ) := by
            gcongr
      _ = 2 / Real.log (x : ℝ) := by ring
  · have hzero :
        ∑ m ∈ Finset.range N, (if x ⌈/⌉ q ≤ m then smallPrimeTailTerm q m else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      grind only [= Finset.mem_range]
    simpa [hzero] using (show 0 ≤ 2 / Real.log (x : ℝ) by positivity)

/-- The `q`-th inner row in the small-prime decomposition is bounded by the corresponding
coefficient times `2 / log x`, and vanishes outside `q ∈ Ico 1 Y`. -/
private lemma sum_range_smallPrimeRow_le {x q N Y : ℕ} (hx : 3 ≤ x) :
    let coeff : ℝ := Λ q / (q : ℝ)
    ∑ m ∈ Finset.range N,
      (if 0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m then
        coeff * smallPrimeTailTerm q m
      else 0) ≤
      if 1 ≤ q ∧ q < Y then coeff * (2 / Real.log (x : ℝ)) else 0 := by
  let coeff : ℝ := Λ q / (q : ℝ)
  by_cases hq : 1 ≤ q ∧ q < Y
  · rcases hq with ⟨hq1, hqY⟩
    have hqpos : 0 < q := Nat.succ_le_iff.mp hq1
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    calc
      ∑ m ∈ Finset.range N,
          (if 0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m then
            coeff * smallPrimeTailTerm q m
          else 0)
        ≤ ∑ m ∈ Finset.range N, coeff * (if x ⌈/⌉ q ≤ m then smallPrimeTailTerm q m else 0) := by
            refine Finset.sum_le_sum ?_
            intro m hm
            by_cases hmcut : x ⌈/⌉ q ≤ m <;> by_cases hbase : 0 < m ∧ q * m < N
            · simp [coeff, hqpos, hqY, hmcut, hbase]
            · simpa [coeff, hqpos, hqY, hmcut, hbase] using
                mul_nonneg hcoeff_nonneg (smallPrimeTailTerm_nonneg q m)
            · simp [coeff, hmcut]
            · simp [coeff, hmcut]
      _ = coeff * ∑ m ∈ Finset.range N, (if x ⌈/⌉ q ≤ m then smallPrimeTailTerm q m else 0) := by
            rw [Finset.mul_sum]
      _ ≤ coeff * (2 / Real.log (x : ℝ)) := by
            exact mul_le_mul_of_nonneg_left
              (sum_range_smallPrimeTail_le_two_inv_log (x := x) (q := q) (N := N) hx hqpos)
              hcoeff_nonneg
      _ = if 1 ≤ q ∧ q < Y then coeff * (2 / Real.log (x : ℝ)) else 0 := by
            simp [hq1, hqY]
  · have hzero :
        ∑ m ∈ Finset.range N,
          (if 0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m then
            coeff * smallPrimeTailTerm q m
          else 0) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro m hm
            have hcond :
                ¬ (0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m) := by
                  grind only [Nat.succ_le_iff]
            simp [hcond]
    simp [coeff, hzero, hq]

/--
For `x ≥ 3`, the small-prime contribution to `B_x` is summable, and its total mass is bounded by
an explicit `O(1 / log x)` term depending only on the fixed cutoff `Y`.
-/
lemma summable_normalizationSmallPrimePart_and_tsum_le {x Y : ℕ} (hx : 3 ≤ x) :
    Summable (fun n : ℕ => normalizationSmallPrimePart x Y n) ∧
      ∑' n : ℕ, normalizationSmallPrimePart x Y n ≤
        (2 * ∑ q ∈ Finset.Ico 1 Y, Λ q / (q : ℝ)) / Real.log (x : ℝ) := by
  let coeff : ℕ → ℝ := fun q => Λ q / (q : ℝ)
  have hcoeff_nonneg : ∀ q, 0 ≤ coeff q := by
    intro q
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hpart_nonneg : ∀ n : ℕ, 0 ≤ normalizationSmallPrimePart x Y n := by
    intro n
    by_cases hn : x ≤ n <;> simp [normalizationSmallPrimePart, hn, smallPrimeEntryWeight_nonneg]
  have hprefix :
      ∀ N : ℕ,
        ∑ n ∈ Finset.range N, normalizationSmallPrimePart x Y n ≤
          (2 * ∑ q ∈ Finset.Ico 1 Y, coeff q) / Real.log (x : ℝ) := by
    intro N
    calc
      ∑ n ∈ Finset.range N, normalizationSmallPrimePart x Y n
        = ∑ q ∈ Finset.range N, ∑ m ∈ Finset.range N,
            if 0 < q ∧ 0 < m ∧ q * m < N ∧ q < Y ∧ x ⌈/⌉ q ≤ m then
              coeff q * smallPrimeTailTerm q m
            else 0 := by
              simpa [coeff, smallPrimeTailTerm] using sum_range_normalizationSmallPrimePart_eq N x Y
      _ ≤ ∑ q ∈ Finset.range N,
            if 1 ≤ q ∧ q < Y then coeff q * (2 / Real.log (x : ℝ)) else 0 := by
              refine Finset.sum_le_sum ?_
              intro q _
              simpa [coeff] using
                (sum_range_smallPrimeRow_le (x := x) (q := q) (N := N) (Y := Y) hx)
      _ = ∑ q ∈ (Finset.range N).filter (fun q => 1 ≤ q ∧ q < Y),
            coeff q * (2 / Real.log (x : ℝ)) := by
              rw [← Finset.sum_filter]
      _ ≤ ∑ q ∈ Finset.Ico 1 Y, coeff q * (2 / Real.log (x : ℝ)) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro q hq
                exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hq).2
              · intro q hqIco hqnot
                exact mul_nonneg (hcoeff_nonneg q) (by positivity)
      _ = (2 * ∑ q ∈ Finset.Ico 1 Y, coeff q) / Real.log (x : ℝ) := by
              rw [← Finset.sum_mul]
              ring
  refine ⟨?_, ?_⟩
  · exact summable_of_sum_range_le
      (f := fun n : ℕ => normalizationSmallPrimePart x Y n)
      (c := (2 * ∑ q ∈ Finset.Ico 1 Y, coeff q) / Real.log (x : ℝ)) hpart_nonneg hprefix
  · exact Real.tsum_le_of_sum_range_le (hf := hpart_nonneg) (h := hprefix)
end PrimitiveSetsAboveX
