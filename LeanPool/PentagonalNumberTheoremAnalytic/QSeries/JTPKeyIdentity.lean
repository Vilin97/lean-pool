/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import Mathlib.Tactic.LinearCombination
public import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.EulerIdentities

/-!
# Key identity for the Jacobi triple product

We prove that for ‖q‖ < 1 and all k ≥ 0:

$$S_k(q) := \sum_{m=0}^{\infty} \frac{q^{m(m+k)}}{(q;q)_m (q;q)_{m+k}} = \frac{1}{(q;q)_\infty}$$

The proof uses a recurrence:
  S_k - S_{k+1} = q^{k+1} (S_{k+2} - S_{k+1})

This forces all differences to be zero (since S_k → 1/(q;q)_∞),
so all S_k are equal to 1/(q;q)_∞.
-/

public section

open Finset Filter
open scoped Topology

namespace QSeries

noncomputable section

/-- The key sum S_k(q) = Σ_{m≥0} q^{m(m+k)} / ((q;q)_m (q;q)_{m+k}). -/
@[expose] def keySum (q : ℂ) (k : ℕ) : ℂ :=
  ∑' m : ℕ, q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))

/-- The summand of S_k. -/
@[expose] def keySummand (q : ℂ) (k : ℕ) (m : ℕ) : ℂ :=
  q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))

/-- Unfolds `keySum` as the tsum of `keySummand`. -/
theorem keySum_eq_tsum (q : ℂ) (k : ℕ) :
    keySum q k = ∑' m, keySummand q k m := rfl

/-- A sequence of positive reals converging to a positive limit is bounded below by a
positive constant. -/
private theorem exists_pos_le_of_tendsto {f : ℕ → ℝ} {L : ℝ} (hL : 0 < L)
    (hf : Tendsto f atTop (𝓝 L)) (hpos : ∀ n, 0 < f n) : ∃ C > 0, ∀ n, C ≤ f n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hf.eventually (lt_mem_nhds (half_lt_self hL)))
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  refine ⟨min (L / 2) ((Finset.range (N + 1)).inf' hne f), ?_, fun n => ?_⟩
  · exact lt_min (by linarith) ((Finset.lt_inf'_iff hne).2 fun i _ => hpos i)
  · rcases le_or_gt n N with h | h
    · exact (min_le_right _ _).trans (Finset.inf'_le f (Finset.mem_range.2 (by omega)))
    · exact (min_le_left _ _).trans (hN n h.le).le

/-- The finite q-Pochhammer symbols `(q;q)_n` are bounded away from `0` uniformly in `n`,
since they converge to the nonzero limit `(q;q)_∞`. -/
theorem exists_pos_le_norm_qPochhammer_self {q : ℂ} (hq : ‖q‖ < 1) :
    ∃ C > 0, ∀ n : ℕ, C ≤ ‖qPochhammer q q n‖ :=
  exists_pos_le_of_tendsto (norm_pos_iff.mpr (qPochhammerInf_ne_zero hq hq))
    (tendsto_qPochhammer hq).norm fun n => norm_pos_iff.mpr (qPochhammer_self_ne_zero hq n)

/-- The series defining $S_k(q)$ is summable for $\|q\| < 1$. -/
theorem summable_keySummand {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    Summable (keySummand q k) := by
  obtain ⟨C, hC₀, hC⟩ := exists_pos_le_norm_qPochhammer_self hq
  have hsq : Summable fun m : ℕ => ‖q‖ ^ (m ^ 2) :=
    Summable.comp_injective (summable_geometric_of_lt_one (norm_nonneg q) hq)
      fun a b h => by simpa using h
  refine Summable.of_norm <| (hsq.mul_right (C * C)⁻¹).of_nonneg_of_le
    (fun m => norm_nonneg _) fun m => ?_
  have h1 : ‖q‖ ^ (m * (m + k)) ≤ ‖q‖ ^ (m ^ 2) :=
    pow_le_pow_of_le_one (norm_nonneg q) hq.le (by nlinarith)
  have h2 : C * C ≤ ‖qPochhammer q q m‖ * ‖qPochhammer q q (m + k)‖ :=
    mul_le_mul (hC m) (hC (m + k)) hC₀.le (hC₀.le.trans (hC m))
  rw [keySummand, norm_div, norm_pow, norm_mul, ← div_eq_mul_inv]
  exact div_le_div₀ (by positivity) h1 (by positivity) h2

/-- As $k \to \infty$, $S_k(q)$ converges to $1/(q;q)_\infty$. -/
theorem tendsto_keySum {q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (keySum q) atTop (𝓝 (1 / qPochhammerInf q q)) := by
  obtain ⟨C, hC₀, hC⟩ := exists_pos_le_norm_qPochhammer_self hq
  have hCC : ∀ m k : ℕ, C * C ≤ ‖qPochhammer q q m * qPochhammer q q (m + k)‖ := fun m k => by
    rw [norm_mul]
    exact mul_le_mul (hC m) (hC (m + k)) hC₀.le (hC₀.le.trans (hC m))
  have hCC₀ : (0 : ℝ) < C * C := mul_pos hC₀ hC₀
  have h_m_zero : Tendsto (fun k => 1 / qPochhammer q q k) atTop (𝓝 (1 / qPochhammerInf q q)) :=
    tendsto_const_nhds.div (tendsto_qPochhammer hq) (qPochhammerInf_ne_zero hq hq)
  have h_sum_zero : Tendsto (fun k => ∑' m : ℕ, (if m = 0 then 0 else
      q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k)))) atTop (𝓝 0) := by
    have h_dominated : ∀ m, m ≠ 0 → Tendsto (fun k : ℕ =>
        q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))) atTop (𝓝 0) := by
      intro m hm
      have h_lim : Tendsto (fun k : ℕ => q ^ (m * (m + k))) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp <|
          tendsto_atTop_mono (fun k => by nlinarith [Nat.one_le_iff_ne_zero.mpr hm])
            tendsto_natCast_atTop_atTop
      have h_bnd : Tendsto (fun k : ℕ => ‖q ^ (m * (m + k))‖ / (C * C)) atTop (𝓝 0) := by
        simpa using h_lim.norm.div_const (C * C)
      refine squeeze_zero_norm (fun k => ?_) h_bnd
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hCC₀ (hCC m k)
    have h_dom_conv : Tendsto (fun k => ∑' m : ℕ, (if m = 0 then 0 else
        q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k)))) atTop
        (𝓝 (∑' _ : ℕ, (0 : ℂ))) := by
      refine tendsto_tsum_of_dominated_convergence
        (bound := fun m : ℕ => if m = 0 then 0 else ‖q‖ ^ (m * m) / (C * C)) ?_ ?_ ?_
      · rw [← summable_nat_add_iff 1]
        refine Summable.mul_right _ <| Summable.of_nonneg_of_le (fun n => by positivity)
          (fun n => ?_) <| summable_geometric_of_lt_one (norm_nonneg q) hq
        simpa using pow_le_pow_of_le_one (norm_nonneg q) hq.le (by nlinarith)
      · intro m
        by_cases hm : m = 0
        · simp only [hm]
          exact tendsto_const_nhds
        · simpa only [ite_eq_right hm] using h_dominated m hm
      · refine Filter.Eventually.of_forall fun k m => ?_
        by_cases hm : m = 0
        · simp [hm]
        · simp only [ite_eq_right hm, norm_div]
          refine div_le_div₀ (by positivity) ?_ hCC₀ (hCC m k)
          rw [norm_pow]
          exact pow_le_pow_of_le_one (norm_nonneg q) hq.le (by nlinarith)
    simpa using h_dom_conv
  convert h_m_zero.add h_sum_zero using 2 <;> norm_num [keySum]
  rw [Summable.tsum_eq_add_tsum_ite]
  any_goals exact Nat.zero
  · norm_num [qPochhammer]
  · exact summable_keySummand hq _

/-- For `‖q‖ < 1` and `n ≥ 1` the tail factor `1 - qⁿ` is bounded away from zero,
uniformly in `n`, by the constant `1 - ‖q‖`. -/
theorem one_sub_norm_le_norm_one_sub_pow {q : ℂ} (hq : ‖q‖ < 1) {n : ℕ} (hn : 1 ≤ n) :
    1 - ‖q‖ ≤ ‖1 - q ^ n‖ := by
  refine le_trans ?_ (norm_sub_norm_le (1 : ℂ) (q ^ n))
  have h : ‖q‖ ^ n ≤ ‖q‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg q) hq.le hn
  simp only [norm_one, norm_pow, pow_one] at h ⊢
  linarith

/-- The shifted family `q ^ (m * (m + k)) / ((q;q)_m (q;q)_{m+k+1})` is summable:
it is `keySummand q k` scaled by the uniformly bounded factor `(1 - q ^ (m+k+1))⁻¹`. -/
theorem summable_pow_div_qPochhammer_succ {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    Summable fun m : ℕ =>
      q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k + 1)) := by
  have hpos : (0 : ℝ) < 1 - ‖q‖ := by linarith
  refine Summable.of_norm <|
    ((summable_keySummand hq k).norm.mul_right (1 - ‖q‖)⁻¹).of_nonneg_of_le
      (fun m => norm_nonneg _) fun m => ?_
  rw [qPochhammer_succ, ← mul_assoc, ← pow_succ', div_mul_eq_div_div, norm_div, div_eq_mul_inv,
    keySummand]
  gcongr
  exact one_sub_norm_le_norm_one_sub_pow hq (by omega)

/-- Multiplying the shifted family by the bounded factor `1 - q ^ m` preserves summability. -/
theorem summable_pow_mul_one_sub_pow_div_qPochhammer {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    Summable fun m : ℕ =>
      q ^ (m * (m + k)) * (1 - q ^ m) / (qPochhammer q q m * qPochhammer q q (m + k + 1)) := by
  refine Summable.of_norm <|
    ((summable_pow_div_qPochhammer_succ hq k).norm.mul_right 2).of_nonneg_of_le
      (fun m => norm_nonneg _) fun m => ?_
  rw [← div_mul_eq_mul_div, norm_mul]
  gcongr
  refine le_trans (norm_sub_le _ _) ?_
  have : ‖q‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg q) hq.le
  simp only [norm_one, norm_pow]
  linarith

/-- The recurrence $S_k - S_{k+1} = q^{k+1}(S_{k+2} - S_{k+1})$ satisfied by $S_k(q)$. -/
theorem keySum_sub_keySum_succ {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    keySum q k - keySum q (k + 1) = q ^ (k + 1) * (keySum q (k + 2) - keySum q (k + 1)) := by
  have h_split : ∑' m : ℕ, (q ^ (m * (m + k)) * (1 - q ^ m - q ^ (m + k + 1))) /
      (qPochhammer q q m * qPochhammer q q (m + k + 1)) =
      q ^ (k + 1) * (keySum q (k + 2) - keySum q (k + 1)) := by
    have h_split : ∑' m : ℕ, q ^ (m * (m + k)) * (1 - q ^ m) /
        (qPochhammer q q m * qPochhammer q q (m + k + 1)) =
        ∑' m : ℕ, q ^ ((m + 1) * (m + 1 + k)) /
          (qPochhammer q q m * qPochhammer q q (m + k + 2)) := by
      rw [Summable.tsum_eq_zero_add (summable_pow_mul_one_sub_pow_div_qPochhammer hq k)]
      norm_num [qPochhammer_succ]
      refine tsum_congr fun m => ?_
      have hne : (1 - q ^ (m + 1)) ≠ 0 := sub_ne_zero_of_ne <| Ne.symm <|
        ne_of_apply_ne Norm.norm <| by
          norm_num
          exact ne_of_lt <| pow_lt_one₀ (by positivity) hq (by positivity)
      convert mul_div_mul_right _ _ hne using 1
      first | rfl | ring_nf
      rw [show 1 + m + k = m + k + 1 by ring, qPochhammer_succ]
      ring
    have hsum1 := summable_pow_mul_one_sub_pow_div_qPochhammer hq k
    have hsum2 : Summable fun m : ℕ => -(q ^ (m * (m + k)) * q ^ (m + k + 1)) /
        (qPochhammer q q m * qPochhammer q q (m + k + 1)) := by
      have h : Summable fun m : ℕ =>
          q ^ (m * (m + k + 1)) / (qPochhammer q q m * qPochhammer q q (m + k + 1)) := by
        exact summable_keySummand hq (k + 1)
      (convert h.mul_left (-q ^ (k + 1)) using 2; first | rfl | ring_nf)
    convert congr_arg₂ (· + ·) h_split
      (show ∑' m : ℕ, -(q ^ (m * (m + k)) * q ^ (m + k + 1)) /
          (qPochhammer q q m * qPochhammer q q (m + k + 1)) = -q ^ (k + 1) * keySum q (k + 1)
        from ?_) using 1
    · rw [← Summable.tsum_add hsum1 hsum2]
      congr
      ext m
      ring
    · unfold keySum
      ring_nf
      norm_num [mul_assoc, mul_comm, mul_left_comm, ← tsum_mul_left]
      ring_nf
    · unfold keySum
      norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ← tsum_mul_left]
      exact tsum_congr fun n => by ring_nf
  rw [← h_split, keySum, keySum, ← Summable.tsum_sub]
  · refine tsum_congr fun m => ?_
    rw [div_sub_div, div_eq_div_iff]
    · rw [show m + (k + 1) = m + k + 1 by ring, qPochhammer_succ]
      ring
    · exact mul_ne_zero (mul_ne_zero (qPochhammer_self_ne_zero hq m)
        (qPochhammer_self_ne_zero hq (m + k)))
        (mul_ne_zero (qPochhammer_self_ne_zero hq m) (qPochhammer_self_ne_zero hq (m + (k + 1))))
    · exact mul_ne_zero (qPochhammer_self_ne_zero hq m) (qPochhammer_self_ne_zero hq (m + k + 1))
    · exact mul_ne_zero (qPochhammer_self_ne_zero hq m) (qPochhammer_self_ne_zero hq (m + k))
    · exact mul_ne_zero (qPochhammer_self_ne_zero hq _) (qPochhammer_self_ne_zero hq _)
  · exact summable_keySummand hq k
  · exact summable_keySummand hq (k + 1)

/-- All $S_k(q)$ are equal to $1/(q;q)_\infty$ for $\|q\| < 1$. -/
theorem keySum_eq_one_div_qPochhammerInf_self {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    keySum q k = 1 / qPochhammerInf q q := by
  have h_ind : ∀ k : ℕ, keySum q k - keySum q (k + 1) = 0 := by
    intro k
    have h_induction : ∀ n : ℕ, ‖keySum q k - keySum q (k + 1)‖ ≤
        ‖q‖ ^ (n * (2 * k + n + 1) / 2) * ‖keySum q (k + n) - keySum q (k + n + 1)‖ := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        have h_induction_step : ‖keySum q (k + n) - keySum q (k + n + 1)‖ ≤
            ‖q‖ ^ (k + n + 1) * ‖keySum q (k + n + 1) - keySum q (k + n + 2)‖ := by
          rw [keySum_sub_keySum_succ hq (k + n), norm_mul, norm_pow, norm_sub_rev]
        convert le_trans ih (mul_le_mul_of_nonneg_left h_induction_step <| by positivity) using 1
        all_goals first | rfl | ring_nf
        rw [show (2 + n * 3 + n * k * 2 + n ^ 2 + k * 2) / 2 =
          n + k + (n + n * k * 2 + n ^ 2) / 2 + 1 from
            Nat.div_eq_of_eq_mul_left zero_lt_two <| by
              linarith [Nat.div_mul_cancel (show 2 ∣ n + n * k * 2 + n ^ 2 from
                even_iff_two_dvd.mp <| by simp [parity_simps])]]
        ring
    have h_diff_zero :
        Tendsto (fun n => keySum q (k + n) - keySum q (k + n + 1)) atTop (𝓝 0) := by
      convert Filter.Tendsto.sub
        ((tendsto_keySum hq).comp
          (tendsto_atTop_mono (fun n => Nat.le_add_left _ _) tendsto_id))
        ((tendsto_keySum hq).comp
          (tendsto_atTop_mono (fun n => Nat.le_succ_of_le <| Nat.le_add_left _ _) tendsto_id))
        using 2 <;> try rfl
      norm_num
    have h_exp_zero : Tendsto (fun n => ‖q‖ ^ (n * (2 * k + n + 1) / 2)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).comp <|
        tendsto_atTop_atTop.mpr fun x =>
          ⟨2 * x + 1, fun n hn => Nat.le_div_iff_mul_le zero_lt_two |>.2 <| by nlinarith⟩
    exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto' tendsto_const_nhds
      (by simpa using h_exp_zero.mul h_diff_zero.norm) h_induction)
  have h_const : ∀ n : ℕ, keySum q n = keySum q 0 :=
    fun n => Nat.recOn n rfl fun n ih => by linear_combination ih - h_ind n
  convert tendsto_nhds_unique (tendsto_const_nhds.congr fun n => (h_const n).symm)
    (tendsto_keySum hq) using 1
  exact h_const k

/-- Telescoping: `(q;q)_∞ = (q;q)_n * (q^{n+1};q)_∞`. -/
private lemma qPochhammerInf_eq_qPochhammer_mul {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInf q q = qPochhammer q q n * qPochhammerInf (q * q ^ n) q := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    rw [ih, qPochhammer_succ, mul_assoc]
    congr 1
    rw [qPochhammerInf_eq_one_sub_mul hq]
    ring_nf

/-- `qPochhammerInf (q * q^n) q = (q;q)_∞ / (q;q)_n`. -/
theorem qPochhammerInf_mul_pow_eq_div {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInf (q * q ^ n) q = qPochhammerInf q q / qPochhammer q q n := by
  rw [eq_div_iff (qPochhammer_self_ne_zero hq n), mul_comm]
  exact (qPochhammerInf_eq_qPochhammer_mul hq n).symm

/-- The sum over $m$ of the $z^k$ cross-terms in the JTP double product has sum
$q^{\binom{k}{2}}$. -/
theorem hasSum_pow_choose_two_nonneg {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    HasSum (fun m : ℕ =>
      q ^ (m + k).choose 2 * qPochhammerInf (q * q ^ (m + k)) q *
      (q ^ m.choose 2 * q ^ m / qPochhammer q q m))
      (q ^ k.choose 2) := by
  have h_base : HasSum (fun m : ℕ =>
      q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k)))
      (1 / qPochhammerInf q q) := by
    convert keySum_eq_one_div_qPochhammerInf_self hq k using 1
    exact ⟨fun h => h.tsum_eq, fun h => h ▸ (summable_keySummand hq k).hasSum⟩
  have h_scaled : HasSum (fun m : ℕ => q ^ (k.choose 2 + m * (m + k)) * qPochhammerInf q q /
      (qPochhammer q q (m + k) * qPochhammer q q m)) (q ^ k.choose 2) := by
    convert h_base.mul_left (q ^ k.choose 2 * qPochhammerInf q q) using 1 <;>
      first | rfl | ring_nf
    · ac_rfl
    · rw [mul_assoc, mul_inv_cancel₀ (qPochhammerInf_ne_zero hq hq), mul_one]
  have h_sum : HasSum (fun m : ℕ =>
      q ^ ((m + k).choose 2 + m.choose 2 + m) * qPochhammerInf q q /
        (qPochhammer q q (m + k) * qPochhammer q q m)) (q ^ k.choose 2) := by
    convert h_scaled using 3
    rw [Nat.choose_two_add_choose_two]
  convert h_sum using 2
  push_cast [qPochhammerInf_mul_pow_eq_div hq]
  ring

/-- The sum over $n$ of the $z^{-(l+1)}$ cross-terms in the JTP double product has sum
$q^{\binom{l+2}{2}}$. -/
theorem hasSum_pow_choose_two_neg {q : ℂ} (hq : ‖q‖ < 1) (l : ℕ) :
    HasSum (fun n : ℕ =>
      q ^ n.choose 2 * qPochhammerInf (q * q ^ n) q *
      (q ^ (n + (l + 1)).choose 2 * q ^ (n + (l + 1)) / qPochhammer q q (n + (l + 1))))
      (q ^ (l + 2).choose 2) := by
  have h_simp : HasSum (fun n : ℕ =>
      q ^ (n.choose 2 + (n + (l + 1)).choose 2 + (n + (l + 1))) * qPochhammerInf q q /
        (qPochhammer q q n * qPochhammer q q (n + (l + 1)))) (q ^ (l + 2).choose 2) := by
    convert HasSum.mul_left (q ^ (l + 2).choose 2 * qPochhammerInf q q)
      (summable_keySummand hq (l + 1)).hasSum using 1 <;> try rfl
    · ext n
      rw [keySummand, Nat.choose_two_add_choose_two']
      ring
    · rw [show (∑' n : ℕ, keySummand q (l + 1) n) = 1 / qPochhammerInf q q from ?_]
      · rw [mul_assoc, mul_one_div_cancel (qPochhammerInf_ne_zero hq hq), mul_one]
      · convert keySum_eq_one_div_qPochhammerInf_self hq (l + 1) using 1
        exact (keySum_eq_tsum q (l + 1)).symm
  convert h_simp using 2
  rw [qPochhammerInf_mul_pow_eq_div hq]
  ring_nf

end

end QSeries
