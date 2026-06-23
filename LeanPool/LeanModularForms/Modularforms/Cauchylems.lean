/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import LeanPool.LeanModularForms.Modularforms.IccIcoLems
public import LeanPool.LeanModularForms.Modularforms.RiemannZetalems
public import LeanPool.LeanModularForms.Modularforms.SummableLems

/-! # Cauchylems -/


@[expose] public section


open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma


lemma cc (f : ℤ → ℂ) (hc : CauchySeq fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, f m)
  (hs : ∀ n , f n = f (-n)) :
  Tendsto f atTop (𝓝 0) := by
  have h := cauchySeq_iff_tendsto_dist_atTop_0.mp hc
  simp_rw [cauchySeq_iff_le_tendsto_0] at *
  obtain ⟨g, hg, H, Hg⟩ := hc
  rw [Metric.tendsto_atTop] at *
  simp only [gt_iff_lt, ge_iff_le, dist_zero_right, Real.norm_eq_abs, abs_dist, Prod.forall,
    Prod.exists, Prod.mk_le_mk, and_imp] at *
  intro ε hε
  have hh := Hg (2 * ε) (by linarith)
  obtain ⟨N, hN⟩ := hh
  use N + 1
  intro n hn
  have H3 := H (n).natAbs (n -1).natAbs N ?_ ?_
  · rw [trex f n.natAbs] at H3
    · simp only [dist_eq_norm, Order.add_one_le_iff, Nat.cast_natAbs, Int.cast_abs, Int.cast_eq,
      neg_sub, Int.cast_sub, Int.cast_one, gt_iff_lt] at *
      have h1 : |n| = n := by simp; linarith
      simp_rw [h1] at H3
      have h2 : |n - 1| = n - 1 := by simp; linarith
      simp_rw [h2] at H3
      simp only [neg_sub, add_sub_cancel_right] at H3
      rw [← hs n] at H3
      rw [show f n + f n = 2 * f n by ring] at H3
      simp only [Complex.norm_mul, norm_ofNat] at H3
      have HN := hN N (by rfl)
      have hgn : g N ≤ |g N| := le_abs_self (g N)
      have := le_trans H3 hgn
      have hgnn : 2 * ‖(f n)‖ < 2 * ε := lt_of_le_of_lt this HN
      nlinarith
    omega
  · omega
  omega


lemma sum_Icc_eq_sum_Ico_succ {α : Type*} [AddCommMonoid α] (f : ℤ → α)
    {l u : ℤ} (h : l ≤ u) :
    ∑ m ∈ Finset.Icc l u, f m = (∑ m ∈ Finset.Ico l u, f m) + f u := by
  rw [Finset.Icc_eq_cons_Ico h]
  simp only [Finset.cons_eq_insert, Finset.mem_Ico, lt_self_iff_false, and_false,
    not_false_eq_true, Finset.sum_insert, add_comm]

lemma CauchySeq_Icc_iff_CauchySeq_Ico (f : ℤ → ℂ) (hs : ∀ n, f n = f (-n))
  (hc : CauchySeq (fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, f m) ) :
  CauchySeq (fun N : ℕ => ∑ m ∈ Finset.Ico (-N : ℤ) N, f m) := by
  have h0 := cc f hc hs
  have : CauchySeq fun n: ℕ => f n := by
    apply Filter.Tendsto.cauchySeq (x := 0)
    rw [Metric.tendsto_atTop] at *
    intro ε hε
    obtain ⟨N, hN⟩ := h0 ε hε
    exact ⟨N.natAbs, fun n hn => by
      simp only [gt_iff_lt, ge_iff_le, dist_zero_right] at *
      exact hN n (by omega)⟩
  have h1 := Filter.Tendsto.mul_const 2 h0
  have hff : Tendsto (fun n : ℕ => 2 * ‖f n‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop] at *
    simp only [gt_iff_lt, ge_iff_le, dist_eq_norm, sub_zero, zero_mul, norm_ofNat, norm_mul,
      Real.norm_ofNat, norm_norm] at *
    intro ε hε
    obtain ⟨N, hN⟩ := h1 ε hε
    exact ⟨N.natAbs, fun n hn => by rw [mul_comm]; exact hN n (by omega)⟩
  simp_rw [cauchySeq_iff_le_tendsto_0] at *
  obtain ⟨b, hb, H, hbb⟩ := hc
  obtain ⟨a, ha, H2, haa⟩ := this
  refine ⟨b + a, ?_, ?_, ?_⟩
  · intro n
    simp only [Pi.add_apply]
    apply add_nonneg
    · exact hb n
    apply ha n
  · intro n m N hn hm
    have H3 := H n m N hn hm
    simp only [zero_mul, dist_eq_norm, Pi.add_apply, ge_iff_le] at *
    rw [sum_Icc_eq_sum_Ico_succ _, sum_Icc_eq_sum_Ico_succ _] at H3
    · apply le_trans (norm_le_add_norm_add _ (f n - f m))
      gcongr
      · apply le_trans _ H3
        apply le_of_eq
        congr
        ring
      exact H2 n m N hn hm
    · omega
    omega
  · have HG := Filter.Tendsto.add hbb haa
    rw [add_zero] at HG
    exact HG

theorem extracted_2 (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, 1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ),
        ((b : ℂ) * ↑z + ↑x + 1)⁻¹ * (((b : ℂ) * ↑z + ↑x) ^ 2)⁻¹)
  have hA:= (G2_prod_summable1 z b).hasSum
  have ht := hA.comp verga
  simp only [one_div, mul_inv_rev] at *
  apply ht

theorem extracted_2_δ (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) + δ b n) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ),
        (((b : ℂ) * ↑z + ↑x + 1)⁻¹ * (((b : ℂ) * ↑z + ↑x) ^ 2)⁻¹ + δ b x))
  have hA:= (G2_prod_summable1_δ z b).hasSum
  have ht := hA.comp verga
  simp only [one_div, mul_inv_rev] at *
  apply ht


theorem telescope_aux (z : ℍ) (m : ℤ) (b : ℕ) :
  ∑ n ∈ Finset.Ico (-b : ℤ) b, (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1)) =
    1 / (↑m * ↑z - ↑b) - 1 / (↑m * ↑z + ↑b) := by
  induction b with
  | zero => aesop
  | succ b ihb =>
    simp only [Nat.cast_add, Nat.cast_one, one_div, Finset.sum_sub_distrib] at *
    rw [fsb, Finset.sum_union, Finset.sum_union, Finset.sum_pair, Finset.sum_pair,add_sub_add_comm,
      ihb]
    · simp only [neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg,
                 Int.cast_one, Int.cast_natCast]
      ring
    · omega
    · omega
    · simp only [neg_add_rev, Int.reduceNeg, Finset.disjoint_insert_right, Finset.mem_Ico,
      le_add_iff_nonneg_left, Left.nonneg_neg_iff, Int.reduceLE, add_neg_lt_iff_lt_add, false_and,
      not_false_eq_true, Finset.disjoint_singleton_right, neg_le_self_iff, Nat.cast_nonneg,
      lt_self_iff_false, and_false, and_self]
    · simp only [neg_add_rev, Int.reduceNeg, Finset.disjoint_insert_right, Finset.mem_Ico,
      le_add_iff_nonneg_left, Left.nonneg_neg_iff, Int.reduceLE, add_neg_lt_iff_lt_add, false_and,
      not_false_eq_true, Finset.disjoint_singleton_right, neg_le_self_iff, Nat.cast_nonneg,
      lt_self_iff_false, and_false, and_self]

theorem extracted_3 (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1)) := by
  conv => enter [1]; intro d; rw [telescope_aux]
  apply Filter.Tendsto.cauchySeq (x := 0)
  have h1 : Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z - ↑d)) atTop (𝓝 0) := by
    have := tendsto_zero_inv_linear z (-b)
    rw [← tendsto_const_smul_iff₀ (c := (-1 : ℂ))] at this
    · simp only [Int.cast_neg, neg_mul, one_div, smul_eq_mul, one_mul, mul_zero] at *
      apply this.congr
      intro x
      rw [neg_inv]
      congr
      ring
    · norm_cast
  have h2 : Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z + ↑d)) atTop (𝓝 0) :=
    tendsto_zero_inv_linear z b
  simpa using Filter.Tendsto.sub h1 h2


theorem extracted_4 (z : ℍ) (b : ℤ) :
  CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z + ↑n) ^ 2 ) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ), ((((b : ℂ) * ↑z + ↑x) ^ 2)⁻¹))
  have hA:= (G2_summable_aux b z 2 (by norm_num)).hasSum
  have ht := hA.comp verga
  simp only [one_div] at *
  apply ht

theorem extracted_5 (z : ℍ) (b : ℤ) :
  CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z - ↑n) ^ 2 ) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ), ((((b : ℂ) * ↑z - ↑x) ^ 2)⁻¹))
  have hA := (summable_neg _ (G2_summable_aux b z 2 (by norm_num))).hasSum
  have ht := hA.comp verga
  simp only [Int.cast_neg, one_div] at *
  have := ht.congr' (f₂ := fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z - ↑n) ^ 2
    )) ?_
  · simp only [one_div] at this
    apply this
  apply Filter.Eventually.of_forall
  intro N
  simp
  congr

lemma CauchySeq.congr (f g : ℕ → ℂ) (hf : f = g) (hh : CauchySeq g) : CauchySeq f := hf ▸ hh

lemma cauchy_seq_mul_const (f : ℕ → ℂ) (c : ℂ) (hc : c ≠ 0) :
  CauchySeq f → CauchySeq (c • f) := by
  intro hf
  rw [Metric.cauchySeq_iff'] at *
  simp only [ne_eq, gt_iff_lt, ge_iff_le, Pi.smul_apply, smul_eq_mul] at *
  intro ε hε
  have hC : 0 < ‖c‖ := by simp [ne_eq, hc, not_false_eq_true]
  obtain ⟨N, hN⟩ := hf (ε / ‖c‖) (by rw [lt_div_iff₀' hC]; simp [hε])
  exact ⟨N, fun n hn => by
    have h1 := hN n hn
    simp only [dist_eq_norm, gt_iff_lt] at *
    rw [← mul_sub]
    simp only [Complex.norm_mul]
    rw [lt_div_iff₀' (by simp [hc])] at h1
    exact h1⟩


lemma auxer (a c : ℂ) : a + 2*2*c - 2*c = a + 2*c := by ring

/-- The summand appearing in the Eisenstein-type series used in the Cauchy lemmas. -/
noncomputable def summableTerm (z : ℍ) : ℤ → ℂ :=
  (fun m : ℤ => (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))

lemma term_evem (z : ℍ) (m : ℤ) : summableTerm z m = summableTerm z (-m) := by
  simp only [summableTerm, one_div, Int.cast_neg, neg_mul]
  nth_rw 1 [int_sum_neg]
  congr
  funext m
  simp
  ring

lemma t8 (z : ℍ) :
  (fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2))) =
  (fun _ : ℕ => 2*((riemannZeta 2))) +
  (fun N : ℕ => ∑ m ∈ Finset.range (N), 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n)) := by
  funext m
  simp only [one_div, neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one,
    Nat.cast_one, div_one, pow_one, Pi.add_apply]
  rw [Icc_sum_even]
  · simp only [Int.cast_natCast, Int.cast_zero, zero_mul, zero_add]
    rw [ zeta_two_eqn]
    nth_rw 2 [add_comm]
    have := sum_range_zero (fun m => (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2))) m
    simp only [Int.cast_natCast, one_div, Int.cast_zero, zero_mul, zero_add, Int.cast_add,
      Int.cast_one] at this
    rw [this, zeta_two_eqn, add_comm, mul_add, ← mul_assoc, auxer]
    congr
    rw [Finset.mul_sum]
    congr
    ext d
    let Z : ℍ := ⟨(d +1)* z, by simp only [mul_im, add_re, natCast_re, one_re, coe_im, add_im,
      natCast_im, one_im, add_zero, coe_re, zero_mul]; exact mul_pos (by linarith) z.2⟩
    have := q_exp_iden 2 (by norm_num) (z := Z)
    simp only [one_div, neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one,
      Nat.factorial_one, Nat.cast_one, div_one, pow_one, Z] at *
    rw [this]
    ring_nf
    congr
    ext r
    congr 1
    ring_nf
  · intro n
    have := term_evem z n
    simp only [summableTerm, one_div, Int.cast_neg, neg_mul] at *
    exact this

theorem G2_c_tendsto (z : ℍ) :
  Tendsto
    (fun N ↦
      ∑ x ∈ Finset.range N,
        2 * (2 * ↑π * Complex.I) ^ 2 * ∑' (n : ℕ+), ↑↑n * cexp (2 * ↑π * Complex.I * (↑x + 1) * ↑z *
          ↑↑n))
    atTop (𝓝 (-8 * ↑π ^ 2 * ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (2 * ↑π * Complex.I * ↑↑n * ↑z))) := by
    rw [← t9]
    have hf : Summable fun m : ℕ => ( 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
        ∑' n : ℕ+, n ^ ((2 - 1)) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n)) := by
        conv =>
          enter [1]
          ext m
          rw [show (m : ℂ) + 1 = (((m + 1) : ℕ) : ℂ) by simp]
        have := nat_pos_tsum2' (f := fun m : ℕ => ( 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
        ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * (m) * z * n)) )
        rw [← this]
        have := (a4 2 z).prod_symm.prod
        apply Summable.mul_left
        apply this.congr
        intro b
        congr
    have := hf.hasSum
    have V := this.comp tendsto_finset_range
    simp only [neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one,
      Nat.cast_one, div_one, pow_one] at *
    apply V

lemma G2_cauchy (z : ℍ) :
    CauchySeq (fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))
    := by
  rw [t8]
  simp only [neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one, Nat.cast_one,
    div_one, pow_one]
  apply CauchySeq.const_add
  apply Filter.Tendsto.cauchySeq (x := -
    8 * π ^ 2 * ∑' (n : ℕ+), (σ 1 n) * cexp (2 * π * Complex.I * n * z))
  apply G2_c_tendsto z
