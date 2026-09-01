/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Clemens Posch
-/
import LeanPool.KahnKalai.Covering
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Tran–Vu Remark 2.5: binomial mixture of level fractions plus a `2^{-X}` Markov
tail, yielding Park–Pham from the covering theorem.
-/

open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable section

/-- The explicit constant in the formalized Park–Pham threshold bound. -/
def parkPhamK : ℝ := 100000

lemma parkPhamK_pos : 0 < parkPhamK := by
  simp [parkPhamK]

lemma parkPhamK_ge_two : (2 : ℝ) ≤ parkPhamK := by
  simp [parkPhamK]
  norm_num

lemma logb_two_ell_ge_one {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (1 : ℝ) ≤ Real.logb 2 (ℓ : ℝ) := by
  have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hself : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
  have hle : Real.logb 2 (2 : ℝ) ≤ Real.logb 2 (ℓ : ℝ) :=
    (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) (by norm_num)
      (by positivity)).mpr h2
  simpa [hself] using hle

lemma ell_add_one_le_sq {ℓ : ℕ} (hℓ : 2 ≤ ℓ) : ℓ + 1 ≤ ℓ ^ 2 := by
  have h1 : 1 ≤ ℓ := le_trans (Nat.le_succ 1) hℓ
  calc
    ℓ + 1 ≤ ℓ + ℓ := Nat.add_le_add_left h1 _
    _ = 2 * ℓ := by ring
    _ ≤ ℓ * ℓ := Nat.mul_le_mul_right ℓ hℓ
    _ = ℓ ^ 2 := (Nat.pow_two ℓ).symm

lemma logb_ell_add_one_le_two {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    Real.logb 2 (ℓ + 1 : ℝ) ≤ 2 * Real.logb 2 (ℓ : ℝ) := by
  have hx : 0 < (ℓ + 1 : ℝ) := by exact_mod_cast Nat.succ_pos ℓ
  have hy : 0 < (ℓ : ℝ) ^ 2 := by positivity
  have hle : (ℓ + 1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by exact_mod_cast (ell_add_one_le_sq hℓ)
  have hlog : Real.logb 2 (ℓ + 1 : ℝ) ≤ Real.logb 2 ((ℓ : ℝ) ^ 2) :=
    (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) hx hy).mpr hle
  have hpow : Real.logb 2 ((ℓ : ℝ) ^ 2) = 2 * Real.logb 2 (ℓ : ℝ) := by
    simpa [pow_two] using Real.logb_pow (2 : ℝ) (ℓ : ℝ) 2
  rwa [hpow] at hlog

lemma logb_min_add_one_le {ℓ N : ℕ} (hℓ : 2 ≤ ℓ) :
    Real.logb 2 ((min ℓ N) + 1 : ℝ) ≤ 2 * Real.logb 2 (ℓ : ℝ) := by
  have hle : ((min ℓ N) + 1 : ℝ) ≤ (ℓ + 1 : ℝ) := by
    exact_mod_cast Nat.add_le_add_right (min_le_left ℓ N) 1
  have hx : 0 < ((min ℓ N) + 1 : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hy : 0 < (ℓ + 1 : ℝ) := by exact_mod_cast Nat.succ_pos ℓ
  have := (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) hx hy).mpr hle
  exact this.trans (logb_ell_add_one_le_two hℓ)

lemma coveringLevel_cast_le (p : ℝ) (N ℓ : ℕ) (hp0 : 0 ≤ p) :
    (coveringLevel p N ℓ : ℝ)
      ≤ coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) :=
  Nat.floor_le (coveringLevel_nonneg p N ℓ hp0)

omit [DecidableEq α] in
lemma IsBounded.min_card {F : Finset (Finset α)} {ℓ : ℕ} (hb : IsBounded F ℓ) :
    IsBounded F (min ℓ (Fintype.card α)) :=
  fun S hS => le_min (hb S hS) (card_le_univ S)

/-- Binomial point mass `C(N,k) p^k (1-p)^{N-k}`. -/
def binomProb (N : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k)

lemma binomProb_nonneg {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ binomProb N p k :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

lemma binom_sum (N : ℕ) (p : ℝ) :
    ∑ k ∈ range (N + 1), binomProb N p k = (p + (1 - p)) ^ N := by
  have h := add_pow p (1 - p) N
  simp only [binomProb]
  convert h.symm using 1
  exact sum_congr rfl fun k _ => by ring

lemma binom_sum_one (N : ℕ) (p : ℝ) :
    ∑ k ∈ range (N + 1), binomProb N p k = 1 := by
  rw [binom_sum, add_sub_cancel, one_pow]

lemma binom_mgf_half (N : ℕ) (p : ℝ) :
    ∑ k ∈ range (N + 1), ((1 : ℝ) / 2) ^ k * binomProb N p k
      = (1 - p / 2) ^ N := by
  have h := add_pow (p / 2) (1 - p) N
  have hre : p / 2 + (1 - p) = 1 - p / 2 := by ring
  have hterm : ∀ k ∈ range (N + 1),
      ((1 : ℝ) / 2) ^ k * binomProb N p k
        = (p / 2) ^ k * (1 - p) ^ (N - k) * N.choose k := by
    intro k _
    simp only [binomProb]
    ring
  calc
    ∑ k ∈ range (N + 1), ((1 : ℝ) / 2) ^ k * binomProb N p k
        = ∑ k ∈ range (N + 1),
            (p / 2) ^ k * (1 - p) ^ (N - k) * N.choose k :=
      sum_congr rfl hterm
    _ = (p / 2 + (1 - p)) ^ N := by
      convert h.symm using 1
    _ = (1 - p / 2) ^ N := by rw [hre]

lemma binom_left_tail (N m : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hm : m ≤ N) :
    ∑ k ∈ range m, binomProb N p k
      ≤ (2 : ℝ) ^ m * (1 - p / 2) ^ N := by
  have hsub : range m ⊆ range (N + 1) :=
    range_subset_range.mpr (Nat.le_succ_of_le hm)
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hhalf1 : (1 : ℝ) / 2 ≤ 1 := by norm_num
  have hle : ∀ k ∈ range m, ((1 : ℝ) / 2) ^ m ≤ ((1 : ℝ) / 2) ^ k := by
    intro k hk
    exact pow_le_pow_of_le_one hhalf hhalf1 (le_of_lt (mem_range.mp hk))
  have hweight :
      ((1 : ℝ) / 2) ^ m * ∑ k ∈ range m, binomProb N p k
        ≤ ∑ k ∈ range m, ((1 : ℝ) / 2) ^ k * binomProb N p k := by
    have h : ∑ k ∈ range m, ((1 : ℝ) / 2) ^ m * binomProb N p k
        ≤ ∑ k ∈ range m, ((1 : ℝ) / 2) ^ k * binomProb N p k :=
      sum_le_sum fun k hk =>
        mul_le_mul_of_nonneg_right (hle k hk) (binomProb_nonneg (N := N) hp0 hp1 k)
    simpa [mul_sum] using h
  have hpart :
      ∑ k ∈ range m, ((1 : ℝ) / 2) ^ k * binomProb N p k
        ≤ ∑ k ∈ range (N + 1), ((1 : ℝ) / 2) ^ k * binomProb N p k :=
    sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
      mul_nonneg (pow_nonneg hhalf _) (binomProb_nonneg hp0 hp1 k)
  have hmgf := binom_mgf_half N p
  have hbound := hweight.trans (hpart.trans_eq hmgf)
  have hcancel : (2 : ℝ) ^ m * (((1 : ℝ) / 2) ^ m *
        ∑ k ∈ range m, binomProb N p k)
      = ∑ k ∈ range m, binomProb N p k := by
    have : (2 : ℝ) ^ m * ((1 : ℝ) / 2) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    rw [← mul_assoc, this, one_mul]
  have := mul_le_mul_of_nonneg_left hbound (pow_nonneg (by positivity : (0 : ℝ) ≤ 2) m)
  rwa [hcancel] at this

lemma one_sub_half_p_le_exp {p : ℝ} (_hp0 : 0 ≤ p) :
    1 - p / 2 ≤ Real.exp (-(p / 2)) := by
  have h := Real.add_one_le_exp (-(p / 2))
  have hre : -(p / 2) + 1 = 1 - p / 2 := by ring
  rwa [hre] at h

lemma two_pow_le_exp (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp (m : ℝ) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
  have hpow : (2 : ℝ) ^ m ≤ Real.exp 1 ^ m :=
    pow_le_pow_left₀ (by positivity) h2 m
  have : Real.exp 1 ^ m = Real.exp (m : ℝ) := by
    rw [← Real.exp_nat_mul]
    simp
  rwa [this] at hpow

lemma exp_neg_four_le_one_div_five : Real.exp (-4) ≤ 1 / 5 := by
  have he1 : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
  have hexp2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hpow : (2 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 :=
      pow_le_pow_left₀ (by positivity) he1 2
    have hsq : (2 : ℝ) ^ 2 = 4 := by norm_num
    rwa [hsq, ← hexp2] at hpow
  have hexp4 : Real.exp 4 = Real.exp 2 ^ 2 := by
    have h := Real.exp_nat_mul (2 : ℝ) 2
    have hmul : ((2 : ℕ) : ℝ) * 2 = (4 : ℝ) := by norm_num
    rw [hmul] at h
    exact h
  have he4 : (16 : ℝ) ≤ Real.exp 4 := by
    have hpow : (4 : ℝ) ^ 2 ≤ Real.exp 2 ^ 2 :=
      pow_le_pow_left₀ (by positivity) he2 2
    have hsq : (4 : ℝ) ^ 2 = 16 := by norm_num
    rwa [hsq, ← hexp4] at hpow
  have h5 : (5 : ℝ) ≤ Real.exp 4 := le_trans (by norm_num) he4
  have hneg : Real.exp (-4) = 1 / Real.exp 4 := by
    rw [Real.exp_neg, one_div]
  rwa [hneg, one_div_le_one_div (Real.exp_pos _) (by positivity)]

lemma binom_left_tail_of_mean {N m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmN : m ≤ N) (hmμ : (m : ℝ) ≤ (N * p) / 4) (hμ : (16 : ℝ) ≤ N * p) :
    ∑ k ∈ range m, binomProb N p k ≤ 1 / 5 := by
  have htail := binom_left_tail N m hp0 hp1 hmN
  have hbase := one_sub_half_p_le_exp hp0
  have hnn : 0 ≤ 1 - p / 2 := by
    have : p / 2 ≤ 1 := by
      have : p ≤ 2 := hp1.trans (by norm_num)
      linarith
    linarith
  have hpow : (1 - p / 2) ^ N ≤ Real.exp (-(p / 2)) ^ N :=
    pow_le_pow_left₀ hnn hbase N
  have hexp : Real.exp (-(p / 2)) ^ N = Real.exp (-(N * p / 2)) := by
    have h := (Real.exp_nat_mul (-(p / 2)) N).symm
    have : (N : ℝ) * (-(p / 2)) = -(N * p / 2) := by ring
    simpa [this] using h
  have h2 := two_pow_le_exp m
  have hprod : (2 : ℝ) ^ m * (1 - p / 2) ^ N
      ≤ Real.exp (m : ℝ) * Real.exp (-(N * p / 2)) :=
    mul_le_mul h2 (hpow.trans_eq hexp) (pow_nonneg hnn _) (Real.exp_nonneg _)
  have hsum : Real.exp (m : ℝ) * Real.exp (-(N * p / 2))
      = Real.exp ((m : ℝ) - N * p / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have hle : Real.exp ((m : ℝ) - N * p / 2) ≤ Real.exp (-((N * p) / 4)) := by
    apply Real.exp_le_exp.mpr
    have : (m : ℝ) - N * p / 2 ≤ N * p / 4 - N * p / 2 :=
      sub_le_sub_right hmμ _
    have : N * p / 4 - N * p / 2 = -((N * p) / 4) := by ring
    linarith
  have h16 : Real.exp (-((N * p) / 4)) ≤ Real.exp (-4) :=
    Real.exp_le_exp.mpr (by linarith [hμ])
  exact (htail.trans (hprod.trans_eq hsum)).trans
    (hle.trans (h16.trans exp_neg_four_le_one_div_five))

lemma measure_one (S : Finset α) :
    measure (1 : ℝ) S = if S = univ then 1 else 0 := by
  simp only [measure, one_pow]
  by_cases h : S = univ
  · simp [h, card_univ]
  · have hlt : S.card < Fintype.card α := by
      have hle : S.card ≤ Fintype.card α := card_le_univ S
      have hne : S.card ≠ Fintype.card α := by
        intro hc
        exact h (S.card_eq_iff_eq_univ.mp hc)
      omega
    have hz : (0 : ℝ) ^ (Fintype.card α - S.card) = 0 :=
      zero_pow (Nat.sub_pos_of_lt hlt).ne'
    simp [h, hz]

lemma measureFamily_one (G : Finset (Finset α)) :
    measureFamily (1 : ℝ) G = if univ ∈ G then 1 else 0 := by
  classical
  simp only [measureFamily]
  have hterm : ∀ S ∈ G, measure (1 : ℝ) S = if S = univ then 1 else 0 :=
    fun S _ => measure_one S
  rw [sum_congr rfl hterm, sum_ite_eq']

omit [DecidableEq α] in
lemma measureFamily_univ (p : ℝ) :
    measureFamily p (univ : Finset (Finset α)) = (p + (1 - p)) ^ Fintype.card α := by
  simpa [measureFamily, measure] using
    (Fintype.sum_pow_mul_eq_add_pow α p (1 - p))

omit [DecidableEq α] in
lemma measureFamily_univ_one {p : ℝ} :
    measureFamily p (univ : Finset (Finset α)) = 1 := by
  rw [measureFamily_univ, add_sub_cancel, one_pow]

lemma measureFamily_generate_eq (p : ℝ) (F : Finset (Finset α)) :
    measureFamily p (generate F) =
      ∑ k ∈ range (Fintype.card α + 1),
        (((generate F).filter (fun S => S.card = k)).card : ℝ) *
          p ^ k * (1 - p) ^ (Fintype.card α - k) := by
  set N := Fintype.card α
  simp only [measureFamily, measure]
  have hmap : ∀ S ∈ generate F, S.card ∈ range (N + 1) :=
    fun S _ => mem_range.mpr (Nat.lt_succ_of_le (card_le_univ S))
  have hfib :=
    (sum_fiberwise_of_maps_to (g := fun S : Finset α => S.card) (t := range (N + 1))
      hmap (fun S => p ^ S.card * (1 - p) ^ (N - S.card))).symm
  rw [hfib]
  refine sum_congr rfl fun k _ => ?_
  have hconst : ∀ S ∈ (generate F).filter (fun S => S.card = k),
      p ^ S.card * (1 - p) ^ (N - S.card) = p ^ k * (1 - p) ^ (N - k) := by
    intro S hS
    have hc : S.card = k := (mem_filter.mp hS).2
    simp [hc]
  rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul]
  ring

lemma threshold_le_of_measure {F : Finset (Finset α)} {p : ℝ}
    (hp : p ∈ Set.Icc 0 1)
    (h : (1 : ℝ) / 2 ≤ measureFamily p (generate F)) :
    threshold F ≤ p :=
  csInf_le ⟨0, fun _ hx => hx.1.1⟩ ⟨hp, h⟩

lemma threshold_le_one_of_nonempty {F : Finset (Finset α)} (hF : F.Nonempty) :
    threshold F ≤ 1 := by
  have huniv : univ ∈ generate F := by
    obtain ⟨S, hS⟩ := hF
    exact mem_generate.mpr ⟨S, hS, subset_univ _⟩
  have hμ : (1 : ℝ) / 2 ≤ measureFamily 1 (generate F) := by
    simp [measureFamily_one, huniv]
    norm_num
  exact threshold_le_of_measure ⟨zero_le_one, le_rfl⟩ hμ

lemma threshold_eq_zero_of_empty_mem {F : Finset (Finset α)} (h : ∅ ∈ F) :
    threshold F = 0 := by
  have hgen := generate_eq_univ_of_empty_mem h
  have h0 : (0 : ℝ) ∈ {p : ℝ | p ∈ Set.Icc 0 1 ∧
      1 / 2 ≤ measureFamily p (generate F)} := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [hgen, measureFamily_univ_one]
    norm_num
  refine le_antisymm ?_ (le_csInf ⟨_, h0⟩ fun x hx => hx.1.1)
  exact csInf_le ⟨0, fun x hx => hx.1.1⟩ h0

lemma threshold_eq_zero_of_empty {F : Finset (Finset α)} (hF : F = ∅) :
    threshold F = 0 := by
  subst hF
  have hempty : {p : ℝ | p ∈ Set.Icc 0 1 ∧
      1 / 2 ≤ measureFamily p (generate (∅ : Finset (Finset α)))} = ∅ := by
    ext p
    constructor
    · intro hp
      have : measureFamily p (generate (∅ : Finset (Finset α))) = 0 := by
        simp [generate_empty, measureFamily]
      have : (1 : ℝ) / 2 ≤ 0 := hp.2.trans_eq this
      linarith
    · intro hp
      exact hp.elim
  unfold threshold
  rw [hempty, Real.sInf_empty]

lemma expectationThreshold_nonneg (F : Finset (Finset α)) :
    0 ≤ expectationThreshold F :=
  Real.sSup_nonneg fun _ hx => hx.1.1

lemma expectationThreshold_le_one (F : Finset (Finset α)) :
    expectationThreshold F ≤ 1 := by
  by_cases h : {p : ℝ | p ∈ Set.Icc 0 1 ∧ coverCost p F ≤ 1 / 2}.Nonempty
  · exact csSup_le h fun x hx => hx.1.2
  · have hempty : {p : ℝ | p ∈ Set.Icc 0 1 ∧ coverCost p F ≤ 1 / 2} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    unfold expectationThreshold
    rw [hempty, Real.sSup_empty]
    norm_num

lemma coverCost_gt_half_of_gt_q {F : Finset (Finset α)} {p : ℝ}
    (hp : p ∈ Set.Icc 0 1) (h : expectationThreshold F < p) :
    (1 : ℝ) / 2 < coverCost p F := by
  have hbdd : BddAbove {q : ℝ | q ∈ Set.Icc 0 1 ∧ coverCost q F ≤ 1 / 2} :=
    ⟨1, fun x hx => hx.1.2⟩
  have : p ∉ {q : ℝ | q ∈ Set.Icc 0 1 ∧ coverCost q F ≤ 1 / 2} := fun hpS =>
    (le_csSup hbdd hpS).not_gt h
  exact lt_of_not_ge fun hle => this ⟨hp, hle⟩

lemma empty_mem_of_q_eq_zero {F : Finset (Finset α)}
    (h : expectationThreshold F = 0) : ∅ ∈ F := by
  by_contra hF
  set N := Fintype.card α
  set r : ℝ := (1 : ℝ) / 2 ^ (N + 2)
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by
    have : (1 : ℝ) ≤ 2 ^ (N + 2) := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact (div_le_one (by positivity)).mpr this
  have hterm : ∀ S ∈ F, r ^ S.card ≤ r := by
    intro S hS
    have hne : S ≠ ∅ := fun he => hF (he ▸ hS)
    have hc : 1 ≤ S.card := Nat.pos_of_ne_zero (mt card_eq_zero.mp hne)
    have := pow_le_pow_of_le_one (le_of_lt hr0) hr1 hc
    simpa using this
  have hE : expectation r F ≤ (1 : ℝ) / 4 := by
    have hsum : expectation r F ≤ ∑ _S ∈ F, r := sum_le_sum hterm
    have hconst : ∑ _S ∈ F, r = (#F : ℝ) * r := by
      simp [sum_const, nsmul_eq_mul]
    have hFcard : (#F : ℝ) ≤ 2 ^ N := by
      have : F.card ≤ Fintype.card (Finset α) := card_le_univ F
      have h2 : Fintype.card (Finset α) = 2 ^ N := by
        simp [Fintype.card_finset, N]
      exact_mod_cast this.trans_eq h2
    have hmul : (#F : ℝ) * r ≤ 2 ^ N * r :=
      mul_le_mul_of_nonneg_right hFcard (le_of_lt hr0)
    have hval : (2 : ℝ) ^ N * r = 1 / 4 := by
      simp only [r]
      rw [pow_add]
      have : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [this]
      field_simp
    linarith
  have hcost : coverCost r F ≤ 1 / 2 :=
    (coverCost_le_expectation (le_of_lt hr0) (covers_self F)).trans
      (hE.trans (by norm_num))
  have hrS : r ∈ {q : ℝ | q ∈ Set.Icc 0 1 ∧ coverCost q F ≤ 1 / 2} :=
    ⟨⟨le_of_lt hr0, hr1⟩, hcost⟩
  have hbdd : BddAbove {q : ℝ | q ∈ Set.Icc 0 1 ∧ coverCost q F ≤ 1 / 2} :=
    ⟨1, fun x hx => hx.1.2⟩
  have : r ≤ expectationThreshold F := le_csSup hbdd hrS
  have : r ≤ 0 := by
    simpa [h] using this
  exact (not_le_of_gt hr0) this

lemma sdiff_range_binom (N m : ℕ) (p : ℝ) (hm : m ≤ N) :
    ∑ k ∈ range (N + 1) \ range m, binomProb N p k
      = 1 - ∑ k ∈ range m, binomProb N p k := by
  have hsub : range m ⊆ range (N + 1) :=
    range_subset_range.mpr (Nat.le_succ_of_le hm)
  have hU : range m ∪ (range (N + 1) \ range m) = range (N + 1) :=
    union_sdiff_of_subset hsub
  have hdis : Disjoint (range m) (range (N + 1) \ range m) :=
    disjoint_sdiff
  have hsum := sum_union (s₁ := range m) (s₂ := range (N + 1) \ range m)
    (f := binomProb N p) hdis
  have h1 := binom_sum_one N p
  rw [hU] at hsum
  linarith

lemma measureFamily_ge_occupation {F : Finset (Finset α)} {p : ℝ} {m : ℕ}
    {α0 : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : m ≤ Fintype.card α)
    (_hα0 : 0 ≤ α0)
    (hocc : α0 * ((Fintype.card α).choose m : ℝ) ≤
      (((generate F).filter (fun S => S.card = m)).card : ℝ)) :
    α0 * ∑ k ∈ range (Fintype.card α + 1) \ range m,
          binomProb (Fintype.card α) p k
      ≤ measureFamily p (generate F) := by
  set N := Fintype.card α
  have hsum := measureFamily_generate_eq p F
  have hterm : ∀ k ∈ range (N + 1) \ range m,
      α0 * binomProb N p k ≤
        (((generate F).filter (fun S => S.card = k)).card : ℝ) *
          p ^ k * (1 - p) ^ (N - k) := by
    intro k hk
    have hkN : k ∈ range (N + 1) := (mem_sdiff.mp hk).1
    have hkm : m ≤ k := le_of_not_gt fun hlt =>
      (mem_sdiff.mp hk).2 (mem_range.mpr hlt)
    have hkN' : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hkN)
    have hch0 : 0 < (N.choose m : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos hm)
    have hfrac := generate_level_frac_le (α := α) F hkm hkN'
    have hαm : α0 ≤
        (((generate F).filter (fun S => S.card = m)).card : ℝ) /
          (N.choose m : ℝ) :=
      (le_div_iff₀ hch0).mpr hocc
    have hch1 : 0 < (N.choose k : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos hkN')
    have hαk : α0 ≤
        (((generate F).filter (fun S => S.card = k)).card : ℝ) /
          (N.choose k : ℝ) :=
      hαm.trans (by simpa [N] using hfrac)
    have hmul : α0 * (N.choose k : ℝ) ≤
        (((generate F).filter (fun S => S.card = k)).card : ℝ) :=
      (le_div_iff₀ hch1).mp hαk
    have hnn : 0 ≤ p ^ k * (1 - p) ^ (N - k) :=
      mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)
    have : α0 * ((N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k))
        ≤ (((generate F).filter (fun S => S.card = k)).card : ℝ) *
            p ^ k * (1 - p) ^ (N - k) := by
      calc
        α0 * ((N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k))
            = (α0 * N.choose k) * (p ^ k * (1 - p) ^ (N - k)) := by ring
        _ ≤ (((generate F).filter (fun S => S.card = k)).card : ℝ) *
              (p ^ k * (1 - p) ^ (N - k)) :=
          mul_le_mul_of_nonneg_right hmul hnn
        _ = (((generate F).filter (fun S => S.card = k)).card : ℝ) *
              p ^ k * (1 - p) ^ (N - k) := by ring
    simpa [binomProb] using this
  have hleft :
      α0 * ∑ k ∈ range (N + 1) \ range m, binomProb N p k
        ≤ ∑ k ∈ range (N + 1) \ range m,
            (((generate F).filter (fun S => S.card = k)).card : ℝ) *
              p ^ k * (1 - p) ^ (N - k) := by
    rw [mul_sum]
    exact sum_le_sum hterm
  have hrest :
      ∑ k ∈ range (N + 1) \ range m,
          (((generate F).filter (fun S => S.card = k)).card : ℝ) *
            p ^ k * (1 - p) ^ (N - k)
        ≤ ∑ k ∈ range (N + 1),
            (((generate F).filter (fun S => S.card = k)).card : ℝ) *
              p ^ k * (1 - p) ^ (N - k) :=
    sum_le_sum_of_subset_of_nonneg sdiff_subset fun k _ _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
        (pow_nonneg (sub_nonneg.mpr hp1) _)
  have := hleft.trans hrest
  simpa [hsum, N] using this

lemma threshold_le_parkPham_of_level_gt_card {F : Finset (Finset α)}
    {ℓ ℓ' N m : ℕ} {q p : ℝ} (hq0 : 0 ≤ q)
    (hlog : (1 : ℝ) ≤ Real.logb 2 (ℓ : ℝ))
    (hlog' : Real.logb 2 (ℓ' + 1 : ℝ) ≤ 2 * Real.logb 2 (ℓ : ℝ))
    (hp : p = 2 * q)
    (hmle : (m : ℝ) ≤ 1000 * p * N * Real.logb 2 (ℓ' + 1 : ℝ))
    (hmN : N < m) (hth1 : threshold F ≤ 1) :
    threshold F ≤ parkPhamK * q * Real.logb 2 (ℓ : ℝ) := by
  have hNpos : (0 : ℝ) < N := by
    have hpos : 0 < N := Nat.pos_of_ne_zero fun hN0 => by
      have hm0 : m = 0 := by
        have hNcast : (N : ℝ) = 0 := by exact_mod_cast hN0
        have : (m : ℝ) ≤ 0 := by simpa [hNcast] using hmle
        exact_mod_cast (le_antisymm this (Nat.cast_nonneg m))
      omega
    exact_mod_cast hpos
  have hml : (N : ℝ) < 1000 * p * N * Real.logb 2 (ℓ' + 1 : ℝ) :=
    (Nat.cast_lt.mpr hmN).trans_le hmle
  have hre : (1000 : ℝ) * p * N * Real.logb 2 (ℓ' + 1 : ℝ) =
      N * (1000 * p * Real.logb 2 (ℓ' + 1 : ℝ)) := by ring
  have h1 : (1 : ℝ) < 1000 * p * Real.logb 2 (ℓ' + 1 : ℝ) := by
    have : (N : ℝ) * 1 < N * (1000 * p * Real.logb 2 (ℓ' + 1 : ℝ)) := by
      rw [mul_one, ← hre]
      exact hml
    exact (mul_lt_mul_iff_of_pos_left hNpos).mp this
  have h1' : (1 : ℝ) < 2000 * q * Real.logb 2 (ℓ' + 1 : ℝ) := by
    have hre' : (1000 : ℝ) * p * Real.logb 2 (ℓ' + 1 : ℝ) =
        2000 * q * Real.logb 2 (ℓ' + 1 : ℝ) := by
      rw [hp]
      ring
    rwa [hre'] at h1
  have h1'' : (1 : ℝ) < 4000 * q * Real.logb 2 (ℓ : ℝ) := by
    have hstep : (1 : ℝ) < 2000 * q * (2 * Real.logb 2 (ℓ : ℝ)) :=
      h1'.trans_le (mul_le_mul_of_nonneg_left hlog'
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2000) hq0))
    have hre' : (2000 : ℝ) * q * (2 * Real.logb 2 (ℓ : ℝ)) =
        4000 * q * Real.logb 2 (ℓ : ℝ) := by ring
    rwa [hre'] at hstep
  have hK : (4000 : ℝ) ≤ parkPhamK := by
    simp [parkPhamK]
    norm_num
  have hmain : (1 : ℝ) < parkPhamK * q * Real.logb 2 (ℓ : ℝ) := by
    have : (4000 : ℝ) * q * Real.logb 2 (ℓ : ℝ) ≤
        parkPhamK * q * Real.logb 2 (ℓ : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hK hq0)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog)
    exact h1''.trans_le this
  exact hth1.trans hmain.le

/-- Explicit Park–Pham bound. -/
lemma park_pham_bound {α : Type} [DecidableEq α] [Fintype α]
    (F : Finset (Finset α)) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (_hb : IsBounded F ℓ) :
    threshold F ≤ parkPhamK * expectationThreshold F * Real.logb 2 (ℓ : ℝ) := by
  set q := expectationThreshold F
  set N := Fintype.card α
  have hq0 : 0 ≤ q := expectationThreshold_nonneg F
  have hlog : (1 : ℝ) ≤ Real.logb 2 (ℓ : ℝ) := logb_two_ell_ge_one hℓ
  have hKlog : 0 ≤ parkPhamK * q * Real.logb 2 (ℓ : ℝ) :=
    mul_nonneg (mul_nonneg (le_of_lt parkPhamK_pos) hq0)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog)
  by_cases hempty : ∅ ∈ F
  · simpa [threshold_eq_zero_of_empty_mem hempty] using hKlog
  by_cases hF0 : F = ∅
  · simpa [threshold_eq_zero_of_empty hF0] using hKlog
  have hFne : F.Nonempty := nonempty_iff_ne_empty.mpr hF0
  have hqpos : 0 < q := by
    have : q ≠ 0 := fun hz => hempty (empty_mem_of_q_eq_zero hz)
    exact lt_of_le_of_ne hq0 this.symm
  have hth1 : threshold F ≤ 1 := threshold_le_one_of_nonempty hFne
  by_cases h2q : (1 : ℝ) ≤ 2 * q
  · have hmain : (1 : ℝ) ≤ parkPhamK * q * Real.logb 2 (ℓ : ℝ) := by
      have h2 : (1 : ℝ) ≤ 2 * q * Real.logb 2 (ℓ : ℝ) := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (2 * q) * Real.logb 2 (ℓ : ℝ) :=
            mul_le_mul h2q hlog (by norm_num)
              (le_trans (by norm_num : (0 : ℝ) ≤ 1) h2q)
      have hK : (2 : ℝ) * q * Real.logb 2 (ℓ : ℝ)
          ≤ parkPhamK * q * Real.logb 2 (ℓ : ℝ) := by
        have : (2 : ℝ) ≤ parkPhamK := parkPhamK_ge_two
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right this hq0)
          (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog)
      exact h2.trans hK
    exact hth1.trans hmain
  set p : ℝ := 2 * q
  have hp0 : 0 ≤ p := mul_nonneg (by norm_num) hq0
  have hp1 : p < 1 := lt_of_not_ge h2q
  have hpI : p ∈ Set.Icc 0 1 := ⟨hp0, le_of_lt hp1⟩
  have hpq : q < p := by
    change q < 2 * q
    linarith [hqpos]
  have hcost : (1 : ℝ) / 2 < coverCost p F := coverCost_gt_half_of_gt_q hpI hpq
  set ℓ' := min ℓ N
  have hℓ'N : ℓ' ≤ N := min_le_right _ _
  have hb' : IsBounded F ℓ' := IsBounded.min_card _hb
  have hf' : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ' + 2) ≤ coverCost p F := by
    have : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ' + 2) ≤ 1 / 2 := by
      have : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ (ℓ' + 2) := by positivity
      linarith
    exact this.trans (le_of_lt hcost)
  have hcov := covering_aux ℓ' F p hℓ'N hp0 (le_of_lt hp1) hb' hf'
  set m := coveringLevel p N ℓ'
  have hmle : (m : ℝ) ≤ 1000 * p * N * Real.logb 2 (ℓ' + 1 : ℝ) := by
    simpa [m, coveringConstant] using coveringLevel_cast_le p N ℓ' hp0
  have hlog' := logb_min_add_one_le (N := N) hℓ
  by_cases hmN : N < m
  · exact threshold_le_parkPham_of_level_gt_card hq0 hlog hlog' rfl hmle hmN hth1
  have hmN' : m ≤ N := le_of_not_gt hmN
  by_cases hm0 : m = 0
  · have hch : (N.choose m : ℝ) = 1 := by simp [hm0]
    have hα : (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2) ≤
        (((generate F).filter (fun S => S.card = m)).card : ℝ) := by
      simpa [hch, m, N] using hcov
    have hpos : (1 : ℝ) / 2 < (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2) := by
      have : 0 < (1 : ℝ) / (2 : ℝ) ^ (ℓ' + 2) := by positivity
      linarith
    have hcardpos : 0 < ((generate F).filter (fun S => S.card = m)).card := by
      have : (0 : ℝ) <
          (((generate F).filter (fun S => S.card = m)).card : ℝ) :=
        lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (hpos.trans_le hα)
      exact Nat.cast_pos.mp this
    obtain ⟨S, hS⟩ := card_pos.mp hcardpos
    have ⟨hgen, hc⟩ := mem_filter.mp hS
    have hSemp : S = ∅ := card_eq_zero.mp (hc.trans hm0)
    have : ∅ ∈ generate F := by rwa [← hSemp]
    obtain ⟨T, hT, hTsub⟩ := mem_generate.mp this
    have : T = ∅ := subset_empty.mp hTsub
    exact (hempty (this ▸ hT)).elim
  have hmpos : 1 ≤ m := Nat.pos_of_ne_zero hm0
  by_cases hbig : (1 : ℝ) ≤ parkPhamK * q * Real.logb 2 (ℓ : ℝ)
  · exact hth1.trans hbig
  set p' : ℝ := parkPhamK * q * Real.logb 2 (ℓ : ℝ)
  have hp'0 : 0 ≤ p' := hKlog
  have hp'1 : p' < 1 := lt_of_not_ge hbig
  have hp'I : p' ∈ Set.Icc 0 1 := ⟨hp'0, le_of_lt hp'1⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hml1 : (1 : ℝ) ≤ 1000 * p * N * Real.logb 2 (ℓ' + 1 : ℝ) :=
    hm1.trans hmle
  have h4000 : (1 : ℝ) ≤ 4000 * q * N * Real.logb 2 (ℓ : ℝ) := by
    have h2000 : (1 : ℝ) ≤ 2000 * q * N * Real.logb 2 (ℓ' + 1 : ℝ) := by
      have hre : (1000 : ℝ) * p * N * Real.logb 2 (ℓ' + 1 : ℝ)
          = 2000 * q * N * Real.logb 2 (ℓ' + 1 : ℝ) := by
        simp only [p]
        ring
      rwa [hre] at hml1
    have hmul : (2000 : ℝ) * q * N * Real.logb 2 (ℓ' + 1 : ℝ)
        ≤ 2000 * q * N * (2 * Real.logb 2 (ℓ : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog'
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2000) hq0)
          (Nat.cast_nonneg N))
    have hre : (2000 : ℝ) * q * N * (2 * Real.logb 2 (ℓ : ℝ))
        = 4000 * q * N * Real.logb 2 (ℓ : ℝ) := by ring
    exact h2000.trans (hmul.trans_eq hre)
  have hμ : (16 : ℝ) ≤ N * p' := by
    have hK : (64000 : ℝ) ≤ parkPhamK := by
      simp [parkPhamK]
      norm_num
    have : (16 : ℝ) * (4000 * q * N * Real.logb 2 (ℓ : ℝ))
        ≤ parkPhamK * q * N * Real.logb 2 (ℓ : ℝ) := by
      have hreL : (16 : ℝ) * (4000 * q * N * Real.logb 2 (ℓ : ℝ))
          = 64000 * (q * N * Real.logb 2 (ℓ : ℝ)) := by ring
      have hreR : parkPhamK * q * N * Real.logb 2 (ℓ : ℝ)
          = parkPhamK * (q * N * Real.logb 2 (ℓ : ℝ)) := by ring
      rw [hreL, hreR]
      exact mul_le_mul_of_nonneg_right hK
        (mul_nonneg (mul_nonneg hq0 (Nat.cast_nonneg N))
          (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog))
    have : (16 : ℝ) ≤ 16 * (4000 * q * N * Real.logb 2 (ℓ : ℝ)) := by
      have := mul_le_mul_of_nonneg_left h4000 (by positivity : (0 : ℝ) ≤ 16)
      simpa using this
    have hre : parkPhamK * q * N * Real.logb 2 (ℓ : ℝ) = N * p' := by
      simp only [p']
      ring
    linarith
  have hmμ : (m : ℝ) ≤ (N * p') / 4 := by
    have hm4000 : (m : ℝ) ≤ 4000 * q * N * Real.logb 2 (ℓ : ℝ) := by
      have hm2000 : (m : ℝ) ≤ 2000 * q * N * Real.logb 2 (ℓ' + 1 : ℝ) := by
        have hre : (1000 : ℝ) * p * N * Real.logb 2 (ℓ' + 1 : ℝ)
            = 2000 * q * N * Real.logb 2 (ℓ' + 1 : ℝ) := by
          simp only [p]
          ring
        rwa [hre] at hmle
      have hmul : (2000 : ℝ) * q * N * Real.logb 2 (ℓ' + 1 : ℝ)
          ≤ 2000 * q * N * (2 * Real.logb 2 (ℓ : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog'
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2000) hq0)
            (Nat.cast_nonneg N))
      have hre : (2000 : ℝ) * q * N * (2 * Real.logb 2 (ℓ : ℝ))
          = 4000 * q * N * Real.logb 2 (ℓ : ℝ) := by ring
      exact hm2000.trans (hmul.trans_eq hre)
    have : (4000 : ℝ) * q * N * Real.logb 2 (ℓ : ℝ) ≤ (N * p') / 4 := by
      have hK : (16000 : ℝ) ≤ parkPhamK := by
        simp [parkPhamK]
        norm_num
      have hreL : (4 : ℝ) * (4000 * q * N * Real.logb 2 (ℓ : ℝ))
          = 16000 * (q * N * Real.logb 2 (ℓ : ℝ)) := by ring
      have hreR : parkPhamK * q * N * Real.logb 2 (ℓ : ℝ)
          = parkPhamK * (q * N * Real.logb 2 (ℓ : ℝ)) := by ring
      have : (4 : ℝ) * (4000 * q * N * Real.logb 2 (ℓ : ℝ))
          ≤ N * p' := by
        have : 16000 * (q * N * Real.logb 2 (ℓ : ℝ))
            ≤ parkPhamK * (q * N * Real.logb 2 (ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_right hK
            (mul_nonneg (mul_nonneg hq0 (Nat.cast_nonneg N))
              (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog))
        have : parkPhamK * (q * N * Real.logb 2 (ℓ : ℝ)) = N * p' := by
          simp only [p']
          ring
        linarith
      linarith
    linarith
  have htail : ∑ k ∈ range m, binomProb N p' k ≤ 1 / 5 :=
    binom_left_tail_of_mean (N := N) (m := m) (p := p') hp'0 (le_of_lt hp'1)
      hmN' hmμ hμ
  have hα0 : (0 : ℝ) ≤ (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2) := by positivity
  have hocc :
      ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2)) * (N.choose m : ℝ) ≤
        (((generate F).filter (fun S => S.card = m)).card : ℝ) := by
    simpa [m, N] using hcov
  have hge := measureFamily_ge_occupation (F := F) (p := p') (m := m)
      (α0 := (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2))
      hp'0 (le_of_lt hp'1) hmN' hα0 hocc
  have hmass :
      (4 : ℝ) / 5 ≤ ∑ k ∈ range (N + 1) \ range m, binomProb N p' k := by
    have := sdiff_range_binom N m p' hmN'
    linarith [htail]
  have hμF : (1 : ℝ) / 2 ≤ measureFamily p' (generate F) := by
    have hmul : ((2 : ℝ) / 3) * (4 / 5) ≤
        ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2)) *
          ∑ k ∈ range (N + 1) \ range m, binomProb N p' k := by
      have h1 : (2 : ℝ) / 3 ≤ (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2) := by
        have : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ (ℓ' + 2) := by positivity
        linarith
      exact mul_le_mul h1 hmass (by positivity) (by positivity)
    have h815 : ((2 : ℝ) / 3) * (4 / 5) = 8 / 15 := by norm_num
    have : (8 : ℝ) / 15 ≤ measureFamily p' (generate F) := by
      rw [← h815]
      exact hmul.trans hge
    have : (1 : ℝ) / 2 ≤ 8 / 15 := by norm_num
    exact this.trans ‹(8 : ℝ) / 15 ≤ measureFamily p' (generate F)›
  have : threshold F ≤ p' := threshold_le_of_measure hp'I hμF
  simpa [p'] using this

end

end KahnKalai
