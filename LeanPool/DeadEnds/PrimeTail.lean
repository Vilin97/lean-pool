/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/

import LeanPool.DeadEnds.Counting

/-!
Prime-tail and single-prime divisibility estimates.
-/

namespace LeanPool.DeadEnds

lemma gt_sup_imp_not_mem (s : Finset Nat.Primes) (q : Nat.Primes) (hq : (q : ℕ) > s.sup (·.val)) :
    q ∉ s := by
  intro hq_mem
  have h := Finset.le_sup (f := fun x : Nat.Primes => (x : ℕ)) hq_mem
  simp only at h
  omega

lemma tsum_primes_gt_le_tsum_compl (f : Nat.Primes → ℝ) (hf : ∀ p, 0 ≤ f p) (hsum : Summable f)
    (s : Finset Nat.Primes) :
    ∑' (p : {q : Nat.Primes // (q : ℕ) > s.sup (·.val)}), f p ≤
    ∑' (p : {q : Nat.Primes // q ∉ s}), f p := by
  apply Summable.tsum_le_tsum_of_inj
    (fun x => ⟨x.val, gt_sup_imp_not_mem s x.val x.property⟩)
  · intro ⟨a, ha⟩ ⟨b, hb⟩ h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h
  · intro c _
    exact hf c.val
  · intro i
    rfl
  · exact hsum.subtype _
  · exact hsum.subtype _

lemma exists_finset_tsum_compl_lt (f : Nat.Primes → ℝ) (_hf : ∀ p, 0 ≤ f p) (_hsum : Summable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset Nat.Primes, ∑' (p : {q : Nat.Primes // q ∉ s}), f p < ε := by
  have htail : Filter.Tendsto
      (fun s : Finset Nat.Primes => ∑' (p : {q : Nat.Primes // q ∉ s}), f p)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_tsum_compl_atTop_zero f
  obtain ⟨s, hs⟩ := Metric.tendsto_atTop.mp htail ε hε
  refine ⟨s, ?_⟩
  have hs_self := hs s (by simp)
  rw [Real.dist_eq] at hs_self
  linarith [(abs_lt.mp hs_self).2]

lemma prime_tail_sum_small (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℕ, ∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (((p : Nat.Primes) : ℕ) : ℝ) ^ 2 < ε :=
        by
  set f : Nat.Primes → ℝ := fun p => 1 / ((p : ℕ) : ℝ) ^ 2 with hf
  have hfnn : ∀ p, 0 ≤ f p := fun p => by simp only [hf]; positivity
  obtain ⟨s, hs⟩ := exists_finset_tsum_compl_lt f hfnn primes_summable_one_div_sq ε hε
  use s.sup (·.val)
  have h1 : ∑' (p : {q : Nat.Primes // (q : ℕ) > s.sup (·.val)}), f p ≤
            ∑' (p : {q : Nat.Primes // q ∉ s}), f p := by
    apply tsum_primes_gt_le_tsum_compl
    · exact hfnn
    · exact primes_summable_one_div_sq
  simp only [hf] at h1 hs
  exact lt_of_le_of_lt h1 hs

lemma prime_count_le_sqrt (M : ℕ) :
    (M.sqrt.primesBelow).card ≤ Nat.sqrt M := by
  calc (M.sqrt.primesBelow).card ≤ (Finset.range (M.sqrt)).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp)
    _ = M.sqrt := Finset.card_range _

lemma sqrt_div_X_small (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (Nat.sqrt X : ℝ) / X < ε := by
  have h₁ : 0 < (1 / ε : ℝ) := by positivity
  have h₂ : 0 < (1 / ε : ℝ) ^ 2 := by positivity
  have h₃ : ∃ (X₀ : ℕ), (1 / ε : ℝ) ^ 2 < (X₀ : ℝ) := by
    obtain ⟨X₀, hX₀⟩ := exists_nat_gt ((1 / ε : ℝ) ^ 2)
    refine ⟨X₀, ?_⟩
    exact_mod_cast hX₀
  obtain ⟨X₀, hX₀⟩ := h₃
  refine ⟨X₀, ?_⟩
  intro X hX
  have h₄ : (X : ℝ) ≥ (X₀ : ℝ) := by exact_mod_cast hX
  have h₆ : 0 < (X : ℝ) := by
    by_contra h
    have h₁₀ : (X₀ : ℕ) = 0 := by
      by_contra _
      linarith
    have h₁₁ : (1 / ε : ℝ) ^ 2 < (X₀ : ℝ) := hX₀
    have h₁₂ : (X₀ : ℝ) = 0 := by simp [h₁₀]
    rw [h₁₂] at h₁₁
    norm_num at h₁₁ ⊢; nlinarith [h₂]
  have h₇ : Real.sqrt (X : ℝ) > 1 / ε := by
    have h₈ : Real.sqrt (X : ℝ) > 1 / ε := by
      have h₉ : Real.sqrt (X : ℝ) > 0 := Real.sqrt_pos.mpr (by positivity)
      have h₁₁ : (Real.sqrt (X : ℝ)) ^ 2 = (X : ℝ) := by
        rw [Real.sq_sqrt]; positivity
      nlinarith [Real.sqrt_nonneg (X : ℝ), Real.sq_sqrt (by positivity : 0 ≤ (X : ℝ))]
    exact h₈
  have h₈ : 1 / Real.sqrt (X : ℝ) < ε := by
    have h₁₂ : 1 / Real.sqrt (X : ℝ) < ε := by
      calc
        1 / Real.sqrt (X : ℝ) < 1 / (1 / ε) := by
          apply one_div_lt_one_div_of_lt
          · positivity
          · linarith
        _ = ε := by
          field_simp
    exact h₁₂
  have h₉ : (Nat.sqrt X : ℝ) ≤ Real.sqrt (X : ℝ) := by
    have h₁₁ : (Nat.sqrt X : ℝ) ^ 2 ≤ (X : ℝ) := by
      norm_cast
      have h₁₂ : (Nat.sqrt X : ℕ) ^ 2 ≤ X := by
        nlinarith [Nat.sqrt_le X, Nat.lt_succ_sqrt X]
      exact_mod_cast h₁₂
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (X : ℝ)),
      sq_nonneg ((Nat.sqrt X : ℝ) - Real.sqrt (X : ℝ))]
  have h₁₀ : (Nat.sqrt X : ℝ) / X ≤ 1 / Real.sqrt (X : ℝ) := by
    have h₁₁ : 0 < (X : ℝ) := by positivity
    calc
      (Nat.sqrt X : ℝ) / X ≤ Real.sqrt (X : ℝ) / X := by
        gcongr
      _ = 1 / Real.sqrt (X : ℝ) := by
        have h₁₄ : Real.sqrt (X : ℝ) > 0 := by positivity
        field_simp [h₁₁.ne', h₁₄.ne'];
        nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (X : ℝ))]
  have h₁₁ : (Nat.sqrt X : ℝ) / X < ε := by
    calc
      (Nat.sqrt X : ℝ) / X ≤ 1 / Real.sqrt (X : ℝ) := h₁₀
      _ < ε := h₈
  exact h₁₁

lemma card_multiples_Icc (q : ℕ) (X : ℕ) :
    ((Finset.Icc 1 X).filter fun N => q ^ 2 ∣ N).card ≤ X / q ^ 2 := by
  have h_subset : ((Finset.Icc 1 X).filter fun N => q ^ 2 ∣ N) ⊆ (Finset.range (X + 1)).filter (
      fun k => k ≠ 0 ∧ q ^ 2 ∣ k) := by
    intro N hN
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hN ⊢
    exact ⟨by omega, by omega, hN.2⟩
  have h_card_multiples' : ((Finset.range (X + 1)).filter (fun k => k ≠ 0 ∧ q ^ 2 ∣ k)).card =
      X / q ^ 2 := Nat.card_multiples' X (q ^ 2)
  simpa [h_card_multiples'] using Finset.card_le_card h_subset

/-- The number of N ∈ (0, X] satisfying N ≡ v (mod r) is at most X / r + 1.

    The exact count is given by `Nat.Ioc_filter_modEq_card`:
    `{x ∈ Finset.Ioc a b | x ≡ v [MOD r]}.card = max(⌊(b - v)/r⌋ - ⌊(a - v)/r⌋, 0)`
    For a = 0, b = X, the count equals max(⌊(X - v)/r⌋ - ⌊-v/r⌋, 0).
    By `floor_diff_bound`, the expression ⌊(X - v)/r⌋ - ⌊-v/r⌋ ≤ ⌊X/r⌋ + 1.
    Since X, r are naturals, ⌊(X : ℝ)/r⌋ = X / r (integer division).
    The nonnegative floor difference is at most the upper bound, giving count ≤ X / r + 1. -/
lemma floor_diff_bound_rat (X v r : ℕ) (hr : 0 < r) :
    ⌊((X : ℚ) - v) / r⌋ - ⌊(-(v : ℚ)) / r⌋ ≤ ⌊(X : ℚ) / r⌋ + 1 := by
  have floor_sub_floor_le : ∀ (a b : ℚ), ⌊a⌋ - ⌊b⌋ ≤ ⌊a - b⌋ + 1 := by
    intro a b
    have h₂ : (⌊a⌋ : ℚ) ≤ a := by exact_mod_cast Int.floor_le a
    have h₅ : (b : ℚ) < (⌊b⌋ : ℚ) + 1 := by exact_mod_cast Int.lt_floor_add_one b
    have h₆ : (⌊a⌋ : ℚ) - (⌊b⌋ : ℚ) - 1 < a - b := by linarith
    have h₇ : ((⌊a⌋ : ℤ) - ⌊b⌋ - 1 : ℤ) ≤ ⌊(a - b : ℚ)⌋ := by
      apply Int.le_floor.mpr
      push_cast
      linarith [h₆]
    linarith
  have h := floor_sub_floor_le (((X : ℚ) - v) / r) ((-(v : ℚ)) / r)
  have hr' : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hr)
  have heq : ((X : ℚ) - v) / r - (-(v : ℚ)) / r = (X : ℚ) / r := by field_simp; ring
  rw [heq] at h
  exact h

lemma card_modEq_Icc_bound (v r X : ℕ) (hr : 0 < r) :
    ((Finset.Ioc 0 X).filter fun N => N ≡ v [MOD r]).card ≤ X / r + 1 := by
  have h := Nat.Ioc_filter_modEq_card 0 X hr v
  simp only [Nat.cast_zero, zero_sub] at h
  have hbd := floor_diff_bound_rat X v r hr
  have hfloor : ⌊(X : ℚ) / r⌋ = (X / r : ℕ) := Rat.floor_natCast_div_natCast X r
  rw [hfloor] at hbd
  have hmax : max (⌊((X : ℚ) - v) / r⌋ - ⌊(-(v : ℚ)) / r⌋) 0 ≤ (X / r : ℤ) + 1 := by
    apply max_le hbd
    have : (0 : ℤ) ≤ (X / r : ℕ) := Nat.cast_nonneg _
    omega
  have hcard : ((Finset.Ioc 0 X).filter fun N => N ≡ v [MOD r]).card =
      (max (⌊((X : ℚ) - v) / r⌋ - ⌊(-(v : ℚ)) / r⌋) 0).toNat := by
    have := congrArg Int.toNat h
    simp only [Int.toNat_natCast] at this
    exact this
  rw [hcard]
  omega

lemma gcd_psq_b_eq_one (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b) (hbp : b < p) :
    (p ^ 2).gcd b = 1 := by
  have h₁ : b.Coprime (p ^ 2) := b_coprime_p_sq p hp b hb hbp
  have h₂ : (p ^ 2).gcd b = 1 := h₁.symm
  aesop

/-- p² > 0 when p is prime. -/
lemma prime_sq_pos (p : ℕ) (hp : Nat.Prime p) : 0 < p ^ 2 := by
  exact Nat.pow_pos hp.pos

lemma zmod_mul_inv_add_eq_zero (n b d : ℕ) (_hn : 0 < n) (hb : b.Coprime n) :
    (↑b : ZMod n) * ((-↑d : ZMod n) * (↑b : ZMod n)⁻¹) + ↑d = 0 := by
  have h_unit : IsUnit (↑b : ZMod n) := (ZMod.isUnit_iff_coprime b n).mpr hb
  have h_inv : (↑b : ZMod n) * (↑b : ZMod n)⁻¹ = 1 := ZMod.mul_inv_of_unit _ h_unit
  have h_main : (↑b : ZMod n) * ((-↑d : ZMod n) * (↑b : ZMod n)⁻¹) = (-↑d : ZMod n) := by
    rw [mul_left_comm, h_inv, mul_one]
  have h_final : (↑b : ZMod n) * ((-↑d : ZMod n) * (↑b : ZMod n)⁻¹) + ↑d = 0 := by aesop
  exact h_final

/-- Constructs a unique residue v such that b*v ≡ -d (mod p²) for prime p > b ≥ 2.
    In ZMod (p²), since b is a unit (coprime to p²), we can define v = b⁻¹ * (-d).
    The result is a natural number v < p² such that p² | b*v + d. -/
lemma exists_inverse_residue (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b) (hbp : b < p) (d : ℕ) :
    ∃ v : ℕ, v < p ^ 2 ∧ (p ^ 2) ∣ (b * v + d) := by
  have hcop : b.Coprime (p ^ 2) := b_coprime_p_sq p hp b hb hbp
  have hp2_pos : 0 < p ^ 2 := prime_sq_pos p hp
  haveI : NeZero (p ^ 2) := ⟨Nat.pos_iff_ne_zero.mp hp2_pos⟩
  let v_zmod : ZMod (p ^ 2) := (-↑d : ZMod (p ^ 2)) * (↑b : ZMod (p ^ 2))⁻¹
  use v_zmod.val
  constructor
  · exact ZMod.val_lt v_zmod
  · rw [← CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2)]
    simp only [Nat.cast_add, Nat.cast_mul]
    have hval : (v_zmod.val : ZMod (p ^ 2)) = v_zmod := ZMod.natCast_zmod_val v_zmod
    rw [hval]
    exact zmod_mul_inv_add_eq_zero (p ^ 2) b d hp2_pos hcop

lemma dvd_iff_modEq_of_coprime (p b v d N : ℕ) (hcop : (p ^ 2).gcd b = 1)
    (hdvd_v : (p ^ 2) ∣ (b * v + d)) :
    (p ^ 2) ∣ (b * N + d) ↔ N ≡ v [MOD (p ^ 2)] := by
  have h_v_mod : (b * v + d) ≡ 0 [MOD (p ^ 2)] := Nat.modEq_zero_iff_dvd.mpr hdvd_v
  constructor
  · intro hdvd_N
    have h_N_mod : (b * N + d) ≡ 0 [MOD (p ^ 2)] := Nat.modEq_zero_iff_dvd.mpr hdvd_N
    have h_eq : (b * N + d) ≡ (b * v + d) [MOD (p ^ 2)] := h_N_mod.trans h_v_mod.symm
    have h_mul : b * N ≡ b * v [MOD (p ^ 2)] := Nat.ModEq.add_right_cancel' d h_eq
    exact Nat.ModEq.cancel_left_of_coprime hcop h_mul
  · intro h_modEq
    have h_mul : b * N ≡ b * v [MOD (p ^ 2)] := h_modEq.mul_left b
    have h_add : (b * N + d) ≡ (b * v + d) [MOD (p ^ 2)] := h_mul.add_right d
    have h_zero : (b * N + d) ≡ 0 [MOD (p ^ 2)] := h_add.trans h_v_mod
    exact Nat.modEq_zero_iff_dvd.mp h_zero

lemma dvd_shift_iff_modEq_unique (b : ℕ) (hb : 2 ≤ b) (q : Nat.Primes) (hq : (q : ℕ) > b) (d : ℕ) :
    ∃ v : ℕ, ∀ N : ℕ, (q : ℕ) ^ 2 ∣ b * N + d ↔ N ≡ v [MOD (q : ℕ) ^ 2] := by
  let p := (q : ℕ)
  have hp : Nat.Prime p := q.prop
  have hbp : b < p := hq
  have hcop := gcd_psq_b_eq_one p hp b hb hbp
  obtain ⟨v, _, hdvd_v⟩ := exists_inverse_residue p hp b hb hbp d
  exact ⟨v, fun N => dvd_iff_modEq_of_coprime p b v d N hcop hdvd_v⟩

lemma filter_shifted_dvd_eq_filter_modEq (b : ℕ) (hb : 2 ≤ b) (q : Nat.Primes) (hq : (q : ℕ) > b)
    (d : ℕ) (S : Finset ℕ) :
    ∃ v : ℕ, (S.filter fun N => (q : ℕ) ^ 2 ∣ b * N + d) =
             (S.filter fun N => N ≡ v [MOD (q : ℕ) ^ 2]) := by
  obtain ⟨v, hv⟩ := dvd_shift_iff_modEq_unique b hb q hq d
  exact ⟨v, Finset.filter_congr (fun N _ => hv N)⟩

/-- For a fixed d, the count of N in [1,X] with q²|(bN+d) is at most X/q² + 1.
    Since q > b and q is prime, gcd(b,q²) = 1, so the congruence bN ≡ -d (mod q²) has
    a unique solution mod q². The solutions form an arithmetic progression with common
    difference q², so there are at most ⌊X/q²⌋ + 1 solutions in [1,X]. -/
lemma card_shifted_divisible_bound (b : ℕ) (hb : 2 ≤ b) (q : Nat.Primes) (hq : (q : ℕ) > b)
    (d : ℕ) (X : ℕ) :
    ((Finset.Icc 1 X).filter fun N => (q : ℕ) ^ 2 ∣ b * N + d).card ≤ X / (q : ℕ) ^ 2 + 1 := by
  obtain ⟨v, hv⟩ := filter_shifted_dvd_eq_filter_modEq b hb q hq d (Finset.Icc 1 X)
  rw [hv]
  exact card_modEq_Icc_bound v ((q : ℕ) ^ 2) X (Nat.pow_pos q.prop.pos)

/-- The count of N in [1,X] with ∃d∈T, q²|(bN+d) is at most |T|*(X/q² + 1).
    This follows from the union bound over T applied to card_shifted_divisible_bound.
    Uses `Finset.card_biUnion_le_card_mul : ∀ (s : Finset ι) (f : ι → Finset β) (n : ℕ),
    (∀ a ∈ s, (f a).card ≤ n) → (s.biUnion f).card ≤ s.card * n`. -/
lemma card_union_shifted_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (q : Nat.Primes) (hq : (q : ℕ) > b) (X : ℕ) :
    ((Finset.Icc 1 X).filter fun N => ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d).card ≤
      T.card * (X / (q : ℕ) ^ 2 + 1) := by
  have h_eq : (Finset.Icc 1 X).filter (fun N => ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d) =
      T.biUnion (fun d => (Finset.Icc 1 X).filter (fun N => (q : ℕ) ^ 2 ∣ b * N + d)) := by
    ext N
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hN, d, hd, hdiv⟩
      exact ⟨d, hd, hN, hdiv⟩
    · rintro ⟨d, hd, hN, hdiv⟩
      exact ⟨hN, d, hd, hdiv⟩
  rw [h_eq]
  apply Finset.card_biUnion_le_card_mul
  intro d _
  exact card_shifted_divisible_bound b hb q hq d X

lemma combined_bound_aux (T : Finset ℕ) (X q_sq : ℕ) :
    X / q_sq + T.card * (X / q_sq + 1) ≤ (T.card + 1) * (X / q_sq + 1) := by
  have h_main : X / q_sq + T.card * (X / q_sq + 1) ≤ (T.card + 1) * (X / q_sq + 1) := by
    rw [add_mul, one_mul]; omega
  aesop

lemma single_prime_violation_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (q : Nat.Primes) (hq : (q : ℕ) > b) (X : ℕ) :
    ((Finset.Icc 1 X).filter fun N =>
      (q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d).card ≤ (T.card + 1) * (X / (q : ℕ) ^ 2 +
          1) := by
  have hA : ((Finset.Icc 1 X).filter fun N => (q : ℕ) ^ 2 ∣ N).card ≤ X / (q : ℕ) ^ 2 :=
    card_multiples_Icc q X
  have hB : ((Finset.Icc 1 X).filter fun N => ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d).card ≤
      T.card * (X / (q : ℕ) ^ 2 + 1) := card_union_shifted_bound b hb T hT q hq X
  calc ((Finset.Icc 1 X).filter fun N => (q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d).card
      ≤ ((Finset.Icc 1 X).filter fun N => (q : ℕ) ^ 2 ∣ N).card +
        ((Finset.Icc 1 X).filter fun N => ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d).card := by
          rw [Finset.filter_or]
          exact Finset.card_union_le _ _
    _ ≤ X / (q : ℕ) ^ 2 + T.card * (X / (q : ℕ) ^ 2 + 1) := Nat.add_le_add hA hB
    _ ≤ (T.card + 1) * (X / (q : ℕ) ^ 2 + 1) := combined_bound_aux T X ((q : ℕ) ^ 2)


end LeanPool.DeadEnds
