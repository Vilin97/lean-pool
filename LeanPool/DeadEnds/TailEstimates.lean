/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/

import LeanPool.DeadEnds.RelevantPrimes

/-!
Asymptotic tail estimates that turn finite-prime counts into density bounds.
-/

namespace LeanPool.DeadEnds

lemma sqrt_bXb_div_X_small (b : ℕ) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (Nat.sqrt (b * X + b) : ℝ) / X < ε := by
  have h₃ : ∃ (X₀ : ℕ), (X₀ : ℝ) > 2 * (b : ℝ) / ε ^ 2 := by
    have h₄ : ∃ (n : ℕ), (2 * (b : ℝ) / ε ^ 2 : ℝ) < n := by
      obtain ⟨n, hn⟩ := exists_nat_gt (2 * (b : ℝ) / ε ^ 2)
      exact ⟨n, by linarith⟩
    obtain ⟨X₀, hX₀⟩ := h₄
    refine ⟨X₀, ?_⟩
    norm_cast at hX₀ ⊢
  obtain ⟨X₀, hX₀⟩ := h₃
  use max 1 X₀
  intro X hX
  have h₄ : X ≥ 1 := by
    have h₅ : max 1 X₀ ≥ 1 := by simp
    linarith
  have h₅ : (X : ℝ) ≥ 1 := by exact_mod_cast h₄
  have h₆ : (X : ℝ) ≥ (X₀ : ℝ) := by
    have h₇ : (max 1 X₀ : ℕ) ≥ X₀ := by simp
    have h₉ : (X : ℕ) ≥ X₀ := by linarith
    exact_mod_cast h₉
  have h₈ : (ε : ℝ) ^ 2 * (X : ℝ) > 2 * (b : ℝ) := by
    have h₁₀ : 0 < (ε : ℝ) ^ 2 := by positivity
    have h₁₁ : 0 < (ε : ℝ) ^ 2 := by positivity
    have h₁₂ : (ε : ℝ) ^ 2 * (X : ℝ) > (ε : ℝ) ^ 2 * (2 * (b : ℝ) / ε ^ 2) := by
      nlinarith
    have h₁₃ : (ε : ℝ) ^ 2 * (2 * (b : ℝ) / ε ^ 2) = 2 * (b : ℝ) := by
      field_simp [h₁₁.ne']
    linarith
  have h₉ : (b : ℝ) * X + b ≤ 2 * (b : ℝ) * X := by
    have h₁₂ : (b : ℝ) * (X : ℝ) ≥ (b : ℝ) := by
      nlinarith
    have h₁₃ : (b : ℝ) * (X : ℝ) + (b : ℝ) ≤ 2 * (b : ℝ) * (X : ℝ) := by
      nlinarith
    norm_cast at h₁₃ ⊢
  have h₁₀ : (b : ℝ) * X + b < (ε : ℝ) ^ 2 * (X : ℝ) ^ 2 := by
    have h₁₆ : (ε : ℝ) ^ 2 * (X : ℝ) ^ 2 > 2 * (b : ℝ) * (X : ℝ) := by
      nlinarith [sq_nonneg ((X : ℝ) - 1)]
    nlinarith
  have h₁₁ : (Nat.sqrt (b * X + b) : ℝ) < (ε : ℝ) * X := by
    have h₁₄ : (Nat.sqrt (b * X + b) : ℕ) * (Nat.sqrt (b * X + b) : ℕ) ≤ (b * X + b) := by
      have h₁₅ : (Nat.sqrt (b * X + b)) * (Nat.sqrt (b * X + b)) ≤ (b * X + b) := by
        nlinarith [Nat.sqrt_le (b * X + b), Nat.lt_succ_sqrt (b * X + b)]
      exact h₁₅
    have h₁₈ : (Nat.sqrt (b * X + b) : ℕ) < (ε : ℝ) * X := by
      by_contra h
      have h₁₉ : (ε : ℝ) * X ≤ (Nat.sqrt (b * X + b) : ℕ) := by
        norm_num at h ⊢;
        (try linarith)
      have h₂₀ : ((ε : ℝ) * X) ^ 2 ≤ ((Nat.sqrt (b * X + b) : ℕ) : ℝ) ^ 2 := by
        have h₂₂ : ((ε : ℝ) * X) ^ 2 ≤ ((Nat.sqrt (b * X + b) : ℕ) : ℝ) ^ 2 := by
          gcongr
        exact h₂₂
      have h₂₂ : ((Nat.sqrt (b * X + b) : ℕ) : ℝ) * ((Nat.sqrt (b * X + b) : ℕ) : ℝ) ≤ (b * X +
          b : ℝ) := by
        have h₂₃ : (Nat.sqrt (b * X + b) : ℕ) * (Nat.sqrt (b * X + b) : ℕ) ≤ (b * X + b) := h₁₄
        norm_cast at h₂₃ ⊢
      linarith
    have h₁₉ : (Nat.sqrt (b * X + b) : ℝ) < (ε : ℝ) * X := by
      norm_cast at h₁₈ ⊢
    exact h₁₉
  have h₁₂ : (Nat.sqrt (b * X + b) : ℝ) / X < ε := by
    have h₁₃ : 0 < (X : ℝ) := by
      linarith
    have h₁₅ : (Nat.sqrt (b * X + b) : ℝ) / X < ε := by
      calc
        (Nat.sqrt (b * X + b) : ℝ) / X < ((ε : ℝ) * X) / X := by gcongr
        _ = (ε : ℝ) := by
          field_simp [h₁₃.ne']
    exact h₁₅
  exact h₁₂

lemma combine_violation_bounds (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (y : ℕ) (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (hyb : y ≥ b)
    (X : ℕ) (hX : 0 < X)
    (ε : ℝ) (_hε : 0 < ε)
    (htail : (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) < ε / 2)
    (hsqrt : (T.card + 1 : ℝ) * ((Nat.sqrt (b * X + b) : ℝ) / X) < ε / 2) :
    (((Finset.Icc 1 X).filter fun N =>
      ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N +
          d)).card : ℝ) / X < ε := by
  have hX_pos : (0 : ℝ) < X := Nat.cast_pos.mpr hX
  have hbound := violation_count_bound b hb T hT S y hy hyb X
  calc (((Finset.Icc 1 X).filter fun N =>
      ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card : ℝ) / X
      ≤ ((T.card + 1 : ℝ) * X * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
          ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) +
         (T.card + 1 : ℝ) * (Nat.sqrt (b * X + b) : ℝ)) / X := by
        apply div_le_div_of_nonneg_right hbound (le_of_lt hX_pos)
    _ = (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) +
        (T.card + 1 : ℝ) * ((Nat.sqrt (b * X + b) : ℝ) / X) := by
        have hXne : (X : ℝ) ≠ 0 := ne_of_gt hX_pos
        field_simp [hXne]
    _ < ε / 2 + ε / 2 := add_lt_add htail hsqrt
    _ = ε := add_halves ε

lemma tail_sum_antitone (y y' : ℕ) (h : y ≤ y') :
    ∑' (p : {q : Nat.Primes // (q : ℕ) > y'}), 1 / (((p : Nat.Primes) : ℕ) : ℝ) ^ 2 ≤
    ∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (((p : Nat.Primes) : ℕ) : ℝ) ^ 2 := by
  let e : {q : Nat.Primes // (q : ℕ) > y'} → {q : Nat.Primes // (q : ℕ) > y} :=
    fun ⟨q, hq⟩ => ⟨q, lt_of_le_of_lt h hq⟩
  apply Summable.tsum_le_tsum_of_inj e
  · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have : a = b := by
      have := congrArg Subtype.val hab
      simp only at this
      exact this
    exact Subtype.ext this
  · intro c _
    positivity
  · intro i
    rfl
  · exact primes_summable_one_div_sq.subtype _
  · exact primes_summable_one_div_sq.subtype _

/-- Choose y large enough that the tail sum is small enough, and y ≥ b.
    Uses prime_tail_sum_small with ε/(2*(|T|+1)). -/
lemma choose_y_for_tail (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℕ, y ≥ b ∧
      (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
          ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) < ε / 2 := by
  have hK : (0 : ℝ) < T.card + 1 := by positivity
  have hε' : 0 < ε / (2 * (T.card + 1)) := by positivity
  obtain ⟨y₁, hy₁⟩ := prime_tail_sum_small (ε / (2 * (T.card + 1))) hε'
  use max b y₁
  constructor
  · exact le_max_left b y₁
  · calc (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > max b y₁}), 1 / (
      ((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
      ≤ (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > y₁}), 1 / (
          ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left
          · exact tail_sum_antitone y₁ (max b y₁) (le_max_right b y₁)
          · linarith
    _ < (T.card + 1 : ℝ) * (ε / (2 * (T.card + 1))) := by
          apply mul_lt_mul_of_pos_left hy₁ hK
    _ = ε / 2 := by field_simp

/-- Choose X₀ large enough that the √(bX+b)/X term is small and X₀ > 0. -/
lemma choose_X_for_sqrt (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 0 < X₀ ∧ ∀ X ≥ X₀,
      (T.card + 1 : ℝ) * ((Nat.sqrt (b * X + b) : ℝ) / X) < ε / 2 := by
  have hc : (0 : ℝ) < T.card + 1 := by positivity
  set ε' := ε / (2 * (T.card + 1)) with hε'_def
  have hε' : 0 < ε' := by positivity
  obtain ⟨X₀', hX₀'⟩ := sqrt_bXb_div_X_small b hb ε' hε'
  use max X₀' 1
  constructor
  · omega
  · intro X hX
    have hXge : X ≥ X₀' := le_trans (le_max_left _ _) hX
    have hbound := hX₀' X hXge
    calc (T.card + 1 : ℝ) * ((Nat.sqrt (b * X + b) : ℝ) / X)
        < (T.card + 1) * ε' := by nlinarith [hbound]
      _ = (T.card + 1) * (ε / (2 * (T.card + 1))) := by rfl
      _ = ε / 2 := by field_simp

/-- The "violation count" (N failing for primes outside S) divided by X vanishes
    as S grows and X gets large. -/
lemma error_term_vanishes (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℕ, ∃ X₁ : ℕ, ∀ S : Finset Nat.Primes, (∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) →
      ∀ X ≥ X₁,
        (((Finset.Icc 1 X).filter fun N =>
          ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N +
              d)).card : ℝ) / X < ε := by
  obtain ⟨y, hyb, htail⟩ := choose_y_for_tail b hb T ε hε
  obtain ⟨X₀, hX₀_pos, hsqrt⟩ := choose_X_for_sqrt b hb T ε hε
  use y, X₀
  intro S hS X hX
  have hX_pos : 0 < X := Nat.lt_of_lt_of_le hX₀_pos hX
  exact combine_violation_bounds b hb T _hT S y hS hyb X hX_pos ε hε htail (hsqrt X hX)


lemma exists_large_for_ratio (M : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (M : ℝ) / X < δ := by
  have h₁ : 0 ≤ (M : ℝ) / δ := by
    positivity
  have h₂ : ∃ X₀ : ℕ, ∀ X ≥ X₀, (M : ℝ) / X < δ := by
    obtain ⟨X₀, hX₀⟩ := exists_nat_gt ((M : ℝ) / δ)
    use X₀
    intro X hX
    have h₃ : (X : ℝ) ≥ (X₀ : ℝ) := by
      exact_mod_cast hX
    have h₅ : 0 < (X : ℝ) := by
      have h₅₅ : (X : ℝ) > 0 := by linarith
      exact h₅₅
    have h₆ : (M : ℝ) / X < δ := by
      have h₆₁ : (M : ℝ) < (X : ℝ) * δ := by
        calc
          (M : ℝ) = ((M : ℝ) / δ) * δ := by
            field_simp [hδ.ne']
          _ < (X : ℝ) * δ := by
            nlinarith
      have h₆₂ : 0 < (X : ℝ) := h₅
      have h₆₃ : (M : ℝ) / X < δ := by
        calc
          (M : ℝ) / X < ((X : ℝ) * δ) / X := by
            gcongr
          _ = δ := by
            field_simp [h₆₂.ne']
      exact h₆₃
    exact h₆
  exact h₂

/-- Lower bound: for large X, C(X)/X ≥ D(b,T) - ε.
    The count equals the count for all primes up to some bound, which is close to X·D(b,T).
    Uses sum of X/p² for primes p > y, which is O(X/y). -/
lemma count_lower_bound_estimate (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (countJointSquarefree b T X : ℝ) / X ≥ jointSquarefreeDensity b T - ε := by
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨y, X₁, hy⟩ := error_term_vanishes b hb T hT (ε / 2) hε2
  let S := primesUpTo y
  obtain ⟨X₂, hX₂⟩ := exists_large_for_ratio (primeSquareProduct S) (ε / 2) hε2
  use max X₁ (max X₂ 1)
  intro X hX
  have hX1 : X ≥ X₁ := le_trans (le_max_left _ _) hX
  have hX2 : X ≥ X₂ := le_trans (le_trans (le_max_left _ _) (le_max_right X₁ _)) hX
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1)
    (le_trans (le_trans (le_max_right _ _) (le_max_right X₁ _)) hX)
  have hS : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S := mem_primesUpTo y
  have hviol := hy S hS X hX1
  have hM := hX₂ X hX2
  have hcomb := combine_bounds_lower b hb T hT S X hXpos (ε / 2) (ε / 2) hviol hM
  linarith

theorem finite_count_upper_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    (countJointSquarefree b T X : ℝ) ≤
      (X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T + ∏ p ∈ S, (p : ℕ) ^ 2 := by
  have h1 := count_upper_bound_via_finite b hb T hT S X
  have h2 := count_finite_prime_approx b hb T hT S X
  set count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card with hcount
  set prodMu := ∏ p ∈ S, localDensityFactor (p : ℕ) b T with hprodMu
  set prodPsq : ℝ := ∏ p ∈ S, (p : ℕ) ^ 2 with hprodPsq
  have h3 : (count : ℝ) ≤ (X : ℝ) * prodMu + prodPsq := by
    have := abs_sub_le_iff.mp h2
    linarith [this.1, this.2]
  have h4 : ((∏ p ∈ S, (p : ℕ) ^ 2 : ℕ) : ℝ) = prodPsq := by
    rw [hprodPsq, Nat.cast_prod]
    congr 1
    ext p
    push_cast
    ring
  calc (countJointSquarefree b T X : ℝ) ≤ (count : ℝ) := h1
    _ ≤ (X : ℝ) * prodMu + prodPsq := h3
    _ = (X : ℝ) * prodMu + (∏ p ∈ S, (p : ℕ) ^ 2 : ℕ) := by rw [h4]

lemma finite_prod_lt_density_add (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (ε : ℝ) (_hε : 0 < ε)
    (h : |∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T| < ε) :
    ∏ p ∈ S, localDensityFactor (p : ℕ) b T < jointSquarefreeDensity b T + ε := by
  have h₁ : ∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T < ε := by
    exact (abs_lt.mp h).2
  linarith

lemma combine_upper_bounds (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) (ε : ℝ) (_hε : 0 < ε) (hX : 0 < X)
    (M : ℕ) (_hM : M = ∏ p ∈ S, (p : ℕ) ^ 2)
    (hcount : (countJointSquarefree b T X : ℝ) ≤
      (X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T + M)
    (hprod : ∏ p ∈ S, localDensityFactor (p : ℕ) b T < jointSquarefreeDensity b T + ε / 2)
    (hratio : (M : ℝ) / X < ε / 2) :
    (countJointSquarefree b T X : ℝ) / X ≤ jointSquarefreeDensity b T + ε := by
  have h_div : (countJointSquarefree b T X : ℝ) / X ≤ (∏ p ∈ S, localDensityFactor (p : ℕ) b T) + (
      M : ℝ) / X := by
    have h₁ : 0 < (X : ℝ) := by exact_mod_cast hX
    have h₂ : (countJointSquarefree b T X : ℝ) / X ≤ ((X : ℝ) * ∏ p ∈ S, localDensityFactor (
        p : ℕ) b T + M) / X := by
      have h₄ : (countJointSquarefree b T X : ℝ) / X ≤ ((X : ℝ) * ∏ p ∈ S, localDensityFactor (
          p : ℕ) b T + M) / X := by
        calc
          (countJointSquarefree b T X : ℝ) / X ≤ ((X : ℝ) * ∏ p ∈ S, localDensityFactor (
              p : ℕ) b T + M) / X := by
            gcongr
          _ = ((X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T + M) / X := by rfl
      exact h₄
    have h₃ : ((X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T + M) / X = (∏ p ∈ S,
        localDensityFactor (p : ℕ) b T) + (M : ℝ) / X := by
      field_simp [h₁.ne']
    rw [h₃] at h₂
    exact h₂
  have h_final : (countJointSquarefree b T X : ℝ) / X ≤ jointSquarefreeDensity b T + ε := by
    linarith
  exact h_final

lemma exists_finite_prime_set (y : ℕ) :
    ∃ S : Finset Nat.Primes, (∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) := by
  have hfin : {p : Nat.Primes | (p : ℕ) ≤ y}.Finite := by
    have heq : {p : Nat.Primes | (p : ℕ) ≤ y} = Subtype.val ⁻¹' (Set.Iic y) := rfl
    rw [heq]
    apply Set.Finite.preimage _ (Set.finite_Iic y)
    exact Set.injOn_of_injective Subtype.val_injective
  use hfin.toFinset
  intro p hp
  rw [Set.Finite.mem_toFinset]
  exact hp

/-- Upper bound: for large X, C(X)/X ≤ D(b,T) + ε. -/
lemma count_upper_bound_direct (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (countJointSquarefree b T X : ℝ) / X ≤ jointSquarefreeDensity b T + ε := by
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨y, hy⟩ := finite_product_converges_to_density b hb T hT (ε / 2) hε2
  obtain ⟨S, hS⟩ := exists_finite_prime_set y
  have hprod : |∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T| < ε / 2 :=
    hy S hS
  let M : ℕ := ∏ p ∈ S, (p : ℕ) ^ 2
  obtain ⟨X₀, hX₀⟩ := exists_large_for_ratio M (ε / 2) hε2
  use max X₀ 1
  intro X hX
  have hX₀' : X ≥ X₀ := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℕ) < X := Nat.one_pos.trans_le hX1
  have hcount : (countJointSquarefree b T X : ℝ) ≤
      (X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T + M :=
    finite_count_upper_bound b hb T hT S X
  have hratio : (M : ℝ) / X < ε / 2 := hX₀ X hX₀'
  have hprod' : ∏ p ∈ S, localDensityFactor (p : ℕ) b T < jointSquarefreeDensity b T + ε / 2 :=
    finite_prod_lt_density_add b hb T hT S (ε / 2) hε2 hprod
  exact combine_upper_bounds b hb T hT S X ε hε hXpos M rfl hcount hprod' hratio

/-- The joint square-free density for subset T equals jointSquarefreeDensity b T.
    Uses Metric.tendsto_atTop: convergence iff for all ε > 0, eventually |f(n) - L| < ε.
    Lower bound: count_lower_bound_estimate.
    Upper bound: count_upper_bound_direct. -/
lemma joint_density_eq_euler_product (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b) :
    Filter.Tendsto
      (fun X : ℕ => (countJointSquarefree b T X : ℝ) / (X : ℝ))
      Filter.atTop (nhds (jointSquarefreeDensity b T)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨X₁, hX₁⟩ := count_lower_bound_estimate b hb T hT (ε/2) (by linarith)
  obtain ⟨X₂, hX₂⟩ := count_upper_bound_direct b hb T hT (ε/2) (by linarith)
  use max X₁ X₂
  intro X hX
  rw [Real.dist_eq]
  have hX₁' : X ≥ X₁ := le_of_max_le_left hX
  have hX₂' : X ≥ X₂ := le_of_max_le_right hX
  have lower := hX₁ X hX₁'
  have upper := hX₂ X hX₂'
  rw [abs_sub_lt_iff]
  constructor <;> linarith


end LeanPool.DeadEnds
