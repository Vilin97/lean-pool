/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.ZMod.Coprime

/-!
# LeanPool.LatticeTriangle.Solution
-/

/-- The largest prime factor of `n`, or `0` if `n` has no prime factors (i.e. `n ≤ 1`). -/
def largestPrimeFactor (n : ℕ) : ℕ :=
  WithBot.unbotD 0 n.primeFactors.max

/-- The *truncated obtuse region* `H_n(η)`: integer pairs `(p, q)` with `η * n ≤ p`,
`η * n ≤ q`, `p + q < n / 2`, and `gcd(p, q, n) = 1`. -/
def truncatedObtuseRegion (n : ℕ) (η : ℝ) : Set (ℤ × ℤ) :=
  {pq : ℤ × ℤ |
    η * (n : ℝ) ≤ (pq.1 : ℝ) ∧
    η * (n : ℝ) ≤ (pq.2 : ℝ) ∧
    (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 ∧
    Int.gcd (Int.gcd pq.1 pq.2) (n : ℤ) = 1}

/-- The image in `ZMod n` of the integer interval `{1, …, m}`. -/
def intervalSet (n : ℕ) (m : ℕ) : Set (ZMod n) :=
  {x : ZMod n | 1 ≤ ZMod.val x ∧ ZMod.val x ≤ m}

instance intervalSetDecidableMem (n : ℕ) (m : ℕ) :
    DecidablePred (· ∈ intervalSet n m) :=
  fun _ => instDecidableAnd

/-- The counting function `S(p, q)`: the number of units `a ∈ (ZMod n)ˣ` for which both `a * p`
and `a * q` land in the initial intervals `intervalSet n (2p-1)` and `intervalSet n (2q-1)`. -/
def countingFunctionS (n : ℕ) (p q : ℤ) : ℕ :=
  if h : n = 0 then 0
  else
    haveI : NeZero n := ⟨h⟩
    let mp := (2 * p - 1).toNat
    let mq := (2 * q - 1).toNat
    (Finset.univ.filter fun a : (ZMod n)ˣ =>
      (a.val * (p : ZMod n)) ∈ intervalSet n mp ∧
      (a.val * (q : ZMod n)) ∈ intervalSet n mq).card

/-- The *bad pairs*: pairs of `truncatedObtuseRegion n η` with `gcd(q, P⁺(n)) = 1` and
`countingFunctionS n p q < 5`, where `P⁺(n) = largestPrimeFactor n`. -/
def badPairsSet (n : ℕ) (η : ℝ) : Set (ℤ × ℤ) :=
  {pq ∈ truncatedObtuseRegion n η |
    Int.gcd pq.2 (largestPrimeFactor n : ℤ) = 1 ∧
    countingFunctionS n pq.1 pq.2 < 5}

lemma truncatedObtuseRegion_subset_box (n : ℕ) (η : ℝ) :
    truncatedObtuseRegion n η ⊆
      (Set.Icc (⌈η * (n : ℝ)⌉ - 1 : ℤ) (⌊(n : ℝ) / 2 - η * (n : ℝ)⌋ : ℤ)) ×ˢ
      (Set.Icc (⌈η * (n : ℝ)⌉ - 1 : ℤ) (⌊(n : ℝ) / 2 - η * (n : ℝ)⌋ : ℤ)) := by
  intro ⟨p, q⟩ h
  simp only [truncatedObtuseRegion, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc] at h ⊢
  have h₁ : (η * (n : ℝ) : ℝ) ≤ (p : ℝ) := h.1
  have h₂ : (η * (n : ℝ) : ℝ) ≤ (q : ℝ) := h.2.1
  have h₃ : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 := h.2.2.1
  have hc : ⌈η * (n : ℝ)⌉ ≤ p + 1 ∧ ⌈η * (n : ℝ)⌉ ≤ q + 1 := by
    constructor <;> · rw [Int.ceil_le]; push_cast; linarith
  have hp : (p : ℤ) ≤ ⌊(n : ℝ) / 2 - η * (n : ℝ)⌋ := by
    rw [Int.le_floor]; linarith
  have hq : (q : ℤ) ≤ ⌊(n : ℝ) / 2 - η * (n : ℝ)⌋ := by
    rw [Int.le_floor]; linarith
  exact ⟨⟨by omega, hp⟩, ⟨by omega, hq⟩⟩

lemma truncatedObtuseRegion_finite (n : ℕ) (η : ℝ) :
    (truncatedObtuseRegion n η).Finite :=
  ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).subset
    (truncatedObtuseRegion_subset_box n η)

lemma badPairsSet_finite (n : ℕ) (η : ℝ) :
    (badPairsSet n η).Finite := by
  exact (truncatedObtuseRegion_finite n η).subset (fun _ h => h.1)

lemma coprime_triangle_subset_truncatedObtuseRegion (n : ℕ) (η : ℝ) :
    {pq : ℤ × ℤ |
      η * (n : ℝ) ≤ (pq.1 : ℝ) ∧
      η * (n : ℝ) ≤ (pq.2 : ℝ) ∧
      (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 ∧
      Int.gcd pq.1 pq.2 = 1}
    ⊆ truncatedObtuseRegion n η := by
  intro ⟨p, q⟩ h
  simp only [Set.mem_setOf_eq, truncatedObtuseRegion] at h ⊢
  have h₁ : η * (n : ℝ) ≤ (p : ℝ) := h.1
  have h₂ : η * (n : ℝ) ≤ (q : ℝ) := h.2.1
  have h₃ : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 := h.2.2.1
  have h₄ : Int.gcd p q = 1 := h.2.2.2
  have h₅ : Int.gcd (Int.gcd p q) (n : ℤ) = 1 := by
    have h₅₁ : (Int.gcd p q : ℤ) = 1 := by exact_mod_cast h₄
    have h₅₂ : Int.gcd (Int.gcd p q) (n : ℤ) = 1 := by
      rw [h₅₁]
      simp
    exact h₅₂
  exact ⟨h₁, h₂, h₃, h₅⟩

lemma coprime_triangle_finite (n : ℕ) (η : ℝ) :
    {pq : ℤ × ℤ |
      η * (n : ℝ) ≤ (pq.1 : ℝ) ∧
      η * (n : ℝ) ≤ (pq.2 : ℝ) ∧
      (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 ∧
      Int.gcd pq.1 pq.2 = 1}.Finite := by
  exact Set.Finite.subset
    (truncatedObtuseRegion_finite n η)
    (coprime_triangle_subset_truncatedObtuseRegion n η)

lemma sum_lt_half_zero_case (p q : ℤ)
    (hp : p ≤ ⌊((0 : ℕ) : ℝ) / 6⌋) (hq : q ≤ ⌊((0 : ℕ) : ℝ) / 6⌋)
    (hgcd : Int.gcd p q = 1) :
    (p : ℝ) + (q : ℝ) < ((0 : ℕ) : ℝ) / 2 := by
  have h₁ : ⌊((0 : ℕ) : ℝ) / 6⌋ = 0 := by
    norm_num [Int.floor_eq_iff]
  have h₂ : p ≤ 0 := by
    have h₃ : (p : ℤ) ≤ ⌊((0 : ℕ) : ℝ) / 6⌋ := hp
    have h₄ : ⌊((0 : ℕ) : ℝ) / 6⌋ = 0 := h₁
    have h₅ : (p : ℤ) ≤ 0 := by
      simpa [h₄] using h₃
    exact_mod_cast h₅
  have h₃ : q ≤ 0 := by
    have h₄ : (q : ℤ) ≤ ⌊((0 : ℕ) : ℝ) / 6⌋ := hq
    have h₅ : ⌊((0 : ℕ) : ℝ) / 6⌋ = 0 := h₁
    have h₆ : (q : ℤ) ≤ 0 := by
      simpa [h₅] using h₄
    exact_mod_cast h₆
  have h₄ : (p : ℝ) + (q : ℝ) < ((0 : ℕ) : ℝ) / 2 := by
    have h₇ : Int.gcd p q = 1 := hgcd
    have h₈ : (p : ℝ) + (q : ℝ) < ((0 : ℕ) : ℝ) / 2 := by
      have h₉ : p < 0 ∨ q < 0 := by
        by_contra! h
        have h₁₀ : p = 0 := by
          linarith
        have h₁₁ : q = 0 := by
          linarith
        have h₁₂ : Int.gcd p q = 0 := by
          simp [h₁₀, h₁₁]
        rw [h₁₂] at h₇
        norm_num at h₇
      cases h₉ with
      | inl h₉ =>
        have h₁₀ : (p : ℝ) < 0 := by exact_mod_cast h₉
        have h₁₁ : (q : ℝ) ≤ 0 := by exact_mod_cast h₃
        have h₁₂ : (p : ℝ) + (q : ℝ) < 0 := by linarith
        norm_num at h₁₂ ⊢
        linarith
      | inr h₉ =>
        have h₁₀ : (q : ℝ) < 0 := by exact_mod_cast h₉
        have h₁₁ : (p : ℝ) ≤ 0 := by exact_mod_cast h₂
        have h₁₂ : (p : ℝ) + (q : ℝ) < 0 := by linarith
        norm_num at h₁₂ ⊢
        linarith
    exact h₈
  exact h₄

lemma sum_lt_half_pos_case (n : ℕ) (p q : ℤ) (hn : 1 ≤ n)
    (hp : p ≤ ⌊(n : ℝ) / 6⌋) (hq : q ≤ ⌊(n : ℝ) / 6⌋) :
    (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 := by
  have h_p_le : (p : ℝ) ≤ (n : ℝ) / 6 := by
    calc (p : ℝ) ≤ (⌊(n : ℝ) / 6⌋ : ℤ) := by exact_mod_cast hp
      _ ≤ (n : ℝ) / 6 := Int.floor_le _
  have h_q_le : (q : ℝ) ≤ (n : ℝ) / 6 := by
    calc (q : ℝ) ≤ (⌊(n : ℝ) / 6⌋ : ℤ) := by exact_mod_cast hq
      _ ≤ (n : ℝ) / 6 := Int.floor_le _
  have h_n_pos : (n : ℝ) > 0 := by exact_mod_cast hn
  have h_final : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 := by nlinarith
  assumption

lemma sum_lt_half_of_le_floor_sixth (n : ℕ) (p q : ℤ)
    (hp : p ≤ ⌊(n : ℝ) / 6⌋) (hq : q ≤ ⌊(n : ℝ) / 6⌋)
    (hgcd : Int.gcd p q = 1) :
    (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact sum_lt_half_zero_case p q hp hq hgcd
  · exact sum_lt_half_pos_case n p q hn hp hq

lemma rectangle_coprime_subset_target (n : ℕ) (η : ℝ) :
    {pq : ℤ × ℤ |
      (⌈η * (n : ℝ)⌉ : ℤ) ≤ pq.1 ∧ pq.1 ≤ (⌊(n : ℝ) / 6⌋ : ℤ) ∧
      (⌈η * (n : ℝ)⌉ : ℤ) ≤ pq.2 ∧ pq.2 ≤ (⌊(n : ℝ) / 6⌋ : ℤ) ∧
      Int.gcd pq.1 pq.2 = 1}
    ⊆ {pq : ℤ × ℤ |
      η * (n : ℝ) ≤ (pq.1 : ℝ) ∧
      η * (n : ℝ) ≤ (pq.2 : ℝ) ∧
      (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 ∧
      Int.gcd pq.1 pq.2 = 1} := by
  intro ⟨p, q⟩ hpq
  simp only [Set.mem_setOf_eq] at hpq ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hpq
  refine ⟨?_, ?_, ?_, h5⟩
  · exact le_trans (Int.le_ceil _) (Int.cast_le.mpr h1)
  · exact le_trans (Int.le_ceil _) (Int.cast_le.mpr h3)
  · exact sum_lt_half_of_le_floor_sixth n p q h2 h4 h5

lemma Int_Icc_ncard (a b : ℤ) :
    (Set.Icc a b).ncard = (b + 1 - a).toNat := by
  have h₁ : (Set.Icc a b : Set ℤ) = ↑(Finset.Icc a b) := by simp
  have h₂ : (Set.Icc a b : Set ℤ).ncard = (Finset.Icc a b : Finset ℤ).card := by
    rw [h₁, Set.ncard_coe_finset]
  have h₃ : (Finset.Icc a b : Finset ℤ).card = (b + 1 - a).toNat := by simp
  have h₄ : (Set.Icc a b).ncard = (b + 1 - a).toNat := by simp_all
  assumption

lemma eta_n_plus_one_le_n_div_six (η : ℝ) (_hη_pos : 0 < η) (hη_lt : η < 1 / 6) :
    ∃ (N₀ : ℕ), ∀ n : ℕ, N₀ ≤ n →
      η * (n : ℝ) + 1 ≤ (n : ℝ) / 6 := by
  have h_delta_pos : 0 < (1 / 6 : ℝ) - η := by simp_all
  set N₀ := ⌈(1 : ℝ) / ((1 / 6 : ℝ) - η)⌉₊ with hN₀_def
  use N₀
  intro n hn
  have h₂ : (n : ℝ) ≥ (1 : ℝ) / ((1 / 6 : ℝ) - η) := by simp_all
  have h₄ : ((1 / 6 : ℝ) - η) * (n : ℝ) ≥ 1 := by
    have := mul_le_mul_of_nonneg_left h₂ (le_of_lt h_delta_pos)
    rw [mul_div_cancel₀] at this
    · linarith
    · exact ne_of_gt h_delta_pos
  have h₅ : η * (n : ℝ) + 1 ≤ (n : ℝ) / 6 := by nlinarith
  exact h₅

lemma int_expr_real_lower_bound (η : ℝ) (n : ℕ) :
    (n : ℝ) / 6 - η * (n : ℝ) - 1 <
      ((⌊(n : ℝ) / 6⌋ + 1 - ⌈η * (n : ℝ)⌉ : ℤ) : ℝ) := by
  have h₁ : (n : ℝ) / 6 - 1 < (⌊(n : ℝ) / 6⌋ : ℝ) := by
    have h₁ : (n : ℝ) / 6 - 1 < (⌊(n : ℝ) / 6⌋ : ℝ) := by
      have h₂ : (n : ℝ) / 6 - 1 < (⌊(n : ℝ) / 6⌋ : ℝ) := by
        linarith [Int.sub_one_lt_floor ((n : ℝ) / 6)]
      exact h₂
    exact h₁
  have h₂ : (⌈(η * (n : ℝ))⌉ : ℝ) < (η * (n : ℝ)) + 1 := by
    have h₃ : (⌈(η * (n : ℝ))⌉ : ℝ) < (η * (n : ℝ)) + 1 := by
      have h₄ : (⌈(η * (n : ℝ))⌉ : ℝ) < (η * (n : ℝ)) + 1 := by
        linarith [Int.ceil_lt_add_one (η * (n : ℝ))]
      exact h₄
    exact h₃
  have h₃ : (n : ℝ) / 6 - η * (n : ℝ) - 1 < ((⌊(n : ℝ) / 6⌋ + 1 - ⌈η * (n : ℝ)⌉ : ℤ) : ℝ) := by
    have h₄ : (n : ℝ) / 6 - η * (n : ℝ) - 1 < ((⌊(n : ℝ) / 6⌋ + 1 - ⌈η * (n : ℝ)⌉ : ℤ) : ℝ) := by
      have h₆ : ((⌊(n : ℝ) / 6⌋ + 1 - ⌈η * (n : ℝ)⌉ : ℤ) : ℝ) = (⌊(n : ℝ) / 6⌋ : ℝ) + 1 - (⌈(η *
        (n : ℝ))⌉ : ℝ) := by
        norm_cast
      linarith
    exact h₄
  exact h₃

lemma ceil_le_floor_for_large_n (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1 / 6) :
    ∃ (N₀ : ℕ), ∀ n : ℕ, N₀ ≤ n →
      (⌈η * (n : ℝ)⌉ : ℤ) ≤ (⌊(n : ℝ) / 6⌋ : ℤ) := by
  obtain ⟨N₀, hN₀⟩ := eta_n_plus_one_le_n_div_six η hη_pos hη_lt
  exact ⟨N₀, fun n hn => Int.le_floor.mpr (le_of_lt (Int.ceil_lt_add_one _) |>.trans (hN₀ n hn))⟩

lemma int_expr_nonneg_for_large_n (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1 / 6) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (0 : ℤ) ≤ (⌊(n : ℝ) / 6⌋ + 1 - ⌈η * (n : ℝ)⌉ : ℤ) := by
  obtain ⟨N₀, hN₀⟩ := ceil_le_floor_for_large_n η hη_pos hη_lt
  exact ⟨N₀, fun n hn => by linarith [hN₀ n hn]⟩

lemma half_bound_for_large_n (η : ℝ) (_hη_pos : 0 < η) (hη_lt : η < 1 / 6) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ((1 / 6 - η) / 2) * (n : ℝ) ≤ (1 / 6 - η) * (n : ℝ) - 1 := by
  have h : 0 < (1 / 6 : ℝ) - η := by
    simp_all
  have h_exists_N₀ : ∃ (N₀ : ℕ), (N₀ : ℝ) ≥ (2 : ℝ) / ((1 / 6 : ℝ) - η) := by
    exact ⟨⌈(2 : ℝ) / ((1 / 6 : ℝ) - η)⌉₊, by exact_mod_cast Nat.le_ceil _⟩
  obtain ⟨N₀, hN₀⟩ := h_exists_N₀
  use N₀
  intro n hn
  have h₁ : (n : ℝ) ≥ (N₀ : ℝ) := by
    simp_all
  have h₂ : (n : ℝ) ≥ (2 : ℝ) / ((1 / 6 : ℝ) - η) := by
    nlinarith
  have h₃ : ((1 / 6 : ℝ) - η) * (n : ℝ) ≥ 2 := by
    have := mul_le_mul_of_nonneg_left h₂ (le_of_lt h)
    rw [mul_div_cancel₀] at this
    · linarith
    · exact ne_of_gt h
  have h₄ : ((1 / 6 - η) / 2) * (n : ℝ) ≤ (1 / 6 - η) * (n : ℝ) - 1 := by
    nlinarith
  assumption

lemma interval_toNat_lower_bound (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1 / 6) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ((1 / 6 - η) / 2) * (n : ℝ) ≤
        ((⌊(n : ℝ) / 6⌋ + 1 - ⌈η * (n : ℝ)⌉ : ℤ).toNat : ℝ) := by
  obtain ⟨N₁, hN₁⟩ := int_expr_nonneg_for_large_n η hη_pos hη_lt
  obtain ⟨N₂, hN₂⟩ := half_bound_for_large_n η hη_pos hη_lt
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ := hN₁ n (le_of_max_le_left hn)
  have hn₂ := hN₂ n (le_of_max_le_right hn)
  have h_real_lb := int_expr_real_lower_bound η n
  have h_nonneg := hn₁
  set z := (⌊(n : ℝ) / 6⌋ + 1 - ⌈η * (n : ℝ)⌉ : ℤ) with hz_def
  have h_cast : (z.toNat : ℝ) = (z : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg h_nonneg
  rw [h_cast]
  calc ((1 / 6 - η) / 2) * (n : ℝ)
      ≤ (1 / 6 - η) * (n : ℝ) - 1 := hn₂
    _ = (n : ℝ) / 6 - η * (n : ℝ) - 1 := by ring
    _ ≤ ((⌊(n : ℝ) / 6⌋ + 1 - ⌈η * (n : ℝ)⌉ : ℤ) : ℝ) := le_of_lt h_real_lb

theorem interval_ncard_lower_bound (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1 / 6) :
    ∃ (N₀ : ℕ), ∀ n : ℕ, N₀ ≤ n →
      ((1 / 6 - η) / 2) * (n : ℝ) ≤
        ((Set.Icc (⌈η * (n : ℝ)⌉ : ℤ) (⌊(n : ℝ) / 6⌋ : ℤ)).ncard : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := interval_toNat_lower_bound η hη_pos hη_lt
  exact ⟨N₀, fun n hn => by
    rw [Int_Icc_ncard]
    exact hN₀ n hn⟩

lemma coprime_pairs_subset_product (A B : ℤ) :
    {pq : ℤ × ℤ |
      A ≤ pq.1 ∧ pq.1 ≤ B ∧
      A ≤ pq.2 ∧ pq.2 ≤ B ∧
      Int.gcd pq.1 pq.2 = 1} ⊆
    Set.Icc A B ×ˢ Set.Icc A B := by
  intro ⟨a, b⟩ h
  simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc] at h ⊢
  have h₁ : A ≤ a := h.1
  have h₂ : a ≤ B := h.2.1
  have h₃ : A ≤ b := h.2.2.1
  have h₄ : b ≤ B := h.2.2.2.1
  exact ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩

lemma coprime_pairs_finite (A B : ℤ) :
    {pq : ℤ × ℤ |
      A ≤ pq.1 ∧ pq.1 ≤ B ∧
      A ≤ pq.2 ∧ pq.2 ≤ B ∧
      Int.gcd pq.1 pq.2 = 1}.Finite := by
  have h₁ : {pq : ℤ × ℤ | A ≤ pq.1 ∧ pq.1 ≤ B ∧ A ≤ pq.2 ∧ pq.2 ≤ B ∧ Int.gcd pq.1 pq.2 = 1} ⊆
    Set.Icc (A, A) (B, B) := by
    intro ⟨x, y⟩ h
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Prod.le_def] at h ⊢
    constructor <;>
    (try constructor) <;>
    (try simp_all)
  have h₂ : Set.Finite (Set.Icc (A, A) (B, B)) := by
    apply Set.Finite.subset (Set.finite_mem_finset (Finset.Icc (A, A) (B, B)))
    intro ⟨x, y⟩ h
    simp only [Set.mem_Icc, Finset.mem_Icc, Prod.le_def] at h ⊢
    aesop
  exact Set.Finite.subset h₂ h₁

lemma sq_add_one_le (a : ℝ) : (a + 1) ^ 2 ≤ 5 / 4 * a ^ 2 + 5 := by
  nlinarith [sq_nonneg (a - 4)]

lemma inv_sq_le_inv_pred_mul (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / ((k - 1 : ℝ) * k) := by
  have h₁ : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h₃ : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have h₇ : (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / ((k - 1 : ℝ) * k) := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  exact h₇

lemma telescoping_sum_eq (N : ℕ) (hN : 3 ≤ N) :
    ∑ k ∈ Finset.Icc 3 N, (1 : ℝ) / ((k - 1 : ℝ) * k) = 1 / 2 - 1 / N := by
  have h₁ : ∀ n : ℕ, 3 ≤ n → ∑ k ∈ Finset.Icc 3 n, (1 : ℝ) / ((k - 1 : ℝ) * k) = 1 / 2 - 1 / n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num [Finset.sum_Icc_succ_top]
    | succ n hn IH =>
      cases n with
      | zero => contradiction
      | succ n =>
        cases n with
        | zero => contradiction
        | succ n =>
          cases n with
          | zero => contradiction
          | succ n =>
            simp_all [Finset.sum_Icc_succ_top, Nat.cast_succ]
            field_simp [Nat.cast_add_one_ne_zero]
            ring_nf
  have h₂ : ∑ k ∈ Finset.Icc 3 N, (1 : ℝ) / ((k - 1 : ℝ) * k) = 1 / 2 - 1 / N := by
    have h₃ := h₁ N hN
    exact h₃
  exact h₂

lemma tail_sum_le_half (N : ℕ) :
    ∑ k ∈ Finset.Icc 3 N, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / 2 := by
  by_cases hN : 3 ≤ N
  · calc ∑ k ∈ Finset.Icc 3 N, (1 : ℝ) / (k : ℝ) ^ 2
        ≤ ∑ k ∈ Finset.Icc 3 N, 1 / ((k - 1 : ℝ) * k) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
          exact inv_sq_le_inv_pred_mul k (by omega)
      _ = 1 / 2 - 1 / N := telescoping_sum_eq N hN
      _ ≤ 1 / 2 := by linarith [show (0 : ℝ) ≤ 1 / (N : ℝ) from by positivity]
  · have : Finset.Icc 3 N = ∅ := by
      simp [Finset.Icc_eq_empty_iff]
      omega
    simp [this]

lemma sum_Icc_split (N : ℕ) (hN : 2 ≤ N) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 2 N, f k = f 2 + ∑ k ∈ Finset.Icc 3 N, f k := by
  have h_main : Finset.Icc 2 N = {2} ∪ Finset.Icc 3 N := by
    ext x; simp [Finset.mem_Icc]; omega
  have h_sum : ∑ k ∈ Finset.Icc 2 N, f k = f 2 + ∑ k ∈ Finset.Icc 3 N, f k := by simp_all
  assumption

lemma sum_inv_sq_le_three_fourths (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 3 / 4 := by
  by_cases hN : 2 ≤ N
  · rw [sum_Icc_split N hN]
    have h1 : (1 : ℝ) / (2 : ℝ) ^ 2 = 1 / 4 := by norm_num
    have h2 : ∑ k ∈ Finset.Icc 3 N, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / 2 := tail_sum_le_half N
    linarith
  · have : Finset.Icc 2 N = ∅ := by
      push Not at hN
      exact Finset.Icc_eq_empty (by omega)
    simp [this]; norm_num

lemma multiples_finite (A B : ℤ) (m : ℕ) :
    {x : ℤ | A ≤ x ∧ x ≤ B ∧ (m : ℤ) ∣ x}.Finite := by
  have h : {x : ℤ | A ≤ x ∧ x ≤ B ∧ (m : ℤ) ∣ x} ⊆ Set.Icc A B := by
    intro x hx
    simp only [Set.mem_Icc, Set.mem_setOf_eq] at hx ⊢
    exact ⟨hx.1, hx.2.1⟩
  have h2 : (Set.Icc A B : Set ℤ).Finite := Set.finite_Icc A B
  exact Set.Finite.subset h2 h

lemma toNat_inj_of_nonneg (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a.toNat = b.toNat) : a = b := by
  have h₁ : (a.toNat : ℤ) = a := by
    rw [Int.toNat_of_nonneg ha]
  have h₂ : (b.toNat : ℤ) = b := by
    rw [Int.toNat_of_nonneg hb]
  have h₄ : a = b := by
    linarith
  exact h₄

lemma emod_eq_of_dvd (x₁ x₂ A : ℤ) (m : ℤ) (h₁ : m ∣ x₁) (h₂ : m ∣ x₂) :
    (x₁ - A) % m = (x₂ - A) % m := by
  have h₃ : (x₁ - A) % m = ((x₁ % m) - (A % m)) % m := by
    rw [Int.sub_emod]
  have h₄ : (x₂ - A) % m = ((x₂ % m) - (A % m)) % m := by
    rw [Int.sub_emod]
  have h₅ : x₁ % m = 0 := by
    exact Int.emod_eq_zero_of_dvd h₁
  have h₆ : x₂ % m = 0 := by
    exact Int.emod_eq_zero_of_dvd h₂
  rw [h₃, h₄, h₅, h₆]

lemma eq_of_ediv_eq_emod_eq (a b m : ℤ) (_hm : m ≠ 0)
    (hdiv : a / m = b / m) (hmod : a % m = b % m) : a = b := by
  have h₁ : a % m + m * (a / m) = a := Int.emod_add_mul_ediv a m
  have h₂ : b % m + m * (b / m) = b := Int.emod_add_mul_ediv b m
  have h₅ : a = b := by simp_all
  assumption

lemma shift_div_toNat_injOn (A B : ℤ) (m : ℕ) (hm : 0 < m) :
    Set.InjOn (fun x => ((x - A) / (m : ℤ)).toNat)
      {x : ℤ | A ≤ x ∧ x ≤ B ∧ (m : ℤ) ∣ x} := by
  intro x₁ hx₁ x₂ hx₂ heq
  simp only [Set.mem_setOf_eq] at hx₁ hx₂
  have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  have hm_pos : (0 : ℤ) < m := Int.natCast_pos.mpr hm
  have h1_nn : 0 ≤ x₁ - A := Int.sub_nonneg.mpr hx₁.1
  have h2_nn : 0 ≤ x₂ - A := Int.sub_nonneg.mpr hx₂.1
  have hq1 : 0 ≤ (x₁ - A) / (m : ℤ) := Int.ediv_nonneg h1_nn (le_of_lt hm_pos)
  have hq2 : 0 ≤ (x₂ - A) / (m : ℤ) := Int.ediv_nonneg h2_nn (le_of_lt hm_pos)
  have hdiv : (x₁ - A) / (m : ℤ) = (x₂ - A) / (m : ℤ) :=
    toNat_inj_of_nonneg _ _ hq1 hq2 heq
  have hmod : (x₁ - A) % (m : ℤ) = (x₂ - A) % (m : ℤ) :=
    emod_eq_of_dvd x₁ x₂ A (m : ℤ) hx₁.2.2 hx₂.2.2
  have hsub : x₁ - A = x₂ - A := eq_of_ediv_eq_emod_eq _ _ (m : ℤ) hm' hdiv hmod
  linarith

lemma shift_div_toNat_le (A B : ℤ) (m : ℕ) (hm : 0 < m) (x : ℤ)
    (hxA : A ≤ x) (hxB : x ≤ B) :
    ((x - A) / (m : ℤ)).toNat ≤ (B + 1 - A).toNat / m := by
  have h₁ : 0 ≤ (x - A : ℤ) := by linarith
  have h₂ : (x - A : ℤ) ≤ (B + 1 - A : ℤ) := by linarith
  have h₃ : 0 ≤ (B + 1 - A : ℤ) := by linarith
  have hm_pos_int : (0 : ℤ) < m := Int.natCast_pos.mpr hm
  have hq : 0 ≤ (x - A) / (m : ℤ) := Int.ediv_nonneg h₁ (le_of_lt hm_pos_int)
  have hxa_le : (x - A) / (m : ℤ) ≤ (B + 1 - A) / (m : ℤ) :=
    Int.ediv_le_ediv hm_pos_int h₂
  have hba_q : 0 ≤ (B + 1 - A) / (m : ℤ) := Int.ediv_nonneg h₃ (le_of_lt hm_pos_int)
  have key1 : ((x - A) / (m : ℤ)).toNat ≤ ((B + 1 - A) / (m : ℤ)).toNat :=
    Int.toNat_le_toNat hxa_le
  have key2 : ((B + 1 - A) / (m : ℤ)).toNat = (B + 1 - A).toNat / m := by
    have h_cast : (B + 1 - A : ℤ) = ((B + 1 - A).toNat : ℤ) :=
      (Int.toNat_of_nonneg h₃).symm
    conv_lhs => rw [h_cast]
    rw [← Int.natCast_div, Int.toNat_natCast]
  omega

lemma shift_div_image_subset_range (A B : ℤ) (m : ℕ) (hm : 0 < m) :
    (fun x => ((x - A) / (m : ℤ)).toNat) ''
      {x : ℤ | A ≤ x ∧ x ≤ B ∧ (m : ℤ) ∣ x} ⊆
    ↑(Finset.range ((Set.Icc A B).ncard / m + 1)) := by
  intro y hy
  rw [Finset.mem_coe, Finset.mem_range]
  obtain ⟨x, ⟨hxA, hxB, _⟩, rfl⟩ := hy
  simp only
  have h := shift_div_toNat_le A B m hm x hxA hxB
  rw [Int_Icc_ncard]
  omega

lemma ncard_multiples_le (A B : ℤ) (m : ℕ) (hm : 0 < m) :
    ({x : ℤ | A ≤ x ∧ x ≤ B ∧ (m : ℤ) ∣ x}).ncard ≤ (Set.Icc A B).ncard / m + 1 := by
  have h1 := shift_div_toNat_injOn A B m hm
  have h2 := shift_div_image_subset_range A B m hm
  have h3 := multiples_finite A B m
  calc ({x : ℤ | A ≤ x ∧ x ≤ B ∧ (m : ℤ) ∣ x}).ncard
      = ((fun x => ((x - A) / (m : ℤ)).toNat) ''
          {x : ℤ | A ≤ x ∧ x ≤ B ∧ (m : ℤ) ∣ x}).ncard := by
        rw [Set.InjOn.ncard_image h1]
    _ ≤ ((Finset.range ((Set.Icc A B).ncard / m + 1) : Set ℕ)).ncard := by
        exact Set.ncard_le_ncard h2 (Set.toFinite _)
    _ = (Set.Icc A B).ncard / m + 1 := by
        rw [Set.ncard_coe_finset, Finset.card_range]

lemma exists_prime_dvd_both (A B : ℤ) (B' : ℕ)
    (hB' : ∀ p : ℤ, A ≤ p → p ≤ B → ∀ ℓ : ℕ, Nat.Prime ℓ → (ℓ : ℤ) ∣ p → ℓ ≤ B')
    (p q : ℤ) (hAp : A ≤ p) (hpB : p ≤ B) (_hAq : A ≤ q) (_hqB : q ≤ B)
    (hgcd : Int.gcd p q ≠ 1) :
    ∃ ℓ : ℕ, Nat.Prime ℓ ∧ 2 ≤ ℓ ∧ ℓ ≤ B' ∧ (ℓ : ℤ) ∣ p ∧ (ℓ : ℤ) ∣ q := by
  obtain ⟨ℓ, hℓprime, hℓdvd⟩ := Nat.exists_prime_and_dvd hgcd
  have hgcd_dvd_p : (↑(Int.gcd p q) : ℤ) ∣ p := by
    rw [Int.coe_gcd]; exact GCDMonoid.gcd_dvd_left p q
  have hgcd_dvd_q : (↑(Int.gcd p q) : ℤ) ∣ q := by
    rw [Int.coe_gcd]; exact GCDMonoid.gcd_dvd_right p q
  have hℓdvd_gcd_int : (ℓ : ℤ) ∣ ↑(Int.gcd p q) := Nat.cast_dvd_cast hℓdvd
  have hℓdvd_p : (ℓ : ℤ) ∣ p := dvd_trans hℓdvd_gcd_int hgcd_dvd_p
  have hℓdvd_q : (ℓ : ℤ) ∣ q := dvd_trans hℓdvd_gcd_int hgcd_dvd_q
  exact ⟨ℓ, hℓprime, hℓprime.two_le, hB' p hAp hpB ℓ hℓprime hℓdvd_p, hℓdvd_p, hℓdvd_q⟩

lemma non_coprime_subset_union (A B : ℤ) (_hAB : A ≤ B) (B' : ℕ)
    (hB' : ∀ p : ℤ, A ≤ p → p ≤ B → ∀ ℓ : ℕ, Nat.Prime ℓ → (ℓ : ℤ) ∣ p → ℓ ≤ B') :
    let S := Set.Icc A B ×ˢ Set.Icc A B
    let C := {pq : ℤ × ℤ |
      A ≤ pq.1 ∧ pq.1 ≤ B ∧
      A ≤ pq.2 ∧ pq.2 ≤ B ∧
      Int.gcd pq.1 pq.2 = 1}
    S \ C ⊆ ⋃ ℓ ∈ (Finset.Icc 2 B').filter Nat.Prime,
      ({x : ℤ | A ≤ x ∧ x ≤ B ∧ (ℓ : ℤ) ∣ x}) ×ˢ
      ({x : ℤ | A ≤ x ∧ x ≤ B ∧ (ℓ : ℤ) ∣ x}) := by
  intro S C pq hpq
  simp only [Set.mem_diff] at hpq
  obtain ⟨hS, hnotC⟩ := hpq
  rw [Set.mem_prod] at hS
  have hAp := (Set.mem_Icc.mp hS.1).1
  have hpB := (Set.mem_Icc.mp hS.1).2
  have hAq := (Set.mem_Icc.mp hS.2).1
  have hqB := (Set.mem_Icc.mp hS.2).2
  have hgcd : Int.gcd pq.1 pq.2 ≠ 1 := by
    intro h
    exact hnotC ⟨hAp, hpB, hAq, hqB, h⟩
  obtain ⟨ℓ, hprime, h2le, hleB', hdvdp, hdvdq⟩ :=
    exists_prime_dvd_both A B B' hB' pq.1 pq.2 hAp hpB hAq hqB hgcd
  simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq]
  exact ⟨ℓ, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h2le, hleB'⟩, hprime⟩,
    ⟨hAp, hpB, hdvdp⟩, ⟨hAq, hqB, hdvdq⟩⟩

lemma ncard_multiples_prod_le (A B : ℤ) (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    let L := (Set.Icc A B).ncard
    let Mℓ := {x : ℤ | A ≤ x ∧ x ≤ B ∧ (ℓ : ℤ) ∣ x}
    (Mℓ ×ˢ Mℓ).ncard ≤ (L / ℓ + 1) ^ 2 := by
  intro L Mℓ
  have hℓpos : 0 < ℓ := hℓ.pos
  calc (Mℓ ×ˢ Mℓ).ncard = Mℓ.ncard * Mℓ.ncard := Set.ncard_prod
    _ = Mℓ.ncard ^ 2 := (sq Mℓ.ncard).symm
    _ ≤ (L / ℓ + 1) ^ 2 := by
        apply pow_le_pow_left' (ncard_multiples_le A B ℓ hℓpos)

lemma non_coprime_ncard_le_sum (A B : ℤ) (hAB : A ≤ B) (B' : ℕ)
    (hB' : ∀ p : ℤ, A ≤ p → p ≤ B → ∀ ℓ : ℕ, Nat.Prime ℓ → (ℓ : ℤ) ∣ p → ℓ ≤ B') :
    let L := (Set.Icc A B).ncard
    let S := Set.Icc A B ×ˢ Set.Icc A B
    let C := {pq : ℤ × ℤ |
      A ≤ pq.1 ∧ pq.1 ≤ B ∧
      A ≤ pq.2 ∧ pq.2 ≤ B ∧
      Int.gcd pq.1 pq.2 = 1}
    (S \ C).ncard ≤ ∑ ℓ ∈ (Finset.Icc 2 B').filter Nat.Prime, (L / ℓ + 1) ^ 2 := by
  intro L S C
  have h_sub := non_coprime_subset_union A B hAB B' hB'
  have h_fin_union : (⋃ ℓ ∈ (Finset.Icc 2 B').filter Nat.Prime,
      ({x : ℤ | A ≤ x ∧ x ≤ B ∧ (ℓ : ℤ) ∣ x}) ×ˢ
      ({x : ℤ | A ≤ x ∧ x ≤ B ∧ (ℓ : ℤ) ∣ x})).Finite := by
    apply Set.Finite.subset ((Set.finite_Icc A B).prod (Set.finite_Icc A B))
    intro ⟨x, y⟩ hxy
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq] at hxy ⊢
    obtain ⟨ℓ, _, ⟨hx1, hx2, _⟩, hy1, hy2, _⟩ := hxy
    exact ⟨⟨hx1, hx2⟩, hy1, hy2⟩
  calc (S \ C).ncard
      ≤ (⋃ ℓ ∈ (Finset.Icc 2 B').filter Nat.Prime,
          ({x : ℤ | A ≤ x ∧ x ≤ B ∧ (ℓ : ℤ) ∣ x}) ×ˢ
          ({x : ℤ | A ≤ x ∧ x ≤ B ∧ (ℓ : ℤ) ∣ x})).ncard := by
        exact Set.ncard_le_ncard h_sub h_fin_union
      _ ≤ ∑ ℓ ∈ (Finset.Icc 2 B').filter Nat.Prime,
          (({x : ℤ | A ≤ x ∧ x ≤ B ∧ (ℓ : ℤ) ∣ x}) ×ˢ
           ({x : ℤ | A ≤ x ∧ x ≤ B ∧ (ℓ : ℤ) ∣ x})).ncard := by
        exact Finset.set_ncard_biUnion_le _ _
      _ ≤ ∑ ℓ ∈ (Finset.Icc 2 B').filter Nat.Prime, (L / ℓ + 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        have hprime : Nat.Prime ℓ := (Finset.mem_filter.mp hℓ).2
        exact ncard_multiples_prod_le A B ℓ hprime

lemma card_primes_le_B' (B' : ℕ) :
    ((Finset.Icc 2 B').filter Nat.Prime).card ≤ B' := by
  calc ((Finset.Icc 2 B').filter Nat.Prime).card
      ≤ (Finset.Icc 2 B').card := Finset.card_filter_le _ _
    _ = B' + 1 - 2 := Nat.card_Icc 2 B'
    _ ≤ B' := by omega

lemma sum_inv_sq_primes_le (B' : ℕ) :
    ∑ ℓ ∈ (Finset.Icc 2 B').filter Nat.Prime, (1 : ℝ) / (ℓ : ℝ) ^ 2 ≤ 3 / 4 := by
  calc ∑ ℓ ∈ (Finset.Icc 2 B').filter Nat.Prime, (1 : ℝ) / (ℓ : ℝ) ^ 2
      ≤ ∑ ℓ ∈ Finset.Icc 2 B', (1 : ℝ) / (ℓ : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        positivity
    _ ≤ 3 / 4 := sum_inv_sq_le_three_fourths B'

lemma term_sq_bound (L ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ((L / ℓ + 1 : ℕ) : ℝ) ^ 2 ≤ 5 / 4 * (L : ℝ) ^ 2 / (ℓ : ℝ) ^ 2 + 5 := by
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by positivity
  push_cast
  have h1 : (↑(L / ℓ) : ℝ) ≤ (↑L : ℝ) / (↑ℓ : ℝ) := Nat.cast_div_le
  have h2 : ((↑(L / ℓ) : ℝ) + 1) ^ 2 ≤ ((↑L : ℝ) / (↑ℓ : ℝ) + 1) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have h3 : ((↑L : ℝ) / (↑ℓ : ℝ) + 1) ^ 2 ≤ 5 / 4 * ((↑L : ℝ) / (↑ℓ : ℝ)) ^ 2 + 5 :=
    sq_add_one_le _
  rw [div_pow] at h3
  rw [mul_div_assoc]
  linarith

lemma sum_sq_bound_real (L B' : ℕ) :
    (∑ ℓ ∈ (Finset.Icc 2 B').filter Nat.Prime, ((L / ℓ + 1 : ℕ) : ℝ) ^ 2) ≤
    15 / 16 * (L : ℝ) ^ 2 + 5 * (B' : ℝ) := by
  set P := (Finset.Icc 2 B').filter Nat.Prime
  have h1 : ∀ ℓ ∈ P, ((L / ℓ + 1 : ℕ) : ℝ) ^ 2 ≤ 5 / 4 * (L : ℝ) ^ 2 / (ℓ : ℝ) ^ 2 + 5 := by
    intro ℓ hℓ
    apply term_sq_bound
    exact (Finset.mem_filter.mp hℓ).1 |> Finset.mem_Icc.mp |>.1
  calc ∑ ℓ ∈ P, ((L / ℓ + 1 : ℕ) : ℝ) ^ 2
      ≤ ∑ ℓ ∈ P, (5 / 4 * (L : ℝ) ^ 2 / (ℓ : ℝ) ^ 2 + 5) :=
        Finset.sum_le_sum h1
    _ = ∑ ℓ ∈ P, (5 / 4 * (L : ℝ) ^ 2 / (ℓ : ℝ) ^ 2) + ∑ ℓ ∈ P, (5 : ℝ) :=
        Finset.sum_add_distrib
    _ = 5 / 4 * (L : ℝ) ^ 2 * (∑ ℓ ∈ P, (1 : ℝ) / (ℓ : ℝ) ^ 2) + ∑ ℓ ∈ P, (5 : ℝ) := by
        congr 1
        rw [Finset.mul_sum]
        congr 1; ext ℓ; ring
    _ = 5 / 4 * (L : ℝ) ^ 2 * (∑ ℓ ∈ P, (1 : ℝ) / (ℓ : ℝ) ^ 2) + P.card * 5 := by
        congr 1
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 5 / 4 * (L : ℝ) ^ 2 * (3 / 4) + (B' : ℝ) * 5 := by
        gcongr
        · exact sum_inv_sq_primes_le B'
        · exact_mod_cast card_primes_le_B' B'
    _ = 15 / 16 * (L : ℝ) ^ 2 + 5 * (B' : ℝ) := by ring

lemma non_coprime_pairs_upper_bound (A B : ℤ) (hAB : A ≤ B) (B' : ℕ)
    (hB' : ∀ p : ℤ, A ≤ p → p ≤ B → ∀ ℓ : ℕ, Nat.Prime ℓ → (ℓ : ℤ) ∣ p → ℓ ≤ B') :
    let L := (Set.Icc A B).ncard
    let S := Set.Icc A B ×ˢ Set.Icc A B
    let C := {pq : ℤ × ℤ |
      A ≤ pq.1 ∧ pq.1 ≤ B ∧
      A ≤ pq.2 ∧ pq.2 ≤ B ∧
      Int.gcd pq.1 pq.2 = 1}
    ((S \ C).ncard : ℝ) ≤ 15 / 16 * (L : ℝ) ^ 2 + 5 * (B' : ℝ) := by
  intro L S C
  have h1 := non_coprime_ncard_le_sum A B hAB B' hB'
  have h2 := sum_sq_bound_real L B'
  calc ((S \ C).ncard : ℝ)
      ≤ (∑ ℓ ∈ (Finset.Icc 2 B').filter Nat.Prime, (L / ℓ + 1) ^ 2 : ℕ) := by
        exact_mod_cast h1
    _ = ∑ ℓ ∈ (Finset.Icc 2 B').filter Nat.Prime, ((L / ℓ + 1 : ℕ) : ℝ) ^ 2 := by
        push_cast; ring_nf
    _ ≤ 15 / 16 * (L : ℝ) ^ 2 + 5 * (B' : ℝ) := h2

lemma coprime_lower_bound_from_complement (L : ℕ) (C_card NC_card : ℕ) (B' : ℕ)
    (h_partition : C_card + NC_card = L * L)
    (h_NC_bound : (NC_card : ℝ) ≤ 15 / 16 * (L : ℝ) ^ 2 + 5 * (B' : ℝ)) :
    (L : ℝ) ^ 2 / 16 - 5 * (B' : ℝ) ≤ (C_card : ℝ) := by
  have h₁ : (C_card : ℝ) + (NC_card : ℝ) = (L : ℝ) ^ 2 := by
    have h₁₁ : (C_card + NC_card : ℕ) = L * L := by
      exact_mod_cast h_partition
    have h₁₂ : (C_card : ℝ) + (NC_card : ℝ) = (L : ℝ) * (L : ℝ) := by
      norm_cast at h₁₁ ⊢
    linarith
  linarith

lemma coprime_pairs_sieve_lower_bound (A B : ℤ) (hAB : A ≤ B) (B' : ℕ)
    (hB' : ∀ p : ℤ, A ≤ p → p ≤ B → ∀ ℓ : ℕ, Nat.Prime ℓ → (ℓ : ℤ) ∣ p → ℓ ≤ B') :
    let L := (Set.Icc A B).ncard
    (L : ℝ) ^ 2 / 16 - 5 * (B' : ℝ) ≤
      ({pq : ℤ × ℤ |
        A ≤ pq.1 ∧ pq.1 ≤ B ∧
        A ≤ pq.2 ∧ pq.2 ≤ B ∧
        Int.gcd pq.1 pq.2 = 1}.ncard : ℝ) := by
  intro L
  set C := {pq : ℤ × ℤ |
    A ≤ pq.1 ∧ pq.1 ≤ B ∧
    A ≤ pq.2 ∧ pq.2 ≤ B ∧
    Int.gcd pq.1 pq.2 = 1}
  set S := Set.Icc A B ×ˢ Set.Icc A B
  have hC_sub : C ⊆ S := coprime_pairs_subset_product A B
  have hS_fin : S.Finite := (Set.finite_Icc A B).prod (Set.finite_Icc A B)
  have hNC := non_coprime_pairs_upper_bound A B hAB B' hB'
  have h_part := Set.ncard_diff_add_ncard_of_subset hC_sub hS_fin
  have hS_card : S.ncard = L * L := Set.ncard_prod
  rw [hS_card] at h_part
  exact coprime_lower_bound_from_complement L C.ncard (S \ C).ncard B'
    (by omega) (hNC)

lemma quadratic_dominates_linear (δ L n B' : ℝ) (hδ : 0 < δ)
    (hn : 0 ≤ n) (hL : δ * n ≤ L) (hB' : 5 * B' ≤ 5 * n)
    (hn_large : 160 / δ ^ 2 ≤ n) :
    δ ^ 2 / 32 * n ^ 2 ≤ L ^ 2 / 16 - 5 * B' := by
  have hL_sq : δ ^ 2 * n ^ 2 ≤ L ^ 2 := by
    have h₁ : 0 ≤ δ * n := by positivity
    have h₄ : (δ * n) ^ 2 ≤ L ^ 2 := by
      nlinarith [sq_nonneg (L - δ * n)]
    linarith
  have h_nδ_ge : n * δ ^ 2 ≥ 160 := by
    have h₂ : 0 < δ ^ 2 := by positivity
    have h₃ : 160 ≤ n * δ ^ 2 := by
      calc
        160 = (160 / δ ^ 2) * δ ^ 2 := by
          field_simp [h₂.ne']
        _ ≤ n * δ ^ 2 := by
          nlinarith
    linarith
  have h_nδ_sq_ge : δ ^ 2 / 32 * n ^ 2 ≥ 5 * n := by
    have h₇ : n * (n * δ ^ 2) ≥ n * 160 := by
      nlinarith
    linarith
  linarith

lemma ceil_eta_n_pos (η : ℝ) (hη_pos : 0 < η) (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ (⌈η * (n : ℝ)⌉ : ℤ) := by
  have h_main : 0 < (η : ℝ) * (n : ℝ) := by
    positivity
  have h_ceil_pos : 1 ≤ (⌈η * (n : ℝ)⌉ : ℤ) := by
    have h₂ : 1 ≤ ⌈(η * (n : ℝ))⌉ := by
      have h₄ : (⌈(η * (n : ℝ))⌉ : ℝ) ≥ (η * (n : ℝ)) := by exact Int.le_ceil _
      have h₆ : (⌈(η * (n : ℝ))⌉ : ℤ) ≥ 1 := by
        by_contra h
        have h₇ : (⌈(η * (n : ℝ))⌉ : ℤ) ≤ 0 := by linarith
        have h₈ : (⌈(η * (n : ℝ))⌉ : ℝ) ≤ 0 := by exact_mod_cast h₇
        nlinarith
      exact_mod_cast h₆
    exact_mod_cast h₂
  exact h_ceil_pos

lemma floor_div_six_le_n (n : ℕ) : (⌊(n : ℝ) / 6⌋ : ℤ) ≤ (n : ℤ) := by
  have h₁ : (n : ℝ) / 6 ≤ (n : ℝ) := by nlinarith
  have h₂ : ((⌊(n : ℝ) / 6⌋ : ℤ) : ℝ) ≤ (n : ℝ) / 6 := Int.floor_le _
  have h₃ : ((⌊(n : ℝ) / 6⌋ : ℤ) : ℝ) ≤ (n : ℝ) := by nlinarith
  exact_mod_cast h₃

lemma interval_ncard_le_n (η : ℝ) (hη_pos : 0 < η) (n : ℕ) (hn : ⌈1 / η⌉₊ ≤ n) :
    (Set.Icc (⌈η * (n : ℝ)⌉ : ℤ) (⌊(n : ℝ) / 6⌋ : ℤ)).ncard ≤ n := by
  rw [Int_Icc_ncard]
  have h1 : 1 ≤ n := by
    have : 0 < ⌈1 / η⌉₊ := Nat.ceil_pos.mpr (by positivity)
    omega
  have hceil := ceil_eta_n_pos η hη_pos n h1
  have hfloor := floor_div_six_le_n n
  omega

lemma interval_ncard_upper_bound (η : ℝ) (hη_pos : 0 < η) :
    ∃ (N₀ : ℕ), ∀ n : ℕ, N₀ ≤ n →
      ((Set.Icc (⌈η * (n : ℝ)⌉ : ℤ) (⌊(n : ℝ) / 6⌋ : ℤ)).ncard : ℝ) ≤ (n : ℝ) := by
  exact ⟨⌈1 / η⌉₊, fun n hn => by exact_mod_cast interval_ncard_le_n η hη_pos n hn⟩

lemma prime_dvd_le_of_pos (p : ℤ) (hp : 0 < p) (ℓ : ℕ) (_hprime : Nat.Prime ℓ)
    (hdvd : (ℓ : ℤ) ∣ p) : (ℓ : ℤ) ≤ p := by
  have h₂ : (ℓ : ℤ) ≤ p := by
    have h₃ : (ℓ : ℤ) ∣ p := hdvd
    have h₄ : (ℓ : ℤ) ≤ p := Int.le_of_dvd hp h₃
    exact h₄
  exact h₂

lemma prime_divisor_bound (η : ℝ) (hη_pos : 0 < η) (n : ℕ) (hn : 1 ≤ n) :
    ∀ p : ℤ, (⌈η * (n : ℝ)⌉ : ℤ) ≤ p → p ≤ (⌊(n : ℝ) / 6⌋ : ℤ) →
    ∀ ℓ : ℕ, Nat.Prime ℓ → (ℓ : ℤ) ∣ p → ℓ ≤ n := by
  intro p hp_low hp_high ℓ hprime hdvd
  have hp_pos : 0 < p := lt_of_lt_of_le (by linarith [ceil_eta_n_pos η hη_pos n hn]) hp_low
  have hℓp : (ℓ : ℤ) ≤ p := prime_dvd_le_of_pos p hp_pos ℓ hprime hdvd
  have hpn : p ≤ (n : ℤ) := le_trans hp_high (floor_div_six_le_n n)
  exact_mod_cast le_trans hℓp hpn

lemma rectangle_coprime_ncard_lower_bound (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1 / 6) :
    ∃ (c : ℝ) (N₁ : ℕ), 0 < c ∧ ∀ n : ℕ, N₁ ≤ n →
      c * (n : ℝ) ^ 2 ≤
        ({pq : ℤ × ℤ |
          (⌈η * (n : ℝ)⌉ : ℤ) ≤ pq.1 ∧ pq.1 ≤ (⌊(n : ℝ) / 6⌋ : ℤ) ∧
          (⌈η * (n : ℝ)⌉ : ℤ) ≤ pq.2 ∧ pq.2 ≤ (⌊(n : ℝ) / 6⌋ : ℤ) ∧
          Int.gcd pq.1 pq.2 = 1}.ncard : ℝ) := by
  set δ := (1 / 6 - η) / 2 with hδ_def
  have hδ : 0 < δ := by linarith
  obtain ⟨N₁, hN₁⟩ := interval_ncard_lower_bound η hη_pos hη_lt
  obtain ⟨N₂, hN₂⟩ := interval_ncard_upper_bound η hη_pos
  obtain ⟨N₃, hN₃⟩ := ceil_le_floor_for_large_n η hη_pos hη_lt
  refine ⟨δ ^ 2 / 32, max (max N₁ N₂) (max N₃ (⌈160 / δ ^ 2⌉₊ + 1)), ?_, ?_⟩
  · positivity
  · intro n hn
    have hn₁ : N₁ ≤ n := le_of_max_le_left (le_of_max_le_left hn)
    have hn₂ : N₂ ≤ n := le_of_max_le_right (le_of_max_le_left hn)
    have hn₃ : N₃ ≤ n := le_of_max_le_left (le_of_max_le_right hn)
    have hL_lower := hN₁ n hn₁
    have hL_upper := hN₂ n hn₂
    have hAB := hN₃ n hn₃
    have hn1 : 1 ≤ n := by omega
    set L := (Set.Icc (⌈η * (n : ℝ)⌉ : ℤ) (⌊(n : ℝ) / 6⌋ : ℤ)).ncard with hL_def
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn_large : 160 / δ ^ 2 ≤ (n : ℝ) := by
      have h4 : (⌈160 / δ ^ 2⌉₊ + 1 : ℕ) ≤ n := le_of_max_le_right (le_of_max_le_right hn)
      have : (⌈160 / δ ^ 2⌉₊ : ℝ) ≤ (n : ℝ) := by
        calc (⌈160 / δ ^ 2⌉₊ : ℝ) ≤ (⌈160 / δ ^ 2⌉₊ + 1 : ℕ) := by
              exact_mod_cast Nat.le_succ _
          _ ≤ (n : ℝ) := Nat.cast_le.mpr h4
      linarith [Nat.le_ceil (160 / δ ^ 2)]
    have hprime := prime_divisor_bound η hη_pos n hn1
    calc δ ^ 2 / 32 * (n : ℝ) ^ 2
        ≤ (L : ℝ) ^ 2 / 16 - 5 * (n : ℝ) :=
          quadratic_dominates_linear δ (L : ℝ) (n : ℝ) (n : ℝ) hδ hnn hL_lower (by linarith)
            hn_large
      _ ≤ ({pq : ℤ × ℤ |
            (⌈η * (n : ℝ)⌉ : ℤ) ≤ pq.1 ∧ pq.1 ≤ (⌊(n : ℝ) / 6⌋ : ℤ) ∧
            (⌈η * (n : ℝ)⌉ : ℤ) ≤ pq.2 ∧ pq.2 ≤ (⌊(n : ℝ) / 6⌋ : ℤ) ∧
            Int.gcd pq.1 pq.2 = 1}.ncard : ℝ) :=
          coprime_pairs_sieve_lower_bound _ _ hAB n hprime

lemma coprime_triangle_ncard_lower_bound (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1 / 6) :
    ∃ (c : ℝ) (N₁ : ℕ), 0 < c ∧ ∀ n : ℕ, N₁ ≤ n →
      c * (n : ℝ) ^ 2 ≤
        ({pq : ℤ × ℤ |
          η * (n : ℝ) ≤ (pq.1 : ℝ) ∧
          η * (n : ℝ) ≤ (pq.2 : ℝ) ∧
          (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 ∧
          Int.gcd pq.1 pq.2 = 1}.ncard : ℝ) := by
  obtain ⟨c, N₁, hc, hbound⟩ := rectangle_coprime_ncard_lower_bound η hη_pos hη_lt
  exact ⟨c, N₁, hc, fun n hn => le_trans (hbound n hn)
    (Nat.cast_le.mpr (Set.ncard_le_ncard
      (rectangle_coprime_subset_target n η)
      (coprime_triangle_finite n η)))⟩

lemma truncatedObtuseRegion_ncard_lower_bound (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1 / 6) :
    ∃ (c : ℝ) (N₁ : ℕ), 0 < c ∧ ∀ n : ℕ, N₁ ≤ n →
      c * (n : ℝ) ^ 2 ≤ ((truncatedObtuseRegion n η).ncard : ℝ) := by
  obtain ⟨c, N₁, hc_pos, h_lower⟩ := coprime_triangle_ncard_lower_bound η hη_pos hη_lt
  exact ⟨c, N₁, hc_pos, fun n hn => by
    calc c * (n : ℝ) ^ 2
        ≤ ({pq : ℤ × ℤ |
              η * (n : ℝ) ≤ (pq.1 : ℝ) ∧
              η * (n : ℝ) ≤ (pq.2 : ℝ) ∧
              (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 ∧
              Int.gcd pq.1 pq.2 = 1}.ncard : ℝ) := h_lower n hn
      _ ≤ ((truncatedObtuseRegion n η).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard
            (coprime_triangle_subset_truncatedObtuseRegion n η)
            (truncatedObtuseRegion_finite n η)⟩

/-- A relaxed family of bad pairs, replacing `countingFunctionS n p q < 5` by
`(countingFunctionS n p q : ℝ) < η ^ 2 / 2 * φ(n)`. -/
noncomputable def badPairsE (n : ℕ) (η : ℝ) : Set (ℤ × ℤ) :=
  {pq ∈ truncatedObtuseRegion n η |
    Int.gcd pq.2 (largestPrimeFactor n : ℤ) = 1 ∧
    (countingFunctionS n pq.1 pq.2 : ℝ) < (η ^ 2 / 2 : ℝ) * (Nat.totient n : ℝ)}

/-- Pairs of `truncatedObtuseRegion n η` with `gcd(q, P⁺(n)) = 1` and `P⁺(n) ∣ p`. -/
noncomputable def pdivPairs (n : ℕ) (η : ℝ) : Set (ℤ × ℤ) :=
  {pq ∈ truncatedObtuseRegion n η |
    Int.gcd pq.2 (largestPrimeFactor n : ℤ) = 1 ∧
    (largestPrimeFactor n : ℤ) ∣ pq.1}


/-- The pairs in `badPairsE n η` whose first coordinate is not divisible by the largest prime
factor of `n`. -/
noncomputable def residueBadPairs (n : ℕ) (η : ℝ) : Set (ℤ × ℤ) :=
  {pq ∈ badPairsE n η | ¬((largestPrimeFactor n : ℤ) ∣ pq.1)}


lemma sq_div_ceil_le_sq_div_log (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊ ≤ (n : ℝ) ^ 2 / Real.log (n : ℝ) := by
  have h₁ : (1 : ℝ) < (n : ℝ) := by norm_cast
  have h₂ : 0 < Real.log (n : ℝ) := by exact Real.log_pos h₁
  have h₃ : (Real.log (n : ℝ) : ℝ) ≤ ⌈Real.log (n : ℝ)⌉₊ := by exact Nat.le_ceil _
  have h₄ : 0 ≤ (n : ℝ) ^ 2 := by simp
  have h₅ : (n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊ ≤ (n : ℝ) ^ 2 / Real.log (n : ℝ) :=
    by exact div_le_div_of_nonneg_left h₄ h₂ h₃
  assumption

lemma div_toNat_mem_range (B : ℤ) (P : ℕ) (_hP : 0 < P) (hB : 0 ≤ B) (x : ℤ)
    (hx0 : 0 ≤ x) (hxB : x ≤ B) :
    (x / (P : ℤ)).toNat < B.toNat / P + 1 := by
  have h₂ : (x / (P : ℤ)).toNat = x.toNat / P := by
    have : x / (P : ℤ) = ↑(x.toNat / P) := by simp_all
    rw [this, Int.toNat_natCast]
  have h₃ : x.toNat ≤ B.toNat := by omega
  have h₄ : x.toNat / P ≤ B.toNat / P := Nat.div_le_div_right h₃
  omega

lemma inj_div_toNat (B : ℤ) (P : ℕ) (hP : 0 < P) :
    Set.InjOn (fun x : ℤ => (x / (P : ℤ)).toNat)
      {x : ℤ | 0 ≤ x ∧ x ≤ B ∧ (P : ℤ) ∣ x} := by
  intro x hx y hy hxy
  have hx₁ : 0 ≤ x := hx.1
  have hx₂ : x ≤ B := hx.2.1
  have hx₃ : (P : ℤ) ∣ x := hx.2.2
  have hy₁ : 0 ≤ y := hy.1
  have hy₂ : y ≤ B := hy.2.1
  have hy₃ : (P : ℤ) ∣ y := hy.2.2
  have h₁ : (x / (P : ℤ)).toNat = (y / (P : ℤ)).toNat := hxy
  have h₂ : (P : ℤ) ≠ 0 := by
    norm_cast
    omega
  have h₃ : x / (P : ℤ) = y / (P : ℤ) := by
    have h₄ : 0 ≤ x / (P : ℤ) := by
      have h₇ : 0 ≤ x / (P : ℤ) := by
        apply Int.ediv_nonneg
        · exact hx₁
        · exact by positivity
      exact h₇
    have h₅ : 0 ≤ y / (P : ℤ) := by
      have h₈ : 0 ≤ y / (P : ℤ) := by
        apply Int.ediv_nonneg
        · exact hy₁
        · exact by positivity
      exact h₈
    have h₆ : (x / (P : ℤ)).toNat = (y / (P : ℤ)).toNat := h₁
    have h₇ : x / (P : ℤ) ≥ 0 := h₄
    have h₈ : y / (P : ℤ) ≥ 0 := h₅
    have h₉ : (x / (P : ℤ)).toNat = (y / (P : ℤ)).toNat := h₁
    have h₁₀ : x / (P : ℤ) = y / (P : ℤ) := by
      have h₁₁ : (x / (P : ℤ)).toNat = (y / (P : ℤ)).toNat := h₉
      have h₁₂ : x / (P : ℤ) = y / (P : ℤ) := by
        have h₁₃ : 0 ≤ x / (P : ℤ) := h₄
        have h₁₄ : 0 ≤ y / (P : ℤ) := h₅
        have h₁₅ : (x / (P : ℤ)).toNat = (y / (P : ℤ)).toNat := h₁₁
        have h₁₆ : x / (P : ℤ) = y / (P : ℤ) := by
          rw [← Int.ofNat_inj] at *
          simp_all
        exact h₁₆
      exact h₁₂
    exact h₁₀
  have h₄ : x = y := by
    have h₅ : x / (P : ℤ) = y / (P : ℤ) := h₃
    have h₈ : x = (x / (P : ℤ)) * (P : ℤ) := by
      have h₉ : (P : ℤ) ∣ x := hx₃
      have h₁₀ : (x / (P : ℤ)) * (P : ℤ) = x := by
        have h₁₁ : (x / (P : ℤ)) * (P : ℤ) = x := by
          apply Int.ediv_mul_cancel h₉
        exact h₁₁
      linarith
    have h₉ : y = (y / (P : ℤ)) * (P : ℤ) := by
      have h₁₀ : (P : ℤ) ∣ y := hy₃
      have h₁₁ : (y / (P : ℤ)) * (P : ℤ) = y := by
        have h₁₂ : (y / (P : ℤ)) * (P : ℤ) = y := by
          apply Int.ediv_mul_cancel h₁₀
        exact h₁₂
      linarith
    have h₁₀ : x = y := by
      rw [h₈, h₉]
      rw [h₅]
    exact h₁₀
  exact h₄

lemma ncard_nonneg_multiples_le (B : ℤ) (P : ℕ) (hP : 0 < P) (hB : 0 ≤ B) :
    ({x : ℤ | 0 ≤ x ∧ x ≤ B ∧ (P : ℤ) ∣ x}).ncard ≤ B.toNat / P + 1 := by
  have h1 := inj_div_toNat B P hP
  calc ({x : ℤ | 0 ≤ x ∧ x ≤ B ∧ (P : ℤ) ∣ x}).ncard
      ≤ (↑(Finset.range (B.toNat / P + 1)) : Set ℕ).ncard := by
        apply Set.ncard_le_ncard_of_injOn
          (fun x : ℤ => (x / (P : ℤ)).toNat)
          (fun a ha => by
            simp only [Finset.coe_range, Set.mem_Iio]
            exact div_toNat_mem_range B P hP hB a ha.1 ha.2.1)
          h1
    _ = B.toNat / P + 1 := by
        rw [Set.ncard_coe_finset, Finset.card_range]

lemma nonneg_multiples_finite (B : ℤ) (P : ℕ) :
    {x : ℤ | 0 ≤ x ∧ x ≤ B ∧ (P : ℤ) ∣ x}.Finite :=
  multiples_finite 0 B P

lemma mul_P_mem_set (B : ℤ) (P : ℕ) (_hP : 0 < P) (hB : 0 ≤ B)
    (k : ℕ) (hk : k ≤ B.toNat / P) :
    (↑k * ↑P : ℤ) ∈ {x : ℤ | 0 ≤ x ∧ x ≤ B ∧ (P : ℤ) ∣ x} := by
  have h₁ : 0 ≤ (↑k * ↑P : ℤ) := by
    nlinarith
  have h₂ : (↑k * ↑P : ℤ) ≤ B := by
    have h₃ : (k : ℕ) ≤ B.toNat / P := hk
    have h₄ : (k : ℕ) * P ≤ (B.toNat / P) * P := by
      exact Nat.mul_le_mul_right P h₃
    have h₅ : (B.toNat / P) * P ≤ B.toNat := by
      have h₅₁ : (B.toNat / P) * P ≤ B.toNat := by
        have h₅₂ : (B.toNat / P) * P ≤ B.toNat := Nat.div_mul_le_self B.toNat P
        exact h₅₂
      exact h₅₁
    have h₇ : (↑k * ↑P : ℤ) = (↑(k * P) : ℤ) := by
      norm_cast
    have h₈ : (↑(k * P) : ℤ) ≤ B := by
      have h₈₃ : (↑(k * P) : ℤ) ≤ B := by
        have h₈₅ : (B.toNat : ℤ) ≤ B := by
          have h₈₆ : 0 ≤ B := hB
          have h₈₇ : (B.toNat : ℤ) = B := by
            rw [Int.toNat_of_nonneg h₈₆]
          linarith
        linarith
      exact h₈₃
    calc
      (↑k * ↑P : ℤ) = (↑(k * P) : ℤ) := by rw [h₇]
      _ ≤ B := h₈
  have h₃ : (P : ℤ) ∣ (↑k * ↑P : ℤ) := by
    use (k : ℤ)
    ring_nf
  refine ⟨h₁, h₂, h₃⟩

lemma ncard_nonneg_multiples_ge (B : ℤ) (P : ℕ) (hP : 0 < P) (hB : 0 ≤ B) :
    B.toNat / P + 1 ≤ ({x : ℤ | 0 ≤ x ∧ x ≤ B ∧ (P : ℤ) ∣ x}).ncard := by
  set S := {x : ℤ | 0 ≤ x ∧ x ≤ B ∧ (P : ℤ) ∣ x}
  set f : ℕ → ℤ := fun k => ↑k * ↑P
  set R := Finset.range (B.toNat / P + 1)
  have hfS : ∀ k ∈ R, f k ∈ S := by
    intro k hk
    have hk' : k ≤ B.toNat / P := by
      simp only [R, Finset.mem_range] at hk; omega
    exact mul_P_mem_set B P hP hB k hk'
  have hfinj : Set.InjOn f ↑R := by
    intro a _ b _ hab
    simp only [f] at hab
    have hPne : (P : ℤ) ≠ 0 := by positivity
    have : (a : ℤ) = (b : ℤ) := mul_right_cancel₀ hPne hab
    exact_mod_cast this
  calc B.toNat / P + 1
      = R.card := (Finset.card_range _).symm
    _ = (f '' ↑R).ncard := by
        rw [Set.InjOn.ncard_image hfinj, Set.ncard_coe_finset]
    _ ≤ S.ncard := by
        apply Set.ncard_le_ncard
        · intro x hx
          obtain ⟨k, hkR, rfl⟩ := hx
          exact hfS k hkR
        · exact nonneg_multiples_finite B P

lemma real_sq_div_mono (n : ℕ) (P : ℕ) (θ : ℝ)
    (hn : 2 ≤ n) (_hP_pos : 0 < P)
    (hP : (P : ℝ) ≥ (n : ℝ) ^ θ) :
    (n : ℝ) ^ 2 / (P : ℝ) ≤ (n : ℝ) ^ 2 / (n : ℝ) ^ θ := by
  have h_n_ge_2 : (n : ℝ) ≥ 2 := by simp_all
  have h_n_pos : (0 : ℝ) < (n : ℝ) := by nlinarith
  have h_c_pos : (0 : ℝ) < (n : ℝ) ^ θ := by exact Real.rpow_pos_of_pos h_n_pos θ
  have h_a_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by simp
  exact div_le_div_of_nonneg_left h_a_nonneg h_c_pos hP

lemma truncatedObtuseRegion_subset_box_rb (n : ℕ) (η : ℝ) :
    truncatedObtuseRegion n η ⊆
      (Set.Icc (⌈η * (n : ℝ)⌉ - 1 : ℤ) (⌊(n : ℝ) / 2 - η * (n : ℝ)⌋ : ℤ)) ×ˢ
      (Set.Icc (⌈η * (n : ℝ)⌉ - 1 : ℤ) (⌊(n : ℝ) / 2 - η * (n : ℝ)⌋ : ℤ)) := by
  intro ⟨p, q⟩ h
  simp only [truncatedObtuseRegion, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc] at h ⊢
  have h₁ : (η * (n : ℝ) : ℝ) ≤ (p : ℝ) := h.1
  have h₂ : (η * (n : ℝ) : ℝ) ≤ (q : ℝ) := h.2.1
  have h₃ : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 := h.2.2.1
  have hc : ⌈η * (n : ℝ)⌉ ≤ p + 1 ∧ ⌈η * (n : ℝ)⌉ ≤ q + 1 := by
    constructor <;> · rw [Int.ceil_le]; push_cast; linarith
  have hp : (p : ℤ) ≤ ⌊(n : ℝ) / 2 - η * (n : ℝ)⌋ := by
    rw [Int.le_floor]; linarith
  have hq : (q : ℤ) ≤ ⌊(n : ℝ) / 2 - η * (n : ℝ)⌋ := by
    rw [Int.le_floor]; linarith
  exact ⟨⟨by omega, hp⟩, ⟨by omega, hq⟩⟩

lemma truncatedObtuseRegion_finite_rb (n : ℕ) (η : ℝ) :
    (truncatedObtuseRegion n η).Finite :=
  ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).subset
    (truncatedObtuseRegion_subset_box_rb n η)

lemma residueBadPairs_finite (n : ℕ) (η : ℝ) :
    (residueBadPairs n η).Finite :=
  (truncatedObtuseRegion_finite n η).subset (fun pq hpq => by
    obtain ⟨⟨h1, _⟩, _⟩ := hpq
    exact h1)



lemma cast_div_rearrange (n c : ℕ) (_hc : 0 < c) :
    (3 * (n : ℝ) ^ 2) / (4 * (c : ℝ)) ≤ 3 / 4 * (n : ℝ) ^ 2 / (c : ℝ) := by
  have h_eq : (3 * (n : ℝ) ^ 2) / (4 * (c : ℝ)) = 3 / 4 * (n : ℝ) ^ 2 / (c : ℝ) := by ring
  have h_le : (3 * (n : ℝ) ^ 2) / (4 * (c : ℝ)) ≤ 3 / 4 * (n : ℝ) ^ 2 / (c : ℝ) := by simp_all
  assumption

lemma largestPrimeFactor_pos_helper (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : ℕ, n.primeFactors.max = ↑a ∧ 0 < a := by
  have h₁ : 1 < n := by
    assumption
  have h₂ : n.primeFactors.Nonempty := by
    simp_all
  have h₃ : ∃ (a : ℕ), n.primeFactors.max = ↑a := by
    exact Finset.max_of_nonempty h₂
  obtain ⟨a, ha⟩ := h₃
  have h₄ : a ∈ n.primeFactors := by
    exact Finset.mem_of_max ha
  have h₅ : 0 < a := by
    exact Nat.pos_of_mem_primeFactors h₄
  exact ⟨a, ha, h₅⟩

lemma largestPrimeFactor_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < largestPrimeFactor n := by
  obtain ⟨a, ha_max, ha_pos⟩ := largestPrimeFactor_pos_helper n hn
  simp only [largestPrimeFactor, ha_max]
  exact ha_pos

lemma fiber_empty_of_gcd_ne_one (n : ℕ) (η : ℝ) (q : ℤ)
    (hq : Int.gcd q (largestPrimeFactor n : ℤ) ≠ 1) :
    {p : ℤ | (p, q) ∈ residueBadPairs n η} = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro p hp
  simp only [Set.mem_setOf_eq, residueBadPairs, badPairsE, Set.mem_setOf_eq] at hp
  apply hq
  simp_all

lemma snd_lt_half_of_mem_truncatedObtuseRegion_fb (n : ℕ) (η : ℝ)
    (pq : ℤ × ℤ) (h : pq ∈ truncatedObtuseRegion n η) (hp_pos : 0 < pq.1) :
    (pq.2 : ℝ) < (n : ℝ) / 2 := by
  simp only [truncatedObtuseRegion] at h
  have h₁ : (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 := by
    exact h.2.2.1
  have h₂ : 0 < (pq.1 : ℝ) := by exact_mod_cast hp_pos
  have h₃ : (pq.2 : ℝ) < (n : ℝ) / 2 := by
    linarith
  exact h₃

lemma intLe_half_of_real_lt_half_fb (n : ℕ) (q : ℤ) (hq : (q : ℝ) < (n : ℝ) / 2) :
    q ≤ ↑n / 2 := by
  have h₂ : (2 : ℝ) * (q : ℝ) < (n : ℝ) := by
    linarith
  have h₃ : (2 : ℤ) * q < (n : ℤ) := by
    norm_cast at h₂ ⊢
  have h₅ : q ≤ (n : ℤ) / 2 := by
    have h₅₂ : q ≤ ((n : ℤ) - 1) / 2 := by
      have h₅₄ : q ≤ ((n : ℤ) - 1) / 2 := by
        omega
      exact h₅₄
    have h₅₃ : ((n : ℤ) - 1) / 2 ≤ (n : ℤ) / 2 := by
      have h₅₄ : ((n : ℤ) - 1) / 2 ≤ (n : ℤ) / 2 := by
        have h₅₅ : (n : ℤ) % 2 = 0 ∨ (n : ℤ) % 2 = 1 := by
          omega
        rcases h₅₅ with (h₅₅ | h₅₅)
        · have h₅₁₁ : ((n : ℤ) - 1) / 2 ≤ (n : ℤ) / 2 := by
            omega
          exact h₅₁₁
        · have h₅₁₁ : ((n : ℤ) - 1) / 2 ≤ (n : ℤ) / 2 := by
            omega
          exact h₅₁₁
      exact h₅₄
    have h₅₄ : q ≤ (n : ℤ) / 2 := by
      linarith
    exact h₅₄
  have h₆ : q ≤ ↑n / 2 := by
    simpa [Int.ediv_eq_zero_of_lt] using h₅
  exact h₆

lemma pos_of_mem_truncatedObtuseRegion_fst_fb (n : ℕ) (η : ℝ) (hη_pos : 0 < η)
    (pq : ℤ × ℤ) (h : pq ∈ truncatedObtuseRegion n η) :
    0 < pq.1 := by
  have h₁ : η * (n : ℝ) ≤ (pq.1 : ℝ) := h.1
  have h₂ : η * (n : ℝ) ≤ (pq.2 : ℝ) := h.2.1
  have h₃ : (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 := h.2.2.1
  by_cases hn : n = 0
  · have h₅ : (n : ℝ) = 0 := by norm_cast
    have h₆ : η * (n : ℝ) = 0 := by rw [h₅]; ring
    have h₈ : (pq.1 : ℝ) > 0 := by
      by_contra _
      linarith
    have h₉ : 0 < (pq.1 : ℤ) := by
      norm_cast at h₈ ⊢
    exact h₉
  · have h₇ : 0 < η * (n : ℝ) := by positivity
    have h₉ : (pq.1 : ℝ) > 0 := by linarith
    have h₁₀ : 0 < (pq.1 : ℤ) := by
      norm_cast at h₉ ⊢
    exact h₁₀

lemma pos_of_mem_truncatedObtuseRegion_snd_fb (n : ℕ) (η : ℝ) (hη_pos : 0 < η)
    (pq : ℤ × ℤ) (h : pq ∈ truncatedObtuseRegion n η) :
    0 < pq.2 := by
  have h₂ : (η * (n : ℝ) : ℝ) ≤ (pq.2 : ℝ) := by
    simpa [truncatedObtuseRegion] using h.2.1
  have h₃ : (0 : ℝ) < η * (n : ℝ) := by
    by_cases hn : n = 0
    · have h₆ : (n : ℝ) = 0 := by simp [hn]
      have h₇ : η * (n : ℝ) = 0 := by rw [h₆]; ring
      have h₉ : (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 :=
        by simpa [truncatedObtuseRegion] using h.2.2.1
      have h₁₁ : (pq.1 : ℝ) + (pq.2 : ℝ) < 0 := by linarith
      have h₁₂ : (η * (n : ℝ) : ℝ) ≤ (pq.1 : ℝ) := by
        simpa [truncatedObtuseRegion] using h.1
      linarith
    · have h₇ : (0 : ℝ) < η * (n : ℝ) := by positivity
      linarith
  have h₅ : 0 < pq.2 := by
    by_contra h₆
    have h₇ : pq.2 ≤ 0 := by linarith
    have h₈ : (pq.2 : ℝ) ≤ 0 := by
      exact_mod_cast h₇
    linarith
  exact h₅

lemma fiber_subset_range (n : ℕ) (η : ℝ) (hη_pos : 0 < η) (q : ℤ) :
    {p : ℤ | (p, q) ∈ residueBadPairs n η} ⊆ Set.Ico (0 : ℤ) (↑n / 2) := by
  intro p hp
  have hres : (p, q) ∈ residueBadPairs n η := hp
  have hbad : (p, q) ∈ badPairsE n η := hres.1
  have htor : (p, q) ∈ truncatedObtuseRegion n η := hbad.1
  have h_eta_p : η * (n : ℝ) ≤ (p : ℝ) := htor.1
  have h_eta_q : η * (n : ℝ) ≤ (q : ℝ) := htor.2.1
  have h_sum : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 := htor.2.2.1
  have hp_pos : 0 < p := pos_of_mem_truncatedObtuseRegion_fst_fb n η hη_pos (p, q) htor
  have hq_pos : 0 < q := pos_of_mem_truncatedObtuseRegion_snd_fb n η hη_pos (p, q) htor
  refine Set.mem_Ico.mpr ⟨le_of_lt hp_pos, ?_⟩
  have hq_ge_one : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pos
  have hp1_lt : ((p + 1 : ℤ) : ℝ) < (n : ℝ) / 2 := by push_cast; linarith
  have hp1_le : p + 1 ≤ ↑n / 2 := intLe_half_of_real_lt_half_fb n (p + 1) hp1_lt
  linarith

lemma fiber_finite (n : ℕ) (η : ℝ) (hη_pos : 0 < η) (q : ℤ) :
    {p : ℤ | (p, q) ∈ residueBadPairs n η}.Finite :=
  (Set.finite_Ico (0 : ℤ) (↑n / 2)).subset (fiber_subset_range n η hη_pos q)

lemma counting_large_implies_not_badPairsE (n : ℕ) (η : ℝ) (p q : ℤ)
    (h : (η ^ 2 / 2 : ℝ) * (Nat.totient n : ℝ) ≤ (countingFunctionS n p q : ℝ)) :
    (p, q) ∉ badPairsE n η := by
  intro h_in
  have h₁ : (countingFunctionS n p q : ℝ) < (η ^ 2 / 2 : ℝ) * (Nat.totient n : ℝ) := by
    simp only [Set.mem_setOf_eq, badPairsE, Set.mem_setOf_eq] at h_in
    have h₂ := h_in.2.2
    exact h₂
  have h₃ : ¬((countingFunctionS n p q : ℝ) < (η ^ 2 / 2 : ℝ) * (Nat.totient n : ℝ)) := by
    intro _
    linarith
  exact h₃ h₁

lemma fiber_div_injOn (n d : ℕ) (hd_pos : 0 < d) (b : ℕ)
    (S : Set ℤ) (hS_sub : S ⊆ Set.Ico (0 : ℤ) (↑n / 2)) :
    Set.InjOn (fun x : ℤ => (x / (d : ℤ)).toNat)
      {x ∈ S | (x % (d : ℤ)).toNat = b} := by
  intro x hx y hy hxy
  have hSx : x ∈ Set.Ico (0 : ℤ) (↑n / 2) := hS_sub hx.1
  have hSy : y ∈ Set.Ico (0 : ℤ) (↑n / 2) := hS_sub hy.1
  have hx0 : 0 ≤ x := hSx.1
  have hy0 : 0 ≤ y := hSy.1
  have hx_cond : (x % (d : ℤ)).toNat = b := hx.2
  have hy_cond : (y % (d : ℤ)).toNat = b := hy.2
  have hx_div : (x / (d : ℤ)).toNat = (y / (d : ℤ)).toNat := by simpa using hxy
  have h₃ : (d : ℤ) ≠ 0 := by exact_mod_cast hd_pos.ne'
  have hd0 : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
  have hmod : x % (d : ℤ) = y % (d : ℤ) := by
    have hx' := Int.toNat_of_nonneg (Int.emod_nonneg x h₃)
    have hy' := Int.toNat_of_nonneg (Int.emod_nonneg y h₃)
    omega
  have hdiv : x / (d : ℤ) = y / (d : ℤ) := by
    have hx' := Int.toNat_of_nonneg (Int.ediv_nonneg hx0 hd0)
    have hy' := Int.toNat_of_nonneg (Int.ediv_nonneg hy0 hd0)
    omega
  have ex := Int.emod_add_mul_ediv x (d : ℤ)
  have ey := Int.emod_add_mul_ediv y (d : ℤ)
  rw [hmod, hdiv] at ex
  omega

lemma int_ediv_eq_natCast_div (n : ℤ) (m : ℕ) (_hm : 0 < m) (hn : 0 ≤ n) :
    n / (m : ℤ) = ↑(n.toNat / m) := by simp_all

lemma int_toNat_ediv_eq (n : ℤ) (m : ℕ) (hm : 0 < m) (hn : 0 ≤ n) :
    (n / (m : ℤ)).toNat = n.toNat / m := by
  rw [int_ediv_eq_natCast_div n m hm hn, Int.toNat_natCast]

lemma int_ediv_toNat_le (a b : ℤ) (m : ℕ) (_hm : 0 < m)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (a / (m : ℤ)).toNat ≤ (b / (m : ℤ)).toNat := by
  have h₁ : ∀ (a : ℤ), 0 ≤ a → (a / (m : ℤ)).toNat = a.toNat / m := by grind
  have h₄ : a.toNat ≤ b.toNat := by simp_all
  have h₅ : 0 ≤ b := by nlinarith
  have h₆ : a.toNat / m ≤ b.toNat / m := by exact Nat.div_le_div_right h₄
  have h₇ : (a / (m : ℤ)).toNat ≤ (b / (m : ℤ)).toNat := by simp_all
  assumption

lemma div_toNat_le_half_div (n d : ℕ) (hd_pos : 0 < d) (x : ℤ)
    (hx0 : 0 ≤ x) (hx_lt : x < (↑n : ℤ) / 2) :
    (x / (↑d : ℤ)).toNat ≤ n / (2 * d) := by
  have hx_le : x ≤ (↑n : ℤ) / 2 := le_of_lt hx_lt
  calc (x / (↑d : ℤ)).toNat
      ≤ ((↑n : ℤ) / 2 / (↑d : ℤ)).toNat := int_ediv_toNat_le x (↑n / 2) d hd_pos hx0 hx_le
    _ = ((↑n : ℤ) / 2).toNat / d :=
      int_toNat_ediv_eq (↑n / 2) d hd_pos (Int.ediv_nonneg (Int.natCast_nonneg n) (by norm_num))
    _ = n / 2 / d := by
        have : ((↑n : ℤ) / 2).toNat = n / 2 :=
          int_toNat_ediv_eq (↑n : ℤ) 2 (by norm_num) (Int.natCast_nonneg n)
        rw [this]
    _ = n / (2 * d) := Nat.div_div_eq_div_mul n 2 d

lemma fiber_div_mem_range (n d : ℕ) (hd_pos : 0 < d) (b : ℕ)
    (S : Set ℤ) (hS_sub : S ⊆ Set.Ico (0 : ℤ) (↑n / 2))
    (x : ℤ) (hx : x ∈ {x ∈ S | (x % (d : ℤ)).toNat = b}) :
    (x / (d : ℤ)).toNat ∈ Finset.range (n / (2 * d) + 1) := by
  rw [Finset.mem_range]
  have hxS : x ∈ S := hx.1
  have hxIco := hS_sub hxS
  rw [Set.mem_Ico] at hxIco
  exact Nat.lt_add_one_of_le (div_toNat_le_half_div n d hd_pos x hxIco.1 hxIco.2)

lemma product_ge_eta_sq_n_sq (η : ℝ) (hη_pos : 0 < η)
    (n : ℕ) (hn : 2 ≤ n)
    (p q : ℤ) (hp : η * (n : ℝ) ≤ (p : ℝ)) (hq : η * (n : ℝ) ≤ (q : ℝ)) :
    (η * (n : ℝ)) ^ 2 ≤ (2 * (p : ℝ) - 1) * (2 * (q : ℝ) - 1) := by
  have h₂ : 0 < η * (n : ℝ) := by positivity
  by_cases h₃ : η * (n : ℝ) ≥ 1
  · have h₆ : (2 * (p : ℝ) - 1) * (2 * (q : ℝ) - 1) ≥ (η * (n : ℝ)) * (η * (n : ℝ)) := by
      nlinarith
    nlinarith
  · have h₅ : p ≥ 1 := by
      by_contra h₅₁
      have h₅₂ : p ≤ 0 := by linarith
      have h₅₃ : (p : ℝ) ≤ 0 := by exact_mod_cast h₅₂
      linarith
    have h₆ : q ≥ 1 := by
      by_contra h₆₁
      have h₆₂ : q ≤ 0 := by linarith
      have h₆₃ : (q : ℝ) ≤ 0 := by exact_mod_cast h₆₂
      linarith
    have h₇ : (p : ℝ) ≥ 1 := by exact_mod_cast h₅
    have h₈ : (q : ℝ) ≥ 1 := by exact_mod_cast h₆
    have h₁₁ : (2 * (p : ℝ) - 1) * (2 * (q : ℝ) - 1) ≥ 1 := by
      nlinarith
    have h₁₂ : (η * (n : ℝ)) ^ 2 < 1 := by
      nlinarith
    nlinarith

lemma rearrange_ineq (η : ℝ) (n : ℕ) (hn : 2 ≤ n) (p q : ℤ)
    (h : (η * (n : ℝ)) ^ 2 ≤ (2 * (p : ℝ) - 1) * (2 * (q : ℝ) - 1)) :
    η ^ 2 * (Nat.totient n : ℝ) ≤
      (2 * (p : ℝ) - 1) * (2 * (q : ℝ) - 1) * (Nat.totient n : ℝ) / (n : ℝ) ^ 2 := by
  have h₂ : 0 < (n : ℝ) ^ 2 := by
    positivity
  have h₃ : (η : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ (2 * (p : ℝ) - 1) * (2 * (q : ℝ) - 1) := by
    have h₄ : (η * (n : ℝ)) ^ 2 ≤ (2 * (p : ℝ) - 1) * (2 * (q : ℝ) - 1) := h
    calc
      (η : ℝ) ^ 2 * (n : ℝ) ^ 2 = (η * (n : ℝ)) ^ 2 := by ring
      _ ≤ (2 * (p : ℝ) - 1) * (2 * (q : ℝ) - 1) := h₄
  have h₄ : (η : ℝ) ^ 2 * (Nat.totient n : ℝ) ≤ (2 * (p : ℝ) - 1) * (2 * (q : ℝ) - 1) *
    (Nat.totient n : ℝ) / (n : ℝ) ^ 2 := by
    have h₇ : (η : ℝ) ^ 2 * (Nat.totient n : ℝ) ≤ (2 * (p : ℝ) - 1) * (2 * (q : ℝ) - 1) *
      (Nat.totient n : ℝ) / (n : ℝ) ^ 2 := by
      calc
        (η : ℝ) ^ 2 * (Nat.totient n : ℝ) = ((η : ℝ) ^ 2 * (n : ℝ) ^ 2) * ((Nat.totient n : ℝ) /
          (n : ℝ) ^ 2) := by
          field_simp [h₂.ne']
        _ ≤ ((2 * (p : ℝ) - 1) * (2 * (q : ℝ) - 1)) * ((Nat.totient n : ℝ) / (n : ℝ) ^ 2) := by
          gcongr
        _ = (2 * (p : ℝ) - 1) * (2 * (q : ℝ) - 1) * (Nat.totient n : ℝ) / (n : ℝ) ^ 2 := by
          ring_nf
    exact h₇
  exact h₄

lemma main_term_lower_bound (η : ℝ) (hη_pos : 0 < η)
    (n : ℕ) (hn : 2 ≤ n)
    (p q : ℤ) (hpq : (p, q) ∈ truncatedObtuseRegion n η) :
    η ^ 2 * (Nat.totient n : ℝ) ≤
      (2 * ↑p - 1) * (2 * ↑q - 1) * (Nat.totient n : ℝ) / (n : ℝ) ^ 2 := by
  obtain ⟨hp, hq, _, _⟩ := hpq
  exact rearrange_ineq η n hn p q (product_ge_eta_sq_n_sq η hη_pos n hn p q hp hq)

/-- The complex-valued indicator function of `intervalSet n m` on `ZMod n`. -/
noncomputable def intervalIndicator (n : ℕ) (m : ℕ) : ZMod n → ℂ :=
  (intervalSet n m).indicator (fun _ => 1)

/-- The normalised discrete Fourier transform of `f : ZMod n → ℂ`, scaled by `(n : ℂ)⁻¹`. -/
noncomputable def normalizedDFT (n : ℕ) [NeZero n] (f : ZMod n → ℂ) (k : ZMod n) : ℂ :=
  ((n : ℂ)⁻¹) * ZMod.dft f k

/-- The Ramanujan sum `c_n(t)`, written via the standard additive character of `ZMod n`. -/
noncomputable def ramanujanSum (n : ℕ) [NeZero n] (t : ℤ) : ℂ :=
  ∑ a : (ZMod n)ˣ, ZMod.stdAddChar (a.val * (t : ZMod n))

lemma toNat_two_mul_sub_one (p : ℤ) (hp : 1 ≤ p) :
    ((2 * p - 1).toNat : ℝ) = 2 * (p : ℝ) - 1 := by
  have h₁ : 0 ≤ 2 * p - 1 := by
    omega
  have h₂ : (2 * p - 1).toNat = 2 * p - 1 := by
    norm_cast
    simp_all
    omega
  norm_cast at h₂ ⊢

lemma indicator_product_eq_ite (n : ℕ) (mp mq : ℕ) (x y : ZMod n) :
    intervalIndicator n mp x * intervalIndicator n mq y =
    if (x ∈ intervalSet n mp ∧ y ∈ intervalSet n mq) then (1 : ℂ) else 0 := by
  have h_main : intervalIndicator n mp x * intervalIndicator n mq y = if (x ∈ intervalSet n mp ∧ y ∈
    intervalSet n mq) then (1 : ℂ) else 0 := by
    dsimp [intervalIndicator]
    by_cases hx : x ∈ intervalSet n mp
    · by_cases hy : y ∈ intervalSet n mq
      · simp [hx, hy]
      · simp [hx, hy]
    · by_cases hy : y ∈ intervalSet n mq
      · simp [hx, hy]
      · simp [hx, hy]
  exact h_main

lemma counting_as_indicator_product (n : ℕ) (p q : ℤ) (hn : 2 ≤ n)
    (_hp : 1 ≤ p) (_hq : 1 ≤ q) (_hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    haveI : NeZero n := ⟨by omega⟩
    (countingFunctionS n p q : ℂ) =
      ∑ a : (ZMod n)ˣ,
        intervalIndicator n (2 * p - 1).toNat (a.val * (p : ZMod n)) *
        intervalIndicator n (2 * q - 1).toNat (a.val * (q : ZMod n)) := by
  haveI : NeZero n := ⟨by omega⟩
  simp only [countingFunctionS, dif_neg (by omega : ¬n = 0)]
  rw [← Finset.sum_boole]
  congr 1
  ext a
  exact (indicator_product_eq_ite n _ _ _ _).symm

lemma fourier_inversion (n : ℕ) [NeZero n] (f : ZMod n → ℂ) (x : ZMod n) :
    f x = ∑ k : ZMod n,
      normalizedDFT n f k * ZMod.stdAddChar (k * x) := by
  have h₁ : (ZMod.dft.symm : (ZMod n → ℂ) ≃ₗ[ℂ] (ZMod n → ℂ)) (ZMod.dft f) = f := by
    apply LinearEquiv.symm_apply_apply
  have h₂ : (ZMod.dft.symm : (ZMod n → ℂ) ≃ₗ[ℂ] (ZMod n → ℂ)) (ZMod.dft f) = (fun x =>
    (↑(n : ℕ) : ℂ)⁻¹ • (∑ (k : ZMod n), ZMod.stdAddChar (k * x) • (ZMod.dft f) k)) := by
    ext x
    simp [ZMod.invDFT_apply]
  have h₃ : f x = (∑ k : ZMod n, normalizedDFT n f k * ZMod.stdAddChar (k * x)) := by
    calc
      f x = (ZMod.dft.symm (ZMod.dft f)) x := by
        rw [h₁]
      _ = (↑(n : ℕ) : ℂ)⁻¹ • (∑ (k : ZMod n), ZMod.stdAddChar (k * x) • (ZMod.dft f) k) := by
        rw [h₂]
      _ = ∑ (k : ZMod n), ((↑(n : ℕ) : ℂ)⁻¹ • (ZMod.dft f) k) * ZMod.stdAddChar (k * x) := by
        simp [smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm]
      _ = ∑ (k : ZMod n), normalizedDFT n f k * ZMod.stdAddChar (k * x) := by
        apply Finset.sum_congr rfl
        intro k _
        simp [normalizedDFT]
  exact h₃

lemma three_sum_comm {α : Type*} {β : Type*} {γ : Type*} {R : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid R]
    (f : α → β → γ → R) :
    (∑ a : α, ∑ b : β, ∑ c : γ, f a b c) =
    (∑ b : β, ∑ c : γ, ∑ a : α, f a b c) := by
  rw [Finset.sum_comm]; congr 1; ext b; rw [Finset.sum_comm]

lemma sum_product_interchange_units (n : ℕ) [NeZero n]
    (c : ZMod n → ℂ) (d : ZMod n → ℂ)
    (f : ZMod n → (ZMod n)ˣ → ℂ) (g : ZMod n → (ZMod n)ˣ → ℂ) :
    (∑ a : (ZMod n)ˣ,
      (∑ k : ZMod n, c k * f k a) * (∑ l : ZMod n, d l * g l a)) =
    ∑ k : ZMod n, ∑ l : ZMod n,
      c k * d l * (∑ a : (ZMod n)ˣ, f k a * g l a) := by
  simp_rw [Fintype.sum_mul_sum]
  simp_rw [show ∀ (k : ZMod n) (l : ZMod n) (a : (ZMod n)ˣ),
      c k * f k a * (d l * g l a) = c k * d l * (f k a * g l a) by
    intros; ring]
  rw [three_sum_comm]
  simp_rw [show ∀ (k : ZMod n) (l : ZMod n),
      (∑ a : (ZMod n)ˣ, c k * d l * (f k a * g l a)) =
      c k * d l * (∑ a : (ZMod n)ˣ, f k a * g l a) by
    intros k l
    rw [← Finset.mul_sum]]

lemma interchange_and_factor (n : ℕ) (p q : ℤ) (hn : 2 ≤ n)
    (_ : 1 ≤ p) (_ : 1 ≤ q) (_ : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    haveI : NeZero n := ⟨by omega⟩
    (∑ a : (ZMod n)ˣ,
      intervalIndicator n (2 * p - 1).toNat (a.val * (p : ZMod n)) *
      intervalIndicator n (2 * q - 1).toNat (a.val * (q : ZMod n)) : ℂ) =
    ∑ k : ZMod n, ∑ l : ZMod n,
      normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
      normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
      (∑ a : (ZMod n)ˣ,
        ZMod.stdAddChar (k * (a.val * (p : ZMod n))) *
        ZMod.stdAddChar (l * (a.val * (q : ZMod n))) : ℂ) := by
  haveI : NeZero n := ⟨by omega⟩
  simp_rw [fourier_inversion n (intervalIndicator n (2 * p - 1).toNat),
           fourier_inversion n (intervalIndicator n (2 * q - 1).toNat)]
  exact sum_product_interchange_units n
    (fun k => normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k)
    (fun l => normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l)
    (fun k a => ZMod.stdAddChar (k * (a.val * (p : ZMod n))))
    (fun l a => ZMod.stdAddChar (l * (a.val * (q : ZMod n))))

lemma character_product_simplify (n : ℕ) [NeZero n] (k l : ZMod n) (p q : ℤ) :
    (∑ a : (ZMod n)ˣ,
      ZMod.stdAddChar (k * (a.val * (p : ZMod n))) *
      ZMod.stdAddChar (l * (a.val * (q : ZMod n))) : ℂ) =
    ramanujanSum n (ZMod.val k * p + ZMod.val l * q) := by
  have h₁ : (∑ a : (ZMod n)ˣ,
    ZMod.stdAddChar (k * (a.val * (p : ZMod n))) * ZMod.stdAddChar (l * (a.val *
      (q : ZMod n))) : ℂ) = (∑ a : (ZMod n)ˣ,
        ZMod.stdAddChar ( (k * (a.val * (p : ZMod n)) + l * (a.val *
          (q : ZMod n)) : ZMod n) ) : ℂ) :=
            by congr 1; ext a; exact (ZMod.stdAddChar.map_add_eq_mul _ _).symm
  have h₂ : (∑ a : (ZMod n)ˣ,
    ZMod.stdAddChar ( (k * (a.val * (p : ZMod n)) + l * (a.val * (q : ZMod n)) : ZMod n) ) : ℂ) =
      (∑ a : (ZMod n)ˣ,
        ZMod.stdAddChar ( ( (a : ZMod n) * (k * (p : ZMod n) + l * (q : ZMod n)) : ZMod n) ) : ℂ) :=
          by group
  have h₃ : (∑ a : (ZMod n)ˣ,
    ZMod.stdAddChar ( ( (a : ZMod n) * (k * (p : ZMod n) + l * (q : ZMod n)) : ZMod n) ) : ℂ) =
      (∑ a : (ZMod n)ˣ,
        ZMod.stdAddChar ( ( (a.val : ZMod n) * (k * (p : ZMod n) + l *
          (q : ZMod n)) : ZMod n) ) : ℂ) := by rfl
  have h₄ : (∑ a : (ZMod n)ˣ,
    ZMod.stdAddChar ( ( (a.val : ZMod n) * (k * (p : ZMod n) + l * (q : ZMod n)) : ZMod n) ) : ℂ) =
      (∑ a : (ZMod n)ˣ,
        ZMod.stdAddChar ( (a.val * ( (ZMod.val k * p + ZMod.val l * q : ℤ) : ZMod n)) : ZMod n) ) :=
          by simp
  have h₅ : (∑ a : (ZMod n)ˣ,
    ZMod.stdAddChar ( (a.val * ( (ZMod.val k * p + ZMod.val l * q : ℤ) : ZMod n)) : ZMod n) ) =
      ramanujanSum n (ZMod.val k * p + ZMod.val l * q) := by rfl
  calc
    (∑ a : (ZMod n)ˣ,
      ZMod.stdAddChar (k * (a.val * (p : ZMod n))) * ZMod.stdAddChar (l * (a.val *
        (q : ZMod n))) : ℂ) = (∑ a : (ZMod n)ˣ,
          ZMod.stdAddChar ( (k * (a.val * (p : ZMod n)) + l * (a.val *
            (q : ZMod n)) : ZMod n) ) : ℂ) := by rw [h₁]
    _ = (∑ a : (ZMod n)ˣ,
      ZMod.stdAddChar ( ( (a : ZMod n) * (k * (p : ZMod n) + l * (q : ZMod n)) : ZMod n) ) : ℂ) :=
        by rw [h₂]
    _ = (∑ a : (ZMod n)ˣ,
      ZMod.stdAddChar ( ( (a.val : ZMod n) * (k * (p : ZMod n) + l *
        (q : ZMod n)) : ZMod n) ) : ℂ) := by rw [h₃]
    _ = (∑ a : (ZMod n)ˣ,
      ZMod.stdAddChar ( (a.val * ( (ZMod.val k * p + ZMod.val l * q : ℤ) : ZMod n)) : ZMod n) ) :=
        by rw [h₄]
    _ = ramanujanSum n (ZMod.val k * p + ZMod.val l * q) := by rw [h₅]

lemma counting_eq_fourier_ramanujan_sum
    (n : ℕ) (hn : 2 ≤ n)
    (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    haveI : NeZero n := ⟨by omega⟩
    (countingFunctionS n p q : ℂ) =
      ∑ k : ZMod n, ∑ l : ZMod n,
        normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
        normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
        ramanujanSum n (ZMod.val k * p + ZMod.val l * q) := by
  haveI : NeZero n := ⟨by omega⟩
  rw [counting_as_indicator_product n p q hn hp hq hpq]
  rw [interchange_and_factor n p q hn hp hq hpq]
  simp_rw [character_product_simplify n]

lemma largestPrimeFactor_pos_helper_fb (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : ℕ, n.primeFactors.max = ↑a ∧ 0 < a := by
  have h₁ : 1 < n := by omega
  have h₂ : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr h₁
  obtain ⟨a, ha⟩ := Finset.max_of_nonempty h₂
  exact ⟨a, ha, Nat.pos_of_mem_primeFactors (Finset.mem_of_max ha)⟩

lemma largestPrimeFactor_ge_two (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ largestPrimeFactor n := by
  obtain ⟨a, ha_max, _ha_pos⟩ := largestPrimeFactor_pos_helper_fb n hn
  have ha_mem : a ∈ n.primeFactors := Finset.mem_of_max ha_max
  have ha_prime : Nat.Prime a := Nat.prime_of_mem_primeFactors ha_mem
  have ha_two_le : 2 ≤ a := ha_prime.two_le
  change 2 ≤ largestPrimeFactor n
  unfold largestPrimeFactor
  rw [ha_max]
  exact ha_two_le


lemma ceil_log_ge_one (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ ⌈Real.log (n : ℝ)⌉₊ := by
  have h₁ : (1 : ℝ) < (n : ℝ) := by
    norm_cast
  have h₂ : 0 < Real.log (n : ℝ) := Real.log_pos h₁
  have h₃ : 1 ≤ ⌈Real.log (n : ℝ)⌉₊ := by
    have h₅ : 1 ≤ ⌈Real.log (n : ℝ)⌉₊ := by
      by_contra h
      have h₆ : ⌈Real.log (n : ℝ)⌉₊ = 0 := by
        have h₉ : ⌈Real.log (n : ℝ)⌉₊ = 0 := by
          omega
        exact h₉
      have h₁₀ : (⌈Real.log (n : ℝ)⌉₊ : ℝ) = 0 := by norm_cast
      have h₁₁ : Real.log (n : ℝ) ≤ 0 := by
        have h₁₂ : Real.log (n : ℝ) ≤ ⌈Real.log (n : ℝ)⌉₊ := Nat.le_ceil _
        linarith
      linarith
    exact h₅
  exact h₃

lemma bound_first_term (P R A : ℝ) (hP : 2 ≤ P) (hR : 1 ≤ R) (hA : 0 ≤ A) :
    A / (P - 1) ≤ 2 * R * A / P := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hP1 : (0 : ℝ) < P - 1 := by linarith
  rw [div_le_div_iff₀ hP1 hP0]
  nlinarith [mul_nonneg hA (by linarith : (0 : ℝ) ≤ P - 1),
             mul_nonneg hA (by linarith : (0 : ℝ) ≤ R - 1),
             mul_nonneg (by linarith : (0 : ℝ) ≤ R - 1) (mul_nonneg hA (by linarith : (0 : ℝ) ≤ P -
               1))]

lemma combine_error_terms_real (P R A : ℝ) (hP : 2 ≤ P) (hR : 1 ≤ R) (hA : 0 ≤ A) :
    A / (P - 1) + 7 * R * A / P ≤ 9 * R * A / P := by
  have hP0 : (0 : ℝ) < P := by linarith
  have h := bound_first_term P R A hP hR hA
  have h2 : 2 * R * A / P + 7 * R * A / P = 9 * R * A / P := by ring
  linarith


/-- The error term `E_{P₀}(p, q)`: the contribution of frequencies `(k, l)` with
`P ^ (α - 1) ∣ k * p + l * q` but `P ^ α ∤ k * p + l * q` to the Fourier expansion. -/
noncomputable def errorTermEP0 (n : ℕ) [NeZero n] (p q : ℤ) : ℂ :=
  let P := largestPrimeFactor n
  let alpha := n.factorization P
  let P0 := P ^ (alpha - 1)
  let d := P ^ alpha
  let fp := intervalIndicator n (2 * p - 1).toNat
  let fq := intervalIndicator n (2 * q - 1).toNat
  ∑ k : ZMod n, ∑ l : ZMod n,
    if (k, l) ≠ (0, 0) ∧
       (P0 : ℤ) ∣ (ZMod.val k * p + ZMod.val l * q) ∧
       ¬((d : ℤ) ∣ (ZMod.val k * p + ZMod.val l * q))
    then normalizedDFT n fp k * normalizedDFT n fq l *
         ramanujanSum n (ZMod.val k * p + ZMod.val l * q)
    else 0

/-- The error term `E_{P^α}(p, q)`: the contribution of nonzero frequencies `(k, l)` with
`P ^ α ∣ k * p + l * q` to the Fourier expansion of `countingFunctionS`. -/
noncomputable def errorTermEPalpha (n : ℕ) [NeZero n] (p q : ℤ) : ℂ :=
  let P := largestPrimeFactor n
  let alpha := n.factorization P
  let d := P ^ alpha
  let fp := intervalIndicator n (2 * p - 1).toNat
  let fq := intervalIndicator n (2 * q - 1).toNat
  ∑ k : ZMod n, ∑ l : ZMod n,
    if (k, l) ≠ (0, 0) ∧
       (d : ℤ) ∣ (ZMod.val k * p + ZMod.val l * q)
    then normalizedDFT n fp k * normalizedDFT n fq l *
         ramanujanSum n (ZMod.val k * p + ZMod.val l * q)
    else 0



lemma zmod_mul_as_cast (n : ℕ) [NeZero n] (k : ZMod n) (p : ℤ) :
    k * (p : ZMod n) = ((ZMod.val k * p : ℤ) : ZMod n) := by
  have h₅ : (k : ZMod n) * (p : ZMod n) = ((ZMod.val k * p : ℤ) : ZMod n) := by simp
  assumption

lemma factor_and_combine_chars (n : ℕ) [NeZero n] (k l : ZMod n) (a : (ZMod n)ˣ) (p q : ℤ) :
    ZMod.stdAddChar (k * (a.val * (p : ZMod n))) *
    ZMod.stdAddChar (l * (a.val * (q : ZMod n))) =
    ZMod.stdAddChar (a.val * (k * (p : ZMod n) + l * (q : ZMod n))) := by
  have h_main : (k * (a.val * (p : ZMod n)) + l * (a.val * (q : ZMod n)) : ZMod n) = (a.val * (k *
    (p : ZMod n) + l * (q : ZMod n)) : ZMod n) := by ring
  have h_char_prod : ZMod.stdAddChar (k * (a.val * (p : ZMod n))) * ZMod.stdAddChar (l * (a.val *
    (q : ZMod n))) = ZMod.stdAddChar (k * (a.val * (p : ZMod n)) + l * (a.val * (q : ZMod n))) :=
      by exact (ZMod.stdAddChar.map_add_eq_mul _ _).symm
  have h_final : ZMod.stdAddChar (k * (a.val * (p : ZMod n))) * ZMod.stdAddChar (l * (a.val *
    (q : ZMod n))) = ZMod.stdAddChar (a.val * (k * (p : ZMod n) + l * (q : ZMod n))) := by simp_all
  assumption

lemma ramanujanSum_zero (n : ℕ) [NeZero n] :
    ramanujanSum n 0 = (Nat.totient n : ℂ) := by
  have h1 : ramanujanSum n 0 = ∑ _ : (ZMod n)ˣ, (1 : ℂ) := by
    calc
      ramanujanSum n 0 = ∑ a : (ZMod n)ˣ, ZMod.stdAddChar (a.val * (0 : ZMod n)) := by
        simp [ramanujanSum]
      _ = ∑ _ : (ZMod n)ˣ, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro a _
        have h₂ : (a.val : ZMod n) * (0 : ZMod n) = 0 := by
          simp [mul_zero]
        have h₃ : ZMod.stdAddChar (a.val * (0 : ZMod n)) = (1 : ℂ) := by
          rw [h₂]
          simp [ZMod.stdAddChar]
        rw [h₃]
  have h2 : (∑ _ : (ZMod n)ˣ, (1 : ℂ)) = (Fintype.card (ZMod n)ˣ : ℂ) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have h3 : (Fintype.card (ZMod n)ˣ : ℂ) = (Nat.totient n : ℂ) := by
    have h₄ : Fintype.card (ZMod n)ˣ = Nat.totient n := by
      apply ZMod.card_units_eq_totient
    rw [h₄]
  calc
    ramanujanSum n 0 = ∑ _ : (ZMod n)ˣ, (1 : ℂ) := h1
    _ = (Fintype.card (ZMod n)ˣ : ℂ) := h2
    _ = (Nat.totient n : ℂ) := h3

lemma card_intervalSet_filter (n : ℕ) [NeZero n] (m : ℕ) (hm2 : m < n) :
    (Finset.univ.filter (fun j : ZMod n =>
      1 ≤ ZMod.val j ∧ ZMod.val j ≤ m)).card = m := by
  have h := Finset.card_bij'
    (i := fun (t : ℕ) (_ : t ∈ Finset.Icc 1 m) => (t : ZMod n))
    (j := fun (j : ZMod n)
      (_ : j ∈ Finset.univ.filter (fun j : ZMod n => 1 ≤ ZMod.val j ∧ ZMod.val j ≤ m)) =>
      ZMod.val j)
    (hi := fun t ht => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have htm := Finset.mem_Icc.mp ht
      constructor
      · rw [ZMod.val_natCast_of_lt (by omega)]
        exact htm.1
      · rw [ZMod.val_natCast_of_lt (by omega)]
        exact htm.2)
    (hj := fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_Icc.mpr hj)
    (left_inv := fun t ht => by
      have htm := Finset.mem_Icc.mp ht
      exact ZMod.val_natCast_of_lt (by omega))
    (right_inv := fun j _ => ZMod.natCast_zmod_val j)
  rw [Nat.card_Icc] at h
  omega

lemma sum_intervalIndicator_eq (n : ℕ) [NeZero n] (m : ℕ) (_hm1 : 1 ≤ m) (hm2 : m < n) :
    ∑ x : ZMod n, intervalIndicator n m x = (m : ℂ) := by
  simp only [intervalIndicator, intervalSet, Set.indicator_apply, Set.mem_setOf_eq,
    Finset.sum_boole]
  exact_mod_cast card_intervalSet_filter n m hm2

lemma normalizedDFT_intervalIndicator_zero (n : ℕ) [NeZero n] (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m < n) :
    normalizedDFT n (intervalIndicator n m) 0 = (m : ℂ) / (n : ℂ) := by
  simp only [normalizedDFT, ZMod.dft_apply_zero]
  rw [sum_intervalIndicator_eq n m hm1 hm2]
  ring

lemma mp_lower_bound (p : ℤ) (hp : 1 ≤ p) :
    1 ≤ (2 * p - 1).toNat := by
  have h₃ : 1 ≤ (2 * p - 1).toNat := by
    have h₇ : (2 * p - 1).toNat ≥ 1 := by
      have h₉ : (2 * p - 1).toNat ≥ 1 := by
        have h₁₂ : (2 * p - 1).toNat ≥ 1 := by
          have h₁₃ : (2 * p - 1 : ℤ) ≥ 1 := by linarith
          have h₁₄ : (2 * p - 1).toNat ≥ 1 := by
            norm_cast at h₁₃ ⊢
            omega
          exact h₁₄
        exact h₁₂
      exact h₉
    exact h₇
  exact h₃

lemma mp_upper_bound (n : ℕ) (_hn : 2 ≤ n) (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    (2 * p - 1).toNat < n := by
  have h₁ : 2 * p - 1 < n := by
    have h₃ : (q : ℝ) ≥ 1 := by exact_mod_cast hq
    have h₉ : (2 : ℝ) * (p : ℝ) - 1 < (n : ℝ) := by
      linarith
    have h₁₀ : (2 : ℤ) * p - 1 < (n : ℤ) := by
      have h₁₀₁ : (2 : ℝ) * (p : ℝ) - 1 < (n : ℝ) := h₉
      have h₁₀₂ : (2 : ℝ) * (p : ℝ) - 1 = ((2 : ℤ) * p - 1 : ℝ) := by
        norm_cast
      have h₁₀₃ : ((2 : ℤ) * p - 1 : ℝ) < (n : ℝ) := by
        rw [h₁₀₂] at h₁₀₁
        exact h₁₀₁
      have h₁₀₄ : ((2 : ℤ) * p - 1 : ℤ) < (n : ℤ) := by
        norm_cast at h₁₀₃ ⊢
      exact_mod_cast h₁₀₄
    exact_mod_cast h₁₀
  have h₃ : (2 * p - 1).toNat < n := by
    have h₄ : (2 * p - 1 : ℤ) < n := by exact_mod_cast h₁
    have h₆ : (2 * p - 1).toNat < n := by
      rw [Int.toNat_lt (by linarith)]
      norm_cast at h₄ ⊢
    exact h₆
  exact h₃

lemma mp_valid (n : ℕ) (hn : 2 ≤ n) (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    1 ≤ (2 * p - 1).toNat ∧ (2 * p - 1).toNat < n := by
  exact ⟨mp_lower_bound p hp, mp_upper_bound n hn p q hp hq hpq⟩

lemma mq_valid (n : ℕ) (_hn : 2 ≤ n) (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    1 ≤ (2 * q - 1).toNat ∧ (2 * q - 1).toNat < n := by
  have h₁ : (2 * q - 1 : ℤ) ≥ 1 := by
    have : (q : ℤ) ≥ 1 := by exact_mod_cast hq
    linarith
  have h₂ : (2 * q - 1 : ℤ) < (n : ℤ) := by
    have h₄ : (q : ℝ) < (n : ℝ) / 2 := by
      have : (p : ℝ) ≥ 1 := by exact_mod_cast hp
      linarith
    have h₅ : (q : ℝ) * 2 < (n : ℝ) := by linarith
    have h₆ : (q : ℤ) * 2 < (n : ℤ) := by
      norm_cast at h₅ ⊢
    have h₇ : (2 * q - 1 : ℤ) < (n : ℤ) := by
      have : (2 : ℤ) * q = q * 2 := by ring
      rw [this] at *
      linarith
    exact h₇
  have h₃ : 1 ≤ (2 * q - 1).toNat := by
    have h₆ : (2 * q - 1).toNat = (2 * q - 1 : ℤ).toNat := rfl
    rw [h₆]
    norm_cast
    (try omega)
  have h₄ : (2 * q - 1).toNat < n := by
    have h₆ : (2 * q - 1 : ℤ) ≥ 0 := by
      have : (2 * q - 1 : ℤ) ≥ 1 := h₁
      linarith
    have h₇ : (2 * q - 1).toNat = (2 * q - 1 : ℤ).toNat := rfl
    rw [h₇]
    have h₈ : ((2 * q - 1 : ℤ).toNat : ℤ) = (2 * q - 1 : ℤ) := by
      rw [Int.toNat_of_nonneg h₆]
    have h₉ : ((2 * q - 1 : ℤ).toNat : ℤ) < (n : ℤ) := by
      linarith
    norm_cast at h₉ ⊢
  exact ⟨h₃, h₄⟩

lemma zero_zero_term_eq_main
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) 0 *
    normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) 0 *
    ramanujanSum n (↑(ZMod.val (0 : ZMod n)) * p + ↑(ZMod.val (0 : ZMod n)) * q) =
    ((2 * p - 1).toNat : ℂ) * ((2 * q - 1).toNat : ℂ) *
      (Nat.totient n : ℂ) / (n : ℂ) ^ 2 := by
  have hmp := mp_valid n hn p q hp hq hpq
  have hmq := mq_valid n hn p q hp hq hpq
  simp only [ZMod.val_zero, Nat.cast_zero, zero_mul, zero_add]
  rw [ramanujanSum_zero]
  rw [normalizedDFT_intervalIndicator_zero n _ hmp.1 hmp.2]
  rw [normalizedDFT_intervalIndicator_zero n _ hmq.1 hmq.2]
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

lemma full_sum_split_zero_nonzero
    (n : ℕ) [NeZero n] (F : ZMod n → ZMod n → ℂ) :
    ∑ k : ZMod n, ∑ l : ZMod n, F k l =
    F 0 0 +
    ∑ k : ZMod n, ∑ l : ZMod n,
      if ¬(k = 0 ∧ l = 0) then F k l else 0 := by
  have h₁ : (∑ k : ZMod n, ∑ l : ZMod n, F k l) = F 0 0 + ∑ k : ZMod n, ∑ l : ZMod n,
    if (¬(k = 0 ∧ l = 0)) then F k l else 0 := by
    calc
      (∑ k : ZMod n, ∑ l : ZMod n, F k l) =
          ∑ k : ZMod n, ∑ l : ZMod n, (if (k = 0 ∧ l = 0) then F k l else F k l) := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        by_cases h : k = 0 ∧ l = 0 <;> simp [h]
      _ = ∑ k : ZMod n, ∑ l : ZMod n,
        ((if (k = 0 ∧ l = 0) then (F 0 0) else 0) + (if (¬(k = 0 ∧ l = 0)) then F k l else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        by_cases h : k = 0 ∧ l = 0 <;> simp [h]
      _ = ∑ k : ZMod n, ∑ l : ZMod n,
        ((if (k = 0 ∧ l = 0) then (F 0 0) else 0) + (if (¬(k = 0 ∧ l = 0)) then F k l else 0)) :=
          by rfl
      _ = (∑ k : ZMod n, ∑ l : ZMod n, (if (k = 0 ∧ l = 0) then (F 0 0) else 0)) + ∑ k : ZMod n,
        ∑ l : ZMod n, (if (¬(k = 0 ∧ l = 0)) then F k l else 0) := by
        have h₂ : (∑ k : ZMod n, ∑ l : ZMod n,
          ((if (k = 0 ∧ l = 0) then (F 0 0) else 0) + (if (¬(k = 0 ∧ l = 0)) then F k l else 0))) =
            (∑ k : ZMod n, ∑ l : ZMod n, (if (k = 0 ∧ l = 0) then (F 0 0) else 0)) + ∑ k : ZMod n,
              ∑ l : ZMod n, (if (¬(k = 0 ∧ l = 0)) then F k l else 0) := by
          simp [Finset.sum_add_distrib]
        rw [h₂]
      _ = F 0 0 + ∑ k : ZMod n, ∑ l : ZMod n, (if (¬(k = 0 ∧ l = 0)) then F k l else 0) := by
        have h₃ : (∑ k : ZMod n, ∑ l : ZMod n, (if (k = 0 ∧ l = 0) then (F 0 0) else 0)) = F 0 0 :=
          by
          calc
            (∑ k : ZMod n, ∑ l : ZMod n, (if (k = 0 ∧ l = 0) then (F 0 0) else 0)) =
                ∑ k : ZMod n, ∑ l : ZMod n, if (k = 0 ∧ l = 0) then (F 0 0) else 0 := by rfl
            _ = F 0 0 := by
              calc
                (∑ k : ZMod n, ∑ l : ZMod n, if (k = 0 ∧ l = 0) then (F 0 0) else 0) =
                    ∑ k : ZMod n, (∑ l : ZMod n, if (k = 0 ∧ l = 0) then (F 0 0) else 0) := by
                  simp [Finset.sum_sigma']
                _ = ∑ k : ZMod n, if (k = 0) then (F 0 0) else 0 := by
                  apply Finset.sum_congr rfl
                  intro k _
                  calc
                    (∑ l : ZMod n, if (k = 0 ∧ l = 0) then (F 0 0) else 0) =
                        ∑ l : ZMod n, if (k = 0 ∧ l = 0) then (F 0 0) else 0 := by rfl
                    _ = if (k = 0) then (F 0 0) else 0 := by
                      by_cases hk : k = 0
                      · simp [hk]
                      · simp [hk]
                _ = F 0 0 := by
                  calc
                    (∑ k : ZMod n, if (k = 0) then (F 0 0) else 0) =
                        ∑ k : ZMod n, if (k = 0) then (F 0 0) else 0 := by rfl
                    _ = F 0 0 := by
                      calc
                        (∑ k : ZMod n, if (k = 0) then (F 0 0) else 0) =
                            ∑ k : ZMod n, if (k = 0) then (F 0 0) else 0 := by rfl
                        _ = F 0 0 := by
                          have h₄ : (∑ k : ZMod n, if (k = 0) then (F 0 0) else 0) = F 0 0 := by
                            calc
                              (∑ k : ZMod n, if (k = 0) then (F 0 0) else 0) =
                                  ∑ k : ZMod n, if (k = 0) then (F 0 0) else 0 := by rfl
                              _ = F 0 0 := by
                                have h₅ : (∑ k : ZMod n, if (k = 0) then (F 0 0) else 0) = F 0 0 :=
                                  by
                                  calc
                                    (∑ k : ZMod n, if (k = 0) then (F 0 0) else 0) =
                                        (if ((0 : ZMod n) = 0) then (F 0 0) else 0) := by
                                      have h₆ : (∑ k : ZMod n, if (k = 0) then (F 0 0) else 0) =
                                          (if ((0 : ZMod n) = 0) then (F 0 0) else 0) := by
                                        simp
                                      rw [h₆]
                                    _ = F 0 0 := by simp
                                rw [h₅]
                          rw [h₄]
        rw [h₃]
  rw [h₁]

lemma sum_stdAddChar_mul_eq (n : ℕ) [NeZero n] (t : ℤ) :
    ∑ a : ZMod n, ZMod.stdAddChar (a * (t : ZMod n)) =
    if (n : ℤ) ∣ t then (n : ℂ) else 0 := by
  have h2 : ∑ a : ZMod n, ZMod.stdAddChar (a * (t : ZMod n)) =
      (if (t : ZMod n) = 0 then (n : ℂ) else 0) := by
    simp [AddChar.sum_mulShift, ZMod.isPrimitive_stdAddChar, ZMod.card]
  have h3 : (t : ZMod n) = 0 ↔ (n : ℤ) ∣ t :=
    ZMod.intCast_zmod_eq_zero_iff_dvd t n
  rw [h2]
  simp only [h3]

lemma sum_filter_units_eq_sum_units (n : ℕ) [NeZero n] (f : ZMod n → ℂ) :
    ∑ a ∈ Finset.univ.filter (fun a : ZMod n => IsUnit a), f a =
    ∑ u : (ZMod n)ˣ, f u.val := by
  rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  exact Fintype.sum_equiv
    { toFun := fun x => x.prop.unit
      invFun := fun u => ⟨u.val, Units.isUnit u⟩
      left_inv := fun x => by ext; exact IsUnit.unit_spec x.prop
      right_inv := fun u => IsUnit.unit_of_val_units (Units.isUnit u) }
    _ _ (fun x => by simp)

lemma sum_eq_ramanujanSum_add_sum_nonunits (n : ℕ) [NeZero n] (t : ℤ) :
    (∑ a : ZMod n, ZMod.stdAddChar (a * (t : ZMod n))) =
    ramanujanSum n t +
    ∑ a ∈ Finset.univ.filter (fun a : ZMod n => ¬ IsUnit a),
      ZMod.stdAddChar (a * (t : ZMod n)) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : ZMod n => IsUnit a)
    (fun a => ZMod.stdAddChar (a * (t : ZMod n))),
    show ∑ a ∈ Finset.univ.filter (fun a : ZMod n => IsUnit a),
      ZMod.stdAddChar (a * (t : ZMod n)) = ramanujanSum n t from
      sum_filter_units_eq_sum_units n _]

lemma p_mul_pow_pred {p k : ℕ} (hk : 0 < k) : p * p ^ (k - 1) = p ^ k := by
  cases k with
  | zero => omega
  | succ n => simp [pow_succ, mul_comm]

/-- Lift a residue mod `p ^ (k - 1)` to a (non-unit) residue mod `p ^ k` by multiplying by `p`. -/
noncomputable def nonunitFwd {p k : ℕ} (b : ZMod (p ^ (k - 1))) : ZMod (p ^ k) :=
  (p : ZMod (p ^ k)) * (b.val : ZMod (p ^ k))

/-- Send a residue mod `p ^ k` to the residue mod `p ^ (k - 1)` got by dividing its value by `p`. -/
noncomputable def nonunitBwd {p k : ℕ} (a : ZMod (p ^ k)) : ZMod (p ^ (k - 1)) :=
  (a.val / p : ℕ)

lemma val_nonunitFwd {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (hk : 0 < k)
    (b : ZMod (p ^ (k - 1))) :
    (nonunitFwd (p := p) (k := k) b).val = p * b.val := by
  unfold nonunitFwd
  rw [ZMod.val_mul, ZMod.val_natCast, ZMod.val_natCast, ← Nat.mul_mod, Nat.mod_eq_of_lt]
  nlinarith [ZMod.val_lt b, hp.out.pos, p_mul_pow_pred hk (p := p)]

lemma nonunitFwd_not_isUnit {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (hk : 0 < k)
    (b : ZMod (p ^ (k - 1))) :
    ¬ IsUnit (nonunitFwd b) := by
  intro ⟨u, hu⟩
  have hcop := ZMod.val_coe_unit_coprime u
  rw [hu, val_nonunitFwd hk b] at hcop
  exact (hp.out.coprime_iff_not_dvd.mp (hcop.of_dvd_left (dvd_mul_right p b.val)))
    (dvd_pow_self p (by omega))

lemma nonunitBwd_nonunitFwd {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (hk : 0 < k)
    (b : ZMod (p ^ (k - 1))) :
    nonunitBwd (nonunitFwd (p := p) (k := k) b) = b := by
  simp [nonunitBwd, val_nonunitFwd hk b, Nat.mul_div_cancel_left _ hp.out.pos,
    ZMod.natCast_val, ZMod.cast_id]

lemma p_dvd_val_of_not_isUnit {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ}
    (a : ZMod (p ^ k)) (ha : ¬ IsUnit a) : p ∣ a.val := by
  by_contra h
  haveI := Fact.mk hp.1
  have h₁ : IsUnit (a : ZMod (p ^ k)) ↔ Nat.Coprime a.val (p ^ k) := by
    simp [← ZMod.isUnit_iff_coprime]
  have h₂ : ¬Nat.Coprime a.val (p ^ k) := by
    intro h₃
    have h₄ : IsUnit (a : ZMod (p ^ k)) := by
      rw [h₁] at *
      exact h₃
    exact ha h₄
  have h₃ : Nat.Coprime (p : ℕ) a.val := by
    have h₄ : Nat.Prime p := hp.1
    have h₅ : ¬p ∣ a.val := h
    have h₆ : Nat.Coprime p a.val := by
      rw [h₄.coprime_iff_not_dvd]
      exact h₅
    exact h₆
  have h₄ : Nat.Coprime (p ^ k) a.val := by
    have h₅ : Nat.Coprime (p : ℕ) a.val := h₃
    have h₆ : Nat.Coprime (p ^ k) a.val := by
      apply Nat.Coprime.pow_left
      exact h₅
    exact h₆
  have h₅ : Nat.Coprime a.val (p ^ k) := by
    rw [Nat.coprime_comm] at h₄
    exact h₄
  exact h₂ h₅

lemma val_div_p_lt {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (hk : 0 < k)
    (a : ZMod (p ^ k)) : a.val / p < p ^ (k - 1) := by
  have h₁ : a.val < p ^ k := by
    exact ZMod.val_lt a
  have h₂ : a.val / p < p ^ (k - 1) := by
    have h₃ : a.val < p ^ k := h₁
    have h₅ : a.val / p < p ^ (k - 1) := by
      have h₆ : a.val / p * p ≤ a.val := Nat.div_mul_le_self a.val p
      have h₇ : a.val < p ^ k := h₃
      have h₈ : a.val / p * p < p ^ k := by
        calc
          a.val / p * p ≤ a.val := h₆
          _ < p ^ k := h₇
      have h₉ : a.val / p < p ^ (k - 1) := by
        have h₁₀ : p ^ (k - 1) * p = p ^ k := by
          cases k with
          | zero => contradiction
          | succ k' =>
            simp [pow_succ, mul_comm]
        have h₁₁ : a.val / p < p ^ (k - 1) := by
          by_contra h
          have h₁₂ : a.val / p ≥ p ^ (k - 1) := by omega
          have h₁₃ : a.val / p * p ≥ p ^ (k - 1) * p := by
            exact Nat.mul_le_mul_right p h₁₂
          omega
        exact h₁₁
      exact h₉
    exact h₅
  exact h₂

lemma nonunitFwd_nonunitBwd {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (hk : 0 < k)
    (a : ZMod (p ^ k))
    (ha : a ∈ Finset.univ.filter (fun a : ZMod (p ^ k) => ¬ IsUnit a)) :
    nonunitFwd (nonunitBwd (p := p) a) = a := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  simp only [nonunitFwd, nonunitBwd]
  rw [ZMod.val_natCast_of_lt (val_div_p_lt hk a), ← Nat.cast_mul,
    Nat.mul_div_cancel' (p_dvd_val_of_not_isUnit a ha), ZMod.natCast_zmod_val]

lemma lhs_cast_eq {p : ℕ} [_hp : Fact (Nat.Prime p)] {k : ℕ} (_hk : 0 < k)
    (b : ZMod (p ^ (k - 1))) (t : ℤ) :
    (nonunitFwd (p := p) (k := k) b * (t : ZMod (p ^ k)) : ZMod (p ^ k)) =
    ((↑p * ↑b.val * t : ℤ) : ZMod (p ^ k)) := by
  change (p : ZMod (p ^ k)) * (b.val : ZMod (p ^ k)) * (t : ZMod (p ^ k)) = _
  push_cast
  ring

lemma rhs_cast_eq {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (_hk : 0 < k)
    (b : ZMod (p ^ (k - 1))) (t : ℤ) :
    (b * (t : ZMod (p ^ (k - 1))) : ZMod (p ^ (k - 1))) =
    ((↑b.val * t : ℤ) : ZMod (p ^ (k - 1))) := by
  haveI : NeZero (p ^ (k - 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  exact zmod_mul_as_cast (p ^ (k - 1)) b t

lemma exponent_eq {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (hk : 0 < k)
    (b : ZMod (p ^ (k - 1))) (t : ℤ) :
    2 * ↑Real.pi * Complex.I * (↑(↑p * ↑b.val * t : ℤ) : ℂ) / (↑(p ^ k) : ℂ) =
    2 * ↑Real.pi * Complex.I * (↑(↑b.val * t : ℤ) : ℂ) / (↑(p ^ (k - 1)) : ℂ) := by
  rw [show (p : ℕ) ^ k = p * p ^ (k - 1) from (p_mul_pow_pred hk).symm]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hp.out.ne_zero,
    show (↑(p ^ (k - 1) : ℕ) : ℂ) ≠ 0 by exact_mod_cast pow_ne_zero _ hp.out.ne_zero]

lemma stdAddChar_nonunitFwd_eq {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (hk : 0 < k)
    (b : ZMod (p ^ (k - 1))) (t : ℤ) :
    ZMod.stdAddChar (nonunitFwd (p := p) (k := k) b * (t : ZMod (p ^ k))) =
    ZMod.stdAddChar (b * (t : ZMod (p ^ (k - 1)))) := by
  rw [lhs_cast_eq hk b t, rhs_cast_eq hk b t,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  exact exponent_eq hk b t

lemma sum_nonunits_eq_sum_lower {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (hk : 0 < k)
    (t : ℤ) :
    (∑ a ∈ Finset.univ.filter (fun a : ZMod (p ^ k) => ¬ IsUnit a),
      ZMod.stdAddChar (a * (t : ZMod (p ^ k)))) =
    ∑ b : ZMod (p ^ (k - 1)), ZMod.stdAddChar (b * (t : ZMod (p ^ (k - 1)))) := by
  symm
  exact Finset.sum_nbij' (nonunitFwd (p := p) (k := k)) (nonunitBwd (p := p) (k := k))
    (fun b _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, nonunitFwd_not_isUnit hk b⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun b _ => nonunitBwd_nonunitFwd hk b)
    (fun a ha => nonunitFwd_nonunitBwd hk a ha)
    (fun b _ => (stdAddChar_nonunitFwd_eq hk b t).symm)

lemma ramanujanSum_prime_pow_decomp {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (hk : 0 < k)
    (t : ℤ) :
    @ramanujanSum (p ^ k) ⟨pow_ne_zero k hp.out.ne_zero⟩ t =
    (∑ a : ZMod (p ^ k), ZMod.stdAddChar (a * (t : ZMod (p ^ k)))) -
    (∑ b : ZMod (p ^ (k - 1)), ZMod.stdAddChar (b * (t : ZMod (p ^ (k - 1))))) := by
  rw [show (∑ a : ZMod (p ^ k), ZMod.stdAddChar (a * (t : ZMod (p ^ k)))) =
    ramanujanSum (p ^ k) t + _ from sum_eq_ramanujanSum_add_sum_nonunits (p ^ k) t,
    @sum_nonunits_eq_sum_lower p hp k hk t, add_sub_cancel_right]

theorem ramanujanSum_prime_pow_eq_zero {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (hk : 0 < k)
    {t : ℤ} (ht : ¬ ((p : ℤ) ^ (k - 1) ∣ t)) :
    @ramanujanSum (p ^ k) ⟨pow_ne_zero k hp.out.ne_zero⟩ t = 0 := by
  rw [ramanujanSum_prime_pow_decomp hk t,
    sum_stdAddChar_mul_eq, sum_stdAddChar_mul_eq]
  simp only [Nat.cast_pow] at ht ⊢
  have hk_not : ¬ ((p : ℤ) ^ k ∣ t) :=
    fun h => ht (dvd_trans (pow_dvd_pow _ (Nat.sub_le k 1)) h)
  simp [hk_not, ht]

lemma ramanujanSum_unit_shift (n : ℕ) [NeZero n] (u : (ZMod n)ˣ) (s : ZMod n) :
    ∑ a : (ZMod n)ˣ, ZMod.stdAddChar (a.val * (u.val * s)) =
    ∑ a : (ZMod n)ˣ, ZMod.stdAddChar (a.val * s) :=
  Fintype.sum_equiv (Equiv.mulRight u)
    (fun a => ZMod.stdAddChar (a.val * (u.val * s)))
    (fun a => ZMod.stdAddChar (a.val * s))
    (fun a => by simp only [Equiv.coe_mulRight, Units.val_mul, mul_assoc])

lemma dvd_sub_mul_crt_val {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]
    (h : Nat.Coprime n₁ n₂) (j : ℤ) :
    (n₁ : ℤ) ∣ j - ↑n₂ * ↑((j : ZMod n₁) * (↑n₂ : ZMod n₁)⁻¹).val := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero, ZMod.natCast_zmod_val, mul_comm (↑n₂ : ZMod n₁), mul_assoc,
    ZMod.inv_mul_of_unit _ (by rwa [ZMod.isUnit_iff_coprime, Nat.coprime_comm]), mul_one]

lemma crt_exponent_eq {n₁ n₂ : ℕ} [hn₁ : NeZero n₁] [hn₂ : NeZero n₂]
    (h : Nat.Coprime n₁ n₂) (j : ℤ) :
    ∃ m : ℤ, 2 * ↑Real.pi * Complex.I * ↑j / ↑(n₁ * n₂) =
      (2 * ↑Real.pi * Complex.I * ↑((j : ZMod n₁) * (↑n₂ : ZMod n₁)⁻¹).val / ↑n₁ +
       2 * ↑Real.pi * Complex.I * ↑((j : ZMod n₂) * (↑n₁ : ZMod n₂)⁻¹).val / ↑n₂) +
      ↑m * (2 * ↑Real.pi * Complex.I) := by
  set v₁ := ((j : ZMod n₁) * (↑n₂ : ZMod n₁)⁻¹).val
  set v₂ := ((j : ZMod n₂) * (↑n₁ : ZMod n₂)⁻¹).val
  have h1 : (n₁ : ℤ) ∣ j - ↑n₂ * ↑v₁ := dvd_sub_mul_crt_val h j
  have h2 : (n₂ : ℤ) ∣ j - ↑n₁ * ↑v₂ := dvd_sub_mul_crt_val h.symm j
  obtain ⟨m, hm⟩ := h.isCoprime.mul_dvd
    (dvd_sub h1 (dvd_mul_right _ _))
    (show (n₂ : ℤ) ∣ j - ↑n₂ * ↑v₁ - ↑n₁ * ↑v₂ by
      rw [show j - ↑n₂ * ↑v₁ - ↑n₁ * ↑v₂ = j - ↑n₁ * ↑v₂ - ↑n₂ * ↑v₁ by ring]
      exact dvd_sub h2 (dvd_mul_right _ _))
  have hint : j = ↑n₂ * ↑v₁ + ↑n₁ * ↑v₂ + m * (↑n₁ * ↑n₂) := by linarith
  exact ⟨m, by
    rw [Nat.cast_mul, show (↑j : ℂ) = ↑n₂ * ↑v₁ + ↑n₁ * ↑v₂ + ↑m * (↑n₁ * ↑n₂) by
      exact_mod_cast hint]
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne n₁),
      Nat.cast_ne_zero.mpr (NeZero.ne n₂)]⟩

lemma stdAddChar_crt_split {n₁ n₂ : ℕ} [hn₁ : NeZero n₁] [hn₂ : NeZero n₂]
    (h : Nat.Coprime n₁ n₂) (x : ZMod (n₁ * n₂)) :
    @ZMod.stdAddChar (n₁ * n₂) ⟨Nat.mul_ne_zero hn₁.ne hn₂.ne⟩ x =
    ZMod.stdAddChar ((ZMod.chineseRemainder h x).1 * (n₂ : ZMod n₁)⁻¹) *
    ZMod.stdAddChar ((ZMod.chineseRemainder h x).2 * (n₁ : ZMod n₂)⁻¹) := by
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective (n := n₁ * n₂) x
  rw [show (ZMod.chineseRemainder h (j : ZMod (n₁ * n₂))).1 = (j : ZMod n₁) by simp,
    show (ZMod.chineseRemainder h (j : ZMod (n₁ * n₂))).2 = (j : ZMod n₂) by simp,
    @ZMod.stdAddChar_coe (n₁ * n₂) ⟨Nat.mul_ne_zero hn₁.ne hn₂.ne⟩]
  simp only [ZMod.stdAddChar_apply, ← Circle.coe_mul]
  rw [Circle.coe_mul, ZMod.toCircle_apply, ZMod.toCircle_apply,
    ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  exact crt_exponent_eq h j

lemma crt_proj_fst {n₁ n₂ : ℕ} [_hn₁ : NeZero n₁] [_hn₂ : NeZero n₂]
    (h : Nat.Coprime n₁ n₂) (a₁ : (ZMod n₁)ˣ) (a₂ : (ZMod n₂)ˣ) (t : ℤ) :
    let e := (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).toEquiv.trans
      MulEquiv.prodUnits.toEquiv
    (ZMod.chineseRemainder h ((e.symm (a₁, a₂)).val * (t : ZMod (n₁ * n₂)))).1 =
      a₁.val * (t : ZMod n₁) := by
  intro e
  have h_e_val : ZMod.chineseRemainder h ((e.symm (a₁, a₂)).val) = (a₁.val, a₂.val) :=
    by simp [e, Equiv.trans, Units.mapEquiv, MulEquiv.prodUnits]
  have h_main : (ZMod.chineseRemainder h ((e.symm (a₁,
    a₂)).val * (t : ZMod (n₁ * n₂)))).1 = a₁.val * (t : ZMod n₁) := by simp_all
  assumption

lemma crt_proj_snd {n₁ n₂ : ℕ} [_hn₁ : NeZero n₁] [_hn₂ : NeZero n₂]
    (h : Nat.Coprime n₁ n₂) (a₁ : (ZMod n₁)ˣ) (a₂ : (ZMod n₂)ˣ) (t : ℤ) :
    let e := (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).toEquiv.trans
      MulEquiv.prodUnits.toEquiv
    (ZMod.chineseRemainder h ((e.symm (a₁, a₂)).val * (t : ZMod (n₁ * n₂)))).2 =
      a₂.val * (t : ZMod n₂) := by
  intro e
  have h₂ : (ZMod.chineseRemainder h ((e.symm (a₁, a₂)).val)) = (a₁.val, a₂.val) :=
    by simp [e, Equiv.trans, Units.mapEquiv, MulEquiv.prodUnits]
  have h₃ : (ZMod.chineseRemainder h ((e.symm (a₁, a₂)).val * (t : ZMod (n₁ * n₂)))).2 =
      a₂.val * (t : ZMod n₂) := by simp_all
  assumption

lemma ramanujanSum_crt_decomp {n₁ n₂ : ℕ} [hn₁ : NeZero n₁] [hn₂ : NeZero n₂]
    (h : Nat.Coprime n₁ n₂) (t : ℤ) :
    ∑ a : (ZMod (n₁ * n₂))ˣ,
      @ZMod.stdAddChar (n₁ * n₂) ⟨Nat.mul_ne_zero hn₁.ne hn₂.ne⟩
        (a.val * (t : ZMod (n₁ * n₂))) =
    ∑ ab : (ZMod n₁)ˣ × (ZMod n₂)ˣ,
      ZMod.stdAddChar (ab.1.val * ((n₂ : ZMod n₁)⁻¹ * (t : ZMod n₁))) *
      ZMod.stdAddChar (ab.2.val * ((n₁ : ZMod n₂)⁻¹ * (t : ZMod n₂))) := by
  let e : (ZMod (n₁ * n₂))ˣ ≃ (ZMod n₁)ˣ × (ZMod n₂)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).toEquiv.trans
    MulEquiv.prodUnits.toEquiv
  rw [show (∑ a : (ZMod (n₁ * n₂))ˣ,
      @ZMod.stdAddChar (n₁ * n₂) ⟨Nat.mul_ne_zero hn₁.ne hn₂.ne⟩
        (a.val * (t : ZMod (n₁ * n₂)))) =
      ∑ ab : (ZMod n₁)ˣ × (ZMod n₂)ˣ,
      @ZMod.stdAddChar (n₁ * n₂) ⟨Nat.mul_ne_zero hn₁.ne hn₂.ne⟩
        ((e.symm ab).val * (t : ZMod (n₁ * n₂)))
    from Fintype.sum_equiv e _ _ (fun a => by simp [e])]
  congr 1
  ext ⟨a₁, a₂⟩
  rw [stdAddChar_crt_split h, crt_proj_fst h a₁ a₂ t, crt_proj_snd h a₁ a₂ t]
  congr 1 <;> congr 1 <;> ring

lemma ramanujanSum_absorb_inv {n m : ℕ} [NeZero n] (hc : Nat.Coprime m n) (s : ZMod n) :
    ∑ a : (ZMod n)ˣ, ZMod.stdAddChar (a.val * ((m : ZMod n)⁻¹ * s)) =
    ∑ a : (ZMod n)ˣ, ZMod.stdAddChar (a.val * s) := by
  let u := ZMod.unitOfCoprime m hc
  rw [show (m : ZMod n)⁻¹ = (u⁻¹ : (ZMod n)ˣ).val by
    rw [← ZMod.coe_unitOfCoprime m hc, ZMod.inv_coe_unit u]]
  exact ramanujanSum_unit_shift n u⁻¹ s

lemma sum_prod_factor {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]
    (s₁ : ZMod n₁) (s₂ : ZMod n₂) :
    ∑ ab : (ZMod n₁)ˣ × (ZMod n₂)ˣ,
      ZMod.stdAddChar (ab.1.val * s₁) * ZMod.stdAddChar (ab.2.val * s₂) =
    (∑ a : (ZMod n₁)ˣ, ZMod.stdAddChar (a.val * s₁)) *
    (∑ a : (ZMod n₂)ˣ, ZMod.stdAddChar (a.val * s₂)) := by
  simp_rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

theorem ramanujanSum_multiplicative {n₁ n₂ : ℕ} [hn₁ : NeZero n₁] [hn₂ : NeZero n₂]
    (h : Nat.Coprime n₁ n₂) (t : ℤ) :
    @ramanujanSum (n₁ * n₂) ⟨Nat.mul_ne_zero hn₁.ne hn₂.ne⟩ t =
    ramanujanSum n₁ t * ramanujanSum n₂ t := by
  unfold ramanujanSum
  rw [ramanujanSum_crt_decomp h t, sum_prod_factor,
    ramanujanSum_absorb_inv h.symm (t : ZMod n₁),
    ramanujanSum_absorb_inv h (t : ZMod n₂)]

lemma largestPrimeFactor_mem_primeFactors (n : ℕ) (hn : 2 ≤ n) :
    largestPrimeFactor n ∈ n.primeFactors := by
  obtain ⟨a, ha_max, _⟩ := largestPrimeFactor_pos_helper_fb n hn
  have hmem : a ∈ n.primeFactors := Finset.mem_of_max ha_max
  have : largestPrimeFactor n = a := by
    unfold largestPrimeFactor
    rw [ha_max]
    rfl
  rw [this]
  exact hmem

theorem largest_prime_factor_multiplicity_pos (n : ℕ) (hn : 2 ≤ n) :
    n.factorization (largestPrimeFactor n) ≥ 1 := by
  have hmem := largestPrimeFactor_mem_primeFactors n hn
  rw [← Nat.support_factorization] at hmem
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hmem)

lemma largest_prime_factor_prime (n : ℕ) (hn : 2 ≤ n) :
    Nat.Prime (largestPrimeFactor n) := by
  exact Nat.prime_of_mem_primeFactors (largestPrimeFactor_mem_primeFactors n hn)

lemma decompose_largest_prime (n : ℕ) (hn : 2 ≤ n) :
    let P := largestPrimeFactor n
    let α := n.factorization P
    let m := n / (P ^ α)
    P ^ α * m = n ∧ Nat.Coprime (P ^ α) m ∧ 0 < m := by
  intro P α m
  have hn_ne_zero : n ≠ 0 := by omega
  have P_mem := largestPrimeFactor_mem_primeFactors n hn
  have P_prime := Nat.prime_of_mem_primeFactors P_mem
  have α_pos := Nat.Prime.factorization_pos_of_dvd P_prime hn_ne_zero
    (Nat.dvd_of_mem_primeFactors P_mem)
  have mul_eq := Nat.ordProj_mul_ordCompl_eq_self n P
  have p_coprime_m := Nat.coprime_ordCompl P_prime hn_ne_zero
  have coprime := (Nat.coprime_pow_left_iff α_pos _ _).mpr p_coprime_m
  have dvd := Nat.ordProj_dvd n P
  have hPα_pos : 0 < P ^ α := Nat.pos_of_ne_zero (pow_ne_zero _ P_prime.ne_zero)
  have m_pos := Nat.div_pos (Nat.le_of_dvd (by omega) dvd) hPα_pos
  exact ⟨mul_eq, coprime, m_pos⟩

lemma ramanujan_vanish_low_valuation
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (t : ℤ)
    (ht : ¬((largestPrimeFactor n ^ (n.factorization (largestPrimeFactor n) - 1) : ℤ) ∣ t)) :
    ramanujanSum n t = 0 := by
  set P := largestPrimeFactor n
  set α := n.factorization P
  have hα_pos : 0 < α := largest_prime_factor_multiplicity_pos n hn
  have hP_prime : Nat.Prime P := largest_prime_factor_prime n hn
  have ⟨hdecomp, hcoprime, hm_pos⟩ := decompose_largest_prime n hn
  set m := n / (P ^ α)
  haveI hPα_ne : NeZero (P ^ α) := ⟨pow_ne_zero α (Nat.Prime.ne_zero hP_prime)⟩
  haveI hm_ne : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm_pos⟩
  have decomp_eq : n = P ^ α * m := hdecomp.symm
  conv_lhs =>
    arg 1
    rw [decomp_eq]
  rw [ramanujanSum_multiplicative hcoprime t]
  haveI : Fact (Nat.Prime P) := ⟨hP_prime⟩
  have vanish_comp : ramanujanSum (P ^ α) t = 0 :=
    ramanujanSum_prime_pow_eq_zero hα_pos ht
  rw [vanish_comp]
  ring

lemma summand_eq_EP0_plus_EPalpha
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (p q : ℤ) (_hp : 1 ≤ p) (_hq : 1 ≤ q)
    (_hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2)
    (k l : ZMod n) :
    (if ¬(k = 0 ∧ l = 0)
     then normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
          normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
          ramanujanSum n (ZMod.val k * p + ZMod.val l * q)
     else 0 : ℂ) =
    (let P := largestPrimeFactor n
     let alpha := n.factorization P
     let P0 := P ^ (alpha - 1)
     let d := P ^ alpha
     let fp := intervalIndicator n (2 * p - 1).toNat
     let fq := intervalIndicator n (2 * q - 1).toNat
     (if (k, l) ≠ (0, 0) ∧
         (P0 : ℤ) ∣ (ZMod.val k * p + ZMod.val l * q) ∧
         ¬((d : ℤ) ∣ (ZMod.val k * p + ZMod.val l * q))
      then normalizedDFT n fp k * normalizedDFT n fq l *
           ramanujanSum n (ZMod.val k * p + ZMod.val l * q)
      else 0) +
     (if (k, l) ≠ (0, 0) ∧
         (d : ℤ) ∣ (ZMod.val k * p + ZMod.val l * q)
      then normalizedDFT n fp k * normalizedDFT n fq l *
           ramanujanSum n (ZMod.val k * p + ZMod.val l * q)
      else 0)) := by
  simp only []
  set t := (↑(ZMod.val k) * p + ↑(ZMod.val l) * q : ℤ)
  set P := largestPrimeFactor n
  set α := n.factorization P
  set V := normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
           normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
           ramanujanSum n t
  have hiff : ¬(k = 0 ∧ l = 0) ↔ (k, l) ≠ (0, 0) := by
    constructor
    · intro h hprod; exact h ⟨(Prod.mk.inj hprod).1, (Prod.mk.inj hprod).2⟩
    · intro h ⟨hk, hl⟩; exact h (Prod.mk.injEq k l 0 0 |>.mpr ⟨hk, hl⟩)
  by_cases hkl : (k, l) = (0, 0)
  · have hkl' : ¬¬(k = 0 ∧ l = 0) := not_not.mpr ⟨(Prod.mk.inj hkl).1, (Prod.mk.inj hkl).2⟩
    rw [if_neg hkl',
        if_neg (show ¬((k, l) ≠ (0, 0) ∧ _) from fun ⟨h, _⟩ => h hkl),
        if_neg (show ¬((k, l) ≠ (0, 0) ∧ _) from fun ⟨h, _⟩ => h hkl)]
    ring
  · have hkl' : ¬(k = 0 ∧ l = 0) := hiff.mpr hkl
    rw [if_pos hkl']
    by_cases hP0 : (↑(P ^ (α - 1)) : ℤ) ∣ t
    · by_cases hd : (↑(P ^ α) : ℤ) ∣ t
      · rw [if_neg (show ¬((_ ≠ _) ∧ _ ∧ ¬_) from by push Not; exact fun _ _ => hd),
            if_pos ⟨hkl, hd⟩]
        ring
      · rw [if_pos ⟨hkl, hP0, hd⟩,
            if_neg (show ¬((_ ≠ _) ∧ _) from by push Not; exact fun _ => hd)]
        ring
    · have hnotd : ¬((↑(P ^ α) : ℤ) ∣ t) := fun hd =>
        hP0 (dvd_trans (by exact_mod_cast pow_dvd_pow P (Nat.sub_le α 1)) hd)
      have hvanish : ramanujanSum n t = 0 := ramanujan_vanish_low_valuation n hn t hP0
      rw [if_neg (show ¬((_ ≠ _) ∧ _ ∧ _) from by push Not; exact fun _ h => absurd h hP0),
          if_neg (show ¬((_ ≠ _) ∧ _) from by push Not; exact fun _ => hnotd)]
      simp [V, hvanish]

lemma nonzero_sum_eq_EP0_plus_EPalpha
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    (∑ k : ZMod n, ∑ l : ZMod n,
      if ¬(k = 0 ∧ l = 0)
      then normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
           normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
           ramanujanSum n (ZMod.val k * p + ZMod.val l * q)
      else 0 : ℂ) =
    errorTermEP0 n p q + errorTermEPalpha n p q := by
  simp only [errorTermEP0, errorTermEPalpha]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext k
  rw [← Finset.sum_add_distrib]
  congr 1
  ext l
  exact summand_eq_EP0_plus_EPalpha n hn p q hp hq hpq k l

lemma fourier_sum_split_into_main_and_errors
    (n : ℕ) (hn : 2 ≤ n)
    (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    haveI : NeZero n := ⟨by omega⟩
    (∑ k : ZMod n, ∑ l : ZMod n,
      normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
      normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
      ramanujanSum n (ZMod.val k * p + ZMod.val l * q) : ℂ) -
    ((2 * p - 1).toNat : ℂ) * ((2 * q - 1).toNat : ℂ) *
      (Nat.totient n : ℂ) / (n : ℂ) ^ 2 =
    errorTermEP0 n p q + errorTermEPalpha n p q := by
  haveI : NeZero n := ⟨by omega⟩
  rw [full_sum_split_zero_nonzero n
    (fun k l => normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
                normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
                ramanujanSum n (ZMod.val k * p + ZMod.val l * q))]
  rw [zero_zero_term_eq_main n hn p q hp hq hpq]
  rw [nonzero_sum_eq_EP0_plus_EPalpha n hn p q hp hq hpq]
  ring

lemma re_complex_lhs_eq_real_lhs
    (n : ℕ) (_hn : 2 ≤ n)
    (p q : ℤ) (_hp : 1 ≤ p) (_hq : 1 ≤ q)
    (_hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    ((countingFunctionS n p q : ℂ) -
      ((2 * p - 1).toNat : ℂ) * ((2 * q - 1).toNat : ℂ) *
        (Nat.totient n : ℂ) / (n : ℂ) ^ 2).re =
    (countingFunctionS n p q : ℝ) -
      ((2 * p - 1).toNat : ℝ) * ((2 * q - 1).toNat : ℝ) *
      (Nat.totient n : ℝ) / (n : ℝ) ^ 2 := by
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]

lemma error_decomposition_from_complex
    (n : ℕ) (hn : 2 ≤ n)
    (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2)
    (h_complex :
      haveI : NeZero n := ⟨by omega⟩
      (countingFunctionS n p q : ℂ) -
      ((2 * p - 1).toNat : ℂ) * ((2 * q - 1).toNat : ℂ) *
        (Nat.totient n : ℂ) / (n : ℂ) ^ 2 =
      errorTermEP0 n p q + errorTermEPalpha n p q) :
    haveI : NeZero n := ⟨by omega⟩
    (countingFunctionS n p q : ℝ) -
      ((2 * p - 1).toNat : ℝ) * ((2 * q - 1).toNat : ℝ) *
      (Nat.totient n : ℝ) / (n : ℝ) ^ 2 =
    (errorTermEP0 n p q).re + (errorTermEPalpha n p q).re := by
  have hre := congr_arg Complex.re h_complex
  rw [Complex.add_re] at hre
  rw [← hre]
  exact (re_complex_lhs_eq_real_lhs n hn p q hp hq hpq).symm

lemma error_decomposition
    (n : ℕ) (hn : 2 ≤ n)
    (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    haveI : NeZero n := ⟨by omega⟩
    (countingFunctionS n p q : ℝ) -
      ((2 * p - 1).toNat : ℝ) * ((2 * q - 1).toNat : ℝ) *
      (Nat.totient n : ℝ) / (n : ℝ) ^ 2 =
    (errorTermEP0 n p q).re + (errorTermEPalpha n p q).re := by
  haveI : NeZero n := ⟨by omega⟩
  have h_repr := counting_eq_fourier_ramanujan_sum n hn p q hp hq hpq
  have h_split := fourier_sum_split_into_main_and_errors n hn p q hp hq hpq
  have h_complex : (countingFunctionS n p q : ℂ) -
      ((2 * p - 1).toNat : ℂ) * ((2 * q - 1).toNat : ℂ) *
        (Nat.totient n : ℂ) / (n : ℂ) ^ 2 =
      errorTermEP0 n p q + errorTermEPalpha n p q := by
    rw [h_repr]; exact h_split
  exact error_decomposition_from_complex n hn p q hp hq hpq h_complex

lemma double_sum_norms_eq_product
    (n : ℕ) [NeZero n] (f g : ZMod n → ℂ) :
    ∑ k : ZMod n, ∑ l : ZMod n, ‖f k‖ * ‖g l‖ =
    (∑ k : ZMod n, ‖f k‖) * (∑ l : ZMod n, ‖g l‖) :=
  (Fintype.sum_mul_sum (fun k => ‖f k‖) (fun l => ‖g l‖)).symm

lemma ramanujanSum_norm_le_totient (n : ℕ) [NeZero n] (t : ℤ) :
    ‖ramanujanSum n t‖ ≤ (Nat.totient n : ℝ) := by
  have h1 : ‖ramanujanSum n t‖ ≤ Fintype.card (ZMod n)ˣ := by
    calc
      ‖ramanujanSum n t‖ = ‖∑ a : (ZMod n)ˣ, ZMod.stdAddChar (a.val * (t : ZMod n))‖ := rfl
      _ ≤ ∑ a : (ZMod n)ˣ, ‖ZMod.stdAddChar (a.val * (t : ZMod n))‖ := norm_sum_le _ _
      _ = ∑ _ : (ZMod n)ˣ, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a _
        have h : ‖ZMod.stdAddChar (a.val * (t : ZMod n))‖ = 1 := by
          simp
        simp [h]
      _ = (Fintype.card (ZMod n)ˣ : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have h2 : (Fintype.card (ZMod n)ˣ : ℝ) = (Nat.totient n : ℝ) := by
    norm_cast
    simp [ZMod.card_units_eq_totient]
  calc
    ‖ramanujanSum n t‖ ≤ Fintype.card (ZMod n)ˣ := h1
    _ = (Nat.totient n : ℝ) := by rw [h2]

lemma ramanujanSum_prime_pow_eq_neg {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (hk : 0 < k)
    {t : ℤ} (ht1 : (p : ℤ) ^ (k - 1) ∣ t) (ht2 : ¬ ((p : ℤ) ^ k ∣ t)) :
    @ramanujanSum (p ^ k) ⟨pow_ne_zero k hp.out.ne_zero⟩ t =
    -(p : ℂ) ^ (k - 1) := by
  rw [ramanujanSum_prime_pow_decomp hk t, sum_stdAddChar_mul_eq, sum_stdAddChar_mul_eq]
  simp only [Nat.cast_pow] at ht1 ht2 ⊢
  simp [ht1, ht2]

lemma norm_ramanujanSum_prime_pow_eq_neg {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} (hk : 0 < k)
    {t : ℤ} (ht1 : (p : ℤ) ^ (k - 1) ∣ t) (ht2 : ¬ ((p : ℤ) ^ k ∣ t)) :
    ‖@ramanujanSum (p ^ k) ⟨pow_ne_zero k hp.out.ne_zero⟩ t‖ = (p : ℝ) ^ (k - 1) := by
  rw [ramanujanSum_prime_pow_eq_neg hk ht1 ht2, norm_neg, Complex.norm_pow, Complex.norm_natCast]

lemma totient_div_prime_minus_one
    (n P α m : ℕ)
    (hP : Nat.Prime P) (hα : 0 < α) (hcop : Nat.Coprime (P ^ α) m)
    (hn : P ^ α * m = n) :
    (P : ℝ) ^ (α - 1) * (Nat.totient m : ℝ) = (Nat.totient n : ℝ) / ((P : ℝ) - 1) := by
  have hP_ge_two : P ≥ 2 := by exact hP.two_le
  have hP_pos : (0 : ℕ) < P := by nlinarith
  have hP_sub_one_pos : (P : ℝ) - 1 > 0 :=
    by linarith [show (1 : ℝ) < (P : ℝ) from by exact_mod_cast hP.one_lt]
  have htotient_mul : Nat.totient (P ^ α * m) = Nat.totient (P ^ α) * Nat.totient m :=
    by exact Nat.totient_mul hcop
  have htotient_prime_pow : Nat.totient (P ^ α) = P ^ (α - 1) * (P - 1) :=
    by exact Nat.totient_prime_pow hP (by omega : 0 < α)
  have htotient_n : (Nat.totient n : ℝ) = (P : ℝ) ^ (α - 1) * ((P : ℝ) - 1) * (Nat.totient m : ℝ) :=
    by simp_all
  have hmain : (P : ℝ) ^ (α - 1) * (Nat.totient m : ℝ) = (Nat.totient n : ℝ) / ((P : ℝ) - 1) :=
    by field_simp; rw [htotient_n]; ring
  assumption

lemma ramanujanSum_EP0_norm_bound
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (t : ℤ)
    (hP0 : (↑(largestPrimeFactor n ^ (n.factorization (largestPrimeFactor n) - 1)) : ℤ) ∣ t)
    (hd : ¬ ((↑(largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) : ℤ) ∣ t)) :
    ‖ramanujanSum n t‖ ≤
      (Nat.totient n : ℝ) / ((largestPrimeFactor n : ℝ) - 1) := by
  set P := largestPrimeFactor n
  set α := n.factorization P
  set m := n / (P ^ α)
  have hPprime : Nat.Prime P := largest_prime_factor_prime n hn
  have hαge : α ≥ 1 := largest_prime_factor_multiplicity_pos n hn
  have hαpos : 0 < α := by linarith
  obtain ⟨hdecomp, hcop, hm_pos⟩ := decompose_largest_prime n hn
  haveI hne_Pα : NeZero (P ^ α) := ⟨pow_ne_zero α (Nat.Prime.ne_zero hPprime)⟩
  haveI hne_m : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm_pos⟩
  haveI : Fact (Nat.Prime P) := ⟨hPprime⟩
  have ht1 : (P : ℤ) ^ (α - 1) ∣ t := by exact_mod_cast hP0
  have ht2 : ¬ ((P : ℤ) ^ α ∣ t) := by exact_mod_cast hd
  have h_norm_Palpha : ‖@ramanujanSum (P ^ α) hne_Pα t‖ = (P : ℝ) ^ (α - 1) :=
    norm_ramanujanSum_prime_pow_eq_neg hαpos ht1 ht2
  have h_norm_m : ‖@ramanujanSum m hne_m t‖ ≤ (Nat.totient m : ℝ) :=
    ramanujanSum_norm_le_totient m t
  have hPαm_ne : P ^ α * m ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.pos_of_ne_zero hne_Pα.ne) hm_pos)
  have h_mult : @ramanujanSum (P ^ α * m) ⟨hPαm_ne⟩ t =
      @ramanujanSum (P ^ α) hne_Pα t * @ramanujanSum m hne_m t :=
    ramanujanSum_multiplicative hcop t
  have hn_rw : ‖@ramanujanSum n _ t‖ = ‖@ramanujanSum (P ^ α * m) ⟨hPαm_ne⟩ t‖ := by
    congr 2
    exact hdecomp.symm
  calc ‖@ramanujanSum n _ t‖
      = ‖@ramanujanSum (P ^ α * m) ⟨hPαm_ne⟩ t‖ := hn_rw
    _ = ‖@ramanujanSum (P ^ α) hne_Pα t * @ramanujanSum m hne_m t‖ := by
        rw [h_mult]
    _ = ‖@ramanujanSum (P ^ α) hne_Pα t‖ * ‖@ramanujanSum m hne_m t‖ := norm_mul _ _
    _ = (P : ℝ) ^ (α - 1) * ‖@ramanujanSum m hne_m t‖ := by rw [h_norm_Palpha]
    _ ≤ (P : ℝ) ^ (α - 1) * (Nat.totient m : ℝ) := by
        apply mul_le_mul_of_nonneg_left h_norm_m
        exact pow_nonneg (Nat.cast_nonneg _) _
    _ = (Nat.totient n : ℝ) / ((P : ℝ) - 1) :=
        totient_div_prime_minus_one n P α m hPprime hαpos hcop hdecomp

lemma sum_split_zero (n : ℕ) [NeZero n] (f : ZMod n → ℝ) :
    ∑ k : ZMod n, f k = f 0 + ∑ k ∈ (Finset.univ : Finset (ZMod n)).filter (· ≠ 0), f k := by
  conv_lhs => rw [show (∑ k : ZMod n, f k : ℝ) = ∑ k ∈ Finset.univ, f k from by simp]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = (0 : ZMod n))]
  simp [show Finset.univ.filter (· = (0 : ZMod n)) = {0} from by ext x; simp]

lemma indicator_formula (n : ℕ) [NeZero n] (m : ℕ) (j : ZMod n) (k : ZMod n) :
    ZMod.stdAddChar (-(j * k)) • intervalIndicator n m j =
    if j ∈ intervalSet n m then ZMod.stdAddChar (-(j * k)) else 0 := by
  simp [intervalIndicator, Set.indicator_apply]

lemma summand_reindex (n : ℕ) [NeZero n] (m : ℕ) (hm2 : m < n) (k : ZMod n) :
    ∑ j : ZMod n, (if j ∈ intervalSet n m then ZMod.stdAddChar (-(j * k)) else 0) =
    ∑ t ∈ Finset.range m, ZMod.stdAddChar (-((t + 1 : ZMod n) * k)) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun j => ZMod.val j - 1) (fun t => ((t + 1 : ℕ) : ZMod n))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, intervalSet, Set.mem_setOf_eq] at hj
    exact Finset.mem_range.mpr (by omega)
  · intro t ht
    have htm : t < m := Finset.mem_range.mp ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, intervalSet, Set.mem_setOf_eq]
    rw [ZMod.val_natCast_of_lt (by omega : t + 1 < n)]
    exact ⟨by omega, by omega⟩
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, intervalSet, Set.mem_setOf_eq] at hj
    rw [show ZMod.val j - 1 + 1 = ZMod.val j from by omega]
    exact ZMod.natCast_zmod_val j
  · intro t ht
    have htm : t < m := Finset.mem_range.mp ht
    rw [ZMod.val_natCast_of_lt (by omega : t + 1 < n)]
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, intervalSet, Set.mem_setOf_eq] at hj
    have hv : ZMod.val j - 1 + 1 = ZMod.val j := by omega
    have : (↑(ZMod.val j - 1 + 1 : ℕ) : ZMod n) = j := by
      rw [hv]; exact ZMod.natCast_zmod_val j
    simp only [Nat.cast_add, Nat.cast_one] at this
    rw [show (↑(ZMod.val j - 1) + 1 : ZMod n) = j from this]

lemma character_multiplication_simplify (n : ℕ) [NeZero n] (t : ℕ) (k : ZMod n) :
    ZMod.stdAddChar (-((t + 1 : ZMod n) * k)) =
    (ZMod.stdAddChar (-k)) ^ (t + 1) := by
  have h1 : (-((t + 1 : ZMod n) * k) : ZMod n) = (t + 1 : ℕ) • (-k : ZMod n) := by
    simp only [smul_neg, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [h1]
  have h2 : ZMod.stdAddChar ((t + 1 : ℕ) • (-k : ZMod n)) = (ZMod.stdAddChar (-k)) ^ (t + 1) := by
    rw [ZMod.stdAddChar.map_nsmul_eq_pow]
  rw [h2]

lemma dft_intervalIndicator_eq_geom_sum (n : ℕ) [NeZero n] (m : ℕ)
    (hm2 : m < n) (k : ZMod n) :
    ZMod.dft (intervalIndicator n m) k =
      ∑ t ∈ Finset.range m, (ZMod.stdAddChar (-k)) ^ (t + 1) := by
  rw [ZMod.dft_apply]
  simp only [indicator_formula]
  rw [summand_reindex n m hm2 k]
  exact Finset.sum_congr rfl fun t _ => character_multiplication_simplify n t k

lemma exponent_algebra (n : ℕ) [NeZero n] (k : ZMod n) :
    (2 : ℂ) * ↑Real.pi * Complex.I * ↑(-(↑(ZMod.val k) : ℤ)) / ↑(n : ℕ) =
      Complex.I * ↑(-2 * Real.pi * (ZMod.val k : ℝ) / (n : ℝ)) := by
  push_cast
  ring

lemma stdAddChar_neg_eq_exp (n : ℕ) [NeZero n] (k : ZMod n) :
    (ZMod.stdAddChar (-k) : ℂ) =
      Complex.exp (Complex.I * ↑(-2 * Real.pi * (ZMod.val k : ℝ) / (n : ℝ))) := by
  rw [show -k = (↑(-(↑(ZMod.val k) : ℤ)) : ZMod n) from by simp, ZMod.stdAddChar_coe]
  congr 1
  exact exponent_algebra n k

lemma norm_one_sub_stdAddChar_eq (n : ℕ) [NeZero n] (k : ZMod n) :
    ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖ = 2 * |Real.sin (Real.pi * (ZMod.val k : ℝ) / n)| := by
  rw [stdAddChar_neg_eq_exp, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one,
    show (-2 * Real.pi * (ZMod.val k : ℝ) / (n : ℝ)) / 2 =
      -(Real.pi * (ZMod.val k : ℝ) / (n : ℝ)) from by ring,
    Real.sin_neg, mul_neg, Real.norm_eq_abs, abs_neg, abs_mul,
    abs_of_pos (by positivity : (2 : ℝ) > 0)]

lemma abs_bound_helper (n : ℕ) (v : ℝ) (hn : 0 < (n : ℝ)) (hvn : v ≤ n / 2) :
    Real.pi * v / n ≤ Real.pi / 2 := by
  have h₁ : (Real.pi : ℝ) * v / n ≤ Real.pi / 2 := by
    have h₃ : 0 < (n : ℝ) := hn
    have h₅ : (Real.pi : ℝ) * v / n ≤ (Real.pi : ℝ) * ((n : ℝ) / 2) / n := by
      calc
        (Real.pi : ℝ) * v / n = (Real.pi : ℝ) / n * v := by ring
        _ ≤ (Real.pi : ℝ) / n * ((n : ℝ) / 2) := by
          gcongr
        _ = (Real.pi : ℝ) * ((n : ℝ) / 2) / n := by
          ring
    have h₆ : (Real.pi : ℝ) * ((n : ℝ) / 2) / n = Real.pi / 2 := by
      field_simp [h₃.ne']
    linarith
  exact h₁

lemma two_v_div_n_le_abs_sin (n : ℕ) (v : ℝ) (hn : 0 < (n : ℝ)) (hv : 0 < v)
    (hvn : v ≤ n / 2) :
    2 * v / n ≤ |Real.sin (Real.pi * v / n)| := by
  have h1 : 0 ≤ Real.pi * v / n := by positivity
  have h2 : |Real.pi * v / n| ≤ Real.pi / 2 := by
    rw [abs_of_nonneg h1]
    exact abs_bound_helper n v hn hvn
  calc 2 * v / n = 2 / Real.pi * |Real.pi * v / n| := by
        rw [abs_of_nonneg h1]; field_simp [Real.pi_pos.ne', hn.ne']
    _ ≤ |Real.sin (Real.pi * v / n)| := Real.mul_abs_le_abs_sin h2

lemma abs_sin_val_eq_abs_sin_complement (n : ℕ) [NeZero n] (k : ZMod n) :
    |Real.sin (Real.pi * (ZMod.val k : ℝ) / n)| =
    |Real.sin (Real.pi * ((n : ℝ) - ZMod.val k) / n)| := by
  have h_angle : Real.pi * ((n : ℝ) - ZMod.val k) / n = Real.pi - Real.pi * (ZMod.val k : ℝ) / n :=
    by
    have h₁ : (n : ℝ) ≠ 0 := by
      norm_cast
      exact_mod_cast NeZero.ne n
    have h₂ : Real.pi * ((n : ℝ) - ZMod.val k) / n = (Real.pi * (n : ℝ) - Real.pi *
      (ZMod.val k : ℝ)) / n := by
      ring_nf
    rw [h₂]
    have h₃ : (Real.pi * (n : ℝ) - Real.pi * (ZMod.val k : ℝ)) / n = Real.pi - Real.pi *
      (ZMod.val k : ℝ) / n := by
      field_simp [h₁]
    rw [h₃]
  have h_sin_eq : Real.sin (Real.pi * ((n : ℝ) - ZMod.val k) / n) = Real.sin (Real.pi *
    (ZMod.val k : ℝ) / n) := by
    have h₂ : Real.sin (Real.pi * ((n : ℝ) - ZMod.val k) / n) = Real.sin (Real.pi - Real.pi *
      (ZMod.val k : ℝ) / n) := by
      rw [h_angle]
    rw [h₂]
    have h₃ : Real.sin (Real.pi - Real.pi * (ZMod.val k : ℝ) / n) = Real.sin (Real.pi *
      (ZMod.val k : ℝ) / n) := by
      rw [Real.sin_pi_sub]
    rw [h₃]
  have h_abs_eq : |Real.sin (Real.pi * (ZMod.val k : ℝ) / n)| = |Real.sin (Real.pi * ((n : ℝ) -
    ZMod.val k) / n)| := by
    rw [h_sin_eq]
  rw [h_abs_eq]

lemma abs_sin_ge_two_min_div (n : ℕ) [NeZero n] (k : ZMod n) (hk : k ≠ 0) :
    2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) / n ≤
    |Real.sin (Real.pi * (ZMod.val k : ℝ) / n)| := by
  have hval_pos : 0 < ZMod.val k := Nat.pos_of_ne_zero ((ZMod.val_ne_zero k).mpr hk)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hval_lt : (ZMod.val k : ℝ) < (n : ℝ) := by exact_mod_cast ZMod.val_lt k
  by_cases hle : 2 * ZMod.val k ≤ n
  · have hle' : (ZMod.val k : ℝ) ≤ (n : ℝ) - (ZMod.val k : ℝ) := by
      have : (2 * ZMod.val k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
      linarith
    rw [min_eq_left hle']
    exact two_v_div_n_le_abs_sin n _ hn_pos (by exact_mod_cast hval_pos) (by linarith)
  · have hgt : (n : ℝ) < 2 * (ZMod.val k : ℝ) := by
      exact_mod_cast (by omega : n < 2 * ZMod.val k)
    have hle' : (n : ℝ) - (ZMod.val k : ℝ) ≤ (ZMod.val k : ℝ) := by linarith
    rw [min_eq_right hle']
    rw [abs_sin_val_eq_abs_sin_complement]
    exact two_v_div_n_le_abs_sin n _ hn_pos (by linarith) (by linarith)

lemma geom_sum_shift_eq (r : ℂ) (hr_ne : r ≠ 1) (m : ℕ) :
    ∑ t ∈ Finset.range m, r ^ (t + 1) = r * (r ^ m - 1) / (r - 1) := by
  simp_rw [pow_succ']
  rw [← Finset.mul_sum, geom_sum_eq hr_ne, mul_div_assoc]

lemma norm_pow_sub_one_le_two (r : ℂ) (hr_norm : ‖r‖ = 1) (m : ℕ) :
    ‖r ^ m - 1‖ ≤ 2 := by
  have h1 : ‖r ^ m‖ = 1 := by simp_all
  have h2 : ‖(1 : ℂ)‖ = 1 := by simp
  have h3 : ‖r ^ m - 1‖ ≤ ‖r ^ m‖ + ‖(1 : ℂ)‖ := by exact norm_sub_le _ _
  have h4 : ‖r ^ m - 1‖ ≤ 2 := by nlinarith
  assumption

lemma norm_geom_sum_le (r : ℂ) (hr_ne : r ≠ 1) (hr_norm : ‖r‖ = 1) (m : ℕ) :
    ‖∑ t ∈ Finset.range m, r ^ (t + 1)‖ ≤ 2 / ‖1 - r‖ := by
  rw [show ‖1 - r‖ = ‖r - 1‖ by rw [norm_sub_rev]]
  rw [geom_sum_shift_eq r hr_ne m]
  rw [norm_div, norm_mul, hr_norm, one_mul]
  exact div_le_div_of_nonneg_right (norm_pow_sub_one_le_two r hr_norm m) (norm_nonneg _)

lemma norm_one_sub_stdAddChar_lower_bound (n : ℕ) [NeZero n] (k : ZMod n) (hk : k ≠ 0) :
    (4 : ℝ) * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) / n ≤
      ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖ := by
  rw [norm_one_sub_stdAddChar_eq,
    show (4 : ℝ) * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) / n
      = 2 * (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) / n) from by ring]
  exact mul_le_mul_of_nonneg_left (abs_sin_ge_two_min_div n k hk) (by norm_num)

lemma stdAddChar_ne_one (n : ℕ) [NeZero n] (k : ZMod n) (hk : k ≠ 0) :
    ZMod.stdAddChar (-k) ≠ 1 := by
  have h_neg_k_ne_zero : -k ≠ 0 := by simp_all
  have h_primitive : (ZMod.stdAddChar : AddChar (ZMod n) ℂ).IsPrimitive :=
    by exact ZMod.isPrimitive_stdAddChar n
  exact fun h_eq => h_neg_k_ne_zero ((h_primitive.zmod_char_eq_one_iff n (-k)).mp h_eq)

lemma norm_stdAddChar_eq_one (n : ℕ) [NeZero n] (k : ZMod n) :
    ‖ZMod.stdAddChar (-k : ZMod n)‖ = 1 := by
  have h_main : ‖ZMod.stdAddChar (-k : ZMod n)‖ = 1 := by simp
  assumption

lemma normalizedDFT_intervalIndicator_nonzero_bound
    (n : ℕ) [NeZero n] (m : ℕ) (_hm1 : 1 ≤ m) (hm2 : m < n)
    (k : ZMod n) (hk : k ≠ 0) :
    ‖normalizedDFT n (intervalIndicator n m) k‖ ≤
      1 / (2 * (min (ZMod.val k) (n - ZMod.val k) : ℝ)) := by
  unfold normalizedDFT
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rw [dft_intervalIndicator_eq_geom_sum n m hm2 k]
  have h_geom := norm_geom_sum_le (ZMod.stdAddChar (-k)) (stdAddChar_ne_one n k hk)
    (norm_stdAddChar_eq_one n k) m
  have h_lower := norm_one_sub_stdAddChar_lower_bound n k hk
  have h_pos : (0 : ℝ) < ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖ := by
    have h_ne : (1 : ℂ) - ZMod.stdAddChar (-k) ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      exact stdAddChar_ne_one n k hk h.symm
    exact norm_pos_iff.mpr h_ne
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have h_min_pos : (0 : ℝ) < min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) :=
    lt_min (by exact_mod_cast Nat.pos_of_ne_zero ((ZMod.val_ne_zero k).mpr hk))
      (sub_pos.mpr (Nat.cast_lt.mpr (ZMod.val_lt k)))
  calc (n : ℝ)⁻¹ * ‖∑ t ∈ Finset.range m, ZMod.stdAddChar (-k) ^ (t + 1)‖
      ≤ (n : ℝ)⁻¹ * (2 / ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖) := by
        nlinarith [inv_pos.mpr hn_pos, h_geom]
    _ = 2 / ((n : ℝ) * ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖) := by
        field_simp [hn_pos.ne', h_pos.ne']
    _ ≤ 1 / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [show 4 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) / (n : ℝ) * (n : ℝ) =
            4 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) from by field_simp [hn_pos.ne']]

lemma sum_nonzero_reindex (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    ∑ k ∈ (Finset.univ : Finset (ZMod n)).filter (· ≠ 0),
      (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) =
    ∑ t ∈ Finset.Icc 1 (n - 1),
      (1 : ℝ) / (2 * min (t : ℝ) ((n : ℝ) - t)) := by
  apply Finset.sum_nbij ZMod.val
  · intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    have h1 := ZMod.val_lt k
    have h2 : ZMod.val k ≠ 0 := (ZMod.val_ne_zero k).mpr hk'
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · exact fun _ _ _ _ h => ZMod.val_injective n h
  · intro y hy
    simp only [Finset.coe_Icc, Set.mem_Icc] at hy
    have h1 : y < n := by omega
    refine ⟨(y : ZMod n), ?_, ZMod.val_cast_of_lt (by omega)⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    intro h
    have hvy : ZMod.val (y : ZMod n) = y := ZMod.val_cast_of_lt (by omega)
    rw [h, ZMod.val_zero] at hvy
    omega
  · intros; rfl

lemma first_half_eq (N : ℕ) (_hN : 1 ≤ N) :
    ∑ t ∈ Finset.Icc 1 N,
      (1 : ℝ) / (2 * min (t : ℝ) ((2 * N + 1 : ℝ) - t)) =
    ∑ t ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * t) := by
  have h₁ : ∀ (t : ℕ), t ∈ Finset.Icc 1 N → (t : ℝ) ≤ (2 * N + 1 : ℝ) - (t : ℝ) := by
    intro t ht
    have h₃ : t ≤ N := by
      simp [Finset.mem_Icc] at ht
      linarith
    have h₄ : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast h₃
    have h₆ : (t : ℝ) ≤ (2 * N + 1 : ℝ) - (t : ℝ) := by
      nlinarith
    exact h₆
  have h₂ : ∀ (t : ℕ), t ∈ Finset.Icc 1 N → min ((t : ℝ)) ((2 * N + 1 : ℝ) - (t : ℝ)) = (t : ℝ) :=
    by
    intro t ht
    have h₃ : (t : ℝ) ≤ (2 * N + 1 : ℝ) - (t : ℝ) := h₁ t ht
    have h₄ : min ((t : ℝ)) ((2 * N + 1 : ℝ) - (t : ℝ)) = (t : ℝ) := by
      rw [min_eq_left];
      (try linarith)
    exact h₄
  calc
    ∑ t ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * min (t : ℝ) ((2 * N + 1 : ℝ) - t)) =
        ∑ t ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * (t : ℝ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have h₃ : min ((t : ℝ)) ((2 * N + 1 : ℝ) - (t : ℝ)) = (t : ℝ) := h₂ t ht
      rw [h₃]
    _ = ∑ t ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * t) := by
      simp [mul_comm]

lemma summand_min_eq (N : ℕ) (_hN : 1 ≤ N) (t : ℕ) (ht : t ∈ Finset.Icc (N + 1) (2 * N)) :
    (1 : ℝ) / (2 * min (t : ℝ) ((2 * N + 1 : ℝ) - t)) =
    (1 : ℝ) / (2 * ((2 * N + 1 : ℝ) - t)) := by
  have h₁ : (N + 1 : ℕ) ≤ t := (Finset.mem_Icc.mp ht).1
  have h₃ : (2 * N + 1 : ℝ) - t ≤ (t : ℝ) := by
    have h₄ : (t : ℝ) ≥ (N + 1 : ℝ) := by
      norm_cast
    linarith
  have h₄ : min (t : ℝ) ((2 * N + 1 : ℝ) - t) = (2 * N + 1 : ℝ) - t := by
    apply min_eq_right
    linarith
  rw [h₄]

lemma second_half_min_simplify (N : ℕ) (hN : 1 ≤ N) :
    ∑ t ∈ Finset.Icc (N + 1) (2 * N),
      (1 : ℝ) / (2 * min (t : ℝ) ((2 * N + 1 : ℝ) - t)) =
    ∑ t ∈ Finset.Icc (N + 1) (2 * N),
      (1 : ℝ) / (2 * ((2 * N + 1 : ℝ) - t)) := by
  exact Finset.sum_congr rfl fun t ht => summand_min_eq N hN t ht

lemma second_half_reindex (N : ℕ) (_hN : 1 ≤ N) :
    ∑ t ∈ Finset.Icc (N + 1) (2 * N),
      (1 : ℝ) / (2 * ((2 * N + 1 : ℝ) - t)) =
    ∑ u ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * u) := by
  exact Finset.sum_nbij' (fun t => 2 * N + 1 - t) (fun u => 2 * N + 1 - u)
    (by simp only [Finset.mem_Icc]; omega)
    (by simp only [Finset.mem_Icc]; omega)
    (by simp only [Finset.mem_Icc]; omega)
    (by simp only [Finset.mem_Icc]; omega)
    (fun t ht => by
      congr 2
      push_cast [Nat.cast_sub (by simp only [Finset.mem_Icc] at ht; omega : t ≤ 2 * N + 1)]
      ring)

lemma second_half_eq (N : ℕ) (hN : 1 ≤ N) :
    ∑ t ∈ Finset.Icc (N + 1) (2 * N),
      (1 : ℝ) / (2 * min (t : ℝ) ((2 * N + 1 : ℝ) - t)) =
    ∑ u ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * u) := by
  rw [second_half_min_simplify N hN]
  exact second_half_reindex N hN

lemma combine_halves (N : ℕ) :
    ∑ u ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * u) +
    ∑ u ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * u) =
    ∑ u ∈ Finset.Icc 1 N, (u : ℝ)⁻¹ := by
  have h₁ : ∑ u ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * u) + ∑ u ∈ Finset.Icc 1 N,
    (1 : ℝ) / (2 * u) = 2 * ∑ u ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * u) := by
    have h₁₁ : ∑ u ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * u) + ∑ u ∈ Finset.Icc 1 N,
      (1 : ℝ) / (2 * u) = 2 * ∑ u ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * u) := by
      ring
    rw [h₁₁]
  have h₂ : 2 * ∑ u ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * u) = ∑ u ∈ Finset.Icc 1 N, (u : ℝ)⁻¹ := by
    have h₂₁ : 2 * ∑ u ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * u) = ∑ u ∈ Finset.Icc 1 N,
      (2 : ℝ) * ((1 : ℝ) / (2 * u)) := by
      rw [Finset.mul_sum]
    rw [h₂₁]
    have h₂₂ : ∑ u ∈ Finset.Icc 1 N, (2 : ℝ) * ((1 : ℝ) / (2 * u)) = ∑ u ∈ Finset.Icc 1 N,
      (1 : ℝ) / u := by
      apply Finset.sum_congr rfl
      intro u hu
      have h₂₂₁ : (u : ℕ) ∈ Finset.Icc 1 N := by simpa using hu
      have h₂₂₂ : 1 ≤ u := by
        simp only [Finset.mem_Icc] at h₂₂₁
        linarith
      have h₂₂₃ : (u : ℝ) ≠ 0 := by
        have h₂₂₄ : (u : ℕ) ≥ 1 := by
          simp only [Finset.mem_Icc] at h₂₂₁
          linarith
        have h₂₂₅ : (u : ℝ) ≥ 1 := by
          norm_cast
        linarith
      field_simp [h₂₂₃]
    rw [h₂₂]
    have h₂₃ : ∑ u ∈ Finset.Icc 1 N, (1 : ℝ) / u = ∑ u ∈ Finset.Icc 1 N, (u : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro u hu
      have h₂₃₁ : (u : ℕ) ∈ Finset.Icc 1 N := by simpa using hu
      have h₂₃₂ : 1 ≤ u := by
        simp only [Finset.mem_Icc] at h₂₃₁
        linarith
      have h₂₃₃ : (u : ℝ) ≠ 0 := by
        have h₂₃₄ : (u : ℕ) ≥ 1 := by
          simp only [Finset.mem_Icc] at h₂₃₁
          linarith
        have h₂₃₅ : (u : ℝ) ≥ 1 := by
          norm_cast
        linarith
      field_simp [h₂₃₃]
    rw [h₂₃]
  rw [h₁]
  rw [h₂]

lemma symmetric_sum_odd (N : ℕ) (hN : 1 ≤ N) :
    ∑ t ∈ Finset.Icc 1 (2 * N),
      (1 : ℝ) / (2 * min (t : ℝ) ((2 * N + 1 : ℝ) - t)) =
    ∑ u ∈ Finset.Icc 1 N, (u : ℝ)⁻¹ := by
  rw [show Finset.Icc 1 (2 * N) = Finset.Icc 1 N ∪ Finset.Icc (N + 1) (2 * N) from by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega]
  rw [Finset.sum_union (by simp only [Finset.disjoint_left, Finset.mem_Icc]; omega)]
  rw [first_half_eq N hN, second_half_eq N hN]
  exact combine_halves N

lemma Icc_split_three (N : ℕ) (hN : 2 ≤ N) :
    Finset.Icc 1 (2 * N - 1) =
      Finset.Icc 1 (N - 1) ∪ {N} ∪ Finset.Icc (N + 1) (2 * N - 1) := by
  have h₂ : Finset.Icc 1 (N - 1) ∪ {N} ∪ Finset.Icc (N + 1) (2 * N - 1) ⊆ Finset.Icc 1 (2 * N -
    1) :=
      by
        intro x hx; simp only [Finset.mem_union, Finset.mem_Icc,
          Finset.mem_singleton] at hx ⊢; omega
  have h_main : Finset.Icc 1 (2 * N - 1) = Finset.Icc 1 (N - 1) ∪ {N} ∪ Finset.Icc (N + 1) (2 * N -
    1) := by ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]; omega
  exact h_main

lemma Icc_disjoint_high (N : ℕ) (hN : 2 ≤ N) :
    Disjoint (Finset.Icc 1 (N - 1) ∪ {N}) (Finset.Icc (N + 1) (2 * N - 1)) := by
  have h₁ : Disjoint (Finset.Icc 1 (N - 1)) (Finset.Icc (N + 1) (2 * N - 1)) := by
    apply Finset.disjoint_left.mpr
    intro x hx₁ hx₂
    simp only [Finset.mem_Icc] at hx₁ hx₂
    have h₇ : N - 1 < N + 1 := by
      have h₉ : N - 1 < N := by
        have h₁₀ : N - 1 < N := by
          omega
        exact h₁₀
      omega
    omega
  have h₂ : Disjoint ({N} : Finset ℕ) (Finset.Icc (N + 1) (2 * N - 1)) := by
    apply Finset.disjoint_left.mpr
    intro x hx₁ hx₂
    simp only [Finset.mem_singleton, Finset.mem_Icc] at hx₁ hx₂
    omega
  have h₃ : Disjoint (Finset.Icc 1 (N - 1) ∪ {N}) (Finset.Icc (N + 1) (2 * N - 1)) := by
    apply Finset.disjoint_union_left.mpr
    constructor
    · exact h₁
    · exact h₂
  exact h₃

lemma Icc_disjoint_mid (N : ℕ) (hN : 2 ≤ N) :
    Disjoint (Finset.Icc 1 (N - 1)) ({N} : Finset ℕ) := by
  have h₁ : ∀ x ∈ Finset.Icc 1 (N - 1), x ≠ N := by
    intro x hx
    have h₃ : x ≤ N - 1 := Finset.mem_Icc.mp hx |>.2
    have h₄ : x < N := by
      have h₆ : N - 1 < N := by
        omega
      omega
    omega
  apply Finset.disjoint_left.mpr
  intro x hx₁ hx₂
  have h₂ : x = N := by simp_all [Finset.mem_singleton]
  have h₃ : x ∈ Finset.Icc 1 (N - 1) := hx₁
  have h₄ : x ≠ N := h₁ x h₃
  contradiction

lemma sum_region_A (N : ℕ) (hN : 2 ≤ N) :
    ∑ t ∈ Finset.Icc 1 (N - 1),
      (1 : ℝ) / (2 * min (t : ℝ) ((2 * N : ℝ) - t)) =
    ∑ t ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (2 * (t : ℝ)) := by
  have h_main : ∀ (t : ℕ),
    t ∈ Finset.Icc 1 (N - 1) → (1 : ℝ) / (2 * min (t : ℝ) ((2 * N : ℝ) - t)) = (1 : ℝ) / (2 *
      (t : ℝ)) := by
    intro t ht
    have h₁ : 1 ≤ t ∧ t ≤ N - 1 := Finset.mem_Icc.mp ht
    have h₄ : (t : ℕ) < N := by
      have h₆ : N - 1 < N := by
        omega
      omega
    have h₅ : (t : ℝ) ≤ (2 * N : ℝ) - t := by
      have h₆ : (t : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (by omega)
      linarith
    have h₆ : min (t : ℝ) ((2 * N : ℝ) - t) = (t : ℝ) := by
      rw [min_eq_left h₅]
    rw [h₆]
  calc
    ∑ t ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (2 * min (t : ℝ) ((2 * N : ℝ) - t)) =
      ∑ t ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (2 * (t : ℝ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [h_main t ht]
    _ = ∑ t ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (2 * (t : ℝ)) := by rfl

lemma min_midpoint (N : ℕ) :
    min (N : ℝ) ((2 * N : ℝ) - N) = (N : ℝ) := by
  have h₁ : (2 * (N : ℝ) - N : ℝ) = (N : ℝ) := by
    ring_nf
  rw [h₁]
  simp

lemma min_eq_complement_in_region_C (N : ℕ) (t : ℕ) (ht : t ∈ Finset.Icc (N + 1) (2 * N - 1)) :
    min (t : ℝ) ((2 * N : ℝ) - t) = (2 * N : ℝ) - t := by
  have h₂ : (t : ℕ) ≥ N + 1 := (Finset.mem_Icc.mp ht).1
  have h₅ : ((2 * N : ℝ) - (t : ℝ)) ≤ (t : ℝ) := by
    have h₅₁ : (t : ℝ) ≥ (N : ℝ) + 1 := by
      exact_mod_cast (by omega)
    have h₅₂ : ((2 : ℝ) * N - (t : ℝ)) ≤ (t : ℝ) := by
      have h₅₃ : (2 : ℝ) * N - (t : ℝ) ≤ (t : ℝ) := by
        nlinarith
      exact h₅₃
    exact h₅₂
  have h₆ : min (t : ℝ) ((2 * N : ℝ) - (t : ℝ)) = (2 * N : ℝ) - (t : ℝ) := by
    apply min_eq_right
    simp_all
  simpa using h₆

lemma sum_region_C (N : ℕ) (hN : 2 ≤ N) :
    ∑ t ∈ Finset.Icc (N + 1) (2 * N - 1),
      (1 : ℝ) / (2 * min (t : ℝ) ((2 * N : ℝ) - t)) =
    ∑ u ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (2 * (u : ℝ)) := by
  have step1 : ∑ t ∈ Finset.Icc (N + 1) (2 * N - 1),
      (1 : ℝ) / (2 * min (t : ℝ) ((2 * N : ℝ) - t)) =
      ∑ t ∈ Finset.Icc (N + 1) (2 * N - 1),
      (1 : ℝ) / (2 * ((2 * N : ℝ) - t)) :=
    Finset.sum_congr rfl fun t ht => by rw [min_eq_complement_in_region_C N t ht]
  rw [step1]
  exact Finset.sum_nbij' (fun t => 2 * N - t) (fun u => 2 * N - u)
    (by simp only [Finset.mem_Icc]; omega)
    (by simp only [Finset.mem_Icc]; omega)
    (by simp only [Finset.mem_Icc]; omega)
    (by simp only [Finset.mem_Icc]; omega)
    (fun t ht => by
      congr 2
      push_cast [Nat.cast_sub (by simp only [Finset.mem_Icc] at ht; omega : t ≤ 2 * N)]
      ring)

lemma symmetric_sum_even (N : ℕ) (hN : 1 ≤ N) :
    ∑ t ∈ Finset.Icc 1 (2 * N - 1),
      (1 : ℝ) / (2 * min (t : ℝ) ((2 * N : ℝ) - t)) =
    (∑ u ∈ Finset.Icc 1 (N - 1), (u : ℝ)⁻¹) + 1 / (2 * N) := by
  obtain rfl | hN2 := eq_or_lt_of_le hN
  · norm_num
  · rw [Icc_split_three N hN2,
        Finset.sum_union (Icc_disjoint_high N hN2),
        Finset.sum_union (Icc_disjoint_mid N hN2),
        Finset.sum_singleton,
        min_midpoint N,
        sum_region_A N hN2,
        sum_region_C N hN2]
    linarith [combine_halves (N - 1)]

lemma ratio_rewrite (u : ℕ) (hu : 1 ≤ u) :
    (2 * (u : ℝ) + 1) / (2 * u - 1) = 1 + 2 / (2 * u - 1) := by
  have h₁ : (u : ℝ) ≥ 1 := by exact_mod_cast hu
  have h₂ : (2 : ℝ) * u - 1 > 0 := by
    linarith
  have h₃ : (2 : ℝ) * (u : ℝ) + 1 = 1 * ((2 : ℝ) * u - 1) + 2 := by
    ring_nf
  have h₄ : (2 * (u : ℝ) + 1) / (2 * u - 1) = 1 + 2 / (2 * u - 1) := by
    have h₅ : (2 * (u : ℝ) + 1) / (2 * u - 1) = (1 * ((2 : ℝ) * u - 1) + 2) / (2 * u - 1) := by
      rw [h₃]
    rw [h₅]
    have h₆ : (1 * ((2 : ℝ) * u - 1) + 2) / (2 * u - 1) = 1 + 2 / (2 * u - 1) := by
      have h₇ : (2 * u - 1 : ℝ) ≠ 0 := by linarith
      field_simp [h₇]
    rw [h₆]
  exact h₄

lemma pade_algebraic_identity (u : ℕ) (hu : 1 ≤ u) :
    2 * (2 / (2 * (u : ℝ) - 1)) / (2 / (2 * u - 1) + 2) = (u : ℝ)⁻¹ := by
  have h₁ : (u : ℝ) ≥ 1 := by simp_all
  have h₂ : (2 : ℝ) * (u : ℝ) - 1 ≠ 0 := by nlinarith
  have h₃ : 2 * (2 / (2 * (u : ℝ) - 1)) / (2 / (2 * (u : ℝ) - 1) + 2) = (u : ℝ)⁻¹ :=
    by field_simp; ring
  assumption

lemma inv_le_log_ratio (u : ℕ) (hu : 1 ≤ u) :
    (u : ℝ)⁻¹ ≤ Real.log ((2 * u + 1) / (2 * u - 1)) := by
  have h1 : (2 : ℝ) * u - 1 > 0 := by
    have : (1 : ℝ) ≤ (u : ℝ) := Nat.one_le_cast.mpr hu
    linarith
  rw [ratio_rewrite u hu, ← pade_algebraic_identity u hu]
  exact le_of_lt (Real.lt_log_one_add_of_pos (by positivity : (0 : ℝ) < 2 / (2 * u - 1)))

lemma telescoping_log_sum (N : ℕ) (hN : 1 ≤ N) :
    ∑ u ∈ Finset.Icc 1 N, Real.log ((2 * (u : ℝ) + 1) / (2 * u - 1)) =
    Real.log (2 * N + 1) := by
  have h : ∀ (n : ℕ), 1 ≤ n → ∑ u ∈ Finset.Icc 1 n,
    Real.log ((2 * (u : ℝ) + 1) / (2 * u - 1)) = Real.log (2 * n + 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num [Finset.sum_Icc_succ_top]
    | succ n hn IH =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n.succ)]
      rw [IH]
      have h₁ : (n : ℝ) ≥ 1 := by exact_mod_cast hn
      have h₂ : (2 * (n : ℝ) + 1 : ℝ) > 0 := by linarith
      have h₃ : (2 * (n : ℝ) - 1 : ℝ) > 0 := by
        linarith
      have h₄ : (2 * (n.succ : ℝ) + 1 : ℝ) > 0 := by positivity
      have h₅ : (2 * (n.succ : ℝ) - 1 : ℝ) > 0 := by
        have h₆ : (n : ℝ) ≥ 1 := by exact_mod_cast hn
        norm_num [Nat.cast_add, Nat.cast_one] at h₆ ⊢
        linarith
      have h₆ : Real.log ((2 * (n.succ : ℝ) + 1) / (2 * (n.succ : ℝ) - 1)) = Real.log (2 *
        (n.succ : ℝ) + 1) - Real.log (2 * (n : ℝ) + 1) := by
        have h₇ : (2 * (n.succ : ℝ) + 1 : ℝ) = (2 * (n : ℝ) + 3 : ℝ) := by
          norm_num [Nat.cast_add, Nat.cast_one]
          ring_nf
        have h₈ : (2 * (n.succ : ℝ) - 1 : ℝ) = (2 * (n : ℝ) + 1 : ℝ) := by
          norm_num [Nat.cast_add, Nat.cast_one]
          ring_nf
        rw [h₇, h₈]
        have h₉ : Real.log ((2 * (n : ℝ) + 3 : ℝ) / (2 * (n : ℝ) + 1 : ℝ)) = Real.log (2 * (n : ℝ) +
          3) - Real.log (2 * (n : ℝ) + 1) := by
          have h₁₂ : Real.log ((2 * (n : ℝ) + 3 : ℝ) / (2 * (n : ℝ) + 1 : ℝ)) = Real.log (2 *
            (n : ℝ) + 3) - Real.log (2 * (n : ℝ) + 1) := by
            rw [Real.log_div (by linarith) (by linarith)]
          rw [h₁₂]
        have h₁₀ : Real.log (2 * (n : ℝ) + 3) = Real.log (2 * (n.succ : ℝ) + 1) := by
          norm_num [Nat.cast_add, Nat.cast_one] at *
          ring_nf at *
        rw [h₉, h₁₀]
      have h₇ : Real.log (2 * (n : ℝ) + 1) + Real.log ((2 * (n.succ : ℝ) + 1) / (2 * (n.succ : ℝ) -
        1)) = Real.log (2 * (n.succ : ℝ) + 1) := by
        rw [h₆]
        linarith
      rw [h₇]
  have h₁ : ∑ u ∈ Finset.Icc 1 N,
    Real.log ((2 * (u : ℝ) + 1) / (2 * u - 1)) = Real.log (2 * N + 1) := by
    exact h N hN
  exact h₁

lemma harmonic_Icc_le_log_odd (N : ℕ) (hN : 1 ≤ N) :
    ∑ u ∈ Finset.Icc 1 N, (u : ℝ)⁻¹ ≤ Real.log (2 * N + 1) := by
  calc ∑ u ∈ Finset.Icc 1 N, (u : ℝ)⁻¹
      ≤ ∑ u ∈ Finset.Icc 1 N, Real.log ((2 * (u : ℝ) + 1) / (2 * u - 1)) :=
        Finset.sum_le_sum fun u hu => inv_le_log_ratio u (Finset.mem_Icc.mp hu).1
    _ = Real.log (2 * N + 1) := telescoping_log_sum N hN

lemma one_sub_inv_ratio_eq (N : ℕ) (hN : 1 ≤ N) :
    1 - (2 * (N : ℝ) / (2 * N - 1))⁻¹ = 1 / (2 * N) := by
  have h₁ : (2 : ℝ) * (N : ℝ) - 1 > 0 := by
    have h₁ : (N : ℝ) ≥ 1 := by exact_mod_cast hN
    linarith
  have h₂ : (2 : ℝ) * (N : ℝ) > 0 := by
    linarith
  have h₃ : (2 * (N : ℝ) / (2 * N - 1))⁻¹ = (2 * N - 1 : ℝ) / (2 * N : ℝ) := by
    have h₃ : (2 * (N : ℝ) / (2 * N - 1))⁻¹ = (2 * N - 1 : ℝ) / (2 * N : ℝ) := by
      field_simp [h₁.ne', h₂.ne']
    rw [h₃]
  calc
    1 - (2 * (N : ℝ) / (2 * N - 1))⁻¹ = 1 - ((2 * N - 1 : ℝ) / (2 * N : ℝ)) := by rw [h₃]
    _ = 1 / (2 * N : ℝ) := by
      have h₄ : (2 * N : ℝ) ≠ 0 := by positivity
      have h₅ : (2 * N - 1 : ℝ) / (2 * N : ℝ) = 1 - 1 / (2 * N : ℝ) := by
        field_simp [h₄]
      rw [h₅]
      ring_nf

lemma inv_two_N_le_log_ratio (N : ℕ) (hN : 1 ≤ N) :
    1 / (2 * (N : ℝ)) ≤ Real.log (2 * N / (2 * N - 1)) := by
  rw [← one_sub_inv_ratio_eq N hN]
  apply Real.one_sub_inv_le_log_of_pos
  have hN' : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  have h2N1 : (0 : ℝ) < 2 * N - 1 := by linarith
  exact div_pos (by linarith) h2N1

lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have := Real.log_two_gt_d9
  norm_num at this ⊢
  linarith

lemma harmonic_Icc_plus_remainder_le_log_even (N : ℕ) (hN : 1 ≤ N) :
    (∑ u ∈ Finset.Icc 1 (N - 1), (u : ℝ)⁻¹) + 1 / (2 * N) ≤ Real.log (2 * N) := by
  rcases eq_or_lt_of_le hN with rfl | hN2
  · simp
    have := half_le_log_two
    linarith
  · calc (∑ u ∈ Finset.Icc 1 (N - 1), (u : ℝ)⁻¹) + 1 / (2 * N)
        ≤ Real.log (2 * ↑(N - 1) + 1) + Real.log (2 * N / (2 * N - 1)) := by
          gcongr
          · exact harmonic_Icc_le_log_odd (N - 1) (by omega)
          · exact inv_two_N_le_log_ratio N (by omega)
      _ = Real.log (2 * N) := by
          rw [show (2 : ℝ) * ↑(N - 1) + 1 = 2 * ↑N - 1 from by
            push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
            ring]
          have hpos : (2 : ℝ) * N - 1 > 0 := by
            linarith [show (2 : ℝ) ≤ (N : ℝ) from by exact_mod_cast hN2]
          rw [← Real.log_mul (by linarith) (by positivity)]
          congr 1
          field_simp

lemma symmetric_harmonic_sum_le_log (n : ℕ) (hn : 2 ≤ n) :
    ∑ t ∈ Finset.Icc 1 (n - 1),
      (1 : ℝ) / (2 * min (t : ℝ) ((n : ℝ) - t)) ≤ Real.log n := by
  obtain ⟨N, hN | hN⟩ := Nat.even_or_odd' n
  · have hN1 : 1 ≤ N := by omega
    subst hN
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    calc ∑ t ∈ Finset.Icc 1 (2 * N - 1),
          (1 : ℝ) / (2 * min (t : ℝ) (2 * ↑N - t))
        = (∑ u ∈ Finset.Icc 1 (N - 1), (u : ℝ)⁻¹) + 1 / (2 * N) :=
          symmetric_sum_even N hN1
      _ ≤ Real.log (2 * N) := harmonic_Icc_plus_remainder_le_log_even N hN1
  · have hN1 : 1 ≤ N := by omega
    subst hN
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [show 2 * N + 1 - 1 = 2 * N from by omega]
    calc ∑ t ∈ Finset.Icc 1 (2 * N),
          (1 : ℝ) / (2 * min (t : ℝ) (2 * ↑N + 1 - t))
      _ = ∑ u ∈ Finset.Icc 1 N, (u : ℝ)⁻¹ := symmetric_sum_odd N hN1
      _ ≤ Real.log (2 * N + 1) := harmonic_Icc_le_log_odd N hN1

lemma fourier_intervalIndicator_l1_bound
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m < n) :
    ∑ k : ZMod n, ‖normalizedDFT n (intervalIndicator n m) k‖ ≤
      1 + Real.log (n : ℝ) := by
  rw [sum_split_zero]
  have h0 : ‖normalizedDFT n (intervalIndicator n m) 0‖ ≤ 1 := by
    rw [normalizedDFT_intervalIndicator_zero n m hm1 hm2, Complex.norm_div,
      Complex.norm_natCast, Complex.norm_natCast,
      div_le_one (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))]
    exact_mod_cast hm2.le
  have h_nonzero : ∑ k ∈ (Finset.univ : Finset (ZMod n)).filter (· ≠ 0),
      ‖normalizedDFT n (intervalIndicator n m) k‖ ≤
      ∑ k ∈ (Finset.univ : Finset (ZMod n)).filter (· ≠ 0),
        (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact normalizedDFT_intervalIndicator_nonzero_bound n m hm1 hm2 k (by simpa using hk)
  linarith [sum_nonzero_reindex n hn, symmetric_harmonic_sum_le_log n hn]

lemma summand_norm_bound
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (p q : ℤ)
    (k l : ZMod n) :
    ‖(if (k, l) ≠ (0, 0) ∧
         (↑(largestPrimeFactor n ^ (n.factorization (largestPrimeFactor n) - 1)) : ℤ) ∣
           (↑(ZMod.val k) * p + ↑(ZMod.val l) * q) ∧
         ¬((↑(largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) : ℤ) ∣
           (↑(ZMod.val k) * p + ↑(ZMod.val l) * q))
       then normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
            normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
            ramanujanSum n (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)
       else 0 : ℂ)‖ ≤
    (Nat.totient n : ℝ) / ((largestPrimeFactor n : ℝ) - 1) *
    (‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
     ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖) := by
  by_cases hcond : (k, l) ≠ (0, 0) ∧
      (↑(largestPrimeFactor n ^ (n.factorization (largestPrimeFactor n) - 1)) : ℤ) ∣
        (↑(ZMod.val k) * p + ↑(ZMod.val l) * q) ∧
      ¬((↑(largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) : ℤ) ∣
        (↑(ZMod.val k) * p + ↑(ZMod.val l) * q))
  · rw [if_pos hcond]
    have hP0 := hcond.2.1
    have hd := hcond.2.2
    calc ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
            normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
          ramanujanSum n (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)‖
        = ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
          ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖ *
          ‖ramanujanSum n (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
          ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖ *
          ((Nat.totient n : ℝ) / ((largestPrimeFactor n : ℝ) - 1)) := by
          gcongr
          exact ramanujanSum_EP0_norm_bound n hn _ hP0 hd
      _ = (Nat.totient n : ℝ) / ((largestPrimeFactor n : ℝ) - 1) *
          (‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
           ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖) := by
          ring
  · rw [if_neg hcond, norm_zero]
    have hP := largestPrimeFactor_ge_two n hn
    apply mul_nonneg
    · apply div_nonneg (Nat.cast_nonneg' _)
      have : (2 : ℝ) ≤ (largestPrimeFactor n : ℝ) := by exact_mod_cast hP
      linarith
    · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

lemma norm_errorTermEP0_le_double_sum
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (p q : ℤ) (_hp : 1 ≤ p) (_hq : 1 ≤ q)
    (_hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    ‖errorTermEP0 n p q‖ ≤
      (Nat.totient n : ℝ) / ((largestPrimeFactor n : ℝ) - 1) *
      (∑ k : ZMod n, ∑ l : ZMod n,
        ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
        ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖) := by
  have h_tri : ‖errorTermEP0 n p q‖ ≤
      ∑ k : ZMod n, ∑ l : ZMod n,
        ‖(if (k, l) ≠ (0, 0) ∧
             (↑(largestPrimeFactor n ^ (n.factorization (largestPrimeFactor n) - 1)) : ℤ) ∣
               (↑(ZMod.val k) * p + ↑(ZMod.val l) * q) ∧
             ¬((↑(largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) : ℤ) ∣
               (↑(ZMod.val k) * p + ↑(ZMod.val l) * q))
           then normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
                normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
                ramanujanSum n (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)
           else 0 : ℂ)‖ := by
    unfold errorTermEP0
    simp only
    exact (norm_sum_le ..).trans (Finset.sum_le_sum fun k _ => norm_sum_le ..)
  calc ‖errorTermEP0 n p q‖
      ≤ ∑ k : ZMod n, ∑ l : ZMod n, _ := h_tri
    _ ≤ ∑ k : ZMod n, ∑ l : ZMod n,
          ((Nat.totient n : ℝ) / ((largestPrimeFactor n : ℝ) - 1) *
          (‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
           ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖)) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
          summand_norm_bound n hn p q k l
    _ = (Nat.totient n : ℝ) / ((largestPrimeFactor n : ℝ) - 1) *
        (∑ k : ZMod n, ∑ l : ZMod n,
          ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
          ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖) := by
        simp_rw [Finset.mul_sum]

lemma norm_errorTermEP0_le_product
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    ‖errorTermEP0 n p q‖ ≤
      (Nat.totient n : ℝ) / ((largestPrimeFactor n : ℝ) - 1) *
      (∑ k : ZMod n, ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖) *
      (∑ l : ZMod n, ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖) := by
  have h1 := norm_errorTermEP0_le_double_sum n hn p q hp hq hpq
  rw [double_sum_norms_eq_product] at h1
  linarith

lemma norm_errorTermEP0_le
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    ‖errorTermEP0 n p q‖ ≤
      (Nat.totient n : ℝ) * (1 + Real.log (n : ℝ)) ^ 2 /
        ((largestPrimeFactor n : ℝ) - 1) := by
  have h1 := norm_errorTermEP0_le_product n hn p q hp hq hpq
  have hmp := mp_valid n hn p q hp hq hpq
  have hmq := mq_valid n hn p q hp hq hpq
  have h2p := fourier_intervalIndicator_l1_bound n hn (2 * p - 1).toNat hmp.1 hmp.2
  have h2q := fourier_intervalIndicator_l1_bound n hn (2 * q - 1).toNat hmq.1 hmq.2
  have hP := largestPrimeFactor_ge_two n hn
  have hP_pos : (0 : ℝ) < (largestPrimeFactor n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (largestPrimeFactor n : ℝ) := by exact_mod_cast hP
    linarith
  calc ‖errorTermEP0 n p q‖
      ≤ (Nat.totient n : ℝ) / ((largestPrimeFactor n : ℝ) - 1) *
        (∑ k : ZMod n, ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖) *
        (∑ l : ZMod n, ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖) := h1
    _ ≤ (Nat.totient n : ℝ) / ((largestPrimeFactor n : ℝ) - 1) *
        (1 + Real.log (n : ℝ)) *
        (1 + Real.log (n : ℝ)) := by
        gcongr
    _ = (Nat.totient n : ℝ) * (1 + Real.log (n : ℝ)) ^ 2 /
        ((largestPrimeFactor n : ℝ) - 1) := by ring
lemma error_EP0_universal_bound
    (n : ℕ) (hn : 2 ≤ n)
    (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2) :
    haveI : NeZero n := ⟨by omega⟩
    |(errorTermEP0 n p q).re| ≤
      (Nat.totient n : ℝ) * (1 + Real.log (n : ℝ)) ^ 2 /
        ((largestPrimeFactor n : ℝ) - 1) := by
  haveI : NeZero n := ⟨by omega⟩
  exact le_trans (Complex.abs_re_le_norm _) (norm_errorTermEP0_le n hn p q hp hq hpq)


lemma summand_norm_le_aux (n : ℕ) [NeZero n] (_p _q : ℤ) (k l : ZMod n)
    (fp fq : ZMod n → ℂ) (t : ℤ)
    (cond : Prop) [Decidable cond] :
    ‖(if cond then normalizedDFT n fp k * normalizedDFT n fq l * ramanujanSum n t
      else 0)‖ ≤
    (Nat.totient n : ℝ) *
    (if cond then ‖normalizedDFT n fp k‖ * ‖normalizedDFT n fq l‖ else 0) := by
  by_cases hc : cond
  · simp only [hc, if_true]
    rw [norm_mul, norm_mul]
    calc ‖normalizedDFT n fp k‖ * ‖normalizedDFT n fq l‖ * ‖ramanujanSum n t‖
        ≤ ‖normalizedDFT n fp k‖ * ‖normalizedDFT n fq l‖ * (Nat.totient n : ℝ) := by
          apply mul_le_mul_of_nonneg_left (ramanujanSum_norm_le_totient n t)
          exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      _ = (Nat.totient n : ℝ) * (‖normalizedDFT n fp k‖ * ‖normalizedDFT n fq l‖) := by ring
  · simp only [hc, if_false, norm_zero, mul_zero, le_refl]


lemma summand_norm_le (n : ℕ) [NeZero n] (p q : ℤ)
    (k l : ZMod n) :
    let P := largestPrimeFactor n
    let alpha := n.factorization P
    let d := P ^ alpha
    let fp := intervalIndicator n (2 * p - 1).toNat
    let fq := intervalIndicator n (2 * q - 1).toNat
    ‖(if (k, l) ≠ (0, 0) ∧ (d : ℤ) ∣ (ZMod.val k * p + ZMod.val l * q)
      then normalizedDFT n fp k * normalizedDFT n fq l *
           ramanujanSum n (ZMod.val k * p + ZMod.val l * q)
      else 0)‖ ≤
    (Nat.totient n : ℝ) *
    (if (k, l) ≠ (0, 0) ∧ ((largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℤ)) ∣
         (ZMod.val k * p + ZMod.val l * q)
     then ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
          ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖
     else 0) := by
  simp only
  have : (↑(largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) : ℤ) =
    (↑(largestPrimeFactor n) : ℤ) ^ n.factorization (largestPrimeFactor n) := by
    push_cast; ring
  rw [this]
  exact summand_norm_le_aux n p q k l _ _ _ _


lemma errorTermEPalpha_norm_le_totient_mul (n : ℕ) [NeZero n] (p q : ℤ) :
    ‖errorTermEPalpha n p q‖ ≤
      (Nat.totient n : ℝ) *
      ∑ k : ZMod n, ∑ l : ZMod n,
        if (k, l) ≠ (0, 0) ∧
           ((largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℤ)) ∣
             (ZMod.val k * p + ZMod.val l * q)
        then ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
             ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖
        else 0 := by
  unfold errorTermEPalpha
  calc ‖∑ k : ZMod n, ∑ l : ZMod n,
        if (k, l) ≠ (0, 0) ∧
           ((largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℤ)) ∣
             (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)
        then normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
             normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
             ramanujanSum n (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)
        else 0‖
      ≤ ∑ k : ZMod n, ‖∑ l : ZMod n,
        if (k, l) ≠ (0, 0) ∧
           ((largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℤ)) ∣
             (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)
        then normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
             normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
             ramanujanSum n (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ k : ZMod n, ∑ l : ZMod n,
        ‖(if (k, l) ≠ (0, 0) ∧
           ((largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℤ)) ∣
             (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)
        then normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k *
             normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l *
             ramanujanSum n (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)
        else 0)‖ :=
        Finset.sum_le_sum fun k _ => norm_sum_le _ _
    _ ≤ ∑ k : ZMod n, ∑ l : ZMod n,
        ((Nat.totient n : ℝ) *
        (if (k, l) ≠ (0, 0) ∧
           ((largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℤ)) ∣
             (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)
        then ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
             ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖
        else 0)) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
          summand_norm_le n p q k l
    _ = (Nat.totient n : ℝ) *
        ∑ k : ZMod n, ∑ l : ZMod n,
        (if (k, l) ≠ (0, 0) ∧
           ((largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℤ)) ∣
             (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)
        then ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
             ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖
        else 0) := by
        rw [Finset.mul_sum]
        congr 1
        ext k
        rw [Finset.mul_sum]

lemma d_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) := by
  have h1 := Nat.prime_of_mem_primeFactors (largestPrimeFactor_mem_primeFactors n hn)
  exact Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.one_le_pow _ _ h1.pos))



lemma val_unitOfCoprime_eq_mod
    (d a : ℕ) (hcoprime : a.Coprime d) :
    (ZMod.unitOfCoprime a hcoprime : ZMod d).val = a % d := by
  have h₁ : (↑(ZMod.unitOfCoprime a hcoprime) : ZMod d) = (a : ZMod d) := by
    apply ZMod.coe_unitOfCoprime
  have h₂ : (ZMod.unitOfCoprime a hcoprime : ZMod d).val = (a : ZMod d).val := by
    rw [h₁]
  have h₃ : (a : ZMod d).val = a % d := by
    apply ZMod.val_natCast
  rw [h₂, h₃]



lemma combine_cases_arithmetic
    (C : ℝ) (L : ℝ) (d : ℝ) :
    C * (5 * L / d) + C * (L / d) = C * (6 * L / d) := by
  ring



lemma min_val_pos (n : ℕ) [NeZero n] (k : ZMod n) (hk : k ≠ 0) :
    (0 : ℝ) < min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) := by
  have h₁ : 0 < (ZMod.val k : ℕ) := by
    haveI : Fact (n ≠ 0) := ⟨by simpa using NeZero.ne n⟩
    have h₃ : ZMod.val k ≠ 0 := by
      intro h₃
      have h₄ : (k : ZMod n) = 0 := by
        have h₅ : (ZMod.val k : ℕ) = 0 := by simpa using h₃
        have h₆ : (k : ZMod n) = 0 := by
          rw [ZMod.val_eq_zero] at h₅
          simp_all
        exact h₆
      contradiction
    have h₄ : 0 < ZMod.val k := Nat.pos_of_ne_zero h₃
    exact_mod_cast h₄
  have h₂ : (ZMod.val k : ℕ) < n := by
    haveI : Fact (n ≠ 0) := ⟨by simpa using NeZero.ne n⟩
    have h₃ : (ZMod.val k : ℕ) < n := ZMod.val_lt k
    exact_mod_cast h₃
  have h₃ : (0 : ℝ) < (ZMod.val k : ℝ) := by
    norm_cast at h₁ ⊢
  have h₄ : (0 : ℝ) < (n : ℝ) - (ZMod.val k : ℝ) := by
    have h₄₁ : (ZMod.val k : ℕ) < n := h₂
    have h₄₂ : (ZMod.val k : ℝ) < (n : ℝ) := by
      norm_cast
    have h₄₃ : (0 : ℝ) < (n : ℝ) - (ZMod.val k : ℝ) := by
      linarith
    exact h₄₃
  have h₅ : (0 : ℝ) < min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) := by
    have h₅₃ : (0 : ℝ) < min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) := by
      obtain h | h := le_total (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) <;>
        simp_all
    exact h₅₃
  exact h₅



lemma summand_nonneg
    (n d : ℕ) [NeZero n] [NeZero d]
    (mq : ℕ) (q : ℤ) (u : (ZMod d)ˣ) (k : ZMod n) (l : ZMod n) :
    0 ≤ (if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
         then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
              (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
         else 0) := by
  split_ifs with h
  · exact div_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) (le_of_lt (min_val_pos n k h.1)))
  · exact le_refl 0


lemma sum_exchange_weighted
    (n d : ℕ) [NeZero n] [NeZero d]
    (mq : ℕ) (q : ℤ) :
    ∑ u : (ZMod d)ˣ,
      (∑ k : ZMod n, ∑ l : ZMod n,
        if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
             (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
        else 0) =
    ∑ k : ZMod n, ∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
             (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
        else 0) := by
  rw [Finset.sum_comm]



lemma k_zero_summand_vanish
    (n d : ℕ) [NeZero n] [NeZero d]
    (mq : ℕ) (q : ℤ) (u : (ZMod d)ˣ) :
    (∑ l : ZMod n,
      if (0 : ZMod n) ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val (0 : ZMod n)) * ↑(u : ZMod d).val +
        ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
           (2 * min (ZMod.val (0 : ZMod n) : ℝ) ((n : ℝ) - ZMod.val (0 : ZMod n)))
      else 0) = 0 := by
  have h_main : ∀ (l : ZMod n),
    (if (0 : ZMod n) ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val (0 : ZMod n)) * ↑(u : ZMod d).val +
      ↑(ZMod.val l) * q)) then ‖normalizedDFT n (intervalIndicator n mq) l‖ / (2 *
        min (ZMod.val (0 : ZMod n) : ℝ) ((n : ℝ) - ZMod.val (0 : ZMod n))) else 0) = 0 := by
    intro l
    have h₁ : ¬((0 : ZMod n) ≠ 0) := by
      intro h
      apply h
      rfl
    split_ifs <;> simp_all
  have h_sum : (∑ l : ZMod n,
    if (0 : ZMod n) ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val (0 : ZMod n)) * ↑(u : ZMod d).val + ↑(ZMod.val l) *
      q)) then ‖normalizedDFT n (intervalIndicator n mq) l‖ / (2 *
        min (ZMod.val (0 : ZMod n) : ℝ) ((n : ℝ) - ZMod.val (0 : ZMod n))) else 0) = 0 := by
    calc
      (∑ l : ZMod n,
        if (0 : ZMod n) ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val (0 : ZMod n)) * ↑(u : ZMod d).val +
          ↑(ZMod.val l) * q)) then ‖normalizedDFT n (intervalIndicator n mq) l‖ / (2 *
            min (ZMod.val (0 : ZMod n) : ℝ) ((n : ℝ) - ZMod.val (0 : ZMod n))) else 0) =
              ∑ l : ZMod n, 0 := by
        apply Finset.sum_congr rfl
        intro l _
        rw [h_main l]
      _ = 0 := by simp
  apply h_sum



lemma outer_sum_split (n : ℕ) [NeZero n] (G : ZMod n → ℝ) :
    ∑ k : ZMod n, G k = G 0 + ∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0), G k := by
  have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : ZMod n => k = 0) G
  rw [Finset.sum_filter, Finset.sum_ite_eq' Finset.univ 0 G, if_pos (Finset.mem_univ _)] at h
  linarith



lemma zero_term_vanishes
    (n d : ℕ) [NeZero n] [NeZero d]
    (mq : ℕ) (q : ℤ) :
    ∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if (0 : ZMod n) ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val (0 : ZMod n)) * ↑(u : ZMod d).val +
          ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
             (2 * min (ZMod.val (0 : ZMod n) : ℝ) ((n : ℝ) - ZMod.val (0 : ZMod n)))
        else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro l _
  simp



lemma summand_congr_on_filter
    (n d : ℕ) [NeZero n] [NeZero d]
    (mq : ℕ) (q : ℤ)
    (k : ZMod n) (hk : k ≠ 0) :
    (∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
             (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
        else 0)) =
    (∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
             (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
        else 0)) := by
  congr 1; ext u; congr 1; ext l
  simp [hk]



lemma sum_restrict_to_nonzero
    (n d : ℕ) [NeZero n] [NeZero d]
    (mq : ℕ) (q : ℤ) :
    ∑ k : ZMod n, ∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
             (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
        else 0) =
    ∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0), ∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
             (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
        else 0) := by
  rw [outer_sum_split]
  rw [zero_term_vanishes]
  simp only [zero_add]
  exact Finset.sum_congr rfl fun k hk => by
    exact summand_congr_on_filter n d mq q k (Finset.mem_filter.mp hk).2



lemma split_nonzero_by_divisibility
    (n d : ℕ) [NeZero n] [NeZero d]
    (mq : ℕ) (q : ℤ) :
    ∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0), ∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
             (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
        else 0) =
    (∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)),
      ∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
               (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
          else 0)) +
    (∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
      ∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
               (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
          else 0)) := by
  have h1 : (∑ k ∈ Finset.univ.filter (fun k : ZMod n =>
    k ≠ 0), ∑ u : (ZMod d)ˣ, (∑ l : ZMod n,
      if (d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) *
        q) then ‖normalizedDFT n (intervalIndicator n mq) l‖ / (2 * min (ZMod.val k : ℝ) ((n : ℝ) -
          ZMod.val k)) else 0)) = (∑ k ∈ Finset.univ.filter (fun k : ZMod n =>
            k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)) ∪ Finset.univ.filter (fun k : ZMod n =>
              k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k), ∑ u : (ZMod d)ˣ, (∑ l : ZMod n,
                if (d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) *
                  q) then ‖normalizedDFT n (intervalIndicator n mq) l‖ / (2 *
                    min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) else 0)) := by
    have h2 : Finset.univ.filter (fun k : ZMod n =>
      k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)) ∪ Finset.univ.filter (fun k : ZMod n =>
        k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k) = Finset.univ.filter (fun k : ZMod n => k ≠ 0) := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro h
        by_cases hx : x = 0 <;> by_cases hd : (d : ℕ) ∣ ZMod.val x <;> simp_all
      · intro h
        by_cases hx : x = 0 <;> by_cases hd : (d : ℕ) ∣ ZMod.val x <;> simp_all
    rw [h2]
  have h3 : (∑ k ∈ Finset.univ.filter (fun k : ZMod n =>
    k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)) ∪ Finset.univ.filter (fun k : ZMod n =>
      k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k), ∑ u : (ZMod d)ˣ, (∑ l : ZMod n,
        if (d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) *
          q) then ‖normalizedDFT n (intervalIndicator n mq) l‖ / (2 *
            min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) else 0)) = (∑ k ∈
              Finset.univ.filter (fun k : ZMod n =>
                k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)), ∑ u : (ZMod d)ˣ, (∑ l : ZMod n,
                  if (d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) *
                    q) then ‖normalizedDFT n (intervalIndicator n mq) l‖ / (2 *
                      min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) else 0)) + (∑ k ∈
                        Finset.univ.filter (fun k : ZMod n =>
                          k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k), ∑ u : (ZMod d)ˣ, (∑ l : ZMod n,
                            if (d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) *
                              q) then ‖normalizedDFT n (intervalIndicator n mq) l‖ / (2 *
                                min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) else 0)) := by
    have h4 : Disjoint (Finset.univ.filter (fun k : ZMod n =>
      k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k))) (Finset.univ.filter (fun k : ZMod n =>
        k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k)) := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      simp only [Finset.mem_filter] at hx1 hx2
      have h5 : ¬((d : ℕ) ∣ ZMod.val x) := hx1.2.2
      have h6 : (d : ℕ) ∣ ZMod.val x := hx2.2.2
      exact h5 h6
    rw [Finset.sum_union h4]
  rw [h1, h3]



lemma k_sum_split_by_d_divisibility
    (n d : ℕ) [NeZero n] [NeZero d]
    (mq : ℕ) (q : ℤ) :
    ∑ k : ZMod n, ∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
             (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
        else 0) =
    (∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)),
      ∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
               (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
          else 0)) +
    (∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
      ∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
               (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
          else 0)) := by
  rw [sum_restrict_to_nonzero, split_nonzero_by_divisibility]

lemma factor_weight_from_double_sum
    (n d : ℕ) [NeZero n] [NeZero d]
    (mq : ℕ) (q : ℤ) (k : ZMod n) (hk : k ≠ 0) :
    (∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
             (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
        else 0)) =
    (∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖
        else 0)) /
    (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) := by
  rcases ne_or_eq k 0 with _ | hk'
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    split_ifs <;> simp
  · exact absurd hk' hk



lemma dvd_simplify_multiple_case
    (n d : ℕ) [NeZero n] [NeZero d]
    (k : ZMod n) (l : ZMod n) (u : (ZMod d)ˣ) (q : ℤ)
    (hdk : (d : ℕ) ∣ ZMod.val k)
    (hq_coprime_d : Int.gcd q (d : ℤ) = 1) :
    ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q)) ↔
    ((d : ℤ) ∣ ↑(ZMod.val l)) := by
  constructor
  · intro h
    have h₁ : (d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val) := by
      have h₂ : (d : ℤ) ∣ ↑(ZMod.val k) := by
        exact_mod_cast hdk
      have h₃ : (d : ℤ) ∣ ↑(ZMod.val k) * ↑(u : ZMod d).val := by
        exact dvd_mul_of_dvd_left h₂ _
      exact h₃
    have h₂ : (d : ℤ) ∣ ↑(ZMod.val l) * q := by
      have h₃ : (d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q) := h
      have h₄ : (d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val) := h₁
      have h₅ : (d : ℤ) ∣ (↑(ZMod.val l) * q) := by
        have h₆ : (d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q) -
          (↑(ZMod.val k) * ↑(u : ZMod d).val) := by
          exact dvd_sub h₃ h₄
        simpa [add_comm, add_left_comm, add_assoc] using h₆
      exact h₅
    have h₃ : (d : ℤ) ∣ ↑(ZMod.val l) := by
      have h₄ : IsCoprime (q : ℤ) (d : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        simp_all
      have h₅ : (d : ℤ) ∣ ↑(ZMod.val l) * q := h₂
      have h₆ : (d : ℤ) ∣ ↑(ZMod.val l) := by
        have h₇ : IsCoprime (q : ℤ) (d : ℤ) := h₄
        have h₈ : (d : ℤ) ∣ ↑(ZMod.val l) * q := h₅
        exact (h₇.symm.dvd_of_dvd_mul_right h₈)
      exact h₆
    exact h₃
  · intro h
    have h₁ : (d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val) := by
      have h₂ : (d : ℤ) ∣ ↑(ZMod.val k) := by
        exact_mod_cast hdk
      have h₃ : (d : ℤ) ∣ ↑(ZMod.val k) * ↑(u : ZMod d).val := by
        exact dvd_mul_of_dvd_left h₂ _
      exact h₃
    have h₂ : (d : ℤ) ∣ (↑(ZMod.val l) * q) := by
      have h₃ : (d : ℤ) ∣ ↑(ZMod.val l) := h
      have h₄ : (d : ℤ) ∣ ↑(ZMod.val l) * q := by
        exact dvd_mul_of_dvd_left h₃ _
      exact h₄
    have h₃ : (d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q) := by
      have h₄ : (d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val) := h₁
      have h₅ : (d : ℤ) ∣ (↑(ZMod.val l) * q) := h₂
      exact dvd_add h₄ h₅
    exact h₃


lemma mq_bounds (n : ℕ) (_hn : 2 ≤ n) (q : ℤ) (hq_pos : 1 ≤ q)
    (hq_bound : (q : ℝ) < (n : ℝ) / 2) :
    1 ≤ (2 * q - 1).toNat ∧ (2 * q - 1).toNat < n := by
  have h₂ : (2 * q - 1 : ℤ) < n := by
    have h₅ : (2 * q - 1 : ℤ) < n := by
      have h₆ : (2 * q - 1 : ℝ) < (n : ℝ) := by
        linarith
      have h₉ : (2 * q - 1 : ℤ) < (n : ℤ) := by
        exact_mod_cast h₆
      exact_mod_cast h₉
    exact h₅
  have h₃ : 1 ≤ (2 * q - 1).toNat := by omega
  have h₄ : (2 * q - 1).toNat < n := by omega
  exact ⟨h₃, h₄⟩



lemma symmetric_sum_le_one_plus_log (n d : ℕ) (hn : 2 ≤ n) (_hd_dvd : d ∣ n) (_hd_pos : 0 < d) :
    ∑ j ∈ Finset.Icc 1 (n / d - 1),
      (1 : ℝ) / (2 * min (j : ℝ) ((↑(n / d) : ℝ) - j)) ≤ 1 + Real.log n := by
  set N := n / d with hN_def
  by_cases hN_small : N ≤ 1
  · have : N - 1 = 0 := Nat.sub_eq_zero_of_le hN_small
    rw [this]
    simp
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
    linarith [Real.log_nonneg this]
  · push Not at hN_small
    have hN2 : 2 ≤ N := hN_small
    have h_log := symmetric_harmonic_sum_le_log N hN2
    have hN_le_n : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.div_le_self n d
    have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
    have h_log_mono : Real.log (N : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hN_pos hN_le_n
    linarith

lemma mul_lt_of_mem_Icc (n d : ℕ) (_hd_dvd : d ∣ n) (hd_pos : 0 < d)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (n / d - 1)) :
    j * d < n := by
  have h₁ : n / d ≥ 1 := by simp only [Finset.mem_Icc] at hj; omega
  have h₂ : j + 1 ≤ n / d := by simp only [Finset.mem_Icc] at hj; omega
  have h₃ : (j + 1) * d ≤ n := by
    have h₂_val := (Finset.mem_Icc.mp hj).2
    have := Nat.div_mul_le_self n d
    nlinarith
  have h₅ : j * d < n := by nlinarith
  exact h₅



lemma fwd_mem (n d : ℕ) [NeZero n] [NeZero d] (hd_dvd : d ∣ n) (hd_pos : 0 < d)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (n / d - 1)) :
    (↑(j * d) : ZMod n) ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k) := by
  have hjd_lt : j * d < n := mul_lt_of_mem_Icc n d hd_dvd hd_pos j hj
  have hj_bounds := Finset.mem_Icc.mp hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hjd_pos : 0 < j * d := Nat.mul_pos (by omega : 0 < j) hd_pos
    exact absurd h (Nat.not_dvd_of_pos_of_lt hjd_pos hjd_lt)
  · rw [ZMod.val_natCast_of_lt hjd_lt]
    exact dvd_mul_left d j


lemma bwd_mem (n d : ℕ) [NeZero n] [NeZero d] (hd_dvd : d ∣ n) (hd_pos : 0 < d)
    (k : ZMod n) (hk : k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k)) :
    ZMod.val k / d ∈ Finset.Icc 1 (n / d - 1) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  obtain ⟨hk_ne, hd_dvd_val⟩ := hk
  have hval_pos : 0 < ZMod.val k := Nat.pos_of_ne_zero ((ZMod.val_ne_zero k).mpr hk_ne)
  have hval_lt : ZMod.val k < n := ZMod.val_lt k
  rw [Finset.mem_Icc]
  constructor
  · exact Nat.div_pos (Nat.le_of_dvd hval_pos hd_dvd_val) hd_pos
  · have h1 : ZMod.val k / d < n / d := Nat.div_lt_div_of_lt_of_dvd hd_dvd hval_lt
    omega



lemma left_inv (n d : ℕ) [NeZero n] [NeZero d] (hd_dvd : d ∣ n) (hd_pos : 0 < d)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (n / d - 1)) :
    ZMod.val (↑(j * d) : ZMod n) / d = j := by
  have hjd : j * d < n := mul_lt_of_mem_Icc n d hd_dvd hd_pos j hj
  rw [ZMod.val_natCast_of_lt hjd, Nat.mul_div_cancel j hd_pos]



lemma right_inv (n d : ℕ) [NeZero n] [NeZero d] (_hd_dvd : d ∣ n) (_hd_pos : 0 < d)
    (k : ZMod n) (hk : k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k)) :
    (↑(ZMod.val k / d * d) : ZMod n) = k := by
  have hmem := (Finset.mem_filter.mp hk).2
  have hdvd : d ∣ ZMod.val k := hmem.2
  rw [Nat.div_mul_cancel hdvd, ZMod.natCast_zmod_val]



lemma div_lt_div_of_dvd (n d : ℕ) [NeZero n] [NeZero d] (hd_dvd : d ∣ n)
    (k : ZMod n) (_hd_dvd_val : d ∣ ZMod.val k) :
    ZMod.val k / d < n / d := by
  have h_val_lt_n : ZMod.val k < n := ZMod.val_lt k
  exact Nat.div_lt_div_of_lt_of_dvd hd_dvd h_val_lt_n



lemma min_factor_d_nat (n d : ℕ) [NeZero n] [NeZero d] (hd_dvd : d ∣ n) (k : ZMod n)
    (_hk_ne : k ≠ 0) (hd_dvd_val : d ∣ ZMod.val k) :
    min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) =
    (d : ℝ) * min (↑(ZMod.val k / d) : ℝ) ((↑(n / d) : ℝ) - ↑(ZMod.val k / d)) := by
  have hj_lt : ZMod.val k / d < n / d := div_lt_div_of_dvd n d hd_dvd k hd_dvd_val
  have hval_eq : ZMod.val k = ZMod.val k / d * d := (Nat.div_mul_cancel hd_dvd_val).symm
  have hn_eq : n = n / d * d := (Nat.div_mul_cancel hd_dvd).symm
  have hd_pos : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  set j := ZMod.val k / d
  set N := n / d
  have hval_cast : (ZMod.val k : ℝ) = (j : ℝ) * (d : ℝ) := by
    rw [← Nat.cast_mul, ← hval_eq]
  have hn_cast : (n : ℝ) = (N : ℝ) * (d : ℝ) := by
    rw [← Nat.cast_mul, ← hn_eq]
  rw [hval_cast, hn_cast, show (N : ℝ) * (d : ℝ) - (j : ℝ) * (d : ℝ) =
    ((N : ℝ) - (j : ℝ)) * (d : ℝ) from by ring]
  rw [← min_mul_of_nonneg _ _ hd_pos, mul_comm]



lemma div_factor_d (d M : ℝ) (hd : d ≠ 0) :
    (1 : ℝ) / (2 * (d * M)) = (1 / d) * (1 / (2 * M)) := by
  have h₁ : (1 : ℝ) / (2 * (d * M)) = (1 : ℝ) / (2 * d * M) := by
    ring_nf
  rw [h₁]
  by_cases h₂ : M = 0
  · simp_all
  · have h₃ : (1 : ℝ) / (2 * d * M) = (1 / d) * (1 / (2 * M)) := by
      have h₄ : 2 * d * M = 2 * M * d := by ring
      rw [h₄]
      field_simp [hd, h₂]
    rw [h₃]



lemma summand_eq_via_bwd (n d : ℕ) [NeZero n] [NeZero d] (hd_dvd : d ∣ n) (_hd_pos : 0 < d)
    (k : ZMod n) (hk : k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k)) :
    let N := n / d
    let j := ZMod.val k / d
    (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) =
    (1 / (d : ℝ)) * ((1 : ℝ) / (2 * min (j : ℝ) ((N : ℝ) - j))) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  obtain ⟨hk_ne, hd_dvd_val⟩ := hk
  intro N j
  rw [min_factor_d_nat n d hd_dvd k hk_ne hd_dvd_val]
  exact div_factor_d (d : ℝ) _ (Nat.cast_ne_zero.mpr (Nat.pos_of_ne_zero (NeZero.ne d)).ne')



lemma reindex_multiples_of_d (n d : ℕ) [NeZero n] [NeZero d]
    (hd_dvd : d ∣ n) (hd_pos : 0 < d) :
    let N := n / d
    ∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
      (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) =
    (1 / (d : ℝ)) * ∑ j ∈ Finset.Icc 1 (N - 1),
      (1 : ℝ) / (2 * min (j : ℝ) ((N : ℝ) - j)) := by
  simp only
  rw [Finset.mul_sum]
  apply Finset.sum_nbij' (fun k => ZMod.val k / d) (fun j => (↑(j * d) : ZMod n))
  · exact fun k hk => bwd_mem n d hd_dvd hd_pos k hk
  · exact fun j hj => fwd_mem n d hd_dvd hd_pos j hj
  · exact fun k hk => right_inv n d hd_dvd hd_pos k hk
  · exact fun j hj => left_inv n d hd_dvd hd_pos j hj
  · intro k hk
    exact summand_eq_via_bwd n d hd_dvd hd_pos k hk



lemma weight_sum_multiples_of_d_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd_dvd : d ∣ n) (hd_pos : 0 < d) :
    ∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
      (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) ≤
    (1 + Real.log (n : ℝ)) / d := by
  have hd_cast : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
  rw [reindex_multiples_of_d n d hd_dvd hd_pos]
  have h := symmetric_sum_le_one_plus_log n d hn hd_dvd hd_pos
  calc 1 / (d : ℝ) * ∑ j ∈ Finset.Icc 1 (n / d - 1),
        (1 : ℝ) / (2 * min (j : ℝ) ((↑(n / d) : ℝ) - j))
      ≤ 1 / (d : ℝ) * (1 + Real.log n) := by
        apply mul_le_mul_of_nonneg_left h
        positivity
    _ = (1 + Real.log (n : ℝ)) / d := by ring


lemma d_dvd_n (n : ℕ) (_hn : 2 ≤ n) :
    largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) ∣ n := by
  exact Nat.ordProj_dvd n (largestPrimeFactor n)



lemma coprimality_q_d (n : ℕ) (_hn : 2 ≤ n) (q : ℤ)
    (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (d : ℕ) (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) :
    Int.gcd q (d : ℤ) = 1 := by
  rw [hd, Nat.cast_pow]
  exact Int.isCoprime_iff_gcd_eq_one.mp (Int.isCoprime_iff_gcd_eq_one.mpr hq_coprime |>.pow_right)


lemma simplify_u_sum_when_d_dvd_k
    (n d : ℕ) [NeZero n] [NeZero d]
    (mq : ℕ) (q : ℤ) (k : ZMod n)
    (hdk : (d : ℕ) ∣ ZMod.val k)
    (hq_coprime_d : Int.gcd q (d : ℤ) = 1) :
    (∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖
        else 0)) =
    ↑(Fintype.card (ZMod d)ˣ) *
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ ↑(ZMod.val l))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖
        else 0) := by
  have h : ∀ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖
        else 0) =
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ ↑(ZMod.val l))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖
        else 0) := by
    intro u
    apply Finset.sum_congr rfl
    intro l _
    have h := dvd_simplify_multiple_case n d k l u q hdk hq_coprime_d
    simp only [h]
  simp_rw [h]
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]


lemma restricted_fourier_mass_le
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (mq : ℕ) (hmq1 : 1 ≤ mq) (hmq2 : mq < n) :
    (∑ l : ZMod n,
      if ((d : ℤ) ∣ ↑(ZMod.val l))
      then ‖normalizedDFT n (intervalIndicator n mq) l‖
      else 0) ≤
    1 + Real.log (n : ℝ) := by
  calc (∑ l : ZMod n,
        if ((d : ℤ) ∣ ↑(ZMod.val l))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖
        else 0)
      ≤ ∑ l : ZMod n, ‖normalizedDFT n (intervalIndicator n mq) l‖ := by
        apply Finset.sum_le_sum
        intro l _
        split_ifs with h
        · exact le_refl _
        · exact norm_nonneg _
    _ ≤ 1 + Real.log (n : ℝ) :=
        fourier_intervalIndicator_l1_bound n hn mq hmq1 hmq2


lemma triple_sum_eq_card_times_product
    (n d : ℕ) [NeZero n] [NeZero d] (_hn : 2 ≤ n)
    (mq : ℕ) (q : ℤ)
    (hq_coprime_d : Int.gcd q (d : ℤ) = 1)
    (_hd_dvd : d ∣ n) :
    (∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
      ∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
               (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
          else 0)) ≤
    ↑(Fintype.card (ZMod d)ˣ) *
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ ↑(ZMod.val l))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖
        else 0) *
      (∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
        (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))) := by
  set A := (∑ l : ZMod n,
    if ((d : ℤ) ∣ ↑(ZMod.val l))
    then ‖normalizedDFT n (intervalIndicator n mq) l‖
    else 0) with hA_def
  set C := (Fintype.card (ZMod d)ˣ : ℝ) with hC_def
  have hk_eq : ∀ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
      (∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
               (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
          else 0)) =
      C * A / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [factor_weight_from_double_sum n d mq q k hk.1,
        simplify_u_sum_when_d_dvd_k n d mq q k hk.2 hq_coprime_d]
  have lhs_eq : (∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
      (∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
               (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
          else 0))) =
      C * A * ∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
        1 / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) := by
    rw [Finset.sum_congr rfl hk_eq]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.mul_sum]
    congr 1
    simp
  linarith [le_refl (C * A * ∑ k ∈ Finset.univ.filter (fun k : ZMod n =>
    k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
    1 / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)))]


lemma triple_sum_bound_via_factoring
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (_hq_pos : 1 ≤ q) (_hq_bound : (q : ℝ) < (n : ℝ) / 2)
    (mq : ℕ) (_hmq : mq = (2 * q - 1).toNat)
    (hmq1 : 1 ≤ mq) (hmq2 : mq < n) :
    (∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
      ∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
               (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
          else 0)) ≤
    ↑(Fintype.card (ZMod d)ˣ) * ((1 + Real.log ↑n) ^ 2 / ↑d) := by
  have hq_coprime_d : Int.gcd q (d : ℤ) = 1 := coprimality_q_d n hn q hq_coprime d hd
  have hd_dvd : d ∣ n := hd ▸ d_dvd_n n hn
  have hd_pos : 0 < d := hd ▸ d_pos n hn
  have h1 := triple_sum_eq_card_times_product n d hn mq q hq_coprime_d hd_dvd
  have h2 := restricted_fourier_mass_le n d hn mq hmq1 hmq2
  have h3 := weight_sum_multiples_of_d_bound n d hn hd_dvd hd_pos
  calc (∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
      ∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
               (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
          else 0))
      ≤ ↑(Fintype.card (ZMod d)ˣ) *
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ ↑(ZMod.val l))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖
          else 0) *
        (∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
          (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))) := h1
    _ ≤ ↑(Fintype.card (ZMod d)ˣ) * (1 + Real.log ↑n) * ((1 + Real.log ↑n) / ↑d) := by
        have hA := h2
        have hB := h3
        have hcard_nonneg : (0 : ℝ) ≤ ↑(Fintype.card (ZMod d)ˣ) := Nat.cast_nonneg _
        have hA_nonneg : (0 : ℝ) ≤ ∑ l : ZMod n,
          if ((d : ℤ) ∣ ↑(ZMod.val l))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖
          else 0 := Finset.sum_nonneg (fun l _ => by split_ifs <;> positivity)
        have hB_nonneg : (0 : ℝ) ≤ ∑ k ∈ Finset.univ.filter (fun k : ZMod n =>
          k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
          (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) :=
          Finset.sum_nonneg (fun k hk => by
            have hkne : k ≠ 0 := (Finset.mem_filter.mp hk).2.1
            exact div_nonneg zero_le_one (mul_nonneg (by norm_num) (le_of_lt (min_val_pos n k
              hkne))))
        nlinarith [mul_le_mul_of_nonneg_left hA (mul_nonneg hcard_nonneg hB_nonneg),
                   mul_le_mul_of_nonneg_left hB (mul_nonneg hcard_nonneg (le_trans hA_nonneg hA))]
    _ = ↑(Fintype.card (ZMod d)ˣ) * ((1 + Real.log ↑n) ^ 2 / ↑d) := by ring



lemma multiple_d_weighted_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (hq_pos : 1 ≤ q) (hq_bound : (q : ℝ) < (n : ℝ) / 2)
    (mq : ℕ) (hmq : mq = (2 * q - 1).toNat) :
    (∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ (d : ℕ) ∣ ZMod.val k),
      ∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
               (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
          else 0)) ≤
    ↑(Fintype.card (ZMod d)ˣ) * ((1 + Real.log ↑n) ^ 2 / ↑d) := by
  have hmq_valid : 1 ≤ mq ∧ mq < n := by
    rw [hmq]
    exact mq_bounds n hn q hq_pos hq_bound
  exact triple_sum_bound_via_factoring n d hn hd q hq_coprime hq_pos hq_bound mq hmq
    hmq_valid.1 hmq_valid.2



lemma weight_nonneg (n : ℕ) [NeZero n] (k : ZMod n) (hk : k ≠ 0) :
    (0 : ℝ) ≤ 2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) := by
  have h := min_val_pos n k hk
  linarith


lemma weight_sum_le_log
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n) :
    ∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)),
      (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) ≤
    1 + Real.log ↑n := by
  have h_subset : Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)) ⊆
      Finset.univ.filter (fun k : ZMod n => k ≠ 0) := by
    intro k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.left
  have h_nonneg : ∀ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0),
      k ∉ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)) →
      0 ≤ (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) := by
    intro k hk _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact div_nonneg zero_le_one (mul_nonneg (by norm_num) (le_of_lt (min_val_pos n k hk)))
  calc ∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)),
        (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
      ≤ ∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0),
        (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) :=
        Finset.sum_le_sum_of_subset_of_nonneg h_subset h_nonneg
    _ = ∑ t ∈ Finset.Icc 1 (n - 1),
        (1 : ℝ) / (2 * min (t : ℝ) ((n : ℝ) - t)) :=
        sum_nonzero_reindex n hn
    _ ≤ Real.log n := symmetric_harmonic_sum_le_log n hn
    _ ≤ 1 + Real.log n := le_add_of_nonneg_left (by norm_num)


lemma const_bound_nonneg (n d : ℕ) [NeZero n] [NeZero d] (_hn : 2 ≤ n) :
    (0 : ℝ) ≤ ↑(Fintype.card (ZMod d)ˣ) * (5 * (1 + Real.log ↑n) / ↑d) := by
  positivity




lemma sum_eq_two_mul_half_sum (M : ℕ) :
    (∑ t ∈ Finset.Icc 1 (M - 1),
      1 / min ((t : ℝ)) ((M : ℝ) - (t : ℝ))) =
    2 * (∑ t ∈ Finset.Icc 1 (M - 1),
      (1 : ℝ) / (2 * min (t : ℝ) ((M : ℝ) - t))) := by
  have h1 : (∑ t ∈ Finset.Icc 1 (M - 1),
    1 / min ((t : ℝ)) ((M : ℝ) - (t : ℝ))) = 2 * (∑ t ∈ Finset.Icc 1 (M - 1),
      (1 : ℝ) / (2 * min (t : ℝ) ((M : ℝ) - t))) := by
    have h2 : ∀ (t : ℕ),
      t ∈ Finset.Icc 1 (M - 1) → 1 / (min ((t : ℝ)) ((M : ℝ) - (t : ℝ)) : ℝ) = 2 * ((1 : ℝ) / (2 *
        min (t : ℝ) ((M : ℝ) - t))) := by
      intro t ht
      have h3 : (min ((t : ℝ)) ((M : ℝ) - (t : ℝ)) : ℝ) > 0 := by
        have h4 : (t : ℕ) ∈ Finset.Icc 1 (M - 1) := ht
        have h5 : 1 ≤ t := by
          simp [Finset.mem_Icc] at h4
          linarith
        have h6 : t ≤ M - 1 := by
          simp [Finset.mem_Icc] at h4
          linarith
        have h8 : (t : ℝ) < M := by
          have h10 : (M : ℕ) ≥ 1 := by
            by_contra h
            have h11 : M = 0 := by omega
            simp_all
          have h11 : (t : ℕ) < M := by
            omega
          exact_mod_cast h11
        have h10 : (min ((t : ℝ)) ((M : ℝ) - (t : ℝ)) : ℝ) > 0 := by
          have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h5
          exact lt_min (by linarith) (by linarith)
        exact h10
      have h4 : 1 / (min ((t : ℝ)) ((M : ℝ) - (t : ℝ)) : ℝ) = 2 * ((1 : ℝ) / (2 *
        min (t : ℝ) ((M : ℝ) - t))) := by
        have h5 : (min ((t : ℝ)) ((M : ℝ) - (t : ℝ)) : ℝ) = min (t : ℝ) ((M : ℝ) - t) := by
          simp
        rw [h5]
        field_simp
      exact h4
    calc
      (∑ t ∈ Finset.Icc 1 (M - 1), 1 / min ((t : ℝ)) ((M : ℝ) - (t : ℝ))) =
          ∑ t ∈ Finset.Icc 1 (M - 1), (2 * ((1 : ℝ) / (2 * min (t : ℝ) ((M : ℝ) - t)))) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [h2 t ht]
      _ = 2 * (∑ t ∈ Finset.Icc 1 (M - 1), (1 : ℝ) / (2 * min (t : ℝ) ((M : ℝ) - t))) := by
        rw [Finset.mul_sum]
  exact h1



lemma harmonic_min_sum_le_two_log (M n : ℕ) (hM : 2 ≤ M) (hMn : M ≤ n) :
    (∑ t ∈ Finset.Icc 1 (M - 1),
      1 / min ((t : ℝ)) ((M : ℝ) - (t : ℝ))) ≤
    2 * (1 + Real.log ↑n) := by
  rw [sum_eq_two_mul_half_sum M]
  have h1 : ∑ t ∈ Finset.Icc 1 (M - 1),
      (1 : ℝ) / (2 * min (t : ℝ) ((M : ℝ) - t)) ≤ Real.log M :=
    symmetric_harmonic_sum_le_log M hM
  have h2 : Real.log (M : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hMn)
  linarith



lemma d_ge_P (n : ℕ) (hn : 2 ≤ n) :
    largestPrimeFactor n ≤ largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) := by
  have hP := largestPrimeFactor_pos n hn
  have hα := largest_prime_factor_multiplicity_pos n hn
  exact le_self_pow hP (by omega)



lemma one_plus_log_nonneg (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ 1 + Real.log (n : ℝ) := by
  have h₁ : 0 ≤ Real.log (n : ℝ) := by
    have h₂ : (1 : ℝ) ≤ (n : ℝ) := by
      norm_cast
      linarith
    exact Real.log_nonneg h₂
  linarith



lemma key_val_eq (d : ℕ) [NeZero d] (k_val : ℕ) (hcop : Nat.Coprime k_val d)
    (u : (ZMod d)ˣ) :
    let k_unit := ZMod.unitOfCoprime k_val hcop
    ((k_unit * u : (ZMod d)ˣ) : ZMod d).val = (k_val * (↑u : ZMod d).val) % d := by
  intro k_unit
  have h1 : ((k_unit * u : (ZMod d)ˣ) : ZMod d).val = ((↑k_unit : ZMod d) * (↑u : ZMod d)).val :=
    by rfl
  have h2 : ((↑k_unit : ZMod d) * (↑u : ZMod d)).val = (↑k_unit : ZMod d).val *
    (↑u : ZMod d).val % d := by exact ZMod.val_mul _ _
  have h3 : (↑k_unit : ZMod d) = (↑k_val : ZMod d) := by rfl
  have h5 : (↑k_val : ZMod d).val = k_val % d := by simp
  have h7 : ((k_unit * u : (ZMod d)ˣ) : ZMod d).val = (k_val % d * (↑u : ZMod d).val) % d :=
    by simp_all
  have h8 : (k_val * (↑u : ZMod d).val) % d = (k_val % d * (↑u : ZMod d).val) % d := by simp
  have h9 : ((k_unit * u : (ZMod d)ˣ) : ZMod d).val = (k_val * (↑u : ZMod d).val) % d :=
    by nlinarith
  assumption



lemma coprime_case_sum_eq
    (d : ℕ) [NeZero d] (k_val : ℕ) (hcop : Nat.Coprime k_val d) :
    (∑ u : (ZMod d)ˣ,
      1 / min ((k_val * (u : ZMod d).val % d : ℕ) : ℝ)
              (((d : ℕ) : ℝ) - (k_val * (u : ZMod d).val % d : ℕ))) =
    (∑ u : (ZMod d)ˣ,
      1 / min (((u : ZMod d).val : ℕ) : ℝ)
              (((d : ℕ) : ℝ) - ((u : ZMod d).val : ℕ))) := by
  set k_unit := ZMod.unitOfCoprime k_val hcop
  have lhs_rw : ∀ u : (ZMod d)ˣ,
      (k_val * (u : ZMod d).val % d : ℕ) = ((k_unit * u : (ZMod d)ˣ) : ZMod d).val := by
    intro u; exact (key_val_eq d k_val hcop u).symm
  simp_rw [lhs_rw]
  exact Fintype.sum_bijective (fun u => k_unit * u)
    (Equiv.mulLeft k_unit).bijective _ _
    (fun u => by simp)



lemma units_val_injective (d : ℕ) [NeZero d] :
    Function.Injective (fun u : (ZMod d)ˣ => (u : ZMod d).val) :=
  (ZMod.val_injective d).comp Units.val_injective



lemma unit_val_mem_Icc (d : ℕ) [NeZero d] (hd : 2 ≤ d) (u : (ZMod d)ˣ) :
    (u : ZMod d).val ∈ Finset.Icc 1 (d - 1) := by
  have h_val_lt_d : (u : ZMod d).val < d := ZMod.val_lt _
  have h_val_coprime_d : Nat.Coprime (u : ZMod d).val d := by exact ZMod.val_coe_unit_coprime u
  have h_val_pos : 1 ≤ (u : ZMod d).val :=
    by exact Nat.pos_of_ne_zero (fun h => by simp [h, Nat.Coprime] at h_val_coprime_d; omega)
  have h_val_le_d_sub_one : (u : ZMod d).val ≤ d - 1 := by omega
  have h_main : (u : ZMod d).val ∈ Finset.Icc 1 (d - 1) := by simp_all
  exact h_main



lemma units_sum_summand_nonneg (d : ℕ) (t : ℕ) (ht : t ∈ Finset.Icc 1 (d - 1)) :
    (0 : ℝ) ≤ 1 / min ((t : ℝ)) (((d : ℕ) : ℝ) - (t : ℝ)) := by
  have h₁ : 1 ≤ t := by
    simp only [Finset.mem_Icc] at ht
    exact ht.1
  have h₂ : t ≤ d - 1 := by
    simp only [Finset.mem_Icc] at ht
    exact ht.2
  have h₄ : (d : ℕ) ≥ t + 1 := by
    have h₄₂ : t + 1 ≤ d := by
      have h₄₄ : t + 1 ≤ d := by
        have h₄₅ : d ≥ t + 1 := by
          by_cases h : d = 0
          · simp_all
          · have h₄₆ : d - 1 + 1 = d := by
              have h₄₇ : d ≥ 1 := by
                by_contra h₄₈
                simp_all
              omega
            omega
        omega
      omega
    omega
  have h₅ : ((d : ℕ) : ℝ) - (t : ℝ) > 0 := by
    have h₅₁ : (d : ℝ) > (t : ℝ) := by
      have h₅₂ : (d : ℕ) ≥ t + 1 := h₄
      have h₅₃ : (d : ℝ) ≥ (t + 1 : ℝ) := by
        exact_mod_cast h₅₂
      linarith
    linarith
  have h₆ : (0 : ℝ) < min ((t : ℝ)) (((d : ℕ) : ℝ) - (t : ℝ)) := by
    apply lt_min
    · exact_mod_cast by linarith
    · exact h₅
  have h₇ : (0 : ℝ) ≤ 1 / min ((t : ℝ)) (((d : ℕ) : ℝ) - (t : ℝ)) := by
    have h₇₁ : (0 : ℝ) < min ((t : ℝ)) (((d : ℕ) : ℝ) - (t : ℝ)) := h₆
    exact div_nonneg (by norm_num) (le_of_lt h₇₁)
  exact h₇



lemma units_sum_le_Icc_sum
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∑ u : (ZMod d)ˣ,
      1 / min (((u : ZMod d).val : ℕ) : ℝ)
              (((d : ℕ) : ℝ) - ((u : ZMod d).val : ℕ))) ≤
    (∑ t ∈ Finset.Icc 1 (d - 1),
      1 / min ((t : ℝ)) (((d : ℕ) : ℝ) - (t : ℝ))) := by
  rw [show (∑ u : (ZMod d)ˣ,
      1 / min (((u : ZMod d).val : ℕ) : ℝ) (((d : ℕ) : ℝ) - ((u : ZMod d).val : ℕ))) =
    ∑ t ∈ Finset.univ.image (fun u : (ZMod d)ˣ => (u : ZMod d).val),
      1 / min ((t : ℝ)) (((d : ℕ) : ℝ) - (t : ℝ)) from by
    rw [Finset.sum_image (fun a _ b _ h => units_val_injective d h)]]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun t ht => by
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
      obtain ⟨u, hu⟩ := ht
      rw [← hu]
      exact unit_val_mem_Icc d hd u)
    (fun t ht _ => units_sum_summand_nonneg d t ht)



lemma nat_mul_mod_right (a b n : ℕ) : a * b % n = a * (b % n) % n := by
  simp


lemma kval_mul_unit_mod_eq_pv_mul
    (d : ℕ) [NeZero d] (p : ℕ) (_hp : Nat.Prime p) (α : ℕ) (_hα : 1 ≤ α)
    (hd_eq : d = p ^ α)
    (k_val : ℕ) (_hk_nd : ¬((d : ℕ) ∣ k_val)) (_hk_dvd_p : p ∣ k_val)
    (v : ℕ) (_hv_pos : 1 ≤ v) (hv_lt : v < α)
    (hv_val : p ^ v ∣ k_val) (_hv_max : ¬(p ^ (v + 1) ∣ k_val))
    [NeZero (p ^ (α - v))]
    (u : (ZMod d)ˣ) :
    k_val * (u : ZMod d).val % d =
      p ^ v * ((k_val / p ^ v) * ((u : ZMod d).val % p ^ (α - v)) % p ^ (α - v)) := by
  have hd_split : d = p ^ v * p ^ (α - v) := by
    rw [hd_eq, ← pow_add, Nat.add_sub_cancel' hv_lt.le]
  set u_val := (u : ZMod d).val with hu_val_def
  have hk_split : k_val = p ^ v * (k_val / p ^ v) := by
    rw [mul_comm]; exact (Nat.div_mul_cancel hv_val).symm
  calc k_val * u_val % d
      = p ^ v * (k_val / p ^ v) * u_val % (p ^ v * p ^ (α - v)) := by
          rw [← hk_split, ← hd_split]
    _ = p ^ v * ((k_val / p ^ v) * u_val) % (p ^ v * p ^ (α - v)) := by
          ring_nf
    _ = p ^ v * ((k_val / p ^ v) * u_val % p ^ (α - v)) := by
          rw [Nat.mul_mod_mul_left]
    _ = p ^ v * ((k_val / p ^ v) * (u_val % p ^ (α - v)) % p ^ (α - v)) := by
          rw [nat_mul_mod_right]



lemma not_p_dvd_div_pow_1
    (p : ℕ) (_hp : Nat.Prime p)
    (k_val v : ℕ)
    (hv_val : p ^ v ∣ k_val) (hv_max : ¬(p ^ (v + 1) ∣ k_val)) :
    ¬(p ∣ k_val / p ^ v) := by
  intro h_dvd
  have h₁ : p ^ v * (k_val / p ^ v) = k_val := by
    apply Nat.mul_div_cancel'
    exact hv_val
  have h₂ : p ^ (v + 1) ∣ k_val := by
    have h₃ : p ∣ k_val / p ^ v := h_dvd
    have h₄ : ∃ m, k_val / p ^ v = p * m := by
      obtain ⟨m, hm⟩ := h₃
      exact ⟨m, by linarith⟩
    obtain ⟨m, hm⟩ := h₄
    have h₅ : k_val = p ^ v * (p * m) := by
      calc
        k_val = p ^ v * (k_val / p ^ v) := by rw [h₁]
        _ = p ^ v * (p * m) := by rw [hm]
    have h₆ : k_val = p ^ (v + 1) * m := by
      calc
        k_val = p ^ v * (p * m) := h₅
        _ = (p ^ v * p) * m := by ring
        _ = p ^ (v + 1) * m := by
          simp [pow_succ, mul_assoc]
    have h₇ : p ^ (v + 1) ∣ k_val := by
      use m
    exact h₇
  exact hv_max h₂



lemma dvd_of_dvd_mod_of_dvd (p a m : ℕ) (hpm : p ∣ m) (hpr : p ∣ a % m) : p ∣ a := by
  have h₁ : p ∣ m := hpm
  have h₂ : p ∣ a % m := hpr
  have h₃ : p ∣ a := by
    have h₄ : a % m + m * (a / m) = a := by
      have h₅ := Nat.mod_add_div a m
      linarith
    have h₅ : p ∣ m * (a / m) := dvd_mul_of_dvd_left h₁ (a / m)
    have h₆ : p ∣ a % m + m * (a / m) := dvd_add h₂ h₅
    have h₇ : p ∣ a := by
      rw [← h₄]
      exact h₆
    exact h₇
  exact h₃



lemma not_p_dvd_unit_val_mod
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (hα : 1 ≤ α)
    (v : ℕ) (hv_lt : v < α)
    [NeZero (p ^ α)]
    (u : (ZMod (p ^ α))ˣ) :
    ¬(p ∣ (u : ZMod (p ^ α)).val % p ^ (α - v)) := by
  have hcop : (u : ZMod (p ^ α)).val.Coprime (p ^ α) := ZMod.val_coe_unit_coprime u
  have hcop_p : p.Coprime (u : ZMod (p ^ α)).val :=
    (Nat.Coprime.of_dvd_right (dvd_pow_self p (by omega : α ≠ 0)) hcop).symm
  have hndvd : ¬ p ∣ (u : ZMod (p ^ α)).val :=
    (hp.coprime_iff_not_dvd.mp hcop_p)
  have hpdvd : p ∣ p ^ (α - v) := dvd_pow_self p (by omega : α - v ≠ 0)
  intro h
  exact hndvd (dvd_of_dvd_mod_of_dvd p (u : ZMod (p ^ α)).val (p ^ (α - v)) hpdvd h)



lemma mul_not_dvd_of_not_dvd
    (p a b : ℕ) (hp : Nat.Prime p)
    (ha : ¬(p ∣ a)) (hb : ¬(p ∣ b)) :
    ¬(p ∣ a * b) := by
  have h : ¬(p ∣ a * b) := by
    intro h₁
    have h₂ : p ∣ a * b := h₁
    have h₃ : p ∣ a * b := h₂
    have h₄ : p ∣ a ∨ p ∣ b := by
      have h₅ : p ∣ a * b := h₃
      exact hp.dvd_mul.mp h₅
    cases h₄ with
    | inl h₄ =>
      exact ha h₄
    | inr h₄ =>
      exact hb h₄
  exact h



lemma mod_ne_zero_of_not_dvd_prime
    (p : ℕ) (_hp : Nat.Prime p) (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : ¬(p ∣ n)) :
    n % p ^ k ≠ 0 := by
  have h₁ : n % p ^ k ≠ 0 := by
    intro h
    have h₂ : p ^ k ∣ n := by
      have h₃ : p ^ k ∣ n := Nat.dvd_of_mod_eq_zero h
      exact h₃
    have h₃ : p ∣ n := by
      have h₄ : p ∣ p ^ k := by
        exact dvd_pow_self p (by omega)
      exact dvd_trans h₄ h₂
    contradiction
  exact h₁



lemma reduced_product_mod_ne_zero
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (hα : 1 ≤ α)
    (k_val : ℕ)
    (v : ℕ) (hv_pos : 1 ≤ v) (hv_lt : v < α)
    (hv_val : p ^ v ∣ k_val) (hv_max : ¬(p ^ (v + 1) ∣ k_val))
    [NeZero (p ^ α)] [NeZero (p ^ (α - v))]
    (u : (ZMod (p ^ α))ˣ) :
    (k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α - v)) % p ^ (α - v) ≠ 0 := by
  have _ := hv_pos
  have h1 : ¬(p ∣ k_val / p ^ v) := not_p_dvd_div_pow_1 p hp k_val v hv_val hv_max
  have h2 : ¬(p ∣ (u : ZMod (p ^ α)).val % p ^ (α - v)) :=
    not_p_dvd_unit_val_mod p hp α hα v hv_lt u
  have h3 : ¬(p ∣ (k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α - v))) :=
    mul_not_dvd_of_not_dvd p _ _ hp h1 h2
  exact mod_ne_zero_of_not_dvd_prime p hp (α - v) (by omega) _ h3



lemma min_pv_factor
    (p : ℕ) (v M x : ℕ)
    (_hx_pos : 0 < x) (_hx_lt : x < M) :
    min ((p ^ v * x : ℕ) : ℝ) (((p ^ v * M : ℕ) : ℝ) - ((p ^ v * x : ℕ) : ℝ))
    = ((p ^ v : ℕ) : ℝ) * min ((x : ℕ) : ℝ) (((M : ℕ) : ℝ) - ((x : ℕ) : ℝ)) := by
  have h_sub_mul : ((p ^ v * M : ℕ) : ℝ) - ((p ^ v * x : ℕ) : ℝ) = ((p ^ v : ℕ) : ℝ) *
    (((M : ℕ) : ℝ) - ((x : ℕ) : ℝ)) := by push_cast; ring
  have h_min_mul : ∀ (a b c : ℝ), 0 ≤ a → min (a * b) (a * c) = a * min b c :=
    by exact fun a b c ha => (mul_min_of_nonneg b c ha).symm
  have h_main : min ((p ^ v * x : ℕ) : ℝ) (((p ^ v * M : ℕ) : ℝ) - ((p ^ v * x : ℕ) : ℝ)) = ((p ^
    v : ℕ) : ℝ) * min ((x : ℕ) : ℝ) (((M : ℕ) : ℝ) - ((x : ℕ) : ℝ)) := by simp_all
  assumption



lemma fiber_element_lt
    (p : ℕ) (hp : Nat.Prime p) (α v : ℕ) (hv_lt : v < α)
    (s : ℕ) (hs_lt : s < p ^ (α - v))
    (j : ℕ) (hj : j < p ^ v) :
    s + j * p ^ (α - v) < p ^ α := by
  have h₁ : α - v + v = α := by
    have h₂ : v ≤ α := by linarith
    have h₃ : α - v + v = α := by
      rw [Nat.sub_add_cancel h₂]
    exact h₃
  have h₂ : p ^ α = p ^ (α - v) * p ^ v := by
    calc
      p ^ α = p ^ (α - v + v) := by rw [h₁]
      _ = p ^ (α - v) * p ^ v := by rw [pow_add]
      _ = p ^ (α - v) * p ^ v := by rfl
  have h₃ : s + j * p ^ (α - v) < p ^ (α - v) * p ^ v := by
    have h₆ : p ^ (α - v) > 0 := pow_pos (Nat.Prime.pos hp) (α - v)
    have h₇ : p ^ v > 0 := pow_pos (Nat.Prime.pos hp) v
    have h₈ : s + j * p ^ (α - v) ≤ (p ^ (α - v) - 1) + (p ^ v - 1) * p ^ (α - v) := by
      have h₉ : s ≤ p ^ (α - v) - 1 := by
        have h₁₁ : s ≤ p ^ (α - v) - 1 := by
          omega
        exact h₁₁
      have h₁₀ : j ≤ p ^ v - 1 := by
        have h₁₂ : j ≤ p ^ v - 1 := by
          omega
        exact h₁₂
      have h₁₁ : j * p ^ (α - v) ≤ (p ^ v - 1) * p ^ (α - v) := by
        have h₁₂ : j ≤ p ^ v - 1 := h₁₀
        have h₁₄ : j * p ^ (α - v) ≤ (p ^ v - 1) * p ^ (α - v) := by
          exact Nat.mul_le_mul_right (p ^ (α - v)) h₁₂
        exact h₁₄
      have h₁₂ : s + j * p ^ (α - v) ≤ (p ^ (α - v) - 1) + (p ^ v - 1) * p ^ (α - v) := by
        calc
          s + j * p ^ (α - v) ≤ (p ^ (α - v) - 1) + j * p ^ (α - v) := by
            omega
          _ ≤ (p ^ (α - v) - 1) + (p ^ v - 1) * p ^ (α - v) := by
            omega
      exact h₁₂
    have h₉ : (p ^ (α - v) - 1) + (p ^ v - 1) * p ^ (α - v) + 1 = p ^ (α - v) * p ^ v := by
      have h₁₂ : (p ^ (α - v) - 1) + (p ^ v - 1) * p ^ (α - v) + 1 = p ^ (α - v) * p ^ v := by
        have h₁₃ : p ^ v - 1 + 1 = p ^ v := by
          have h₁₅ : p ^ v - 1 + 1 = p ^ v := by
            omega
          exact h₁₅
        have h₁₄ : (p ^ v - 1) * p ^ (α - v) + p ^ (α - v) = p ^ (α - v) * p ^ v := by
          calc
            (p ^ v - 1) * p ^ (α - v) + p ^ (α - v) = (p ^ v - 1 + 1) * p ^ (α - v) := by
              ring_nf
            _ = p ^ v * p ^ (α - v) := by
              have h₁₅ : p ^ v - 1 + 1 = p ^ v := by
                omega
              rw [h₁₅]
            _ = p ^ (α - v) * p ^ v := by
              ring_nf
        calc
          (p ^ (α - v) - 1) + (p ^ v - 1) * p ^ (α - v) + 1 = (p ^ (α - v) - 1 + 1) + (p ^ v - 1) *
            p ^ (α - v) := by
            ring_nf
          _ = p ^ (α - v) + (p ^ v - 1) * p ^ (α - v) := by
            have h₁₅ : p ^ (α - v) - 1 + 1 = p ^ (α - v) := by
              omega
            rw [h₁₅]
          _ = (p ^ v - 1) * p ^ (α - v) + p ^ (α - v) := by
            ring_nf
          _ = p ^ (α - v) * p ^ v := by
            rw [h₁₄]
      exact h₁₂
    have h₁₀ : s + j * p ^ (α - v) < p ^ (α - v) * p ^ v := by
      have h₁₃ : s + j * p ^ (α - v) < p ^ (α - v) * p ^ v := by
        omega
      exact h₁₃
    exact h₁₀
  calc
    s + j * p ^ (α - v) < p ^ (α - v) * p ^ v := h₃
    _ = p ^ α := by
      rw [h₂]



lemma not_p_dvd_fiber_element
    (p : ℕ) (hp : Nat.Prime p) (α v : ℕ) (hv_lt : v < α)
    (s : ℕ) (hs_cop : Nat.Coprime s p)
    (j : ℕ) :
    ¬ p ∣ (s + j * p ^ (α - v)) := by
  have h_main : (s + j * p ^ (α - v)) % p = s % p := by
    have h₁ : (s + j * p ^ (α - v)) % p = (s % p + (j * p ^ (α - v)) % p) % p := by
      simp [Nat.add_mod]
    rw [h₁]
    have h₂ : (j * p ^ (α - v)) % p = 0 := by
      have h₃ : p ∣ j * p ^ (α - v) := by
        have h₄ : p ∣ p ^ (α - v) := by
          exact dvd_pow_self p (by
            have h₅ : α - v ≥ 1 := by
              have h₇ : α - v > 0 := by omega
              omega
            omega)
        exact dvd_mul_of_dvd_right h₄ j
      exact Nat.mod_eq_zero_of_dvd h₃
    rw [h₂]
    simp
  have h₂ : s % p ≠ 0 := by
    intro h₃
    have h₄ : p ∣ s := by
      have h₅ : s % p = 0 := h₃
      exact Nat.dvd_of_mod_eq_zero h₅
    have h₅ : p ∣ s := h₄
    have h₆ : ¬p ∣ s := by
      have h₇ : Nat.Coprime s p := hs_cop
      have h₈ : ¬p ∣ s := by
        by_contra h₉
        have h₁₀ : p ∣ s := h₉
        have h₁₁ : p ∣ Nat.gcd s p := Nat.dvd_gcd h₁₀ (by simp)
        have h₁₂ : Nat.gcd s p = 1 := by
          rw [Nat.coprime_iff_gcd_eq_one] at hs_cop
          exact hs_cop
        rw [h₁₂] at h₁₁
        have h₁₃ : p ∣ 1 := h₁₁
        have h₁₄ : p ≤ 1 := Nat.le_of_dvd (by norm_num) h₁₃
        have h₁₅ : p ≥ 2 := Nat.Prime.two_le hp
        linarith
      exact h₈
    exact h₆ h₅
  intro h
  have h₅ : s % p = 0 := by
    omega
  contradiction



lemma fiber_element_coprime
    (p : ℕ) (hp : Nat.Prime p) (α v : ℕ) (hv_lt : v < α)
    (s : ℕ) (hs_cop : Nat.Coprime s p)
    (j : ℕ) :
    Nat.Coprime (s + j * p ^ (α - v)) (p ^ α) := by
  exact hp.coprime_pow_of_not_dvd (not_p_dvd_fiber_element p hp α v hv_lt s hs_cop j)



lemma fiber_element_mod_eq
    (p : ℕ) (α v : ℕ)
    (s : ℕ) (hs_lt : s < p ^ (α - v))
    (j : ℕ) :
    (s + j * p ^ (α - v)) % p ^ (α - v) = s := by
  have h₁ : (s + j * p ^ (α - v)) % p ^ (α - v) = s % p ^ (α - v) := by
    have h₂ : (s + j * p ^ (α - v)) % p ^ (α - v) = (s % p ^ (α - v) + (j * p ^ (α - v)) % p ^ (α -
      v)) % p ^ (α - v) := by
      simp [Nat.add_mod]
    rw [h₂]
    have h₃ : (j * p ^ (α - v)) % p ^ (α - v) = 0 := by
      have h₄ : p ^ (α - v) ∣ j * p ^ (α - v) := by
        exact ⟨j, by ring⟩
      have h₅ : (j * p ^ (α - v)) % p ^ (α - v) = 0 := by
        exact Nat.mod_eq_zero_of_dvd h₄
      exact h₅
    rw [h₃]
    have h₆ : (s % p ^ (α - v) + 0) % p ^ (α - v) = s % p ^ (α - v) := by
      simp
    rw [h₆]
  rw [h₁]
  have h₂ : s % p ^ (α - v) = s := by
    have h₃ : s < p ^ (α - v) := hs_lt
    have h₄ : s % p ^ (α - v) = s := Nat.mod_eq_of_lt h₃
    exact h₄
  rw [h₂]



lemma fiber_index_lt
    (p : ℕ) (_hp : Nat.Prime p) (α v : ℕ) (hv_lt : v < α)
    [NeZero (p ^ α)]
    (s : ℕ) (_hs_lt : s < p ^ (α - v))
    (u : (ZMod (p ^ α))ˣ)
    (hu : (u : ZMod (p ^ α)).val % p ^ (α - v) = s) :
    ((u : ZMod (p ^ α)).val - s) / p ^ (α - v) < p ^ v := by
  have h₁ : ((u : ZMod (p ^ α)).val : ℕ) < p ^ α := by
    have h₂ : (u : ZMod (p ^ α)).val < p ^ α := by
      exact ZMod.val_lt _
    exact_mod_cast h₂
  have h₃ : ((u : ZMod (p ^ α)).val - s) / p ^ (α - v) < p ^ v := by
    have h₄ : α - v + v = α := by
      have h₅ : v ≤ α := by linarith
      have h₆ : α - v + v = α := by
        rw [Nat.sub_add_cancel h₅]
      exact h₆
    have h₅ : p ^ (α - v) * p ^ v = p ^ α := by
      calc
        p ^ (α - v) * p ^ v = p ^ ((α - v) + v) := by
          rw [← pow_add]
        _ = p ^ α := by
          rw [h₄]
    have h₆ : ((u : ZMod (p ^ α)).val - s) / p ^ (α - v) < p ^ v := by
      have h₇ : ((u : ZMod (p ^ α)).val - s) < p ^ (α - v) * p ^ v := by
        have h₁₀ : ((u : ZMod (p ^ α)).val - s) ≤ (u : ZMod (p ^ α)).val := by
          omega
        omega
      have h₈ : ((u : ZMod (p ^ α)).val - s) / p ^ (α - v) < p ^ v := by
        have h₁₀ : ((u : ZMod (p ^ α)).val - s) / p ^ (α - v) < p ^ v := by
          apply Nat.div_lt_of_lt_mul
          nlinarith [Nat.zero_le (p ^ (α - v))]
        exact h₁₀
      exact h₈
    exact h₆
  exact h₃



lemma fiber_reconstruct
    (M s n : ℕ) (hn : n % M = s) (hs_le : s ≤ n) :
    s + (n - s) / M * M = n := by
  have h₁ : M * (n / M) + n % M = n := Nat.div_add_mod n M
  have h₃ : M ∣ n - s := ⟨n / M, by omega⟩
  have h₄ : (n - s) / M * M = n - s := Nat.div_mul_cancel h₃
  omega



lemma fiber_fwd_bwd
    (p : ℕ) (hp : Nat.Prime p) (α v : ℕ) (hv_lt : v < α)
    [NeZero (p ^ α)]
    (s : ℕ) (hs_lt : s < p ^ (α - v)) (hs_cop : Nat.Coprime s p)
    (j : ℕ) (hj : j < p ^ v) :
    let a := s + j * p ^ (α - v)
    let hcop := fiber_element_coprime p hp α v hv_lt s hs_cop j
    ((ZMod.unitOfCoprime a hcop : ZMod (p ^ α)).val - s) / p ^ (α - v) = j := by
  simp only
  have ha_lt : s + j * p ^ (α - v) < p ^ α := fiber_element_lt p hp α v hv_lt s hs_lt j hj
  rw [val_unitOfCoprime_eq_mod, Nat.mod_eq_of_lt ha_lt, Nat.add_sub_cancel_left,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero))]



lemma fiber_bwd_fwd
    (p : ℕ) (hp : Nat.Prime p) (α v : ℕ) (hv_lt : v < α)
    [NeZero (p ^ α)] [NeZero (p ^ (α - v))]
    (s : ℕ) (_hs_lt : s < p ^ (α - v)) (hs_cop : Nat.Coprime s p)
    (u : (ZMod (p ^ α))ˣ)
    (hu : (u : ZMod (p ^ α)).val % p ^ (α - v) = s) :
    let idx := ((u : ZMod (p ^ α)).val - s) / p ^ (α - v)
    let a := s + idx * p ^ (α - v)
    let hcop := fiber_element_coprime p hp α v hv_lt s hs_cop idx
    ZMod.unitOfCoprime a hcop = u := by
  intro idx a hcop
  apply Units.ext
  simp only [ZMod.coe_unitOfCoprime]
  have hkey : a = (u : ZMod (p ^ α)).val :=
    fiber_reconstruct (p ^ (α - v)) s ((u : ZMod (p ^ α)).val) hu (hu ▸ Nat.mod_le _ _)
  rw [hkey, ZMod.natCast_zmod_val]



lemma fiber_fwd_mem
    (p : ℕ) (hp : Nat.Prime p) (α v : ℕ) (hv_lt : v < α)
    [NeZero (p ^ α)]
    (s : ℕ) (hs_lt : s < p ^ (α - v)) (hs_cop : Nat.Coprime s p)
    (j : ℕ) (hj : j < p ^ v) :
    let a := s + j * p ^ (α - v)
    let hcop := fiber_element_coprime p hp α v hv_lt s hs_cop j
    let u := ZMod.unitOfCoprime a hcop
    (u : ZMod (p ^ α)).val % p ^ (α - v) = s := by
  simp only
  rw [val_unitOfCoprime_eq_mod]
  rw [Nat.mod_eq_of_lt (fiber_element_lt p hp α v hv_lt s hs_lt j hj)]
  exact fiber_element_mod_eq p α v s hs_lt j



lemma projection_fiber_card
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (_hα : 1 ≤ α)
    (v : ℕ) (_hv_pos : 1 ≤ v) (hv_lt : v < α)
    [NeZero (p ^ α)] [NeZero (p ^ (α - v))]
    (s : ℕ) (hs_lt : s < p ^ (α - v)) (hs_cop : Nat.Coprime s p) :
    (Finset.univ.filter (fun u : (ZMod (p ^ α))ˣ =>
      (u : ZMod (p ^ α)).val % p ^ (α - v) = s)).card = p ^ v := by
  set F := Finset.univ.filter (fun u : (ZMod (p ^ α))ˣ =>
      (u : ZMod (p ^ α)).val % p ^ (α - v) = s)
  set R := Finset.range (p ^ v)
  set fwd : (ZMod (p ^ α))ˣ → ℕ := fun u => ((u : ZMod (p ^ α)).val - s) / p ^ (α - v)
  set bwd : ℕ → (ZMod (p ^ α))ˣ := fun j =>
    ZMod.unitOfCoprime (s + j * p ^ (α - v)) (fiber_element_coprime p hp α v hv_lt s hs_cop j)
  rw [show p ^ v = R.card from (Finset.card_range _).symm]
  exact Finset.card_nbij' fwd bwd
    (fun u hu => by
      simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (fiber_index_lt p hp α v hv_lt s hs_lt u hu)))
    (fun j hj => by
      simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fiber_fwd_mem p hp α v hv_lt s hs_lt hs_cop j (Finset.mem_range.mp (Finset.mem_coe.mp
        hj)))
    (fun u hu => by
      simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact fiber_bwd_fwd p hp α v hv_lt s hs_lt hs_cop u hu)
    (fun j hj => by
      exact fiber_fwd_bwd p hp α v hv_lt s hs_lt hs_cop j (Finset.mem_range.mp (Finset.mem_coe.mp
        hj)))



lemma kprime_coprime_p
    (p : ℕ) (hp : Nat.Prime p) (k_val : ℕ)
    (v : ℕ) (hv_val : p ^ v ∣ k_val) (hv_max : ¬(p ^ (v + 1) ∣ k_val)) :
    Nat.Coprime (k_val / p ^ v) p := by
  have h₁ : ¬p ∣ (k_val / p ^ v) := by
    intro h
    have h₂ : p ^ (v + 1) ∣ k_val := by
      have h₃ : p ∣ (k_val / p ^ v) := h
      have h₄ : p ^ (v + 1) ∣ k_val := by
        have h₇ : p ^ (v + 1) ∣ k_val := by
          have h₈ : p ^ (v + 1) = p ^ v * p := by
            ring_nf
          rw [h₈]
          have h₉ : p ^ v ∣ k_val := hv_val
          have h₁₀ : p ∣ (k_val / p ^ v) := h₃
          have h₁₁ : p ^ v * p ∣ k_val := by
            obtain ⟨m, hm⟩ := h₉
            obtain ⟨n, _⟩ := h₁₀
            use m * n
            rw [hm]
            simp_all [mul_comm]
          exact h₁₁
        exact h₇
      exact h₄
    exact hv_max h₂
  have h₂ : Nat.Coprime (k_val / p ^ v) p := by
    have h₄ : ¬p ∣ (k_val / p ^ v) := h₁
    have h₅ : Nat.Coprime (k_val / p ^ v) p := by
      rw [Nat.coprime_comm]
      apply Nat.Prime.coprime_iff_not_dvd hp |>.mpr
      exact h₄
    exact h₅
  exact h₂


lemma reduced_product_mod_lt
    (p : ℕ) (_hp : Nat.Prime p) (α v : ℕ) (_hv_lt : v < α)
    [NeZero (p ^ (α - v))]
    (k_val : ℕ) (u : (ZMod (p ^ α))ˣ) :
    (k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α - v)) % p ^ (α - v) < p ^ (α - v) := by
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))



lemma summand_rewrite
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (hα : 1 ≤ α)
    (k_val : ℕ) (hk_nd : ¬((p ^ α : ℕ) ∣ k_val)) (hk_dvd_p : p ∣ k_val)
    (v : ℕ) (hv_pos : 1 ≤ v) (hv_lt : v < α)
    (hv_val : p ^ v ∣ k_val) (hv_max : ¬(p ^ (v + 1) ∣ k_val))
    [NeZero (p ^ α)] [NeZero (p ^ (α - v))] :
    (∑ u : (ZMod (p ^ α))ˣ,
      1 / min ((k_val * (u : ZMod (p ^ α)).val % (p ^ α) : ℕ) : ℝ)
              (((p ^ α : ℕ) : ℝ) - (k_val * (u : ZMod (p ^ α)).val % (p ^ α) : ℕ))) =
    (∑ u : (ZMod (p ^ α))ˣ,
      1 / (((p ^ v : ℕ) : ℝ) * min (((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α - v)) % p ^
        (α - v) : ℕ) : ℝ)
              (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α -
                v)) % p ^ (α - v) : ℕ)))) := by
  congr 1; ext u
  have hd_eq : p ^ α = p ^ α := rfl
  have hmod :=
    kval_mul_unit_mod_eq_pv_mul (p ^
      α) p hp α hα rfl k_val hk_nd hk_dvd_p v hv_pos hv_lt hv_val hv_max u
  have hne := reduced_product_mod_ne_zero p hp α hα k_val v hv_pos hv_lt hv_val hv_max u
  have hlt := reduced_product_mod_lt p hp α v hv_lt k_val u
  set r := (k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α - v)) % p ^ (α - v)
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hne
  rw [hmod]
  have hpow : p ^ α = p ^ v * p ^ (α - v) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]
  rw [min_pv_factor p v (p ^ (α - v)) r hr_pos hlt]


lemma pv_cancel (pv : ℝ) (x : ℝ) (hpv : 0 < pv) (hx : x ≠ 0) :
    pv * (1 / (pv * x)) = 1 / x := by
  have h₁ : pv * (1 / (pv * x)) = 1 / x := by
    have h₂ : pv ≠ 0 := by linarith
    have h₃ : pv * x ≠ 0 := by
      intro h₄
      have h₅ : x = 0 := by
        apply mul_left_cancel₀ h₂
        nlinarith
      contradiction
    field_simp [h₂, h₃]
  exact h₁



lemma unit_mod_coprime_p
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (hα : 1 ≤ α)
    (v : ℕ) (hv_lt : v < α)
    [NeZero (p ^ α)]
    (u : (ZMod (p ^ α))ˣ) :
    Nat.Coprime ((u : ZMod (p ^ α)).val % p ^ (α - v)) p := by
  have hcop : Nat.Coprime (u : ZMod (p ^ α)).val (p ^ α) := ZMod.val_coe_unit_coprime u
  have hcop_p : Nat.Coprime (u : ZMod (p ^ α)).val p :=
    hcop.coprime_dvd_right (dvd_pow_self p (by omega))
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd] at hcop_p ⊢
  intro hdvd
  exact hcop_p (dvd_of_dvd_mod_of_dvd p (u : ZMod (p ^ α)).val (p ^ (α - v))
    (dvd_pow_self p (by omega)) hdvd)



lemma summand_fiber_constant
    (k' M s u_val : ℕ) (hs : u_val % M = s) :
    k' * (u_val % M) % M = k' * s % M := by
  subst hs; rfl


lemma reduced_product_mod_ne_zero_of_coprime
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (_hα : 1 ≤ α)
    (k_val : ℕ)
    (v : ℕ) (_hv_pos : 1 ≤ v) (hv_lt : v < α)
    (hv_val : p ^ v ∣ k_val) (hv_max : ¬(p ^ (v + 1) ∣ k_val))
    [NeZero (p ^ (α - v))]
    (s : ℕ) (hs_cop : Nat.Coprime s p) :
    (k_val / p ^ v) * s % p ^ (α - v) ≠ 0 := by
  intro h
  have h₅ : p ^ (α - v) ∣ (k_val / p ^ v) * s := Nat.dvd_of_mod_eq_zero h
  have h₆ : p ∣ (k_val / p ^ v) * s :=
    dvd_trans (dvd_pow_self p (by omega)) h₅
  rcases (hp.dvd_mul).mp h₆ with h₈ | h₈
  · have hk : p ^ v * (k_val / p ^ v) = k_val := Nat.mul_div_cancel' hv_val
    apply hv_max
    obtain ⟨m, hm⟩ := h₈
    exact ⟨m, by rw [pow_succ, mul_assoc, ← hm, hk]⟩
  · exact absurd h₈ (hp.coprime_iff_not_dvd.mp hs_cop.symm)



lemma min_pos_of_ne_zero_lt
    (r M : ℕ) (hr_ne : r ≠ 0) (hr_lt : r < M) :
    (0 : ℝ) < min ((r : ℝ)) (((M : ℕ) : ℝ) - (r : ℝ)) := by
  have h₁ : (0 : ℝ) < (r : ℝ) := by
    norm_cast
    exact Nat.pos_of_ne_zero hr_ne
  have h₂ : (0 : ℝ) < ((M : ℕ) : ℝ) - (r : ℝ) := by
    have h₃ : (r : ℕ) < M := hr_lt
    have h₄ : (r : ℝ) < (M : ℝ) := by
      norm_cast
    linarith
  have h₃ : (0 : ℝ) < min ((r : ℝ)) (((M : ℕ) : ℝ) - (r : ℝ)) := by
    have h₄ : (0 : ℝ) < (r : ℝ) := h₁
    have h₅ : (0 : ℝ) < ((M : ℕ) : ℝ) - (r : ℝ) := h₂
    exact lt_min h₄ h₅
  exact h₃



lemma fiber_sum_cancel
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (hα : 1 ≤ α)
    (k_val : ℕ) (_hk_nd : ¬((p ^ α : ℕ) ∣ k_val))
    (v : ℕ) (hv_pos : 1 ≤ v) (hv_lt : v < α)
    (hv_val : p ^ v ∣ k_val) (hv_max : ¬(p ^ (v + 1) ∣ k_val))
    [NeZero (p ^ α)] [NeZero (p ^ (α - v))]
    (s : ℕ) (hs_lt : s < p ^ (α - v)) (hs_cop : Nat.Coprime s p) :
    (∑ u ∈ Finset.univ.filter (fun u : (ZMod (p ^ α))ˣ =>
        (u : ZMod (p ^ α)).val % p ^ (α - v) = s),
      (1 : ℝ) / (((p ^ v : ℕ) : ℝ) * min (((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α -
        v)) % p ^ (α - v) : ℕ) : ℝ)
              (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α -
                v)) % p ^ (α - v) : ℕ)))) =
    (1 : ℝ) / min (((k_val / p ^ v) * s % p ^ (α - v) : ℕ) : ℝ)
            (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * s % p ^ (α - v) : ℕ)) := by
  have h_const : ∀ u ∈ Finset.univ.filter (fun u : (ZMod (p ^ α))ˣ =>
      (u : ZMod (p ^ α)).val % p ^ (α - v) = s),
    (1 : ℝ) / (((p ^ v : ℕ) : ℝ) * min (((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α -
      v)) % p ^ (α - v) : ℕ) : ℝ)
            (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α -
              v)) % p ^ (α - v) : ℕ))) =
    (1 : ℝ) / (((p ^ v : ℕ) : ℝ) * min (((k_val / p ^ v) * s % p ^ (α - v) : ℕ) : ℝ)
            (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * s % p ^ (α - v) : ℕ))) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [summand_fiber_constant (k_val / p ^ v) (p ^ (α - v)) s _ hu]
  rw [Finset.sum_congr rfl h_const, Finset.sum_const, nsmul_eq_mul]
  rw [projection_fiber_card p hp α hα v hv_pos hv_lt s hs_lt hs_cop]
  have hpv_pos : (0 : ℝ) < ((p ^ v : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (pow_ne_zero v hp.ne_zero))
  have hr_ne : (k_val / p ^ v) * s % p ^ (α - v) ≠ 0 :=
    reduced_product_mod_ne_zero_of_coprime p hp α hα k_val v hv_pos hv_lt hv_val hv_max s hs_cop
  have hr_lt : (k_val / p ^ v) * s % p ^ (α - v) < p ^ (α - v) :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))
  have hmin_ne : (min (((k_val / p ^ v) * s % p ^ (α - v) : ℕ) : ℝ)
    (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * s % p ^ (α - v) : ℕ))) ≠ 0 :=
    ne_of_gt (min_pos_of_ne_zero_lt _ _ hr_ne hr_lt)
  exact pv_cancel ((p ^ v : ℕ) : ℝ) _ hpv_pos hmin_ne



lemma unit_mod_coprime_pow
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (hα : 1 ≤ α)
    (v : ℕ) (hv_lt : v < α)
    [NeZero (p ^ α)]
    (u : (ZMod (p ^ α))ˣ) :
    Nat.Coprime ((u : ZMod (p ^ α)).val % p ^ (α - v)) (p ^ (α - v)) :=
  hp.coprime_pow_of_not_dvd
    ((hp.coprime_iff_not_dvd.mp (unit_mod_coprime_p p hp α hα v hv_lt u).symm))



lemma unitProjection_filter_iff
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (hα : 1 ≤ α)
    (v : ℕ) (hv_lt : v < α)
    [NeZero (p ^ α)] [NeZero (p ^ (α - v))]
    (u : (ZMod (p ^ α))ˣ) (t : (ZMod (p ^ (α - v)))ˣ) :
    ZMod.unitOfCoprime
      ((u : ZMod (p ^ α)).val % p ^ (α - v))
      (unit_mod_coprime_pow p hp α hα v hv_lt u) = t ↔
    (u : ZMod (p ^ α)).val % p ^ (α - v) = (t : ZMod (p ^ (α - v))).val := by
  constructor
  · intro h
    have hval : (ZMod.unitOfCoprime
      ((u : ZMod (p ^ α)).val % p ^ (α - v))
      (unit_mod_coprime_pow p hp α hα v hv_lt u) : ZMod (p ^ (α - v))).val =
      (t : ZMod (p ^ (α - v))).val := by rw [h]
    rw [val_unitOfCoprime_eq_mod] at hval
    rwa [Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _)))] at hval
  · intro h
    apply Units.val_injective
    apply ZMod.val_injective
    rw [val_unitOfCoprime_eq_mod,
        Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))), h]



lemma fiberwise_sum_eq_double_sum
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (hα : 1 ≤ α)
    (k_val : ℕ) (_hk_nd : ¬((p ^ α : ℕ) ∣ k_val))
    (v : ℕ) (_hv_pos : 1 ≤ v) (hv_lt : v < α)
    (_hv_val : p ^ v ∣ k_val) (_hv_max : ¬(p ^ (v + 1) ∣ k_val))
    [NeZero (p ^ α)] [NeZero (p ^ (α - v))] :
    (∑ u : (ZMod (p ^ α))ˣ,
      1 / (((p ^ v : ℕ) : ℝ) * min (((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α - v)) % p ^
        (α - v) : ℕ) : ℝ)
              (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α -
                v)) % p ^ (α - v) : ℕ)))) =
    ∑ t : (ZMod (p ^ (α - v)))ˣ,
      ∑ u ∈ Finset.univ.filter (fun u : (ZMod (p ^ α))ˣ =>
        (u : ZMod (p ^ α)).val % p ^ (α - v) = (t : ZMod (p ^ (α - v))).val),
      (1 : ℝ) / (((p ^ v : ℕ) : ℝ) * min (((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α -
        v)) % p ^ (α - v) : ℕ) : ℝ)
              (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α -
                v)) % p ^ (α - v) : ℕ))) := by
  set π : (ZMod (p ^ α))ˣ → (ZMod (p ^ (α - v)))ˣ := fun u =>
    ZMod.unitOfCoprime
      ((u : ZMod (p ^ α)).val % p ^ (α - v))
      (unit_mod_coprime_pow p hp α hα v hv_lt u) with hπ_def
  set f : (ZMod (p ^ α))ˣ → ℝ := fun u =>
    1 / (((p ^ v : ℕ) : ℝ) * min (((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α - v)) % p ^
      (α - v) : ℕ) : ℝ)
            (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α -
              v)) % p ^ (α - v) : ℕ))) with hf_def
  have h_fiber : ∑ t : (ZMod (p ^ (α - v)))ˣ, ∑ u ∈ Finset.univ.filter (fun u => π u = t), f u =
      ∑ u : (ZMod (p ^ α))ˣ, f u :=
    Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) f
  rw [show ∑ u : (ZMod (p ^ α))ˣ, f u = ∑ t, ∑ u ∈ Finset.univ.filter (fun u =>
    π u = t), f u from h_fiber.symm]
  congr 1
  ext t
  apply Finset.sum_congr
  · ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact unitProjection_filter_iff p hp α hα v hv_lt u t
  · intros; rfl



lemma fiber_grouping_step
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (hα : 1 ≤ α)
    (k_val : ℕ) (hk_nd : ¬((p ^ α : ℕ) ∣ k_val))
    (v : ℕ) (hv_pos : 1 ≤ v) (hv_lt : v < α)
    (hv_val : p ^ v ∣ k_val) (hv_max : ¬(p ^ (v + 1) ∣ k_val))
    [NeZero (p ^ α)] [NeZero (p ^ (α - v))] :
    (∑ u : (ZMod (p ^ α))ˣ,
      1 / (((p ^ v : ℕ) : ℝ) * min (((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α - v)) % p ^
        (α - v) : ℕ) : ℝ)
              (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α -
                v)) % p ^ (α - v) : ℕ)))) =
    (∑ t : (ZMod (p ^ (α - v)))ˣ,
      1 / min (((k_val / p ^ v) * (t : ZMod (p ^ (α - v))).val % p ^ (α - v) : ℕ) : ℝ)
              (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * (t : ZMod (p ^ (α - v))).val % p ^ (α -
                v) : ℕ))) := by
  rw [fiberwise_sum_eq_double_sum p hp α hα k_val hk_nd v hv_pos hv_lt hv_val hv_max]
  congr 1
  ext t
  have ht_lt : (t : ZMod (p ^ (α - v))).val < p ^ (α - v) := ZMod.val_lt (t : ZMod (p ^ (α - v)))
  have ht_cop : Nat.Coprime (t : ZMod (p ^ (α - v))).val p :=
    (ZMod.val_coe_unit_coprime t).coprime_dvd_right (dvd_pow_self p (by omega : α - v ≠ 0))
  exact fiber_sum_cancel p hp α hα k_val hk_nd v hv_pos hv_lt hv_val hv_max
    (t : ZMod (p ^ (α - v))).val ht_lt ht_cop


lemma coprime_of_prime_power_not_dvd
    (d : ℕ) (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (_hα : 1 ≤ α)
    (hd_eq : d = p ^ α) (k_val : ℕ) (hp_ndvd : ¬(p ∣ k_val)) :
    Nat.Coprime k_val d := by
  rw [hd_eq]
  have h₁ : Nat.Coprime k_val (p ^ α) := by
    have h₂ : ¬p ∣ k_val := hp_ndvd
    have h₃ : Nat.Coprime k_val p := by
      rw [Nat.coprime_comm]
      simpa [Nat.prime_iff_prime_int.mp hp] using hp.coprime_iff_not_dvd.mpr h₂
    exact Nat.Coprime.pow_right _ h₃
  exact h₁



lemma permutation_step
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (_hα : 1 ≤ α)
    (k_val : ℕ)
    (v : ℕ) (_hv_pos : 1 ≤ v) (hv_lt : v < α)
    (hv_val : p ^ v ∣ k_val) (hv_max : ¬(p ^ (v + 1) ∣ k_val))
    [NeZero (p ^ (α - v))] :
    (∑ t : (ZMod (p ^ (α - v)))ˣ,
      1 / min (((k_val / p ^ v) * (t : ZMod (p ^ (α - v))).val % p ^ (α - v) : ℕ) : ℝ)
              (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * (t : ZMod (p ^ (α - v))).val % p ^ (α -
                v) : ℕ))) =
    (∑ t : (ZMod (p ^ (α - v)))ˣ,
      1 / min (((t : ZMod (p ^ (α - v))).val : ℕ) : ℝ)
              (((p ^ (α - v) : ℕ) : ℝ) - ((t : ZMod (p ^ (α - v))).val : ℕ))) := by
  have hndvd : ¬(p ∣ k_val / p ^ v) :=
    not_p_dvd_div_pow_1 p hp k_val v hv_val hv_max
  have hcop : Nat.Coprime (k_val / p ^ v) (p ^ (α - v)) :=
    coprime_of_prime_power_not_dvd (p ^ (α - v)) p hp (α - v) (by omega) rfl
      (k_val / p ^ v) hndvd
  exact coprime_case_sum_eq (p ^ (α - v)) (k_val / p ^ v) hcop



lemma orbit_fiber_sum_eq
    (d : ℕ) [NeZero d] (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (hα : 1 ≤ α)
    (hd_eq : d = p ^ α)
    (k_val : ℕ) (hk_nd : ¬((d : ℕ) ∣ k_val)) (hk_dvd_p : p ∣ k_val)
    (v : ℕ) (hv_pos : 1 ≤ v) (hv_lt : v < α)
    (hv_val : p ^ v ∣ k_val) (hv_max : ¬(p ^ (v + 1) ∣ k_val))
    [NeZero (p ^ (α - v))] :
    (∑ u : (ZMod d)ˣ,
      1 / min ((k_val * (u : ZMod d).val % d : ℕ) : ℝ)
              (((d : ℕ) : ℝ) - (k_val * (u : ZMod d).val % d : ℕ))) =
    (∑ t : (ZMod (p ^ (α - v)))ˣ,
      1 / min (((t : ZMod (p ^ (α - v))).val : ℕ) : ℝ)
              (((p ^ (α - v) : ℕ) : ℝ) - ((t : ZMod (p ^ (α - v))).val : ℕ))) := by
  subst hd_eq
  calc (∑ u : (ZMod (p ^ α))ˣ,
        1 / min ((k_val * (u : ZMod (p ^ α)).val % (p ^ α) : ℕ) : ℝ)
                (((p ^ α : ℕ) : ℝ) - (k_val * (u : ZMod (p ^ α)).val % (p ^ α) : ℕ)))
      = (∑ u : (ZMod (p ^ α))ˣ,
        1 / (((p ^ v : ℕ) : ℝ) * min (((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α -
          v)) % p ^ (α - v) : ℕ) : ℝ)
                (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * ((u : ZMod (p ^ α)).val % p ^ (α -
                  v)) % p ^ (α - v) : ℕ)))) := by
          exact summand_rewrite p hp α hα k_val hk_nd hk_dvd_p v hv_pos hv_lt hv_val hv_max
    _ = (∑ t : (ZMod (p ^ (α - v)))ˣ,
        1 / min (((k_val / p ^ v) * (t : ZMod (p ^ (α - v))).val % p ^ (α - v) : ℕ) : ℝ)
                (((p ^ (α - v) : ℕ) : ℝ) - ((k_val / p ^ v) * (t : ZMod (p ^ (α - v))).val % p ^
                  (α - v) : ℕ))) := by
          exact fiber_grouping_step p hp α hα k_val hk_nd v hv_pos hv_lt hv_val hv_max
    _ = (∑ t : (ZMod (p ^ (α - v)))ˣ,
        1 / min (((t : ZMod (p ^ (α - v))).val : ℕ) : ℝ)
                (((p ^ (α - v) : ℕ) : ℝ) - ((t : ZMod (p ^ (α - v))).val : ℕ))) := by
          exact permutation_step p hp α hα k_val v hv_pos hv_lt hv_val hv_max



lemma distribute_two_over_sum (k : ℕ) (hk : 1 ≤ k) :
    2 * ((∑ u ∈ Finset.Icc 1 (k - 1), (u : ℝ)⁻¹) + 1 / (2 * (k : ℝ))) =
    2 * (∑ u ∈ Finset.Icc 1 (k - 1), (u : ℝ)⁻¹) + 1 / (k : ℝ) := by
  have h₁ : (2 : ℝ) * (1 / (2 * (k : ℝ))) = 1 / (k : ℝ) := by
    have h₂ : (k : ℝ) ≠ 0 := by
      norm_cast
      (try omega)
    field_simp [h₂]
  calc
    2 * ((∑ u ∈ Finset.Icc 1 (k - 1), (u : ℝ)⁻¹) + 1 / (2 * (k : ℝ))) =
        2 * (∑ u ∈ Finset.Icc 1 (k - 1), (u : ℝ)⁻¹) + 2 * (1 / (2 * (k : ℝ))) := by
      ring_nf
    _ = 2 * (∑ u ∈ Finset.Icc 1 (k - 1), (u : ℝ)⁻¹) + 1 / (k : ℝ) := by
      rw [h₁]



lemma even_step_lhs_eq (k : ℕ) (hk : 1 ≤ k) :
    (∑ t ∈ Finset.Icc 1 (2 * k - 1),
      1 / min ((t : ℝ)) ((2 * k : ℝ) - (t : ℝ))) =
    2 * (∑ u ∈ Finset.Icc 1 (k - 1), (u : ℝ)⁻¹) + 1 / (k : ℝ) := by
  have h1 : (∑ t ∈ Finset.Icc 1 (2 * k - 1),
      1 / min ((t : ℝ)) ((2 * k : ℝ) - (t : ℝ))) =
    2 * (∑ t ∈ Finset.Icc 1 (2 * k - 1),
      (1 : ℝ) / (2 * min (t : ℝ) ((2 * k : ℝ) - t))) := by
    have := sum_eq_two_mul_half_sum (2 * k)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at this
    exact this
  rw [h1, symmetric_sum_even k hk]
  exact distribute_two_over_sum k hk



lemma lhs_eq_1 (k : ℕ) (hk : 1 ≤ k) :
    (∑ t ∈ Finset.Icc 1 (2 * k),
      1 / min ((t : ℝ)) ((2 * (k : ℝ) + 1) - (t : ℝ))) =
    2 * ∑ u ∈ Finset.Icc 1 k, (u : ℝ)⁻¹ := by
  have h1 := sum_eq_two_mul_half_sum (2 * k + 1)
  simp only [show (2 * k + 1) - 1 = 2 * k from by omega] at h1
  push_cast [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h1
  rw [h1]
  congr 1
  exact symmetric_sum_odd k hk


lemma harmonic_split (k : ℕ) (hk : 1 ≤ k) :
    ∑ u ∈ Finset.Icc 1 k, (u : ℝ)⁻¹ =
    (∑ u ∈ Finset.Icc 1 (k - 1), (u : ℝ)⁻¹) + (k : ℝ)⁻¹ := by
  have h₁ : ∑ u ∈ Finset.Icc 1 k, (u : ℝ)⁻¹ = ∑ u ∈ Finset.Icc 1 (k - 1), (u : ℝ)⁻¹ + (k : ℝ)⁻¹ :=
    by
    have h₂ : ∑ u ∈ Finset.Icc 1 k, (u : ℝ)⁻¹ = ∑ u ∈ Finset.Icc 1 (k - 1), (u : ℝ)⁻¹ + (k : ℝ)⁻¹ :=
      by
      cases k with
      | zero =>
        exfalso
        linarith
      | succ k' =>
        cases k' with
        | zero =>
          norm_num [Finset.sum_Icc_succ_top]
        | succ k'' =>
          simp_all [Finset.sum_Icc_succ_top, Nat.cast_add, Nat.cast_one]
    exact h₂
  exact h₁



lemma even_step (k : ℕ) (hk : 1 ≤ k) :
    (∑ t ∈ Finset.Icc 1 (2 * k - 1),
      1 / min ((t : ℝ)) ((2 * k : ℝ) - (t : ℝ))) ≤
    (∑ t ∈ Finset.Icc 1 (2 * k),
      1 / min ((t : ℝ)) ((2 * k + 1 : ℝ) - (t : ℝ))) := by
  rw [even_step_lhs_eq k hk, lhs_eq_1 k hk, harmonic_split k hk]
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have : 1 / (k : ℝ) ≤ 2 * (k : ℝ)⁻¹ := by
    rw [one_div]
    linarith [inv_pos.mpr hk_pos]
  linarith



lemma rhs_eq (k : ℕ) (hk : 1 ≤ k) :
    (∑ t ∈ Finset.Icc 1 (2 * k + 1),
      1 / min ((t : ℝ)) ((2 * (k : ℝ) + 1 + 1) - (t : ℝ))) =
    2 * ((∑ u ∈ Finset.Icc 1 k, (u : ℝ)⁻¹) + 1 / (2 * ((k : ℝ) + 1))) := by
  have hM : (2 * (k + 1) : ℕ) - 1 = 2 * k + 1 := by omega
  have h1 := sum_eq_two_mul_half_sum (2 * (k + 1))
  rw [hM] at h1
  conv at h1 => lhs; arg 2; ext t; rw [show (↑(2 * (k + 1)) : ℝ) = 2 * (↑k : ℝ) + 1 + 1 from by
    push_cast; ring]
  conv at h1 =>
    rhs; arg 2; arg 2; ext t; rw [show (↑(2 * (k + 1)) : ℝ) = 2 * (↑k : ℝ) + 1 + 1 from by
      push_cast; ring]
  rw [h1]
  have h2 := symmetric_sum_even (k + 1) (by omega : 1 ≤ k + 1)
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 from by omega, show k + 1 - 1 = k from by omega] at h2
  congr 1
  conv at h2 => lhs; arg 2; ext t; rw [show (2 * (↑(k + 1) : ℝ) : ℝ) = 2 * (↑k : ℝ) + 1 + 1 from by
    push_cast; ring]
  rw [h2]
  congr 1
  push_cast; ring



lemma odd_step (k : ℕ) (hk : 1 ≤ k) :
    (∑ t ∈ Finset.Icc 1 (2 * k),
      1 / min ((t : ℝ)) ((2 * (k : ℝ) + 1) - (t : ℝ))) ≤
    (∑ t ∈ Finset.Icc 1 (2 * k + 1),
      1 / min ((t : ℝ)) ((2 * (k : ℝ) + 1 + 1) - (t : ℝ))) := by
  rw [lhs_eq_1 k hk, rhs_eq k hk]
  linarith [show (0 : ℝ) < 1 / (2 * ((k : ℝ) + 1)) from by positivity]



lemma harmonic_min_sum_step (N : ℕ) (hN : 2 ≤ N) :
    (∑ t ∈ Finset.Icc 1 (N - 1),
      1 / min ((t : ℝ)) (((N : ℕ) : ℝ) - (t : ℝ))) ≤
    (∑ t ∈ Finset.Icc 1 ((N + 1) - 1),
      1 / min ((t : ℝ)) ((((N + 1) : ℕ) : ℝ) - (t : ℝ))) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
  · have hk : 1 ≤ k := by omega
    change (∑ t ∈ Finset.Icc 1 (2 * k - 1),
      1 / min ((t : ℝ)) (((2 * k : ℕ) : ℝ) - (t : ℝ))) ≤
      (∑ t ∈ Finset.Icc 1 ((2 * k + 1) - 1),
      1 / min ((t : ℝ)) ((((2 * k + 1) : ℕ) : ℝ) - (t : ℝ)))
    simp only [show (2 * k + 1 : ℕ) - 1 = 2 * k from by omega]
    push_cast
    exact even_step k hk
  · have hk : 1 ≤ k := by omega
    change (∑ t ∈ Finset.Icc 1 ((2 * k + 1) - 1),
      1 / min ((t : ℝ)) ((((2 * k + 1) : ℕ) : ℝ) - (t : ℝ))) ≤
      (∑ t ∈ Finset.Icc 1 ((2 * k + 1 + 1) - 1),
      1 / min ((t : ℝ)) ((((2 * k + 1 + 1) : ℕ) : ℝ) - (t : ℝ)))
    simp only [show (2 * k + 1 : ℕ) - 1 = 2 * k from by omega,
               show (2 * k + 1 + 1 : ℕ) - 1 = 2 * k + 1 from by omega]
    push_cast
    exact odd_step k hk



lemma harmonic_min_sum_mono
    (M d : ℕ) (hM : 2 ≤ M) (hMd : M ≤ d) :
    (∑ t ∈ Finset.Icc 1 (M - 1),
      1 / min ((t : ℝ)) (((M : ℕ) : ℝ) - (t : ℝ))) ≤
    (∑ t ∈ Finset.Icc 1 (d - 1),
      1 / min ((t : ℝ)) (((d : ℕ) : ℝ) - (t : ℝ))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hMd
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    have hstep := harmonic_min_sum_step (M + k) (by omega)
    have h1 : M + k + 1 - 1 = M + k := by omega
    have h2 : M + (k + 1) - 1 = M + k := by omega
    rw [h2]
    rw [h1] at hstep
    exact le_trans ih' hstep



lemma exists_padic_valuation
    (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (_hα : 1 ≤ α)
    (k_val : ℕ) (hk_dvd_p : p ∣ k_val) (hk_nd : ¬(p ^ α ∣ k_val)) :
    ∃ v, 1 ≤ v ∧ v < α ∧ p ^ v ∣ k_val ∧ ¬(p ^ (v + 1) ∣ k_val) := by
  by_cases hk : k_val = 0
  · have h_absurd : False := by simp_all
    have h_main : ∃ v, 1 ≤ v ∧ v < α ∧ p ^ v ∣ k_val ∧ ¬(p ^ (v + 1) ∣ k_val) := by contradiction
    exact h_main
  · haveI := Fact.mk hp
    have h1 : 1 ≤ padicValNat p k_val := by
      exact one_le_padicValNat_of_dvd hk hk_dvd_p
    have h2 : padicValNat p k_val < α := by
      by_contra h_ge
      push Not at h_ge
      exact hk_nd ((Nat.pow_dvd_pow p h_ge).trans pow_padicValNat_dvd)
    have h3 : p ^ (padicValNat p k_val) ∣ k_val := by exact pow_padicValNat_dvd
    have h4 : ¬(p ^ (padicValNat p k_val + 1) ∣ k_val) :=
      pow_succ_padicValNat_not_dvd hk
    exact ⟨padicValNat p k_val, h1, h2, h3, h4⟩



lemma general_case_bound
    (d : ℕ) [NeZero d] (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (hα : 1 ≤ α)
    (hd_eq : d = p ^ α)
    (k_val : ℕ) (hk_nd : ¬((d : ℕ) ∣ k_val)) (hk_dvd_p : p ∣ k_val) :
    (∑ u : (ZMod d)ˣ,
      1 / min ((k_val * (u : ZMod d).val % d : ℕ) : ℝ)
              (((d : ℕ) : ℝ) - (k_val * (u : ZMod d).val % d : ℕ))) ≤
    (∑ t ∈ Finset.Icc 1 (d - 1),
      1 / min ((t : ℝ)) (((d : ℕ) : ℝ) - (t : ℝ))) := by
  have hk_nd' : ¬(p ^ α ∣ k_val) := hd_eq ▸ hk_nd
  obtain ⟨v, hv_pos, hv_lt, hv_dvd, hv_max⟩ :=
    exists_padic_valuation p hp α hα k_val hk_dvd_p hk_nd'
  set M := p ^ (α - v) with hM_def
  have hM_pos : 0 < M := by
    simp only [hM_def]
    exact pow_pos hp.pos _
  haveI : NeZero M := ⟨by omega⟩
  haveI : NeZero (p ^ (α - v)) := ⟨by omega⟩
  have hM_ge : 2 ≤ M := by
    have : p ^ 1 ≤ M := by
      apply Nat.pow_le_pow_right hp.pos
      omega
    linarith [hp.two_le]
  calc (∑ u : (ZMod d)ˣ,
        1 / min ((k_val * (u : ZMod d).val % d : ℕ) : ℝ)
                (((d : ℕ) : ℝ) - (k_val * (u : ZMod d).val % d : ℕ)))
      = (∑ t : (ZMod M)ˣ,
          1 / min (((t : ZMod M).val : ℕ) : ℝ)
                  (((M : ℕ) : ℝ) - ((t : ZMod M).val : ℕ))) :=
        orbit_fiber_sum_eq d p hp α hα hd_eq k_val hk_nd hk_dvd_p v hv_pos hv_lt hv_dvd hv_max
    _ ≤ (∑ t ∈ Finset.Icc 1 (M - 1),
          1 / min ((t : ℝ)) (((M : ℕ) : ℝ) - (t : ℝ))) :=
        units_sum_le_Icc_sum M hM_ge
    _ ≤ (∑ t ∈ Finset.Icc 1 (d - 1),
          1 / min ((t : ℝ)) (((d : ℕ) : ℝ) - (t : ℝ))) := by
        apply harmonic_min_sum_mono M d hM_ge
        calc M = p ^ (α - v) := rfl
          _ ≤ p ^ α := Nat.pow_le_pow_right hp.pos (by omega)
          _ = d := hd_eq.symm



lemma orbit_fiber_sum_bound
    (d : ℕ) [NeZero d] (p : ℕ) (hp : Nat.Prime p) (α : ℕ) (hα : 1 ≤ α)
    (hd_eq : d = p ^ α)
    (k_val : ℕ) (hk_nd : ¬((d : ℕ) ∣ k_val)) :
    (∑ u : (ZMod d)ˣ,
      1 / min ((k_val * (u : ZMod d).val % d : ℕ) : ℝ)
              (((d : ℕ) : ℝ) - (k_val * (u : ZMod d).val % d : ℕ))) ≤
    (∑ t ∈ Finset.Icc 1 (d - 1),
      1 / min ((t : ℝ)) (((d : ℕ) : ℝ) - (t : ℝ))) := by
  by_cases hp_dvd : p ∣ k_val
  · exact general_case_bound d p hp α hα hd_eq k_val hk_nd hp_dvd
  · have hcop : Nat.Coprime k_val d := coprime_of_prime_power_not_dvd d p hp α hα hd_eq k_val hp_dvd
    have hd2 : 2 ≤ d := by
      rw [hd_eq]; exact le_trans (Nat.Prime.two_le hp) (Nat.le_self_pow (by omega) p)
    calc (∑ u : (ZMod d)ˣ,
            1 / min ((k_val * (u : ZMod d).val % d : ℕ) : ℝ)
                    (((d : ℕ) : ℝ) - (k_val * (u : ZMod d).val % d : ℕ)))
        = (∑ u : (ZMod d)ˣ,
            1 / min (((u : ZMod d).val : ℕ) : ℝ)
                    (((d : ℕ) : ℝ) - ((u : ZMod d).val : ℕ))) := coprime_case_sum_eq d k_val hcop
      _ ≤ (∑ t ∈ Finset.Icc 1 (d - 1),
            1 / min ((t : ℝ)) (((d : ℕ) : ℝ) - (t : ℝ))) := units_sum_le_Icc_sum d hd2


lemma d_ge_two (n d : ℕ) (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) :
    2 ≤ d := by
  rw [hd]
  exact le_trans (largestPrimeFactor_ge_two n hn) (d_ge_P n hn)



lemma d_le_n (n d : ℕ) (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) :
    d ≤ n := by
  rw [hd]
  exact Nat.le_of_dvd (by omega) (d_dvd_n n hn)



lemma orbit_sum_le_two_log
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (k : ZMod n) (_hk : k ≠ 0) (hk_nd : ¬((d : ℕ) ∣ ZMod.val k)) :
    (∑ u : (ZMod d)ˣ,
      1 / min ((ZMod.val k * (u : ZMod d).val % d : ℕ) : ℝ)
              ((d : ℝ) - (ZMod.val k * (u : ZMod d).val % d : ℕ))) ≤
    2 * (1 + Real.log ↑n) := by
  set P := largestPrimeFactor n
  set α := n.factorization P
  have hP : Nat.Prime P := largest_prime_factor_prime n hn
  have hα : 1 ≤ α := largest_prime_factor_multiplicity_pos n hn
  have hd2 : 2 ≤ d := d_ge_two n d hn hd
  have hdn : d ≤ n := d_le_n n d hn hd
  calc (∑ u : (ZMod d)ˣ,
        1 / min ((ZMod.val k * (u : ZMod d).val % d : ℕ) : ℝ)
                ((d : ℝ) - (ZMod.val k * (u : ZMod d).val % d : ℕ)))
      ≤ (∑ t ∈ Finset.Icc 1 (d - 1),
        1 / min ((t : ℝ)) ((d : ℝ) - (t : ℝ))) :=
        orbit_fiber_sum_bound d P hP α hα hd (ZMod.val k) hk_nd
    _ ≤ 2 * (1 + Real.log ↑n) :=
        harmonic_min_sum_le_two_log d n hd2 hdn



lemma pow_pred_mul_eq (P α : ℕ) (hα : 0 < α) :
    P ^ (α - 1) * P = P ^ α := by
  have h1 : α - 1 + 1 = α := by
    have h2 : 1 ≤ α := by linarith
    have h3 : α - 1 + 1 = α := by
      have h4 : α - 1 + 1 = α := by
        rw [Nat.sub_add_cancel h2]
      exact h4
    exact h3
  calc
    P ^ (α - 1) * P = P ^ (α - 1) * P ^ 1 := by
      simp [pow_one]
    _ = P ^ ((α - 1) + 1) := by
      rw [pow_add]
    _ = P ^ α := by
      rw [h1]



lemma cast_nat_sub_one (P : ℕ) (hP2 : 2 ≤ P) : (↑(P - 1) : ℝ) = ↑P - 1 := by
  have h₁ : 1 ≤ P := by
    omega
  have h₂ : (↑(P - 1) : ℝ) = (P : ℝ) - 1 := by
    norm_num [h₁] at hP2 ⊢
  exact h₂



lemma totient_prime_pow_simplify (P α : ℕ) (hP2 : 2 ≤ P) (hα : 0 < α) :
    (↑(P ^ (α - 1) * (P - 1)) : ℝ) * (4 / ↑(P ^ α)) = 4 * (↑P - 1) / ↑P := by
  have hP_pos : (0 : ℝ) < ↑P := by positivity
  have hPα1_pos : (0 : ℝ) < ↑(P ^ (α - 1)) := by positivity
  have hkey : (↑(P ^ α) : ℝ) = ↑(P ^ (α - 1)) * ↑P := by
    rw [← Nat.cast_mul, pow_pred_mul_eq P α hα]
  have hcast : (↑(P - 1) : ℝ) = ↑P - 1 := cast_nat_sub_one P hP2
  rw [Nat.cast_mul, hcast, hkey]
  have hPne : (↑P : ℝ) ≠ 0 := ne_of_gt hP_pos
  have hPα1ne : (↑(P ^ (α - 1)) : ℝ) ≠ 0 := ne_of_gt hPα1_pos
  field_simp


lemma four_times_sub_one_div_ge_two (P : ℕ) (hP2 : 2 ≤ P) :
    2 ≤ 4 * ((↑P : ℝ) - 1) / ↑P := by
  have hP_pos : (0 : ℝ) < ↑P := by positivity
  rw [le_div_iff₀ hP_pos]
  nlinarith [show (2 : ℝ) ≤ ↑P from by exact_mod_cast hP2]



lemma totient_prime_pow_times_four_div_ge_two
    (P α : ℕ) (hP : Nat.Prime P) (hα : 0 < α) (hP2 : 2 ≤ P) :
    2 ≤ ((P ^ α).totient : ℝ) * (4 / ((P ^ α : ℕ) : ℝ)) := by
  rw [Nat.totient_prime_pow hP hα]
  rw [totient_prime_pow_simplify P α hP2 hα]
  exact four_times_sub_one_div_ge_two P hP2



lemma totient_times_four_div_d_ge_two
    (n d : ℕ) [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) :
    2 ≤ (d.totient : ℝ) * (4 / (d : ℝ)) := by
  have hP := largest_prime_factor_prime n hn
  have hα := largest_prime_factor_multiplicity_pos n hn
  have hP2 := largestPrimeFactor_ge_two n hn
  rw [hd]
  exact totient_prime_pow_times_four_div_ge_two _ _ hP (by omega) hP2



lemma two_log_le_card_times_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) :
    2 * (1 + Real.log ↑n) ≤
    ↑(Fintype.card (ZMod d)ˣ) * (4 * (1 + Real.log ↑n) / ↑d) := by
  have hlog := one_plus_log_nonneg n hn
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  rw [show (4 : ℝ) * (1 + Real.log ↑n) / ↑d = 4 / ↑d * (1 + Real.log ↑n) by ring]
  rw [show (↑(Fintype.card (ZMod d)ˣ) : ℝ) * (4 / ↑d * (1 + Real.log ↑n)) =
    (↑(Fintype.card (ZMod d)ˣ) : ℝ) * (4 / ↑d) * (1 + Real.log ↑n) by ring]
  rw [show (2 : ℝ) * (1 + Real.log ↑n) = 2 * (1 + Real.log ↑n) from rfl]
  rw [ZMod.card_units_eq_totient]
  calc 2 * (1 + Real.log ↑n)
      = 2 * (1 + Real.log ↑n) := rfl
    _ ≤ (↑(d.totient) * (4 / ↑d)) * (1 + Real.log ↑n) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        exact totient_times_four_div_d_ge_two n d hn hd



lemma orbit_reciprocal_sum_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (k : ZMod n) (hk : k ≠ 0) (hk_nd : ¬((d : ℕ) ∣ ZMod.val k)) :
    (∑ u : (ZMod d)ˣ,
      1 / min ((ZMod.val k * (u : ZMod d).val % d : ℕ) : ℝ)
              ((d : ℝ) - (ZMod.val k * (u : ZMod d).val % d : ℕ))) ≤
    ↑(Fintype.card (ZMod d)ˣ) * (4 * (1 + Real.log ↑n) / ↑d) := by
  calc (∑ u : (ZMod d)ˣ,
      1 / min ((ZMod.val k * (u : ZMod d).val % d : ℕ) : ℝ)
              ((d : ℝ) - (ZMod.val k * (u : ZMod d).val % d : ℕ)))
      ≤ 2 * (1 + Real.log ↑n) := orbit_sum_le_two_log n d hn hd k hk hk_nd
    _ ≤ ↑(Fintype.card (ZMod d)ˣ) * (4 * (1 + Real.log ↑n) / ↑d) :=
        two_log_le_card_times_bound n d hn hd

namespace PerUnitMerge



lemma neg_inv_isUnit
    (d : ℕ) [NeZero d]
    (q : ℤ) (hq : Int.gcd q (d : ℤ) = 1) :
    IsUnit (-(q : ZMod d)⁻¹) := by
  apply IsUnit.neg
  apply ZMod.isUnit_inv
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  rw [Int.isCoprime_iff_gcd_eq_one]
  rwa [Int.gcd_comm]



lemma dvd_of_dvd_mul_unit_val
    (d : ℕ) [NeZero d]
    (k_val : ℕ) (u : (ZMod d)ˣ)
    (h : d ∣ k_val * (u : ZMod d).val) :
    d ∣ k_val := by
  have h_coprime : Nat.Coprime (u : ZMod d).val d := by exact ZMod.val_coe_unit_coprime u
  have h_coprime_symm : Nat.Coprime d (u : ZMod d).val := by exact h_coprime.symm
  have h_main : d ∣ k_val := by exact (Nat.Coprime.dvd_of_dvd_mul_right h_coprime_symm h)
  assumption



lemma b_ne_zero
    (d : ℕ) [NeZero d]
    (q : ℤ) (hq_coprime_d : Int.gcd q (d : ℤ) = 1)
    (k_val : ℕ) (hk_nd : ¬(d ∣ k_val))
    (u : (ZMod d)ˣ) :
    (-(q : ZMod d)⁻¹ * ((k_val * (u : ZMod d).val : ℕ) : ZMod d)) ≠ 0 := by
  intro h
  apply hk_nd
  apply dvd_of_dvd_mul_unit_val d k_val u
  have h2 : ((k_val * (u : ZMod d).val : ℕ) : ZMod d) = 0 :=
    (neg_inv_isUnit d q hq_coprime_d).mul_right_eq_zero.mp h
  exact (ZMod.natCast_eq_zero_iff _ _).mp h2


lemma b_bounds
    (d : ℕ) [NeZero d]
    (q : ℤ) (hq_coprime_d : Int.gcd q (d : ℤ) = 1)
    (k_val : ℕ) (hk_nd : ¬(d ∣ k_val))
    (u : (ZMod d)ˣ) :
    let b := ZMod.val (-(q : ZMod d)⁻¹ * ((k_val * (u : ZMod d).val : ℕ) : ZMod d))
    1 ≤ b ∧ b < d := by
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero _).mpr (b_ne_zero d q hq_coprime_d k_val
    hk_nd u))
  · exact ZMod.val_lt _


lemma q_isUnit_of_gcd (d : ℕ) [NeZero d] (q : ℤ) (hq : Int.gcd q (d : ℤ) = 1) :
    IsUnit (q : ZMod d) := by
  have h₁ : (q : ℤ).gcd (d : ℤ) = 1 := by assumption
  have h₂ : IsCoprime (q : ℤ) (d : ℤ) := by exact Int.isCoprime_iff_gcd_eq_one.mpr h₁
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  exact h₂.symm



lemma inv_isUnit_of_isUnit (d : ℕ) [NeZero d] (a : ZMod d) (ha : IsUnit a) :
    IsUnit (a⁻¹) := by
  have h : a⁻¹ * a = 1 := ZMod.inv_mul_of_unit a ha
  have h2 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a ha
  exact ⟨⟨a⁻¹, a, h, h2⟩, rfl⟩


lemma isCoprime_intCast_of_gcd_eq_one (d : ℕ) (q : ℤ) (hq : Int.gcd q (d : ℤ) = 1) :
    IsCoprime (d : ℤ) q := by
  have h := Int.isCoprime_iff_gcd_eq_one.mpr hq
  exact h.symm



lemma neg_inv_eq_inv_neg (d : ℕ) [NeZero d] (q : ℤ) (hq : Int.gcd q (d : ℤ) = 1) :
    -(q : ZMod d)⁻¹ = (-(q : ZMod d))⁻¹ := by
  have hu := q_isUnit_of_gcd d q hq
  have h1 : (-(q : ZMod d)) * (-(q : ZMod d)⁻¹) = 1 := by
    rw [neg_mul_neg]
    exact ZMod.mul_inv_of_unit _ hu
  rw [← ZMod.inv_eq_of_mul_eq_one d (-(q : ZMod d)) (-(q : ZMod d)⁻¹) h1]



lemma dvd_iff_zmod_eq_zero
    (d : ℕ) [NeZero d] (k_val u_val l_val : ℕ) (q : ℤ) :
    ((d : ℤ) ∣ (↑k_val * ↑u_val + ↑l_val * q)) ↔
    ((k_val : ZMod d) * (u_val : ZMod d) + (l_val : ZMod d) * (q : ZMod d) = 0) := by
  have h_iff : ((d : ℤ) ∣ (↑k_val * ↑u_val + ↑l_val * q)) ↔ (((k_val : ℤ) * (u_val : ℤ) +
    (l_val : ℤ) * q : ℤ) : ZMod d) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm
  have h_final : ((d : ℤ) ∣ (↑k_val * ↑u_val + ↑l_val * q)) ↔ ((k_val : ZMod d) * (u_val : ZMod d) +
    (l_val : ZMod d) * (q : ZMod d) = 0) := by simp_all
  assumption



lemma zmod_eq_zero_forward
    (d : ℕ) [NeZero d] (k_val u_val l_val : ℕ) (q : ℤ)
    (hq : IsUnit (q : ZMod d))
    (h : (k_val : ZMod d) * (u_val : ZMod d) + (l_val : ZMod d) * (q : ZMod d) = 0) :
    (l_val : ZMod d) = -(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d) := by
  have h₂ : (q : ZMod d)⁻¹ * (q : ZMod d) = 1 := by exact ZMod.inv_mul_of_unit _ hq
  have h₃ : (l_val : ZMod d) = -(q : ZMod d)⁻¹ * ((k_val : ZMod d) * (u_val : ZMod d)) := by
    have : (l_val : ZMod d) * (q : ZMod d) = -((k_val : ZMod d) * (u_val : ZMod d)) :=
      by linear_combination h
    calc (l_val : ZMod d)
        = (l_val : ZMod d) * ((q : ZMod d)⁻¹ * (q : ZMod d)) := by rw [h₂, mul_one]
      _ = ((l_val : ZMod d) * (q : ZMod d)) * (q : ZMod d)⁻¹ := by ring
      _ = -((k_val : ZMod d) * (u_val : ZMod d)) * (q : ZMod d)⁻¹ := by rw [this]
      _ = -(q : ZMod d)⁻¹ * ((k_val : ZMod d) * (u_val : ZMod d)) := by ring
  have h₄ : (l_val : ZMod d) = -(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d) := by simp_all
  exact h₄



lemma zmod_eq_zero_backward
    (d : ℕ) [NeZero d] (k_val u_val l_val : ℕ) (q : ℤ)
    (hq : IsUnit (q : ZMod d))
    (h : (l_val : ZMod d) = -(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d)) :
    (k_val : ZMod d) * (u_val : ZMod d) + (l_val : ZMod d) * (q : ZMod d) = 0 := by
  have h1 : (l_val : ZMod d) * (q : ZMod d) = -((q : ZMod d)⁻¹ * (q : ZMod d)) * ((k_val *
    u_val : ℕ) : ZMod d) := by rw [h]; ring
  have h2 : ((q : ZMod d)⁻¹ * (q : ZMod d) : ZMod d) = 1 := by exact ZMod.inv_mul_of_unit _ hq
  have h3 : (l_val : ZMod d) * (q : ZMod d) = -((k_val * u_val : ℕ) : ZMod d) := by simp_all
  have h4 : (k_val : ZMod d) * (u_val : ZMod d) = ((k_val * u_val : ℕ) : ZMod d) := by simp
  have h5 : (k_val : ZMod d) * (u_val : ZMod d) + (l_val : ZMod d) * (q : ZMod d) = 0 :=
    by rw [h4, h3]; ring
  assumption



lemma zmod_eq_zero_iff_eq_neg_inv_mul
    (d : ℕ) [NeZero d] (k_val u_val l_val : ℕ) (q : ℤ)
    (hq : IsUnit (q : ZMod d)) :
    ((k_val : ZMod d) * (u_val : ZMod d) + (l_val : ZMod d) * (q : ZMod d) = 0) ↔
    ((l_val : ZMod d) = -(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d)) :=
  ⟨zmod_eq_zero_forward d k_val u_val l_val q hq,
   zmod_eq_zero_backward d k_val u_val l_val q hq⟩



lemma residue_iff_zmod_eq
    (d : ℕ) [NeZero d] (k_val u_val l_val : ℕ) (q : ℤ) :
    (l_val % d = ZMod.val (-(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d))) ↔
    ((l_val : ZMod d) = -(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d)) := by
  have h_main : (l_val : ZMod d) = (l_val % d : ℕ) := by simp
  have h_val_nat_cast : (l_val : ZMod d).val = l_val % d := by simp
  have h_forward : (l_val % d = ZMod.val (-(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d))) →
    ((l_val : ZMod d) = -(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d)) := by
    intro heq
    have : (l_val : ZMod d).val = (-(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d)).val := by
      rw [h_val_nat_cast]; exact heq
    exact ZMod.val_injective _ this
  have h_backward : ((l_val : ZMod d) = -(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d)) →
    (l_val % d = ZMod.val (-(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d))) :=
      by intro heq; rw [← h_val_nat_cast, heq]
  have h_final : (l_val % d = ZMod.val (-(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d))) ↔
    ((l_val : ZMod d) = -(q : ZMod d)⁻¹ * ((k_val * u_val : ℕ) : ZMod d)) :=
      by exact ⟨h_forward, h_backward⟩
  assumption



lemma divisibility_iff_residue_class
    (n d : ℕ) [NeZero n] [NeZero d]
    (_hd_dvd : d ∣ n)
    (q : ℤ) (hq_coprime_d : Int.gcd q (d : ℤ) = 1)
    (k : ZMod n) (_hk : k ≠ 0)
    (u : (ZMod d)ˣ)
    (l : ZMod n) :
    let b := ZMod.val (-(q : ZMod d)⁻¹ * ((ZMod.val k * (u : ZMod d).val : ℕ) : ZMod d))
    ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q)) ↔
    (ZMod.val l % d = b) := by
  intro b
  have hq_unit : IsUnit (q : ZMod d) := q_isUnit_of_gcd d q hq_coprime_d
  rw [dvd_iff_zmod_eq_zero d (ZMod.val k) ((u : ZMod d).val) (ZMod.val l) q,
      zmod_eq_zero_iff_eq_neg_inv_mul d (ZMod.val k) ((u : ZMod d).val) (ZMod.val l) q hq_unit,
      ← residue_iff_zmod_eq d (ZMod.val k) ((u : ZMod d).val) (ZMod.val l) q]



lemma cond_sum_eq_residue_class_sum
    (n d : ℕ) [NeZero n] [NeZero d]
    (hd_dvd : d ∣ n)
    (q : ℤ) (hq_coprime_d : Int.gcd q (d : ℤ) = 1)
    (mq : ℕ)
    (k : ZMod n) (hk : k ≠ 0)
    (u : (ZMod d)ˣ) :
    let b := ZMod.val (-(q : ZMod d)⁻¹ * ((ZMod.val k * (u : ZMod d).val : ℕ) : ZMod d))
    (∑ l : ZMod n,
      if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mq) l‖
      else 0) =
    ∑ l : ZMod n,
      if (ZMod.val l % d = b)
      then ‖normalizedDFT n (intervalIndicator n mq) l‖
      else 0 := by
  simp only
  apply Finset.sum_congr rfl
  intro l _
  have h := divisibility_iff_residue_class n d hd_dvd q hq_coprime_d k hk u l
  simp only at h
  simp only [h]


lemma nonzero_of_val_mod_eq_pos (n d : ℕ) [NeZero n] [NeZero d]
    (l : ZMod n) (b : ℕ) (hb_pos : 1 ≤ b) (_hb_lt : b < d)
    (hmod : ZMod.val l % d = b) : l ≠ 0 := by
  intro h
  rw [h] at hmod
  have h₁ : ZMod.val (0 : ZMod n) = 0 := by
    simp [ZMod.val_zero]
  have h₂ : (0 : ℕ) % d = 0 := by
    simp [Nat.zero_mod]
  rw [h₁] at hmod
  simp_all only [ZMod.val_zero]
  (try omega)



lemma min_eq_val_of_two_mul_le (n : ℕ) [NeZero n] (l : ZMod n)
    (h2 : 2 * ZMod.val l ≤ n) :
    (min (ZMod.val l : ℝ) ((n : ℝ) - ZMod.val l)) = (ZMod.val l : ℝ) := by
  have h₁ : (ZMod.val l : ℝ) ≤ ((n : ℝ) - ZMod.val l) := by
    have h₃ : 2 * ZMod.val l ≤ n := h2
    have h₄ : (2 : ℝ) * (ZMod.val l : ℝ) ≤ (n : ℝ) := by
      norm_cast at h₃ ⊢
    have h₅ : (ZMod.val l : ℝ) ≤ (n : ℝ) - (ZMod.val l : ℝ) := by
      linarith
    exact h₅
  have h₂ : min (ZMod.val l : ℝ) ((n : ℝ) - ZMod.val l) = (ZMod.val l : ℝ) := by
    apply min_eq_left
    exact h₁
  exact h₂


lemma pointwise_bound_in_low_range (n d : ℕ) [NeZero n] [NeZero d]
    (mq : ℕ) (hmq_lo : 1 ≤ mq) (hmq_hi : mq < n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d)
    (l : ZMod n) (hmod : ZMod.val l % d = b) (hlow : 2 * ZMod.val l ≤ n) :
    ‖normalizedDFT n (intervalIndicator n mq) l‖ ≤
      1 / (2 * (ZMod.val l : ℝ)) := by
  have hl_ne : l ≠ 0 := nonzero_of_val_mod_eq_pos n d l b hb_pos hb_lt hmod
  have hbound := normalizedDFT_intervalIndicator_nonzero_bound n mq hmq_lo hmq_hi l hl_ne
  rw [min_eq_val_of_two_mul_le n l hlow] at hbound
  exact hbound



lemma val_eq_of_mod_eq_and_quot_eq (n d : ℕ) [NeZero n] [NeZero d]
    (b : ℕ) (_hb_lt : b < d)
    (l₁ l₂ : ZMod n)
    (h1 : ZMod.val l₁ % d = b)
    (h2 : ZMod.val l₂ % d = b)
    (heq : (ZMod.val l₁ - b) / d = (ZMod.val l₂ - b) / d) :
    ZMod.val l₁ = ZMod.val l₂ := by
  have hb1 : b ≤ ZMod.val l₁ := h1 ▸ Nat.mod_le _ _
  have hb2 : b ≤ ZMod.val l₂ := h2 ▸ Nat.mod_le _ _
  have hr1 := fiber_reconstruct d b (ZMod.val l₁) h1 hb1
  have hr2 := fiber_reconstruct d b (ZMod.val l₂) h2 hb2
  rw [heq] at hr1
  linarith



lemma quotient_injOn (n d : ℕ) [NeZero n] [NeZero d] (_hd_dvd : d ∣ n)
    (b : ℕ) (hb_lt : b < d) :
    Set.InjOn (fun l : ZMod n => (ZMod.val l - b) / d)
      (↑(Finset.univ.filter (fun l : ZMod n => ZMod.val l % d = b ∧ 2 * ZMod.val l ≤ n))) := by
  intro l₁ hl₁ l₂ hl₂ heq
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hl₁ hl₂
  have hval := val_eq_of_mod_eq_and_quot_eq n d b hb_lt l₁ l₂ hl₁.1 hl₂.1 heq
  exact ZMod.val_injective n hval


lemma quotient_mem_range (n d : ℕ) [NeZero n] [NeZero d] (_hd_dvd : d ∣ n)
    (b : ℕ) (_hb_pos : 1 ≤ b) (_hb_lt : b < d)
    (l : ZMod n) (hl : ZMod.val l % d = b ∧ 2 * ZMod.val l ≤ n) :
    (ZMod.val l - b) / d ∈ Finset.range (n / (2 * d) + 1) := by
  have h₁ : (ZMod.val l - b) / d < n / (2 * d) + 1 := by
    have h₃ : (ZMod.val l - b) / d ≤ (ZMod.val l) / d := by
      have h₄ : ZMod.val l - b ≤ ZMod.val l := by
        have h₅ : b ≤ ZMod.val l := by
          have h₁₂ : b ≤ ZMod.val l := by
            by_contra h
            have h₁₄ : ZMod.val l % d = ZMod.val l := by
              have h₁₅ : ZMod.val l < d := by
                omega
              have h₁₆ : ZMod.val l % d = ZMod.val l := by
                rw [Nat.mod_eq_of_lt h₁₅]
              exact h₁₆
            omega
          exact h₁₂
        omega
      have h₅ : (ZMod.val l - b) / d ≤ (ZMod.val l) / d := by
        apply Nat.div_le_div_right
        omega
      exact h₅
    have h₄ : (ZMod.val l) / d ≤ n / (2 * d) := by
      have h₆ : ZMod.val l ≤ n / 2 := by
        omega
      have h₇ : (ZMod.val l) / d ≤ (n / 2) / d := by
        apply Nat.div_le_div_right
        omega
      have h₈ : (n / 2) / d ≤ n / (2 * d) := by
        have h₉ : (n / 2) / d = n / (2 * d) := by
          rw [← Nat.div_div_eq_div_mul]
        rw [h₉]
      calc
        (ZMod.val l) / d ≤ (n / 2) / d := h₇
        _ ≤ n / (2 * d) := h₈
    have h₅ : (ZMod.val l - b) / d ≤ n / (2 * d) := by
      calc
        (ZMod.val l - b) / d ≤ (ZMod.val l) / d := h₃
        _ ≤ n / (2 * d) := h₄
    omega
  exact Finset.mem_range.mpr h₁



lemma summand_eq (n d : ℕ) [NeZero n] [NeZero d]
    (b : ℕ) (_hb_pos : 1 ≤ b) (_hb_lt : b < d)
    (l : ZMod n) (hl : ZMod.val l % d = b ∧ 2 * ZMod.val l ≤ n) :
    (1 : ℝ) / (2 * (ZMod.val l : ℝ)) =
    (1 : ℝ) / (2 * ((b : ℝ) + ((ZMod.val l - b) / d : ℕ) * (d : ℝ))) := by
  have hb_le : b ≤ ZMod.val l := hl.1 ▸ Nat.mod_le _ _
  have hnat := fiber_reconstruct d b (ZMod.val l) hl.1 hb_le
  congr 1
  congr 1
  exact_mod_cast hnat.symm



lemma rhs_term_nonneg (b d : ℕ) (hb_pos : 1 ≤ b) (j : ℕ) :
    (0 : ℝ) ≤ (1 : ℝ) / (2 * ((b : ℝ) + (j : ℝ) * (d : ℝ))) := by
  have h₁ : (0 : ℝ) < 2 * ((b : ℝ) + (j : ℝ) * (d : ℝ)) := by
    have h₅ : (0 : ℝ) < 2 * ((b : ℝ) + (j : ℝ) * (d : ℝ)) := by positivity
    exact h₅
  have h₂ : (0 : ℝ) ≤ (1 : ℝ) / (2 * ((b : ℝ) + (j : ℝ) * (d : ℝ))) := by
    apply div_nonneg
    · norm_num
    · linarith
  exact h₂



lemma sum_val_reciprocal_le_sum_range (n d : ℕ) [NeZero n] [NeZero d] (_hn : 2 ≤ n)
    (hd_dvd : d ∣ n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    (∑ l : ZMod n,
      if (ZMod.val l % d = b ∧ 2 * ZMod.val l ≤ n)
      then (1 : ℝ) / (2 * (ZMod.val l : ℝ))
      else 0) ≤
    ∑ j ∈ Finset.range (n / (2 * d) + 1), (1 : ℝ) / (2 * ((b : ℝ) + (j : ℝ) * (d : ℝ))) := by
  rw [← Finset.sum_filter]
  set S := Finset.univ.filter (fun l : ZMod n => ZMod.val l % d = b ∧ 2 * ZMod.val l ≤ n)
  set φ := fun l : ZMod n => (ZMod.val l - b) / d
  set g := fun j : ℕ => (1 : ℝ) / (2 * ((b : ℝ) + (j : ℝ) * (d : ℝ)))
  have hsummand : ∀ l ∈ S, (1 : ℝ) / (2 * (ZMod.val l : ℝ)) = g (φ l) := by
    intro l hl
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    exact summand_eq n d b hb_pos hb_lt l hl
  calc ∑ l ∈ S, (1 : ℝ) / (2 * (ZMod.val l : ℝ))
      = ∑ l ∈ S, g (φ l) := Finset.sum_congr rfl hsummand
    _ = ∑ j ∈ S.image φ, g j := by
        rw [Finset.sum_image]
        exact fun l₁ hl₁ l₂ hl₂ heq =>
          quotient_injOn n d hd_dvd b hb_lt (Finset.mem_coe.mpr hl₁) (Finset.mem_coe.mpr hl₂) heq
    _ ≤ ∑ j ∈ Finset.range (n / (2 * d) + 1), g j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          rw [Finset.mem_image] at hj
          obtain ⟨l, hl, rfl⟩ := hj
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hl
          exact quotient_mem_range n d hd_dvd b hb_pos hb_lt l hl
        · intro j _ _
          exact rhs_term_nonneg b d hb_pos j



lemma low_range_le_sum_over_j (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd_dvd : d ∣ n) (mq : ℕ) (hmq_lo : 1 ≤ mq) (hmq_hi : mq < n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    (∑ l : ZMod n,
      if (ZMod.val l % d = b ∧ 2 * ZMod.val l ≤ n)
      then ‖normalizedDFT n (intervalIndicator n mq) l‖
      else 0) ≤
    ∑ j ∈ Finset.range (n / (2 * d) + 1), (1 : ℝ) / (2 * ((b : ℝ) + (j : ℝ) * (d : ℝ))) := by
  calc (∑ l : ZMod n,
        if (ZMod.val l % d = b ∧ 2 * ZMod.val l ≤ n)
        then ‖normalizedDFT n (intervalIndicator n mq) l‖
        else 0)
      ≤ (∑ l : ZMod n,
        if (ZMod.val l % d = b ∧ 2 * ZMod.val l ≤ n)
        then (1 : ℝ) / (2 * (ZMod.val l : ℝ))
        else 0) := by
        apply Finset.sum_le_sum
        intro l _
        split_ifs with h
        · exact pointwise_bound_in_low_range n d mq hmq_lo hmq_hi b hb_pos hb_lt l h.1 h.2
        · exact le_refl 0
    _ ≤ ∑ j ∈ Finset.range (n / (2 * d) + 1),
          (1 : ℝ) / (2 * ((b : ℝ) + (j : ℝ) * (d : ℝ))) := by
        exact sum_val_reciprocal_le_sum_range n d hn hd_dvd b hb_pos hb_lt


lemma sum_range_split (J : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range (J + 1), f j = f 0 + ∑ j ∈ Finset.Icc 1 J, f j := by
  have h : Finset.range (J + 1) = {0} ∪ Finset.Icc 1 J := by
    ext x; simp [Finset.mem_range, Finset.mem_Icc]; omega
  have hdisj : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 J) := by
    simp [Finset.mem_Icc]
  rw [h, Finset.sum_union hdisj, Finset.sum_singleton]


lemma two_mul_add_one_le_real (M n : ℕ) (hM : M ≤ n) :
    (2 : ℝ) * ↑M + 1 ≤ 2 * ↑n + 1 := by
  norm_cast
  omega


lemma two_mul_add_one_pos (M : ℕ) :
    (0 : ℝ) < 2 * ↑M + 1 := by
  positivity



theorem log_two_n_plus_one_le_one_plus_log (n : ℕ) (hn : 2 ≤ n) :
    Real.log (2 * ↑n + 1) ≤ 1 + Real.log ↑n := by
  have h₁ : (n : ℝ) ≥ 2 := by exact_mod_cast hn
  have h₄ : (2 : ℝ) * ↑n + 1 ≤ (n : ℝ) * Real.exp 1 := by
    have h₅ : Real.exp 1 ≥ 2 + 1 / 2 := by
      have := Real.exp_one_gt_d9
      norm_num at this ⊢
      linarith
    have h₆ : (2 : ℝ) * ↑n + 1 ≤ (n : ℝ) * Real.exp 1 := by
      have h₈ : (n : ℝ) * Real.exp 1 ≥ (n : ℝ) * (2 + 1 / 2) := by
        nlinarith
      linarith
    exact h₆
  have h₅ : Real.log (2 * ↑n + 1) ≤ Real.log ((n : ℝ) * Real.exp 1) := by
    apply Real.log_le_log
    · positivity
    · exact h₄
  have h₆ : Real.log ((n : ℝ) * Real.exp 1) = Real.log (n : ℝ) + Real.log (Real.exp 1) := by
    rw [Real.log_mul (by positivity) (by positivity)]
  have h₇ : Real.log (Real.exp 1) = 1 := by
    rw [Real.log_exp]
  linarith



theorem sum_range_eq_sum_Icc (M : ℕ) :
    ∑ j ∈ Finset.range M, (1 : ℝ) / ((j : ℝ) + 1) = ∑ u ∈ Finset.Icc 1 M, (↑u)⁻¹ := by
  have h₁ : ∑ j ∈ Finset.range M, (1 : ℝ) / ((j : ℝ) + 1) = ∑ j ∈ Finset.range M,
    ((j + 1 : ℕ) : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro j _
    have h₂ : (1 : ℝ) / ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ)⁻¹ := by
      field_simp [Nat.cast_add_one_ne_zero]
      ring_nf
      norm_cast
    rw [h₂]
  rw [h₁]
  have h₂ : ∑ j ∈ Finset.range M, ((j + 1 : ℕ) : ℝ)⁻¹ = ∑ u ∈ Finset.Icc 1 M, (u : ℝ)⁻¹ := by
    have h₃ : ∑ j ∈ Finset.range M, ((j + 1 : ℕ) : ℝ)⁻¹ = ∑ u ∈ Finset.Icc 1 M, (u : ℝ)⁻¹ := by
      have h₅ : Finset.sum (Finset.range M) (fun j =>
        ((j + 1 : ℕ) : ℝ)⁻¹) = Finset.sum (Finset.Icc 1 M) (fun u => (u : ℝ)⁻¹) := by
        apply Eq.symm
        apply Finset.sum_bij' (fun (u : ℕ) _ => u - 1) (fun (j : ℕ) _ => j + 1) <;>
          simp_all [Finset.mem_Icc, Finset.mem_range]
        omega
      rw [h₅]
    rw [h₃]
  rw [h₂]


lemma harmonic_range_le_one_plus_log (M n : ℕ) (hn : 2 ≤ n) (hM : M ≤ n) :
    ∑ j ∈ Finset.range M, (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 + Real.log ↑n := by
  by_cases hM0 : M = 0
  · subst hM0
    simp only [Finset.range_zero, Finset.sum_empty]
    exact one_plus_log_nonneg n hn
  · push Not at hM0
    have hM_pos : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM0
    rw [sum_range_eq_sum_Icc M]
    calc ∑ u ∈ Finset.Icc 1 M, (↑u)⁻¹
        ≤ Real.log (2 * ↑M + 1) := harmonic_Icc_le_log_odd M hM_pos
      _ ≤ Real.log (2 * ↑n + 1) := by
          apply Real.log_le_log (two_mul_add_one_pos M)
          exact two_mul_add_one_le_real M n hM
      _ ≤ 1 + Real.log ↑n := log_two_n_plus_one_le_one_plus_log n hn



lemma summand_bound (d : ℕ) (hd_pos : 0 < d) (b : ℕ) (hb_pos : 1 ≤ b)
    (j : ℕ) (hj : 1 ≤ j) :
    (1 : ℝ) / (2 * ((b : ℝ) + (j : ℝ) * (d : ℝ))) ≤
    (1 : ℝ) / (2 * ((j : ℝ) * (d : ℝ))) := by
  have h₃ : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast (by positivity)
  have h₉ : (1 : ℝ) / (2 * ((b : ℝ) + (j : ℝ) * (d : ℝ))) ≤ (1 : ℝ) / (2 * ((j : ℝ) * (d : ℝ))) :=
    by
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  exact h₉



lemma sum_factor_Icc (n d : ℕ) (hd_pos : 0 < d) :
    ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
      (1 : ℝ) / (2 * ((j : ℝ) * (d : ℝ))) =
    (∑ j ∈ Finset.Icc 1 (n / (2 * d)), (1 : ℝ) / (j : ℝ)) / (2 * (d : ℝ)) := by
  have h₁ : ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
    (1 : ℝ) / (2 * ((j : ℝ) * (d : ℝ))) = ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
      ((1 : ℝ) / (j : ℝ)) / (2 * (d : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have h₂ : j ∈ Finset.Icc 1 (n / (2 * d)) := hj
    have h₃ : 1 ≤ j := by
      simp [Finset.mem_Icc] at h₂
      linarith
    have h₄ : 0 < (j : ℝ) := by
      norm_cast
    have h₅ : 0 < (d : ℝ) := by
      norm_cast
    have h₆ : 0 < (j : ℝ) * (d : ℝ) := by positivity
    have h₇ : 0 < 2 * ((j : ℝ) * (d : ℝ)) := by positivity
    field_simp [h₄.ne', h₅.ne', h₆.ne', h₇.ne']
  have h₂ : ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
    ((1 : ℝ) / (j : ℝ)) / (2 * (d : ℝ)) = (∑ j ∈ Finset.Icc 1 (n / (2 * d)),
      (1 : ℝ) / (j : ℝ)) / (2 * (d : ℝ)) := by
    calc
      ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
        ((1 : ℝ) / (j : ℝ)) / (2 * (d : ℝ)) = ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
          (1 / (j : ℝ) : ℝ) / (2 * (d : ℝ)) := by simp
      _ = (∑ j ∈ Finset.Icc 1 (n / (2 * d)), (1 / (j : ℝ) : ℝ)) / (2 * (d : ℝ)) := by
        rw [Finset.sum_div]
  rw [h₁, h₂]



lemma sum_Icc_eq_sum_range (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / (j : ℝ) =
    ∑ j ∈ Finset.range J, (1 : ℝ) / ((j : ℝ) + 1) := by
  induction J with
  | zero =>
    simp
  | succ J ih =>
    simp_all [Finset.sum_Icc_succ_top, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]



lemma harmonic_sum_over_Icc_le_log_div
    (n d : ℕ) (hn : 2 ≤ n) (hd_pos : 0 < d) (_hd_le : d ≤ n) :
    ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
      (1 : ℝ) / (2 * ((j : ℝ) * (d : ℝ))) ≤
    (1 + Real.log ↑n) / (2 * ↑d) := by
  rw [sum_factor_Icc n d hd_pos, sum_Icc_eq_sum_range]
  apply div_le_div_of_nonneg_right
  · exact harmonic_range_le_one_plus_log _ n hn (Nat.div_le_self n (2 * d))
  · positivity



lemma tail_sum_le_log_div
    (n d : ℕ) (hn : 2 ≤ n) (hd_pos : 0 < d) (hd_le : d ≤ n)
    (b : ℕ) (hb_pos : 1 ≤ b) :
    ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
      (1 : ℝ) / (2 * ((b : ℝ) + (j : ℝ) * (d : ℝ))) ≤
    (1 + Real.log ↑n) / (2 * ↑d) := by
  calc ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
        (1 : ℝ) / (2 * ((b : ℝ) + (j : ℝ) * (d : ℝ)))
      ≤ ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
        (1 : ℝ) / (2 * ((j : ℝ) * (d : ℝ))) := by
        apply Finset.sum_le_sum
        intro j hj
        exact summand_bound d hd_pos b hb_pos j (by exact (Finset.mem_Icc.mp hj).1)
    _ ≤ (1 + Real.log ↑n) / (2 * ↑d) :=
        harmonic_sum_over_Icc_le_log_div n d hn hd_pos hd_le



lemma arith_prog_sum_le_low
    (n d : ℕ) (hn : 2 ≤ n) (hd_pos : 0 < d) (hd_le : d ≤ n)
    (b : ℕ) (hb_pos : 1 ≤ b) (_hb_lt : b < d) :
    ∑ j ∈ Finset.range (n / (2 * d) + 1),
      (1 : ℝ) / (2 * ((b : ℝ) + (j : ℝ) * (d : ℝ))) ≤
    1 / (2 * (b : ℝ)) + (1 + Real.log ↑n) / (2 * ↑d) := by
  rw [sum_range_split]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  gcongr
  exact tail_sum_le_log_div n d hn hd_pos hd_le b hb_pos



lemma low_range_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd_dvd : d ∣ n)
    (mq : ℕ) (hmq_lo : 1 ≤ mq) (hmq_hi : mq < n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    (∑ l : ZMod n,
      if (ZMod.val l % d = b ∧ 2 * ZMod.val l ≤ n)
      then ‖normalizedDFT n (intervalIndicator n mq) l‖
      else 0) ≤
    1 / (2 * (b : ℝ)) + (1 + Real.log ↑n) / (2 * ↑d) := by
  have hd_pos : (0 : ℕ) < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd_le : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hd_dvd
  have step1 := low_range_le_sum_over_j n d hn hd_dvd mq hmq_lo hmq_hi b hb_pos hb_lt
  have step2 := arith_prog_sum_le_low n d hn hd_pos hd_le b hb_pos hb_lt
  linarith



lemma high_range_pointwise_bound
    (n : ℕ) [NeZero n] (mq : ℕ) (hmq_lo : 1 ≤ mq) (hmq_hi : mq < n)
    (d : ℕ) (b : ℕ) (hb_pos : 1 ≤ b)
    (l : ZMod n) (hl_mod : ZMod.val l % d = b) (hl_high : ¬(2 * ZMod.val l ≤ n)) :
    ‖normalizedDFT n (intervalIndicator n mq) l‖ ≤
      1 / (2 * ((n : ℝ) - ZMod.val l)) := by
  have hval_pos : 0 < ZMod.val l := by
    have h1 : 0 < ZMod.val l % d := by rw [hl_mod]; exact hb_pos
    exact Nat.pos_of_ne_zero (by intro h; simp [h] at h1)
  have hl_ne : l ≠ 0 := by
    intro h
    rw [h, ZMod.val_zero] at hval_pos
    exact Nat.lt_irrefl 0 hval_pos
  have hbound := normalizedDFT_intervalIndicator_nonzero_bound n mq hmq_lo hmq_hi l hl_ne
  have hgt : n < 2 * ZMod.val l := by omega
  have hmin : min (↑(ZMod.val l)) ((↑n : ℝ) - ↑(ZMod.val l)) = (↑n : ℝ) - ↑(ZMod.val l) := by
    apply min_eq_right
    have : (↑n : ℝ) < 2 * (↑(ZMod.val l) : ℝ) := by exact_mod_cast hgt
    linarith
  rwa [hmin] at hbound



lemma quot_lt
    (n d : ℕ) (hd_dvd : d ∣ n) (b : ℕ) (hb_pos : 1 ≤ b) (_hb_lt : b < d)
    (v : ℕ) (hv_lt : v < n) (hv_mod : v % d = b) :
    v / d < n / d := by
  have h_v_eq : d * (v / d) + (v % d) = v := Nat.div_add_mod v d
  have h_n_eq : d * (n / d) = n := Nat.mul_div_cancel' hd_dvd
  have h_mul_lt : d * (v / d) < d * (n / d) := by omega
  exact Nat.lt_of_mul_lt_mul_left h_mul_lt



lemma nat_sub_mul_add (A B d b : ℕ) (hBA : B < A) (hbd : b < d) :
    d * A - (d * B + b) = d * (A - B - 1) + (d - b) := by
  have e1 : d * (A - B) = d * A - d * B := Nat.mul_sub_left_distrib d A B
  have e2 : d * (A - B - 1) + d = d * (A - B) := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  have e3 : d * B + d ≤ d * A := by
    have hmul : d * (B + 1) ≤ d * A := by
      apply Nat.mul_le_mul_left
      omega
    rw [Nat.mul_add, Nat.mul_one] at hmul
    exact hmul
  omega



lemma n_sub_v_eq
    (n d : ℕ) (hd_dvd : d ∣ n) (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d)
    (v : ℕ) (hv_lt : v < n) (hv_mod : v % d = b)
    (hquot : v / d < n / d) :
    n - v = d * (n / d - v / d - 1) + (d - b) := by
  have hn_eq : n = d * (n / d) := by
    have h0 : n % d = 0 := Nat.dvd_iff_mod_eq_zero.mp hd_dvd
    have := Nat.div_add_mod n d
    omega
  have hv_eq : v = d * (v / d) + b := by
    have := Nat.div_add_mod v d
    omega
  have _hb := hb_pos
  have key := nat_sub_mul_add (n / d) (v / d) d b hquot hb_lt
  omega



lemma n_sub_v_mod_eq_d_sub_b
    (n d : ℕ) (hd_dvd : d ∣ n) (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d)
    (v : ℕ) (hv_lt : v < n) (hv_mod : v % d = b) :
    (n - v) % d = d - b := by
  have hquot := quot_lt n d hd_dvd b hb_pos hb_lt v hv_lt hv_mod
  rw [n_sub_v_eq n d hd_dvd b hb_pos hb_lt v hv_lt hv_mod hquot]
  have hdb : d - b < d := by omega
  rw [Nat.add_comm]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hdb


lemma d_sub_b_le_n_sub_v
    (n d : ℕ) (hd_dvd : d ∣ n) (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d)
    (v : ℕ) (hv_lt : v < n) (hv_mod : v % d = b) (_hv_big : n < 2 * v) :
    d - b ≤ n - v := by
  by_contra h
  push Not at h
  have hdb_lt_d : d - b < d := Nat.sub_lt (by omega) hb_pos
  have hnv_lt_d : n - v < d := by omega
  have hmod : (n - v) % d = d - b := n_sub_v_mod_eq_d_sub_b n d hd_dvd b hb_pos hb_lt v hv_lt hv_mod
  rw [Nat.mod_eq_of_lt hnv_lt_d] at hmod
  omega



lemma n_modEq_d_of_dvd
    (n d : ℕ) (hd_dvd : d ∣ n) :
    n ≡ d [MOD d] := by
  simp [Nat.ModEq, Nat.mod_self, Nat.dvd_iff_mod_eq_zero.mp hd_dvd]



lemma v_modEq_b_of_mod
    (d : ℕ) (b : ℕ) (hb_lt : b < d)
    (v : ℕ) (hv_mod : v % d = b) :
    v ≡ b [MOD d] := by
  simp [Nat.ModEq, hv_mod, Nat.mod_eq_of_lt hb_lt]



lemma complement_div_d_dvd
    (n d : ℕ) (hd_dvd : d ∣ n) (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d)
    (v : ℕ) (hv_lt : v < n) (hv_mod : v % d = b) (hv_big : n < 2 * v) :
    d ∣ (n - v - (d - b)) := by
  have h_le : d - b ≤ n - v := d_sub_b_le_n_sub_v n d hd_dvd b hb_pos hb_lt v hv_lt hv_mod hv_big
  have h1 : n ≡ d [MOD d] := n_modEq_d_of_dvd n d hd_dvd
  have h2 : v ≡ b [MOD d] := v_modEq_b_of_mod d b hb_lt v hv_mod
  have hv_le : v ≤ n := le_of_lt hv_lt
  have hb_le : b ≤ d := le_of_lt hb_lt
  have h3 : n - v ≡ d - b [MOD d] := Nat.ModEq.sub hv_le hb_le h1 h2
  exact (Nat.modEq_iff_dvd' h_le).mp (Nat.ModEq.comm.mpr h3)



lemma sub_d_sub_b_le_sub_v
    (n d : ℕ) (_hd_pos : 0 < d) (_hd_dvd : d ∣ n)
    (b : ℕ) (_hb_pos : 1 ≤ b) (_hb_lt : b < d)
    (v : ℕ) (_hv_lt : v < n) (_hv_mod : v % d = b) (_hv_big : n < 2 * v) :
    n - v - (d - b) ≤ n - v := by
  exact Nat.sub_le (n - v) (d - b)



lemma n_sub_v_le_half_n
    (n : ℕ) (v : ℕ) (hv_lt : v < n) (hv_big : n < 2 * v) :
    n - v ≤ n / 2 := by
  omega



lemma complement_j_in_range
    (n d : ℕ) (hd_pos : 0 < d) (hd_dvd : d ∣ n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d)
    (v : ℕ) (hv_lt : v < n) (hv_mod : v % d = b) (hv_big : n < 2 * v) :
    (n - v - (d - b)) / d < n / (2 * d) + 1 := by
  calc (n - v - (d - b)) / d
      ≤ (n - v) / d :=
        Nat.div_le_div_right (sub_d_sub_b_le_sub_v n d hd_pos hd_dvd b hb_pos hb_lt v hv_lt hv_mod
          hv_big)
    _ ≤ (n / 2) / d := Nat.div_le_div_right (n_sub_v_le_half_n n v hv_lt hv_big)
    _ = n / (2 * d) := Nat.div_div_eq_div_mul n 2 d
    _ < n / (2 * d) + 1 := Nat.lt_succ_of_le (le_refl _)


lemma complement_eq_arith_prog
    (n d : ℕ) (hd_dvd : d ∣ n) (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d)
    (v : ℕ) (hv_lt : v < n) (hv_mod : v % d = b) (hv_big : n < 2 * v) :
    n - v = (d - b) + ((n - v - (d - b)) / d) * d := by
  have h_le : d - b ≤ n - v := d_sub_b_le_n_sub_v n d hd_dvd b hb_pos hb_lt v hv_lt hv_mod hv_big
  have h_dvd : d ∣ (n - v - (d - b)) :=
    complement_div_d_dvd n d hd_dvd b hb_pos hb_lt v hv_lt hv_mod hv_big
  have h_cancel : (n - v - (d - b)) / d * d = n - v - (d - b) := Nat.div_mul_cancel h_dvd
  omega


lemma complement_eq_arith_prog_real
    (n d : ℕ) (hd_dvd : d ∣ n) (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d)
    (v : ℕ) (hv_lt : v < n) (hv_mod : v % d = b) (hv_big : n < 2 * v) :
    (n : ℝ) - v = (d : ℝ) - b + ((n - v - (d - b)) / d : ℕ) * d := by
  have hnat := complement_eq_arith_prog n d hd_dvd b hb_pos hb_lt v hv_lt hv_mod hv_big
  have hvn : v ≤ n := le_of_lt hv_lt
  have hbd : b ≤ d := le_of_lt hb_lt
  have hdb_le : d - b ≤ n - v := d_sub_b_le_n_sub_v n d hd_dvd b hb_pos hb_lt v hv_lt hv_mod hv_big
  have hnat_cast : ((n - v : ℕ) : ℝ) = (((d - b) + ((n - v - (d - b)) / d) * d : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_sub hvn] at hnat_cast
  rw [Nat.cast_add, Nat.cast_sub hbd, Nat.cast_mul] at hnat_cast
  exact hnat_cast


lemma eq_of_dvd_div_eq (a b d : ℕ) (_hd : 0 < d) (ha : d ∣ a) (hb : d ∣ b)
    (h : a / d = b / d) : a = b := by
  have h₁ : a = d * (a / d) := by
    have h₂ : d * (a / d) = a := by
      apply Nat.mul_div_cancel'
      exact ha
    linarith
  have h₂ : b = d * (b / d) := by
    have h₃ : d * (b / d) = b := by
      apply Nat.mul_div_cancel'
      exact hb
    linarith
  have h₃ : a = b := by
    rw [h₁, h₂, h]
  exact h₃



lemma complement_map_injective
    (n d : ℕ) (hd_dvd : d ∣ n) (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    ∀ v₁ v₂ : ℕ,
      v₁ < n → v₁ % d = b → n < 2 * v₁ →
      v₂ < n → v₂ % d = b → n < 2 * v₂ →
      (n - v₁ - (d - b)) / d = (n - v₂ - (d - b)) / d →
      v₁ = v₂ := by
  intro v₁ v₂ hv₁_lt hv₁_mod hv₁_big hv₂_lt hv₂_mod hv₂_big hdiv_eq
  have hd_pos : 0 < d := by omega
  have h_dvd₁ := complement_div_d_dvd n d hd_dvd b hb_pos hb_lt v₁ hv₁_lt hv₁_mod hv₁_big
  have h_dvd₂ := complement_div_d_dvd n d hd_dvd b hb_pos hb_lt v₂ hv₂_lt hv₂_mod hv₂_big
  have h_le₁ := d_sub_b_le_n_sub_v n d hd_dvd b hb_pos hb_lt v₁ hv₁_lt hv₁_mod hv₁_big
  have h_le₂ := d_sub_b_le_n_sub_v n d hd_dvd b hb_pos hb_lt v₂ hv₂_lt hv₂_mod hv₂_big
  have h_eq := eq_of_dvd_div_eq _ _ d hd_pos h_dvd₁ h_dvd₂ hdiv_eq
  omega



lemma arith_prog_summand_nonneg
    (d b : ℕ) (_hb_pos : 1 ≤ b) (hb_lt : b < d) (j : ℕ) :
    (0 : ℝ) ≤ (1 : ℝ) / (2 * ((d : ℝ) - b + j * d)) := by
  have h₁ : (d : ℝ) - b + j * d > 0 := by
    have h₂ : (d : ℝ) - b > 0 := by
      have h₃ : (b : ℝ) < d := by exact_mod_cast hb_lt
      linarith
    have h₄ : (j : ℝ) * d ≥ 0 := by
      nlinarith
    linarith
  have h₃ : (0 : ℝ) ≤ (1 : ℝ) / (2 * ((d : ℝ) - b + j * d)) := by
    apply (div_nonneg) <;>
      (try positivity)
  exact h₃



lemma reindex_map_injOn
    (n d : ℕ) [NeZero n] [NeZero d] (_hn : 2 ≤ n)
    (hd_dvd : d ∣ n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    Set.InjOn (fun l : ZMod n => (n - ZMod.val l - (d - b)) / d)
      (Finset.univ.filter (fun l : ZMod n =>
        ZMod.val l % d = b ∧ ¬(2 * ZMod.val l ≤ n)) : Set (ZMod n)) := by
  intro l₁ hl₁ l₂ hl₂ heq
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hl₁ hl₂
  have hv₁_lt := ZMod.val_lt l₁
  have hv₂_lt := ZMod.val_lt l₂
  have hv₁_mod := hl₁.1
  have hv₂_mod := hl₂.1
  have hv₁_big : n < 2 * ZMod.val l₁ := by omega
  have hv₂_big : n < 2 * ZMod.val l₂ := by omega
  have hval_eq : ZMod.val l₁ = ZMod.val l₂ :=
    complement_map_injective n d hd_dvd b hb_pos hb_lt
      (ZMod.val l₁) (ZMod.val l₂)
      hv₁_lt hv₁_mod hv₁_big
      hv₂_lt hv₂_mod hv₂_big
      heq
  exact ZMod.val_injective n hval_eq



lemma reindex_filtered_sum
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd_dvd : d ∣ n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    (∑ l ∈ Finset.univ.filter (fun l : ZMod n =>
        ZMod.val l % d = b ∧ ¬(2 * ZMod.val l ≤ n)),
      (1 : ℝ) / (2 * ((n : ℝ) - ZMod.val l))) =
    ∑ j ∈ (Finset.univ.filter (fun l : ZMod n =>
        ZMod.val l % d = b ∧ ¬(2 * ZMod.val l ≤ n))).image
      (fun l : ZMod n => (n - ZMod.val l - (d - b)) / d),
      (1 : ℝ) / (2 * ((d : ℝ) - b + j * d)) := by
  rw [Finset.sum_image (fun l hl l' hl' heq =>
    reindex_map_injOn n d hn hd_dvd b hb_pos hb_lt (Finset.mem_coe.mpr hl) (Finset.mem_coe.mpr hl')
      heq)]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
  have hv_lt := ZMod.val_lt l
  have hv_mod := hl.1
  have hv_big : n < 2 * ZMod.val l := by omega
  have heq :=
    complement_eq_arith_prog_real n d hd_dvd b hb_pos hb_lt (ZMod.val l) hv_lt hv_mod hv_big
  rw [show (2 : ℝ) * ((n : ℝ) - ZMod.val l) = 2 * ((d : ℝ) - b + ((n - ZMod.val l - (d - b)) /
    d : ℕ) * d) from by rw [heq]]



lemma image_subset_range
    (n d : ℕ) [NeZero n] [NeZero d] (_hn : 2 ≤ n)
    (hd_dvd : d ∣ n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    (Finset.univ.filter (fun l : ZMod n =>
        ZMod.val l % d = b ∧ ¬(2 * ZMod.val l ≤ n))).image
      (fun l : ZMod n => (n - ZMod.val l - (d - b)) / d) ⊆
    Finset.range (n / (2 * d) + 1) := by
  rw [Finset.image_subset_iff]
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
  rw [Finset.mem_range]
  exact complement_j_in_range n d (NeZero.pos d) hd_dvd b hb_pos hb_lt
    (ZMod.val l) (ZMod.val_lt l) hl.1 (by omega)



lemma high_range_reindex_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd_dvd : d ∣ n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    (∑ l : ZMod n,
      if (ZMod.val l % d = b ∧ ¬(2 * ZMod.val l ≤ n))
      then (1 : ℝ) / (2 * ((n : ℝ) - ZMod.val l))
      else 0) ≤
    ∑ j ∈ Finset.range (n / (2 * d) + 1),
      (1 : ℝ) / (2 * ((d : ℝ) - b + j * d)) := by
  rw [← Finset.sum_filter]
  rw [reindex_filtered_sum n d hn hd_dvd b hb_pos hb_lt]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (image_subset_range n d hn hd_dvd b hb_pos hb_lt)
    (fun j _ _ => arith_prog_summand_nonneg d b hb_pos hb_lt j)



lemma sum_range_le_sum_Icc (n d : ℕ) (hd_pos : 0 < d)
    (b : ℕ) (_hb_pos : 1 ≤ b) (hb_lt : b < d) :
    ∑ j ∈ Finset.range (n / (2 * d)),
      (1 : ℝ) / (2 * ((d : ℝ) - b + ((j : ℝ) + 1) * d)) ≤
    ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
      (1 : ℝ) / (2 * ((j : ℝ) * (d : ℝ))) := by
  have h₁ : ∑ j ∈ Finset.range (n / (2 * d)),
    (1 : ℝ) / (2 * ((d : ℝ) - b + ((j : ℝ) + 1) * d)) = ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
      (1 : ℝ) / (2 * ((d : ℝ) - b + ((j : ℝ) - 1 + 1) * d)) := by
    have h₂ : ∑ j ∈ Finset.range (n / (2 * d)),
      (1 : ℝ) / (2 * ((d : ℝ) - b + ((j : ℝ) + 1) * d)) = ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
        (1 : ℝ) / (2 * ((d : ℝ) - b + ((j : ℝ) - 1 + 1) * d)) := by
      apply Eq.symm
      apply Finset.sum_bij' (fun j _ => j - 1) (fun j _ => j + 1) <;>
        simp_all [Finset.mem_Icc, Finset.mem_range]
      omega
    rw [h₂]
  rw [h₁]
  have h₃ : ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
    (1 : ℝ) / (2 * ((d : ℝ) - b + ((j : ℝ) - 1 + 1) * d)) ≤ ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
      (1 : ℝ) / (2 * ((j : ℝ) * (d : ℝ))) := by
    apply Finset.sum_le_sum
    intro j hj
    have h₄ : (j : ℕ) ∈ Finset.Icc 1 (n / (2 * d)) := hj
    have h₅ : 1 ≤ j := by
      simp only [Finset.mem_Icc] at h₄
      exact h₄.1
    have h₉ : (d : ℝ) - b ≥ 0 := by
      have h₁₀ : (d : ℕ) ≥ b := by
        omega
      have h₁₁ : (d : ℝ) ≥ (b : ℝ) := by
        exact_mod_cast h₁₀
      linarith
    have h₁₀ : (1 : ℝ) / (2 * ((d : ℝ) - b + ((j : ℝ) - 1 + 1) * d)) ≤ (1 : ℝ) / (2 * ((j : ℝ) *
      (d : ℝ))) := by
      have h₂₁ : (2 * ((d : ℝ) - b + ((j : ℝ) - 1 + 1) * d) : ℝ) ≥ (2 * ((j : ℝ) * (d : ℝ)) : ℝ) :=
        by
        nlinarith
      have h₂₇ : (1 : ℝ) / (2 * ((d : ℝ) - b + ((j : ℝ) - 1 + 1) * d)) ≤ (1 : ℝ) / (2 * ((j : ℝ) *
        (d : ℝ))) := by
        apply one_div_le_one_div_of_le
        · positivity
        · exact h₂₁
      exact h₂₇
    exact h₁₀
  linarith



lemma tail_sum_le (n d : ℕ) (hn : 2 ≤ n) (hd_pos : 0 < d) (hd_le : d ≤ n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    ∑ j ∈ Finset.range (n / (2 * d)),
      (1 : ℝ) / (2 * ((d : ℝ) - b + ((j : ℝ) + 1) * d)) ≤
    (1 + Real.log ↑n) / (2 * ↑d) := by
  calc ∑ j ∈ Finset.range (n / (2 * d)),
        (1 : ℝ) / (2 * ((d : ℝ) - b + ((j : ℝ) + 1) * d))
      ≤ ∑ j ∈ Finset.Icc 1 (n / (2 * d)),
        (1 : ℝ) / (2 * ((j : ℝ) * (d : ℝ))) :=
          sum_range_le_sum_Icc n d hd_pos b hb_pos hb_lt
    _ ≤ (1 + Real.log ↑n) / (2 * ↑d) :=
          harmonic_sum_over_Icc_le_log_div n d hn hd_pos hd_le



lemma arith_prog_sum_le
    (n d : ℕ) (hn : 2 ≤ n) (hd_pos : 0 < d) (hd_le : d ≤ n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    ∑ j ∈ Finset.range (n / (2 * d) + 1),
      (1 : ℝ) / (2 * ((d : ℝ) - b + j * d)) ≤
    1 / (2 * ((d : ℝ) - b)) + (1 + Real.log ↑n) / (2 * ↑d) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have h1 : ∀ k ∈ Finset.range (n / (2 * d)),
      (1 : ℝ) / (2 * ((d : ℝ) - b + ↑(k + 1) * d)) =
      (1 : ℝ) / (2 * ((d : ℝ) - b + (↑k + 1) * d)) := by
    intro k _; push_cast; ring_nf
  rw [Finset.sum_congr rfl h1]
  linarith [tail_sum_le n d hn hd_pos hd_le b hb_pos hb_lt]



lemma high_range_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd_dvd : d ∣ n)
    (mq : ℕ) (hmq_lo : 1 ≤ mq) (hmq_hi : mq < n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    (∑ l : ZMod n,
      if (ZMod.val l % d = b ∧ ¬(2 * ZMod.val l ≤ n))
      then ‖normalizedDFT n (intervalIndicator n mq) l‖
      else 0) ≤
    1 / (2 * ((d : ℝ) - b)) + (1 + Real.log ↑n) / (2 * ↑d) := by
  have hd_pos : 0 < d := NeZero.pos d
  have hd_le : d ≤ n := Nat.le_of_dvd (by omega) hd_dvd
  have step1 : (∑ l : ZMod n,
      if (ZMod.val l % d = b ∧ ¬(2 * ZMod.val l ≤ n))
      then ‖normalizedDFT n (intervalIndicator n mq) l‖
      else 0) ≤
    (∑ l : ZMod n,
      if (ZMod.val l % d = b ∧ ¬(2 * ZMod.val l ≤ n))
      then (1 : ℝ) / (2 * ((n : ℝ) - ZMod.val l))
      else 0) := by
    apply Finset.sum_le_sum
    intro l _
    split_ifs with h
    · exact high_range_pointwise_bound n mq hmq_lo hmq_hi d b hb_pos l h.1 h.2
    · exact le_refl _
  have step2 : (∑ l : ZMod n,
      if (ZMod.val l % d = b ∧ ¬(2 * ZMod.val l ≤ n))
      then (1 : ℝ) / (2 * ((n : ℝ) - ZMod.val l))
      else 0) ≤
    ∑ j ∈ Finset.range (n / (2 * d) + 1),
      (1 : ℝ) / (2 * ((d : ℝ) - b + j * d)) :=
    high_range_reindex_bound n d hn hd_dvd b hb_pos hb_lt
  have step3 : ∑ j ∈ Finset.range (n / (2 * d) + 1),
      (1 : ℝ) / (2 * ((d : ℝ) - b + j * d)) ≤
    1 / (2 * ((d : ℝ) - b)) + (1 + Real.log ↑n) / (2 * ↑d) :=
    arith_prog_sum_le n d hn hd_pos hd_le b hb_pos hb_lt
  linarith



lemma split_sum_low_high
    (n d : ℕ) [NeZero n] [NeZero d]
    (mq : ℕ)
    (b : ℕ) :
    (∑ l : ZMod n,
      if (ZMod.val l % d = b)
      then ‖normalizedDFT n (intervalIndicator n mq) l‖
      else 0) =
    (∑ l : ZMod n,
      if (ZMod.val l % d = b ∧ 2 * ZMod.val l ≤ n)
      then ‖normalizedDFT n (intervalIndicator n mq) l‖
      else 0) +
    (∑ l : ZMod n,
      if (ZMod.val l % d = b ∧ ¬(2 * ZMod.val l ≤ n))
      then ‖normalizedDFT n (intervalIndicator n mq) l‖
      else 0) := by
  have h₁ : (∑ l : ZMod n,
    (if (ZMod.val l % d = b) then ‖normalizedDFT n (intervalIndicator n mq) l‖ else 0 : ℝ)) =
      (∑ l : ZMod n,
        ((if (ZMod.val l % d = b ∧ 2 * ZMod.val l ≤
          n) then ‖normalizedDFT n (intervalIndicator n mq) l‖ else 0 : ℝ) + (if (ZMod.val l % d =
            b ∧ ¬(2 * ZMod.val l ≤
              n)) then ‖normalizedDFT n (intervalIndicator n mq) l‖ else 0 : ℝ))) := by
    congr 1; ext l; split_ifs with h1 h2 h3 <;> simp_all
  rw [h₁, Finset.sum_add_distrib]



lemma half_reciprocal_sum_le_min_reciprocal
    (b d : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    1 / (2 * (b : ℝ)) + 1 / (2 * ((d : ℝ) - b)) ≤
    1 / min (b : ℝ) ((d : ℝ) - b) := by
  have h₂ : (d : ℝ) - b > 0 := by
    have h₃ : (b : ℝ) < (d : ℝ) := by exact_mod_cast hb_lt
    linarith
  by_cases h₄ : (b : ℝ) ≤ (d : ℝ) - b
  · have h₅ : min (b : ℝ) ((d : ℝ) - b) = (b : ℝ) := by
      rw [min_eq_left h₄]
    rw [h₅]
    have h₆ : 1 / (2 * (b : ℝ)) + 1 / (2 * ((d : ℝ) - b)) ≤ 1 / (b : ℝ) := by
      have h₁₁ : 1 / (2 * ((d : ℝ) - b)) ≤ 1 / (2 * (b : ℝ)) := by
        apply one_div_le_one_div_of_le
        · positivity
        · nlinarith
      have h₁₃ : 1 / (2 * (b : ℝ)) + 1 / (2 * (b : ℝ)) = 1 / (b : ℝ) := by
        field_simp
        ring_nf
      linarith
    exact h₆
  · have h₅ : min (b : ℝ) ((d : ℝ) - b) = (d : ℝ) - b := by
      rw [min_eq_right (by linarith)]
    rw [h₅]
    have h₆ : 1 / (2 * (b : ℝ)) + 1 / (2 * ((d : ℝ) - b)) ≤ 1 / ((d : ℝ) - b) := by
      have h₁₁ : 1 / (2 * (b : ℝ)) ≤ 1 / (2 * ((d : ℝ) - b)) := by
        apply one_div_le_one_div_of_le
        · positivity
        · nlinarith
      have h₁₃ : 1 / (2 * ((d : ℝ) - b)) + 1 / (2 * ((d : ℝ) - b)) = 1 / ((d : ℝ) - b) := by
        field_simp
        ring_nf
      linarith
    exact h₆



lemma fourier_mass_residue_class_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd_dvd : d ∣ n)
    (mq : ℕ) (hmq_lo : 1 ≤ mq) (hmq_hi : mq < n)
    (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    (∑ l : ZMod n,
      if (ZMod.val l % d = b)
      then ‖normalizedDFT n (intervalIndicator n mq) l‖
      else 0) ≤
    1 / min (b : ℝ) ((d : ℝ) - b) + (1 + Real.log ↑n) / ↑d := by
  rw [split_sum_low_high n d mq b]
  have hlow := low_range_bound n d hn hd_dvd mq hmq_lo hmq_hi b hb_pos hb_lt
  have hhigh := high_range_bound n d hn hd_dvd mq hmq_lo hmq_hi b hb_pos hb_lt
  have hcombine := half_reciprocal_sum_le_min_reciprocal b d hb_pos hb_lt
  have hlog := one_plus_log_nonneg n hn
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hsum : (1 + Real.log ↑n) / (2 * ↑d) + (1 + Real.log ↑n) / (2 * ↑d) =
      (1 + Real.log ↑n) / ↑d := by field_simp; ring
  linarith



lemma inner_sum_bound_at_residue
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd_dvd : d ∣ n)
    (q : ℤ) (hq_coprime_d : Int.gcd q (d : ℤ) = 1)
    (_hq_pos : 1 ≤ q) (_hq_bound : (q : ℝ) < (n : ℝ) / 2)
    (mq : ℕ) (hmq_lo : 1 ≤ mq) (hmq_hi : mq < n)
    (k : ZMod n) (hk : k ≠ 0) (hk_nd : ¬((d : ℕ) ∣ ZMod.val k))
    (u : (ZMod d)ˣ) :
    let b := ZMod.val (-(q : ZMod d)⁻¹ * ((ZMod.val k * (u : ZMod d).val : ℕ) : ZMod d))
    (∑ l : ZMod n,
      if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mq) l‖
      else 0) ≤
    1 / min (b : ℝ) ((d : ℝ) - b)
    + (1 + Real.log ↑n) / ↑d := by
  intro b
  clear _hq_pos _hq_bound
  have hb := b_bounds d q hq_coprime_d (ZMod.val k) hk_nd u
  rw [cond_sum_eq_residue_class_sum n d hd_dvd q hq_coprime_d mq k hk u]
  exact fourier_mass_residue_class_bound n d hn hd_dvd mq hmq_lo hmq_hi b hb.1 hb.2



lemma zmod_expr_simplify
    (d : ℕ) [NeZero d]
    (q : ℤ) (hq_coprime_d : Int.gcd q (d : ℤ) = 1)
    (k_val : ℕ)
    (w : (ZMod d)ˣ) (hw : (w : ZMod d) = -(q : ZMod d))
    (v : (ZMod d)ˣ) :
    (-(q : ZMod d)⁻¹ * ((k_val * (↑(w * v) : ZMod d).val : ℕ) : ZMod d) : ZMod d) =
    ((k_val * (↑v : ZMod d).val : ℕ) : ZMod d) := by
  have _h_unit := neg_inv_isUnit d q hq_coprime_d
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val, Units.val_mul, hw]
  rw [neg_inv_eq_inv_neg d q hq_coprime_d, ← hw, ZMod.inv_coe_unit w]
  rw [show (↑(w⁻¹) : ZMod d) * ((↑k_val : ZMod d) * ((↑w : ZMod d) * (↑v : ZMod d))) =
    (↑(w⁻¹) : ZMod d) * ((↑w : ZMod d) * ((↑k_val : ZMod d) * (↑v : ZMod d))) from by ring]
  rw [Units.inv_mul_cancel_left]



lemma summand_val_eq_after_bijection
    (d : ℕ) [NeZero d]
    (q : ℤ) (hq_coprime_d : Int.gcd q (d : ℤ) = 1)
    (k_val : ℕ) (_hk_nd : ¬(d ∣ k_val))
    (w : (ZMod d)ˣ) (hw : (w : ZMod d) = -(q : ZMod d))
    (v : (ZMod d)ˣ) :
    ZMod.val (-(q : ZMod d)⁻¹ * ((k_val * (↑(w * v) : ZMod d).val : ℕ) : ZMod d)) =
    k_val * (↑v : ZMod d).val % d := by
  rw [zmod_expr_simplify d q hq_coprime_d k_val w hw v]
  exact ZMod.val_natCast d (k_val * (↑v : ZMod d).val)



lemma neg_q_unit_exists
    (d : ℕ) [NeZero d]
    (q : ℤ) (hq_coprime_d : Int.gcd q (d : ℤ) = 1) :
    ∃ w : (ZMod d)ˣ, (w : ZMod d) = -(q : ZMod d) := by
  have hq_int_is_coprime : IsCoprime (q : ℤ) (d : ℤ) :=
    by exact Int.isCoprime_iff_gcd_eq_one.mpr hq_coprime_d
  have hq_zmod_unit : IsUnit (q : ZMod d) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime]
    exact hq_int_is_coprime.symm
  have h_neg_q_zmod_unit : IsUnit (-(q : ZMod d)) := hq_zmod_unit.neg
  obtain ⟨w, hw⟩ := h_neg_q_zmod_unit
  exact ⟨w, hw⟩



lemma bijection_sum_eq
    (d : ℕ) [NeZero d]
    (q : ℤ) (hq_coprime_d : Int.gcd q (d : ℤ) = 1)
    (k_val : ℕ) (hk_nd : ¬(d ∣ k_val)) :
    (∑ u : (ZMod d)ˣ,
      let b := ZMod.val (-(q : ZMod d)⁻¹ * ((k_val * (u : ZMod d).val : ℕ) : ZMod d))
      1 / min (b : ℝ) ((d : ℝ) - b)) =
    (∑ u : (ZMod d)ˣ,
      1 / min ((k_val * (u : ZMod d).val % d : ℕ) : ℝ)
              ((d : ℝ) - (k_val * (u : ZMod d).val % d : ℕ))) := by
  obtain ⟨w, hw⟩ := neg_q_unit_exists d q hq_coprime_d
  symm
  exact Fintype.sum_equiv (Equiv.mulLeft w)
    (fun v =>
      1 / min ((k_val * (v : ZMod d).val % d : ℕ) : ℝ)
              ((d : ℝ) - (k_val * (v : ZMod d).val % d : ℕ)))
    (fun u =>
      let b := ZMod.val (-(q : ZMod d)⁻¹ * ((k_val * (u : ZMod d).val : ℕ) : ZMod d))
      1 / min (b : ℝ) ((d : ℝ) - b))
    (fun v => by
      change 1 / min ((k_val * (v : ZMod d).val % d : ℕ) : ℝ)
              ((d : ℝ) - (k_val * (v : ZMod d).val % d : ℕ)) =
           (let b :=
             ZMod.val (-(q : ZMod d)⁻¹ * ((k_val *
               ((Equiv.mulLeft w v : (ZMod d)ˣ) : ZMod d).val : ℕ) : ZMod d))
            1 / min (b : ℝ) ((d : ℝ) - b))
      simp only [Equiv.coe_mulLeft]
      have h := summand_val_eq_after_bijection d q hq_coprime_d k_val hk_nd w hw v
      rw [← h])

end PerUnitMerge

open PerUnitMerge in
lemma per_unit_inner_sum_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (hq_pos : 1 ≤ q) (hq_bound : (q : ℝ) < (n : ℝ) / 2)
    (mq : ℕ) (hmq : mq = (2 * q - 1).toNat)
    (k : ZMod n) (hk : k ≠ 0) (hk_nd : ¬((d : ℕ) ∣ ZMod.val k)) :
    (∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖
        else 0)) ≤
    (∑ u : (ZMod d)ˣ,
      1 / min ((ZMod.val k * (u : ZMod d).val % d : ℕ) : ℝ)
              ((d : ℝ) - (ZMod.val k * (u : ZMod d).val % d : ℕ)))
    + ↑(Fintype.card (ZMod d)ˣ) * ((1 + Real.log ↑n) / ↑d) := by
  have hd_dvd : d ∣ n := hd ▸ _root_.d_dvd_n n hn
  have hq_coprime_d : Int.gcd q (d : ℤ) = 1 := coprimality_q_d n hn q hq_coprime d hd
  have hmq_bounds := mq_bounds n hn q hq_pos hq_bound
  have hmq_lo : 1 ≤ mq := hmq ▸ hmq_bounds.1
  have hmq_hi : mq < n := hmq ▸ hmq_bounds.2
  calc ∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖
        else 0)
    ≤ ∑ u : (ZMod d)ˣ,
      (let b := ZMod.val (-(q : ZMod d)⁻¹ * ((ZMod.val k * (u : ZMod d).val : ℕ) : ZMod d))
       1 / min (b : ℝ) ((d : ℝ) - b)
       + (1 + Real.log ↑n) / ↑d) := by
        exact Finset.sum_le_sum fun u _ =>
          inner_sum_bound_at_residue n d hn hd_dvd q hq_coprime_d hq_pos hq_bound
            mq hmq_lo hmq_hi k hk hk_nd u
    _ = (∑ u : (ZMod d)ˣ,
          (let b := ZMod.val (-(q : ZMod d)⁻¹ * ((ZMod.val k * (u : ZMod d).val : ℕ) : ZMod d))
           1 / min (b : ℝ) ((d : ℝ) - b)))
        + ∑ _u : (ZMod d)ˣ, ((1 + Real.log ↑n) / ↑d) := by
        exact Finset.sum_add_distrib
    _ = (∑ u : (ZMod d)ˣ,
          1 / min ((ZMod.val k * (u : ZMod d).val % d : ℕ) : ℝ)
                  ((d : ℝ) - (ZMod.val k * (u : ZMod d).val % d : ℕ)))
        + ∑ _u : (ZMod d)ˣ, ((1 + Real.log ↑n) / ↑d) := by
        congr 1
        exact bijection_sum_eq d q hq_coprime_d (ZMod.val k) hk_nd
    _ = (∑ u : (ZMod d)ˣ,
          1 / min ((ZMod.val k * (u : ZMod d).val % d : ℕ) : ℝ)
                  ((d : ℝ) - (ZMod.val k * (u : ZMod d).val % d : ℕ)))
        + ↑(Fintype.card (ZMod d)ˣ) * ((1 + Real.log ↑n) / ↑d) := by
        congr 1
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]



lemma combine_orbit_and_tail_bounds
    (C L d_real : ℝ) (_hC : 0 ≤ C) (_hL : 0 ≤ L) (hd : 0 < d_real) :
    C * (4 * L / d_real) + C * (L / d_real) ≤ C * (5 * L / d_real) := by
  have h₃ : 0 < d_real := hd
  have h₅ : 0 < d_real := h₃
  have h₆ : C * (4 * L / d_real) + C * (L / d_real) = C * (4 * L / d_real + L / d_real) := by
    ring
  rw [h₆]
  have h₇ : 4 * L / d_real + L / d_real = 5 * L / d_real := by
    field_simp [h₅.ne']
    ring
  rw [h₇]


lemma orbit_average_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (hq_pos : 1 ≤ q) (hq_bound : (q : ℝ) < (n : ℝ) / 2)
    (mq : ℕ) (hmq : mq = (2 * q - 1).toNat)
    (k : ZMod n) (hk : k ≠ 0) (hk_nd : ¬((d : ℕ) ∣ ZMod.val k)) :
    (∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖
        else 0)) ≤
    ↑(Fintype.card (ZMod d)ˣ) * (5 * (1 + Real.log ↑n) / ↑d) := by
  have h_step1 := per_unit_inner_sum_bound n d hn hd q hq_coprime hq_pos hq_bound mq hmq k hk hk_nd
  have h_step2 := orbit_reciprocal_sum_bound n d hn hd k hk hk_nd
  calc (∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖
          else 0))
      ≤ (∑ u : (ZMod d)ˣ,
          1 / min ((ZMod.val k * (u : ZMod d).val % d : ℕ) : ℝ)
                  ((d : ℝ) - (ZMod.val k * (u : ZMod d).val % d : ℕ)))
        + ↑(Fintype.card (ZMod d)ˣ) * ((1 + Real.log ↑n) / ↑d) := h_step1
    _ ≤ ↑(Fintype.card (ZMod d)ˣ) * (4 * (1 + Real.log ↑n) / ↑d)
        + ↑(Fintype.card (ZMod d)ˣ) * ((1 + Real.log ↑n) / ↑d) := by
          gcongr
    _ ≤ ↑(Fintype.card (ZMod d)ˣ) * (5 * (1 + Real.log ↑n) / ↑d) :=
          combine_orbit_and_tail_bounds
            ↑(Fintype.card (ZMod d)ˣ) (1 + Real.log ↑n) ↑d
            (by positivity) (by positivity)
            (Nat.cast_pos.mpr (NeZero.pos d))



lemma nonmultiple_d_weighted_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (hq_pos : 1 ≤ q) (hq_bound : (q : ℝ) < (n : ℝ) / 2)
    (mq : ℕ) (hmq : mq = (2 * q - 1).toNat) :
    (∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)),
      ∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
               (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
          else 0)) ≤
    ↑(Fintype.card (ZMod d)ˣ) * (5 * (1 + Real.log ↑n) ^ 2 / ↑d) := by
  have h_rw : ∀ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)),
      (∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
               (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
          else 0)) =
      (∑ u : (ZMod d)ˣ,
        (∑ l : ZMod n,
          if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
          then ‖normalizedDFT n (intervalIndicator n mq) l‖
          else 0)) /
      (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) := by
    intro k hk
    exact factor_weight_from_double_sum n d mq q k ((Finset.mem_filter.mp hk).2.1)
  rw [Finset.sum_congr rfl h_rw]
  calc ∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)),
        (∑ u : (ZMod d)ˣ,
          (∑ l : ZMod n,
            if ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
            then ‖normalizedDFT n (intervalIndicator n mq) l‖
            else 0)) /
        (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
      ≤ ∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)),
          ↑(Fintype.card (ZMod d)ˣ) * (5 * (1 + Real.log ↑n) / ↑d) /
          (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply div_le_div_of_nonneg_right
        · exact orbit_average_bound n d hn hd q hq_coprime hq_pos hq_bound mq hmq
              k ((Finset.mem_filter.mp hk).2.1) ((Finset.mem_filter.mp hk).2.2)
        · exact weight_nonneg n k ((Finset.mem_filter.mp hk).2.1)
    _ = ↑(Fintype.card (ZMod d)ˣ) * (5 * (1 + Real.log ↑n) / ↑d) *
        ∑ k ∈ Finset.univ.filter (fun k : ZMod n => k ≠ 0 ∧ ¬((d : ℕ) ∣ ZMod.val k)),
          (1 : ℝ) / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) := by
        rw [Finset.mul_sum]
        congr 1
        ext k
        ring
    _ ≤ ↑(Fintype.card (ZMod d)ˣ) * (5 * (1 + Real.log ↑n) / ↑d) *
        (1 + Real.log ↑n) := by
        apply mul_le_mul_of_nonneg_left (weight_sum_le_log n d hn)
        exact const_bound_nonneg n d hn
    _ = ↑(Fintype.card (ZMod d)ˣ) * (5 * (1 + Real.log ↑n) ^ 2 / ↑d) := by
        ring



lemma weighted_orbit_total
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (hq_pos : 1 ≤ q) (hq_bound : (q : ℝ) < (n : ℝ) / 2)
    (mq : ℕ) (hmq : mq = (2 * q - 1).toNat) :
    ∑ k : ZMod n, ∑ u : (ZMod d)ˣ,
      (∑ l : ZMod n,
        if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
             (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
        else 0) ≤
    ↑(Fintype.card (ZMod d)ˣ) * (6 * (1 + Real.log ↑n) ^ 2 / ↑d) := by
  rw [k_sum_split_by_d_divisibility n d mq q]
  calc _ ≤ ↑(Fintype.card (ZMod d)ˣ) * (5 * (1 + Real.log ↑n) ^ 2 / ↑d) +
           ↑(Fintype.card (ZMod d)ˣ) * ((1 + Real.log ↑n) ^ 2 / ↑d) :=
        add_le_add
          (nonmultiple_d_weighted_bound n d hn hd q hq_coprime hq_pos hq_bound mq hmq)
          (multiple_d_weighted_bound n d hn hd q hq_coprime hq_pos hq_bound mq hmq)
    _ = _ := combine_cases_arithmetic _ _ _




lemma average_S_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (hq_pos : 1 ≤ q) (hq_bound : (q : ℝ) < (n : ℝ) / 2)
    (mq : ℕ) (hmq : mq = (2 * q - 1).toNat) :
    ∑ u : (ZMod d)ˣ,
      (∑ k : ZMod n, ∑ l : ZMod n,
        if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
        then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
             (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
        else 0) ≤
    ↑(Fintype.card (ZMod d)ˣ) * (6 * (1 + Real.log ↑n) ^ 2 / ↑d) := by
  rw [sum_exchange_weighted n d mq q]
  exact weighted_orbit_total n d hn hd q hq_coprime hq_pos hq_bound mq hmq


lemma sum_filter_lower_bound
    (d : ℕ) [NeZero d]
    (f : (ZMod d)ˣ → ℝ) (_hf : ∀ u, 0 ≤ f u)
    (avg : ℝ) (R : ℕ)
    (S : Finset (ZMod d)ˣ)
    (hS : ∀ u ∈ S, ↑R * avg < f u) :
    S.card • (↑R * avg) ≤ ∑ u ∈ S, f u := by
  exact Finset.card_nsmul_le_sum S f (↑R * avg) (fun u hu => le_of_lt (hS u hu))


lemma sum_filter_le_sum_univ
    (d : ℕ) [NeZero d]
    (f : (ZMod d)ˣ → ℝ) (hf : ∀ u, 0 ≤ f u)
    (avg : ℝ) (R : ℕ) :
    ∑ u ∈ (Finset.univ.filter (fun u : (ZMod d)ˣ => ↑R * avg < f u)), f u ≤
      ∑ u : (ZMod d)ˣ, f u := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro i _ _
  exact hf i


lemma card_mul_R_le_of_nsmul_le
    (s C R : ℕ) (avg : ℝ) (havg : 0 < avg)
    (h : s • (↑R * avg) ≤ ↑C * avg) :
    s * R ≤ C := by
  have h₁ : (s : ℝ) * (R : ℝ) * avg ≤ (C : ℝ) * avg := by
    have h₂ : (s : ℝ) * (R : ℝ) * avg = s • (↑R * avg) := by
      simp [mul_comm, mul_left_comm]
    rw [h₂] at *
    exact h
  have h₂ : (s : ℝ) * (R : ℝ) ≤ (C : ℝ) := by
    have h₄ : 0 < (avg : ℝ) := havg
    have h₅ : (s : ℝ) * (R : ℝ) ≤ (C : ℝ) := by
      have h₆ : (s : ℝ) * (R : ℝ) * avg / avg ≤ (C : ℝ) * avg / avg := by
        gcongr
      have h₇ : (C : ℝ) * avg / avg = (C : ℝ) := by
        field_simp [h₄.ne']
      have h₈ : (s : ℝ) * (R : ℝ) * avg / avg = (s : ℝ) * (R : ℝ) := by
        field_simp [h₄.ne']
      linarith
    exact h₅
  have h₃ : (s * R : ℝ) ≤ (C : ℝ) := by
    have h₄ : (s * R : ℝ) = (s : ℝ) * (R : ℝ) := by
      norm_cast
    rw [h₄]
    exact h₂
  have h₄ : s * R ≤ C := by
    norm_cast at h₃ ⊢
  exact h₄


lemma filter_empty_of_avg_zero
    (d : ℕ) [NeZero d]
    (f : (ZMod d)ˣ → ℝ) (hf : ∀ u, 0 ≤ f u)
    (hsum : ∑ u : (ZMod d)ˣ, f u ≤ 0)
    (_R : ℕ) :
    (Finset.univ.filter (fun u : (ZMod d)ˣ => 0 < f u)) = ∅ := by
  have h_filter_empty : (Finset.univ.filter (fun u : (ZMod d)ˣ => 0 < f u)) = ∅ := by
    have h₁ : ∀ (u : (ZMod d)ˣ), f u = 0 := by
      intro u
      have h₂ : 0 ≤ f u := hf u
      have h₄ : f u ≤ 0 := by
        have h₆ : f u ≤ ∑ u : (ZMod d)ˣ, f u := by
          apply Finset.single_le_sum (fun i _ => hf i) (Finset.mem_univ u)
        linarith
      linarith
    apply Finset.filter_eq_empty_iff.mpr
    intro u _
    have h₂ : f u = 0 := h₁ u
    have h₃ : ¬(0 < f u) := by
      rw [h₂]
      norm_num
    exact h₃
  exact h_filter_empty


lemma markov_card_mul_le
    (d : ℕ) [NeZero d]
    (f : (ZMod d)ˣ → ℝ) (hf : ∀ u, 0 ≤ f u)
    (avg : ℝ) (havg : 0 ≤ avg)
    (hsum : ∑ u : (ZMod d)ˣ, f u ≤ ↑(Fintype.card (ZMod d)ˣ) * avg)
    (R : ℕ) (hR : 1 ≤ R) :
    (Finset.univ.filter (fun u : (ZMod d)ˣ => ↑R * avg < f u)).card * R ≤
      Fintype.card (ZMod d)ˣ := by
  have hR_pos : (0 : ℝ) < ↑R := Nat.cast_pos.mpr (Nat.one_le_iff_ne_zero.mp hR |>.bot_lt)
  set S := Finset.univ.filter (fun u : (ZMod d)ˣ => ↑R * avg < f u)
  rcases le_or_gt avg 0 with havg0 | havg0
  · have heq : avg = 0 := le_antisymm havg0 havg
    subst heq
    have hS_empty : S = ∅ := by
      have : Finset.univ.filter (fun u : (ZMod d)ˣ => 0 < f u) = ∅ :=
        filter_empty_of_avg_zero d f hf (by simp_all) R
      simpa [S, mul_zero] using this
    rw [hS_empty]
    simp
  · have hlower := sum_filter_lower_bound d f hf avg R S (fun u hu => by
      exact (Finset.mem_filter.mp hu).2)
    have hupper := sum_filter_le_sum_univ d f hf avg R
    have hchain : S.card • (↑R * avg) ≤ ↑(Fintype.card (ZMod d)ˣ) * avg :=
      le_trans hlower (le_trans hupper hsum)
    exact card_mul_R_le_of_nsmul_le S.card (Fintype.card (ZMod d)ˣ) R avg havg0 hchain


lemma markov_card_filter_le
    (d : ℕ) [NeZero d]
    (f : (ZMod d)ˣ → ℝ) (hf : ∀ u, 0 ≤ f u)
    (avg : ℝ) (havg : 0 ≤ avg)
    (hsum : ∑ u : (ZMod d)ˣ, f u ≤ ↑(Fintype.card (ZMod d)ˣ) * avg)
    (R : ℕ) (hR : 1 ≤ R) :
    (Finset.univ.filter (fun u : (ZMod d)ˣ => ↑R * avg < f u)).card ≤
      Fintype.card (ZMod d)ˣ / R := by
  have hR_pos : 0 < R := Nat.one_le_iff_ne_zero.mp hR |>.bot_lt
  exact (Nat.galoisConnection_mul_div hR_pos).le_iff_le.mp
    (markov_card_mul_le d f hf avg havg hsum R hR)


lemma image_val_card_le
    (d : ℕ) [NeZero d]
    (S : Finset (ZMod d)ˣ)
    (R : ℕ) (_hR : 1 ≤ R)
    (hcard : S.card ≤ Fintype.card (ZMod d)ˣ / R) :
    (S.image (fun u : (ZMod d)ˣ => (u : ZMod d).val)).card ≤ d / R := by
  have h₁ : (S.image (fun u : (ZMod d)ˣ => (u : ZMod d).val)).card ≤ S.card := by
    apply Finset.card_image_le
  have h₂ : Fintype.card (ZMod d)ˣ ≤ d := by
    have h₃ : Fintype.card (ZMod d)ˣ = d.totient := by
      rw [ZMod.card_units_eq_totient]
    rw [h₃]
    have h₄ : d.totient ≤ d := by
      apply Nat.totient_le
    exact h₄
  have h₃ : Fintype.card (ZMod d)ˣ / R ≤ d / R := by
    have h₄ : Fintype.card (ZMod d)ˣ ≤ d := h₂
    have h₅ : Fintype.card (ZMod d)ˣ / R ≤ d / R := by
      apply Nat.div_le_div_right
      (try omega)
    exact h₅
  calc
    (S.image (fun u : (ZMod d)ˣ => (u : ZMod d).val)).card ≤ S.card := h₁
    _ ≤ Fintype.card (ZMod d)ˣ / R := hcard
    _ ≤ d / R := h₃


lemma bad_set_from_average
    (d : ℕ) [NeZero d]
    (f : (ZMod d)ˣ → ℝ) (hf : ∀ u, 0 ≤ f u)
    (avg : ℝ) (havg : 0 ≤ avg)
    (hsum : ∑ u : (ZMod d)ˣ, f u ≤ ↑(Fintype.card (ZMod d)ˣ) * avg)
    (R : ℕ) (hR : 1 ≤ R) :
    ∃ B : Finset ℕ, B.card ≤ d / R ∧
      ∀ u : (ZMod d)ˣ, (u : ZMod d).val ∉ B → f u ≤ ↑R * avg := by
  set B_units := Finset.univ.filter (fun u : (ZMod d)ˣ => ↑R * avg < f u) with hB_units_def
  set B := B_units.image (fun u : (ZMod d)ˣ => (u : ZMod d).val) with hB_def
  refine ⟨B, ?_, ?_⟩
  · have hcard := markov_card_filter_le d f hf avg havg hsum R hR
    exact image_val_card_le d B_units R hR hcard
  · intro u hu
    by_contra h
    push Not at h
    have : u ∈ B_units := by
      simp only [hB_units_def, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    have : (u : ZMod d).val ∈ B := by
      simp only [hB_def]
      exact Finset.mem_image_of_mem _ this
    contradiction


lemma k_zero_term_eq (n d : ℕ) [NeZero n] [NeZero d]
    (mp mq : ℕ) (p q : ℤ) :
    (∑ l : ZMod n,
      if ((0 : ZMod n), l) ≠ (0, 0) ∧ ((d : ℤ) ∣ (↑(ZMod.val (0 : ZMod n)) * p + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mp) (0 : ZMod n)‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) =
    (∑ l : ZMod n,
      if l ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mp) (0 : ZMod n)‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) := by
  apply Finset.sum_congr rfl
  intro l _
  simp_all


lemma inner_sum_eq_of_k_ne_zero (n d : ℕ) [NeZero n] [NeZero d]
    (mp mq : ℕ) (p q : ℤ) (k : ZMod n) (hk : k ≠ 0) :
    (∑ l : ZMod n,
      if (k, l) ≠ (0, 0) ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * p + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mp) k‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) =
    (∑ l : ZMod n,
      if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * p + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mp) k‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) := by
  simp_all



lemma filtered_sum_to_full_sum (n d : ℕ) [NeZero n] [NeZero d]
    (mp mq : ℕ) (p q : ℤ) :
    (∑ k ∈ Finset.univ.filter (· ≠ (0 : ZMod n)), ∑ l : ZMod n,
      if (k, l) ≠ (0, 0) ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * p + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mp) k‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) =
    (∑ k : ZMod n, ∑ l : ZMod n,
      if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * p + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mp) k‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_pos hk]
    exact inner_sum_eq_of_k_ne_zero n d mp mq p q k hk



lemma double_sum_split_k0_kneq0
    (n d : ℕ) [NeZero n] [NeZero d]
    (mp mq : ℕ)
    (p q : ℤ) :
    (∑ k : ZMod n, ∑ l : ZMod n,
      if (k, l) ≠ (0, 0) ∧ ((d : ℤ)) ∣ (ZMod.val k * p + ZMod.val l * q)
      then ‖normalizedDFT n (intervalIndicator n mp) k‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) =
    (∑ l : ZMod n,
      if l ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mp) (0 : ZMod n)‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) +
    (∑ k : ZMod n, ∑ l : ZMod n,
      if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * p + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mp) k‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) := by
  rw [sum_split_zero]
  rw [k_zero_term_eq n d mp mq p q]
  rw [filtered_sum_to_full_sum n d mp mq p q]


lemma int_coprime_dvd_mul_imp_dvd (d v : ℕ) (q : ℤ)
    (hgcd : Int.gcd q (d : ℤ) = 1)
    (hdvd : (d : ℤ) ∣ (↑v * q)) :
    d ∣ v := by
  have h₁ : IsCoprime (d : ℤ) q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simp_all [Int.gcd_comm]
  have h₂ : (d : ℤ) ∣ (v : ℤ) := by
    have h₃ : (d : ℤ) ∣ (v : ℤ) * q := by simpa [mul_comm] using hdvd
    have h₄ : IsCoprime (d : ℤ) q := h₁
    exact h₄.dvd_of_dvd_mul_right h₃
  have h₃ : d ∣ v := by
    exact Int.natCast_dvd_natCast.mp (by simpa using h₂)
  exact h₃



lemma dvd_val_of_dvd_val_mul_q
    (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (l : ZMod n) (_hl : l ≠ 0)
    (hdvd : (d : ℤ) ∣ (↑(ZMod.val l) * q)) :
    (d : ℕ) ∣ ZMod.val l := by
  exact int_coprime_dvd_mul_imp_dvd d (ZMod.val l) q
    (coprimality_q_d n hn q hq_coprime d hd) hdvd



lemma norm_normalizedDFT_zero_le_one
    (n : ℕ) [NeZero n] (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m < n) :
    ‖normalizedDFT n (intervalIndicator n m) 0‖ ≤ 1 := by
  rw [normalizedDFT_intervalIndicator_zero n m hm1 hm2]
  rw [Complex.norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact div_le_one_of_le₀ (by exact_mod_cast hm2.le) (by positivity)


lemma sum_nonzero_multiples_dft_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd_dvd : d ∣ n) (hd_pos : 0 < d)
    (mq : ℕ) (hmq1 : 1 ≤ mq) (hmq2 : mq < n) :
    ∑ l ∈ Finset.univ.filter (fun l : ZMod n => l ≠ 0 ∧ (d : ℕ) ∣ ZMod.val l),
      ‖normalizedDFT n (intervalIndicator n mq) l‖ ≤
    (1 + Real.log (n : ℝ)) / d := by
  calc ∑ l ∈ Finset.univ.filter (fun l : ZMod n => l ≠ 0 ∧ (d : ℕ) ∣ ZMod.val l),
        ‖normalizedDFT n (intervalIndicator n mq) l‖
      ≤ ∑ l ∈ Finset.univ.filter (fun l : ZMod n => l ≠ 0 ∧ (d : ℕ) ∣ ZMod.val l),
        (1 : ℝ) / (2 * min (ZMod.val l : ℝ) ((n : ℝ) - ZMod.val l)) := by
          apply Finset.sum_le_sum
          intro l hl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
          exact normalizedDFT_intervalIndicator_nonzero_bound n mq hmq1 hmq2 l hl.1
    _ ≤ (1 + Real.log (n : ℝ)) / d :=
          weight_sum_multiples_of_d_bound n d hn hd_dvd hd_pos



lemma filter_int_dvd_subset_filter_nat_dvd
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1) :
    Finset.univ.filter (fun l : ZMod n => l ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val l) * q))) ⊆
    Finset.univ.filter (fun l : ZMod n => l ≠ 0 ∧ (d : ℕ) ∣ ZMod.val l) := by
  apply Finset.monotone_filter_right
  intro l _ ⟨hl_ne, hdvd⟩
  exact ⟨hl_ne, dvd_val_of_dvd_val_mul_q n d hn hd q hq_coprime l hl_ne hdvd⟩



lemma sum_int_dvd_le_sum_nat_dvd
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (f g : ZMod n → ℝ) (hf_nonneg : ∀ l, 0 ≤ f l) (hg_nonneg : ∀ l, 0 ≤ g l) :
    (∑ l : ZMod n,
      if l ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val l) * q))
      then f l * g l else (0 : ℝ)) ≤
    ∑ l ∈ Finset.univ.filter (fun l : ZMod n => l ≠ 0 ∧ (d : ℕ) ∣ ZMod.val l),
      f l * g l := by
  rw [← Finset.sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (filter_int_dvd_subset_filter_nat_dvd n d hn hd q hq_coprime)
    (fun l _ _ => mul_nonneg (hf_nonneg l) (hg_nonneg l))



lemma sum_mul_le_sum_of_le_one
    (n : ℕ) [NeZero n] (c : ℝ) (hc : c ≤ 1) (_hc_nonneg : 0 ≤ c)
    (g : ZMod n → ℝ) (hg_nonneg : ∀ l, 0 ≤ g l)
    (S : Finset (ZMod n)) :
    ∑ l ∈ S, c * g l ≤ ∑ l ∈ S, g l := by
  have h_pointwise : ∀ l ∈ S, c * g l ≤ g l :=
    by intro l _; exact mul_le_of_le_one_left (hg_nonneg l) hc
  have h_sum : ∑ l ∈ S, c * g l ≤ ∑ l ∈ S, g l := by exact Finset.sum_le_sum h_pointwise
  exact h_sum



lemma k_zero_contribution_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (p q : ℤ) (hp_pos : 1 ≤ p) (hq_pos : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2)
    (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1) :
    let mp := (2 * p - 1).toNat
    let mq := (2 * q - 1).toNat
    (∑ l : ZMod n,
      if l ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mp) (0 : ZMod n)‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) ≤
      (1 + Real.log ↑n) / ↑d := by
  set mp := (2 * p - 1).toNat
  set mq := (2 * q - 1).toNat
  have hmp := mp_valid n hn p q hp_pos hq_pos hpq
  have hmq := mq_valid n hn p q hp_pos hq_pos hpq
  have hd_dvd : d ∣ n := hd ▸ d_dvd_n n hn
  have hd_pos' : 0 < d := hd ▸ d_pos n hn
  have h_step1 : (∑ l : ZMod n,
      if l ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mp) (0 : ZMod n)‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) ≤
    ∑ l ∈ Finset.univ.filter (fun l : ZMod n => l ≠ 0 ∧ (d : ℕ) ∣ ZMod.val l),
        ‖normalizedDFT n (intervalIndicator n mp) (0 : ZMod n)‖ *
        ‖normalizedDFT n (intervalIndicator n mq) l‖ :=
    sum_int_dvd_le_sum_nat_dvd n d hn hd q hq_coprime _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have h_zero_le : ‖normalizedDFT n (intervalIndicator n mp) 0‖ ≤ 1 :=
    norm_normalizedDFT_zero_le_one n mp hmp.1 hmp.2
  have h_step2 : (∑ l ∈ Finset.univ.filter (fun l : ZMod n => l ≠ 0 ∧ (d : ℕ) ∣ ZMod.val l),
        ‖normalizedDFT n (intervalIndicator n mp) (0 : ZMod n)‖ *
        ‖normalizedDFT n (intervalIndicator n mq) l‖) ≤
    ∑ l ∈ Finset.univ.filter (fun l : ZMod n => l ≠ 0 ∧ (d : ℕ) ∣ ZMod.val l),
        ‖normalizedDFT n (intervalIndicator n mq) l‖ :=
    sum_mul_le_sum_of_le_one n _ h_zero_le (norm_nonneg _) _
      (fun _ => norm_nonneg _) _
  have h_step3 :
    ∑ l ∈ Finset.univ.filter (fun l : ZMod n => l ≠ 0 ∧ (d : ℕ) ∣ ZMod.val l),
        ‖normalizedDFT n (intervalIndicator n mq) l‖ ≤
    (1 + Real.log ↑n) / ↑d :=
    sum_nonzero_multiples_dft_bound n d hn hd_dvd hd_pos' mq hmq.1 hmq.2
  linarith



lemma dvd_diff_from_zmod_eq (d : ℕ) [NeZero d] (p : ℤ) (u_val : ℕ)
    (hu : (p : ZMod d) = (u_val : ZMod d))
    (k_val l_val : ℕ) (q : ℤ) :
    ((d : ℤ) ∣ (↑k_val * p + ↑l_val * q - (↑k_val * ↑u_val + ↑l_val * q))) := by
  have h₁ : (d : ℤ) ∣ (p - (u_val : ℤ)) := by
    have h₂ : (p : ZMod d) = (u_val : ZMod d) := hu
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num [ZMod.intCast_eq_intCast_iff_dvd_sub] at h₂ ⊢
    (try {
      norm_cast at h₂ ⊢
      simp_all
    })
  have h₂ : (d : ℤ) ∣ (↑k_val * (p - (u_val : ℤ))) := by
    exact dvd_mul_of_dvd_right h₁ _
  have h₃ : (↑k_val * p + ↑l_val * q - (↑k_val * ↑u_val + ↑l_val * q)) = (↑k_val * (p -
    (u_val : ℤ))) := by
    ring_nf
  rw [h₃]
  exact h₂



lemma congr_dvd_equiv (d : ℕ) [NeZero d] (p : ℤ) (u_val : ℕ)
    (hu : (p : ZMod d) = (u_val : ZMod d))
    (k_val l_val : ℕ) (q : ℤ) :
    ((d : ℤ) ∣ (↑k_val * p + ↑l_val * q)) ↔
    ((d : ℤ) ∣ (↑k_val * ↑u_val + ↑l_val * q)) := by
  exact dvd_iff_dvd_of_dvd_sub (dvd_diff_from_zmod_eq d p u_val hu k_val l_val q)



lemma summand_le (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (p q : ℤ) (hp_pos : 1 ≤ p) (hq_pos : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2)
    (u_val : ℕ) (hu_congr : (p : ZMod d) = (u_val : ZMod d))
    (k l : ZMod n) :
    let mp := (2 * p - 1).toNat
    let mq := (2 * q - 1).toNat
    (if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * p + ↑(ZMod.val l) * q))
     then ‖normalizedDFT n (intervalIndicator n mp) k‖ *
          ‖normalizedDFT n (intervalIndicator n mq) l‖
     else (0 : ℝ)) ≤
    (if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑u_val + ↑(ZMod.val l) * q))
     then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
          (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
     else 0) := by
  simp only
  have h_equiv : ((d : ℤ) ∣ (↑(ZMod.val k) * p + ↑(ZMod.val l) * q)) ↔
      ((d : ℤ) ∣ (↑(ZMod.val k) * ↑u_val + ↑(ZMod.val l) * q)) :=
    congr_dvd_equiv d p u_val hu_congr (ZMod.val k) (ZMod.val l) q
  by_cases hcond : k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * p + ↑(ZMod.val l) * q))
  · rw [if_pos hcond, if_pos ⟨hcond.1, h_equiv.mp hcond.2⟩]
    have hk := hcond.1
    have hmp1 : 1 ≤ (2 * p - 1).toNat := mp_lower_bound p hp_pos
    have hmp2 : (2 * p - 1).toNat < n := mp_upper_bound n hn p q hp_pos hq_pos hpq
    have hbound := normalizedDFT_intervalIndicator_nonzero_bound n
      (2 * p - 1).toNat hmp1 hmp2 k hk
    have hnorm_nonneg : 0 ≤ ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖ :=
      norm_nonneg _
    have hmin_pos : (0 : ℝ) < min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k) :=
      min_val_pos n k hk
    calc ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
          ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖
        ≤ (1 / (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))) *
          ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖ :=
          mul_le_mul_of_nonneg_right hbound hnorm_nonneg
      _ = ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖ /
          (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k)) := by
          rw [one_div, mul_comm]
          rfl
  · rw [if_neg hcond]
    by_cases hcond2 : k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑u_val + ↑(ZMod.val l) * q))
    · exfalso
      apply hcond
      exact ⟨hcond2.1, h_equiv.mpr hcond2.2⟩
    · rw [if_neg hcond2]


lemma k_nonzero_contribution_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (_hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (p q : ℤ) (hp_pos : 1 ≤ p) (hq_pos : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2)
    (u_val : ℕ)
    (hu_congr : (p : ZMod d) = (u_val : ZMod d)) :
    let mp := (2 * p - 1).toNat
    let mq := (2 * q - 1).toNat
    (∑ k : ZMod n, ∑ l : ZMod n,
      if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * p + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mp) k‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) ≤
    (∑ k : ZMod n, ∑ l : ZMod n,
      if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑u_val + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
           (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
      else 0) := by
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro l _
  exact summand_le n d hn p q hp_pos hq_pos hpq u_val hu_congr k l



lemma combine_bounds_arithmetic
    (R : ℕ) (P d : ℕ) (hR : 1 ≤ R) (hP : 0 < P) (hd : 0 < d)
    (hdP : P ≤ d) (n_real : ℝ) (hn_log : 0 ≤ Real.log n_real)
    (S0 Sneq0 : ℝ)
    (hS0 : S0 ≤ (1 + Real.log n_real) / ↑d)
    (hSneq0 : Sneq0 ≤ 6 * ↑R * (1 + Real.log n_real) ^ 2 / ↑d) :
    S0 + Sneq0 ≤ 7 * ↑R * (1 + Real.log n_real) ^ 2 / (P : ℝ) := by
  have h₂ : (1 + Real.log n_real : ℝ) / ↑d + 6 * ↑R * (1 + Real.log n_real) ^ 2 / ↑d = ((1 +
    Real.log n_real) + 6 * ↑R * (1 + Real.log n_real) ^ 2) / ↑d := by
    field_simp [hd.ne']
  have h₅ : ((1 + Real.log n_real : ℝ) + 6 * ↑R * (1 + Real.log n_real) ^ 2) / ↑d ≤ (7 * ↑R * (1 +
    Real.log n_real) ^ 2 : ℝ) / ↑d := by
    have h₅₁ : (1 + Real.log n_real : ℝ) ≤ ↑R * (1 + Real.log n_real) ^ 2 := by
      have h₅₂ : (1 : ℝ) ≤ ↑R := by exact_mod_cast hR
      nlinarith [sq_nonneg (1 + Real.log n_real - 1)]
    calc
      ((1 + Real.log n_real : ℝ) + 6 * ↑R * (1 + Real.log n_real) ^ 2) / ↑d ≤ (↑R * (1 +
        Real.log n_real) ^ 2 + 6 * ↑R * (1 + Real.log n_real) ^ 2 : ℝ) / ↑d := by
        gcongr
      _ = (7 * ↑R * (1 + Real.log n_real) ^ 2 : ℝ) / ↑d := by
        ring_nf
  have h₆ : (7 * ↑R * (1 + Real.log n_real) ^ 2 : ℝ) / ↑d ≤ (7 * ↑R * (1 + Real.log n_real) ^
    2 : ℝ) / (P : ℝ) := by
    have h₆₁ : (P : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdP
    have h₆₂ : 0 < (P : ℝ) := by positivity
    have h₆₃ : 0 < (d : ℝ) := by positivity
    have h₆₅ : (1 : ℝ) / (d : ℝ) ≤ (1 : ℝ) / (P : ℝ) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact h₆₁
    calc
      (7 * ↑R * (1 + Real.log n_real) ^ 2 : ℝ) / ↑d = (7 * ↑R * (1 + Real.log n_real) ^ 2 : ℝ) *
        (1 / (d : ℝ)) := by
        field_simp [h₆₃.ne']
      _ ≤ (7 * ↑R * (1 + Real.log n_real) ^ 2 : ℝ) * (1 / (P : ℝ)) := by
        gcongr
      _ = (7 * ↑R * (1 + Real.log n_real) ^ 2 : ℝ) / (P : ℝ) := by
        field_simp [h₆₂.ne']
  have h₇ : (S0 : ℝ) + Sneq0 ≤ (7 * ↑R * (1 + Real.log n_real) ^ 2 : ℝ) / (P : ℝ) := by
    calc
      (S0 : ℝ) + Sneq0 ≤ ((1 + Real.log n_real) + 6 * ↑R * (1 + Real.log n_real) ^ 2) / ↑d :=
        by linarith
      _ ≤ (7 * ↑R * (1 + Real.log n_real) ^ 2 : ℝ) / ↑d := by linarith
      _ ≤ (7 * ↑R * (1 + Real.log n_real) ^ 2 : ℝ) / (P : ℝ) := by linarith
  exact h₇



lemma combine_k0_kneq0_bounds
    (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d]
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) :
    let P := largestPrimeFactor n
    let R := ⌈Real.log (n : ℝ)⌉₊
    ∀ (S0 Sneq0 : ℝ),
    S0 ≤ (1 + Real.log ↑n) / ↑d →
    Sneq0 ≤ 6 * ↑R * (1 + Real.log ↑n) ^ 2 / ↑d →
    S0 + Sneq0 ≤ 7 * ↑R * (1 + Real.log ↑n) ^ 2 / (P : ℝ) := by
  intro P R S0 Sneq0 hS0 hSneq0
  exact combine_bounds_arithmetic R P d
    (ceil_log_ge_one n hn)
    (largestPrimeFactor_pos n hn)
    (Nat.pos_of_ne_zero (NeZero.ne d))
    (hd ▸ d_ge_P n hn)
    (↑n) (Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < n)))
    S0 Sneq0 hS0 hSneq0


lemma good_p_double_sum_bound
    (n d : ℕ) [NeZero n] [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (p q : ℤ)
    (hp_pos : 1 ≤ p) (hq_pos : 1 ≤ q)
    (hpq : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2)
    (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (hp_coprime : ¬ ((largestPrimeFactor n : ℤ) ∣ p))
    (u_val : ℕ)
    (hu_congr : (p : ZMod d) = (u_val : ZMod d)) :
    let P := largestPrimeFactor n
    let R := ⌈Real.log (n : ℝ)⌉₊
    let mp := (2 * p - 1).toNat
    let mq := (2 * q - 1).toNat
    (∑ k : ZMod n, ∑ l : ZMod n,
      if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑u_val + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mq) l‖ /
           (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
      else 0) ≤ 6 * ↑R * (1 + Real.log ↑n) ^ 2 / ↑d →
    (∑ k : ZMod n, ∑ l : ZMod n,
      if (k, l) ≠ (0, 0) ∧
         ((d : ℤ)) ∣ (ZMod.val k * p + ZMod.val l * q)
      then ‖normalizedDFT n (intervalIndicator n mp) k‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) ≤
      7 * ↑R * (1 + Real.log ↑n) ^ 2 / (P : ℝ) := by
  intro P R mp mq hS
  have _ := hp_coprime
  have hsplit := double_sum_split_k0_kneq0 n d mp mq p q
  rw [hsplit]
  have hk0 := k_zero_contribution_bound n d hn hd p q hp_pos hq_pos hpq hq_coprime
  have hkneq0 := k_nonzero_contribution_bound n d hn hd p q hp_pos hq_pos hpq u_val hu_congr
  have hkneq0_final : (∑ k : ZMod n, ∑ l : ZMod n,
      if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * p + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n mp) k‖ *
           ‖normalizedDFT n (intervalIndicator n mq) l‖
      else (0 : ℝ)) ≤ 6 * ↑R * (1 + Real.log ↑n) ^ 2 / ↑d :=
    le_trans hkneq0 hS
  exact combine_k0_kneq0_bounds n hn d hd _ _ hk0 hkneq0_final


lemma int_not_dvd_imp_nat_not_dvd
    (P : ℕ) (p : ℤ) (_hp_pos : 1 ≤ p) (hp_not_dvd : ¬ ((P : ℤ) ∣ p)) :
    ¬ P ∣ p.natAbs := by
  intro h
  have h₁ : (P : ℤ) ∣ p := by
    have h₂ : (P : ℕ) ∣ p.natAbs := h
    have h₃ : (P : ℤ) ∣ p := by
      rw [Int.natCast_dvd]
      exact h₂
    exact h₃
  exact hp_not_dvd h₁


lemma natAbs_mod_eq_emod_toNat
    (d : ℕ) (d_pos : 0 < d) (p : ℤ) (hp_pos : 1 ≤ p) :
    p.natAbs % d = (p % (d : ℤ)).toNat := by
  have hp_nn : 0 ≤ p := by omega
  have h₁ : p.natAbs = p.toNat := by omega
  rw [h₁, Int.toNat_emod hp_nn (by omega : (0 : ℤ) ≤ ↑d)]
  simp


lemma intCast_eq_natCast_of_pos
    (d : ℕ) [NeZero d] (p : ℤ) (hp_pos : 1 ≤ p) :
    (p : ZMod d) = (p.natAbs : ZMod d) := by
  have h_p_nonneg : 0 ≤ (p : ℤ) := by nlinarith
  have h_toNat_eq_natAbs : p.toNat = p.natAbs := by grind
  have h_int_cast_eq_toNat_cast : (p : ZMod d) = (p.toNat : ZMod d) := by
    exact Eq.symm (ZMod.natCast_toNat d h_p_nonneg)
  have h_main : (p : ZMod d) = (p.natAbs : ZMod d) := by simp_all
  assumption


lemma p_mod_d_unit
    (n d : ℕ) [NeZero d] (hn : 2 ≤ n)
    (hd : d = largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (p : ℤ) (hp_pos : 1 ≤ p)
    (hp_coprime : ¬ ((largestPrimeFactor n : ℤ) ∣ p)) :
    ∃ u : (ZMod d)ˣ,
      (u : ZMod d).val = (p % (d : ℕ)).toNat ∧
      (p : ZMod d) = (u : ZMod d) := by
  have hP_prime : Nat.Prime (largestPrimeFactor n) := largest_prime_factor_prime n hn
  have hp_not_dvd_nat : ¬ largestPrimeFactor n ∣ p.natAbs :=
    int_not_dvd_imp_nat_not_dvd (largestPrimeFactor n) p hp_pos hp_coprime
  have hp_natAbs_coprime_d : p.natAbs.Coprime d := by
    rw [hd]
    exact Nat.Prime.coprime_pow_of_not_dvd hP_prime hp_not_dvd_nat
  exact ⟨ZMod.unitOfCoprime p.natAbs hp_natAbs_coprime_d,
    by rw [val_unitOfCoprime_eq_mod]
       exact natAbs_mod_eq_emod_toNat d (NeZero.pos d) p hp_pos,
    by rw [ZMod.coe_unitOfCoprime, intCast_eq_natCast_of_pos d p hp_pos]⟩



lemma double_sum_bad_set_construction
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (hq_pos : 1 ≤ q) (hq_bound : (q : ℝ) < (n : ℝ) / 2) :
    let P := largestPrimeFactor n
    let d := P ^ n.factorization P
    let R := ⌈Real.log (n : ℝ)⌉₊
    ∃ B : Finset ℕ, B.card ≤ d / R ∧
      ∀ p : ℤ, ¬ ((P : ℤ) ∣ p) →
        1 ≤ p →
        (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 →
        (p % (d : ℕ)).toNat ∉ B →
        (∑ k : ZMod n, ∑ l : ZMod n,
          if (k, l) ≠ (0, 0) ∧
             ((largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℤ)) ∣
               (ZMod.val k * p + ZMod.val l * q)
          then ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
               ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖
          else (0 : ℝ)) ≤
          7 * R * (1 + Real.log (n : ℝ)) ^ 2 / (P : ℝ) := by
  intro P d R
  haveI hd_pos : NeZero d := ⟨by positivity [d_pos n hn]⟩
  have havg := average_S_bound n d hn rfl q hq_coprime hq_pos hq_bound
    ((2 * q - 1).toNat) rfl
  have hS_nonneg : ∀ u : (ZMod d)ˣ, 0 ≤
    (∑ k : ZMod n, ∑ l : ZMod n,
      if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖ /
           (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
      else 0) := by
    intro u; apply Finset.sum_nonneg; intro k _; apply Finset.sum_nonneg; intro l _
    split_ifs with h
    · apply div_nonneg (norm_nonneg _)
      apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      exact le_min (Nat.cast_nonneg _)
        (sub_nonneg.mpr (by exact_mod_cast (ZMod.val_lt k).le))
    · exact le_refl _
  have havg_nonneg : (0 : ℝ) ≤ 6 * (1 + Real.log ↑n) ^ 2 / ↑d := by
    apply div_nonneg
    · apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (sq_nonneg _)
    · exact Nat.cast_nonneg _
  obtain ⟨B, hBcard, hBbound⟩ := bad_set_from_average d
    (fun u => ∑ k : ZMod n, ∑ l : ZMod n,
      if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖ /
           (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
      else 0)
    hS_nonneg
    (6 * (1 + Real.log ↑n) ^ 2 / ↑d)
    havg_nonneg
    havg
    R
    (ceil_log_ge_one n hn)
  exact ⟨B, hBcard, fun p hp_cop hp_pos hpq hp_not_in_B => by
    obtain ⟨u, hu_val, hu_eq⟩ := p_mod_d_unit n d hn rfl p hp_pos hp_cop
    have hS_bound := hBbound u (hu_val ▸ hp_not_in_B)
    have hS_bound' : (∑ k : ZMod n, ∑ l : ZMod n,
      if k ≠ 0 ∧ ((d : ℤ) ∣ (↑(ZMod.val k) * ↑(u : ZMod d).val + ↑(ZMod.val l) * q))
      then ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖ /
           (2 * min (ZMod.val k : ℝ) ((n : ℝ) - ZMod.val k))
      else 0) ≤ 6 * ↑R * (1 + Real.log ↑n) ^ 2 / ↑d := by
      calc _ ≤ ↑R * (6 * (1 + Real.log ↑n) ^ 2 / ↑d) := hS_bound
        _ = 6 * ↑R * (1 + Real.log ↑n) ^ 2 / ↑d := by ring
    have hu_congr : (p : ZMod d) = ((u : ZMod d).val : ZMod d) := by
      rw [ZMod.natCast_zmod_val]; exact hu_eq
    exact good_p_double_sum_bound n d hn rfl p q hp_pos hq_pos hpq hq_coprime hp_cop
      (u : ZMod d).val hu_congr hS_bound'⟩


lemma error_EPalpha_markov
    (n : ℕ) (hn : 2 ≤ n)
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (hq_pos : 1 ≤ q) (hq_bound : (q : ℝ) < (n : ℝ) / 2) :
    haveI : NeZero n := ⟨by omega⟩
    let P := largestPrimeFactor n
    let d := P ^ n.factorization P
    let R := ⌈Real.log (n : ℝ)⌉₊
    ∃ B : Finset ℕ, B.card ≤ d / R ∧
      ∀ p : ℤ, ¬ ((P : ℤ) ∣ p) →
        1 ≤ p →
        (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 →
        (p % (d : ℕ)).toNat ∉ B →
        |(errorTermEPalpha n p q).re| ≤
          7 * R * (Nat.totient n : ℝ) *
            (1 + Real.log (n : ℝ)) ^ 2 / (P : ℝ) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨B, hB_card, hB_good⟩ :=
    double_sum_bad_set_construction n hn q hq_coprime hq_pos hq_bound
  refine ⟨B, hB_card, fun p hp_coprime hp_pos hp_bound hp_notinB => ?_⟩
  have h_ds := hB_good p hp_coprime hp_pos hp_bound hp_notinB
  have h_norm := errorTermEPalpha_norm_le_totient_mul n p q
  calc |(errorTermEPalpha n p q).re|
      ≤ ‖errorTermEPalpha n p q‖ := Complex.abs_re_le_norm _
    _ ≤ (Nat.totient n : ℝ) *
        (∑ k : ZMod n, ∑ l : ZMod n,
          if (k, l) ≠ (0, 0) ∧
             ((largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℤ)) ∣
               (ZMod.val k * p + ZMod.val l * q)
          then ‖normalizedDFT n (intervalIndicator n (2 * p - 1).toNat) k‖ *
               ‖normalizedDFT n (intervalIndicator n (2 * q - 1).toNat) l‖
          else 0) := h_norm
    _ ≤ (Nat.totient n : ℝ) *
        (7 * ⌈Real.log (n : ℝ)⌉₊ * (1 + Real.log (n : ℝ)) ^ 2 /
          (largestPrimeFactor n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left h_ds
        exact Nat.cast_nonneg _
    _ = 7 * ⌈Real.log (n : ℝ)⌉₊ * (Nat.totient n : ℝ) *
        (1 + Real.log (n : ℝ)) ^ 2 / (largestPrimeFactor n : ℝ) := by
        ring

lemma error_split_bound
    (n : ℕ) (hn : 2 ≤ n)
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (hq_pos : 1 ≤ q) (hq_bound : (q : ℝ) < (n : ℝ) / 2) :
    ∃ B : Finset ℕ, B.card ≤
      largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
        ⌈Real.log (n : ℝ)⌉₊ ∧
      ∀ p : ℤ, ¬ ((largestPrimeFactor n : ℤ) ∣ p) →
        1 ≤ p →
        (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 →
        (p % (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℕ)).toNat ∉ B →
        |(countingFunctionS n p q : ℝ) -
          ((2 * p - 1).toNat : ℝ) * ((2 * q - 1).toNat : ℝ) *
          (Nat.totient n : ℝ) / (n : ℝ) ^ 2| ≤
        (Nat.totient n : ℝ) * (1 + Real.log (n : ℝ)) ^ 2 /
          ((largestPrimeFactor n : ℝ) - 1) +
        7 * ⌈Real.log (n : ℝ)⌉₊ * (Nat.totient n : ℝ) *
          (1 + Real.log (n : ℝ)) ^ 2 / (largestPrimeFactor n : ℝ) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨B, hB_card, hB_bound⟩ :=
    error_EPalpha_markov n hn q hq_coprime hq_pos hq_bound
  refine ⟨B, hB_card, fun p hp_ndvd hp_pos hp_sum hp_notbad => ?_⟩
  have h_decomp := error_decomposition n hn p q hp_pos hq_pos hp_sum
  have h_EP0 := error_EP0_universal_bound n hn p q hp_pos hq_pos hp_sum
  have h_EPalpha := hB_bound p hp_ndvd hp_pos hp_sum hp_notbad
  rw [h_decomp]
  calc |(@errorTermEP0 n ⟨by omega⟩ p q).re + (@errorTermEPalpha n ⟨by omega⟩ p q).re|
      ≤ |(@errorTermEP0 n ⟨by omega⟩ p q).re| + |(@errorTermEPalpha n ⟨by omega⟩ p q).re| :=
        abs_add_le _ _
    _ ≤ (Nat.totient n : ℝ) * (1 + Real.log (n : ℝ)) ^ 2 /
          ((largestPrimeFactor n : ℝ) - 1) +
        7 * ⌈Real.log (n : ℝ)⌉₊ * (Nat.totient n : ℝ) *
          (1 + Real.log (n : ℝ)) ^ 2 / (largestPrimeFactor n : ℝ) :=
        add_le_add h_EP0 h_EPalpha


lemma combine_error_P0_Palpha
    (n : ℕ) (hn : 2 ≤ n) :
    (Nat.totient n : ℝ) * (1 + Real.log (n : ℝ)) ^ 2 /
      ((largestPrimeFactor n : ℝ) - 1) +
    7 * ⌈Real.log (n : ℝ)⌉₊ * (Nat.totient n : ℝ) *
      (1 + Real.log (n : ℝ)) ^ 2 / (largestPrimeFactor n : ℝ) ≤
    9 * ⌈Real.log (n : ℝ)⌉₊ * (Nat.totient n : ℝ) *
      (1 + Real.log (n : ℝ)) ^ 2 / (largestPrimeFactor n : ℝ) := by
  have hP_ge : 2 ≤ largestPrimeFactor n := largestPrimeFactor_ge_two n hn
  have hR_ge : 1 ≤ ⌈Real.log (n : ℝ)⌉₊ := ceil_log_ge_one n hn
  have hP_real : (2 : ℝ) ≤ (largestPrimeFactor n : ℝ) := by exact_mod_cast hP_ge
  have hR_real : (1 : ℝ) ≤ (⌈Real.log (n : ℝ)⌉₊ : ℝ) := by exact_mod_cast hR_ge
  have hA : (0 : ℝ) ≤ (Nat.totient n : ℝ) * (1 + Real.log (n : ℝ)) ^ 2 := by
    apply mul_nonneg
    · exact Nat.cast_nonneg _
    · positivity
  have key := combine_error_terms_real
    (largestPrimeFactor n : ℝ) (⌈Real.log (n : ℝ)⌉₊ : ℝ)
    ((Nat.totient n : ℝ) * (1 + Real.log (n : ℝ)) ^ 2)
    hP_real hR_real hA
  ring_nf at key ⊢
  linarith


lemma fourier_markov_bad_set
    (n : ℕ) (hn : 2 ≤ n)
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1)
    (hq_pos : 1 ≤ q) (hq_bound : (q : ℝ) < (n : ℝ) / 2) :
    ∃ B : Finset ℕ, B.card ≤
      largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
        ⌈Real.log (n : ℝ)⌉₊ ∧
      ∀ p : ℤ, ¬ ((largestPrimeFactor n : ℤ) ∣ p) →
        1 ≤ p →
        (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 →
        (p % (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℕ)).toNat ∉ B →
        |(countingFunctionS n p q : ℝ) -
          (2 * ↑p - 1) * (2 * ↑q - 1) * (Nat.totient n : ℝ) / (n : ℝ) ^ 2| ≤
        9 * ⌈Real.log (n : ℝ)⌉₊ * (Nat.totient n : ℝ) *
          (1 + Real.log (n : ℝ)) ^ 2 / (largestPrimeFactor n : ℝ) := by
  obtain ⟨B, hB_card, hB_bound⟩ := error_split_bound n hn q hq_coprime hq_pos hq_bound
  exact ⟨B, hB_card, fun p hp_coprime hp_pos hp_bound hp_not_in_B => by
    have h := hB_bound p hp_coprime hp_pos hp_bound hp_not_in_B
    rw [toNat_two_mul_sub_one p hp_pos, toNat_two_mul_sub_one q hq_pos] at h
    exact le_trans h (combine_error_P0_Palpha n hn)⟩
lemma ceil_log_mul_sq_le_cube' (n : ℕ) (hn : 2 ≤ n) :
    9 * ⌈Real.log (n : ℝ)⌉₊ * (1 + Real.log (n : ℝ)) ^ 2 ≤
    9 * (1 + Real.log (n : ℝ)) ^ 3 := by
  have h₁ : (⌈Real.log (n : ℝ)⌉₊ : ℝ) ≤ 1 + Real.log (n : ℝ) := by
    have h₂ : (⌈Real.log (n : ℝ)⌉₊ : ℝ) < Real.log (n : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_lt_add_one (by
        have h₃ : 0 ≤ Real.log (n : ℝ) := by
          apply Real.log_nonneg
          norm_cast;
            (try linarith)
        linarith)
    linarith
  have h₅ : 9 * ⌈Real.log (n : ℝ)⌉₊ * (1 + Real.log (n : ℝ)) ^ 2 ≤ 9 * (1 + Real.log (n : ℝ)) ^ 3 :=
    by
    have h₆ : (⌈Real.log (n : ℝ)⌉₊ : ℝ) * (1 + Real.log (n : ℝ)) ^ 2 ≤ (1 + Real.log (n : ℝ)) ^ 3 :=
      by
      nlinarith [sq_nonneg (1 + Real.log (n : ℝ)), sq_nonneg (Real.log (n : ℝ))]
    calc
      9 * ⌈Real.log (n : ℝ)⌉₊ * (1 + Real.log (n : ℝ)) ^ 2 = 9 * ((⌈Real.log (n : ℝ)⌉₊ : ℝ) * (1 +
        Real.log (n : ℝ)) ^ 2) := by
        simp [mul_assoc]
      _ ≤ 9 * ((1 + Real.log (n : ℝ)) ^ 3) := by
        gcongr
      _ = 9 * (1 + Real.log (n : ℝ)) ^ 3 := by ring
  exact h₅

lemma log_cube_div_P_le_div_rpow' (θ : ℝ) (_hθ_pos : 0 < θ) (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ) :
    9 * (1 + Real.log (n : ℝ)) ^ 3 / (largestPrimeFactor n : ℝ) ≤
    9 * (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ := by
  have h_cube_pos : (1 + Real.log (n : ℝ)) ^ 3 > 0 := by
    have h₂ : (1 + Real.log (n : ℝ)) ^ 3 > 0 := by positivity
    exact h₂
  have h_main : 9 * (1 + Real.log (n : ℝ)) ^ 3 / (largestPrimeFactor n : ℝ) ≤ 9 * (1 +
    Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ := by
    have h₁ : (n : ℝ) ^ θ ≤ (largestPrimeFactor n : ℝ) := by
      linarith
    have h₄ : 9 * (1 + Real.log (n : ℝ)) ^ 3 / (largestPrimeFactor n : ℝ) ≤ 9 * (1 +
      Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ := by
      have h₅ : (n : ℝ) ^ θ ≤ (largestPrimeFactor n : ℝ) := h₁
      calc
        9 * (1 + Real.log (n : ℝ)) ^ 3 / (largestPrimeFactor n : ℝ) ≤ 9 * (1 + Real.log (n : ℝ)) ^
          3 / (n : ℝ) ^ θ := by
          apply div_le_div_of_nonneg_left _ (by positivity) h₅
          linarith
        _ = 9 * (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ := by rfl
    exact h₄
  exact h_main

lemma nine_hundredths_lt_tenth' (η : ℝ) (hη_pos : 0 < η) :
    9 * (η ^ 2 / 100) < η ^ 2 / 10 := by
  have h₁ : 0 < η ^ 2 := pow_pos hη_pos 2
  have h₂ : 9 * (η ^ 2 / 100) = (9 / 100 : ℝ) * η ^ 2 := by ring
  have h₃ : η ^ 2 / 10 = (1 / 10 : ℝ) * η ^ 2 := by ring
  rw [h₂, h₃]
  have h₄ : (9 / 100 : ℝ) * η ^ 2 < (1 / 10 : ℝ) * η ^ 2 := by
    nlinarith
  exact h₄

theorem fourier_without_totient' (η θ : ℝ)
    (hη_pos : 0 < η) (hθ_pos : 0 < θ)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100) :
    9 * ⌈Real.log (n : ℝ)⌉₊ *
      (1 + Real.log (n : ℝ)) ^ 2 / (largestPrimeFactor n : ℝ) <
    η ^ 2 / 10 := by
  have hP_pos : (0 : ℝ) < (largestPrimeFactor n : ℝ) := by
    exact_mod_cast largestPrimeFactor_pos n hn
  have h1 : 9 * ↑⌈Real.log (n : ℝ)⌉₊ * (1 + Real.log (n : ℝ)) ^ 2 /
      (largestPrimeFactor n : ℝ) ≤
      9 * (1 + Real.log (n : ℝ)) ^ 3 / (largestPrimeFactor n : ℝ) := by
    apply div_le_div_of_nonneg_right (ceil_log_mul_sq_le_cube' n hn) (le_of_lt hP_pos)
  have h2 : 9 * (1 + Real.log (n : ℝ)) ^ 3 / (largestPrimeFactor n : ℝ) ≤
      9 * (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ :=
    log_cube_div_P_le_div_rpow' θ hθ_pos n hn hP
  have h3 : 9 * (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < 9 * (η ^ 2 / 100) := by
    rw [mul_div_assoc]
    exact mul_lt_mul_of_pos_left h_small (by positivity)
  have h4 : 9 * (η ^ 2 / 100) < η ^ 2 / 10 := nine_hundredths_lt_tenth' η hη_pos
  linarith

lemma fourier_bound_lt_target (η θ : ℝ)
    (hη_pos : 0 < η) (hθ_pos : 0 < θ)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100) :
    9 * ⌈Real.log (n : ℝ)⌉₊ * (Nat.totient n : ℝ) *
      (1 + Real.log (n : ℝ)) ^ 2 / (largestPrimeFactor n : ℝ) <
    η ^ 2 / 10 * (Nat.totient n : ℝ) := by
  have phi_pos : (0 : ℝ) < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < n)
  have key := fourier_without_totient' η θ hη_pos hθ_pos n hn hP h_small
  calc 9 * ⌈Real.log (n : ℝ)⌉₊ * (Nat.totient n : ℝ) *
      (1 + Real.log (n : ℝ)) ^ 2 / (largestPrimeFactor n : ℝ)
    = (9 * ⌈Real.log (n : ℝ)⌉₊ * (1 + Real.log (n : ℝ)) ^ 2 /
        (largestPrimeFactor n : ℝ)) * (Nat.totient n : ℝ) := by ring
    _ < (η ^ 2 / 10) * (Nat.totient n : ℝ) :=
      mul_lt_mul_of_pos_right key phi_pos

lemma region_implies_bounds (n : ℕ) (η : ℝ) (hη_pos : 0 < η) (hn : 2 ≤ n)
    (p q : ℤ) (hpq : (p, q) ∈ truncatedObtuseRegion n η) :
    1 ≤ p ∧ 1 ≤ q ∧ (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 ∧ (q : ℝ) < (n : ℝ) / 2 := by
  have h₁ : (η : ℝ) * n ≤ (p : ℝ) := by
    simp only [truncatedObtuseRegion, Set.mem_setOf_eq] at hpq
    exact hpq.1
  have h₂ : (η : ℝ) * n ≤ (q : ℝ) := by
    simp only [truncatedObtuseRegion, Set.mem_setOf_eq] at hpq
    exact hpq.2.1
  have h₃ : (p : ℝ) + (q : ℝ) < (n : ℝ) / 2 := by
    simp only [truncatedObtuseRegion, Set.mem_setOf_eq] at hpq
    exact hpq.2.2.1
  have hηn_pos : 0 < (η : ℝ) * n := by
    positivity
  have hp_pos : 1 ≤ p := by
    by_contra h
    have h₅ : p ≤ 0 := by
      linarith
    have h₆ : (p : ℝ) ≤ 0 := by
      exact_mod_cast h₅
    linarith
  have hq_pos : 1 ≤ q := by
    by_contra h
    have h₅ : q ≤ 0 := by
      linarith
    have h₆ : (q : ℝ) ≤ 0 := by
      exact_mod_cast h₅
    linarith
  have hq_bound : (q : ℝ) < (n : ℝ) / 2 := by
    linarith
  exact ⟨hp_pos, hq_pos, h₃, hq_bound⟩

lemma error_bound_with_bad_set (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (_hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (_hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100)
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1) :
    ∃ B : Finset ℕ, B.card ≤
      largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
        ⌈Real.log (n : ℝ)⌉₊ ∧
      ∀ p : ℤ, ¬ ((largestPrimeFactor n : ℤ) ∣ p) →
        (p, q) ∈ truncatedObtuseRegion n η →
        (p % (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℕ)).toNat ∉ B →
        |(countingFunctionS n p q : ℝ) -
          (2 * ↑p - 1) * (2 * ↑q - 1) * (Nat.totient n : ℝ) / (n : ℝ) ^ 2| <
        η ^ 2 / 10 * (Nat.totient n : ℝ) := by
  by_cases hq : 1 ≤ q ∧ (q : ℝ) < (n : ℝ) / 2
  · obtain ⟨hq_pos, hq_bound⟩ := hq
    obtain ⟨B, hB_card, hB_bound⟩ := fourier_markov_bad_set n hn q hq_coprime hq_pos hq_bound
    exact ⟨B, hB_card, fun p hp_coprime hpq hp_good =>
      lt_of_le_of_lt
        (hB_bound p hp_coprime
          (region_implies_bounds n η hη_pos hn p q hpq).1
          (region_implies_bounds n η hη_pos hn p q hpq).2.2.1
          hp_good)
        (fourier_bound_lt_target η θ hη_pos hθ_pos n hn hP h_small)⟩
  · push Not at hq
    exact ⟨∅, by simp, fun p _ hpq _ => by
      exfalso
      have hbds := region_implies_bounds n η hη_pos hn p q hpq
      exact not_lt.mpr (hq hbds.2.1) hbds.2.2.2⟩

lemma combine_main_and_error (η : ℝ) (hη_pos : 0 < η)
    (n : ℕ) (S_val : ℝ) (M_val : ℝ)
    (hM : η ^ 2 * (Nat.totient n : ℝ) ≤ M_val)
    (hE : |S_val - M_val| < η ^ 2 / 10 * (Nat.totient n : ℝ)) :
    η ^ 2 / 2 * (Nat.totient n : ℝ) ≤ S_val := by
  have h4 : (η ^ 2 : ℝ) * (Nat.totient n : ℝ) ≥ 0 := by positivity
  have h6 : S_val ≥ M_val - |S_val - M_val| := by
    obtain h6 | h6 := abs_cases (S_val - M_val) <;> linarith
  have h7 : S_val ≥ η ^ 2 * (Nat.totient n : ℝ) - η ^ 2 / 10 * (Nat.totient n : ℝ) := by
    linarith [h6, hE, hM]
  have h8 : η ^ 2 * (Nat.totient n : ℝ) - η ^ 2 / 10 * (Nat.totient n : ℝ) = (9 : ℝ) / 10 * η ^ 2 *
    (Nat.totient n : ℝ) := by
    ring_nf
  rw [h8] at h7
  linarith

lemma fourier_markov_residue_bound (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100)
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1) :
    ∃ B : Finset ℕ, B.card ≤
      largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
        ⌈Real.log (n : ℝ)⌉₊ ∧
      ∀ p : ℤ, ¬ ((largestPrimeFactor n : ℤ) ∣ p) →
        (p, q) ∈ truncatedObtuseRegion n η →
        (p % (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℕ)).toNat ∉ B →
        (η ^ 2 / 2 : ℝ) * (Nat.totient n : ℝ) ≤ (countingFunctionS n p q : ℝ) := by
  obtain ⟨B, hB_card, hB_error⟩ :=
    error_bound_with_bad_set η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP h_small q hq_coprime
  exact ⟨B, hB_card, fun p hp_coprime hpq hp_notinB => by
    have hE := hB_error p hp_coprime hpq hp_notinB
    have hM := main_term_lower_bound η hη_pos n hn p q hpq
    exact combine_main_and_error η hη_pos n
      (countingFunctionS n p q : ℝ)
      ((2 * ↑p - 1) * (2 * ↑q - 1) * (Nat.totient n : ℝ) / (n : ℝ) ^ 2)
      hM hE⟩
lemma bad_residues_bound (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100)
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1) :
    ∃ B : Finset ℕ, B.card ≤
      largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
        ⌈Real.log (n : ℝ)⌉₊ ∧
      ∀ p : ℤ, (p, q) ∈ residueBadPairs n η →
        (p % (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) : ℕ)).toNat ∈ B := by
  obtain ⟨B, hB_card, hB_good⟩ := fourier_markov_residue_bound η θ hη_pos hη_lt hθ_pos hθ_lt
    n hn hP h_small q hq_coprime
  exact ⟨B, hB_card, fun p hp => by
    by_contra hp_not_mem
    have hp_mem : (p, q) ∈ badPairsE n η := hp.1
    have hp_not_dvd : ¬ ((largestPrimeFactor n : ℤ) ∣ p) := hp.2
    have hp_tor : (p, q) ∈ truncatedObtuseRegion n η := hp_mem.1
    have hS_large := hB_good p hp_not_dvd hp_tor hp_not_mem
    exact counting_large_implies_not_badPairsE n η p q hS_large hp_mem⟩
lemma residue_class_fiber_ncard_le (n d : ℕ) (hd_pos : 0 < d) (b : ℕ)
    (S : Set ℤ) (hS_sub : S ⊆ Set.Ico (0 : ℤ) (↑n / 2))
    (_hS_fin : S.Finite) :
    {x ∈ S | (x % (d : ℤ)).toNat = b}.ncard ≤ n / (2 * d) + 1 := by
  calc {x ∈ S | (x % (d : ℤ)).toNat = b}.ncard
      ≤ (↑(Finset.range (n / (2 * d) + 1)) : Set ℕ).ncard := by
        apply Set.ncard_le_ncard_of_injOn (fun x : ℤ => (x / (d : ℤ)).toNat)
        · intro x hx
          simp only [Finset.mem_coe]
          exact fiber_div_mem_range n d hd_pos b S hS_sub x hx
        · exact fiber_div_injOn n d hd_pos b S hS_sub
    _ = (Finset.range (n / (2 * d) + 1)).card := Set.ncard_coe_finset _
    _ = n / (2 * d) + 1 := Finset.card_range _

lemma subset_biUnion_residue_fibers (d : ℕ) (B : Finset ℕ)
    (S : Set ℤ)
    (hS_res : ∀ x ∈ S, (x % (d : ℤ)).toNat ∈ B) :
    S ⊆ ⋃ b ∈ B, {x ∈ S | (x % (d : ℤ)).toNat = b} := by
  have h_main : ∀ (x : ℤ), x ∈ S → x ∈ ⋃ b ∈ B, {x ∈ S | (x % (d : ℤ)).toNat = b} := by simp_all
  have h_final : S ⊆ ⋃ b ∈ B, {x ∈ S | (x % (d : ℤ)).toNat = b} := by assumption
  exact h_final

lemma ncard_union_residue_classes_bound (n d K : ℕ) (hd_pos : 0 < d)
    (B : Finset ℕ) (hB_card : B.card ≤ K)
    (S : Set ℤ) (hS_sub : S ⊆ Set.Ico (0 : ℤ) (↑n / 2))
    (hS_fin : S.Finite)
    (hS_res : ∀ x ∈ S, (x % (d : ℤ)).toNat ∈ B) :
    S.ncard ≤ K * (n / (2 * d) + 1) := by
  have h_subset : S ⊆ ⋃ b ∈ B, {x ∈ S | (x % (d : ℤ)).toNat = b} :=
    subset_biUnion_residue_fibers d B S hS_res
  have h_union_fin : (⋃ b ∈ B, {x ∈ S | (x % (d : ℤ)).toNat = b}).Finite :=
    Set.Finite.biUnion B.finite_toSet (fun b _ => hS_fin.subset (fun x hx => hx.1))
  have h1 : S.ncard ≤ (⋃ b ∈ B, {x ∈ S | (x % (d : ℤ)).toNat = b}).ncard :=
    Set.ncard_le_ncard h_subset h_union_fin
  have h2 : (⋃ b ∈ B, {x ∈ S | (x % (d : ℤ)).toNat = b}).ncard ≤
      ∑ b ∈ B, {x ∈ S | (x % (d : ℤ)).toNat = b}.ncard :=
    Finset.set_ncard_biUnion_le B _
  have h3 : ∑ b ∈ B, {x ∈ S | (x % (d : ℤ)).toNat = b}.ncard ≤
      ∑ _b ∈ B, (n / (2 * d) + 1) :=
    Finset.sum_le_sum (fun b _ => residue_class_fiber_ncard_le n d hd_pos b S hS_sub hS_fin)
  have h4 : ∑ _b ∈ B, (n / (2 * d) + 1) = B.card * (n / (2 * d) + 1) :=
    Finset.sum_const_nat (fun _ _ => rfl)
  calc S.ncard
      ≤ (⋃ b ∈ B, {x ∈ S | (x % (d : ℤ)).toNat = b}).ncard := h1
    _ ≤ ∑ b ∈ B, {x ∈ S | (x % (d : ℤ)).toNat = b}.ncard := h2
    _ ≤ ∑ _b ∈ B, (n / (2 * d) + 1) := h3
    _ = B.card * (n / (2 * d) + 1) := h4
    _ ≤ K * (n / (2 * d) + 1) := Nat.mul_le_mul_right _ hB_card

lemma fiber_ncard_bound_coprime (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100)
    (q : ℤ) (hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1) :
    {p : ℤ | (p, q) ∈ residueBadPairs n η}.ncard ≤
      (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
        ⌈Real.log (n : ℝ)⌉₊) *
      (n / (2 * largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) + 1) := by
  obtain ⟨B, hB_card, hB_mem⟩ := bad_residues_bound η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP
    h_small q hq_coprime
  exact ncard_union_residue_classes_bound n
    (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n))
    (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) / ⌈Real.log (n : ℝ)⌉₊)
    (by
      apply Nat.pos_of_ne_zero
      intro h
      simp only [Nat.pow_eq_zero] at h
      have : largestPrimeFactor n ≠ 0 := by
        intro h0
        have : (largestPrimeFactor n : ℝ) = 0 := by exact_mod_cast h0
        rw [this] at hP
        have : (n : ℝ) ^ θ ≤ 0 := le_trans (le_of_eq rfl) hP
        have : (0 : ℝ) < (n : ℝ) ^ θ := by positivity
        linarith
      exact this h.1)
    B hB_card
    {p : ℤ | (p, q) ∈ residueBadPairs n η}
    (fiber_subset_range n η hη_pos q)
    (fiber_finite n η hη_pos q)
    (fun x hx => hB_mem x hx)


lemma fiber_ncard_bound (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100)
    (q : ℤ) :
    {p : ℤ | (p, q) ∈ residueBadPairs n η}.ncard ≤
      (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
        ⌈Real.log (n : ℝ)⌉₊) *
      (n / (2 * largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) + 1) := by
  by_cases hq_coprime : Int.gcd q (largestPrimeFactor n : ℤ) = 1
  · exact fiber_ncard_bound_coprime η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP h_small q hq_coprime
  · have h_empty := fiber_empty_of_gcd_ne_one n η q hq_coprime
    simp [h_empty]


lemma pos_of_mem_truncatedObtuseRegion_snd (n : ℕ) (η : ℝ) (hη_pos : 0 < η)
    (pq : ℤ × ℤ) (h : pq ∈ truncatedObtuseRegion n η) :
    0 < pq.2 := by
  have h₂ : (η * (n : ℝ) : ℝ) ≤ (pq.2 : ℝ) := by
    simpa [truncatedObtuseRegion] using h.2.1
  have h₃ : (0 : ℝ) < η * (n : ℝ) := by
    by_cases hn : n = 0
    · have h₆ : (n : ℝ) = 0 := by simp [hn]
      have h₇ : η * (n : ℝ) = 0 := by rw [h₆]; ring
      have h₉ : (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 :=
        by simpa [truncatedObtuseRegion] using h.2.2.1
      have h₁₁ : (pq.1 : ℝ) + (pq.2 : ℝ) < 0 := by linarith
      have h₁₂ : (η * (n : ℝ) : ℝ) ≤ (pq.1 : ℝ) := by
        simpa [truncatedObtuseRegion] using h.1
      linarith
    · have h₇ : (0 : ℝ) < η * (n : ℝ) := by positivity
      linarith
  have h₅ : 0 < pq.2 := by
    by_contra h₆
    have h₇ : pq.2 ≤ 0 := by linarith
    have h₈ : (pq.2 : ℝ) ≤ 0 := by
      exact_mod_cast h₇
    linarith
  exact h₅

lemma pos_of_mem_truncatedObtuseRegion_fst (n : ℕ) (η : ℝ) (hη_pos : 0 < η)
    (pq : ℤ × ℤ) (h : pq ∈ truncatedObtuseRegion n η) :
    0 < pq.1 := by
  have h₁ : η * (n : ℝ) ≤ (pq.1 : ℝ) := h.1
  have h₂ : η * (n : ℝ) ≤ (pq.2 : ℝ) := h.2.1
  have h₃ : (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 := h.2.2.1
  by_cases hn : n = 0
  · have h₅ : (n : ℝ) = 0 := by norm_cast
    have h₆ : η * (n : ℝ) = 0 := by rw [h₅]; ring
    have h₈ : (pq.1 : ℝ) > 0 := by
      by_contra _
      linarith
    have h₉ : 0 < (pq.1 : ℤ) := by
      norm_cast at h₈ ⊢
    exact h₉
  · have h₇ : 0 < η * (n : ℝ) := by positivity
    have h₉ : (pq.1 : ℝ) > 0 := by linarith
    have h₁₀ : 0 < (pq.1 : ℤ) := by
      norm_cast at h₉ ⊢
    exact h₁₀

lemma snd_lt_half_of_mem_truncatedObtuseRegion' (n : ℕ) (η : ℝ)
    (pq : ℤ × ℤ) (h : pq ∈ truncatedObtuseRegion n η) (hp_pos : 0 < pq.1) :
    (pq.2 : ℝ) < (n : ℝ) / 2 := by
  simp only [truncatedObtuseRegion] at h
  have h₁ : (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 := by
    exact h.2.2.1
  have h₂ : 0 < (pq.1 : ℝ) := by exact_mod_cast hp_pos
  linarith

lemma intLe_half_of_real_lt_half (n : ℕ) (q : ℤ) (hq : (q : ℝ) < (n : ℝ) / 2) :
    q ≤ ↑n / 2 := by
  have h₂ : (2 : ℝ) * (q : ℝ) < (n : ℝ) := by linarith
  have h₃ : (2 : ℤ) * q < (n : ℤ) := by norm_cast at h₂ ⊢
  have h₅ : q ≤ (n : ℤ) / 2 := by omega
  simpa [Int.ediv_eq_zero_of_lt] using h₅

lemma snd_mem_Icc_of_mem_residueBadPairs (n : ℕ) (η : ℝ) (hη : 0 < η) (_hn : 2 ≤ n)
    (pq : ℤ × ℤ) (hpq : pq ∈ residueBadPairs n η) :
    pq.2 ∈ Finset.Icc (1 : ℤ) (↑n / 2) := by
  have hbad : pq ∈ badPairsE n η := hpq.1
  have htor : pq ∈ truncatedObtuseRegion n η := hbad.1
  have hq_pos : 0 < pq.2 := pos_of_mem_truncatedObtuseRegion_snd n η hη pq htor
  have h1 : 1 ≤ pq.2 := hq_pos
  have hp_pos : 0 < pq.1 := pos_of_mem_truncatedObtuseRegion_fst n η hη pq htor
  have hq_lt : (pq.2 : ℝ) < (n : ℝ) / 2 :=
    snd_lt_half_of_mem_truncatedObtuseRegion' n η pq htor hp_pos
  have h2 : pq.2 ≤ ↑n / 2 := intLe_half_of_real_lt_half n pq.2 hq_lt
  exact Finset.mem_Icc.mpr ⟨h1, h2⟩

lemma fiber_pair_ncard_le (S : Set (ℤ × ℤ)) (q : ℤ) :
    {pq ∈ S | pq.2 = q}.ncard ≤ {p : ℤ | (p, q) ∈ S}.ncard := by
  have h₁ : {pq ∈ S | pq.2 = q} = Set.image (fun p : ℤ => (p, q)) {p : ℤ | (p, q) ∈ S} := by
    ext ⟨a, b⟩; simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨ha, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
    · rintro ⟨_, hp, rfl, rfl⟩; exact ⟨hp, rfl⟩
  have h₂ : Function.Injective (fun p : ℤ => (p, q)) := by exact fun a b hab => (Prod.mk.inj hab).1
  have h₃ : {pq ∈ S | pq.2 = q}.ncard ≤ {p : ℤ | (p, q) ∈ S}.ncard :=
    by rw [h₁]; exact (Set.ncard_image_of_injective _ h₂).le
  exact h₃

lemma card_Icc_one_half_le (n : ℕ) (hn : 2 ≤ n) :
    (Finset.Icc (1 : ℤ) (↑n / 2)).card ≤ n / 2 := by
  have h₁ : (Finset.Icc (1 : ℤ) (↑n / 2)).card = ((↑n / 2 : ℤ) + 1 - 1).toNat := by
    simp
  rw [h₁]
  have h₂ : ((↑n / 2 : ℤ) + 1 - 1 : ℤ) = ↑n / 2 := by ring_nf
  rw [h₂]
  have h₃ : (↑n / 2 : ℤ).toNat = n / 2 := by
    have h₄ : (n : ℤ) / 2 ≥ 0 := by omega
    have h₅ : (↑n / 2 : ℤ).toNat = (n / 2 : ℕ) := by
      have h₇ : (↑n / 2 : ℤ) = ↑(n / 2 : ℕ) := by
        have h₉ : (n : ℤ) % 2 = 0 ∨ (n : ℤ) % 2 = 1 := by omega
        rcases h₉ with (h₉ | h₉)
        · have h₁₁ : (n : ℤ) / 2 * 2 = (n : ℤ) := by omega
          norm_cast at h₁₁ ⊢
        · have h₁₁ : (n : ℤ) / 2 * 2 + 1 = (n : ℤ) := by omega
          norm_cast at h₁₁ ⊢
      rw [h₇]
      simp
      norm_cast
    rw [h₅]
  rw [h₃]

lemma residueBadPairs_ncard_from_fibers (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (_hη_lt : η < 1 / 6) (_hθ_pos : 0 < θ) (_hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (_hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (_h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100)
    (hfiber : ∀ q : ℤ, {p : ℤ | (p, q) ∈ residueBadPairs n η}.ncard ≤
      (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
        ⌈Real.log (n : ℝ)⌉₊) *
      (n / (2 * largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) + 1)) :
    (residueBadPairs n η).ncard ≤
      n / 2 *
      ((largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
        ⌈Real.log (n : ℝ)⌉₊) *
      (n / (2 * largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) + 1)) := by
  set M := (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
        ⌈Real.log (n : ℝ)⌉₊) *
      (n / (2 * largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) + 1) with hM_def
  set Q := Finset.Icc (1 : ℤ) (↑n / 2) with hQ_def
  have hsub : residueBadPairs n η ⊆ ⋃ q ∈ Q, {pq : ℤ × ℤ | pq ∈ residueBadPairs n η ∧ pq.2 = q} :=
    by
    intro pq hpq
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨pq.2, snd_mem_Icc_of_mem_residueBadPairs n η hη_pos hn pq hpq, hpq, rfl⟩
  calc (residueBadPairs n η).ncard
      ≤ (⋃ q ∈ Q, {pq : ℤ × ℤ | pq ∈ residueBadPairs n η ∧ pq.2 = q}).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet Q |>.biUnion (fun _ _ =>
          (residueBadPairs_finite n η).subset (fun _ h => h.1)))
    _ ≤ ∑ q ∈ Q, ({pq : ℤ × ℤ | pq ∈ residueBadPairs n η ∧ pq.2 = q}).ncard :=
        Finset.set_ncard_biUnion_le Q _
    _ ≤ ∑ q ∈ Q, {p : ℤ | (p, q) ∈ residueBadPairs n η}.ncard := by
        apply Finset.sum_le_sum
        intro q _
        exact fiber_pair_ncard_le (residueBadPairs n η) q
    _ ≤ ∑ _q ∈ Q, M := by
        apply Finset.sum_le_sum
        intro q _
        exact hfiber q
    _ = Q.card * M := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (n / 2) * M := by
        apply Nat.mul_le_mul_right
        exact card_Icc_one_half_le n hn


lemma residueBadPairs_ncard_le_counting (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100) :
    (residueBadPairs n η).ncard ≤
      n / 2 *
      (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
        ⌈Real.log (n : ℝ)⌉₊) *
      (n / (2 * largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) + 1) := by
  have hfibers := residueBadPairs_ncard_from_fibers η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP
    h_small (fiber_ncard_bound η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP h_small)
  linarith [Nat.mul_assoc (n / 2)
    (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) / ⌈Real.log ↑n⌉₊)
    (n / (2 * largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) + 1)]

lemma nat_div_le_mul_div_mul (a b : ℕ) : a / b ≤ 2 * a / (2 * b) := by
  by_cases h : b = 0
  · simp_all
  · have h₁ : a / b * b ≤ a := by exact Nat.div_mul_le_self _ _
    have h₂ : a / b * (2 * b) ≤ 2 * a := by nlinarith
    have h₃ : 2 * b > 0 := by omega
    have h₄ : a / b ≤ 2 * a / (2 * b) := by exact Nat.le_div_iff_mul_le h₃ |>.mpr h₂
    assumption

lemma nat_div_prod_le (a b c d : ℕ) (hc : 0 < c) (hd : 0 < d) :
    (a / c) * (b / d) ≤ (a * b) / (c * d) := by
  have h₁ : (a / c) * c ≤ a := Nat.div_mul_le_self a c
  have h₂ : (b / d) * d ≤ b := Nat.div_mul_le_self b d
  have h₃ : (a / c) * (b / d) * (c * d) ≤ a * b := by
    have h₄ : (a / c) * (b / d) * (c * d) = ((a / c) * c) * ((b / d) * d) := by
      ring
    rw [h₄]
    have h₅ : ((a / c) * c) * ((b / d) * d) ≤ a * b := by
      calc
        ((a / c) * c) * ((b / d) * d) = (a / c * c) * (b / d * d) := by rfl
        _ ≤ a * (b / d * d) := by
          gcongr
        _ ≤ a * b := by
          gcongr
    exact h₅
  have h₆ : (a / c) * (b / d) ≤ (a * b) / (c * d) := by
    have h₉ : (a / c) * (b / d) ≤ (a * b) / (c * d) := by
      apply Nat.le_div_iff_mul_le (by positivity) |>.mpr
      nlinarith
    exact h₉
  exact h₆

lemma dR_mul_n2d_le_n2R (n d R : ℕ) (hd_pos : 0 < d) (hR_pos : 0 < R)
    (hd_dvd : d ∣ n) :
    d / R * (n / (2 * d)) ≤ n / (2 * R) := by
  have h2d_pos : 0 < 2 * d := Nat.mul_pos (by norm_num) hd_pos
  calc d / R * (n / (2 * d))
      ≤ (d * n) / (R * (2 * d)) := nat_div_prod_le d n R (2 * d) hR_pos h2d_pos
    _ = (d * n) / (d * (2 * R)) := by ring_nf
    _ = n / (2 * R) := by
        obtain ⟨k, hk⟩ := hd_dvd
        subst hk
        show d * (d * k) / (d * (2 * R)) = d * k / (2 * R)
        rw [Nat.mul_div_mul_left _ _ hd_pos]

lemma n2_mul_n2R_le_nsq_4R (n R : ℕ) (hR_pos : 0 < R) :
    n / 2 * (n / (2 * R)) ≤ n ^ 2 / (4 * R) := by
  have h2R_pos : 0 < 2 * R := Nat.mul_pos (by norm_num) hR_pos
  calc n / 2 * (n / (2 * R))
      ≤ (n * n) / (2 * (2 * R)) := nat_div_prod_le n n 2 (2 * R) (by norm_num) h2R_pos
    _ = n ^ 2 / (4 * R) := by ring_nf

theorem product_bound_first_term (n d R : ℕ) (hd_pos : 0 < d) (hR_pos : 0 < R)
    (hd_dvd : d ∣ n) :
    n / 2 * (d / R) * (n / (2 * d)) ≤ n ^ 2 / (4 * R) := by
  calc n / 2 * (d / R) * (n / (2 * d))
      = n / 2 * (d / R * (n / (2 * d))) := by ring
    _ ≤ n / 2 * (n / (2 * R)) := by
        apply Nat.mul_le_mul_left
        exact dR_mul_n2d_le_n2R n d R hd_pos hR_pos hd_dvd
    _ ≤ n ^ 2 / (4 * R) := n2_mul_n2R_le_nsq_4R n R hR_pos

lemma product_bound_second_term (n d R : ℕ) (hR_pos : 0 < R) (hd_le : d ≤ n) :
    n / 2 * (d / R) ≤ n ^ 2 / (2 * R) := by
  have h₁ : n / 2 * (d / R) ≤ n / 2 * (n / R) := by
    have h₂ : d / R ≤ n / R := by
      apply Nat.div_le_div_right
      linarith
    have h₃ : 0 ≤ n / 2 := by positivity
    nlinarith
  have h₂ : n / 2 * (n / R) ≤ n ^ 2 / (2 * R) := by
    have h₄ : n / 2 * (n / R) ≤ n ^ 2 / (2 * R) := by
      have h₅ : n / 2 * (n / R) ≤ n ^ 2 / (2 * R) := by
        calc
          n / 2 * (n / R) ≤ n / 2 * (n / R) := le_refl _
          _ ≤ n ^ 2 / (2 * R) := by
            have h₆ : (n / 2) * (n / R) * (2 * R) ≤ n ^ 2 := by
              have h₇ : (n / 2) * 2 ≤ n := by
                have h₇₁ : n / 2 * 2 ≤ n := by
                  have h₇₂ : n / 2 * 2 ≤ n := by
                    apply Nat.div_mul_le_self
                  exact h₇₂
                exact h₇₁
              have h₈ : (n / R) * R ≤ n := by
                have h₈₁ : (n / R) * R ≤ n := by
                  apply Nat.div_mul_le_self
                exact h₈₁
              calc
                (n / 2) * (n / R) * (2 * R) = ((n / 2) * (n / R)) * (2 * R) := by ring
                _ = (n / 2) * 2 * ((n / R) * R) := by ring
                _ ≤ n * ((n / R) * R) := by
                  gcongr
                _ ≤ n * n := by
                  gcongr
                _ = n ^ 2 := by ring
            have h₁₀ : (n / 2) * (n / R) ≤ n ^ 2 / (2 * R) := by
              apply Nat.le_div_iff_mul_le (by positivity) |>.mpr
              nlinarith
            exact h₁₀
      exact h₅
    exact h₄
  calc
    n / 2 * (d / R) ≤ n / 2 * (n / R) := h₁
    _ ≤ n ^ 2 / (2 * R) := h₂

lemma combine_frac_bounds (n R : ℕ) (hR_pos : 0 < R) :
    n ^ 2 / (4 * R) + n ^ 2 / (2 * R) ≤ 3 * n ^ 2 / (4 * R) := by
  have h₁ : (n ^ 2 / (4 * R)) * (4 * R) ≤ n ^ 2 := by
    have h₂ : (n ^ 2 / (4 * R)) * (4 * R) ≤ n ^ 2 := Nat.div_mul_le_self (n ^ 2) (4 * R)
    exact h₂
  have h₂ : (n ^ 2 / (2 * R)) * (2 * R) ≤ n ^ 2 := by
    have h₃ : (n ^ 2 / (2 * R)) * (2 * R) ≤ n ^ 2 := Nat.div_mul_le_self (n ^ 2) (2 * R)
    exact h₃
  have h₄ : (n ^ 2 / (4 * R) + n ^ 2 / (2 * R)) * (4 * R) ≤ 3 * n ^ 2 := by
    have h₅ : (n ^ 2 / (4 * R) + n ^ 2 / (2 * R)) * (4 * R) = (n ^ 2 / (4 * R)) * (4 * R) + (n ^ 2 /
      (2 * R)) * (4 * R) := by
      ring_nf
    rw [h₅]
    linarith
  have h₅ : n ^ 2 / (4 * R) + n ^ 2 / (2 * R) ≤ 3 * n ^ 2 / (4 * R) := by
    have h₇ : (n ^ 2 / (4 * R) + n ^ 2 / (2 * R)) * (4 * R) ≤ 3 * n ^ 2 := h₄
    have h₈ : n ^ 2 / (4 * R) + n ^ 2 / (2 * R) ≤ 3 * n ^ 2 / (4 * R) := by
      apply Nat.le_div_iff_mul_le (by positivity) |>.mpr
      (try omega)
    exact h₈
  exact h₅

lemma counting_bound_simplify (n : ℕ) (hn : 2 ≤ n)
    (hP_pos : 0 < largestPrimeFactor n) :
    n / 2 *
    (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
      ⌈Real.log (n : ℝ)⌉₊) *
    (n / (2 * largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) + 1) ≤
    3 * n ^ 2 / (4 * ⌈Real.log (n : ℝ)⌉₊) := by
  set P := largestPrimeFactor n
  set d := P ^ n.factorization P
  set R := ⌈Real.log (n : ℝ)⌉₊
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
  have hR_pos : 0 < R := by
    apply Nat.ceil_pos.mpr
    apply Real.log_pos
    exact_mod_cast hn
  have hd_dvd : d ∣ n := Nat.ordProj_dvd n P
  have hd_le : d ≤ n := Nat.le_of_dvd (by omega) hd_dvd
  rw [Nat.mul_add]
  simp only [Nat.mul_one]
  calc n / 2 * (d / R) * (n / (2 * d)) + n / 2 * (d / R)
      ≤ n ^ 2 / (4 * R) + n ^ 2 / (2 * R) :=
        Nat.add_le_add (product_bound_first_term n d R hd_pos hR_pos hd_dvd)
          (product_bound_second_term n d R hR_pos hd_le)
    _ ≤ 3 * n ^ 2 / (4 * R) := combine_frac_bounds n R hR_pos


lemma residueBadPairs_ncard_le_nat (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100) :
    (residueBadPairs n η).ncard ≤ 3 * n ^ 2 / (4 * ⌈Real.log (n : ℝ)⌉₊) := by
  calc (residueBadPairs n η).ncard
      ≤ n / 2 *
        (largestPrimeFactor n ^ n.factorization (largestPrimeFactor n) /
          ⌈Real.log (n : ℝ)⌉₊) *
        (n / (2 * largestPrimeFactor n ^ n.factorization (largestPrimeFactor n)) + 1) :=
        residueBadPairs_ncard_le_counting η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP h_small
    _ ≤ 3 * n ^ 2 / (4 * ⌈Real.log (n : ℝ)⌉₊) :=
        counting_bound_simplify n hn (largestPrimeFactor_pos n hn)

lemma ncard_nat_to_real_bound (ncard_val n : ℕ) (_hn : 2 ≤ n)
    (h : ncard_val ≤ 3 * n ^ 2 / (4 * ⌈Real.log (n : ℝ)⌉₊)) :
    (ncard_val : ℝ) ≤ 3 / 4 * (n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊ := by
  have h₁ : (ncard_val : ℝ) ≤ ( (3 * n ^ 2 / (4 * ⌈Real.log (n : ℝ)⌉₊) : ℕ) : ℝ ) := by simp_all
  have h₂ : ( (3 * n ^ 2 / (4 * ⌈Real.log (n : ℝ)⌉₊) : ℕ) : ℝ ) ≤ ( (3 * n ^ 2 : ℕ) : ℝ ) / ( (4 *
    ⌈Real.log (n : ℝ)⌉₊ : ℕ) : ℝ ) := by exact Nat.cast_div_le
  have h₃ : ( (3 * n ^ 2 : ℕ) : ℝ ) / ( (4 * ⌈Real.log (n : ℝ)⌉₊ : ℕ) : ℝ ) = (3 : ℝ) / 4 *
    (n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊ := by
    push_cast; ring
  have h₄ : (ncard_val : ℝ) ≤ 3 / 4 * (n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊ := by nlinarith
  exact h₄

lemma residueBadPairs_ncard_le (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100) :
    ((residueBadPairs n η).ncard : ℝ) ≤ 3 / 4 * (n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊ := by
  exact ncard_nat_to_real_bound _ n hn
    (residueBadPairs_ncard_le_nat η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP h_small)

lemma three_fourths_ceil_le_inv_log (n : ℕ) (hn : 2 ≤ n) :
    3 / 4 * (n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊ ≤ (n : ℝ) ^ 2 / Real.log (n : ℝ) := by
  have h₁ : (n : ℝ) ≥ 2 := by exact_mod_cast hn
  have h₂ : Real.log (n : ℝ) > 0 := by
    have h₂₁ : (1 : ℝ) < (n : ℝ) := by linarith
    exact Real.log_pos h₂₁
  have h₃ : (⌈Real.log (n : ℝ)⌉₊ : ℝ) ≥ Real.log (n : ℝ) := by
    exact Nat.le_ceil _
  have h₆ : (3 / 4 : ℝ) * ((n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊) ≤ ((n : ℝ) ^ 2 /
    ⌈Real.log (n : ℝ)⌉₊) := by
    have h₆₁ : (n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊ ≥ 0 := by positivity
    nlinarith
  have h₇ : ((n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊) ≤ ((n : ℝ) ^ 2 / Real.log (n : ℝ)) := by
    have h₇₇ : 1 / (⌈Real.log (n : ℝ)⌉₊ : ℝ) ≤ 1 / Real.log (n : ℝ) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast h₃
    calc
      ((n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊) = (n : ℝ) ^ 2 * (1 / (⌈Real.log (n : ℝ)⌉₊ : ℝ)) :=
        by field_simp
      _ ≤ (n : ℝ) ^ 2 * (1 / Real.log (n : ℝ)) := by gcongr
      _ = ((n : ℝ) ^ 2 / Real.log (n : ℝ)) := by field_simp
  have h₈ : (3 / 4 : ℝ) * ((n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊) ≤ ((n : ℝ) ^ 2 / Real.log (n : ℝ)) :=
    by
    linarith
  have h₉ : 3 / 4 * (n : ℝ) ^ 2 / ⌈Real.log (n : ℝ)⌉₊ = (3 / 4 : ℝ) * ((n : ℝ) ^ 2 /
    ⌈Real.log (n : ℝ)⌉₊) := by
    ring_nf
  rw [h₉]
  exact h₈

lemma residueBadPairs_ncard_bound (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100) :
    ((residueBadPairs n η).ncard : ℝ) ≤ (n : ℝ) ^ 2 / Real.log n :=
  le_trans
    (residueBadPairs_ncard_le η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP h_small)
    (three_fourths_ceil_le_inv_log n hn)


lemma pos_of_mem_truncatedObtuseRegion_fst_pd (n : ℕ) (η : ℝ) (hη_pos : 0 < η)
    (pq : ℤ × ℤ) (h : pq ∈ truncatedObtuseRegion n η) :
    0 < pq.1 := by
  have h₁ : η * (n : ℝ) ≤ (pq.1 : ℝ) := h.1
  have h₂ : η * (n : ℝ) ≤ (pq.2 : ℝ) := h.2.1
  have h₃ : (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 := h.2.2.1
  by_cases hn : n = 0
  · have h₅ : (n : ℝ) = 0 := by norm_cast
    have h₆ : η * (n : ℝ) = 0 := by rw [h₅]; ring
    have h₈ : (pq.1 : ℝ) > 0 := by
      by_contra _
      linarith
    have h₉ : 0 < (pq.1 : ℤ) := by
      norm_cast at h₈ ⊢
    exact h₉
  · have h₇ : 0 < η * (n : ℝ) := by positivity
    have h₉ : (pq.1 : ℝ) > 0 := by linarith
    have h₁₀ : 0 < (pq.1 : ℤ) := by
      norm_cast at h₉ ⊢
    exact h₁₀

lemma pos_of_mem_truncatedObtuseRegion_snd_pd (n : ℕ) (η : ℝ) (hη_pos : 0 < η)
    (pq : ℤ × ℤ) (h : pq ∈ truncatedObtuseRegion n η) :
    0 < pq.2 := by
  have h₂ : (η * (n : ℝ) : ℝ) ≤ (pq.2 : ℝ) := by
    simpa [truncatedObtuseRegion] using h.2.1
  have h₃ : (0 : ℝ) < η * (n : ℝ) := by
    by_cases hn : n = 0
    · have h₆ : (n : ℝ) = 0 := by simp [hn]
      have h₇ : η * (n : ℝ) = 0 := by rw [h₆]; ring
      have h₉ : (pq.1 : ℝ) + (pq.2 : ℝ) < (n : ℝ) / 2 :=
        by simpa [truncatedObtuseRegion] using h.2.2.1
      have h₁₁ : (pq.1 : ℝ) + (pq.2 : ℝ) < 0 := by linarith
      have h₁₂ : (η * (n : ℝ) : ℝ) ≤ (pq.1 : ℝ) := by
        simpa [truncatedObtuseRegion] using h.1
      linarith
    · have h₇ : (0 : ℝ) < η * (n : ℝ) := by positivity
      linarith
  have h₅ : 0 < pq.2 := by
    by_contra h₆
    have h₇ : pq.2 ≤ 0 := by linarith
    have h₈ : (pq.2 : ℝ) ≤ 0 := by
      exact_mod_cast h₇
    linarith
  exact h₅

lemma fst_lt_half_of_mem_truncatedObtuseRegion (n : ℕ) (η : ℝ)
    (pq : ℤ × ℤ) (h : pq ∈ truncatedObtuseRegion n η) (hq_pos : 0 < pq.2) :
    (pq.1 : ℝ) < (n : ℝ) / 2 := by
  have h₃ : ((pq.1 : ℝ) + (pq.2 : ℝ) : ℝ) < (n : ℝ) / 2 := h.2.2.1
  have h₄ : (pq.2 : ℝ) > 0 := by exact_mod_cast hq_pos
  have h₅ : (pq.1 : ℝ) < (n : ℝ) / 2 := by
    linarith
  exact h₅

lemma largestPrimeFactor_le_of_dvd_pos (P : ℕ) (p : ℤ) (hp_pos : 0 < p)
    (hdvd : (P : ℤ) ∣ p) :
    (P : ℤ) ≤ p := by
  have h₁ : (P : ℤ) ≤ p := by
    by_cases h₅ : (P : ℤ) = 0
    · exfalso
      have h₇ : (0 : ℤ) ∣ p := by simpa [h₅] using hdvd
      have h₈ : p = 0 := by
        simpa [h₅] using h₇
      linarith
    · have h₈ : (P : ℤ) ≤ p := by
        have h₉ : (P : ℤ) ∣ p := hdvd
        exact Int.le_of_dvd (by positivity) h₉
      exact h₈
  exact h₁

lemma pdivPairs_empty_of_large_P (n : ℕ) (η : ℝ) (hη_pos : 0 < η)
    (hP_large : n < 2 * largestPrimeFactor n) :
    pdivPairs n η = ∅ := by
  ext pq
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hpq
  have hmem : pq ∈ truncatedObtuseRegion n η := hpq.1
  have hdvd : (largestPrimeFactor n : ℤ) ∣ pq.1 := hpq.2.2
  have hp_pos : 0 < pq.1 := pos_of_mem_truncatedObtuseRegion_fst_pd n η hη_pos pq hmem
  have hq_pos : 0 < pq.2 := pos_of_mem_truncatedObtuseRegion_snd_pd n η hη_pos pq hmem
  have hPle : (largestPrimeFactor n : ℤ) ≤ pq.1 :=
    largestPrimeFactor_le_of_dvd_pos (largestPrimeFactor n) pq.1 hp_pos hdvd
  have hp_lt : (pq.1 : ℝ) < (n : ℝ) / 2 :=
    fst_lt_half_of_mem_truncatedObtuseRegion n η pq hmem hq_pos
  have hPle_real : (largestPrimeFactor n : ℝ) ≤ (pq.1 : ℝ) := by exact_mod_cast hPle
  have hP_large_real : (n : ℝ) < 2 * (largestPrimeFactor n : ℝ) := by exact_mod_cast hP_large
  linarith

lemma pdivPairs_subset_prod_half (n : ℕ) (η : ℝ) (hη_pos : 0 < η) :
    pdivPairs n η ⊆
      {x : ℤ | 0 ≤ x ∧ x ≤ (n / 2 : ℤ) ∧ (largestPrimeFactor n : ℤ) ∣ x} ×ˢ
      Set.Icc (0 : ℤ) (n / 2 : ℤ) := by
  intro ⟨a, b⟩ h
  simp only [pdivPairs, truncatedObtuseRegion, Set.mem_setOf_eq, Set.mem_prod] at h ⊢
  have h₁ : (η : ℝ) * (n : ℝ) ≤ (a : ℝ) := h.1.1
  have h₂ : (η : ℝ) * (n : ℝ) ≤ (b : ℝ) := h.1.2.1
  have h₃ : (a : ℝ) + (b : ℝ) < (n : ℝ) / 2 := h.1.2.2.1
  have h₆ : (largestPrimeFactor n : ℤ) ∣ a := h.2.2
  have hηn : 0 ≤ (η : ℝ) * (n : ℝ) := by positivity
  have h₇ : 0 ≤ a := by exact_mod_cast (by linarith : (0 : ℝ) ≤ (a : ℝ))
  have h₈ : 0 ≤ b := by exact_mod_cast (by linarith : (0 : ℝ) ≤ (b : ℝ))
  have ha2 : (2 * a : ℤ) < (n : ℤ) := by
    have hr : (2 : ℝ) * (a : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast hr
  have hb2 : (2 * b : ℤ) < (n : ℤ) := by
    have hr : (2 : ℝ) * (b : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast hr
  have h₁₁ : (a : ℤ) ≤ (n / 2 : ℤ) := by omega
  have h₁₂ : (b : ℤ) ≤ (n / 2 : ℤ) := by omega
  exact ⟨⟨h₇, h₁₁, h₆⟩, ⟨h₈, h₁₂⟩⟩

lemma ncard_nonneg_multiples_eq (B : ℤ) (P : ℕ) (hP : 0 < P) (hB : 0 ≤ B) :
    ({x : ℤ | 0 ≤ x ∧ x ≤ B ∧ (P : ℤ) ∣ x}).ncard = B.toNat / P + 1 :=
  Nat.le_antisymm (ncard_nonneg_multiples_le B P hP hB) (ncard_nonneg_multiples_ge B P hP hB)

lemma div_two_add_one_le_1 (a : ℕ) (ha : 2 ≤ a) : a / 2 + 1 ≤ a := by
  have h₁ : a / 2 + 1 ≤ a := by
    omega
  exact h₁

lemma ncard_multiples_half_le (n P : ℕ) (hP_pos : 0 < P) (h2P : 2 * P ≤ n) :
    ({x : ℤ | 0 ≤ x ∧ x ≤ (n / 2 : ℤ) ∧ (P : ℤ) ∣ x}).ncard ≤ n / P := by
  have hB : (0 : ℤ) ≤ (n : ℤ) / 2 := by omega
  rw [ncard_nonneg_multiples_eq ((n : ℤ) / 2) P hP_pos hB]
  have h1 : ((n : ℤ) / 2).toNat = n / 2 := by
    have hnn : (0 : ℤ) ≤ ↑n := Int.natCast_nonneg n
    have h2 : (0 : ℤ) < 2 := by omega
    rw [show (2 : ℤ) = ↑(2 : ℕ) from rfl]
    exact int_toNat_ediv_eq (↑n) 2 (by omega) hnn
  rw [h1]
  rw [Nat.div_right_comm]
  apply div_two_add_one_le_1
  rwa [Nat.le_div_iff_mul_le hP_pos]

lemma ncard_Icc_zero_half_le (n : ℕ) (hn : 2 ≤ n) :
    (Set.Icc (0 : ℤ) (n / 2 : ℤ)).ncard ≤ n := by
  rw [Int_Icc_ncard]
  exact div_two_add_one_le_1 n hn

lemma multiples_in_half_finite (n P : ℕ) :
    {x : ℤ | 0 ≤ x ∧ x ≤ (n / 2 : ℤ) ∧ (P : ℤ) ∣ x}.Finite :=
  multiples_finite 0 (n / 2 : ℤ) P

lemma Icc_zero_half_finite (n : ℕ) :
    (Set.Icc (0 : ℤ) (n / 2 : ℤ)).Finite :=
  Set.finite_Icc _ _

lemma prod_half_finite (n P : ℕ) :
    ({x : ℤ | 0 ≤ x ∧ x ≤ (n / 2 : ℤ) ∧ (P : ℤ) ∣ x} ×ˢ
     Set.Icc (0 : ℤ) (n / 2 : ℤ)).Finite :=
  Set.Finite.prod (multiples_in_half_finite n P) (Icc_zero_half_finite n)

lemma nat_div_mul_le_mul_div (n P : ℕ) (hP_pos : 0 < P) :
    (n / P) * n ≤ n * n / P := by
  rw [Nat.le_div_iff_mul_le hP_pos]
  calc (n / P) * n * P = (n / P) * P * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right n (Nat.div_mul_le_self n P)

lemma pdivPairs_ncard_le_when_small_P (n : ℕ) (η : ℝ) (hη_pos : 0 < η)
    (hn : 2 ≤ n)
    (hP_pos : 0 < largestPrimeFactor n)
    (h2P : 2 * largestPrimeFactor n ≤ n) :
    (pdivPairs n η).ncard ≤ n * n / largestPrimeFactor n := by
  let multiples := {x : ℤ | 0 ≤ x ∧ x ≤ (n / 2 : ℤ) ∧ (largestPrimeFactor n : ℤ) ∣ x}
  let interval := Set.Icc (0 : ℤ) (n / 2 : ℤ)
  let prod_set := multiples ×ˢ interval
  have prod_finite : prod_set.Finite := prod_half_finite n (largestPrimeFactor n)
  have subset : pdivPairs n η ⊆ prod_set := pdivPairs_subset_prod_half n η hη_pos
  have ncard_mono : (pdivPairs n η).ncard ≤ prod_set.ncard :=
    Set.ncard_le_ncard subset prod_finite
  have ncard_prod_eq : prod_set.ncard = multiples.ncard * interval.ncard :=
    Set.ncard_prod
  have ncard_multiples := ncard_multiples_half_le n (largestPrimeFactor n) hP_pos h2P
  have ncard_interval := ncard_Icc_zero_half_le n hn
  have ncard_prod_le : prod_set.ncard ≤ (n / largestPrimeFactor n) * n := by
    rw [ncard_prod_eq]
    exact Nat.mul_le_mul ncard_multiples ncard_interval
  have arith_bound := nat_div_mul_le_mul_div n (largestPrimeFactor n) hP_pos
  calc (pdivPairs n η).ncard
      ≤ prod_set.ncard := ncard_mono
    _ ≤ (n / largestPrimeFactor n) * n := ncard_prod_le
    _ ≤ n * n / largestPrimeFactor n := arith_bound

lemma nat_sq_div_le_real (n : ℕ) (P : ℕ) (θ : ℝ)
    (hn : 2 ≤ n) (hP_pos : 0 < P)
    (hP : (P : ℝ) ≥ (n : ℝ) ^ θ) :
    (↑(n * n / P) : ℝ) ≤ (n : ℝ) ^ 2 / (n : ℝ) ^ θ := by
  calc (↑(n * n / P) : ℝ) ≤ ↑(n * n) / ↑P := Nat.cast_div_le
    _ = (n : ℝ) ^ 2 / (P : ℝ) := by rw [Nat.cast_mul, sq]
    _ ≤ (n : ℝ) ^ 2 / (n : ℝ) ^ θ := real_sq_div_mono n P θ hn hP_pos hP

lemma pdivPairs_ncard_bound (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (_hη_lt : η < 1 / 6) (_hθ_pos : 0 < θ) (_hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ) :
    ((pdivPairs n η).ncard : ℝ) ≤ (n : ℝ) ^ 2 / (n : ℝ) ^ θ := by
  by_cases h2P : 2 * largestPrimeFactor n ≤ n
  · have hP_pos : 0 < largestPrimeFactor n := by
      rcases Nat.eq_zero_or_pos (largestPrimeFactor n) with h | h
      · exfalso; rw [h] at hP; simp at hP
        have : (0 : ℝ) < (n : ℝ) ^ θ := by positivity
        linarith
      · exact h
    calc ((pdivPairs n η).ncard : ℝ)
        ≤ ↑(n * n / largestPrimeFactor n) := by
          exact_mod_cast pdivPairs_ncard_le_when_small_P n η hη_pos hn hP_pos h2P
      _ ≤ (n : ℝ) ^ 2 / (n : ℝ) ^ θ :=
          nat_sq_div_le_real n (largestPrimeFactor n) θ hn hP_pos hP
  · push Not at h2P
    have : pdivPairs n η = ∅ := pdivPairs_empty_of_large_P n η hη_pos h2P
    rw [this, Set.ncard_empty]
    simp only [CharP.cast_eq_zero, ge_iff_le]
    apply div_nonneg
    · positivity
    · positivity

lemma badPairsE_subset_union (n : ℕ) (η : ℝ) :
    badPairsE n η ⊆ pdivPairs n η ∪ residueBadPairs n η := by
  intro ⟨p, q⟩ hpq
  simp only [badPairsE, pdivPairs, residueBadPairs, Set.mem_setOf_eq,
             Set.mem_union] at hpq ⊢
  by_cases h : (largestPrimeFactor n : ℤ) ∣ p
  · left
    exact ⟨hpq.1, hpq.2.1, h⟩
  · right
    exact ⟨hpq, h⟩

lemma badPairsE_ncard_le (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100) :
    ((badPairsE n η).ncard : ℝ) ≤
      (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ θ + 1 / Real.log n) := by
  have h_subset := badPairsE_subset_union n η
  have h_finite_pdiv : (pdivPairs n η).Finite :=
    (truncatedObtuseRegion_finite n η).subset (fun _ h => h.1)
  have h_finite_residue : (residueBadPairs n η).Finite :=
    residueBadPairs_finite n η
  have h_finite_union : (pdivPairs n η ∪ residueBadPairs n η).Finite :=
    Set.Finite.union h_finite_pdiv h_finite_residue
  have h_ncard_mono : (badPairsE n η).ncard ≤ (pdivPairs n η ∪ residueBadPairs n η).ncard :=
    Set.ncard_le_ncard h_subset h_finite_union
  have h_ncard_union : ((pdivPairs n η ∪ residueBadPairs n η).ncard : ℝ) ≤
      ((pdivPairs n η).ncard : ℝ) + ((residueBadPairs n η).ncard : ℝ) := by
    have := Set.ncard_union_le (pdivPairs n η) (residueBadPairs n η)
    exact_mod_cast this
  have h_pdiv_bound := pdivPairs_ncard_bound η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP
  have h_residue_bound := residueBadPairs_ncard_bound η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP h_small
  calc ((badPairsE n η).ncard : ℝ)
      ≤ ((pdivPairs n η ∪ residueBadPairs n η).ncard : ℝ) := by exact_mod_cast h_ncard_mono
    _ ≤ ((pdivPairs n η).ncard : ℝ) + ((residueBadPairs n η).ncard : ℝ) := h_ncard_union
    _ ≤ (n : ℝ) ^ 2 / (n : ℝ) ^ θ + (n : ℝ) ^ 2 / Real.log n := by linarith
    _ = (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ θ) + (n : ℝ) ^ 2 * (1 / Real.log n) := by field_simp
    _ = (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ θ + 1 / Real.log n) := by ring

lemma exists_fourier_exceptional_superset (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100) :
    ∃ E' : Set (ℤ × ℤ),
      E'.Finite ∧
      badPairsE n η ⊆ E' ∧
      (E'.ncard : ℝ) ≤ (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ θ + 1 / Real.log n) := by
  use badPairsE n η
  refine ⟨?_, Set.Subset.rfl, ?_⟩
  · exact (truncatedObtuseRegion_finite n η).subset (fun _ h => h.1)
  · exact badPairsE_ncard_le η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP h_small

lemma badPairsE_ncard_bound (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100) :
    ((badPairsE n η).ncard : ℝ) ≤ (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ θ + 1 / Real.log n) := by
  obtain ⟨E', hE'_fin, hE'_sub, hE'_card⟩ :=
    exists_fourier_exceptional_superset η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP h_small
  calc ((badPairsE n η).ncard : ℝ)
      ≤ (E'.ncard : ℝ) := by exact_mod_cast Set.ncard_le_ncard hE'_sub hE'_fin
    _ ≤ (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ θ + 1 / Real.log n) := hE'_card

lemma exceptional_set_construction_single_n (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ)
    (h_small : (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < η ^ 2 / 100) :
    ∃ (E : Set (ℤ × ℤ)),
      E ⊆ truncatedObtuseRegion n η ∧
      E.Finite ∧
      (E.ncard : ℝ) ≤ (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ θ + 1 / Real.log n) ∧
      ∀ pq ∈ truncatedObtuseRegion n η,
        Int.gcd pq.2 (largestPrimeFactor n : ℤ) = 1 →
        pq ∉ E →
        (η ^ 2 / 2 : ℝ) * (Nat.totient n : ℝ) ≤
          (countingFunctionS n pq.1 pq.2 : ℝ) := by
  refine ⟨badPairsE n η, ?_, ?_, ?_, ?_⟩
  · intro pq hpq; exact hpq.1
  · exact (truncatedObtuseRegion_finite n η).subset (fun pq hpq => hpq.1)
  · exact badPairsE_ncard_bound η θ hη_pos hη_lt hθ_pos hθ_lt n hn hP h_small
  · intro pq hpq hgcd hnotE
    by_contra h
    push Not at h
    exact hnotE ⟨hpq, hgcd, h⟩


lemma log_ge_one_of_ge_three (n : ℕ) (hn : 3 ≤ n) : 1 ≤ Real.log (n : ℝ) := by
  have h₀ : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have h₁ : Real.log 3 > 1 := by
    have h₄ : 1 < Real.log 3 := by
      by_contra h
      have h₅ : Real.log 3 ≤ 1 := by linarith
      have h₆ : Real.exp (Real.log 3) ≤ Real.exp 1 := Real.exp_le_exp.mpr h₅
      have h₇ : Real.exp (Real.log 3) = 3 := by
        rw [Real.exp_log (by positivity : (0 : ℝ) < 3)]
      rw [h₇] at h₆
      linarith
    linarith
  have h₃ : Real.log (n : ℝ) ≥ Real.log 3 := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hn
  have h₄ : 1 ≤ Real.log (n : ℝ) := by
    linarith
  exact h₄

lemma one_plus_log_pow_le (n : ℕ) (hn : 3 ≤ n) :
    (1 + Real.log (n : ℝ)) ^ 3 ≤ 8 * Real.log (n : ℝ) ^ 3 := by
  have hlog : 1 ≤ Real.log (n : ℝ) := log_ge_one_of_ge_three n hn
  have h1 : 1 + Real.log (n : ℝ) ≤ 2 * Real.log (n : ℝ) := by linarith
  have h2 : 0 ≤ 1 + Real.log (n : ℝ) := by linarith
  calc (1 + Real.log (n : ℝ)) ^ 3
      ≤ (2 * Real.log (n : ℝ)) ^ 3 := pow_le_pow_left₀ h2 h1 3
    _ = 8 * Real.log (n : ℝ) ^ 3 := by ring

lemma norm_log_pow_le_mul_norm_rpow (θ : ℝ) (hθ : 0 < θ) (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ‖Real.log (n : ℝ) ^ 3‖ ≤ c * ‖(n : ℝ) ^ θ‖ := by
  simp only [← Real.rpow_natCast (Real.log _) 3]
  have h1 : (fun x => Real.log x ^ (3 : ℝ)) =o[Filter.atTop] fun x => x ^ θ :=
    isLittleO_log_rpow_rpow_atTop 3 hθ
  have h2 : ∀ᶠ (x : ℝ) in Filter.atTop, ‖Real.log x ^ (3 : ℝ)‖ ≤ c * ‖x ^ θ‖ :=
    h1.def hc
  exact (tendsto_natCast_atTop_atTop.eventually h2).exists_forall_of_atTop

theorem norm_bound_implies_div_lt (θ : ℝ) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 1 ≤ n)
    (hbound : ‖Real.log (n : ℝ) ^ 3‖ ≤ (ε / 2) * ‖(n : ℝ) ^ θ‖) :
    Real.log (n : ℝ) ^ 3 / (n : ℝ) ^ θ < ε := by
  have h_log_cube_nonneg : 0 ≤ Real.log (n : ℝ) ^ 3 := by
    positivity
  have h_norm_log_cube : ‖(Real.log (n : ℝ) : ℝ) ^ 3‖ = (Real.log (n : ℝ) : ℝ) ^ 3 := by
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg h_log_cube_nonneg]
  have h_n_rpow_pos : 0 < (n : ℝ) ^ θ := by
    exact Real.rpow_pos_of_pos (by positivity) θ
  have h_norm_n_rpow : ‖(n : ℝ) ^ θ‖ = (n : ℝ) ^ θ := by
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_of_lt h_n_rpow_pos)]
  have h_main_ineq : (Real.log (n : ℝ) : ℝ) ^ 3 ≤ (ε / 2) * (n : ℝ) ^ θ := by
    have h₁ : ‖(Real.log (n : ℝ) : ℝ) ^ 3‖ ≤ (ε / 2) * ‖(n : ℝ) ^ θ‖ := hbound
    have h₂ : ‖(Real.log (n : ℝ) : ℝ) ^ 3‖ = (Real.log (n : ℝ) : ℝ) ^ 3 := h_norm_log_cube
    have h₃ : ‖(n : ℝ) ^ θ‖ = (n : ℝ) ^ θ := h_norm_n_rpow
    rw [h₂] at h₁
    rw [h₃] at h₁
    linarith
  have h_div_ineq : (Real.log (n : ℝ) : ℝ) ^ 3 / (n : ℝ) ^ θ ≤ ε / 2 := by
    have h₂ : 0 < (n : ℝ) ^ θ := h_n_rpow_pos
    have h₃ : (Real.log (n : ℝ) : ℝ) ^ 3 / (n : ℝ) ^ θ ≤ (ε / 2) * (n : ℝ) ^ θ / (n : ℝ) ^ θ := by
      gcongr
    have h₄ : (ε / 2) * (n : ℝ) ^ θ / (n : ℝ) ^ θ = ε / 2 := by
      field_simp [h₂.ne']
    rw [h₄] at h₃
    linarith
  have h_final : (Real.log (n : ℝ) : ℝ) ^ 3 / (n : ℝ) ^ θ < ε := by
    linarith
  simpa [div_eq_mul_inv] using h_final

lemma norm_bound_to_div_lt (θ : ℝ) (_hθ : 0 < θ) (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → ‖Real.log (n : ℝ) ^ 3‖ ≤ (ε / 2) * ‖(n : ℝ) ^ θ‖) :
    ∃ N' : ℕ, ∀ n : ℕ, N' ≤ n →
      Real.log (n : ℝ) ^ 3 / (n : ℝ) ^ θ < ε := by
  exact ⟨max N 1, fun n hn => norm_bound_implies_div_lt θ ε hε n
    (le_of_max_le_right hn) (hN n (le_of_max_le_left hn))⟩

lemma log_pow_three_div_rpow_eventually_lt (θ : ℝ) (hθ : 0 < θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.log (n : ℝ) ^ 3 / (n : ℝ) ^ θ < ε := by
  obtain ⟨N, hN⟩ := norm_log_pow_le_mul_norm_rpow θ hθ (ε / 2) (by linarith)
  exact norm_bound_to_div_lt θ hθ ε hε N hN

lemma log_pow_over_rpow_eventually_lt (θ : ℝ) (hθ_pos : 0 < θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ < ε := by
  obtain ⟨N₁, hN₁⟩ := log_pow_three_div_rpow_eventually_lt θ hθ_pos (ε / 8) (by linarith)
  refine ⟨max N₁ 3, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := by omega
  have hn₃ : 3 ≤ n := by omega
  have h_n_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have h_rpow_pos : (0 : ℝ) < (n : ℝ) ^ θ := Real.rpow_pos_of_pos h_n_pos θ
  calc (1 + Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ θ
      ≤ 8 * Real.log (n : ℝ) ^ 3 / (n : ℝ) ^ θ := by
        apply div_le_div_of_nonneg_right (one_plus_log_pow_le n hn₃) (le_of_lt h_rpow_pos)
    _ = 8 * (Real.log (n : ℝ) ^ 3 / (n : ℝ) ^ θ) := by ring
    _ < 8 * (ε / 8) := by
        apply mul_lt_mul_of_pos_left (hN₁ n hn₁) (by norm_num : (0 : ℝ) < 8)
    _ = ε := by ring

lemma exceptional_set_with_counting_bound (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ →
      ∃ (E : Set (ℤ × ℤ)),
        E ⊆ truncatedObtuseRegion n η ∧
        E.Finite ∧
        (E.ncard : ℝ) ≤ (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ θ + 1 / Real.log n) ∧
        ∀ pq ∈ truncatedObtuseRegion n η,
          Int.gcd pq.2 (largestPrimeFactor n : ℤ) = 1 →
          pq ∉ E →
          (η ^ 2 / 2 : ℝ) * (Nat.totient n : ℝ) ≤
            (countingFunctionS n pq.1 pq.2 : ℝ) := by
  have hε : (0 : ℝ) < η ^ 2 / 100 := by positivity
  obtain ⟨N, hN⟩ := log_pow_over_rpow_eventually_lt θ hθ_pos (η ^ 2 / 100) hε
  refine ⟨max N 2, fun n hn hP => ?_⟩
  have hn_ge_N : N ≤ n := le_of_max_le_left hn
  have hn_ge_2 : 2 ≤ n := le_of_max_le_right hn
  have h_small := hN n hn_ge_N
  exact exceptional_set_construction_single_n η θ hη_pos hη_lt hθ_pos hθ_lt n hn_ge_2 hP h_small

lemma pred_sq_ge (p : ℕ) (hp : 3 ≤ p) : p ≤ (p - 1) ^ 2 := by
  have h₁ : p ≤ (p - 1) ^ 2 := by
    cases p with
    | zero =>
      exfalso
      linarith
    | succ p' =>
      cases p' with
      | zero =>
        exfalso
        linarith
      | succ p'' =>
        cases p'' with
        | zero =>
          exfalso
          linarith
        | succ p''' =>
          simp_all [Nat.pow_succ, Nat.add_assoc]
          ring_nf at *
          nlinarith
  exact h₁

lemma odd_prime_pow_le_totient_sq (p k : ℕ) (hp : Nat.Prime p) (hodd : p ≠ 2) (hk : 1 ≤ k) :
    p ^ k ≤ (p ^ k).totient ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  rw [Nat.totient_prime_pow_succ hp, mul_pow]
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  calc p ^ (m + 1)
      = p ^ m * p := pow_succ p m
    _ ≤ p ^ m * (p - 1) ^ 2 := Nat.mul_le_mul_left _ (pred_sq_ge p hp3)
    _ ≤ (p ^ m) ^ 2 * (p - 1) ^ 2 := by
        apply Nat.mul_le_mul_right
        exact Nat.le_self_pow (by omega) _

lemma ordCompl_lt_of_dvd (n p : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hdvd : p ∣ n) :
    n / p ^ n.factorization p < n := by
  apply Nat.div_lt_self hn
  have hpos : 0 < n.factorization p := hp.factorization_pos_of_dvd (by omega) hdvd
  exact one_lt_pow' hp.one_lt (by omega)

lemma not_two_dvd_of_dvd_odd (n d : ℕ) (hodd : ¬ 2 ∣ n) (hdvd : d ∣ n) : ¬ 2 ∣ d := by
  intro h
  have h₁ : 2 ∣ d := h
  have h₂ : 2 ∣ n := dvd_trans h₁ hdvd
  contradiction

lemma totient_sq_mul_of_coprime (a b : ℕ) (hcop : a.Coprime b)
    (ha : a ≤ a.totient ^ 2) (hb : b ≤ b.totient ^ 2) :
    a * b ≤ (a * b).totient ^ 2 := by
  have h₁ : (a * b).totient = a.totient * b.totient := Nat.totient_mul hcop
  have h₃ : (a.totient * b.totient) ^ 2 = a.totient ^ 2 * b.totient ^ 2 := by nlinarith
  have h₄ : a * b ≤ a.totient ^ 2 * b.totient ^ 2 := by nlinarith
  have h₅ : a * b ≤ (a * b).totient ^ 2 := by simp_all
  exact h₅

lemma odd_le_totient_sq (n : ℕ) (hn : 1 ≤ n) (hodd : ¬ 2 ∣ n) : n ≤ n.totient ^ 2 := by
  induction n using Nat.strongRec' with
  | _ n ih =>
  obtain rfl | hn2 := eq_or_lt_of_le hn
  · simp [Nat.totient_one]
  · set p := n.minFac with hp_def
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpdvd : p ∣ n := Nat.minFac_dvd n
    have hpodd : p ≠ 2 := fun heq => hodd (heq ▸ hpdvd)
    set v := n.factorization p
    set m := n / p ^ v
    have hm_lt : m < n := ordCompl_lt_of_dvd n p (by omega) hp hpdvd
    have hm_pos : 0 < m := Nat.ordCompl_pos p (by omega)
    have hm_odd : ¬ 2 ∣ m := not_two_dvd_of_dvd_odd n m hodd (Nat.ordCompl_dvd n p)
    have hn_eq : p ^ v * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hv_pos : 1 ≤ v := hp.factorization_pos_of_dvd (by omega) hpdvd
    have hcop : (p ^ v).Coprime m :=
      (Nat.coprime_pow_left_iff hv_pos p m).mpr (Nat.coprime_ordCompl hp (by omega))
    have hpv : p ^ v ≤ (p ^ v).totient ^ 2 :=
      odd_prime_pow_le_totient_sq p v hp hpodd hv_pos
    have hm_ih : m ≤ m.totient ^ 2 := ih m hm_lt hm_pos hm_odd
    calc n = p ^ v * m := hn_eq.symm
      _ ≤ (p ^ v * m).totient ^ 2 := totient_sq_mul_of_coprime _ _ hcop hpv hm_ih
      _ = n.totient ^ 2 := by rw [hn_eq]

lemma pow_two_le_two_mul_totient_sq (k : ℕ) (hk : 1 ≤ k) :
    2 ^ k ≤ 2 * (2 ^ k).totient ^ 2 := by
  have h₁ : (2 ^ k).totient = 2 ^ (k - 1) := by
    have h₂ : (2 ^ k).totient = 2 ^ (k - 1) := by
      rw [Nat.totient_prime_pow (by decide : Nat.Prime 2)]
      <;> cases k with
      | zero => contradiction
      | succ k =>
        simp [mul_comm]
    exact h₂
  rw [h₁]
  have h₂ : 2 ^ k ≤ 2 * (2 ^ (k - 1)) ^ 2 := by
    have h₃ : k ≥ 1 := hk
    have h₄ : 2 ^ k ≤ 2 * (2 ^ (k - 1)) ^ 2 := by
      have h₅ : ∀ n : ℕ, n ≥ 1 → 2 ^ n ≤ 2 * (2 ^ (n - 1)) ^ 2 := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => norm_num
        | succ n hn IH =>
          cases n with
          | zero =>
            norm_num at hn
          | succ n =>
            simp_all [Nat.pow_succ, Nat.mul_assoc]
            nlinarith [pow_pos (by norm_num : (0 : ℕ) < 2) n]
      exact h₅ k h₃
    exact h₄
  exact h₂

lemma totient_sq_lower_bound (n : ℕ) (hn : 1 ≤ n) : n ≤ 2 * n.totient ^ 2 := by
  set v := n.factorization 2 with hv_def
  set m := n / 2 ^ v with hm_def
  have hn_eq : 2 ^ v * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hn0 : n ≠ 0 := by omega
  have hm_odd : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two hn0
  have hm_pos : 1 ≤ m := by
    by_contra h
    push Not at h
    interval_cases m
    simp at hn_eq; omega
  rcases v.eq_zero_or_pos with hv0 | hv_pos
  · rw [hv0] at hn_eq
    simp only [pow_zero, one_mul] at hn_eq
    rw [← hn_eq]
    have := odd_le_totient_sq m hm_pos hm_odd
    linarith [Nat.totient_pos.mpr (by omega : 0 < m)]
  · have h2v := pow_two_le_two_mul_totient_sq v hv_pos
    have hm_bound := odd_le_totient_sq m hm_pos hm_odd
    have hsuper := Nat.totient_super_multiplicative (2 ^ v) m
    rw [hn_eq] at hsuper
    have : n = 2 ^ v * m := hn_eq.symm
    calc n = 2 ^ v * m := this
      _ ≤ (2 * (2 ^ v).totient ^ 2) * m.totient ^ 2 := by
          apply Nat.mul_le_mul h2v hm_bound
      _ = 2 * ((2 ^ v).totient * m.totient) ^ 2 := by ring
      _ ≤ 2 * n.totient ^ 2 := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_left hsuper 2

lemma totient_tendsto_atTop :
    ∀ K : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ≤ Nat.totient n := by
  intro K
  use 2 * K ^ 2 + 1
  intro n hn
  by_contra h
  push Not at h
  have hn1 : 1 ≤ n := by omega
  have hbound := totient_sq_lower_bound n hn1
  have hlt : n.totient ≤ K - 1 := by omega
  have hsq : n.totient ^ 2 ≤ (K - 1) ^ 2 := Nat.pow_le_pow_left hlt 2
  have : (K - 1) ^ 2 < K ^ 2 := by
    rcases K with _ | K
    · omega
    · simp; nlinarith [Nat.pos_of_ne_zero (by omega : K.succ ≠ 0)]
  nlinarith

lemma totient_large_enough (η : ℝ) (hη_pos : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      5 ≤ (η ^ 2 / 2 : ℝ) * (Nat.totient n : ℝ) := by
  obtain ⟨N, hN⟩ := totient_tendsto_atTop ⌈10 / η ^ 2⌉₊
  exact ⟨N, fun n hn => by
    have h1 : (⌈10 / η ^ 2⌉₊ : ℝ) ≤ (Nat.totient n : ℝ) := by
      exact_mod_cast hN n hn
    have h2 : 10 / η ^ 2 ≤ (⌈10 / η ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have hη2 : (0 : ℝ) < η ^ 2 := by positivity
    calc (5 : ℝ) = η ^ 2 / 2 * (10 / η ^ 2) := by field_simp; ring
      _ ≤ η ^ 2 / 2 * (Nat.totient n : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith⟩

lemma countingFunctionS_ge_five_outside_exceptional (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ →
      ∃ (exceptionalPairs : Set (ℤ × ℤ)),
        exceptionalPairs.Finite ∧
        (exceptionalPairs.ncard : ℝ) ≤ (n : ℝ) ^ 2 *
          (1 / (n : ℝ) ^ θ + 1 / Real.log n) ∧
        ∀ pq ∈ truncatedObtuseRegion n η,
          Int.gcd pq.2 (largestPrimeFactor n : ℤ) = 1 →
          pq ∉ exceptionalPairs →
          5 ≤ countingFunctionS n pq.1 pq.2 := by
  obtain ⟨N₁, hN₁⟩ := exceptional_set_with_counting_bound η θ hη_pos hη_lt hθ_pos hθ_lt
  obtain ⟨N₂, hN₂⟩ := totient_large_enough η hη_pos
  refine ⟨max N₁ N₂, fun n hn hP => ?_⟩
  have hn1 : N₁ ≤ n := le_of_max_le_left hn
  have hn2 : N₂ ≤ n := le_of_max_le_right hn
  obtain ⟨E, hEsub, hEfin, hEcard, hEprop⟩ := hN₁ n hn1 hP
  refine ⟨E, hEfin, hEcard, fun pq hpq hgcd hnotE => ?_⟩
  have h_lower := hEprop pq hpq hgcd hnotE
  have h_totient := hN₂ n hn2
  have h5 : (5 : ℝ) ≤ (countingFunctionS n pq.1 pq.2 : ℝ) := le_trans h_totient h_lower
  exact_mod_cast h5


lemma badPairsSet_ncard_upper_bound (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1) :
    ∃ (C : ℝ) (N₂ : ℕ), 0 < C ∧ ∀ n : ℕ, N₂ ≤ n →
      (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ →
      ((badPairsSet n η).ncard : ℝ) ≤ C * (n : ℝ) ^ 2 *
        (1 / (n : ℝ) ^ θ + 1 / Real.log n) := by
  obtain ⟨N₀, hN₀⟩ := countingFunctionS_ge_five_outside_exceptional η θ hη_pos hη_lt hθ_pos hθ_lt
  refine ⟨1, N₀, one_pos, fun n hn hP => ?_⟩
  obtain ⟨E, hE_fin, hE_card, hE_good⟩ := hN₀ n hn hP
  have hbad_sub : badPairsSet n η ⊆ E := by
    intro pq hpq
    by_contra hpqE
    have hpq_mem := hpq.1
    have hpq_gcd := hpq.2.1
    have hpq_lt := hpq.2.2
    have hge := hE_good pq hpq_mem hpq_gcd hpqE
    omega
  calc ((badPairsSet n η).ncard : ℝ)
      ≤ (E.ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hbad_sub hE_fin
    _ ≤ (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ θ + 1 / Real.log n) := hE_card
    _ = 1 * (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ θ + 1 / Real.log n) := by ring
lemma inv_rpow_tendsto_zero (θ : ℝ) (hθ_pos : 0 < θ) :
    Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ θ) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop := by
    simpa using tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun x : ℝ => x ^ θ) Filter.atTop Filter.atTop := by
    apply tendsto_rpow_atTop
    linarith
  have h3 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ θ) Filter.atTop Filter.atTop := by
    have h4 : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop := h1
    have h5 : Filter.Tendsto (fun x : ℝ => x ^ θ) Filter.atTop Filter.atTop := h2
    have h6 : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop := h4
    have h7 : Filter.Tendsto (fun x : ℝ => x ^ θ) Filter.atTop Filter.atTop := h5
    have h8 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ θ) Filter.atTop Filter.atTop := h7.comp h6
    exact h8
  have h4 : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ θ) Filter.atTop (nhds 0) := by
    have h5 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ θ) Filter.atTop Filter.atTop := h3
    have h6 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ θ) Filter.atTop (nhds 0) := by
      have h7 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ θ) Filter.atTop Filter.atTop := h5
      have h8 : Filter.Tendsto (fun x : ℝ => (1 : ℝ) / x) (Filter.atTop : Filter ℝ) (nhds 0) := by
        have h9 : Filter.Tendsto (fun x : ℝ => (1 : ℝ) / x) (Filter.atTop : Filter ℝ) (nhds 0) := by
          simpa using tendsto_inv_atTop_zero
        exact h9
      have h9 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ θ) Filter.atTop Filter.atTop := h7
      have h10 : Filter.Tendsto (fun x : ℝ => (1 : ℝ) / x) (Filter.atTop : Filter ℝ) (nhds 0) := h8
      have h11 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ θ) Filter.atTop (nhds 0) :=
        h10.comp (h9)
      exact h11
    exact h6
  exact h4

lemma dist_to_ineq (θ : ℝ) (_hθ_pos : 0 < θ) (ε : ℝ) (_hε : 0 < ε) :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n → dist (1 / (n : ℝ) ^ θ) 0 < ε) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 / (n : ℝ) ^ θ < ε := by
  intro h
  have h_main : ∀ (n : ℕ), 1 / (n : ℝ) ^ θ ≥ 0 := by
    intro n
    by_cases hn : n = 0
    · rw [hn]
      simp only [CharP.cast_eq_zero, one_div, ge_iff_le, inv_nonneg]
      positivity
    · have h₃ : 1 / (n : ℝ) ^ θ ≥ 0 := by positivity
      exact h₃
  have h_dist_eq : ∀ (n : ℕ), dist (1 / (n : ℝ) ^ θ) 0 = 1 / (n : ℝ) ^ θ := by
    intro n
    have h₁ : 1 / (n : ℝ) ^ θ ≥ 0 := h_main n
    have h₂ : dist (1 / (n : ℝ) ^ θ) 0 = |(1 / (n : ℝ) ^ θ : ℝ)| := by
      simp
    rw [h₂]
    have h₃ : |(1 / (n : ℝ) ^ θ : ℝ)| = 1 / (n : ℝ) ^ θ := by
      rw [abs_of_nonneg h₁]
    rw [h₃]
  have h_final : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 / (n : ℝ) ^ θ < ε := by
    obtain ⟨N, hN⟩ := h
    refine ⟨N, fun n hn => ?_⟩
    have h₁ : dist (1 / (n : ℝ) ^ θ) 0 < ε := hN n hn
    have h₂ : dist (1 / (n : ℝ) ^ θ) 0 = 1 / (n : ℝ) ^ θ := h_dist_eq n
    rw [h₂] at h₁
    exact h₁
  exact h_final

lemma inv_rpow_eventually_lt (θ : ℝ) (hθ_pos : 0 < θ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        1 / (n : ℝ) ^ θ < ε := by
  intro ε hε
  have htendsto := inv_rpow_tendsto_zero θ hθ_pos
  rw [Metric.tendsto_atTop] at htendsto
  exact dist_to_ineq θ hθ_pos ε hε (htendsto ε hε)

lemma inv_log_eventually_lt :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        1 / Real.log n < ε := by
  intro ε hε
  have h₁ : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / Real.log n) Filter.atTop (nhds 0) := by
    have h₂ : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop := by
      simpa using tendsto_natCast_atTop_atTop
    have h₃ : Filter.Tendsto (fun x : ℝ => Real.log x) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop
    have h₄ : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop := by
      have h₅ : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop := h₂
      have h₆ : Filter.Tendsto (fun x : ℝ => Real.log x) Filter.atTop Filter.atTop := h₃
      exact h₆.comp h₅
    have h₅ : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / Real.log n) Filter.atTop (nhds 0) := by
      have h₇ : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / Real.log (n : ℝ)) Filter.atTop (nhds 0) := by
        have h₈ : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop := h₄
        have h₉ : Filter.Tendsto (fun x : ℝ => (1 : ℝ) / x) Filter.atTop (nhds 0) := by
          simpa using tendsto_inv_atTop_zero
        have h₁₀ : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / Real.log (n : ℝ)) Filter.atTop (nhds 0) :=
          h₉.comp h₈
        exact h₁₀
      convert h₇ using 1
    exact h₅
  have h₂ : ∀ ε : ℝ, 0 < ε → (∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 / Real.log n < ε) := by
    intro ε hε
    have h₅ : ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (1 : ℝ) / Real.log n < ε := by
      have h₆ : ∀ᶠ (n : ℕ) in Filter.atTop, (1 : ℝ) / Real.log n < ε := by
        have h₉ : ∀ᶠ (n : ℕ) in Filter.atTop, (1 : ℝ) / Real.log n < ε := by
          have h₁₃ : ∀ᶠ (n : ℕ) in Filter.atTop, (1 : ℝ) / Real.log n < ε := by
            have h₁₆ : ∀ᶠ (n : ℕ) in Filter.atTop, (1 : ℝ) / Real.log n ∈ Set.Iio ε := by
              have h₁₉ : Set.Iio ε ∈ nhds (0 : ℝ) := by
                apply Iio_mem_nhds
                linarith
              have h₂₀ : ∀ᶠ (n : ℕ) in Filter.atTop, (1 : ℝ) / Real.log n ∈ Set.Iio ε := by
                have h₂₁ : Filter.Tendsto (fun n : ℕ =>
                  (1 : ℝ) / Real.log n) Filter.atTop (nhds 0) := h₁
                have h₂₂ : Set.Iio ε ∈ nhds (0 : ℝ) := h₁₉
                exact h₂₁ h₂₂
              exact h₂₀
            have h₂₁ : ∀ᶠ (n : ℕ) in Filter.atTop, (1 : ℝ) / Real.log n ∈ Set.Iio ε := h₁₆
            filter_upwards [h₂₁] with n hn
            exact hn
          exact h₁₃
        exact h₉
      have h₇ : ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (1 : ℝ) / Real.log n < ε := by
        have h₈ : ∀ᶠ (n : ℕ) in Filter.atTop, (1 : ℝ) / Real.log n < ε := h₆
        have h₉ : ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (1 : ℝ) / Real.log n < ε := by
          have h₁₀ : ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (1 : ℝ) / Real.log n < ε := by
            simp only [Filter.eventually_atTop] at h₈
            obtain ⟨N, hN⟩ := h₈
            refine ⟨N, ?_⟩
            intro n hn
            exact hN n hn
          exact h₁₀
        exact h₉
      exact h₇
    exact h₅
  exact h₂ ε hε

lemma asymptotic_decay (θ : ℝ) (hθ_pos : 0 < θ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        1 / (n : ℝ) ^ θ + 1 / Real.log n < ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := inv_rpow_eventually_lt θ hθ_pos (ε / 2) hε2
  obtain ⟨N₂, hN₂⟩ := inv_log_eventually_lt (ε / 2) hε2
  exact ⟨max N₁ N₂, fun n hn => by
    have h1 := hN₁ n (le_of_max_le_left hn)
    have h2 := hN₂ n (le_of_max_le_right hn)
    linarith⟩

lemma ratio_bound_core (bad Hn c C n2 decay ε : ℝ)
    (hc_pos : 0 < c) (hC_pos : 0 < C) (hε_pos : 0 < ε)
    (hn2_pos : 0 < n2)
    (_h_bad_nonneg : 0 ≤ bad)
    (h_upper : bad ≤ C * n2 * decay)
    (h_lower : c * n2 ≤ Hn)
    (h_decay : decay < c * ε / C) :
    bad / Hn < ε := by
  have h_C_decay_lt_cε : C * decay < c * ε := by
    exact (lt_div_iff₀' hC_pos).mp h_decay
  have h_Cn2_decay_lt_cεn2 : C * n2 * decay < c * ε * n2 := by nlinarith
  have h_cεn2_le_εHn : c * ε * n2 ≤ ε * Hn := by nlinarith
  have h_bad_lt_εHn : bad < ε * Hn := by nlinarith
  have h_Hn_pos : 0 < Hn := by nlinarith
  exact (div_lt_iff₀ h_Hn_pos).mpr h_bad_lt_εHn

lemma ratio_bound_from_three_lemmas (c C : ℝ) (N₁ N₂ : ℕ) (η θ : ℝ)
    (hc_pos : 0 < c) (hC_pos : 0 < C)
    (h_lower : ∀ n : ℕ, N₁ ≤ n → c * (n : ℝ) ^ 2 ≤ ((truncatedObtuseRegion n η).ncard : ℝ))
    (h_upper : ∀ n : ℕ, N₂ ≤ n → (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ →
      ((badPairsSet n η).ncard : ℝ) ≤ C * (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ θ + 1 / Real.log n))
    (_hη_pos : 0 < η) (_hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ →
        ((badPairsSet n η).ncard : ℝ) / ((truncatedObtuseRegion n η).ncard : ℝ) < ε := by
  intro ε hε_pos
  have hδ_pos : 0 < c * ε / C := by positivity
  obtain ⟨N₃, hN₃⟩ := asymptotic_decay θ hθ_pos (c * ε / C) hδ_pos
  refine ⟨max N₁ (max N₂ (max N₃ 1)), fun n hn hP => ?_⟩
  have hn_N₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn_N₂ : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn_N₃ : N₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right N₁ _) hn)
  have hn_ge_one : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_right N₁ _) hn)
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn2_pos : 0 < (n : ℝ) ^ 2 := pow_pos hn_pos 2
  have h_low := h_lower n hn_N₁
  have h_up := h_upper n hn_N₂ hP
  have h_dec := hN₃ n hn_N₃
  have h_bad_nonneg : (0 : ℝ) ≤ ((badPairsSet n η).ncard : ℝ) := Nat.cast_nonneg _
  exact ratio_bound_core
    ((badPairsSet n η).ncard : ℝ)
    ((truncatedObtuseRegion n η).ncard : ℝ)
    c C ((n : ℝ) ^ 2)
    (1 / (n : ℝ) ^ θ + 1 / Real.log n)
    ε
    hc_pos hC_pos hε_pos hn2_pos h_bad_nonneg
    h_up h_low h_dec


theorem analyticEngine_lower_bound (η : ℝ) (θ : ℝ)
    (hη_pos : 0 < η) (hη_lt : η < 1 / 6) (hθ_pos : 0 < θ) (hθ_lt : θ < 1) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (largestPrimeFactor n : ℝ) ≥ (n : ℝ) ^ θ →
        ((badPairsSet n η).ncard : ℝ) / ((truncatedObtuseRegion n η).ncard : ℝ) < ε := by
  obtain ⟨c, N₁, hc_pos, h_lower⟩ := truncatedObtuseRegion_ncard_lower_bound η hη_pos hη_lt
  obtain ⟨C, N₂, hC_pos, h_upper⟩ := badPairsSet_ncard_upper_bound η θ hη_pos hη_lt hθ_pos hθ_lt
  exact ratio_bound_from_three_lemmas c C N₁ N₂ η θ hc_pos hC_pos h_lower h_upper
    hη_pos hη_lt hθ_pos
