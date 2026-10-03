/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Interfaces

/-! the proof notes, §8.1 (ii): the column values `colVal n p b` through the residues
`r₀ = n % p`, `s₀ = 5n % p`, and the closed forms of `Σ_b c_b` and `Σ_b c_b²`
(the column multiset `β+1` once, `β+3` μ times, `β−1` (s₀−μ) times, `β+4` (r₀−μ) times, `β`
otherwise). -/

public section
namespace Zeta32.Arith.Relaxed
open Zeta32

/-- `#{1 ≤ i ≤ n : i ≡ b mod p} = ⌊n/p⌋ + [1 ≤ b ≤ n mod p]` for `b < p`. -/
theorem card_filter_mod_Icc (p b : ℕ) (hp : 0 < p) (hb : b < p) : ∀ n : ℕ,
    ((Finset.Icc 1 n).filter (fun i => i % p = b)).card =
      n / p + (if 1 ≤ b ∧ b ≤ n % p then 1 else 0)
  | 0 => by simp; omega
  | n+1 => by
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ n + 1), Finset.filter_insert]
    have ih := card_filter_mod_Icc p b hp hb n
    have hq := Nat.mod_add_div n p
    have hr := Nat.mod_lt n hp
    have hnot : n + 1 ∉ (Finset.Icc 1 n).filter (fun i => i % p = b) := by simp
    have key : ((n+1)/p = n/p ∧ (n+1)%p = n%p + 1) ∨
        ((n+1)/p = n/p + 1 ∧ (n+1)%p = 0 ∧ n%p + 1 = p) := by
      rcases Nat.lt_or_ge (n%p + 1) p with h | h
      · left
        exact (Nat.div_mod_unique hp).mpr ⟨by omega, h⟩
      · right
        have h' : n % p + 1 = p := by omega
        have := (Nat.div_mod_unique hp (a := n+1) (d := n/p+1) (c := 0)).mpr
          ⟨by rw [mul_add]; omega, hp⟩
        exact ⟨this.1, this.2, h'⟩
    by_cases hin : (n+1) % p = b
    · rw [ite_eq_left hin, Finset.card_insert_of_notMem hnot, ih]
      rcases key with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · rw [h1, h2]
        have hb1 : 1 ≤ b := by omega
        rw [ite_eq_right (by omega), ite_eq_left ⟨hb1, by omega⟩]
      · rw [h1, h2]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right hin, ih]
      rcases key with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · rw [h1, h2]
        by_cases hc : 1 ≤ b ∧ b ≤ n % p
        · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, by omega⟩]
        · rw [ite_eq_right hc, ite_eq_right (by omega)]
      · rw [h1, h2]
        rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_right (by omega)]

/-- Real indicator `[c < r]`. -/
noncomputable def ind (c r : ℕ) : ℝ := if c < r then 1 else 0

lemma sum_ind {m r : ℕ} (hr : r ≤ m) : (∑ c ∈ Finset.range m, ind c r) = r := by
  unfold ind
  rw [Finset.sum_boole]
  have : (Finset.range m).filter (fun c => c < r) = Finset.range r := by
    ext c; simp; omega
  rw [this, Finset.card_range]

/-- Column value for `1 ≤ b = c + 1 < p`. -/
lemma colVal_succ (n p c A L r₀ s₀ : ℕ) (hp : 0 < p) (hc : c + 1 < p)
    (hA : n / p = A) (hL : (5 * n) / p = L) (hr : n % p = r₀) (hs : (5 * n) % p = s₀) :
    (colVal n p (c+1) : ℝ) = (4 * (A : ℝ) - (L : ℝ) - 2) + 4 * ind c r₀ - ind c s₀ := by
  unfold colVal ind
  rw [card_filter_mod_Icc p (c+1) hp hc n, card_filter_mod_Icc p (c+1) hp hc (5*n), hA, hL, hr, hs]
  by_cases h1 : c < r₀ <;> by_cases h2 : c < s₀
  · rw [ite_eq_left (show 1 ≤ c + 1 ∧ c + 1 ≤ r₀ by omega),
      ite_eq_left (show 1 ≤ c + 1 ∧ c + 1 ≤ s₀ by omega), ite_eq_right (show ¬ c + 1 = 0 by omega),
      ite_eq_left h1, ite_eq_left h2]
    push_cast; ring
  · rw [ite_eq_left (show 1 ≤ c + 1 ∧ c + 1 ≤ r₀ by omega),
      ite_eq_right (show ¬ (1 ≤ c + 1 ∧ c + 1 ≤ s₀) by omega), ite_eq_right (show ¬ c + 1 = 0 by
        omega),
      ite_eq_left h1, ite_eq_right h2]
    push_cast; ring
  · rw [ite_eq_right (show ¬ (1 ≤ c + 1 ∧ c + 1 ≤ r₀) by omega),
      ite_eq_left (show 1 ≤ c + 1 ∧ c + 1 ≤ s₀ by omega), ite_eq_right (show ¬ c + 1 = 0 by omega),
      ite_eq_right h1, ite_eq_left h2]
    push_cast; ring
  · rw [ite_eq_right (show ¬ (1 ≤ c + 1 ∧ c + 1 ≤ r₀) by omega),
      ite_eq_right (show ¬ (1 ≤ c + 1 ∧ c + 1 ≤ s₀) by omega), ite_eq_right (show ¬ c + 1 = 0 by
        omega),
      ite_eq_right h1, ite_eq_right h2]
    push_cast; ring

/-- Column value for `b = 0`. -/
lemma colVal_zero (n p A L : ℕ) (hp : 0 < p) (hA : n / p = A) (hL : (5 * n) / p = L) :
    (colVal n p 0 : ℝ) = (4 * (A : ℝ) - (L : ℝ) - 2) + 1 := by
  unfold colVal
  rw [card_filter_mod_Icc p 0 hp hp n, card_filter_mod_Icc p 0 hp hp (5*n), hA, hL,
    ite_eq_right (show ¬ (1 ≤ 0 ∧ 0 ≤ n % p) by omega),
    ite_eq_right (show ¬ (1 ≤ 0 ∧ 0 ≤ (5*n) % p) by omega), ite_eq_left rfl]
  push_cast; ring

lemma ind_mul_ind (c r s : ℕ) : ind c r * ind c s = ind c (min r s) := by
  unfold ind
  by_cases h1 : c < r <;> by_cases h2 : c < s <;> simp [h1, h2, lt_min_iff]

lemma ind_sq (c r : ℕ) : ind c r ^ 2 = ind c r := by
  unfold ind; split_ifs <;> norm_num

/-- `Σ_b c_b = pβ + 4r₀ − s₀ + 1`, `β = 4A − L − 2`. -/
theorem sum_colVal (n p A L r₀ s₀ : ℕ) (hp : 0 < p)
    (hA : n / p = A) (hL : (5 * n) / p = L) (hr : n % p = r₀) (hs : (5 * n) % p = s₀) :
    (∑ b ∈ Finset.range p, (colVal n p b : ℝ)) =
      (p : ℝ) * (4 * (A : ℝ) - (L : ℝ) - 2) + 4 * (r₀ : ℝ) - (s₀ : ℝ) + 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Finset.sum_range_succ', colVal_zero n (q+1) A L hp hA hL]
  have hr' : r₀ ≤ q := by rw [← hr]; exact Nat.lt_succ_iff.mp (Nat.mod_lt _ hp)
  have hs' : s₀ ≤ q := by rw [← hs]; exact Nat.lt_succ_iff.mp (Nat.mod_lt _ hp)
  rw [Finset.sum_congr rfl (fun c hc => colVal_succ n (q+1) c A L r₀ s₀ hp
    (by simp at hc; omega) hA hL hr hs)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ind hr',
    sum_ind hs', Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- `Σ_b c_b² = pβ² + 2β(4r₀ − s₀ + 1) + 1 + 16r₀ + s₀ − 8μ`, `μ = min(r₀, s₀)`. -/
theorem sum_colVal_sq (n p A L r₀ s₀ : ℕ) (hp : 0 < p)
    (hA : n / p = A) (hL : (5 * n) / p = L) (hr : n % p = r₀) (hs : (5 * n) % p = s₀) :
    (∑ b ∈ Finset.range p, (colVal n p b : ℝ) ^ 2) =
      (p : ℝ) * (4 * (A : ℝ) - (L : ℝ) - 2) ^ 2 +
        2 * (4 * (A : ℝ) - (L : ℝ) - 2) * (4 * (r₀ : ℝ) - (s₀ : ℝ) + 1) +
        1 + 16 * (r₀ : ℝ) + (s₀ : ℝ) - 8 * ((min r₀ s₀ : ℕ) : ℝ) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Finset.sum_range_succ', colVal_zero n (q+1) A L hp hA hL]
  have hr' : r₀ ≤ q := by rw [← hr]; exact Nat.lt_succ_iff.mp (Nat.mod_lt _ hp)
  have hs' : s₀ ≤ q := by rw [← hs]; exact Nat.lt_succ_iff.mp (Nat.mod_lt _ hp)
  have hm : min r₀ s₀ ≤ q := le_trans (min_le_left _ _) hr'
  set β : ℝ := 4 * (A : ℝ) - (L : ℝ) - 2 with hβ
  have hpt : ∀ c ∈ Finset.range q, (colVal n (q+1) (c+1) : ℝ) ^ 2 =
      β ^ 2 + (2 * β * 4) * ind c r₀ - (2 * β) * ind c s₀ +
        16 * ind c r₀ + ind c s₀ - 8 * ind c (min r₀ s₀) := by
    intro c hc
    rw [colVal_succ n (q+1) c A L r₀ s₀ hp (by simp at hc; omega) hA hL hr hs, ← ind_mul_ind]
    have h1 := ind_sq c r₀
    have h2 := ind_sq c s₀
    rw [← hβ]
    linear_combination 16 * h1 + h2
  rw [Finset.sum_congr rfl hpt]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ind hr',
    sum_ind hs', sum_ind hm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

end Zeta32.Arith.Relaxed
end
