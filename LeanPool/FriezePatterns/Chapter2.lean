/-
Copyright (c) 2026 Antoine de Saint-Germain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine de Saint-Germain
-/

import LeanPool.FriezePatterns.Chapter1
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity
---- n-Flutes ----

/-- An `n`-flute: a positive integer sequence `a` with `a 0 = 1`, periodic with period
`n - 1`, and satisfying the divisibility relation `a (k + 1) ∣ a k + a (k + 2)`. -/
structure flute (n : ℕ) where
  /-- The underlying sequence of the flute. -/
  a : ℕ → ℕ
  /-- Every entry of the flute is positive. -/
  pos : ∀ i, a i > 0
  /-- The flute starts at `1`. -/
  hd : a 0 = 1
  /-- The flute is periodic with period `n - 1`. -/
  period : ∀ k, a k = a (k + (n - 1))
  /-- Each interior entry divides the sum of its neighbours. -/
  div : ∀ k, a (k + 1) ∣ (a k + a (k + 2))

/-- The constant flute (the sequence identically equal to `1`).

`Inhabited` is preferred over `Nonempty` so that we can recover the explicit witness. -/
@[reducible] def csteFlute (n : ℕ) : Inhabited (flute n) := by
  let a : ℕ → ℕ := fun _ => 1
  have pos : ∀ i, a i > 0 := fun _ => Nat.one_pos
  have hd : a 0 = 1 := rfl
  have period : ∀ k, a k = a (k + n - 1) := fun _ => rfl
  have div : ∀ k, a (k + 1) ∣ (a k + a (k + 2)) := fun _ => ⟨2, rfl⟩
  exact ⟨a, pos, hd, period, div⟩

/-- The set of all `n`-flutes. -/
def fluteSet (n : ℕ) : Set (flute n) :=
  Set.univ

/-- The underlying sequence of the Fibonacci-maximal `(2k+1)`-flute. -/
def a_odd (k i : ℕ) : ℕ :=
  if k = 0 then
    1
  else if i ≥ 2 * k then
    a_odd k (i - 2 * k) -- this does not terminate when k = 0
    else
    if i < k then
      Nat.fib (2 * i + 2)
    else
      Nat.fib (1 + 4 * k - 2 * i)

/-- The Fibonacci-maximal `(2k+1)`-flute, built from `a_odd`. -/
def fib_flute_odd (k : ℕ) : flute (2*k+1) := by
  by_cases hk : k = 0
  · exact ⟨a_odd k 0, fun _ => by simp [hk, a_odd], by simp [hk, a_odd],
      by simp [hk, a_odd], fun _ => by simp⟩
  have pos : ∀ i, a_odd k i > 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ≥ 2*k
      · unfold a_odd; simp only [hk, ↓reduceIte, ge_iff_le, hi, gt_iff_lt]
        exact ih (i-(2*k)) (by omega)
      · by_cases hi₂ : i < k
        · simp [a_odd, hk, hi, hi₂]
        · simp [a_odd, hk, hi, hi₂]; omega
  have hd : a_odd k 0 = 1 := by simp [hk, a_odd]
  have period : ∀ i, a_odd k i = a_odd k (i+(2*k+1)-1) := by
    intro i
    nth_rw 2 [a_odd]
    simp [hk]
  have div : ∀ i, a_odd k (i+1) ∣ (a_odd k i + a_odd k (i+2)) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ≥ 2*k
      · have hi₂ : 2*k ≤ i+1 := by omega
        have hi₃ : 2*k ≤ i+2 := by omega
        unfold a_odd; simp only [hk, ↓reduceIte, ge_iff_le, hi₂, hi, hi₃]
        specialize ih (i-(2*k)) (by omega)
        have hi₄ : i-2*k+1 = i+1-2*k := by omega
        have hi₅ : i-2*k+2 = i+2-2*k := by omega
        simpa [hi₄, hi₅] using ih
      · by_cases hi₂ : i+2<k
        · have hi₃ : i+1 < k := by omega
          have hi₄ : i < k := by omega
          have hi₅ : ¬ 2*k ≤ i+1 := by omega
          have hi₆ : ¬ 2*k ≤ i+2 := by omega
          unfold a_odd; simp [hk, hi, hi₂, hi₃, hi₄, hi₅, hi₆]
          ring_nf
          have : 6 + i*2 = (2*i+3)+2+1 := by omega
          rw [this, Nat.fib_add (2*i+3) 2]
          ring_nf
          have h :=
            calc Nat.fib (2+i*2) + Nat.fib (3+i*2) = Nat.fib (i*2+2) + Nat.fib ((i*2+2)+1) := by
                  ring_nf
            _ = Nat.fib ((i*2+2)+2) := by rw [←Nat.fib_add_two]
            _ = Nat.fib (4+i*2) := by ring_nf
          rw [h]
          use 3; omega
        · by_cases hi₃ : i+1 < k
          · have hi₄ : ¬ 2*k ≤ i+1 := by omega
            have hi₅ : ¬ 2*k ≤ i+2 := by omega
            have hi₆ : i < k := by omega
            have hi₇ : 2 * (i+1)+2 = 2*k := by omega
            have hi₈ : 2 * i+2 = 2*k-2 := by omega
            have hi₉ : 1+4*k-2*(i+2) = (2*k-1)+2 := by omega
            unfold a_odd; simp only [hk, ↓reduceIte, ge_iff_le, hi₄, hi₃, hi₇, hi, hi₆, hi₈, hi₅,
              hi₂, hi₉]
            simp only [Nat.fib_add_two, ← add_assoc]
            have : Nat.fib (2*k-2) + Nat.fib (2*k-1) = Nat.fib (2*k) := by
              have : 2*k = (2*k-2)+2 := by omega
              nth_rw 3 [this]
              rw [Nat.fib_add_two]
              congr; omega
            rw [this]
            have : 2*k-1+1=2*k := by omega
            rw [this]
            use 2; omega
          · by_cases hi₄ : i < k
            · have hi₅ : ¬ 2*k ≤ i+1 := by omega
              unfold a_odd; simp only [hk, ↓reduceIte, ge_iff_le, hi₅, hi₃, hi, hi₄, hi₂]
              by_cases hk₁ : k = 1
              · have hi₀ : i = 0 := by omega
                simp only [hk₁, mul_one, Nat.reduceAdd, hi₀, zero_add, Nat.reduceSub, mul_zero,
                  Nat.fib_two, Std.le_refl, ↓reduceIte, tsub_self]
                use 1
                unfold a_odd
                decide
              · have hi₆ : ¬ 2*k ≤ i+2 := by omega
                have hi₇ : 1+4*k-2*(i+1) = (2*k-1)+2 := by omega
                have hi₈ : 2*i+2 = (2*k-1)+1 := by omega
                have hi₉ : 1+4*k-2*(i+2) = 2*k-1 := by omega
                simp only [hi₇, hi₈, hi₆, ↓reduceIte, hi₉]
                use 1; simp [Nat.fib_add_two] ; omega
            · by_cases hi₅ : 2*k ≤ i+2
              · by_cases hi₆ : 2*k ≤ i+1
                · have hi₇ : i+1-2*k = 0 := by omega
                  have hi₈ : i+2-2*k = 1 := by omega
                  unfold a_odd; simp only [hk, ↓reduceIte, ge_iff_le, hi₆, hi₇, hi, hi₄, hi₅, hi₈]
                  unfold a_odd; simp [hk]
                · unfold a_odd; simp only [hk, ↓reduceIte, ge_iff_le, hi₆, hi₃, hi, hi₄, hi₅]
                  have hi₇ : 1+4*k-2*(i+1) = 3 := by omega
                  have hi₈ : 1+4*k-2*i = 5 := by omega
                  have hi₉ : i+2-2*k = 0 := by omega
                  have hk₂ : 0<k := by omega
                  unfold a_odd
                  simp only [hi₇, hi₈, hk, ↓reduceIte, hi₉, ge_iff_le, nonpos_iff_eq_zero,
                    mul_eq_zero, OfNat.ofNat_ne_zero, or_self, hk₂, mul_zero, zero_add, Nat.fib_two]
                  use 3; simp [Nat.fib_add_two]
              · have hi₆ : ¬ 2*k ≤ i+1 := by omega
                unfold a_odd; simp only [hk, ↓reduceIte, ge_iff_le, hi₆, hi₃, hi, hi₄, hi₅, hi₂]
                have hi₇ : 1+4*k-2*(i+1) = 4*k-2*i-1 := by omega
                have hi₈ : 1+4*k-2*i = 4*k-2*i-2+2+1 := by omega
                have hi₉ : 1+4*k-2*(i+2) = 4*k-2*i-3 := by omega
                rw [hi₇, hi₈, hi₉, Nat.fib_add]
                simp only [Nat.fib_add_two, Nat.fib_zero, zero_add, Nat.fib_one, mul_one,
                  Nat.reduceAdd]
                use 3
                rw [add_assoc, add_comm, add_assoc]
                have hi₁₀ : 4*k-2*i-2 = (4*k-2*i-3)+1 := by omega
                have hi₁₁ : 4*k-2*i-3+1+1 = 4*k-2*i-1 := by omega
                rw [hi₁₀, ← Nat.fib_add_two, hi₁₁]
                omega
  exact ⟨a_odd k, pos, hd, period, div⟩

/-- The underlying sequence of the Fibonacci-maximal `(2k+2)`-flute. -/
def a_even (k i : ℕ) : ℕ :=
  if i ≥ 2 * k + 1 then
    a_even k (i - 2 * k - 1)
  else if i < k + 1 then
    Nat.fib (2 * i + 2)
    else
    Nat.fib (3 + 4 * k - 2 * i)

/-- The Fibonacci-maximal `(2k+2)`-flute, built from `a_even`. -/
def fib_flute_even (k : ℕ) : flute (2*k+2) := by
  have pos : ∀ i, a_even k i > 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ≥ 2*k+1
      · unfold a_even; simp only [ge_iff_le, hi, ↓reduceIte, gt_iff_lt]
        exact ih (i-(2*k)-1) (by omega)
      · by_cases hi₂ : i < k+1
        · simp [a_even, hi, hi₂]
        · simp [a_even, hi, hi₂]; omega
  have hd : a_even k 0 = 1 := by simp [a_even]
  have period : ∀ i, a_even k i = a_even k (i+(2*k+2)-1) := by
    intro i
    nth_rw 2 [a_even]
    simp only [Nat.add_succ_sub_one, ge_iff_le, le_add_iff_nonneg_left, zero_le, ↓reduceIte]
    have hj : i+(2*k+1)-2*k-1 = i := by omega
    simp [hj]
  have div : ∀ i, a_even k (i+1) ∣ (a_even k i + a_even k (i+2)) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ≥ 2*k+1
      · -- by_cases hi pos
        have hi₂ : i+1 ≥ 2*k+1 := by omega
        have hi₃ : 2*k ≤ i+1 := by omega
        unfold a_even; simp only [ge_iff_le, hi₂, ↓reduceIte, hi, add_le_add_iff_right, hi₃]
        have hi₄ : i+1-2*k-1 = (i-2*k-1)+1 := by omega
        have hi₅ : i+2-2*k-1 = (i-2*k-1)+2 := by omega
        have hi₆ : (i-2*k-1) < i := by omega
        rw [hi₄, hi₅]
        exact ih (i-2*k-1) hi₆
      · by_cases hi₂ : i+2≤k
        · -- by_cases hi neg + by_cases hi₂ pos :
          have hi₃ : i+2 < k+1 := by omega
          have hi₄ : i+1 < k+1 := by omega
          have hi₅ : i < k+1 := by omega
          unfold a_even; simp only [ge_iff_le, add_le_add_iff_right, hi₄, ↓reduceIte, hi, hi₅, hi₃]
          have hi₆ : ¬ 2*k ≤ i := by omega
          have hi₇ : ¬ 2*k ≤ i+1 := by omega
          simp [hi₆,hi₇]
          ring_nf
          have : 6+i*2 = (2*i+3)+2+1 := by omega
          rw [this, Nat.fib_add (2*i+3) 2]
          ring_nf
          have h :=
            calc Nat.fib (2+i*2) + Nat.fib (3+i*2) = Nat.fib (i*2+2) + Nat.fib ((i*2+2)+1) := by
                  ring_nf
            _ = Nat.fib ((i*2+2)+2) := Nat.fib_add_two.symm
            _ = Nat.fib (4+i*2) := by ring_nf
          rw [h]
          use 3; omega
        · by_cases hi₃ : i+1 ≤ k
          · -- by_cases hi neg + by_cases hi₂ neg + by_cases hi₃ pos :
            have hi₄ : ¬ i+1 ≥ 2*k+1 := by omega
            have hi₅ : ¬ i+2 ≥ 2*k+1 := by omega
            have hi₆ : i < k := by omega
            have hi₇ : i < k+1 := by omega
            have hi₈ : ¬ i+2 < k+1 := by omega
            have hi₉ : i+1 = k := by omega
            unfold a_even; simp [hi, hi₄, hi₅,hi₆,hi₇,hi₈]
            ring_nf
            have hi₁₀ : 3 + (i + 1) * 4 - (4 + i * 2) = (2 + i*2)+1 := by omega
            rw [← hi₉, hi₁₀]
            use 1
            rw [← Nat.fib_add_two]
            ring_nf
          · by_cases hi₄ : i ≤ k
            · -- by_cases hi neg + by_cases hi₂ neg + by_cases hi₃ neg + by_cases hi₄ pos :
              have hi₅ : i = k := by omega
              have hi₆ : ¬ 2 * k + 1 ≤ k := by omega
              unfold a_even; simp only [hi₅, ge_iff_le, add_le_add_iff_right, lt_self_iff_false,
                ↓reduceIte, hi₆, lt_add_iff_pos_right, zero_lt_one, add_lt_add_iff_left,
                Nat.not_ofNat_lt_one]
              by_cases hk₀ : k = 0
              · -- by_cases hi/hi₂/hi₃ neg + hi₄/hk₀ pos
                simp [hk₀]
                have : a_even k 0 = 1 := by exact hd
                rw [hk₀] at this
                simp [this]
              · have hi₇ : ¬ 2 * k ≤ k := by omega
                simp only [hi₇, ↓reduceIte]
                by_cases hk₁ : k = 1
                · -- by_cases hi/hi₂/hi₃ neg + hi₄/hk₁ pos + hk₀ neg
                  simp only [hk₁, mul_one, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
                    Std.le_refl, ↓reduceIte, tsub_self]
                  have f₁ : a_even k 0 = 1 := by exact hd
                  have f₃ : Nat.fib 3 = 2 := by simp [Nat.fib]
                  have f₄ : Nat.fib 4 = 3 := by simp [Nat.fib]
                  rw [hk₁] at f₁
                  rw [f₁, f₃, f₄]
                  use 2
                · -- by_cases hi/hi₂/hi₃ neg + hi₄ pos + hk₀/hk₁ neg
                  have hk₂ : 1 < k := by omega
                  have h₈ : ¬ 2 * k ≤ k + 1 := by omega
                  have h₉ : 3 + 4 * k - 2 * (k + 1) = 2*k + 1 := by omega
                  have h₁₀ : 3 + 4 * k - 2 * (k + 2) = 2*k-1 := by omega
                  simp only [h₉, h₈, ↓reduceIte, h₁₀]
                  rw [Nat.fib_add_two, add_comm (Nat.fib (2 * k)), add_assoc, Nat.fib_add_one]
                  · use 2; omega
                  · omega
            · -- by_cases hi neg + by_cases hi₂ neg + by_cases hi₃ neg + by_cases hi₄ neg
              have h₅ : ¬ i+1 < k+1 := by omega
              have h₇ : ¬ i < k+1 := by omega
              have h₈ : ¬ i+2 < k+1 := by omega
              unfold a_even; simp only [ge_iff_le, add_le_add_iff_right, h₅, ↓reduceIte, hi, h₇, h₈]
              by_cases hi₅ :2*k ≤ i
              · -- hi/hi₂/hi₃/hi₄ neg + hi₅ pos
                have h₉ : i = 2*k := by omega
                rw [h₉]
                simp only [Std.le_refl, ↓reduceIte, add_tsub_cancel_left, tsub_self,
                  le_add_iff_nonneg_right, zero_le, Nat.add_one_sub_one]
                rw [hd]
                use (Nat.fib (3 + 4 * k - 2 * (2 * k)) + a_even k 1); omega
              · -- by_cases hi/hi₂/hi₃/hi₄/hi₅ neg
                simp only [hi₅, ↓reduceIte]
                by_cases hi₆ : 2*k ≤ i+1
                · -- by_cases hi/hi₂/hi₃/hi₄/hi₅ neg + by_cases hi₆ pos
                  have h₁ : i+1 = 2*k := by omega
                  rw [h₁]; simp only [Std.le_refl, ↓reduceIte]
                  have h₂ : 3 + 4 * k - 2 * (2 * k) = 3 := by omega
                  have h₃ : 3 + 4 * k - 2 * i = 5 := by omega
                  have h₄ : i + 2 - 2 * k - 1 = 0 := by omega
                  have f₃ : Nat.fib 3 = 2 := by simp [Nat.fib]
                  have f₅ : Nat.fib 5 = 5 := by simp [Nat.fib]
                  rw [h₂,h₃,h₄,hd,f₃,f₅]
                  use 3;
                · -- by_cases hi/hi₂/hi₃/hi₄/hi₅ neg + by_cases hi₆ neg
                  simp only [hi₆, ↓reduceIte]
                  have h₁: 3 + 4 * k - 2 * (i + 1) = 4*k -2*i +1 := by omega
                  have h₂ : 3 + 4 * k - 2 * i = 4*k -2*i + 1 + 2 :=by omega
                  have h₃ : 4 * k - 2 * i + 1 + 1 = 4 * k - 2 * i + 2 := by omega
                  have h₄ : 3 + 4 * k - 2 * (i + 2) = 4 * k - 2 * i - 1 := by omega
                  rw [h₁, h₂, Nat.fib_add_two, h₃, Nat.fib_add_two, h₄, add_assoc,
                    add_comm (Nat.fib (4 * k - 2 * i)), add_assoc,
                    add_comm (Nat.fib (4 * k - 2 * i))]
                  rw [← Nat.fib_add_one]
                  · have h : Nat.fib (4 * k - 2 * i + 1) + (Nat.fib (4 * k - 2 * i + 1) +
                        Nat.fib (4 * k - 2 * i + 1)) = Nat.fib (4 * k - 2 * i + 1)*3 := by omega
                    rw [h]
                    use 3
                  · have h₃ : ¬ 4*k = 2*i := by omega
                    omega
  exact ⟨a_even k, pos, hd, period, div⟩

/-- Reduction of an `(n+3)`-flute (assuming `f.a 1 = 1`) to an `(n+2)`-flute (underlying
sequence). -/
def a_1 (n : ℕ) (f : flute (n + 3)) (k : ℕ) : ℕ :=
  if k ≥ n + 1 then
    a_1 n f (k - (n + 1))
  else if k = 0 then
    f.a 0
  else
    f.a (k + 1)

/-- Reduction of an `(n+3)`-flute with `f.a 1 = 1` to an `(n+2)`-flute. -/
def aux_1 (n : ℕ) (f : flute (n + 3)) (h : f.a 1 = 1) : flute (n + 2) := by
  have pos : ∀ i, a_1 n f i > 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ≥ n+1
      · unfold a_1; simp only [ge_iff_le, hi, ↓reduceIte, gt_iff_lt]
        exact ih (i-(n+1)) (by omega)
      · by_cases hi₂ : i = 0
        · simp only [hi₂, a_1, ge_iff_le, nonpos_iff_eq_zero, Nat.add_eq_zero_iff, one_ne_zero,
          and_false, ↓reduceIte, gt_iff_lt]
          exact f.pos 0
        · simp only [a_1, ge_iff_le, hi, ↓reduceIte, hi₂, gt_iff_lt]
          exact f.pos (i+1)
  have hd : a_1 n f 0 = 1 := by simp [a_1, f.hd]
  have period : ∀ i, a_1 n f i = a_1 n f (i+(n+2)-1) := by
    intro i
    nth_rw 2 [a_1]
    simp
  have div : ∀ i, a_1 n f (i+1) ∣ (a_1 n f i + a_1 n f (i+2)) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ≥ n+1
      · have hi₂ : n ≤ i := by omega
        have hi₃ : n ≤ i+1 := by omega
        unfold a_1; simp only [ge_iff_le, add_le_add_iff_right, hi₂, ↓reduceIte, Nat.reduceSubDiff,
          hi, hi₃]
        specialize ih (i-(n+1)) (by omega)
        have hi₄ : i-(n+1)+1 = i-n := by omega
        have hi₅ : i-(n+1)+2 = i+1-n := by omega
        rw [hi₄, hi₅] at ih; exact ih
      · by_cases hi₂ : i = 0
        · unfold a_1; simp only [hi₂, zero_add, ge_iff_le, add_le_iff_nonpos_left,
          nonpos_iff_eq_zero, le_add_iff_nonneg_left, zero_le, Nat.sub_eq_zero_of_le, one_ne_zero,
          ↓reduceIte, Nat.reduceAdd, Nat.add_eq_zero_iff, and_false, Nat.reduceLeDiff,
          Nat.reduceSubDiff, OfNat.ofNat_ne_zero]
          match n with
          | 0 => simp [hd]
          | 1 =>
            simp only [one_ne_zero, ↓reduceIte, Nat.reduceAdd, Std.le_refl, tsub_self]
            rw [hd, f.hd]
            nth_rw 1 [←h]
            have : f.a 3 = 1 := by
              have := f.period 0
              simp only [Nat.reduceAdd, f.hd, Nat.add_one_sub_one, zero_add] at this
              rw [←this]
            nth_rw 3 [←this]
            simp [f.div 1]
          | n+2 =>
            simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte, f.hd,
              Nat.reduceLeDiff]
            rw [←h]
            exact f.div 1
        · by_cases hi₃ : i+1 ≥ n+1
          · have hi₄ : i=n := by omega
            unfold a_1; simp [hi₄, hd]
          · by_cases hi₄ : i+2 ≥ n+1
            · have hi₅ : i+1 = n := by omega
              unfold a_1; simp only [hi₅, ge_iff_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
                one_ne_zero, ↓reduceIte, hi, hi₂, hi₄, Nat.reduceLeDiff, Std.le_refl,
                Nat.sub_eq_zero_of_le]
              match n with
              | 0 => simp [f.hd]
              | 1 =>
                simp only [one_ne_zero, ↓reduceIte, Nat.reduceAdd]
                rw [hd]
                have : f.a 3 = 1 := by
                  have := f.period 0
                  simp only [Nat.reduceAdd, f.hd, Nat.add_one_sub_one, zero_add] at this
                  rw [←this]
                nth_rw 2 [←this]
                simp [f.div 1]
              | n+2 =>
                simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte, hd]
                have h : f.a (n+2+2) = 1 := by
                  have := f.period 0
                  simp only [f.hd, Nat.add_one_sub_one, zero_add] at this
                  rw [←this]
                nth_rw 2 [←h]
                exact f.div (n+2)
            · unfold a_1; simp only [ge_iff_le, hi₃, ↓reduceIte, Nat.add_eq_zero_iff, hi₂,
              one_ne_zero, and_self, hi, hi₄, OfNat.ofNat_ne_zero]
              exact f.div (i+1)
  exact ⟨a_1 n f, pos, hd, period, div⟩

/-- Reduction of an `(n+3)`-flute (assuming `f.a (n + 1) = 1`) to an `(n+2)`-flute
(underlying sequence). -/
def a_2 (n : ℕ) (f : flute (n + 3)) (k : ℕ) : ℕ :=
  if k ≥ n + 1 then
    a_2 n f (k - (n + 1))
  else
    f.a k

/-- Reduction of an `(n+3)`-flute with `f.a (n + 1) = 1` to an `(n+2)`-flute. -/
def aux_2 (n : ℕ) (f : flute (n + 3)) (h : f.a (n + 1) = 1) : flute (n + 2) := by
  have pos : ∀ i, a_2 n f i > 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ≥ n+1
      · unfold a_2; simp only [ge_iff_le, hi, ↓reduceIte, gt_iff_lt]
        exact ih (i-(n+1)) (by omega)
      · simpa [a_2, hi] using f.pos i
  have hd : a_2 n f 0 = 1 := by simp [a_2, f.hd]
  have period : ∀ i, a_2 n f i = a_2 n f (i+(n+2)-1) := by
    intro i
    nth_rw 2 [a_2]
    simp
  have div : ∀ i, a_2 n f (i+1) ∣ (a_2 n f i + a_2 n f (i+2)) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ≥ n+1
      · have hi₂ : n ≤ i := by omega
        have hi₃ : n ≤ i+1 := by omega
        unfold a_2; simp only [ge_iff_le, add_le_add_iff_right, hi₂, ↓reduceIte, Nat.reduceSubDiff,
          hi, hi₃]
        specialize ih (i-(n+1)) (by omega)
        have hi₄ : i-(n+1)+1 = i-n := by omega
        have hi₅ : i-(n+1)+2 = i+1-n := by omega
        rw [hi₄, hi₅] at ih; exact ih
      · by_cases hi₂ : i = 0
        · unfold a_2; simp only [hi₂, zero_add, ge_iff_le, add_le_iff_nonpos_left,
          nonpos_iff_eq_zero, le_add_iff_nonneg_left, zero_le, Nat.sub_eq_zero_of_le,
          Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.reduceLeDiff,
          Nat.reduceSubDiff]
          match n with
          | 0 => simp [hd]
          | 1 =>
            simp only [one_ne_zero, ↓reduceIte, Nat.reduceAdd, Std.le_refl, tsub_self]
            simp only [Nat.reduceAdd] at h
            rw [hd, f.hd]
            nth_rw 2 [←h]
            nth_rw 2 [←f.hd]
            simp [f.div 0, add_comm]
          | n+2 =>
            simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte, f.hd,
              Nat.reduceLeDiff]
            nth_rw 2 [←f.hd]
            exact f.div 0
        · unfold a_2; simp only [ge_iff_le, add_le_add_iff_right, Nat.reduceSubDiff, hi, ↓reduceIte]
          by_cases hi₃ : n ≤ i
          · have hi₄ : i = n := by omega
            simp [hi₄, hd]
          · by_cases hi₄ : n ≤ i+1
            · have hi₅ : i+1 = n := by omega
              simp only [hi₃, ↓reduceIte, hi₅, Std.le_refl, tsub_self, hd]
              have key := f.div i
              rw [hi₅, ←one_add_one_eq_two, ←add_assoc, hi₅, h] at key
              exact key
            · simp [hi₃, hi₄, f.div i]
  exact ⟨a_2 n f, pos, hd, period, div⟩

/-- Reduction of an `(n+3)`-flute admitting a reducible index `i` to an `(n+2)`-flute
(underlying sequence). -/
def a_3 (n : ℕ) (f : flute (n + 3)) (i : ℕ)
    (hi : i ≤ n ∧ f.a (i + 1) = f.a i + f.a (i + 2)) (k : ℕ) : ℕ :=
  if k ≥ n + 1 then
    a_3 n f i hi (k - (n + 1))
  else if k ≤ i then
    f.a k
  else f.a (k + 1)

/-- Reduction of an `(n+3)`-flute admitting a reducible index `j` to an `(n+2)`-flute. -/
def aux_3 (n : ℕ) (f : flute (n + 3)) (j : ℕ)
    (hj : j ≤ n ∧ f.a (j + 1) = f.a j + f.a (j + 2)) : flute (n + 2) := by
  have pos : ∀ i, a_3 n f j hj i > 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ≥ n+1
      · unfold a_3; simp only [ge_iff_le, hi, ↓reduceIte, gt_iff_lt]
        exact ih (i-(n+1)) (by omega)
      · by_cases hi₂ : i ≤ j
        · unfold a_3; simp only [ge_iff_le, hi, ↓reduceIte, hi₂, gt_iff_lt]
          exact f.pos i
        · unfold a_3; simp only [ge_iff_le, hi, ↓reduceIte, hi₂, gt_iff_lt]
          exact f.pos (i+1)
  have hd : a_3 n f j hj 0 = 1 := by simp [a_3, f.hd]
  have period : ∀ i, a_3 n f j hj i = a_3 n f j hj (i+(n+2)-1) := by
    intro i
    nth_rw 2 [a_3]
    simp
  have div : ∀ i, a_3 n f j hj (i+1) ∣ (a_3 n f j hj i + a_3 n f j hj (i+2)) := by
    have f.tl : f.a (n+2) = 1 := by
      have := f.period 0
      simpa [f.hd] using this.symm
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ≥ n+1
      · have hi₂ : n ≤ i := by omega
        have hi₃ : n ≤ i+1 := by omega
        unfold a_3; simp only [ge_iff_le, add_le_add_iff_right, hi₂, ↓reduceIte, Nat.reduceSubDiff,
          hi, hi₃]
        specialize ih (i-(n+1)) (by omega)
        have hi₄ : i-(n+1)+1 = i-n := by omega
        have hi₅ : i-(n+1)+2 = i+1-n := by omega
        rw [hi₄, hi₅] at ih; exact ih
      · by_cases hi₂ : n ≤ i
        · have hi₂ : i = n := by omega
          simp [hi₂, a_3, f.hd]
        · by_cases hi₃ : n ≤ i+1
          · have hi₃ : i = n-1 := by omega
            have hn : ¬ n ≤ n-1 := by omega
            have hn₂ : n-1+1 = n := by omega
            have hn₃ : ¬ n+1 ≤ n-1 := by omega
            unfold a_3; simp only [hi₃, hn₂, ge_iff_le, add_le_iff_nonpos_right,
              nonpos_iff_eq_zero, one_ne_zero, ↓reduceIte, hn₃, tsub_le_iff_right,
              add_le_add_iff_right, Std.le_refl, Nat.reduceLeDiff, Nat.sub_eq_zero_of_le]
            simp only [hd]
            by_cases hn₄ : n ≤ j
            · have hn₅ : j = n := by omega
              simp only [hn₅, Std.le_refl, ↓reduceIte, le_add_iff_nonneg_right, zero_le]
              have key := f.div (n-1)
              have hn₆ : n-1+2 = n+1 := by omega
              simp only [hn₂, hn₆] at key
              simp only [hn₅ ▸ hj.2] at key
              rw [f.tl] at key
              rcases key with ⟨k, hk⟩
              use k-1
              calc
                f.a (n-1) +1 = f.a (n-1) + (f.a n +1) - f.a n := by omega
                _ = f.a n * k - f.a n := by rw [hk]
                _ = f.a n * (k-1) := by exact (Nat.mul_sub_one (f.a n) k).symm
            · simp only [hn₄, ↓reduceIte]
              by_cases hn₅ : n ≤ j+1
              · have hn₆ : j = n-1 := by omega
                have hn₇ : n ≤ n-1+1 := by omega
                simp only [hn₆, hn₇, ↓reduceIte]
                have key := hn₆ ▸ hj.2
                have hn₈ : n-1+2 = n+1 := by omega
                simp only [hn₂, hn₈] at key
                have key₂ := f.div n
                simp only [f.tl] at key₂
                rcases key₂ with ⟨k, hk⟩
                use k-1
                calc
                  f.a (n-1) + 1 = f.a (n+1)*k - f.a (n+1) := by omega
                  _ = f.a (n+1) * (k-1) := by exact (Nat.mul_sub_one (f.a (n+1)) k).symm
              · simp [hn₅]
                simpa [f.tl] using f.div n
          · unfold a_3; simp only [ge_iff_le, add_le_add_iff_right, hi₂, ↓reduceIte, add_assoc,
            Nat.reduceAdd, hi, hi₃]
            by_cases hij : i+2 ≤ j
            · have hij₂ : i+1 ≤ j := by omega
              have hij₃ : i ≤ j := by omega
              simp [hij, hij₂, hij₃, f.div i]
            · by_cases hij₂ : i+1 ≤ j
              · have hij₃ : i ≤ j := by omega
                have hij₄ : i+1 = j := by omega
                simp only [← hij₄, Std.le_refl, ↓reduceIte, le_add_iff_nonneg_right, zero_le,
                  add_le_add_iff_left, Nat.not_ofNat_le_one]
                have key := hij₄ ▸ hj.2
                simp only [add_assoc, Nat.reduceAdd] at key
                rcases f.div i with ⟨k, hk⟩
                use k-1
                calc
                  f.a i + f.a (i+3) = f.a (i+1) * k - f.a (i+1) := by omega
                  _ = f.a (i+1) * (k-1) := by exact (Nat.mul_sub_one (f.a (i+1)) k).symm
              · by_cases hij₃ : i ≤ j
                · have hij₄ : i = j := by omega
                  simp only [hij₄, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero,
                    ↓reduceIte, Std.le_refl, OfNat.ofNat_ne_zero]
                  rcases f.div (j+1) with ⟨k, hk⟩
                  simp only [add_assoc, Nat.reduceAdd] at hk
                  use k-1
                  calc
                    f.a j + f.a (j+3) = f.a (j+2) * k - f.a (j+2) := by omega
                    _ = f.a (j+2) * (k-1) := by exact (Nat.mul_sub_one (f.a (j+2)) k).symm
                · simp [hij, hij₂, hij₃, f.div (i+1)]
  exact ⟨a_3 n f j hj, pos, hd, period, div⟩

/-- The set of `n`-flutes is nonempty. -/
lemma fluteSetNonEmpty (n : ℕ) : Nonempty (fluteSet n) := by
  rcases csteFlute n with ⟨f⟩
  exact ⟨f, trivial⟩

/-- Every `n`-flute either has `f.a 1 = 1`, has `f.a (n-2) = 1`, or admits a *reducible*
index `i` where `f.a (i+1) = f.a i + f.a (i+2)`. -/
lemma FluteReduction (n : ℕ) (f : flute n) : ((f.a 1 = 1) ∨ (f.a (n - 2) = 1)) ∨
    (∃ i ≤ n - 3, f.a (i + 1) = f.a i + f.a (i + 2)) := by
  by_contra! H
  rcases H with ⟨⟨h₁, h₂⟩, h₃⟩
  have ha₁ : (↑(f.a 1):ℤ) - f.a 0 > 0 := by
    have := f.pos 1
    have := f.hd
    omega
  have ha₂ : (↑(f.a (n-1)):ℤ) - f.a (n-2) < 0 := by
    have := f.pos (n-2)
    have := f.period 0
    simp [f.hd] at this
    omega
  have key : ∀ i ≤ n-3, (↑(f.a i):ℤ) + f.a (i+2) ≥ (f.a (i+1))*2 := by
    intro i hi
    rcases f.div i with ⟨k, hk⟩
    match k with
    | 0 =>
      simp at hk
      have := f.pos i
      omega
    | 1 =>
      specialize h₃ i hi
      omega
    | k+2 =>
      nlinarith
  have key₂ : ∀ i ≤ n-3, (↑ (f.a (i+2)) : ℤ) - f.a (i+1) ≥ f.a 1 - f.a 0 := by
    intro i hi
    induction i with
    | zero =>
      specialize key 0 hi
      linarith
    | succ i ih =>
      specialize key (i+1) hi
      specialize ih (by omega)
      linarith
  have key₃ : f.a (n-1) = 1 := by
    have := f.period 0
    simp only [f.hd, zero_add] at this
    rw [←this]
  match n with -- n ≤ 2 contradicts with h₁ and h₂
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith
  | n+3 =>
    simp only [add_tsub_cancel_right, ne_eq, Nat.reduceSubDiff, Int.sub_pos, Nat.cast_lt,
      Nat.add_one_sub_one, sub_neg, ge_iff_le, tsub_le_iff_right] at *
    specialize key₂ n (by omega)
    linarith

theorem FluteBounded (n : ℕ) (hn : n > 0) (f : flute n) :
    ∀ i ≤ n - 1, f.a i ≤ Nat.fib n := by
  -- note the statement is false without hn
  -- strengthen the inductive hypothesis to avoid having to do everything twice
  suffices : ∃ l, ∀ i ≤ n-1,
      ((i ≠ l → f.a i ≤ Nat.fib (n-2+1)) ∧ (i=l → f.a i ≤ Nat.fib n))
  · rcases this with ⟨l, hl⟩
    intro i hi
    match n with
    | 0 => linarith
    | 1 =>
      simp at *
      simp [hi, f.hd]
    | n+2 =>
      simp only [Nat.add_one_sub_one, ne_eq, add_tsub_cancel_right] at hl
      specialize hl i (by omega)
      by_cases hil : i=l
      · exact hl.2 hil
      · have := hl.1 hil
        have : Nat.fib (n+1) ≤ Nat.fib (n+2) := Nat.fib_mono (by omega)
        omega
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => linarith
  | 1 =>
    use 0
    intro i hi
    simp only [Nat.lt_one_iff, gt_iff_lt, ne_eq, forall_eq, lt_self_iff_false, zero_tsub,
      nonpos_iff_eq_zero, zero_add, Nat.fib_one, Nat.fib_zero, IsEmpty.forall_iff, zero_lt_one,
      tsub_self, Nat.one_le_ofNat, Nat.sub_eq_zero_of_le] at *
    exact ⟨(by omega), (by simp [hi, f.hd])⟩
  | 2 =>
    use 2
    intro i hi
    simp only [gt_iff_lt, ne_eq, Nat.ofNat_pos, Nat.add_one_sub_one, tsub_self, zero_add,
      Nat.fib_one, Nat.fib_two] at *
    apply And.intro _ (by omega)
    have h₀ := f.hd
    have h₁ : f.a 1 = 1 := by
      have := f.period 0
      simp only [f.hd, Nat.add_one_sub_one, zero_add] at this
      rw [←this]
    match i with
    | 0 => simp [h₀]
    | 1 => simp [h₁]
    | i+2 => linarith
  | n+3 =>
    have h₁ := ih (n+2) (by linarith) (by linarith)
    simp only [gt_iff_lt, ne_eq, lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true,
      Nat.add_one_sub_one, add_tsub_cancel_right, Nat.reduceSubDiff] at *
    have hh : 0 < Nat.fib (n+2) := Nat.fib_pos.mpr (by omega)
    have hh₂ : Nat.fib (n+1) ≤ Nat.fib (n+2) := Nat.fib_mono (by omega)
    have hh₃ : Nat.fib (n+3) = Nat.fib (n+1) + Nat.fib (n+2) := Nat.fib_add_two
    rcases FluteReduction _ f with (h₂ | h₂) | h₂
    · -- case 1: f.a 1 = 1
      let g := aux_1 n f h₂
      use n+3; intros i hi
      apply And.intro _ (by omega)
      intro
      match i with
      | 0 =>
        simp [f.hd, add_assoc]
        omega
      | 1 =>
        simp [h₂, add_assoc]
        omega
      | i+2 =>
        specialize h₁ g
        rcases h₁ with ⟨l, h₁⟩
        specialize h₁ (i+1) (by omega)
        change (¬i + 1 = l → (aux_1 n f h₂).a (i + 1) ≤ Nat.fib (n + 1)) ∧
          (i + 1 = l → (aux_1 n f h₂).a (i + 1) ≤ Nat.fib (n + 2)) at h₁
        unfold aux_1 at h₁; dsimp only at h₁; unfold a_1 at h₁; simp only [ge_iff_le,
          add_le_add_iff_right, Nat.reduceSubDiff, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          ↓reduceIte] at h₁
        simp only [add_assoc, Nat.reduceAdd, ge_iff_le]
        by_cases hi₂ : n ≤ i
        · have : i = n := by omega
          rw [this]
          have : f.a (n+2) = 1 := by
            have := f.period 0
            simp only [f.hd, Nat.add_one_sub_one, zero_add] at this
            rw [←this]
          simp [this]
          omega
        · simp only [hi₂, ↓reduceIte, add_assoc, Nat.reduceAdd] at h₁
          by_cases hil : i+1 = l
          · exact h₁.2 hil
          · have := h₁.1 hil
            omega
    · -- case 2 : f.a (n+1) = 1
      let g := aux_2 n f h₂
      simp only [Nat.reduceSubDiff] at h₂
      use n+3; intros i hi; apply And.intro _ (by omega)
      intro
      by_cases hi₂ : i = n+1
      · simp [hi₂, h₂, add_assoc]; omega
      · by_cases hi₃ : i = n+2
        · have := f.period 0
          simp at this; simp [add_assoc, hi₃, ←this, f.hd]; omega
        · rcases h₁ g with ⟨l, h₁⟩
          specialize h₁ i (by omega)
          have hi₄ : ¬ n+1 ≤ i := by omega
          change (¬i = l → (aux_2 n f h₂).a i ≤ Nat.fib (n + 1)) ∧
            (i = l → (aux_2 n f h₂).a i ≤ Nat.fib (n + 2)) at h₁
          unfold aux_2 at h₁; dsimp only at h₁; unfold a_2 at h₁; simp only [ge_iff_le, hi₄,
            ↓reduceIte] at h₁
          by_cases hil : i = l
          · exact h₁.2 hil
          · have := h₁.1 hil
            simp [add_assoc]; omega
    · -- case 3 : ∃ i ≤ n, f.a (i+1) = f.a i + f.a (i+2)
      rcases h₂ with ⟨j, hj⟩
      simp only [add_tsub_cancel_right] at hj; simp only [add_assoc, Nat.reduceAdd]
      let g := aux_3 n f j hj
      have hg : g = aux_3 n f j hj := rfl
      have key₁ : ∀ i ≤ n+2, i ≠ j+1 → f.a i ≤ Nat.fib (n+2) := by
        intro i hi hij
        by_cases hij : i≤j
        · rcases h₁ g with ⟨l, h₁⟩
          specialize h₁ i (by omega)
          have hi₂ : ¬ n+1 ≤ i := by omega
          rw [hg] at h₁; unfold aux_3 at h₁; dsimp only at h₁; unfold a_3 at h₁
          simp [hij, hi₂] at h₁
          omega
        · have hij : ¬ i≤j+1 := by omega
          rcases h₁ g with ⟨l, h₁⟩
          specialize h₁ (i-1) (by omega)
          rw [hg] at h₁; unfold aux_3 at h₁; dsimp only at h₁; unfold a_3 at h₁
          simp [hij] at h₁
          by_cases hi₃ : n+1 ≤ i-1
          · have hi₄ : i = n+2 := by omega
            rw [hi₄]
            have := f.period 0
            simp [f.hd] at this
            have : Nat.fib (n+2) > 0 := Nat.fib_pos.mpr (by omega)
            omega
          · have hi₄ : ¬ i-1<j := by omega
            have hi₅ : ¬ n < i - 1 := by omega
            simp [hi₃, @Nat.sub_add_cancel i 1 (by omega)] at h₁
            omega
      use j+1; intro i hi
      by_cases hij : i = j+1
      · rw [hij, hj.2]
        specialize ih (n+1) (by omega) (by omega)
        apply And.intro (by omega)
        intro
        rcases h₁ g with ⟨l, h₁⟩
        by_cases hjl : l = j+1
        · have hf₁ := (h₁ j (by omega)).1 (by omega)
          rw [hg] at hf₁; unfold aux_3 at hf₁; dsimp only at hf₁; unfold a_3 at hf₁
          simp only [ge_iff_le, Std.le_refl, ↓reduceIte] at hf₁
          have : ¬ (n+1) ≤ j := by omega
          have hnj : ¬ n < j := by omega
          simp only [this, ↓reduceIte] at hf₁
          have hf₂ := (h₁ (j+1) (by omega)).2 (by omega)
          rw [hg] at hf₂; unfold aux_3 at hf₂; dsimp only at hf₂; unfold a_3 at hf₂
          simp [] at hf₂
          by_cases hj : n ≤ j
          · simp [hj] at hf₂
            have hj : j = n := by omega
            rw [hj]; rw [hj] at hf₁
            have := f.period 0
            simp [f.hd] at this; omega
          · simp [hj, add_assoc] at hf₂; omega
        · have hf₁ := (h₁ (j+1) (by omega)).1 (by omega)
          have hf₂ := key₁ j (by omega) (by omega)
          rw [hg] at hf₁; unfold aux_3 at hf₁; dsimp only at hf₁; unfold a_3 at hf₁
          simp [hj] at hf₁
          by_cases hj : n ≤ j
          · have hj : j = n := by omega
            rw [hj]; rw [hj] at hf₂
            have := f.period 0
            simp [f.hd] at this
            have : Nat.fib (n+1) > 0 := Nat.fib_pos.mpr (by omega)
            omega
          · simp [hj, add_assoc] at hf₁; omega
      · have := key₁ i hi hij
        exact ⟨(by omega), (by omega)⟩
