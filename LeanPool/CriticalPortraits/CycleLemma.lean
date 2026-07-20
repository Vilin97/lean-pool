/-
Copyright (c) 2026 Keston Aquino-Michaels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keston Aquino-Michaels
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The cycle lemma (Raney / Dvoretzky–Motzkin), sum = 1 case — PROVED

Sorry-free, kernel-axiom-clean (`propext, Classical.choice, Quot.sound`).

Raney's lemma: any integers summing to `1` have **exactly one** cyclic shift with all partial
sums positive. We formalize it on a period-`n` sequence `a : ℕ → ℤ` with period-sum `1`, via the
partial sums `Q k = ∑_{j<k} a j` (so `Q (k+n) = Q k + 1`). A shift `i` is *good* iff
`Q i < Q t` for all `t ∈ (i, i+n)`; the unique good `i ∈ [0,n)` is the **last** argmin of `Q`
over `[0,n)`. The count `#level-canonical = C(N,d-1)/d` will follow (`a_k = 1 - (level counts)`).
-/

namespace CriticalPortraits.Cycle

variable {n : ℕ}

/-- Partial sums of `a`. -/
def Q (a : ℕ → ℤ) (k : ℕ) : ℤ := ∑ j ∈ Finset.range k, a j

lemma Q_zero (a : ℕ → ℤ) : Q a 0 = 0 := by simp [Q]

lemma Q_succ (a : ℕ → ℤ) (k : ℕ) : Q a (k + 1) = Q a k + a k := by
  simp [Q, Finset.sum_range_succ]

/-- A window of length `n` of a period-`n` sequence sums to the period sum. -/
lemma window_sum (a : ℕ → ℤ) (hper : ∀ k, a (k + n) = a k)
    (k : ℕ) : Q a (k + n) - Q a k = Q a n - Q a 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : Q a (k + 1 + n) = Q a (k + n) + a (k + n) := by
      have : k + 1 + n = (k + n) + 1 := by ring
      rw [this, Q_succ]
    rw [e1, Q_succ a k, hper k]
    linarith [ih]

/-- Periodicity of the partial sums: `Q (k+n) = Q k + (period sum)`. -/
lemma Q_periodic (a : ℕ → ℤ) (hper : ∀ k, a (k + n) = a k) (hsum : Q a n = 1)
    (k : ℕ) : Q a (k + n) = Q a k + 1 := by
  have := window_sum a hper k
  rw [Q_zero] at this
  linarith [this, hsum]

/-- Shift `i` is *good*: every partial sum of the shifted sequence is positive, i.e.
    `Q i` is a strict minimum of `Q` over the half-open window `(i, i+n)`. -/
def Good (n : ℕ) (a : ℕ → ℤ) (i : ℕ) : Prop := ∀ t, i < t → t < i + n → Q a i < Q a t

/-- **The cycle lemma (Raney), sum = 1.** For a period-`n` integer sequence with period-sum `1`,
    exactly one shift `i ∈ [0,n)` is good. The witness is the *last* argmin of `Q` over `[0,n)`. -/
theorem cycle_lemma (a : ℕ → ℤ) (hn : 0 < n) (hper : ∀ k, a (k + n) = a k)
    (hsum : Q a n = 1) : ∃! i, i < n ∧ Good n a i := by
  classical
  have hne : (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr hn.ne'
  obtain ⟨i0, hi0r, hi0min⟩ := Finset.exists_min_image (Finset.range n) (Q a) hne
  -- the last argmin (max index among minimizers)
  set S := (Finset.range n).filter (fun i => Q a i = Q a i0) with hSdef
  have hSne : S.Nonempty := ⟨i0, Finset.mem_filter.mpr ⟨hi0r, rfl⟩⟩
  set istar := S.max' hSne with hist
  have histS : istar ∈ S := Finset.max'_mem _ _
  have histrange : istar < n := Finset.mem_range.mp (Finset.filter_subset _ _ histS)
  have histeq : Q a istar = Q a i0 := (Finset.mem_filter.mp histS).2
  have hMle : ∀ t, t < n → Q a istar ≤ Q a t := by
    intro t ht; rw [histeq]; exact hi0min t (Finset.mem_range.mpr ht)
  -- existence: istar is good
  have hGoodStar : Good n a istar := by
    intro t hlt hlt2
    rcases lt_or_ge t n with htn | htn
    · have hle : Q a istar ≤ Q a t := hMle t htn
      rcases eq_or_lt_of_le hle with heq | hlt3
      · exfalso
        have hQt : Q a t = Q a i0 := by rw [← heq]; exact histeq
        have htS : t ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htn, hQt⟩
        have : t ≤ istar := Finset.le_max' _ _ htS
        omega
      · exact hlt3
    · have hsub : t - n + n = t := Nat.sub_add_cancel htn
      have hper' := Q_periodic a hper hsum (t - n)
      rw [hsub] at hper'
      have hle : Q a istar ≤ Q a (t - n) := hMle (t - n) (by omega)
      rw [hper']; omega
  -- uniqueness
  refine ⟨istar, ⟨histrange, hGoodStar⟩, ?_⟩
  rintro y ⟨hyn, hyGood⟩
  rcases lt_trichotomy y istar with h | h | h
  · have h1 : Q a y < Q a istar := hyGood istar (by omega) (by omega)
    have h2 : Q a istar < Q a (y + n) := hGoodStar (y + n) (by omega) (by omega)
    rw [Q_periodic a hper hsum y] at h2; omega
  · exact h
  · have h1 : Q a istar < Q a y := hGoodStar y (by omega) (by omega)
    have h2 : Q a y < Q a (istar + n) := hyGood (istar + n) (by omega) (by omega)
    rw [Q_periodic a hper hsum istar] at h2; omega

end CriticalPortraits.Cycle
