/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import LeanPool.ThreeGap.SimultaneousApprox
import LeanPool.ThreeGap.ChevallierGapBound
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators

/-!
# The sup-norm growth inequality via the orthant pigeonhole (fully proven)

For best simultaneous Diophantine approximation in the **sup norm** on `ℝ^d`, the denominators at
least double every `2^d` steps:

  `2 q_N ≤ q_{N + 2^d}`.

This is the elementary half of Shutov's `L^∞` growth inequality (the full `q_{N+2^d} ≥ q_{N+1}+q_N`
is Lagarias 1980; the doubling form here already suffices for the gap bound, via
`ChevallierGapBound.gap_count_doubling`). The proof is the **orthant pigeonhole** of the Chevallier
survey (§2.4.1, attributed to Lagarias):

* Among the `2^d + 1` remainder vectors `ε_N, …, ε_{N+2^d}`, two share an orthant (a sign pattern in
  `{≥0, <0}^d`), since there are only `2^d` orthants — `Fintype.exists_ne_map_eq_of_card_lt`.
* Two vectors in the same orthant, each of sup-norm `≤ r_N = δ_{q_N}`, have difference of sup-norm
  `≤ r_N` (coordinatewise, same sign ⟹ `|a−b| ≤ max(|a|,|b|)`).
* That difference is the remainder of `m = q_{N+k₂} − q_{N+k₁}` (`SimApprox.delta_diff_le`), so
  `δ_m ≤ r_N`; the best-approximation/record property then forces `m ≥ q_N`, giving the doubling.

No convex geometry, no kissing number — purely the pigeonhole. Axiom-clean.
-/

namespace ThreeGap.SimApprox

variable {d : ℕ}

/-- Pointwise: two reals of the **same sign** (`0 ≤ a ↔ 0 ≤ b`) with `|a|, |b| ≤ r` satisfy
`|a − b| ≤ r`. (If both `≥ 0` or both `≤ 0`, the difference cannot exceed the larger magnitude.) -/
theorem abs_sub_le_of_same_sign {a b r : ℝ} (hsign : (0 ≤ a) ↔ (0 ≤ b))
    (ha : |a| ≤ r) (hb : |b| ≤ r) : |a - b| ≤ r := by
  rw [abs_le] at ha hb ⊢
  rcases lt_or_ge a 0 with h | h
  · have hb0 : b < 0 := by
      by_contra hb'
      exact absurd (hsign.mpr (not_lt.mp hb')) (not_le.mpr h)
    exact ⟨by linarith, by linarith⟩
  · have hb0 : 0 ≤ b := hsign.mp h
    exact ⟨by linarith [ha.1, ha.2, hb.1, hb.2], by linarith [ha.1, ha.2, hb.1, hb.2]⟩

/-- **Same-orthant sup-norm bound.** If `u, v : Fin d → ℝ` lie in the same orthant
(`0 ≤ u k ↔ 0 ≤ v k` for every `k`) and each has sup-norm `≤ r`, then `‖u − v‖ ≤ r`. -/
theorem norm_sub_le_of_sameOrthant {u v : Fin d → ℝ} {r : ℝ}
    (hsign : ∀ k, (0 ≤ u k) ↔ (0 ≤ v k)) (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ r) :
    ‖u - v‖ ≤ r := by
  have hr : 0 ≤ r := le_trans (norm_nonneg u) hu
  rw [pi_norm_le_iff_of_nonneg hr]
  intro k
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have huk : |u k| ≤ r := by rw [← Real.norm_eq_abs]; exact (pi_norm_le_iff_of_nonneg hr).mp hu k
  have hvk : |v k| ≤ r := by rw [← Real.norm_eq_abs]; exact (pi_norm_le_iff_of_nonneg hr).mp hv k
  exact abs_sub_le_of_same_sign (hsign k) huk hvk

/-- **The sup-norm growth inequality, doubling form (orthant pigeonhole).** Suppose `q` enumerates
best-approximation denominators of `α` in the sup norm, with remainders `p` attaining the defect
(`hattain`), defects non-increasing along the sequence (`hdec`), and each `q k` a record minimum
(`hbsad`: every smaller positive denominator has strictly larger defect). Then

  `2 q_N ≤ q_{N + 2^d}`.

This feeds `ChevallierGapBound.gap_count_doubling` with `K = 2^d` to give `g_∞ ≤ 2^d + 1`. -/
theorem supNorm_growth_doubling (α : Fin d → ℝ) (q : ℕ → ℤ) (p : ℕ → Fin d → ℤ)
    (hmono : StrictMono q)
    (hattain : ∀ k, ‖rem α (q k) (p k)‖ = delta α (q k))
    (hdec : ∀ i j, i ≤ j → delta α (q j) ≤ delta α (q i))
    (hbsad : ∀ (k : ℕ) (m : ℤ), 0 < m → m < q k → delta α (q k) < delta α m)
    (N : ℕ) : 2 * q N ≤ q (N + 2 ^ d) := by
  set ε : ℕ → Fin d → ℝ := fun k => rem α (q (N + k)) (p (N + k)) with hε
  set sgn : ℕ → Fin d → Bool := fun k i => decide (0 ≤ ε k i) with hsgn
  -- the core bound for an ordered same-orthant pair
  have key : ∀ j1 j2 : ℕ, j1 < j2 → j2 ≤ 2 ^ d → sgn j1 = sgn j2 →
      2 * q N ≤ q (N + 2 ^ d) := by
    intro j1 j2 hlt hle hse
    have hqlt : q (N + j1) < q (N + j2) := hmono (by omega)
    have hm : (0 : ℤ) < q (N + j2) - q (N + j1) := by omega
    have hnorm1 : ‖ε j1‖ ≤ delta α (q N) := by
      simp only [hε]; rw [hattain (N + j1)]; exact hdec N (N + j1) (by omega)
    have hnorm2 : ‖ε j2‖ ≤ delta α (q N) := by
      simp only [hε]; rw [hattain (N + j2)]; exact hdec N (N + j2) (by omega)
    have hsign : ∀ i, (0 ≤ ε j1 i) ↔ (0 ≤ ε j2 i) := by
      intro i
      have hi := congrFun hse i
      simp only [hsgn, decide_eq_decide] at hi
      exact hi
    have hsub : ‖ε j2 - ε j1‖ ≤ delta α (q N) :=
      norm_sub_le_of_sameOrthant (fun i => (hsign i).symm) hnorm2 hnorm1
    have hdd : delta α (q (N + j2) - q (N + j1)) ≤ ‖ε j2 - ε j1‖ := by
      simp only [hε]
      exact delta_diff_le α (q (N + j2)) (q (N + j1)) (p (N + j2)) (p (N + j1))
    have hdle : delta α (q (N + j2) - q (N + j1)) ≤ delta α (q N) := le_trans hdd hsub
    have hge : q N ≤ q (N + j2) - q (N + j1) := by
      by_contra hc
      rw [not_le] at hc
      exact absurd hdle (not_le.mpr (hbsad N _ hm hc))
    have hj1 : q N ≤ q (N + j1) := hmono.monotone (by omega)
    have hj2 : q (N + j2) ≤ q (N + 2 ^ d) := hmono.monotone (by omega)
    omega
  -- pigeonhole: two of the 2^d + 1 indices share a sign pattern
  have hcard : Fintype.card (Fin d → Bool) < Fintype.card (Fin (2 ^ d + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    omega
  obtain ⟨a, b, hab, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (2 ^ d + 1) => sgn i.val) hcard
  have hne : a.val ≠ b.val := fun h => hab (Fin.val_injective h)
  have hale : a.val ≤ 2 ^ d := Nat.lt_succ_iff.mp a.isLt
  have hble : b.val ≤ 2 ^ d := Nat.lt_succ_iff.mp b.isLt
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a.val b.val h hble heq
  · exact key b.val a.val h hale heq.symm

/-- **`g_∞ ≤ 2^d + 1` from the orthant pigeonhole + Chevallier's Lemma.** Assembling
`supNorm_growth_doubling` (the fully-proven sup-norm growth, `K = 2^d`) with the doubling gap-count
reduction, the number of distinct nearest-neighbour distances of a sup-norm best-approximation
sequence is at most `2^d + 1`. The *only* remaining hypothesis is Chevallier's Lemma (`hg`: the
`g = n − m` / `n − m + 1` index dictionary) — the growth geometry is now entirely elementary
(orthant pigeonhole), with no kissing number or convex-geometry input. -/
theorem gap_count_supNorm (α : Fin d → ℝ) (q : ℕ → ℤ) (p : ℕ → Fin d → ℤ)
    (hmono : StrictMono q)
    (hattain : ∀ k, ‖rem α (q k) (p k)‖ = delta α (q k))
    (hdec : ∀ i j, i ≤ j → delta α (q j) ≤ delta α (q i))
    (hbsad : ∀ (k : ℕ) (m : ℤ), 0 < m → m < q k → delta α (q k) < delta α m)
    {N : ℤ} {m n g : ℕ} (hnN : q n ≤ N) (hNm : N < 2 * q (m + 1))
    (hg : g = n - m ∨ g = n - m + 1) :
    g ≤ 2 ^ d + 1 :=
  ThreeGap.Chevallier.gap_count_doubling q hmono (2 ^ d)
    (fun k => supNorm_growth_doubling α q p hmono hattain hdec hbsad k) hnN hNm hg

end ThreeGap.SimApprox
