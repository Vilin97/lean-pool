/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Locating a point in a partition

For a strictly increasing grid `t 0 < t 1 < … < t m`, `pieceIdx t m x` is the index of the piece
`[t i, t (i+1))` containing `x ∈ [t 0, t m)`.
-/

public section

namespace Zeta5Irrational

open Classical in
/-- The piece containing `x`. -/
noncomputable def pieceIdx (t : ℕ → ℝ) (m : ℕ) (x : ℝ) : ℕ :=
  Nat.findGreatest (fun i => t i ≤ x) m

lemma grid_mono {t : ℕ → ℝ} {m : ℕ} (h : ∀ i < m, t i < t (i + 1)) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ m) : t i ≤ t j := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    rw [this]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h1 | h1
    · exact (ih (by omega) (by omega)).trans (h j (by omega)).le
    · have : i = j + 1 := by omega
      rw [this]

/-- `x ∈ [t 0, t m)` lies in the piece `pieceIdx t m x`. -/
lemma pieceIdx_spec {t : ℕ → ℝ} {m : ℕ} (_h : ∀ i < m, t i < t (i + 1)) {x : ℝ} (h0 : t 0 ≤ x)
    (hm : x < t m) : pieceIdx t m x < m ∧ t (pieceIdx t m x) ≤ x ∧ x < t (pieceIdx t m x + 1) := by
  classical
  unfold pieceIdx
  set i := Nat.findGreatest (fun i => t i ≤ x) m with hi
  have hspec : t i ≤ x := Nat.findGreatest_spec (P := fun i => t i ≤ x) (Nat.zero_le m) h0
  have hle : i ≤ m := Nat.findGreatest_le m
  have hlt : i < m := by
    rcases Nat.lt_or_ge i m with h1 | h1
    · exact h1
    · have : i = m := by omega
      rw [this] at hspec; linarith
  refine ⟨hlt, hspec, ?_⟩
  by_contra hc
  rw [not_lt] at hc
  have :=
    Nat.findGreatest_is_greatest (P := fun i => t i ≤ x) (n := m) (k := i + 1) (by omega)
      (by omega)
  exact this hc

/-- Inside the piece `i` the index is `i`. -/
lemma pieceIdx_eq {t : ℕ → ℝ} {m : ℕ} (h : ∀ i < m, t i < t (i + 1)) {i : ℕ} (hi : i < m) {x : ℝ}
    (hx : x ∈ Set.Ico (t i) (t (i + 1))) : pieceIdx t m x = i := by
  classical
  unfold pieceIdx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨hi.le, fun _ => hx.1, fun j hj1 hj2 => ?_⟩
  have := grid_mono h (show i + 1 ≤ j by omega) hj2
  exact not_le.mpr (lt_of_lt_of_le hx.2 this)

end Zeta5Irrational
