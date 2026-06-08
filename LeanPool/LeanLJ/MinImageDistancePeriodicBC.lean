/-
Copyright (c) 2026 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import LeanPool.LeanLJ.Function

/-!
# Minimum-image distance under periodic boundary conditions

This file establishes basic properties of the real-valued minimum-image distance used in
molecular simulation: non-negativity, vanishing on the diagonal, an upper bound by the box
diagonal, and invariance under periodic translations. It reuses the periodic-boundary wrap
`pbcReal` and minimum-image distances from `LeanPool.LeanLJ.Function`.
-/

namespace LeanLJ

theorem minImageDistance_real_self (pos box_length : Fin 3 → ℝ) :
    minImageDistanceReal pos pos box_length = 0 := by
  unfold minImageDistanceReal squaredminImageDistanceReal
  have h0 : pbcReal (pos (0 : Fin 3) - pos (0 : Fin 3)) (box_length (0 : Fin 3)) = 0 := by
    simp [pbcReal, sub_self, zero_div, round_zero, mul_zero]
  have h1 : pbcReal (pos (1 : Fin 3) - pos (1 : Fin 3)) (box_length (1 : Fin 3)) = 0 := by
    simp [pbcReal, sub_self, zero_div, round_zero, mul_zero]
  have h2 : pbcReal (pos (2 : Fin 3) - pos (2 : Fin 3)) (box_length (2 : Fin 3)) = 0 := by
    simp [pbcReal, sub_self, zero_div, round_zero, mul_zero]
  rw [h0, h1, h2]
  simp

theorem minImageDistance_real_nonneg (posA posB box_length : Fin 3 → ℝ) :
    0 ≤ minImageDistanceReal posA posB box_length := by
  unfold minImageDistanceReal
  apply Real.sqrt_nonneg

/-- Alternate way of defining the minimum image distance function. -/
noncomputable def minImageDist (box_length posA posB : Fin n → ℝ) : ℝ :=
  let dist := fun i => pbcReal (posB i - posA i) (box_length i)
  (Finset.univ.sum (fun i => (dist i) ^ 2)).sqrt


/-! ## Basic math theorems on the `round` function. -/

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_sub_one_le_x (x : α) : round x - 1 ≤ x := by
  rw [round_eq x]
  have h1 : ↑⌊x + 1 / 2⌋ ≤ x + 1 / 2 := Int.floor_le (x + 1 / 2)
  have h2 : ↑⌊x + 1 / 2⌋ - 1 ≤ (x + 1 / 2) - 1 := by linarith
  have h3 : (x + 1 / 2) - 1 = x - 1 / 2 := by ring
  rw [h3] at h2
  have h4 : x - 1 / 2 ≤ x := by linarith
  exact le_trans h2 h4

theorem abs_diff_round_le_half (x : α) : |x - round x| ≤ 1 / 2 := by
  rw [round_eq]
  have h1 : x - 1 / 2 < ↑⌊x + 1 / 2⌋ := by
    have h1a : x + 1 / 2 < ↑⌊x + 1 / 2⌋ + 1 := by apply Int.lt_floor_add_one
    linarith
  have h2 : ↑⌊x + 1 / 2⌋ ≤ x + 1 / 2 := Int.floor_le (x + 1 / 2)
  have h3 : -(1 / 2) ≤ x - ↑⌊x + 1 / 2⌋ ∧ x - ↑⌊x + 1 / 2⌋ ≤ 1 / 2 := by
    constructor
    · linarith
    · linarith
  exact abs_le.mpr h3

theorem abs_pbc_le (x L : ℝ) (hL : 0 < L) : |pbcReal x L| ≤ L / 2 := by
  dsimp only [pbcReal]
  have : |(x / L) - round (x / L)| ≤ 1 / 2 := abs_diff_round_le_half (x / L)
  calc
    |x - L * round (x / L)| = |L * ((x / L) - round (x / L))| := by field_simp
    _ = |L| * |(x / L) - round (x / L)| := by rw [abs_mul]
    _ = L * |(x / L) - round (x / L)| := by rw [abs_of_pos hL]
    _ ≤ L * (1 / 2) := mul_le_mul_of_nonneg_left this (by linarith)
    _ = L / 2 := by ring


/-- The periodic boundary conditions guarantee periodic behavior. -/
theorem pbc_periodic (x L : ℝ) (k : ℤ) (hL : L ≠ 0) :
    pbcReal (x - k * L) L = pbcReal x L := by
  dsimp only [pbcReal]
  have : round ((x - k * L) / L) = round (x / L - k) := by
    congr
    field_simp [mul_comm]
  rw [this, round_sub_intCast, Int.cast_sub, mul_sub]
  ring


/-- The minimum-image distance is bounded above by the diagonal of the simulation cell. -/
theorem minImageDistance_bounded
    (box_length posA posB : Fin n → ℝ) (hbox : ∀ i, 0 < box_length i) :
    minImageDist box_length posA posB
    ≤ (Finset.univ.sum fun i => (box_length i / 2) ^ 2).sqrt := by
  dsimp only [minImageDist]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have bound : |pbcReal (posB i - posA i) (box_length i)| ≤ box_length i / 2 :=
    abs_pbc_le (posB i - posA i) (box_length i) (hbox i)
  calc
    (pbcReal (posB i - posA i) (box_length i)) ^ 2
        = |pbcReal (posB i - posA i) (box_length i)| ^ 2 := by rw [sq_abs]
    _ ≤ (box_length i / 2) ^ 2 := by
      apply pow_le_pow_left₀ (abs_nonneg _) bound


/-- The minimum image distance is invariant under periodic translations. -/
theorem minImageDistance_real_periodic
    (box_length posA posB : Fin n → ℝ) (k : Fin n → ℤ)
    (hbox : ∀ i, box_length i ≠ 0) :
    minImageDist box_length posA posB =
    minImageDist box_length (fun i => posA i + (k i : ℝ) * box_length i) posB := by
  dsimp [minImageDist]
  have h_dist : ∀ i,
      pbcReal (posB i - (posA i + (k i : ℝ) * box_length i)) (box_length i)
        = pbcReal (posB i - posA i) (box_length i) := by
    intro i
    rw [sub_add_eq_sub_sub]
    exact pbc_periodic (posB i - posA i) (box_length i) (k i) (hbox i)
  simp_rw [h_dist]


/-- The minimum image distance between any two points is non-negative. -/
theorem minImageDist_nonneg (box_length posA posB : Fin n → ℝ) :
    0 ≤ minImageDist box_length posA posB := by
  unfold minImageDist
  apply Real.sqrt_nonneg


/-- The minimum image distance between two identical points is zero. -/
theorem minImageDist_self (box_length pos : Fin n → ℝ) :
    minImageDist box_length pos pos = 0 := by
  unfold minImageDist
  have h_dist : ∀ i, pbcReal (pos i - pos i) (box_length i) = 0 := by
    intro i
    simp [pbcReal]
  simp_rw [h_dist]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, Real.sqrt_zero]

lemma apply_pbc_sub (a b L : ℝ) :
    pbcReal (a - b) L = (a - b) - L * round ((a - b) / L) := by rfl


lemma apply_pbc_nested (a b L : ℝ) (hL : L ≠ 0) :
    pbcReal (pbcReal a L - pbcReal b L) L = (a - b) - L * round ((a - b) / L) := by
  calc
    pbcReal (pbcReal a L - pbcReal b L) L
        = pbcReal ((a - L * round (a / L)) - (b - L * round (b / L))) L := by rfl
    _ = pbcReal ((a - b) - L * (round (a / L) - round (b / L))) L := by ring_nf
    _ = (a - b) - L * (round (a / L) - round (b / L))
        - L * round (((a - b) - L * (round (a / L) - round (b / L))) / L) := by rw [pbcReal]
    _ = (a - b) - L * (round (a / L) - round (b / L))
        - L * round ((a - b) / L - (round (a / L) - round (b / L))) := by
      have h_div : ((a - b) - L * (round (a / L) - round (b / L))) / L =
                    (a - b) / L - (round (a / L) - round (b / L)) := by field_simp [hL]
      rw [h_div]
    _ = (a - b) - L * round ((a - b) / L) := by
        rw [← Int.cast_sub, round_sub_intCast, sub_sub, ← mul_add, ← Int.cast_add,
          add_sub_cancel]


/-- Applying PBC to each position individually gives the same squared distance.

This theorem asserts that the squared minimum image distance between two positions `posA`
and `posB` in a periodic box can be computed equivalently either directly, or by first
applying periodic boundary conditions (PBC) to both positions; the order of applying PBC
does not affect the final result. -/
theorem squaredminImageDistance_theorem (posA posB box_length : Fin 3 → ℝ)
    (hL : ∀ i, box_length i ≠ 0) :
    squaredminImageDistanceReal posA posB box_length =
    squaredminImageDistanceReal
      (fun i => pbcReal (posA i) (box_length i))
      (fun i => pbcReal (posB i) (box_length i))
      box_length := by
  unfold squaredminImageDistanceReal
  have h0 : pbcReal (pbcReal (posB (0 : Fin 3)) (box_length (0 : Fin 3)) -
              pbcReal (posA (0 : Fin 3)) (box_length (0 : Fin 3))) (box_length (0 : Fin 3)) =
            pbcReal (posB (0 : Fin 3) - posA (0 : Fin 3)) (box_length (0 : Fin 3)) :=
    apply_pbc_nested _ _ _ (hL (0 : Fin 3))
  have h1 : pbcReal (pbcReal (posB (1 : Fin 3)) (box_length (1 : Fin 3)) -
              pbcReal (posA (1 : Fin 3)) (box_length (1 : Fin 3))) (box_length (1 : Fin 3)) =
            pbcReal (posB (1 : Fin 3) - posA (1 : Fin 3)) (box_length (1 : Fin 3)) :=
    apply_pbc_nested _ _ _ (hL (1 : Fin 3))
  have h2 : pbcReal (pbcReal (posB (2 : Fin 3)) (box_length (2 : Fin 3)) -
              pbcReal (posA (2 : Fin 3)) (box_length (2 : Fin 3))) (box_length (2 : Fin 3)) =
            pbcReal (posB (2 : Fin 3) - posA (2 : Fin 3)) (box_length (2 : Fin 3)) :=
    apply_pbc_nested _ _ _ (hL (2 : Fin 3))
  rw [h0, h1, h2]

end LeanLJ
