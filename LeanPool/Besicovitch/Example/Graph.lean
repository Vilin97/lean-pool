/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Besicovitch's function

Besicovitch's purely unrectifiable set with lower density `1/2` is the graph of the function
`g = ∑ₙ fₙ`, where `fₙ` is a square wave of period `2 * 2^(-n²)` and amplitude
`2^(-n²) / n`.  This file defines the function and proves the two estimates that everything
else rests on: inside a level-`n` cell `g` varies by at most `4 * 2^(-(n+1)²) / (n+1)`, and
across a level-`n` cell boundary it jumps by at least `2^(-n²) / n`.

The construction follows Capdevila, *Besicovitch's example in higher dimensions*,
arXiv:2607.05206, §2, which in turn follows Besicovitch (1938) and Dickinson (1939).
-/

@[expose] public section

noncomputable section

open Finset

namespace LeanPool.Besicovitch.Example

/-- The length `2^(-n²)` of a level-`n` cell. -/
def cellLength (n : ℕ) : ℝ := (1 / 2) ^ (n ^ 2)

/-- The amplitude `2^(-n²) / n` of the level-`n` square wave. -/
def jumpHeight (n : ℕ) : ℝ := cellLength n / n

/-- The index of the level-`n` cell `[i * cellLength n, (i + 1) * cellLength n)` containing `x`. -/
def cellIndex (n : ℕ) (x : ℝ) : ℤ := ⌊x / cellLength n⌋

/-- The level-`n` square wave: `-jumpHeight n` on even cells, `+jumpHeight n` on odd cells. -/
def squareWave (n : ℕ) (x : ℝ) : ℝ :=
  if Even (cellIndex n x) then -jumpHeight n else jumpHeight n

/-- Besicovitch's function, the sum of the square waves of every level `n ≥ 1`. -/
def besicovitchFun (x : ℝ) : ℝ := ∑' n : ℕ, squareWave (n + 1) x

/-! ### The cell lengths -/

theorem cellLength_pos (n : ℕ) : 0 < cellLength n := by
  unfold cellLength; positivity

theorem cellLength_le_one (n : ℕ) : cellLength n ≤ 1 := by
  unfold cellLength; exact pow_le_one₀ (by norm_num) (by norm_num)

/-- Consecutive cell lengths shrink by a factor of at least two. -/
theorem cellLength_succ_le (n : ℕ) : cellLength (n + 1) ≤ cellLength n / 2 := by
  unfold cellLength
  have h : n ^ 2 + 1 ≤ (n + 1) ^ 2 := by ring_nf; omega
  calc ((1 : ℝ) / 2) ^ ((n + 1) ^ 2) ≤ (1 / 2) ^ (n ^ 2 + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    _ = (1 / 2) ^ (n ^ 2) / 2 := by rw [pow_succ]; ring

/-- At level `n ≥ 1` consecutive cell lengths shrink by a factor of at least eight. -/
theorem cellLength_succ_le_of_pos {n : ℕ} (hn : 1 ≤ n) :
    cellLength (n + 1) ≤ cellLength n / 8 := by
  unfold cellLength
  have h : n ^ 2 + 3 ≤ (n + 1) ^ 2 := by ring_nf; omega
  calc ((1 : ℝ) / 2) ^ ((n + 1) ^ 2) ≤ (1 / 2) ^ (n ^ 2 + 3) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    _ = (1 / 2) ^ (n ^ 2) / 8 := by rw [pow_add]; ring

theorem cellLength_add_le (n m : ℕ) : cellLength (n + m) ≤ cellLength n * (1 / 2) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc cellLength (n + (m + 1)) ≤ cellLength (n + m) / 2 := cellLength_succ_le _
      _ ≤ cellLength n * (1 / 2) ^ m / 2 := by gcongr
      _ = cellLength n * (1 / 2) ^ (m + 1) := by rw [pow_succ]; ring

theorem cellLength_antitone : Antitone cellLength := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  have := cellLength_succ_le n
  have := cellLength_pos n
  linarith

/-- A coarser cell length is a natural multiple of a finer one. -/
theorem cellLength_eq_mul {j n : ℕ} (h : j ≤ n) :
    cellLength j = cellLength n * ((2 ^ (n ^ 2 - j ^ 2) : ℕ) : ℝ) := by
  have hle : j ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left h 2
  obtain ⟨d, hd⟩ : ∃ d, n ^ 2 = j ^ 2 + d := ⟨n ^ 2 - j ^ 2, by omega⟩
  unfold cellLength
  rw [hd, Nat.add_sub_cancel_left, pow_add]
  push_cast
  rw [mul_assoc, ← mul_pow]
  norm_num

theorem jumpHeight_nonneg (n : ℕ) : 0 ≤ jumpHeight n :=
  div_nonneg (cellLength_pos n).le (Nat.cast_nonneg n)

theorem jumpHeight_le_cellLength (n : ℕ) : jumpHeight n ≤ cellLength n := by
  unfold jumpHeight
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [(cellLength_pos 0).le]
  · exact div_le_self (cellLength_pos n).le (by exact_mod_cast hn)

/-! ### The square waves -/

theorem abs_squareWave (n : ℕ) (x : ℝ) : |squareWave n x| = jumpHeight n := by
  unfold squareWave
  split_ifs
  · rw [abs_neg, abs_of_nonneg (jumpHeight_nonneg n)]
  · rw [abs_of_nonneg (jumpHeight_nonneg n)]

theorem squareWave_eq_of_cellIndex_eq {n : ℕ} {x y : ℝ} (h : cellIndex n x = cellIndex n y) :
    squareWave n x = squareWave n y := by
  simp [squareWave, h]

/-- On adjacent cells the square waves have opposite signs. -/
theorem squareWave_add_squareWave_of_adjacent {n : ℕ} {x y : ℝ}
    (h : cellIndex n y = cellIndex n x + 1 ∨ cellIndex n x = cellIndex n y + 1) :
    squareWave n x + squareWave n y = 0 := by
  have key : ∀ a : ℤ, (if Even a then -jumpHeight n else jumpHeight n) +
      (if Even (a + 1) then -jumpHeight n else jumpHeight n) = 0 := by
    intro a
    by_cases ha : Even a
    · have h1 : ¬ Even (a + 1) := by rw [Int.even_add_one]; exact not_not.mpr ha
      simp [ha, h1]
    · have h1 : Even (a + 1) := Int.even_add_one.mpr ha
      simp [ha, h1]
  unfold squareWave
  rcases h with h | h
  · rw [h]; exact key _
  · rw [h, add_comm]; exact key _

/-- Points less than a cell length apart lie in the same or in adjacent cells. -/
theorem cellIndex_sub_le {n : ℕ} {x y : ℝ} (h : |x - y| < cellLength n) :
    |cellIndex n x - cellIndex n y| ≤ 1 := by
  unfold cellIndex
  have hpos := cellLength_pos n
  have hxy : |x / cellLength n - y / cellLength n| < 1 := by
    rw [← sub_div, abs_div, abs_of_pos hpos, div_lt_one hpos]; exact h
  rw [abs_lt] at hxy
  have h1 := Int.floor_le (x / cellLength n)
  have h2 := Int.lt_floor_add_one (x / cellLength n)
  have h3 := Int.floor_le (y / cellLength n)
  have h4 := Int.lt_floor_add_one (y / cellLength n)
  have hu : (⌊x / cellLength n⌋ : ℝ) < ⌊y / cellLength n⌋ + 2 := by linarith
  have hl : (⌊y / cellLength n⌋ : ℝ) < ⌊x / cellLength n⌋ + 2 := by linarith
  have hu' : ⌊x / cellLength n⌋ < ⌊y / cellLength n⌋ + 2 := by exact_mod_cast hu
  have hl' : ⌊y / cellLength n⌋ < ⌊x / cellLength n⌋ + 2 := by exact_mod_cast hl
  rw [abs_le]; omega

/-- Cells of a coarser level are unions of cells of a finer level. -/
theorem cellIndex_eq_of_le {j n : ℕ} (hjn : j ≤ n) {x y : ℝ}
    (h : cellIndex n x = cellIndex n y) : cellIndex j x = cellIndex j y := by
  unfold cellIndex at *
  have hcell := cellLength_eq_mul hjn
  have key : ∀ z : ℝ,
      z / cellLength j = z / cellLength n / ((2 ^ (n ^ 2 - j ^ 2) : ℕ) : ℝ) :=
    fun z ↦ by rw [hcell, div_mul_eq_div_div]
  rw [key x, key y, Int.floor_div_natCast, Int.floor_div_natCast, h]

/-! ### Summability and the tail bound -/

theorem cellLength_le_geom (n : ℕ) : cellLength n ≤ (1 / 2) ^ n := by
  unfold cellLength
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_self_pow two_ne_zero n)

theorem tendsto_cellLength : Filter.Tendsto cellLength Filter.atTop (nhds 0) :=
  squeeze_zero (fun n ↦ (cellLength_pos n).le) cellLength_le_geom
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

theorem cellLength_succ_le_geom (n : ℕ) : cellLength (n + 1) ≤ (1 / 2) ^ n := by
  unfold cellLength
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by nlinarith)

theorem summable_squareWave (x : ℝ) : Summable fun n : ℕ ↦ squareWave (n + 1) x := by
  refine Summable.of_norm_bounded summable_geometric_two fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_squareWave]
  exact (jumpHeight_le_cellLength _).trans (cellLength_succ_le_geom n)

theorem summable_jumpHeight (n : ℕ) : Summable fun m : ℕ ↦ jumpHeight (n + 1 + m) := by
  refine Summable.of_nonneg_of_le (fun m ↦ jumpHeight_nonneg _) (fun m ↦ ?_)
    (summable_geometric_two.mul_left (cellLength (n + 1)))
  calc jumpHeight (n + 1 + m) ≤ cellLength (n + 1 + m) := jumpHeight_le_cellLength _
    _ ≤ cellLength (n + 1) * (1 / 2) ^ m := cellLength_add_le _ _

/-- The amplitudes beyond level `n` sum to at most `2 * cellLength (n+1) / (n+1)`. -/
theorem tsum_jumpHeight_tail_le (n : ℕ) :
    ∑' m : ℕ, jumpHeight (n + 1 + m) ≤ 2 * cellLength (n + 1) / (n + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbound : ∀ m : ℕ,
      jumpHeight (n + 1 + m) ≤ cellLength (n + 1) / (n + 1) * (1 / 2) ^ m := by
    intro m
    unfold jumpHeight
    have h1 : cellLength (n + 1 + m) ≤ cellLength (n + 1) * (1 / 2) ^ m := cellLength_add_le _ _
    have h2 : (n : ℝ) + 1 ≤ ((n + 1 + m : ℕ) : ℝ) := by
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
    calc cellLength (n + 1 + m) / ((n + 1 + m : ℕ) : ℝ)
        ≤ cellLength (n + 1 + m) / ((n : ℝ) + 1) :=
          div_le_div_of_nonneg_left (cellLength_pos _).le hn h2
      _ ≤ cellLength (n + 1) * (1 / 2) ^ m / ((n : ℝ) + 1) := by gcongr
      _ = cellLength (n + 1) / (n + 1) * (1 / 2) ^ m := by ring
  calc ∑' m : ℕ, jumpHeight (n + 1 + m)
      ≤ ∑' m : ℕ, cellLength (n + 1) / (n + 1) * (1 / 2) ^ m :=
        Summable.tsum_le_tsum hbound (summable_jumpHeight n) (summable_geometric_two.mul_left _)
    _ = cellLength (n + 1) / (n + 1) * 2 := by rw [tsum_mul_left, tsum_geometric_two]
    _ = 2 * cellLength (n + 1) / (n + 1) := by ring

/-! ### The two estimates -/

/-- The difference of `g` at two points, with the first `n` levels separated off. -/
theorem besicovitchFun_sub_eq (n : ℕ) (x y : ℝ) :
    besicovitchFun x - besicovitchFun y =
      (∑ m ∈ range n, (squareWave (m + 1) x - squareWave (m + 1) y)) +
        ∑' m : ℕ, (squareWave (n + 1 + m) x - squareWave (n + 1 + m) y) := by
  have hx := summable_squareWave x
  have hy := summable_squareWave y
  have h1 : besicovitchFun x - besicovitchFun y =
      ∑' m : ℕ, (squareWave (m + 1) x - squareWave (m + 1) y) := by
    unfold besicovitchFun
    exact (hx.tsum_sub hy).symm
  have h2 : ∑' m : ℕ, (squareWave (m + 1) x - squareWave (m + 1) y) =
      (∑ m ∈ range n, (squareWave (m + 1) x - squareWave (m + 1) y)) +
        ∑' m : ℕ, (squareWave (m + n + 1) x - squareWave (m + n + 1) y) :=
    ((hx.sub hy).sum_add_tsum_nat_add n).symm
  have h3 : ∑' m : ℕ, (squareWave (m + n + 1) x - squareWave (m + n + 1) y) =
      ∑' m : ℕ, (squareWave (n + 1 + m) x - squareWave (n + 1 + m) y) :=
    tsum_congr fun m ↦ by rw [show m + n + 1 = n + 1 + m by ring]
  rw [h1, h2, h3]

theorem abs_squareWave_sub_le (n : ℕ) (x y : ℝ) :
    |squareWave n x - squareWave n y| ≤ 2 * jumpHeight n := by
  calc |squareWave n x - squareWave n y| ≤ |squareWave n x| + |squareWave n y| := abs_sub _ _
    _ = 2 * jumpHeight n := by rw [abs_squareWave, abs_squareWave]; ring

/-- The tail beyond level `n` contributes at most `4 * cellLength (n+1) / (n+1)`. -/
theorem abs_tail_le (n : ℕ) (x y : ℝ) :
    |∑' m : ℕ, (squareWave (n + 1 + m) x - squareWave (n + 1 + m) y)| ≤
      4 * cellLength (n + 1) / (n + 1) := by
  have hsum : Summable fun m : ℕ ↦ 2 * jumpHeight (n + 1 + m) :=
    (summable_jumpHeight n).mul_left 2
  have hle : ∀ m : ℕ, ‖squareWave (n + 1 + m) x - squareWave (n + 1 + m) y‖ ≤
      2 * jumpHeight (n + 1 + m) := fun m ↦ by
    rw [Real.norm_eq_abs]; exact abs_squareWave_sub_le _ x y
  have hnorm : Summable fun m : ℕ ↦ ‖squareWave (n + 1 + m) x - squareWave (n + 1 + m) y‖ :=
    Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _) hle hsum
  have h1 := norm_tsum_le_tsum_norm hnorm
  have h2 : ∑' m : ℕ, ‖squareWave (n + 1 + m) x - squareWave (n + 1 + m) y‖ ≤
      ∑' m : ℕ, 2 * jumpHeight (n + 1 + m) := Summable.tsum_le_tsum hle hnorm hsum
  have h3 : ∑' m : ℕ, 2 * jumpHeight (n + 1 + m) ≤
      2 * (2 * cellLength (n + 1) / (n + 1)) := by
    rw [tsum_mul_left]; gcongr; exact tsum_jumpHeight_tail_le n
  simp only [Real.norm_eq_abs] at h1 h2
  calc |∑' m : ℕ, (squareWave (n + 1 + m) x - squareWave (n + 1 + m) y)|
      ≤ ∑' m : ℕ, |squareWave (n + 1 + m) x - squareWave (n + 1 + m) y| := h1
    _ ≤ ∑' m : ℕ, 2 * jumpHeight (n + 1 + m) := h2
    _ ≤ 2 * (2 * cellLength (n + 1) / (n + 1)) := h3
    _ = 4 * cellLength (n + 1) / (n + 1) := by ring

/-- **(E1)** Inside a level-`n` cell, `g` varies by at most `4 * cellLength (n+1) / (n+1)`. -/
theorem abs_besicovitchFun_sub_le {n : ℕ} {x y : ℝ} (h : cellIndex n x = cellIndex n y) :
    |besicovitchFun x - besicovitchFun y| ≤ 4 * cellLength (n + 1) / (n + 1) := by
  rw [besicovitchFun_sub_eq n]
  have hzero : ∑ m ∈ range n, (squareWave (m + 1) x - squareWave (m + 1) y) = 0 := by
    refine sum_eq_zero fun m hm ↦ ?_
    rw [squareWave_eq_of_cellIndex_eq (cellIndex_eq_of_le (by simpa using hm) h), sub_self]
  rw [hzero, zero_add]
  exact abs_tail_le n x y

/-- Adjacent cells at level `n` are less than two cell lengths apart. -/
theorem abs_sub_lt_of_adjacent {n : ℕ} {x y : ℝ}
    (h : cellIndex n y = cellIndex n x + 1 ∨ cellIndex n x = cellIndex n y + 1) :
    |x - y| < 2 * cellLength n := by
  unfold cellIndex at h
  have hpos := cellLength_pos n
  have h1 := Int.floor_le (x / cellLength n)
  have h2 := Int.lt_floor_add_one (x / cellLength n)
  have h3 := Int.floor_le (y / cellLength n)
  have h4 := Int.lt_floor_add_one (y / cellLength n)
  have key : |x - y| = |x / cellLength n - y / cellLength n| * cellLength n := by
    rw [← sub_div, abs_div, abs_of_pos hpos, div_mul_cancel₀ _ hpos.ne']
  have hlt : |x / cellLength n - y / cellLength n| < 2 := by
    rw [abs_lt]
    rcases h with h | h
    · have : (⌊y / cellLength n⌋ : ℝ) = ⌊x / cellLength n⌋ + 1 := by exact_mod_cast h
      constructor <;> linarith
    · have : (⌊x / cellLength n⌋ : ℝ) = ⌊y / cellLength n⌋ + 1 := by exact_mod_cast h
      constructor <;> linarith
  rw [key]
  exact mul_lt_mul_of_pos_right hlt hpos

/-- **(E2)** Across a level-`n` cell boundary, `g` jumps by at least `cellLength n / n`. -/
theorem le_abs_besicovitchFun_sub {n : ℕ} (hn : 1 ≤ n) {x y : ℝ}
    (h : cellIndex n y = cellIndex n x + 1 ∨ cellIndex n x = cellIndex n y + 1) :
    cellLength n / n ≤ |besicovitchFun x - besicovitchFun y| := by
  have hne : cellIndex n x ≠ cellIndex n y := by rcases h with h | h <;> omega
  -- the least level `k ≥ 1` at which `x` and `y` separate
  classical
  have hex : ∃ k, 1 ≤ k ∧ cellIndex k x ≠ cellIndex k y := ⟨n, hn, hne⟩
  obtain ⟨k, hk1, hkne, hkn, hmin⟩ :
      ∃ k, 1 ≤ k ∧ cellIndex k x ≠ cellIndex k y ∧ k ≤ n ∧
      ∀ j, 1 ≤ j → j < k → cellIndex j x = cellIndex j y :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, Nat.find_min' hex ⟨hn, hne⟩,
      fun j hj hjk ↦ by_contra fun hc ↦ Nat.find_min hex hjk ⟨hj, hc⟩⟩
  -- `x` and `y` are adjacent at level `k`
  have hadj : cellIndex k y = cellIndex k x + 1 ∨ cellIndex k x = cellIndex k y + 1 := by
    rcases hkn.lt_or_eq with hlt | heq
    · have hdist : |x - y| < cellLength k :=
        calc |x - y| < 2 * cellLength n := abs_sub_lt_of_adjacent h
          _ ≤ 2 * cellLength (k + 1) := by gcongr; exact cellLength_antitone hlt
          _ ≤ cellLength k := by linarith [cellLength_succ_le k]
      have := cellIndex_sub_le hdist
      rw [abs_le] at this
      omega
    · rw [heq]; exact h
  -- split off the levels below `k`, which cancel, and level `k` itself
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hsplit := besicovitchFun_sub_eq (k' + 1) x y
  rw [sum_range_succ] at hsplit
  have hlow : ∑ m ∈ range k', (squareWave (m + 1) x - squareWave (m + 1) y) = 0 := by
    refine sum_eq_zero fun m hm ↦ ?_
    rw [squareWave_eq_of_cellIndex_eq (hmin (m + 1) (by omega) (by simpa using hm)), sub_self]
  rw [hlow, zero_add] at hsplit
  have hlevel : squareWave (k' + 1) x - squareWave (k' + 1) y = 2 * squareWave (k' + 1) x := by
    have := squareWave_add_squareWave_of_adjacent hadj; linarith
  set T := ∑' m : ℕ, (squareWave (k' + 1 + 1 + m) x - squareWave (k' + 1 + 1 + m) y) with hT
  have htail := abs_tail_le (k' + 1) x y
  rw [← hT] at htail
  push_cast at htail
  -- numerics, with `K = k' + 1 ≥ 1`
  have hK : (1 : ℝ) ≤ (k' : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k']
  have hKpos : (0 : ℝ) < (k' : ℝ) + 1 := by linarith
  have hratio := cellLength_succ_le_of_pos hk1
  have hpos := cellLength_pos (k' + 1)
  have hpos' := cellLength_pos (k' + 1 + 1)
  have hT' : 4 * cellLength (k' + 1 + 1) / ((k' : ℝ) + 1 + 1) ≤
      cellLength (k' + 1) / (2 * ((k' : ℝ) + 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hjump : jumpHeight (k' + 1) = cellLength (k' + 1) / ((k' : ℝ) + 1) := by
    rw [jumpHeight, Nat.cast_add, Nat.cast_one]
  have hA : 0 ≤ cellLength (k' + 1) / ((k' : ℝ) + 1) := div_nonneg hpos.le hKpos.le
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn' : (k' : ℝ) + 1 ≤ n := by exact_mod_cast hkn
  have hcl : cellLength n ≤ cellLength (k' + 1) := cellLength_antitone hkn
  calc cellLength n / n ≤ cellLength (k' + 1) / n := div_le_div_of_nonneg_right hcl hn'.le
    _ ≤ cellLength (k' + 1) / ((k' : ℝ) + 1) :=
        div_le_div_of_nonneg_left hpos.le hKpos hkn'
    _ ≤ 2 * jumpHeight (k' + 1) - |T| := by
        rw [hjump]
        have : cellLength (k' + 1) / (2 * ((k' : ℝ) + 1)) =
            cellLength (k' + 1) / ((k' : ℝ) + 1) / 2 := by rw [div_div, mul_comm]
        linarith
    _ = |2 * squareWave (k' + 1) x| - |-T| := by rw [abs_mul, abs_two, abs_squareWave, abs_neg]
    _ ≤ |2 * squareWave (k' + 1) x - -T| := abs_sub_abs_le_abs_sub _ _
    _ = |besicovitchFun x - besicovitchFun y| := by rw [sub_neg_eq_add, hsplit, hlevel]

end LeanPool.Besicovitch.Example
