/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Sum.Pieces
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The numerical constant of the finite-piece route (the proof notes, §8.5).

* `midRat` = Σ over the 196 relaxed pieces of `a_J |J| + b_J (x₂² − x₁²)/2` (exact rational; one
kernel `decide`
  per block of at most 10 pieces, about 200 rational operations each);
* `log (140/3) > 3842/1000` from `log 2 > 0.6931471803` and eight terms of the series of `log (1
− 13/48)`;
* `tailConst/20 + midRat + 35/36 − (25/4)·(3842/1000) < 283/50`.

The rational `midRat + tailConst'/20 + 35/36` with the addendum's tail constant is `Q_lean` of
results/lean-route-A.out; here the tail constant is `33/5 + 121/2000` (slightly weaker than
`33/5 + 28/500`,
see `psiL_le_tail`). -/

public section

namespace Zeta32.ArithSum
noncomputable section

/-- Exact integral of `pa i + pb i · x` over piece `i` in `x` (from `1/ub (i+1)` to `1/ub i`). -/
@[expose]
def pieceRat (i : ℕ) : ℚ :=
  pa i * (1 / ub i - 1 / ub (i + 1)) + pb i * ((1 / ub i ^ 2 - 1 / ub (i + 1) ^ 2) / 2)

/-- Block `m` of ten pieces (pieces `6 + 10 m, …, 15 + 10 m`, i.e. `⌊1/x⌋ = m + 1`). -/
def blockSum (m : ℕ) : ℚ := ∑ k ∈ Finset.range 10, pieceRat (6 + 10 * m + k)

theorem sum_blocks (f : ℕ → ℚ) (M : ℕ) :
    ∑ i ∈ Finset.range (6 + 10 * M), f i =
      ∑ i ∈ Finset.range 6, f i + ∑ m ∈ Finset.range M, ∑ k ∈ Finset.range 10, f (6 + 10 * m +
        k) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 6 + 10 * (M + 1) = (6 + 10 * M) + 10 by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ (fun m => ∑ k ∈ Finset.range 10, f (6 + 10 * m + k)) M, add_assoc]

theorem block_first : (∑ k ∈ Finset.range 6, pieceRat k) = 1009 / 144 := by
  decide +kernel

theorem block_0 : blockSum 0 = 4015 / 672 := by
  unfold blockSum; decide +kernel

theorem block_1 : blockSum 1 = 152363 / 51480 := by
  unfold blockSum; decide +kernel

theorem block_2 : blockSum 2 = 616250519 / 310390080 := by
  unfold blockSum; decide +kernel

theorem block_3 : blockSum 3 = 4012219219 / 2677114440 := by
  unfold blockSum; decide +kernel

theorem block_4 : blockSum 4 = 3283464907 / 2724081360 := by
  unfold blockSum; decide +kernel

theorem block_5 : blockSum 5 = 124791792809 / 123712617600 := by
  unfold blockSum; decide +kernel

theorem block_6 : blockSum 6 = 12118655774737 / 13968448253760 := by
  unfold blockSum; decide +kernel

theorem block_7 : blockSum 7 = 328867465879 / 432013982400 := by
  unfold blockSum; decide +kernel

theorem block_8 : blockSum 8 = 27420989731061 / 40430669872320 := by
  unfold blockSum; decide +kernel

theorem block_9 : blockSum 9 = 14470067125139 / 23659965769440 := by
  unfold blockSum; decide +kernel

theorem block_10 : blockSum 10 = 18445124464849 / 33120847987920 := by
  unfold blockSum; decide +kernel

theorem block_11 : blockSum 11 = 141300797426723 / 276398980166400 := by
  unfold blockSum; decide +kernel

theorem block_12 : blockSum 12 = 4153872264547 / 8791663949640 := by
  unfold blockSum; decide +kernel

theorem block_13 : blockSum 13 = 4351654092363449 / 9908021983933920 := by
  unfold blockSum; decide +kernel

theorem block_14 : blockSum 14 = 1036993512889637 / 2527297896689280 := by
  unfold blockSum; decide +kernel

theorem block_15 : blockSum 15 = 100380564220117 / 260728810742400 := by
  unfold blockSum; decide +kernel

theorem block_16 : blockSum 16 = 85354574727978923 / 235376990336648160 := by
  unfold blockSum; decide +kernel

theorem block_17 : blockSum 17 = 1061963532040441 / 3098647368016200 := by
  unfold blockSum; decide +kernel

theorem block_18 : blockSum 18 = 1088835113079157 / 3351473441796480 := by
  unfold blockSum; decide +kernel

/-- The rational part of the 196 relaxed pieces. -/
def midRat : ℚ := 100640561701307678525350005057360349523 / 3548246127954628149396735699088377600

theorem sum_pieceRat : (∑ i ∈ Finset.range 196, pieceRat i) = midRat := by
  rw [show (196 : ℕ) = 6 + 10 * 19 by norm_num, sum_blocks, block_first]
  change _ + ∑ m ∈ Finset.range 19, blockSum m = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, block_0, block_1, block_2, block_3,
    block_4, block_5, block_6, block_7, block_8, block_9, block_10, block_11, block_12,
    block_13, block_14, block_15, block_16, block_17, block_18]
  norm_num [midRat]

/-- `log (140/3) > 3.842`. -/
theorem log_140_div_3_gt : (3842 / 1000 : ℝ) < Real.log (140 / 3) := by
  have h2 := Real.log_two_gt_d9
  have hx : |(13 / 48 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hs := Real.abs_log_sub_add_sum_range_le hx 8
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 13 / 48)] at hs
  have hs' := (abs_le.mp hs).1
  have e : Real.log (140 / 3) = 6 * Real.log 2 + Real.log (1 - 13 / 48) := by
    rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 2), ← Real.log_mul (by positivity) (by norm_num)]
    norm_num
  rw [e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs'
  norm_num at hs' ⊢
  linarith

/-- Tail constant: `psiL x ≤ tailConst` for `0 < x ≤ 1/20`. -/
@[expose]
def tailConst : ℚ := 33 / 5 + 121 / 2000

theorem constant_lt :
    (tailConst : ℝ) / 20 + (midRat : ℝ) + 35 / 36 - 25 / 4 * Real.log (140 / 3) < 283 / 50 := by
  have h := log_140_div_3_gt
  have hq : (tailConst : ℝ) / 20 + (midRat : ℝ) + 35 / 36 - 25 / 4 * (3842 / 1000) < 283 / 50 := by
    norm_num [tailConst, midRat]
  linarith

end
end Zeta32.ArithSum

end
