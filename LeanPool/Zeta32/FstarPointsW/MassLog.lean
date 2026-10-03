/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.FstarPointsW.Bounds

/-! Mass bracket `massA aMinus < 1 < massA aPlus` (square roots compared
through rational squares; `massA a = (1 + a + 4√(1+a²) - √(25+a²))/6`, margins ≈ 1.2e-6 and 5.7e-6),
and `549/500 < log 3` from `2 log 3 = 3 log 2 + log (1 + 1/8)`. Written from scratch. -/

public section

open Real

namespace Zeta32.Fstar.PW

theorem mass_minus_lt_one : massA aMinus < 1 := by
  have h1 : √(1 + aMinus^2) < 21176096 / 10^7 :=
    (sqrt_lt' (by norm_num)).2 (by norm_num [aMinus])
  have h25 : 53370656 / 10^7 < √(25 + aMinus^2) :=
    (lt_sqrt (by norm_num)).2 (by norm_num [aMinus])
  have ha : aMinus = 186662 / 100000 := by norm_num [aMinus]
  unfold massA
  rw [ha] at h1 h25 ⊢
  linarith

theorem one_lt_mass_plus : 1 < massA aPlus := by
  have h1 : 21176183 / 10^7 < √(1 + aPlus^2) :=
    (lt_sqrt (by norm_num)).2 (by norm_num [aPlus])
  have h25 : √(25 + aPlus^2) < 53370692 / 10^7 :=
    (sqrt_lt' (by norm_num)).2 (by norm_num [aPlus])
  have ha : aPlus = 186663 / 100000 := by norm_num [aPlus]
  unfold massA
  rw [ha] at h1 h25 ⊢
  linarith

theorem log_three_gt : (549/500 : ℝ) < log 3 := by
  have hl : (117742 / 1000000 : ℝ) ≤ log (1 + 1/8) := by
    refine le_trans ?_ (log_one_add_ge (by norm_num) (by norm_num) 4)
    norm_num [Finset.sum_range_succ]
  have h9 : log 9 = 2 * log 3 := by
    rw [show (9:ℝ) = 3^2 by norm_num, log_pow]; norm_num
  have h98 : log 9 = 3 * log 2 + log (1 + 1/8) := by
    rw [show (9:ℝ) = 2^3 * (1 + 1/8) by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  linarith [log_two_gt_d9]

end Zeta32.Fstar.PW
