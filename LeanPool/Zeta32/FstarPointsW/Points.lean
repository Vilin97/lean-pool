/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.FstarPointsW.Bounds

/-! The 15 point checks `Wlow_(k-1) ≤ Wt (x_k)`, `x_k = aMinus·k/16`.
Each is `Wt_ge` applied to the rational atom bounds of `Bounds.lean`, followed by one `norm_num`
over exact rationals. Parameters (arctan mode, scaling `2^k` and Taylor lengths for the two logs)
were attributed upstream to `tools/choose_params.py` and `tools/gen_points.py`.
Those scripts are not distributed upstream; see `CertificateReproduction.lean` for the exact
inputs and a self-contained rational reproduction procedure. -/

public section

open Real

namespace Zeta32.Fstar.PW

/-- `x_1 = 0.11666375`; exact slack of the rational bound ≈ 0.0015. -/
theorem Wt_x1 : ((17/250 : ℚ) : ℝ) ≤ Wt (xk 1) := by
  have hx : xk 1 = (93331/800000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (93331/800000 : ℝ)) (by norm_num) (arctan_ge_S4 (by norm_num))
    (log_le_scaled (by norm_num) 0 1 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_2 = 0.23332750`; exact slack of the rational bound ≈ 0.0003. -/
theorem Wt_x2 : ((153/1000 : ℚ) : ℝ) ≤ Wt (xk 2) := by
  have hx : xk 2 = (93331/400000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (93331/400000 : ℝ)) (by norm_num) (arctan_ge_S4 (by norm_num))
    (log_le_scaled (by norm_num) 0 1 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_3 = 0.34999125`; exact slack of the rational bound ≈ 0.0042. -/
theorem Wt_x3 : ((127/500 : ℚ) : ℝ) ≤ Wt (xk 3) := by
  have hx : xk 3 = (279993/800000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (279993/800000 : ℝ)) (by norm_num) (arctan_ge_S4 (by norm_num))
    (log_le_scaled (by norm_num) 0 2 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_4 = 0.46665500`; exact slack of the rational bound ≈ 0.0015. -/
theorem Wt_x4 : ((369/1000 : ℚ) : ℝ) ≤ Wt (xk 4) := by
  have hx : xk 4 = (93331/200000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (93331/200000 : ℝ)) (by norm_num) (arctan_ge_S4 (by norm_num))
    (log_le_scaled (by norm_num) 0 2 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_5 = 0.58331875`; exact slack of the rational bound ≈ 0.0058. -/
theorem Wt_x5 : ((499/1000 : ℚ) : ℝ) ≤ Wt (xk 5) := by
  have hx : xk 5 = (93331/160000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (93331/160000 : ℝ)) (by norm_num) (arctan_ge_S4 (by norm_num))
    (log_le_scaled (by norm_num) 0 4 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_6 = 0.69998250`; exact slack of the rational bound ≈ 0.0055. -/
theorem Wt_x6 : ((641/1000 : ℚ) : ℝ) ≤ Wt (xk 6) := by
  have hx : xk 6 = (279993/400000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (279993/400000 : ℝ)) (by norm_num) (arctan_ge_S4 (by norm_num))
    (log_le_scaled (by norm_num) 1 3 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_7 = 0.81664625`; exact slack of the rational bound ≈ 0.0113. -/
theorem Wt_x7 : ((397/500 : ℚ) : ℝ) ≤ Wt (xk 7) := by
  have hx : xk 7 = (653317/800000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (653317/800000 : ℝ)) (by norm_num) (arctan_ge_shift_neg (by
    norm_num) (by norm_num))
    (log_le_scaled (by norm_num) 1 2 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_8 = 0.93331000`; exact slack of the rational bound ≈ 0.0156. -/
theorem Wt_x8 : ((239/250 : ℚ) : ℝ) ≤ Wt (xk 8) := by
  have hx : xk 8 = (93331/100000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (93331/100000 : ℝ)) (by norm_num) (arctan_ge_shift_neg (by
    norm_num) (by norm_num))
    (log_le_scaled (by norm_num) 1 1 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_9 = 1.04997375`; exact slack of the rational bound ≈ 0.0199. -/
theorem Wt_x9 : ((141/125 : ℚ) : ℝ) ≤ Wt (xk 9) := by
  have hx : xk 9 = (839979/800000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (839979/800000 : ℝ)) (by norm_num) (arctan_ge_shift_pos (by
    norm_num))
    (log_le_scaled (by norm_num) 1 1 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_10 = 1.16663750`; exact slack of the rational bound ≈ 0.0222. -/
theorem Wt_x10 : ((1307/1000 : ℚ) : ℝ) ≤ Wt (xk 10) := by
  have hx : xk 10 = (93331/80000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (93331/80000 : ℝ)) (by norm_num) (arctan_ge_shift_pos (by
    norm_num))
    (log_le_scaled (by norm_num) 1 2 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_11 = 1.28330125`; exact slack of the rational bound ≈ 0.0014. -/
theorem Wt_x11 : ((1493/1000 : ℚ) : ℝ) ≤ Wt (xk 11) := by
  have hx : xk 11 = (1026641/800000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (1026641/800000 : ℝ)) (by norm_num) (arctan_ge_shift_pos (by
    norm_num))
    (log_le_scaled (by norm_num) 1 2 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_12 = 1.39996500`; exact slack of the rational bound ≈ 0.0115. -/
theorem Wt_x12 : ((421/250 : ℚ) : ℝ) ≤ Wt (xk 12) := by
  have hx : xk 12 = (279993/200000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (279993/200000 : ℝ)) (by norm_num) (arctan_ge_shift_pos (by
    norm_num))
    (log_le_scaled (by norm_num) 2 2 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_13 = 1.51662875`; exact slack of the rational bound ≈ 0.0020. -/
theorem Wt_x13 : ((1881/1000 : ℚ) : ℝ) ≤ Wt (xk 13) := by
  have hx : xk 13 = (1213303/800000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (1213303/800000 : ℝ)) (by norm_num) (arctan_ge_shift_pos (by
    norm_num))
    (log_le_scaled (by norm_num) 2 1 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 2))
  norm_num [Finset.sum_range_succ]

/-- `x_14 = 1.63329250`; exact slack of the rational bound ≈ 0.0291. -/
theorem Wt_x14 : ((2083/1000 : ℚ) : ℝ) ≤ Wt (xk 14) := by
  have hx : xk 14 = (653317/400000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (653317/400000 : ℝ)) (by norm_num) (arctan_ge_shift_pos (by
    norm_num))
    (log_le_scaled (by norm_num) 2 1 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

/-- `x_15 = 1.74995625`; exact slack of the rational bound ≈ 0.0387. -/
theorem Wt_x15 : ((286/125 : ℚ) : ℝ) ≤ Wt (xk 15) := by
  have hx : xk 15 = (279993/160000 : ℝ) := by norm_num [xk, aMinus]
  rw [hx]
  refine le_trans ?_ (Wt_ge (x := (279993/160000 : ℝ)) (by norm_num) (arctan_ge_shift_pos (by
    norm_num))
    (log_le_scaled (by norm_num) 2 1 (by norm_num)) (arctan_le_S3 (by norm_num))
    (log_one_add_ge (by norm_num) (by norm_num) 1))
  norm_num [Finset.sum_range_succ]

end Zeta32.Fstar.PW
