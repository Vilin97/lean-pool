/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationBasic

/-!
# Pointwise truncation bounds

The Marcinkiewicz interpolation argument used for the Caffarelli–Kohn–Nirenberg
program (CKN 1982) controls the two pieces of a function `f` cut at a level
`l > 0` by the single power `|f| ^ p`, for `1 < p < 2`.  This file records the
two elementary pointwise inequalities that make that reduction work, stated for
the `ℝ≥0∞`-valued modulus `absE f x = ENNReal.ofReal |f x|`.

Above the level the first inequality bounds the modulus itself by
`l ^ (1 - p) * |f| ^ p`; below the level the second bounds its square by
`l ^ (2 - p) * |f| ^ p`.  Both are pointwise in `x` and depend only on the
scalar comparison of `|f x|` with `l`; the exponents `l ^ (1 - p)` and
`l ^ (2 - p)` are real powers.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- Above the level `l`, the modulus is dominated by the `p`-th power with the
weight `l ^ (1 - p)`: from `l < |f x|` the monotonicity of real powers gives
`|f x| ≤ l ^ (1 - p) * |f x| ^ p` whenever `1 < p`. -/
lemma absE_le_of_lt_absE {f : Vec3 → ℝ} {p l : ℝ} (hp1 : 1 < p) (hl : 0 < l) {x : Vec3}
    (hx : ENNReal.ofReal l < absE f x) :
    absE f x ≤ ENNReal.ofReal (l ^ (1 - p)) * absE f x ^ p := by
  have hx' : ENNReal.ofReal l < ENNReal.ofReal |f x| := hx
  have hla : l < |f x| := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hl.le).mp hx'
  have hapos : 0 < |f x| := lt_trans hl hla
  have hp0 : (0 : ℝ) ≤ p := by linarith only [hp1]
  have hrpowpos : 0 < l ^ (p - 1) := Real.rpow_pos_of_pos hl _
  have hle : l ^ (p - 1) ≤ |f x| ^ (p - 1) :=
    Real.rpow_le_rpow hl.le hla.le (by linarith only [hp1])
  have hap : |f x| ^ p = |f x| * |f x| ^ (p - 1) := by
    calc |f x| ^ p = |f x| ^ (1 + (p - 1)) := by congr 1; ring
      _ = |f x| ^ 1 * |f x| ^ (p - 1) := Real.rpow_add hapos 1 (p - 1)
      _ = |f x| * |f x| ^ (p - 1) := by rw [Real.rpow_one]
  have hlinv : l ^ (1 - p) = (l ^ (p - 1))⁻¹ := by
    rw [show 1 - p = -(p - 1) by ring, Real.rpow_neg hl.le]
  have hreal : |f x| ≤ l ^ (1 - p) * |f x| ^ p := by
    rw [hlinv, hap, inv_mul_eq_div, le_div_iff₀ hrpowpos]
    exact mul_le_mul_of_nonneg_left hle hapos.le
  change ENNReal.ofReal |f x| ≤ ENNReal.ofReal (l ^ (1 - p)) * ENNReal.ofReal |f x| ^ p
  calc ENNReal.ofReal |f x| ≤ ENNReal.ofReal (l ^ (1 - p) * |f x| ^ p) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (l ^ (1 - p)) * ENNReal.ofReal |f x| ^ p := by
        rw [ENNReal.ofReal_rpow_of_nonneg hapos.le hp0,
          ENNReal.ofReal_mul (Real.rpow_nonneg hl.le _)]

/-- Below the level `l`, the square is dominated by the `p`-th power with the
weight `l ^ (2 - p)`: from `|f x| ≤ l` the monotonicity of real powers gives
`|f x| ^ 2 ≤ l ^ (2 - p) * |f x| ^ p` whenever `0 < p < 2`. -/
lemma absE_sq_le_of_absE_le {f : Vec3 → ℝ} {p l : ℝ} (hp0 : 0 < p) (hp2 : p < 2) (hl : 0 < l)
    {x : Vec3} (hx : absE f x ≤ ENNReal.ofReal l) :
    absE f x ^ 2 ≤ ENNReal.ofReal (l ^ (2 - p)) * absE f x ^ p := by
  have hx' : ENNReal.ofReal |f x| ≤ ENNReal.ofReal l := hx
  have hal : |f x| ≤ l := (ENNReal.ofReal_le_ofReal_iff hl.le).mp hx'
  have ha : (0 : ℝ) ≤ |f x| := abs_nonneg _
  have h2p : (0 : ℝ) ≤ 2 - p := by linarith only [hp2]
  have hreal : |f x| ^ 2 ≤ l ^ (2 - p) * |f x| ^ p := by
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · rw [← ha0]
      simp [Real.zero_rpow hp0.ne']
    · have hle : |f x| ^ (2 - p) ≤ l ^ (2 - p) :=
        Real.rpow_le_rpow hapos.le hal h2p
      have hid : |f x| ^ 2 = |f x| ^ p * |f x| ^ (2 - p) := by
        calc |f x| ^ 2 = |f x| ^ (2 : ℝ) := (Real.rpow_natCast |f x| 2).symm
          _ = |f x| ^ (p + (2 - p)) := by congr 1; ring
          _ = |f x| ^ p * |f x| ^ (2 - p) := Real.rpow_add hapos p (2 - p)
      rw [hid]
      calc |f x| ^ p * |f x| ^ (2 - p) ≤ |f x| ^ p * l ^ (2 - p) :=
            mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hapos.le p)
        _ = l ^ (2 - p) * |f x| ^ p := by rw [mul_comm]
  change ENNReal.ofReal |f x| ^ 2 ≤ ENNReal.ofReal (l ^ (2 - p)) * ENNReal.ofReal |f x| ^ p
  calc ENNReal.ofReal |f x| ^ 2 = ENNReal.ofReal (|f x| ^ 2) :=
        (ENNReal.ofReal_pow ha 2).symm
    _ ≤ ENNReal.ofReal (l ^ (2 - p) * |f x| ^ p) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (l ^ (2 - p)) * ENNReal.ofReal |f x| ^ p := by
        rw [ENNReal.ofReal_rpow_of_nonneg ha hp0.le,
          ENNReal.ofReal_mul (Real.rpow_nonneg hl.le _)]

end CKN.Foundation.Euclidean
