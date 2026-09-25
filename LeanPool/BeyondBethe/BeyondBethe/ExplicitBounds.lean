/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.CleanConstants
public import LeanPool.BeyondBethe.BeyondBethe.NumericalWitness
public import LeanPool.BeyondBethe.BeyondBethe.GoodRowScore
public import LeanPool.BeyondBethe.BeyondBethe.DirectedElementary
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

/-! # Explicit Bounds -/

@[expose] public section

open scoped Topology

namespace BeyondBethe

/-!
# Explicit analytic bounds for the structural constants

The qualitative proof originally selected its absolute constants from
continuity neighborhoods.  This file develops quantitative estimates instead.
They will be used to replace every such choice by fixed rational data.
-/

/-- The entropy singularity at zero has an explicit square-root modulus. -/
theorem abs_negMulLog_lt_two_sqrt_abs {x : ℝ} (hx : abs x ≤ 1) :
    abs (Real.negMulLog x) ≤ 2 * Real.sqrt (abs x) := by
  by_cases hx0 : x = 0
  · subst x
    simp
  have hax : 0 < abs x := abs_pos.mpr hx0
  have hseries := Real.abs_log_mul_self_rpow_lt (abs x) (1 / 2 : ℝ)
    hax hx (by norm_num)
  rw [← Real.sqrt_eq_rpow] at hseries
  have hsqrt : 0 ≤ Real.sqrt (abs x) := Real.sqrt_nonneg _
  have hsquare : Real.sqrt (abs x) * Real.sqrt (abs x) = abs x := by
    nlinarith [Real.sq_sqrt (abs_nonneg x)]
  have hfactor :
      abs (Real.negMulLog x) =
        Real.sqrt (abs x) * abs (Real.log (abs x) * Real.sqrt (abs x)) := by
    calc
      abs (Real.negMulLog x) = abs x * abs (Real.log x) := by
        simp [Real.negMulLog_def]
      _ = abs x * abs (Real.log (abs x)) := by rw [Real.log_abs]
      _ = Real.sqrt (abs x) *
          abs (Real.log (abs x) * Real.sqrt (abs x)) := by
        rw [abs_mul, abs_of_nonneg hsqrt]
        calc
          abs x * abs (Real.log (abs x)) =
              (Real.sqrt (abs x) * Real.sqrt (abs x)) *
                abs (Real.log (abs x)) := by rw [hsquare]
          _ = Real.sqrt (abs x) *
              (abs (Real.log (abs x)) * Real.sqrt (abs x)) := by ring
  rw [hfactor]
  have htwo : abs (Real.log (abs x) * Real.sqrt (abs x)) < 2 := by
    norm_num at hseries ⊢
    exact hseries
  exact (mul_le_mul_of_nonneg_left htwo.le hsqrt).trans_eq (by ring)

/-- On a positive interval bounded away from zero, logarithm has the expected
elementary Lipschitz bound. -/
theorem abs_log_sub_log_le_div {a x y : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hay : a ≤ y) :
    abs (Real.log x - Real.log y) ≤ abs (x - y) / a := by
  have hx : 0 < x := ha.trans_le hax
  have hy : 0 < y := ha.trans_le hay
  rcases le_total x y with hxy | hyx
  · have hlogxy : Real.log x ≤ Real.log y :=
      Real.strictMonoOn_log.monotoneOn hx hy hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hlogxy), abs_of_nonpos (sub_nonpos.mpr hxy)]
    rw [neg_sub, neg_sub, ← Real.log_div hy.ne' hx.ne']
    calc
      Real.log (y / x) ≤ y / x - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hy hx)
      _ = (y - x) / x := by field_simp
      _ ≤ (y - x) / a := by
        exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) ha hax
  · have hlogyx : Real.log y ≤ Real.log x :=
      Real.strictMonoOn_log.monotoneOn hy hx hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hlogyx), abs_of_nonneg (sub_nonneg.mpr hyx)]
    rw [← Real.log_div hx.ne' hy.ne']
    calc
      Real.log (x / y) ≤ x / y - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hx hy)
      _ = (x - y) / y := by field_simp
      _ ≤ (x - y) / a := by
        exact div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) ha hay

/-- A coarse numerical log bound on the fixed interval used by the good-row
argument.  Its slack is intentional: only an absolute modulus is needed. -/
theorem abs_log_le_two_of_mem {x : ℝ}
    (hxlo : (3 / 10 : ℝ) ≤ x) (hxhi : x ≤ 3 / 2) :
    abs (Real.log x) ≤ 2 := by
  have hx : 0 < x := (by norm_num : (0 : ℝ) < 3 / 10).trans_le hxlo
  have he : Real.exp (-2) < (1 / 4 : ℝ) := by
    rw [show (-2 : ℝ) = -1 + -1 by ring, Real.exp_add]
    have h := Real.exp_neg_one_lt_half
    have hp := Real.exp_pos (-1)
    nlinarith
  have hlow : -2 < Real.log x := by
    rw [← Real.exp_lt_exp, Real.exp_log hx]
    exact (he.trans_le (show (1 / 4 : ℝ) ≤ 3 / 10 by norm_num)).trans_le hxlo
  have hupp : Real.log x ≤ 1 / 2 := by
    exact (Real.log_le_sub_one_of_pos hx).trans (by linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `negMulLog` is explicitly Lipschitz on `[3/10,6/5]`. -/
theorem abs_negMulLog_sub_le_six_mul {x y : ℝ}
    (hxlo : (3 / 10 : ℝ) ≤ x) (hxhi : x ≤ 6 / 5)
    (hylo : (3 / 10 : ℝ) ≤ y) (hyhi : y ≤ 6 / 5) :
    abs (Real.negMulLog x - Real.negMulLog y) ≤ 6 * abs (x - y) := by
  have hlogx := abs_log_le_two_of_mem hxlo (hxhi.trans (by norm_num))
  have hlogdiff := abs_log_sub_log_le_div
    (a := (3 / 10 : ℝ)) (by norm_num) hxlo hylo
  have hy0 : 0 ≤ y := (by norm_num : (0 : ℝ) ≤ 3 / 10).trans hylo
  rw [Real.negMulLog_def]
  have hid :
      -x * Real.log x - -y * Real.log y =
        -(x - y) * Real.log x - y * (Real.log x - Real.log y) := by ring
  rw [hid]
  calc
    abs (-(x - y) * Real.log x - y * (Real.log x - Real.log y)) ≤
        abs (-(x - y) * Real.log x) +
          abs (y * (Real.log x - Real.log y)) := abs_sub _ _
    _ = abs (x - y) * abs (Real.log x) +
          y * abs (Real.log x - Real.log y) := by
        rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hy0]
    _ ≤ abs (x - y) * 2 + y * (abs (x - y) / (3 / 10 : ℝ)) := by
        gcongr
    _ ≤ 6 * abs (x - y) := by
        have hd : 0 ≤ abs (x - y) := abs_nonneg _
        have hycoef : (10 / 3 : ℝ) * y ≤ 4 := by nlinarith
        have hterm : y * (abs (x - y) / (3 / 10 : ℝ)) ≤
            4 * abs (x - y) := by
          calc
            y * (abs (x - y) / (3 / 10 : ℝ)) =
                ((10 / 3 : ℝ) * y) * abs (x - y) := by ring
            _ ≤ 4 * abs (x - y) :=
              mul_le_mul_of_nonneg_right hycoef hd
        linarith

/-- A product-log estimate on the same fixed interval. -/
theorem abs_mul_log_sub_mul_log_le
    {x y s t : ℝ}
    (hx : abs x ≤ 6 / 5) (hy : abs y ≤ 6 / 5)
    (hslo : (3 / 10 : ℝ) ≤ s) (hshi : s ≤ 3 / 2)
    (htlo : (3 / 10 : ℝ) ≤ t) (hthi : t ≤ 3 / 2) :
    abs (x * Real.log s - y * Real.log t) ≤
      2 * abs (x - y) + 4 * abs (s - t) := by
  have hlogs := abs_log_le_two_of_mem hslo hshi
  have hlogdiff := abs_log_sub_log_le_div
    (a := (3 / 10 : ℝ)) (by norm_num) hslo htlo
  have hid : x * Real.log s - y * Real.log t =
      (x - y) * Real.log s + y * (Real.log s - Real.log t) := by ring
  rw [hid]
  calc
    abs ((x - y) * Real.log s + y * (Real.log s - Real.log t)) ≤
        abs ((x - y) * Real.log s) +
          abs (y * (Real.log s - Real.log t)) := abs_add_le _ _
    _ = abs (x - y) * abs (Real.log s) +
          abs y * abs (Real.log s - Real.log t) := by rw [abs_mul, abs_mul]
    _ ≤ abs (x - y) * 2 +
          (6 / 5 : ℝ) * (abs (s - t) / (3 / 10 : ℝ)) := by gcongr
    _ = 2 * abs (x - y) + 4 * abs (s - t) := by ring

/-- Binary entropy is explicitly Lipschitz on `[3/10,7/10]`. -/
theorem abs_binaryEntropy_sub_half_le {p : ℝ}
    (hp0 : (3 / 10 : ℝ) ≤ p) (hp1 : p ≤ 7 / 10) :
    abs (binaryEntropy p - Real.log 2) ≤ 12 * abs (p - 1 / 2) := by
  have h1p0 : (3 / 10 : ℝ) ≤ 1 - p := by linarith
  have h1p1 : 1 - p ≤ 7 / 10 := by linarith
  have hp := abs_negMulLog_sub_le_six_mul hp0 (hp1.trans (by norm_num))
    (show (3 / 10 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) ≤ 6 / 5 by norm_num)
  have h1p := abs_negMulLog_sub_le_six_mul h1p0 (h1p1.trans (by norm_num))
    (show (3 / 10 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) ≤ 6 / 5 by norm_num)
  rw [binaryEntropy, Real.negMulLog_def]
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hcenter :
      -((1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) +
          -((1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) = Real.log 2 := by
    rw [hloghalf]
    ring
  rw [← hcenter]
  have hid :
      (-p * Real.log p + -(1 - p) * Real.log (1 - p)) -
          (-((1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) +
            -((1 / 2 : ℝ) * Real.log (1 / 2 : ℝ))) =
        (Real.negMulLog p - Real.negMulLog (1 / 2 : ℝ)) +
          (Real.negMulLog (1 - p) - Real.negMulLog (1 / 2 : ℝ)) := by
    simp only [Real.negMulLog_def]
    ring
  rw [hid]
  calc
    abs ((Real.negMulLog p - Real.negMulLog (1 / 2 : ℝ)) +
        (Real.negMulLog (1 - p) - Real.negMulLog (1 / 2 : ℝ))) ≤
      abs (Real.negMulLog p - Real.negMulLog (1 / 2 : ℝ)) +
        abs (Real.negMulLog (1 - p) - Real.negMulLog (1 / 2 : ℝ)) :=
      abs_add_le _ _
    _ ≤ 6 * abs (p - 1 / 2) +
        6 * abs ((1 - p) - 1 / 2) := add_le_add hp h1p
    _ = 12 * abs (p - 1 / 2) := by
      congr 1
      rw [show (1 - p) - 1 / 2 = -(p - 1 / 2) by ring, abs_neg]
      ring

/-- The suffix error with a small suffix mass has an explicit square-root
modulus around `(1/2,0)`. -/
theorem abs_continuousSuffixError_near_zero
    {u q r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 10)
    (hu : abs (u - 1 / 2) ≤ r) (hq : abs q ≤ r) :
    abs (continuousSuffixError u q -
        continuousSuffixError (1 / 2) 0) ≤
      11 * r + 2 * Real.sqrt r := by
  have hu' := abs_le.mp hu
  have hq' := abs_le.mp hq
  have hu0 : (2 / 5 : ℝ) ≤ u := by linarith
  have hu1 : u ≤ 3 / 5 := by linarith
  have hq0 : -(1 / 10 : ℝ) ≤ q := by linarith
  have hq1 : q ≤ 1 / 10 := by linarith
  have hs0 : (3 / 10 : ℝ) ≤ u + q := by linarith
  have hs1 : u + q ≤ 7 / 10 := by linarith
  have hqabs : abs q ≤ 6 / 5 := hq.trans (hr1.trans (by norm_num))
  have hprod := abs_mul_log_sub_mul_log_le
    hqabs (by norm_num : abs (0 : ℝ) ≤ 6 / 5)
    hs0 (hs1.trans (by norm_num))
    (show (3 / 10 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) ≤ 3 / 2 by norm_num)
  have hsdev : abs ((u + q) - 1 / 2) ≤ 2 * r := by
    calc
      abs ((u + q) - 1 / 2) = abs ((u - 1 / 2) + q) := by ring
      _ ≤ abs (u - 1 / 2) + abs q := abs_add_le _ _
      _ ≤ r + r := add_le_add hu hq
      _ = 2 * r := by ring
  have hprod' : abs (q * Real.log (u + q) -
      0 * Real.log (1 / 2)) ≤ 10 * r := by
    calc
      abs (q * Real.log (u + q) - 0 * Real.log (1 / 2)) ≤
          2 * abs (q - 0) + 4 * abs ((u + q) - 1 / 2) := hprod
      _ ≤ 2 * r + 4 * (2 * r) := by gcongr <;> simpa using hq
      _ = 10 * r := by ring
  have hnml := abs_negMulLog_lt_two_sqrt_abs
    (x := q) (hq.trans (hr1.trans (by norm_num)))
  have hsqrt : Real.sqrt (abs q) ≤ Real.sqrt r :=
    Real.sqrt_le_sqrt hq
  have hnml' : abs (Real.negMulLog q - Real.negMulLog 0) ≤
      2 * Real.sqrt r := by
    simpa using hnml.trans (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
  simp only [continuousSuffixError]
  have hid :
      (u - q * Real.log (u + q) - Real.negMulLog q) -
          ((1 / 2 : ℝ) - 0 * Real.log (1 / 2 + 0) - Real.negMulLog 0) =
        (u - 1 / 2) -
          (q * Real.log (u + q) - 0 * Real.log (1 / 2)) -
          (Real.negMulLog q - Real.negMulLog 0) := by ring
  rw [hid]
  calc
    abs ((u - 1 / 2) -
        (q * Real.log (u + q) - 0 * Real.log (1 / 2)) -
        (Real.negMulLog q - Real.negMulLog 0)) ≤
      abs (u - 1 / 2) +
        abs (q * Real.log (u + q) - 0 * Real.log (1 / 2)) +
        abs (Real.negMulLog q - Real.negMulLog 0) := by
          calc
            abs (((u - 1 / 2) -
                (q * Real.log (u + q) - 0 * Real.log (1 / 2))) -
                (Real.negMulLog q - Real.negMulLog 0)) ≤
              abs ((u - 1 / 2) -
                (q * Real.log (u + q) - 0 * Real.log (1 / 2))) +
                abs (Real.negMulLog q - Real.negMulLog 0) := abs_sub _ _
            _ ≤ (abs (u - 1 / 2) +
                abs (q * Real.log (u + q) - 0 * Real.log (1 / 2))) +
                abs (Real.negMulLog q - Real.negMulLog 0) :=
              add_le_add (abs_sub _ _) le_rfl
    _ ≤ r + 10 * r + 2 * Real.sqrt r :=
      add_le_add (add_le_add hu hprod') hnml'
    _ = 11 * r + 2 * Real.sqrt r := by ring

/-- The nonsingular suffix terms are uniformly Lipschitz around
`(1/2,1/2)`. -/
theorem abs_continuousSuffixError_near_half
    {u v q r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 10)
    (hu : abs (u - 1 / 2) ≤ r)
    (hv : abs (v - 1 / 2) ≤ r) (hq : abs q ≤ r) :
    abs (continuousSuffixError u (v + q) -
        continuousSuffixError (1 / 2) (1 / 2)) ≤ 29 * r := by
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  have hq' := abs_le.mp hq
  have hxdev : abs ((v + q) - 1 / 2) ≤ 2 * r := by
    calc
      abs ((v + q) - 1 / 2) = abs ((v - 1 / 2) + q) := by ring
      _ ≤ abs (v - 1 / 2) + abs q := abs_add_le _ _
      _ ≤ r + r := add_le_add hv hq
      _ = 2 * r := by ring
  have hsdev : abs ((u + (v + q)) - 1) ≤ 3 * r := by
    calc
      abs ((u + (v + q)) - 1) =
          abs ((u - 1 / 2) + (v - 1 / 2) + q) := by ring
      _ ≤ abs ((u - 1 / 2) + (v - 1 / 2)) + abs q := abs_add_le _ _
      _ ≤ (abs (u - 1 / 2) + abs (v - 1 / 2)) + abs q := by
        gcongr
        exact abs_add_le _ _
      _ ≤ (r + r) + r := by gcongr
      _ = 3 * r := by ring
  have hx0 : (3 / 10 : ℝ) ≤ v + q := by linarith
  have hx1 : v + q ≤ 7 / 10 := by linarith
  have hs0 : (7 / 10 : ℝ) ≤ u + (v + q) := by linarith
  have hs1 : u + (v + q) ≤ 13 / 10 := by linarith
  have hprod := abs_mul_log_sub_mul_log_le
    (show abs (v + q) ≤ 6 / 5 by rw [abs_le]; constructor <;> linarith)
    (by norm_num : abs (1 / 2 : ℝ) ≤ 6 / 5)
    (show (3 / 10 : ℝ) ≤ u + (v + q) from hs0.trans' (by norm_num))
    (show u + (v + q) ≤ (3 / 2 : ℝ) from hs1.trans (by norm_num))
    (show (3 / 10 : ℝ) ≤ 1 by norm_num)
    (show (1 : ℝ) ≤ 3 / 2 by norm_num)
  have hprod' :
      abs ((v + q) * Real.log (u + (v + q)) -
          (1 / 2) * Real.log 1) ≤ 16 * r := by
    calc
      abs ((v + q) * Real.log (u + (v + q)) -
          (1 / 2) * Real.log 1) ≤
          2 * abs ((v + q) - 1 / 2) +
            4 * abs ((u + (v + q)) - 1) := hprod
      _ ≤ 2 * (2 * r) + 4 * (3 * r) := by gcongr
      _ = 16 * r := by ring
  have hnml := abs_negMulLog_sub_le_six_mul hx0
    (hx1.trans (by norm_num))
    (show (3 / 10 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) ≤ 6 / 5 by norm_num)
  have hnml' :
      abs (Real.negMulLog (v + q) - Real.negMulLog (1 / 2)) ≤
        12 * r := by
    calc
      abs (Real.negMulLog (v + q) - Real.negMulLog (1 / 2)) ≤
          6 * abs ((v + q) - 1 / 2) := hnml
      _ ≤ 6 * (2 * r) := mul_le_mul_of_nonneg_left hxdev (by norm_num)
      _ = 12 * r := by ring
  simp only [continuousSuffixError]
  have hid :
      (u - (v + q) * Real.log (u + (v + q)) - Real.negMulLog (v + q)) -
          ((1 / 2 : ℝ) - (1 / 2) * Real.log ((1 / 2) + (1 / 2)) -
            Real.negMulLog (1 / 2)) =
        (u - 1 / 2) -
          ((v + q) * Real.log (u + (v + q)) - (1 / 2) * Real.log 1) -
          (Real.negMulLog (v + q) - Real.negMulLog (1 / 2)) := by ring
  rw [hid]
  calc
    abs ((u - 1 / 2) -
        ((v + q) * Real.log (u + (v + q)) - (1 / 2) * Real.log 1) -
        (Real.negMulLog (v + q) - Real.negMulLog (1 / 2))) ≤
      abs (u - 1 / 2) +
        abs ((v + q) * Real.log (u + (v + q)) - (1 / 2) * Real.log 1) +
        abs (Real.negMulLog (v + q) - Real.negMulLog (1 / 2)) := by
          calc
            abs (((u - 1 / 2) -
                ((v + q) * Real.log (u + (v + q)) -
                  (1 / 2) * Real.log 1)) -
                (Real.negMulLog (v + q) - Real.negMulLog (1 / 2))) ≤
              abs ((u - 1 / 2) -
                ((v + q) * Real.log (u + (v + q)) -
                  (1 / 2) * Real.log 1)) +
                abs (Real.negMulLog (v + q) - Real.negMulLog (1 / 2)) :=
              abs_sub _ _
            _ ≤ (abs (u - 1 / 2) +
                abs ((v + q) * Real.log (u + (v + q)) -
                  (1 / 2) * Real.log 1)) +
                abs (Real.negMulLog (v + q) - Real.negMulLog (1 / 2)) :=
              add_le_add (abs_sub _ _) le_rfl
    _ ≤ r + 16 * r + 12 * r := add_le_add (add_le_add hu hprod') hnml'
    _ = 29 * r := by ring

/-- An explicit modulus for the complete three-variable good-row expression.
The constant `70` is deliberately loose; having a transparent computable
bound is more important than optimizing this one-time structural constant. -/
theorem abs_continuousGoodRowPsi_sub_center_le
    {u v q r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 10)
    (hu : abs (u - 1 / 2) ≤ r)
    (hv : abs (v - 1 / 2) ≤ r) (hq : abs q ≤ r) :
    abs (continuousGoodRowPsi u v q -
        continuousGoodRowPsi (1 / 2) (1 / 2) 0) ≤
      70 * Real.sqrt r := by
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  have hq' := abs_le.mp hq
  have hden0 : 9 / 10 ≤ 1 - q := by linarith
  have hden1 : 1 - q ≤ 11 / 10 := by linarith
  have hdenpos : 0 < 1 - q := (by norm_num : (0 : ℝ) < 9 / 10).trans_le hden0
  let p : ℝ := u / (1 - q)
  have hpdev : abs (p - 1 / 2) ≤ 2 * r := by
    have hnum : abs ((u - 1 / 2) + q / 2) ≤ 3 * r / 2 := by
      calc
        abs ((u - 1 / 2) + q / 2) ≤
            abs (u - 1 / 2) + abs (q / 2) := abs_add_le _ _
        _ = abs (u - 1 / 2) + abs q / 2 := by
          rw [abs_div, show abs (2 : ℝ) = 2 by norm_num]
        _ ≤ r + r / 2 := by gcongr
        _ = 3 * r / 2 := by ring
    have hid : p - 1 / 2 = ((u - 1 / 2) + q / 2) / (1 - q) := by
      dsimp only [p]
      field_simp
      ring
    rw [hid, abs_div, abs_of_pos hdenpos]
    rw [div_le_iff₀ hdenpos]
    calc
      abs ((u - 1 / 2) + q / 2) ≤ 3 * r / 2 := hnum
      _ ≤ 2 * r * (1 - q) := by
        have : (9 / 10 : ℝ) ≤ 1 - q := hden0
        nlinarith
  have hp0 : (3 / 10 : ℝ) ≤ p := by
    have := (abs_le.mp hpdev).1
    linarith
  have hp1 : p ≤ 7 / 10 := by
    have := (abs_le.mp hpdev).2
    linarith
  have hH := abs_binaryEntropy_sub_half_le hp0 hp1
  have hH' : abs (Real.binEntropy p - Real.log 2) ≤ 24 * r := by
    rw [← binaryEntropy_eq_realBinEntropy]
    exact hH.trans (by
      calc
        12 * abs (p - 1 / 2) ≤ 12 * (2 * r) :=
          mul_le_mul_of_nonneg_left hpdev (by norm_num)
        _ = 24 * r := by ring)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2one : abs (Real.log 2) ≤ 1 := by
    rw [abs_of_pos hlog2pos]
    exact Real.log_two_lt_d9.le.trans (by norm_num)
  have hdenabs : abs (1 - q) ≤ 11 / 10 := by
    rw [abs_of_pos hdenpos]
    exact hden1
  have hmain :
      abs ((1 - q) * Real.binEntropy p - Real.log 2) ≤ 28 * r := by
    have hid : (1 - q) * Real.binEntropy p - Real.log 2 =
        (1 - q) * (Real.binEntropy p - Real.log 2) - q * Real.log 2 := by ring
    rw [hid]
    calc
      abs ((1 - q) * (Real.binEntropy p - Real.log 2) - q * Real.log 2) ≤
          abs ((1 - q) * (Real.binEntropy p - Real.log 2)) +
            abs (q * Real.log 2) := abs_sub _ _
      _ = abs (1 - q) * abs (Real.binEntropy p - Real.log 2) +
          abs q * abs (Real.log 2) := by rw [abs_mul, abs_mul]
      _ ≤ (11 / 10 : ℝ) * (24 * r) + r * 1 := by gcongr
      _ ≤ 28 * r := by nlinarith
  have hU0 := abs_continuousSuffixError_near_zero hr0 hr1 hu hq
  have hV0 := abs_continuousSuffixError_near_zero hr0 hr1 hv hq
  have hUV := abs_continuousSuffixError_near_half hr0 hr1 hu hv hq
  have hVU := abs_continuousSuffixError_near_half hr0 hr1 hv hu hq
  let dU0 := continuousSuffixError u q - continuousSuffixError (1 / 2) 0
  let dUV := continuousSuffixError u (v + q) -
    continuousSuffixError (1 / 2) (1 / 2)
  let dV0 := continuousSuffixError v q - continuousSuffixError (1 / 2) 0
  let dVU := continuousSuffixError v (u + q) -
    continuousSuffixError (1 / 2) (1 / 2)
  have hsum : abs (dU0 + dUV + dV0 + dVU) ≤
      (11 * r + 2 * Real.sqrt r) + 29 * r +
        (11 * r + 2 * Real.sqrt r) + 29 * r := by
    calc
      abs (dU0 + dUV + dV0 + dVU) ≤
          abs (dU0 + dUV + dV0) + abs dVU := abs_add_le _ _
      _ ≤ (abs (dU0 + dUV) + abs dV0) + abs dVU :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (abs dU0 + abs dUV + abs dV0) + abs dVU :=
        add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ = abs dU0 + abs dUV + abs dV0 + abs dVU := by ring
      _ ≤ (11 * r + 2 * Real.sqrt r) + 29 * r +
          (11 * r + 2 * Real.sqrt r) + 29 * r := by
        dsimp only [dU0, dUV, dV0, dVU]
        gcongr
  have hbin : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
  have hid :
      continuousGoodRowPsi u v q -
          continuousGoodRowPsi (1 / 2) (1 / 2) 0 =
        ((1 - q) * Real.binEntropy p - Real.log 2) +
          (1 / 2) * (dU0 + dUV + dV0 + dVU) := by
    dsimp only [p, dU0, dUV, dV0, dVU]
    simp only [continuousGoodRowPsi, sub_zero, div_one, add_zero, one_mul]
    rw [hbin]
    ring
  rw [hid]
  have hsqrt0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg _
  have hrleone : r ≤ 1 := hr1.trans (by norm_num)
  have hrle : r ≤ Real.sqrt r := by
    rw [Real.le_sqrt hr0 hr0]
    nlinarith
  calc
    abs (((1 - q) * Real.binEntropy p - Real.log 2) +
        (1 / 2) * (dU0 + dUV + dV0 + dVU)) ≤
      abs ((1 - q) * Real.binEntropy p - Real.log 2) +
        abs ((1 / 2) * (dU0 + dUV + dV0 + dVU)) := abs_add_le _ _
    _ = abs ((1 - q) * Real.binEntropy p - Real.log 2) +
        (1 / 2) * abs (dU0 + dUV + dV0 + dVU) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ 28 * r + (1 / 2) *
        ((11 * r + 2 * Real.sqrt r) + 29 * r +
          (11 * r + 2 * Real.sqrt r) + 29 * r) := by gcongr
    _ = 68 * r + 2 * Real.sqrt r := by ring
    _ ≤ 70 * Real.sqrt r := by nlinarith

/-- The compact supremum used by the structural proof is bounded by the
explicit modulus above. -/
theorem goodRowOmega_le_seventy_sqrt_radius (η : ℝ) :
    goodRowOmega η ≤ 70 * Real.sqrt (goodRowRadius η) := by
  unfold goodRowOmega
  apply csSup_le ((goodRowBall_nonempty η).image goodRowDeviation)
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hz' := hz
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff,
    Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq,
    Real.dist_eq] at hz'
  rcases hz' with ⟨hu, hv, hq⟩
  simp only [goodRowCenter, Prod.fst, Prod.snd, sub_zero] at hu hv hq
  have hbound := abs_continuousGoodRowPsi_sub_center_le
    (goodRowRadius_nonneg η) (goodRowRadius_le_tenth η) hu hv hq
  have hc : continuousGoodRowPsi (1 / 2) (1 / 2) 0 = Real.log 2 / 2 := by
    simpa [goodRowCenter] using continuousGoodRowPsi_center
  rw [goodRowDeviation, ← hc, abs_sub_comm]
  exact hbound

theorem goodRowOmega_le_seventy_sqrt
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 10) :
    goodRowOmega η ≤ 70 * Real.sqrt η := by
  simpa [goodRowRadius_eq hη0 hη1] using
    goodRowOmega_le_seventy_sqrt_radius η

/-- An exact algebraic form of the clean core on its natural domain. -/
theorem cleanCoreFunction_eq_expanded
    {κ ρ : ℝ} (hρ : ρ < 1) :
    cleanCoreFunction κ ρ =
      Real.log 2 - ρ * Real.log 2 - 2 * κ + ρ * κ -
        (1 - ρ) * Real.log (1 - ρ) - Real.negMulLog ρ - ρ := by
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ
  have hexp : Real.exp (-κ) ≠ 0 := (Real.exp_pos _).ne'
  rw [cleanCoreFunction, Real.log_div (mul_ne_zero (by norm_num) (pow_ne_zero 2 hexp))
    hden.ne', Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 hexp),
    Real.log_pow, Real.log_exp]
  ring

/-- A simple lower bound for the clean core. -/
theorem cleanCoreFunction_lower
    {κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Real.log 2 - ρ * Real.log 2 - 2 * κ - Real.negMulLog ρ - ρ ≤
      cleanCoreFunction κ ρ := by
  rw [cleanCoreFunction_eq_expanded hρ1]
  have hκρ : 0 ≤ ρ * κ := mul_nonneg hρ0 hκ
  have hlog : Real.log (1 - ρ) ≤ 0 :=
    Real.log_nonpos (sub_nonneg.mpr hρ1.le) (by linarith)
  have hden : 0 ≤ 1 - ρ := sub_nonneg.mpr hρ1.le
  have hterm : 0 ≤ -(1 - ρ) * Real.log (1 - ρ) :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hden) hlog
  linarith

/-- The fixed local-cost threshold used by the executable proof. -/
def explicitKappa : ℚ := 1 / 1000

theorem explicitKappa_pos : 0 < explicitKappa := by
  norm_num [explicitKappa]

theorem leakageEnvelope_explicitKappa_le :
    leakageEnvelope (explicitKappa : ℝ) ≤ 1 / 250 := by
  have hkabs : abs ((explicitKappa : ℚ) : ℝ) ≤ 1 := by
    norm_num [explicitKappa]
  have hexp := Real.abs_exp_sub_one_le hkabs
  have hnonneg : 0 ≤ Real.exp ((explicitKappa : ℚ) : ℝ) - 1 := by
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num [explicitKappa])
  rw [abs_of_nonneg hnonneg] at hexp
  rw [leakageEnvelope]
  norm_num [explicitKappa] at hexp ⊢
  linarith

theorem explicitKappa_cleanCore
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρbar : ρ ≤ leakageEnvelope (explicitKappa : ℝ)) :
    Real.log 2 / 2 < cleanCoreFunction (explicitKappa : ℝ) ρ := by
  have hρ250 : ρ ≤ 1 / 250 :=
    hρbar.trans leakageEnvelope_explicitKappa_le
  have hρ1 : ρ < 1 := hρ250.trans_lt (by norm_num)
  have hρabs : abs ρ ≤ 1 := by
    rw [abs_of_nonneg hρ0]
    exact hρ250.trans (by norm_num)
  have hnmlabs := abs_negMulLog_lt_two_sqrt_abs hρabs
  have hnml : Real.negMulLog ρ ≤ 2 / 15 := by
    calc
      Real.negMulLog ρ ≤ abs (Real.negMulLog ρ) := le_abs_self _
      _ ≤ 2 * Real.sqrt ρ := by simpa [abs_of_nonneg hρ0] using hnmlabs
      _ ≤ 2 * (1 / 15 : ℝ) := by
        gcongr
        rw [Real.sqrt_le_iff]
        constructor
        · norm_num
        · nlinarith
      _ = 2 / 15 := by ring
  have hcore := cleanCoreFunction_lower
    (κ := ((explicitKappa : ℚ) : ℝ)) (ρ := ρ)
    (by norm_num [explicitKappa]) hρ0 hρ1
  have hloglo := Real.log_two_gt_d9
  have hloghi := Real.log_two_lt_d9
  have hcore' :
      Real.log 2 - ρ * Real.log 2 - 1 / 500 - Real.negMulLog ρ - ρ ≤
        cleanCoreFunction (explicitKappa : ℝ) ρ := by
    convert hcore using 1 <;> norm_num [explicitKappa]
  have hρlog : ρ * Real.log 2 ≤ (1 / 250 : ℝ) * 0.6931471808 := by
    calc
      ρ * Real.log 2 ≤ (1 / 250 : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hρ250 (Real.log_pos (by norm_num)).le
      _ ≤ (1 / 250 : ℝ) * 0.6931471808 :=
        mul_le_mul_of_nonneg_left hloghi.le (by norm_num)
  have hhalf : Real.log 2 / 2 < 1 / 2 := by
    linarith
  have hlower : (1 / 2 : ℝ) <
      Real.log 2 - ρ * Real.log 2 - 1 / 500 - Real.negMulLog ρ - ρ := by
    nlinarith
  exact hhalf.trans (hlower.trans_le hcore')

/-- The clean-pair constants are fixed data, rather than values selected from
an unspecified continuity neighborhood. -/
def explicitXiSource : ℚ := 1 / 100

/-- The fixed rational structural gain parameter `1/4`. -/
def explicitGamma : ℚ := 1 / 4

theorem explicit_cleanPairGain_constants :
    CleanPairGainGuarantee (explicitKappa : ℝ)
      (explicitXiSource : ℝ) (explicitGamma : ℝ) := by
  intro n ell ξ τ A X rscale cscale hell hlogn hξ hξ₀ hτ
    hApos hX hXint hrscale hcscale hKKT r s a b hrs hab hcost
  have hellpos : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hτpos : 0 < τ := by rw [hτ]; positivity
  let ρ := outsideMassTwo (pairAlpha X r s) a b
  have hρnonneg : 0 ≤ ρ := by
    dsimp only [ρ, outsideMassTwo]
    exact Finset.sum_nonneg fun j _ ↦ pairAlpha_nonneg hX r s j
  have hκposR : 0 < ((explicitKappa : ℚ) : ℝ) := by
    exact_mod_cast explicitKappa_pos
  by_cases hρzero : ρ = 0
  · have hbarNonneg : 0 ≤ leakageEnvelope ((explicitKappa : ℚ) : ℝ) := by
      rw [leakageEnvelope]
      have hexp : 1 ≤ Real.exp ((explicitKappa : ℚ) : ℝ) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr hκposR.le
      linarith
    have hcoreZero := explicitKappa_cleanCore (ρ := 0) le_rfl hbarNonneg
    have hcoreLog : Real.log 2 / 2 <
        Real.log (2 * (Real.exp (-((explicitKappa : ℚ) : ℝ))) ^ 2) := by
      simpa [cleanCoreFunction] using hcoreZero
    have hgain := log_pairGain_ge_core_of_zeroLeakage
      hτpos.le hApos hX hXint hrscale hcscale hKKT hrs hab hcost
      (by simpa only [ρ] using hρzero)
    have hgamma : ((explicitGamma : ℚ) : ℝ) < Real.log 2 / 2 := by
      have := Real.log_two_gt_d9
      norm_num [explicitGamma] at *
      linarith
    exact le_of_lt (hgamma.trans (hcoreLog.trans_le hgain))
  · have hρpos : 0 < ρ := lt_of_le_of_ne hρnonneg (Ne.symm hρzero)
    have hρbar : ρ ≤ leakageEnvelope ((explicitKappa : ℚ) : ℝ) := by
      dsimp only [ρ, leakageEnvelope]
      exact pairOutsideMass_le_exp hτpos.le hκposR.le hXint hab hcost
    have hρsmall : ρ < 1 / 10 :=
      (hρbar.trans leakageEnvelope_explicitKappa_le).trans_lt (by norm_num)
    have hρone : ρ < 1 := hρsmall.trans (by norm_num)
    have hcoreRho := explicitKappa_cleanCore hρnonneg hρbar
    have hentropy := outsideEntropyBracket_lt_four_scale hX hρpos
      hρsmall hell hlogn
    have hclean := cleanGainLowerBound_gt_of_core_and_entropy
      hξ hellpos hτ hcoreRho hentropy
    have hgain := log_pairGain_ge_cleanGainLowerBound_of_positiveLeakage
      hτpos.le hApos hX hXint hrscale hcscale hKKT hrs hab hcost
      hρpos hρone
    have hgamma : ((explicitGamma : ℚ) : ℝ) <
        Real.log 2 / 2 - ξ := by
      have hlog := Real.log_two_gt_d9
      have hξbound : ξ ≤ 1 / 100 := by
        simpa [explicitXiSource] using hξ₀
      norm_num [explicitGamma] at *
      linarith
    exact le_of_lt (hgamma.trans (hclean.trans_le hgain))

/-- The same hard-coded constants lower-bound the explicit finite witness
itself.  Thus the clean-pair analysis needs no per-pair capacity optimizer. -/
theorem explicit_cleanPairWitnessGain_constants :
    ExplicitPairWitnessGainGuarantee (explicitKappa : ℝ)
      (explicitXiSource : ℝ) (explicitGamma : ℝ) := by
  intro n ell ξ τ X hell hlogn hξ hξ₀ hτ hX hXint
    r s a b hrs hab hcost
  have hellpos : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hτpos : 0 < τ := by rw [hτ]; positivity
  let ρ := outsideMassTwo (pairAlpha X r s) a b
  have hρnonneg : 0 ≤ ρ := by
    dsimp only [ρ, outsideMassTwo]
    exact Finset.sum_nonneg fun j _ ↦ pairAlpha_nonneg hX r s j
  have hκposR : 0 < ((explicitKappa : ℚ) : ℝ) := by
    exact_mod_cast explicitKappa_pos
  by_cases hρzero : ρ = 0
  · have hbarNonneg : 0 ≤ leakageEnvelope ((explicitKappa : ℚ) : ℝ) := by
      rw [leakageEnvelope]
      have hexp : 1 ≤ Real.exp ((explicitKappa : ℚ) : ℝ) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr hκposR.le
      linarith
    have hcoreZero := explicitKappa_cleanCore (ρ := 0) le_rfl hbarNonneg
    have hcoreLog : Real.log 2 / 2 <
        Real.log (2 * (Real.exp (-((explicitKappa : ℚ) : ℝ))) ^ 2) := by
      simpa [cleanCoreFunction] using hcoreZero
    have hgain := coreLowerBound_le_explicitPairWitnessLogGain_of_zeroLeakage
      hτpos.le hX hXint hrs hab hcost (by simpa only [ρ] using hρzero)
    have hgamma : ((explicitGamma : ℚ) : ℝ) < Real.log 2 / 2 := by
      have := Real.log_two_gt_d9
      norm_num [explicitGamma] at *
      linarith
    exact le_of_lt (hgamma.trans (hcoreLog.trans_le hgain))
  · have hρpos : 0 < ρ := lt_of_le_of_ne hρnonneg (Ne.symm hρzero)
    have hρbar : ρ ≤ leakageEnvelope ((explicitKappa : ℚ) : ℝ) := by
      dsimp only [ρ, leakageEnvelope]
      exact pairOutsideMass_le_exp hτpos.le hκposR.le hXint hab hcost
    have hρsmall : ρ < 1 / 10 :=
      (hρbar.trans leakageEnvelope_explicitKappa_le).trans_lt (by norm_num)
    have hρone : ρ < 1 := hρsmall.trans (by norm_num)
    have hcoreRho := explicitKappa_cleanCore hρnonneg hρbar
    have hentropy := outsideEntropyBracket_lt_four_scale hX hρpos
      hρsmall hell hlogn
    have hclean := cleanGainLowerBound_gt_of_core_and_entropy
      hξ hellpos hτ hcoreRho hentropy
    have hgain := cleanGainLowerBound_le_explicitPairWitnessLogGain
      hτpos.le hX hXint hrs hab hcost hρpos hρone
    have hgamma : ((explicitGamma : ℚ) : ℝ) <
        Real.log 2 / 2 - ξ := by
      have hlog := Real.log_two_gt_d9
      have hξbound : ξ ≤ 1 / 100 := by
        simpa [explicitXiSource] using hξ₀
      norm_num [explicitGamma] at *
      linarith
    exact le_of_lt (hgamma.trans (hclean.trans_le hgain))

end BeyondBethe
