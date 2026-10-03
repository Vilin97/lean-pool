/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # The weight `w` of (2.10)

`w(y) = (2π)⁴ y⁵ / 12 · ∑_{ℓ ≥ 1} ℓ⁴ e^{-2πℓy}`, its positivity, the bound
`w(y) ≤ (32 y + 11) e^{-π y}` for `y > 0` (a crude form of (6.11)), and measurability on `(0, ∞)`.
-/

public section

open MeasureTheory Set Filter Topology

namespace Zeta5Irrational

/-- The series `∑_{ℓ ≥ 1} ℓ⁴ e^{-2πℓy}`. -/
@[expose] noncomputable def wS (y : ℝ) : ℝ :=
  ∑' ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y))

/-- The weight `w(y) = (2π)⁴ y⁵ / 12 · ∑_{ℓ ≥ 1} ℓ⁴ e^{-2πℓy}` of (2.10). -/
@[expose] noncomputable def w (y : ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 * y ^ 5 / 12 * wS y

lemma summable_w_term {y : ℝ} (hy : 0 < y) :
    Summable fun ℓ : ℕ => ((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y)) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul 4 (r := 2 * Real.pi * y) (by positivity)
  have h2 := (summable_nat_add_iff 1).mpr h
  refine h2.congr fun ℓ => ?_
  push_cast
  ring_nf

lemma wS_pos {y : ℝ} (hy : 0 < y) : 0 < wS y :=
  (summable_w_term hy).tsum_pos (fun ℓ => by positivity) 0 (by positivity)

lemma w_pos {y : ℝ} (hy : 0 < y) : 0 < w y := by unfold w; have := wS_pos hy; positivity

/-- `1 / (1 - e^{-x}) ≤ 1 + 1 / x` for `x > 0`. -/
lemma one_div_one_sub_exp_neg_le {x : ℝ} (hx : 0 < x) : 1 / (1 - Real.exp (-x)) ≤ 1 + 1 / x := by
  have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h2 : Real.exp (-x) = 1 / Real.exp x := by rw [Real.exp_neg, one_div]
  have h3 : 0 < Real.exp x := Real.exp_pos x
  have h4 : Real.exp (-x) < 1 := by rw [h2, div_lt_one h3]; linarith
  rw [div_le_iff₀ (by linarith), h2]
  have hid : (1 + 1 / x) * (1 - 1 / Real.exp x) = 1 + (Real.exp x - x - 1) / (x * Real.exp x) := by
    field_simp
    ring
  rw [hid]
  have : 0 ≤ (Real.exp x - x - 1) / (x * Real.exp x) := div_nonneg (by linarith) (by positivity)
  linarith

/-- The bound `wS y ≤ 24 (1 + 1/(πy)) e^{-πy} / (πy)⁴`. -/
lemma wS_le {y : ℝ} (hy : 0 < y) :
    wS y ≤ 24 / (Real.pi * y) ^ 4 * (1 + 1 / (Real.pi * y)) * Real.exp (-(Real.pi * y)) := by
  have hpy : 0 < Real.pi * y := by positivity
  set q : ℝ := Real.exp (-(Real.pi * y)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero];
    exact
      Real.exp_lt_exp.mpr
        (by linarith)
          -- termwise bound
  have hterm :
    ∀ ℓ : ℕ,
      ((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y)) ≤
        24 / (Real.pi * y) ^ 4 * (q * q ^ ℓ) := by
    intro ℓ
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) + 1 := by positivity
    have hpow :=
      Real.pow_div_factorial_le_exp (x := Real.pi * y * ((ℓ : ℝ) + 1)) (by positivity) 4
    have hexp :
      Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y)) =
        Real.exp (-(Real.pi * y * ((ℓ : ℝ) + 1))) * (q * q ^ ℓ) :=
      by rw [hq, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [hexp]
    have hE :
      Real.exp (-(Real.pi * y * ((ℓ : ℝ) + 1))) = 1 / Real.exp (Real.pi * y * ((ℓ : ℝ) + 1)) := by
      rw [Real.exp_neg, one_div]
    rw [hE]
    have hEpos : 0 < Real.exp (Real.pi * y * ((ℓ : ℝ) + 1)) := Real.exp_pos _
    have hqq : 0 ≤ q * q ^ ℓ := by positivity
    have key :
      ((ℓ : ℝ) + 1) ^ 4 * (1 / Real.exp (Real.pi * y * ((ℓ : ℝ) + 1))) ≤ 24 / (Real.pi * y) ^ 4 :=
  by
      rw [mul_one_div, div_le_div_iff₀ hEpos (by positivity)]
      have :
        (Real.pi * y * ((ℓ : ℝ) + 1)) ^ 4 / (4 : ℕ).factorial =
          (Real.pi * y) ^ 4 * ((ℓ : ℝ) + 1) ^ 4 / 24 :=
        by rw [Nat.factorial]; norm_num; ring
      rw [this] at hpow
      nlinarith [pow_pos hpy 4]
    calc
      ((ℓ : ℝ) + 1) ^ 4 * (1 / Real.exp (Real.pi * y * ((ℓ : ℝ) + 1)) * (q * q ^ ℓ)) =
          (((ℓ : ℝ) + 1) ^ 4 * (1 / Real.exp (Real.pi * y * ((ℓ : ℝ) + 1)))) * (q * q ^ ℓ) :=
        by ring
      _ ≤ 24 / (Real.pi * y) ^ 4 * (q * q ^ ℓ) := mul_le_mul_of_nonneg_right key hqq
  have hgeom : Summable fun ℓ : ℕ => 24 / (Real.pi * y) ^ 4 * (q * q ^ ℓ) :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left q).mul_left _
  calc
    wS y ≤ ∑' ℓ : ℕ, 24 / (Real.pi * y) ^ 4 * (q * q ^ ℓ) :=
      (summable_w_term hy).tsum_le_tsum hterm hgeom
    _ = 24 / (Real.pi * y) ^ 4 * (q * (1 / (1 - q))) := by
      rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, one_div]
    _ ≤ 24 / (Real.pi * y) ^ 4 * (1 + 1 / (Real.pi * y)) * q := by
      have h := one_div_one_sub_exp_neg_le hpy
      rw [← hq] at h
      have h24 : 0 ≤ 24 / (Real.pi * y) ^ 4 := by positivity
      calc
        24 / (Real.pi * y) ^ 4 * (q * (1 / (1 - q))) ≤
            24 / (Real.pi * y) ^ 4 * (q * (1 + 1 / (Real.pi * y))) :=
          by gcongr
        _ = 24 / (Real.pi * y) ^ 4 * (1 + 1 / (Real.pi * y)) * q := by ring

/-- The bound `w(y) ≤ (32 y + 11) e^{-πy}` for `y > 0`. -/
lemma w_le {y : ℝ} (hy : 0 < y) : w y ≤ (32 * y + 11) * Real.exp (-(Real.pi * y)) := by
  unfold w
  have h := wS_le hy
  have hpi := Real.pi_gt_three
  have hpy : 0 < Real.pi * y := by positivity
  have hc : 0 ≤ (2 * Real.pi) ^ 4 * y ^ 5 / 12 := by positivity
  calc
    (2 * Real.pi) ^ 4 * y ^ 5 / 12 * wS y ≤
        (2 * Real.pi) ^ 4 * y ^ 5 / 12 *
          (24 / (Real.pi * y) ^ 4 * (1 + 1 / (Real.pi * y)) * Real.exp (-(Real.pi * y))) :=
      mul_le_mul_of_nonneg_left h hc
    _ = (32 * y + 32 / Real.pi) * Real.exp (-(Real.pi * y)) := by
      field_simp
      ring
    _ ≤ (32 * y + 11) * Real.exp (-(Real.pi * y)) := by
      have : 32 / Real.pi ≤ 11 := by rw [div_le_iff₀ (by positivity)]; linarith
      have he : 0 ≤ Real.exp (-(Real.pi * y)) := (Real.exp_pos _).le
      nlinarith

/-- `wS` is a.e.-measurable on `(0, ∞)`, as the pointwise limit of continuous partial sums. -/
lemma aemeasurable_wS : AEMeasurable wS (volume.restrict (Ioi 0)) := by
  refine
    aemeasurable_of_tendsto_metrizable_ae' (f := fun n y =>
      ∑ ℓ ∈ Finset.range n, ((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y))) ?_
      ?_
  · intro n
    refine (Continuous.measurable ?_).aemeasurable
    exact
      continuous_finsetSum _ fun ℓ _ =>
        continuous_const.mul (Real.continuous_exp.comp (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    exact (summable_w_term hy).hasSum.tendsto_sum_nat

lemma aemeasurable_w : AEMeasurable w (volume.restrict (Ioi 0)) := by
  unfold w
  exact
    (aemeasurable_const.mul (measurable_id.pow_const 5).aemeasurable |>.div_const 12).mul
      aemeasurable_wS

end Zeta5Irrational
