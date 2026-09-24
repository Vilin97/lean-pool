/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.KappaCapArithmetic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Growth Exponent Arithmetic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

noncomputable section

namespace CKN.Core.Step4

/-- Lower bound `59/25` for the growth exponent when `q > 5/2` and `τ ≥ 25/3`. -/
theorem growth_exponent_lower {q τ : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) :
    59 / 25 ≤ 5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) := by
  set κ := min ((1 / τ + 8 / 25)⁻¹) q
  have hkappa_ge : 25 / 11 ≤ κ := by
    have hbase : min (25 / 11 : ℝ) q = 25 / 11 := min_twentyFive_div_eleven_q hq
    have hle : min (25 / 11 : ℝ) q ≤ min ((1 / τ + 8 / 25)⁻¹) q := min_kappa_base_le hτ
    linarith only [hbase, hle]
  have hτpos : 0 < τ := by
    have hpos : 0 < (25 : ℝ) / 3 := by norm_num
    linarith only [hpos, hτ]
  have hqpos : 0 < q := by linarith only [hq]
  have hkappa_pos : 0 < κ := min_kappa_pos hτpos hqpos
  have hone_div : 1 / κ ≤ 11 / 25 := by
    have hpos_25_11 : 0 < (25 / 11 : ℝ) := by norm_num
    have h := one_div_le_one_div_of_le hpos_25_11 hkappa_ge
    simpa [div_div] using h
  have hdiv : 6 / κ ≤ 66 / 25 := by
    calc
      6 / κ = 6 * (1 / κ) := by ring
      _ ≤ 6 * (11 / 25) := by
        nlinarith only [hone_div]
      _ = 66 / 25 := by norm_num
  have htarget : 5 * (1 - (6 / 5 : ℝ) / κ) = 5 - 6 / κ := by ring
  rw [htarget]
  nlinarith only [hdiv]

/-- Positivity of the growth exponent when `q > 5/2` and `τ ≥ 25/3`. -/
theorem growth_exponent_pos {q τ : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) :
    0 < 5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) := by
  have h := growth_exponent_lower hq hτ
  linarith only [h]

/-- Upper bound `71/25` for the growth exponent when `0 < τ ≤ 25` and `q > 0`. -/
theorem growth_exponent_upper {q τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 25) (hq : 0 < q) :
    5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) ≤ 71 / 25 := by
  set κ := min ((1 / τ + 8 / 25)⁻¹) q
  have hkappa_pos : 0 < κ := min_kappa_pos hτ hq
  have hkappa_le_inv : κ ≤ (1 / τ + 8 / 25)⁻¹ := min_le_left _ _
  have hinv_le_25_9 : (1 / τ + 8 / 25)⁻¹ ≤ 25 / 9 := by
    have hsum : 9 / 25 ≤ 1 / τ + 8 / 25 := by
      have hone_div : 1 / 25 ≤ 1 / τ := one_div_le_one_div_of_le hτ hτ'
      linarith only [hone_div]
    have hpos_sum : 0 < 1 / τ + 8 / 25 := by positivity
    have hpos_9_25 : 0 < (9 : ℝ) / 25 := by norm_num
    have h := ((inv_le_inv₀ hpos_sum hpos_9_25).mpr hsum)
    simpa [div_div] using h
  have hkappa_le : κ ≤ 25 / 9 := le_trans hkappa_le_inv hinv_le_25_9
  have hone_div_ge : 9 / 25 ≤ 1 / κ := by
    have h := one_div_le_one_div_of_le hkappa_pos hkappa_le
    simpa [div_div] using h
  have hdiv : 54 / 25 ≤ 6 / κ := by
    calc
      54 / 25 = 6 * (9 / 25) := by norm_num
      _ ≤ 6 * (1 / κ) := by
        nlinarith only [hone_div_ge]
      _ = 6 / κ := by ring
  have htarget : 5 * (1 - (6 / 5 : ℝ) / κ) = 5 - 6 / κ := by ring
  rw [htarget]
  nlinarith only [hdiv]

/-- Monotonicity of `r ^ (growth exponent)` in the base when the exponent is positive. -/
theorem rpow_growth_exponent_mono {q τ r R : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ)
    (hr : 0 ≤ r) (hrR : r ≤ R) :
    r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) ≤
      R ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) := by
  have hexp_pos : 0 < 5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) :=
    growth_exponent_pos hq hτ
  exact Real.rpow_le_rpow hr hrR hexp_pos.le

end CKN.Core.Step4
