/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Covering
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RpowSquares

/-!
# Pressure Decay

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Core.Step3

open CKN




/-- Take square roots in the three-group pressure estimate, with the constants
used by `eq:pressure-decay`. -/
theorem pressureDecay_algebra
    {κ C₁₂ C₁₃ α β δ lam δr : ℝ}
    (hκ : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hC₁₂ : 0 ≤ C₁₂) (hC₁₃ : 0 ≤ C₁₃)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (hlam : 0 ≤ lam) (_ : 0 ≤ δr)
    (hsq : δr ^ 2 ≤
      C₁₂ * κ⁻¹ * α * β + C₁₂ * κ * α * β +
        C₁₂ * κ ^ (2 / 3 : ℝ) * δ ^ 2 + C₁₃ * κ * lam) :
    δr ≤ Real.sqrt (2 * C₁₂) * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β +
      Real.sqrt (2 * C₁₂) * κ ^ (1 / 3 : ℝ) * δ +
      Real.sqrt C₁₃ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam := by
  let A : ℝ := Real.sqrt (2 * C₁₂) * κ ^ (-1 / 2 : ℝ) *
    Real.sqrt α * Real.sqrt β
  let B : ℝ := Real.sqrt (2 * C₁₂) * κ ^ (1 / 3 : ℝ) * δ
  let D : ℝ := Real.sqrt C₁₃ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hA_sq : A ^ 2 = 2 * C₁₂ * κ⁻¹ * α * β := by
    dsimp [A]
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
      CKN.Foundation.Euclidean.rpow_neg_half_sq hκ, Real.sq_sqrt hα, Real.sq_sqrt hβ,
      Real.rpow_neg_one]
  have hB_sq : B ^ 2 = 2 * C₁₂ * κ ^ (2 / 3 : ℝ) * δ ^ 2 := by
    dsimp [B]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), CKN.Foundation.Euclidean.rpow_third_sq hκ]
  have hD_sq : D ^ 2 = C₁₃ * κ * lam := by
    dsimp [D]
    rw [mul_pow, mul_pow, Real.sq_sqrt hC₁₃, CKN.Foundation.Euclidean.rpow_half_sq hκ,
      Real.sq_sqrt hlam]
  have hκone : κ ≤ 1 := by linarith only [hκhalf]
  have hκinv : κ ≤ κ⁻¹ := by
    rw [← Real.rpow_neg_one κ]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hκ hκone
        (by norm_num : (-1 : ℝ) ≤ 1))
  have hgroup : C₁₂ * κ * α * β ≤ C₁₂ * κ⁻¹ * α * β := by
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hκinv hC₁₂) (mul_nonneg hα hβ)
    nlinarith only [hmul]
  have hsum : δr ^ 2 ≤ A ^ 2 + B ^ 2 + D ^ 2 := by
    calc
      δr ^ 2 ≤ C₁₂ * κ⁻¹ * α * β + C₁₂ * κ * α * β +
          C₁₂ * κ ^ (2 / 3 : ℝ) * δ ^ 2 + C₁₃ * κ * lam := hsq
      _ ≤ 2 * C₁₂ * κ⁻¹ * α * β + C₁₂ * κ ^ (2 / 3 : ℝ) * δ ^ 2 +
          C₁₃ * κ * lam := by nlinarith only [hgroup]
      _ ≤ A ^ 2 + B ^ 2 + D ^ 2 := by
        rw [hA_sq, hB_sq, hD_sq]
        have hterm : 0 ≤ C₁₂ * κ ^ (2 / 3 : ℝ) * δ ^ 2 := by positivity
        nlinarith only [hterm]
  have hAB : 0 ≤ 2 * A * B := by positivity
  have hAD : 0 ≤ 2 * A * D := by positivity
  have hBD : 0 ≤ 2 * B * D := by positivity
  have hsum_sq : δr ^ 2 ≤ (A + B + D) ^ 2 := by
    nlinarith only [hsum, hAB, hAD, hBD]
  have hright : 0 ≤ A + B + D := by positivity
  have hroot : δr ≤ A + B + D := by
    nlinarith only [hsum_sq, hright]
  simpa only [A, B, D] using hroot

/-! The source-level bridge keeps the two external pressure inputs visible as
the names used in the paper.  The annular shares are supplied through the
conditional cylinder assemblers until their unconditional replacements land. -/


end CKN.Core.Step3
