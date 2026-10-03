/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMorrey

/-!
# The scale cost of measuring the one-sided constant at the margin

The one-sided transfer constant `oneSidedMorreyBound` is built from a
small-cell bound and a whole-carrier integral bound. This file isolates
the exact cost of measuring the meeting point of the two regimes at the
margin scale `ρ₀` rather than at the carrier radius `ρ₁`: the small-cell
constant `A` is untouched, while the whole-carrier constant `B` carries
the explicit scale ratio `(ρ₁ / ρ₀) ^ (5 * (1 - P / τ))`. The second
statement is the form in which a comparison against an explicit majorant
stated at the carrier radius is transported down to the margin scale.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame


noncomputable section

namespace CKN.Core.Step4

/-- Measuring the one-sided transfer constant at a smaller scale `ρ₀` is
exactly the same as measuring it at `ρ₁` with the whole-carrier constant `B`
inflated by the explicit ratio `(ρ₁ / ρ₀) ^ (5 * (1 - P / τ))`; the small-cell
constant is untouched. -/
theorem oneSidedMorreyBound_scale_eq
    {P τ ρ₀ ρ₁ : ℝ} {A B : ℝ≥0∞} (hP : 0 < P) (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) :
    oneSidedMorreyBound P τ ρ₀ A B =
      oneSidedMorreyBound P τ ρ₁ A
        (B * ENNReal.ofReal ((ρ₁ / ρ₀) ^ (5 * (1 - P / τ)))) := by
  unfold oneSidedMorreyBound
  set θ : ℝ := 5 * (1 - P / τ)
  have hb : (0 : ℝ) < ρ₁ / ρ₀ := div_pos hρ₁ hρ₀
  have hθpos : (0 : ℝ) < (ρ₁ / ρ₀) ^ θ := Real.rpow_pos_of_pos hb θ
  have ha : (0 : ℝ) < (ρ₁ / 2) ^ (-(θ / P)) := Real.rpow_pos_of_pos (by positivity) _
  have hb2 : (0 : ℝ) < (ρ₁ / ρ₀) ^ (θ / P) := Real.rpow_pos_of_pos hb _
  have hreal : (ρ₁ / 2) ^ (-(θ / P)) * (ρ₁ / ρ₀) ^ (θ / P) = (ρ₀ / 2) ^ (-(θ / P)) := by
    have hfirst : (ρ₁ / 2) ^ (-(θ / P)) = (2 / ρ₁) ^ (θ / P) := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ ρ₁ / 2),
        ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ ρ₁ / 2), inv_div]
    have hlast : (ρ₀ / 2) ^ (-(θ / P)) = (2 / ρ₀) ^ (θ / P) := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ ρ₀ / 2),
        ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ ρ₀ / 2), inv_div]
    have hbase : (2 / ρ₁) * (ρ₁ / ρ₀) = 2 / ρ₀ := by
      field_simp
    rw [hfirst, hlast, ← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 / ρ₁)
      (by positivity : (0 : ℝ) ≤ ρ₁ / ρ₀), hbase]
  have hstep : ENNReal.ofReal ((ρ₁ / 2) ^ (-(θ / P))) *
      (B * ENNReal.ofReal ((ρ₁ / ρ₀) ^ θ)) ^ (1 / P : ℝ) =
      ENNReal.ofReal ((ρ₁ / 2) ^ (-(θ / P))) *
        (B ^ (1 / P : ℝ) * ENNReal.ofReal ((ρ₁ / ρ₀) ^ (θ / P))) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hP.le),
      ENNReal.ofReal_rpow_of_pos hθpos, ← Real.rpow_mul hb.le θ (1 / P), mul_one_div]
  have hsecond : ENNReal.ofReal ((ρ₀ / 2) ^ (-(θ / P))) * B ^ (1 / P : ℝ) =
      ENNReal.ofReal ((ρ₁ / 2) ^ (-(θ / P))) *
        (B * ENNReal.ofReal ((ρ₁ / ρ₀) ^ θ)) ^ (1 / P : ℝ) := by
    rw [hstep]
    symm
    calc ENNReal.ofReal ((ρ₁ / 2) ^ (-(θ / P))) *
          (B ^ (1 / P : ℝ) * ENNReal.ofReal ((ρ₁ / ρ₀) ^ (θ / P)))
        = (ENNReal.ofReal ((ρ₁ / 2) ^ (-(θ / P))) *
            ENNReal.ofReal ((ρ₁ / ρ₀) ^ (θ / P))) * B ^ (1 / P : ℝ) := by
          ac_rfl
      _ = ENNReal.ofReal ((ρ₁ / 2) ^ (-(θ / P)) * (ρ₁ / ρ₀) ^ (θ / P)) *
            B ^ (1 / P : ℝ) := by
          rw [← ENNReal.ofReal_mul ha.le]
      _ = ENNReal.ofReal ((ρ₀ / 2) ^ (-(θ / P))) * B ^ (1 / P : ℝ) := by rw [hreal]
  rw [hsecond]

/-- Transport to the margin scale of a comparison against an explicit
majorant stated at the carrier radius: a bound on the constant measured at
`ρ₁` with the inflated whole-carrier constant also bounds the constant
measured at `ρ₀`. -/
theorem oneSidedMorreyBound_margin_le_of_scaled
    {P τ ρ₀ ρ₁ : ℝ} {A B K : ℝ≥0∞} (hP : 0 < P) (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁)
    (h : oneSidedMorreyBound P τ ρ₁ A
        (B * ENNReal.ofReal ((ρ₁ / ρ₀) ^ (5 * (1 - P / τ)))) ≤ K) :
    oneSidedMorreyBound P τ ρ₀ A B ≤ K := by
  rw [oneSidedMorreyBound_scale_eq hP hρ₀ hρ₁]
  exact h

end CKN.Core.Step4
