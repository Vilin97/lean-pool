/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Radius exponents for the pressure term of a slice majorant

The pressure-gradient slice estimate of `ss:step3` carries, on a cell of
radius `r` and at doubled spatial radius `ρ = 2 r`, the positive term
`ρ⁻¹/² ‖p(·,s)‖_{L^{3/2}(B_ρ)}`.  Raising it to the power `6/5` and
integrating over the backward window `(t - r², t]` produces a power of `r`
that has to dominate the power `5 - 6/κ` demanded by membership of the
gradient in the parabolic Morrey class `M^{6/5,κ}` of `def:parabolic-morrey`.

This file records the two exponent balances involved, in the normalisation
`5 * (1 - (6/5)/κ) = 5 - 6/κ`:

* the *cell-centred* route, in which the pressure is replaced by the
  cell-mean-subtracted pressure and controlled in a parabolic Morrey class
  `M^{3/2,χ}` on the doubled cell.  Hölder in time and the Morrey growth then
  give the radius power `19/5 - 6/χ`, so the route closes exactly when
  `1/χ ≤ 1/κ - 1/5`.  The gradient exponent in
  `eq:pressure-gradient-morrey` lies between `25/11` and `25/9`; the
  required pressure exponent ranges from `25/6` to `25/4` at those endpoints.
  Thus `χ ≥ 25/4` suffices uniformly over the admissible range.
* the *fixed-scale* route, in which the pressure enters only through a
  majorant that is bounded in space on a fixed carrier and lies in `L^{3/2}`
  in time, as for the fixed-carrier remainder in the proof of
  `lem:pressure-gradient-morrey`.  The spatial
  measure of the cell then contributes and the radius power is `17/5`, which
  dominates the requirement for every admissible `κ` with room to spare.
-/

public section

open scoped ENNReal

noncomputable section

namespace CKN.Core.Step4

/-- The Morrey growth power in the normalisation used by the cell clauses. -/
theorem five_mul_one_sub_six_fifths_div {κ : ℝ} (hκ : κ ≠ 0) :
    5 * (1 - (6 / 5 : ℝ) / κ) = 5 - 6 / κ := by
  field_simp

/-- The cell-centred balance: the radius power produced by a pressure Morrey
exponent `χ` dominates the power required by the gradient Morrey exponent `κ`
exactly when `1/χ ≤ 1/κ - 1/5`. -/
theorem cellCentred_pressure_exponent_le_iff (χ κ : ℝ) :
    5 - 6 / κ ≤ 19 / 5 - 6 / χ ↔ 1 / χ ≤ 1 / κ - 1 / 5 := by
  rw [div_eq_mul_inv (6 : ℝ) κ, div_eq_mul_inv (6 : ℝ) χ, one_div, one_div]
  constructor
  · intro h
    linarith only [h]
  · intro h
    linarith only [h]

/-- At the smallest admissible gradient Morrey exponent the cell-centred route
needs pressure Morrey exponent exactly `25/6`; both sides equal `59/25`. -/
theorem cellCentred_pressure_exponent_at_min_kappa :
    (19 : ℝ) / 5 - 6 / (25 / 6) = 5 - 6 / (25 / 11) := by
  norm_num

/-- At the largest admissible gradient Morrey exponent the cell-centred route
needs pressure Morrey exponent exactly `25/4`; both sides equal `71/25`. -/
theorem cellCentred_pressure_exponent_at_max_kappa :
    (19 : ℝ) / 5 - 6 / (25 / 4) = 5 - 6 / (25 / 9) := by
  norm_num

/-- The gradient Morrey exponent of `thm:endgame` never exceeds `25/9`. -/
theorem endgame_kappa_le {τ q : ℝ} (hτ : 0 < τ) (hτ25 : τ ≤ 25) :
    min ((1 / τ + 8 / 25)⁻¹) q ≤ 25 / 9 := by
  have hinv : (1 : ℝ) / 25 ≤ 1 / τ := one_div_le_one_div_of_le hτ hτ25
  have hge : (9 : ℝ) / 25 ≤ 1 / τ + 8 / 25 := by linarith only [hinv]
  have hle : (1 / τ + 8 / 25)⁻¹ ≤ 25 / 9 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9 / 25) hge
    calc (1 / τ + 8 / 25)⁻¹ = 1 / (1 / τ + 8 / 25) := (one_div _).symm
      _ ≤ 1 / (9 / 25) := h
      _ = 25 / 9 := by norm_num
  exact le_trans (min_le_left _ _) hle

/-- The gradient Morrey exponent of `thm:endgame` is never below `25/11`. -/
theorem endgame_kappa_ge {τ q : ℝ} (hτ : 25 / 3 ≤ τ) (hq : 5 / 2 < q) :
    25 / 11 ≤ min ((1 / τ + 8 / 25)⁻¹) q := by
  have hτpos : (0 : ℝ) < τ := by linarith only [hτ]
  have hinv : (1 : ℝ) / τ ≤ 1 / (25 / 3) :=
    one_div_le_one_div_of_le (by norm_num) hτ
  have hle : (1 : ℝ) / τ + 8 / 25 ≤ 11 / 25 := by
    have : (1 : ℝ) / (25 / 3) = 3 / 25 := by norm_num
    rw [this] at hinv
    linarith only [hinv]
  have hpos : (0 : ℝ) < 1 / τ + 8 / 25 := by positivity
  have hfirst : (25 : ℝ) / 11 ≤ (1 / τ + 8 / 25)⁻¹ := by
    have h := one_div_le_one_div_of_le hpos hle
    calc (25 : ℝ) / 11 = 1 / (11 / 25) := by norm_num
      _ ≤ 1 / (1 / τ + 8 / 25) := h
      _ = (1 / τ + 8 / 25)⁻¹ := one_div _
  exact le_min hfirst (by linarith only [hq])

/-- Pressure Morrey exponent `25/4` closes the cell-centred balance for every
gradient Morrey exponent admissible in `thm:endgame`. -/
theorem cellCentred_pressure_exponent_quarter_suffices {κ : ℝ}
    (hκ : 0 < κ) (hκle : κ ≤ 25 / 9) :
    5 - 6 / κ ≤ 19 / 5 - 6 / (25 / 4 : ℝ) := by
  have h : (6 : ℝ) / (25 / 9) ≤ 6 / κ := by
    apply div_le_div_of_nonneg_left (by norm_num) hκ hκle
  have hval : (19 : ℝ) / 5 - 6 / (25 / 4) = 5 - 6 / (25 / 9) := by norm_num
  rw [hval]
  linarith only [h]

/-- The pressure Morrey exponent available from the decay estimate, `25/8`,
does **not** close the cell-centred balance for any admissible gradient Morrey
exponent: the produced radius power `47/25` stays strictly below the required
one, which is at least `59/25`. -/
theorem cellCentred_pressure_exponent_deficit {κ : ℝ}
    (hκ : 25 / 11 ≤ κ) :
    19 / 5 - 6 / (25 / 8 : ℝ) < 5 - 6 / κ := by
  have h : (6 : ℝ) / κ ≤ 6 / (25 / 11) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hκ
  have hval : (19 : ℝ) / 5 - 6 / (25 / 8) = 47 / 25 := by norm_num
  have hval2 : (6 : ℝ) / (25 / 11) = 66 / 25 := by norm_num
  rw [hval2] at h
  rw [hval]
  linarith only [h]

/-- The fixed-scale balance: the radius power `17/5` produced by a spatially
bounded, `L^{3/2}`-in-time pressure majorant dominates the requirement for
every admissible gradient Morrey exponent, with the strict margin `14/25`
already at the top of the range. -/
theorem fixedScale_pressure_exponent_suffices {κ : ℝ} (hκ : κ ≤ 25 / 9)
    (hκpos : 0 < κ) :
    5 - 6 / κ ≤ 17 / 5 := by
  have h : (6 : ℝ) / (25 / 9) ≤ 6 / κ :=
    div_le_div_of_nonneg_left (by norm_num) hκpos hκ
  have hval : (6 : ℝ) / (25 / 9) = 54 / 25 := by norm_num
  rw [hval] at h
  linarith only [h]

end CKN.Core.Step4
