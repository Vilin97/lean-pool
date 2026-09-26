/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedMarginCost
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseBudget

/-!
# Pressure Gradient Origin Budget Sufficient

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-!
# Sufficient origin-carrier budget conditions

The first result transports an explicit inflated whole-carrier budget to the
margin-scale one-sided constant. The second is the independent scalar bound
on the exponent appearing in that inflation factor.
-/

/-- The two displayed budget inequalities suffice to bound the one-sided
Morrey constant measured at the origin-carrier margin scale by the specialized
pressure-gradient constant. -/
theorem margin_clause_of_inflated_budget
    {q τ C_CZ R₀ R₁ ε : ℝ} {KU KD A B : ℝ≥0∞}
    (hR₁ : 0 < R₁) (hR₁34 : R₁ < 3 / 4)
    (hA : A ≤ 3 * (3 * KU * KD + forceSourceMorreyBound q ε))
    (hB : B * ENNReal.ofReal
        ((R₁ / ((1 - R₁) / 4)) ^
          (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) ≤
      ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) :
    oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q) ((1 - R₁) / 4) A B ≤
      oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD := by
  have hmargin : (0 : ℝ) < (1 - R₁) / 4 := by linarith only [hR₁34]
  rw [oneSidedMorreyBound_scale_eq (P := 6 / 5)
    (τ := min ((1 / τ + 8 / 25)⁻¹) q) (ρ₀ := (1 - R₁) / 4) (ρ₁ := R₁)
    (A := A) (B := B) (by norm_num) hmargin hR₁]
  exact oneSidedMorreyBound_le_pressureGradientKP hA hB

/-- Under the admissible ranges for `q` and `τ`, the exponent in the
origin-carrier budget inflation lies between `59 / 25` and `71 / 25`. -/
theorem growth_exponent_range {q τ : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ)
    (hτ' : τ ≤ 25) :
    59 / 25 ≤ 5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) ∧
      5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) ≤ 71 / 25 := by
  have hτpos : (0 : ℝ) < τ := by linarith only [hτ]
  have hsum : (0 : ℝ) < 1 / τ + 8 / 25 := by positivity
  have hlow : (25 : ℝ) / 11 ≤ (1 / τ + 8 / 25)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hsum]
    have h1 : 1 / τ ≤ 3 / 25 := by
      rw [div_le_div_iff₀ hτpos (by norm_num)]
      linarith only [hτ]
    linarith only [h1]
  have hhigh : ((1 / τ + 8 / 25)⁻¹ : ℝ) ≤ 25 / 9 := by
    rw [inv_le_comm₀ hsum (by norm_num)]
    have h1 : (1 : ℝ) / 25 ≤ 1 / τ := by
      rw [div_le_div_iff₀ (by norm_num) hτpos]
      linarith only [hτ']
    linarith only [h1]
  have hkl : (25 : ℝ) / 11 ≤ min ((1 / τ + 8 / 25)⁻¹) q :=
    le_min hlow (by linarith only [hq])
  have hkh : min ((1 / τ + 8 / 25)⁻¹) q ≤ (25 : ℝ) / 9 :=
    le_trans (min_le_left _ _) hhigh
  have hkpos : (0 : ℝ) < min ((1 / τ + 8 / 25)⁻¹) q := by linarith only [hkl]
  constructor
  · have hdiv : (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q ≤ 66 / 125 := by
      rw [div_le_div_iff₀ hkpos (by norm_num)]
      linarith only [hkl]
    linarith only [hdiv]
  · have hdiv : (54 : ℝ) / 125 ≤ (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q := by
      rw [div_le_div_iff₀ (by norm_num) hkpos]
      linarith only [hkh]
    linarith only [hdiv]

end CKN.Core.Step4
