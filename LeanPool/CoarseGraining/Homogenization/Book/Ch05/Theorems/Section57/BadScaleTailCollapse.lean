/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailJoint

/-! # Bad Scale Tail Collapse -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Collapse of synchronized bad-scale components to one tail

This file contains the deterministic final step after the three bad-scale
components have been estimated with synchronized constants.  The probabilistic
input is the selected-denominator component theorem from `BadScaleTailJoint`;
the remaining hypotheses are purely large-scale/prefactor inequalities.
-/

noncomputable section

theorem three_exp_terms_le_exp_of_prefactor_gap
    {c₁ c₂ c₃ A Ac T₀ T : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hA : T₀ ≤ A) (hAc : T₀ ≤ Ac)
    (hpref : c₁ + c₂ + c₃ ≤ Real.exp (T₀ - T)) :
    c₁ * Real.exp (-A) + c₂ * Real.exp (-A) + c₃ * Real.exp (-Ac) ≤
      Real.exp (-T) := by
  have hEA : Real.exp (-A) ≤ Real.exp (-T₀) :=
    Real.exp_le_exp.mpr (by linarith)
  have hEAc : Real.exp (-Ac) ≤ Real.exp (-T₀) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsum :
      c₁ * Real.exp (-A) + c₂ * Real.exp (-A) + c₃ * Real.exp (-Ac) ≤
        (c₁ + c₂ + c₃) * Real.exp (-T₀) := by
    calc
      c₁ * Real.exp (-A) + c₂ * Real.exp (-A) + c₃ * Real.exp (-Ac)
          ≤ c₁ * Real.exp (-T₀) + c₂ * Real.exp (-T₀) +
              c₃ * Real.exp (-T₀) := by
            nlinarith [mul_le_mul_of_nonneg_left hEA hc₁,
              mul_le_mul_of_nonneg_left hEA hc₂,
              mul_le_mul_of_nonneg_left hEAc hc₃]
      _ = (c₁ + c₂ + c₃) * Real.exp (-T₀) := by ring
  calc
    c₁ * Real.exp (-A) + c₂ * Real.exp (-A) + c₃ * Real.exp (-Ac)
        ≤ (c₁ + c₂ + c₃) * Real.exp (-T₀) := hsum
    _ ≤ Real.exp (T₀ - T) * Real.exp (-T₀) :=
        mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ = Real.exp (-T) := by
        rw [← Real.exp_add]
        congr 1
        ring

theorem rpow_three_sub_div_eq_div_mul_rpow
    {x O Den : ℝ} (hDen : Den ≠ 0) :
    ((3 : ℝ) ^ (x - O)) / Den =
      (3 : ℝ) ^ x / (Den * (3 : ℝ) ^ O) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h3O : (3 : ℝ) ^ O ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h3 O)
  rw [Real.rpow_sub h3]
  field_simp [hDen, h3O]

theorem rpow_div_le_rpow_div_of_den_le
    {x D₁ D₂ η : ℝ}
    (hx : 0 ≤ x) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hD : D₁ ≤ D₂) (hη : 0 < η) :
    (x / D₂) ^ η ≤ (x / D₁) ^ η := by
  have hfrac₁_nonneg : 0 ≤ x / D₁ := div_nonneg hx hD₁.le
  have hfrac_le : x / D₂ ≤ x / D₁ :=
    div_le_div_of_nonneg_left hx hD₁ hD
  exact Real.rpow_le_rpow (div_nonneg hx hD₂.le) hfrac_le hη.le

theorem selected_tail_parameter_power_le_high
    {q : ℕ} {Den B η O : ℝ}
    (hDen : 0 < Den) (hB : 0 < B) (hη : 0 < η)
    (hden : Den * (3 : ℝ) ^ O ≤ B) :
    (((3 : ℝ) ^ (q : ℝ) / B) ^ η) ≤
      ((((3 : ℝ) ^ ((q : ℝ) - O)) / Den) ^ η) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hdenO_pos : 0 < Den * (3 : ℝ) ^ O :=
    mul_pos hDen (Real.rpow_pos_of_pos h3 O)
  have hpow_nonneg : 0 ≤ (3 : ℝ) ^ (q : ℝ) :=
    (Real.rpow_pos_of_pos h3 _).le
  calc
    (((3 : ℝ) ^ (q : ℝ) / B) ^ η)
        ≤ (((3 : ℝ) ^ (q : ℝ) / (Den * (3 : ℝ) ^ O)) ^ η) :=
          rpow_div_le_rpow_div_of_den_le hpow_nonneg hdenO_pos hB hden hη
    _ = ((((3 : ℝ) ^ ((q : ℝ) - O)) / Den) ^ η) := by
          rw [rpow_three_sub_div_eq_div_mul_rpow hDen.ne']

/-- Deterministic component collapse in the exact algebraic shape produced by
the synchronized selected-denominator estimate. -/
theorem measureReal_badScaleEvent_le_exp_tail_of_component_prefactor_gap
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {t α : ℝ} {q : ℕ}
    {Ctop ChighBottom CcrudeBottom A Acrude Alead Atail η : ℝ}
    (hcomponent :
      μ.real (badScaleEvent H t α q) ≤
        Ctop * Real.exp (-(A ^ η)) +
          ChighBottom * Real.exp (-(A ^ η)) +
          CcrudeBottom * Real.exp (-(Acrude ^ η)))
    (hAlead_A : Alead ≤ A ^ η)
    (hAlead_Acrude : Alead ≤ Acrude ^ η)
    (hpref :
      max 0 Ctop + max 0 ChighBottom + max 0 CcrudeBottom ≤
        Real.exp (Alead - Atail)) :
    μ.real (badScaleEvent H t α q) ≤ Real.exp (-Atail) := by
  have hcomponent_max :
      μ.real (badScaleEvent H t α q) ≤
        max 0 Ctop * Real.exp (-(A ^ η)) +
          max 0 ChighBottom * Real.exp (-(A ^ η)) +
          max 0 CcrudeBottom * Real.exp (-(Acrude ^ η)) := by
    have htop :
        Ctop * Real.exp (-(A ^ η)) ≤
          max 0 Ctop * Real.exp (-(A ^ η)) :=
      mul_le_mul_of_nonneg_right (le_max_right 0 Ctop) (Real.exp_pos _).le
    have hhigh :
        ChighBottom * Real.exp (-(A ^ η)) ≤
          max 0 ChighBottom * Real.exp (-(A ^ η)) :=
      mul_le_mul_of_nonneg_right
        (le_max_right 0 ChighBottom) (Real.exp_pos _).le
    have hcrude :
        CcrudeBottom * Real.exp (-(Acrude ^ η)) ≤
          max 0 CcrudeBottom * Real.exp (-(Acrude ^ η)) :=
      mul_le_mul_of_nonneg_right
        (le_max_right 0 CcrudeBottom) (Real.exp_pos _).le
    linarith
  exact hcomponent_max.trans
    (three_exp_terms_le_exp_of_prefactor_gap
      (c₁ := max 0 Ctop) (c₂ := max 0 ChighBottom)
      (c₃ := max 0 CcrudeBottom)
      (A := A ^ η) (Ac := Acrude ^ η) (T₀ := Alead) (T := Atail)
      (le_max_left 0 Ctop) (le_max_left 0 ChighBottom)
      (le_max_left 0 CcrudeBottom)
      hAlead_A hAlead_Acrude hpref)

/-- Same deterministic collapse, with the component sum written in the
selected-denominator theorem's native factorization. -/
theorem measureReal_badScaleEvent_le_exp_tail_of_selected_component_sum
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {t α : ℝ} {q : ℕ}
    {S qPlus Cbottom wq Ktop Kbottom Kcrude A Acrude Alead Atail η : ℝ}
    (hcomponent :
      μ.real (badScaleEvent H t α q) ≤
        S * (Real.exp (-(A ^ η)) * Ktop) +
          qPlus * (Cbottom * wq) *
            (Real.exp (-(A ^ η)) * Kbottom) +
          qPlus * (S * wq) *
            (Real.exp (-(Acrude ^ η)) * Kcrude))
    (hAlead_A : Alead ≤ A ^ η)
    (hAlead_Acrude : Alead ≤ Acrude ^ η)
    (hpref :
      max 0 (S * Ktop) +
          max 0 (qPlus * (Cbottom * wq) * Kbottom) +
          max 0 (qPlus * (S * wq) * Kcrude) ≤
        Real.exp (Alead - Atail)) :
    μ.real (badScaleEvent H t α q) ≤ Real.exp (-Atail) := by
  have hcomponent_coeff :
      μ.real (badScaleEvent H t α q) ≤
        (S * Ktop) * Real.exp (-(A ^ η)) +
          (qPlus * (Cbottom * wq) * Kbottom) * Real.exp (-(A ^ η)) +
          (qPlus * (S * wq) * Kcrude) * Real.exp (-(Acrude ^ η)) := by
    calc
      μ.real (badScaleEvent H t α q)
          ≤ S * (Real.exp (-(A ^ η)) * Ktop) +
              qPlus * (Cbottom * wq) *
                (Real.exp (-(A ^ η)) * Kbottom) +
              qPlus * (S * wq) *
                (Real.exp (-(Acrude ^ η)) * Kcrude) := hcomponent
      _ =
        (S * Ktop) * Real.exp (-(A ^ η)) +
          (qPlus * (Cbottom * wq) * Kbottom) * Real.exp (-(A ^ η)) +
          (qPlus * (S * wq) * Kcrude) * Real.exp (-(Acrude ^ η)) := by
          ring
  exact
    measureReal_badScaleEvent_le_exp_tail_of_component_prefactor_gap
      (hcomponent := hcomponent_coeff)
      hAlead_A hAlead_Acrude hpref

end

end Section57
end Ch05
end Book
end Homogenization
