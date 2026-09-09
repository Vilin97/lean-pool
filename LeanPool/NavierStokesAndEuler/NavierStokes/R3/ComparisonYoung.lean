/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity.Finset

/-!
# Scalar absorption for the whole-space comparison estimate

The constants in these estimates are uniform in the cutoff radius and in the
nonnegative quantity that will represent a weighted gradient norm. All
fractional powers have real exponents.
-/

@[expose] public section



noncomputable section

open Filter

namespace NavierStokesR3.ComparisonYoung

/-- Every nonnegative subquadratic power can be absorbed into an arbitrarily
small multiple of the square, with a constant independent of the argument. -/
theorem exists_rpow_absorption {C δ p : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hp0 : 0 ≤ p) (hp2 : p < 2) :
    ∃ D ≥ 0, ∀ A ≥ 0, C * A ^ p ≤ δ * A ^ 2 + D := by
  have hevent : ∀ᶠ A : ℝ in atTop, C / δ ≤ A ^ (2 - p) :=
    (tendsto_rpow_atTop (by linarith : 0 < 2 - p)).eventually
      (eventually_ge_atTop (C / δ))
  obtain ⟨b, hb⟩ := eventually_atTop.mp hevent
  let K : ℝ := max 1 b
  have hK : 0 ≤ K := le_trans zero_le_one (le_max_left _ _)
  have hD : 0 ≤ C * K ^ p := mul_nonneg hC (Real.rpow_nonneg hK _)
  refine ⟨C * K ^ p, hD, ?_⟩
  intro A hA
  by_cases hAK : A ≤ K
  · calc
      C * A ^ p ≤ C * K ^ p :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hA hAK hp0) hC
      _ ≤ δ * A ^ 2 + C * K ^ p :=
        le_add_of_nonneg_left (mul_nonneg hδ.le (sq_nonneg A))
  · have hKA : K ≤ A := le_of_lt (lt_of_not_ge hAK)
    have hApos : 0 < A := lt_of_lt_of_le zero_lt_one
      ((le_max_left 1 b).trans hKA)
    have hlarge : C ≤ A ^ (2 - p) * δ :=
      (div_le_iff₀ hδ).mp (hb A ((le_max_right 1 b).trans hKA))
    have hpow : A ^ (2 - p) * A ^ p = A ^ 2 := by
      rw [← Real.rpow_add hApos]
      norm_num
    calc
      C * A ^ p ≤ (A ^ (2 - p) * δ) * A ^ p :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hA _)
      _ = δ * (A ^ (2 - p) * A ^ p) := by ring
      _ = δ * A ^ 2 := by rw [hpow]
      _ ≤ δ * A ^ 2 + C * K ^ p := le_add_of_nonneg_right hD

/-- The same absorption estimate is uniform for a fixed unit shift. -/
theorem exists_shifted_rpow_absorption {C δ p : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hp0 : 0 ≤ p) (hp2 : p < 2) :
    ∃ D ≥ 0, ∀ A ≥ 0, C * (A + 1) ^ p ≤ δ * A ^ 2 + D := by
  obtain ⟨D, hD, hbound⟩ := exists_rpow_absorption hC (half_pos hδ) hp0 hp2
  refine ⟨D + δ, add_nonneg hD hδ.le, ?_⟩
  intro A hA
  have hboundA := hbound (A + 1) (by linarith)
  have hsquare : (A + 1) ^ 2 ≤ 2 * A ^ 2 + 2 := by
    nlinarith [sq_nonneg (A - 1)]
  have hscaled := mul_le_mul_of_nonneg_left hsquare (half_pos hδ).le
  nlinarith

/-- Dividing the shifted estimate by a radius at least one preserves the
arbitrarily small square coefficient and makes the constant decay as `1 / R`. -/
theorem exists_scaled_shifted_rpow_absorption {C δ p : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hp0 : 0 ≤ p) (hp2 : p < 2) :
    ∃ D ≥ 0, ∀ A ≥ 0, ∀ R ≥ 1,
      C / R * (A + 1) ^ p ≤ δ * A ^ 2 + D / R := by
  obtain ⟨D, hD, hbound⟩ := exists_shifted_rpow_absorption hC hδ hp0 hp2
  refine ⟨D, hD, ?_⟩
  intro A hA R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hInv : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  have hInv1 : R⁻¹ ≤ 1 := (inv_le_one₀ hRpos).mpr hR
  have hscaled := mul_le_mul_of_nonneg_right (hbound A hA) hInv
  have hquadratic := mul_le_mul_of_nonneg_left hInv1
    (mul_nonneg hδ.le (sq_nonneg A))
  simp only [div_eq_mul_inv]
  nlinarith

/-- The pressure and transport cutoff remainders are controlled by one shifted
subquadratic power. The estimate retains the full factor `1 / R`. -/
theorem cutoff_expression_le {C A R : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hR : 1 ≤ R) :
    C * ((A + R⁻¹) ^ (1 / 2 : ℝ) + 1) *
        (R⁻¹ * A + R ^ (-2 : ℝ)) +
      C * R ^ (-7 / 4 : ℝ) * (A + R⁻¹) ^ (3 / 4 : ℝ) +
      C * R⁻¹ * (A + R⁻¹) ^ (3 / 2 : ℝ) ≤
        4 * C / R * (A + 1) ^ (3 / 2 : ℝ) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hInv : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  have hInv1 : R⁻¹ ≤ 1 := (inv_le_one₀ hRpos).mpr hR
  have hx : 0 ≤ A + R⁻¹ := add_nonneg hA hInv
  have hxB : A + R⁻¹ ≤ A + 1 := add_le_add_right hInv1 A
  have hB1 : 1 ≤ A + 1 := by linarith
  have hBpos : 0 < A + 1 := by linarith
  have hR2 : R ^ (-2 : ℝ) ≤ R⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (-2 : ℝ) ≤ -1))
  have hR74 : R ^ (-7 / 4 : ℝ) ≤ R⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (-7 / 4 : ℝ) ≤ -1))
  have hhalf : (A + R⁻¹) ^ (1 / 2 : ℝ) + 1 ≤
      2 * (A + 1) ^ (1 / 2 : ℝ) := by
    have hmon := Real.rpow_le_rpow hx hxB (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hone := Real.one_le_rpow hB1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hlinear : R⁻¹ * A + R ^ (-2 : ℝ) ≤ R⁻¹ * (A + 1) := by
    nlinarith
  have hlinear0 : 0 ≤ R⁻¹ * A + R ^ (-2 : ℝ) :=
    add_nonneg (mul_nonneg hInv hA) (Real.rpow_nonneg hRpos.le _)
  have hprod : (A + 1) ^ (1 / 2 : ℝ) * (A + 1) =
      (A + 1) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hBpos.ne']
    norm_num
  have hfactor : ((A + R⁻¹) ^ (1 / 2 : ℝ) + 1) *
      (R⁻¹ * A + R ^ (-2 : ℝ)) ≤ 2 * R⁻¹ * (A + 1) ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ (2 * (A + 1) ^ (1 / 2 : ℝ)) * (R⁻¹ * (A + 1)) :=
        mul_le_mul hhalf hlinear hlinear0
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hBpos.le _))
      _ = 2 * R⁻¹ * ((A + 1) ^ (1 / 2 : ℝ) * (A + 1)) := by ring
      _ = _ := by rw [hprod]
  have hthreeQuarters : (A + R⁻¹) ^ (3 / 4 : ℝ) ≤
      (A + 1) ^ (3 / 2 : ℝ) :=
    (Real.rpow_le_rpow hx hxB (by norm_num : (0 : ℝ) ≤ 3 / 4)).trans
      (Real.rpow_le_rpow_of_exponent_le hB1
        (by norm_num : (3 / 4 : ℝ) ≤ 3 / 2))
  have hthreeHalves : (A + R⁻¹) ^ (3 / 2 : ℝ) ≤
      (A + 1) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hx hxB (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hterm1 := mul_le_mul_of_nonneg_left hfactor hC
  have hterm2 := mul_le_mul_of_nonneg_left
    (mul_le_mul hR74 hthreeQuarters (Real.rpow_nonneg hx _) hInv) hC
  have hterm3 := mul_le_mul_of_nonneg_left hthreeHalves (mul_nonneg hC hInv)
  simp only [div_eq_mul_inv]
  nlinarith only [hterm1, hterm2, hterm3]

/-- Scalar Young absorption of all cutoff remainders. The same nonnegative
constant works for every nonnegative gradient norm and every radius at least
one. -/
theorem exists_cutoff_absorption {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ D ≥ 0, ∀ A ≥ 0, ∀ R ≥ 1,
      C * ((A + R⁻¹) ^ (1 / 2 : ℝ) + 1) *
          (R⁻¹ * A + R ^ (-2 : ℝ)) +
        C * R ^ (-7 / 4 : ℝ) * (A + R⁻¹) ^ (3 / 4 : ℝ) +
        C * R⁻¹ * (A + R⁻¹) ^ (3 / 2 : ℝ) ≤
          δ * A ^ 2 + D / R := by
  obtain ⟨D, hD, hbound⟩ := exists_scaled_shifted_rpow_absorption
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC) hδ
    (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) < 2)
  exact ⟨D, hD, fun A hA R hR =>
    (cutoff_expression_le hC hA hR).trans (hbound A hA R hR)⟩

end NavierStokesR3.ComparisonYoung
