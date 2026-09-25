/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedMarginCost
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseBudget

/-!
# Pressure Gradient Origin Budget

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-!
# The clipped origin-carrier budget

At the clipped scale `(1 - R₁) / 2`, rescaling the one-sided Morrey bound
leaves its small-cell budget unchanged and multiplies its whole-carrier budget
by `(R₁ / ((1 - R₁) / 2)) ^ θ`. This file records the exact sufficient budget
condition, the threshold where that factor is at most one, and the strict
failure of the saturated established budget above that threshold.
-/

/-- The clipped radius is positive whenever the carrier radius is less than
one. -/
theorem clipped_scale_pos {R₁ : ℝ} (hR₁ : R₁ < 1) :
    0 < (1 - R₁) / 2 := by
  linarith only [hR₁]

/-- For `R₁ < 3 / 4`, the clipped scale ratio is at most six. -/
theorem clipped_scale_ratio_le_six {R₁ : ℝ} (hR₁ : R₁ < 3 / 4) :
    R₁ / ((1 - R₁) / 2) ≤ 6 := by
  have hρ₀ : 0 < (1 - R₁) / 2 := clipped_scale_pos (lt_trans hR₁ (by norm_num))
  rw [div_le_iff₀ hρ₀]
  linarith only [hR₁]

/-- The clipped scale ratio is at most one exactly up to the radius `1 / 3`. -/
theorem clipped_scale_ratio_le_one_iff {R₁ : ℝ} (hR₁ : R₁ < 1) :
    R₁ / ((1 - R₁) / 2) ≤ 1 ↔ R₁ ≤ 1 / 3 := by
  rw [div_le_one₀ (clipped_scale_pos hR₁)]
  constructor <;> intro h <;> linarith only [h]

/-- Above the threshold, the clipped scale ratio is strictly greater than
one. -/
theorem one_lt_clipped_scale_ratio {R₁ : ℝ}
    (hthird : 1 / 3 < R₁) (hR₁ : R₁ < 1) :
    1 < R₁ / ((1 - R₁) / 2) := by
  rw [one_lt_div (clipped_scale_pos hR₁)]
  linarith only [hthird]

/-- Under the admissible bounds on `q` and `τ`, the exponent in the clipped
scale factor lies between `59 / 25` and `71 / 25`. -/
theorem growth_exponent_mem_Icc {q τ : ℝ} (hq : 5 / 2 < q)
    (hτ : 25 / 3 ≤ τ) (hτ' : τ ≤ 25) :
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
  have hκlow : (25 : ℝ) / 11 ≤ min ((1 / τ + 8 / 25)⁻¹) q :=
    le_min hlow (by linarith only [hq])
  have hκhigh : min ((1 / τ + 8 / 25)⁻¹) q ≤ (25 : ℝ) / 9 :=
    le_trans (min_le_left _ _) hhigh
  have hκpos : (0 : ℝ) < min ((1 / τ + 8 / 25)⁻¹) q := by
    linarith only [hκlow]
  constructor
  · have hdiv : (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q ≤ 66 / 125 := by
      rw [div_le_div_iff₀ hκpos (by norm_num)]
      linarith only [hκlow]
    linarith only [hdiv]
  · have hdiv : (54 : ℝ) / 125 ≤ (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q := by
      rw [div_le_div_iff₀ (by norm_num) hκpos]
      linarith only [hκhigh]
    linarith only [hdiv]

/-- The clipped scale inflation factor has the uniform upper bound `216` on
the admissible range. -/
theorem clipped_factor_le_216 {R₁ θ : ℝ} (hR₁ : 0 < R₁)
    (hR₁' : R₁ < 3 / 4) (hθ : 0 ≤ θ) (hθ' : θ ≤ 3) :
    (R₁ / ((1 - R₁) / 2)) ^ θ ≤ 216 := by
  have hratio : R₁ / ((1 - R₁) / 2) ≤ 6 := clipped_scale_ratio_le_six hR₁'
  calc
    (R₁ / ((1 - R₁) / 2)) ^ θ ≤ 6 ^ θ :=
      Real.rpow_le_rpow (div_nonneg hR₁.le (clipped_scale_pos (lt_trans hR₁' (by norm_num))).le)
        hratio hθ
    _ ≤ 6 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ'
    _ = 216 := by norm_num

/-- On the lower-radius range, the clipped scale inflation factor is at most
one. -/
theorem clipped_factor_le_one {R₁ θ : ℝ} (hR₁ : 0 < R₁)
    (hR₁' : R₁ ≤ 1 / 3) (hθ : 0 ≤ θ) :
    (R₁ / ((1 - R₁) / 2)) ^ θ ≤ 1 := by
  have hR₁lt : R₁ < 1 := by linarith only [hR₁']
  have hratio : R₁ / ((1 - R₁) / 2) ≤ 1 :=
    (clipped_scale_ratio_le_one_iff hR₁lt).2 hR₁'
  exact Real.rpow_le_one (div_nonneg hR₁.le (clipped_scale_pos hR₁lt).le) hratio hθ

/-- Above `R₁ = 1 / 3`, every positive clipped scale exponent makes the
inflation factor strictly greater than one. -/
theorem one_lt_clipped_factor {R₁ θ : ℝ} (hthird : 1 / 3 < R₁)
    (hR₁ : R₁ < 1) (hθ : 0 < θ) :
    1 < (R₁ / ((1 - R₁) / 2)) ^ θ :=
  Real.one_lt_rpow (one_lt_clipped_scale_ratio hthird hR₁) hθ

/-- If the whole-carrier bound includes the clipped scale inflation, it
suffices for the one-sided Morrey bound at the clipped radius. -/
theorem clipped_clause_of_inflated_budget
    {q τ C_CZ R₀ R₁ ε : ℝ} {KU KD A B : ℝ≥0∞}
    (hR₁ : 0 < R₁) (hR₁' : R₁ < 1)
    (hA : A ≤ 3 * (3 * KU * KD + forceSourceMorreyBound q ε))
    (hB : B * ENNReal.ofReal
        ((R₁ / ((1 - R₁) / 2)) ^
          (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) ≤
      ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) :
    oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q)
        ((1 - R₁) / 2) A B ≤
      oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD := by
  rw [oneSidedMorreyBound_scale_eq (P := 6 / 5)
    (τ := min ((1 / τ + 8 / 25)⁻¹) q) (ρ₀ := (1 - R₁) / 2) (ρ₁ := R₁)
    (A := A) (B := B) (by norm_num) (clipped_scale_pos hR₁') hR₁]
  exact oneSidedMorreyBound_le_pressureGradientKP hA hB

/-- When `R₁ ≤ 1 / 3`, the established whole-carrier budget alone suffices at the
clipped radius. -/
theorem clipped_clause_of_global_bound
    {q τ C_CZ R₀ R₁ ε : ℝ} {KU KD A B : ℝ≥0∞}
    (hR₁ : 0 < R₁) (hR₁third : R₁ ≤ 1 / 3)
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτ' : τ ≤ 25)
    (hA : A ≤ 3 * (3 * KU * KD + forceSourceMorreyBound q ε))
    (hB : B ≤ ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) :
    oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q)
        ((1 - R₁) / 2) A B ≤
      oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD := by
  have hrange := growth_exponent_mem_Icc hq hτ hτ'
  have hθ : 0 ≤ 5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) := by
    linarith only [hrange.1]
  have hR₁lt : R₁ < 1 := by linarith only [hR₁third]
  have hfactor : ENNReal.ofReal
      ((R₁ / ((1 - R₁) / 2)) ^
        (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) : ℝ) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (clipped_factor_le_one hR₁ hR₁third hθ)
  have hB' : B * ENNReal.ofReal
      ((R₁ / ((1 - R₁) / 2)) ^
        (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) : ℝ) ≤
      ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) := by
    calc
      _ ≤ ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) *
          ENNReal.ofReal
            ((R₁ / ((1 - R₁) / 2)) ^
              (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) : ℝ) :=
        mul_le_mul' hB le_rfl
      _ ≤ ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) * 1 :=
        mul_le_mul' le_rfl hfactor
      _ = ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) := mul_one _
  exact clipped_clause_of_inflated_budget hR₁ hR₁lt hA hB'

private theorem oneSidedMorreyBound_strict_mono_right
    {P τ ρ : ℝ} {A B₁ B₂ : ℝ≥0∞}
    (hP : 0 < P) (hρ : 0 < ρ) (hA : A < ⊤) (hB₁₂ : B₁ < B₂) :
    oneSidedMorreyBound P τ ρ A B₁ < oneSidedMorreyBound P τ ρ A B₂ := by
  unfold oneSidedMorreyBound
  apply ENNReal.add_lt_add_left
  · exact (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hP.le)
      (ENNReal.mul_ne_top hA.ne ENNReal.ofReal_ne_top)).ne
  · have hcoef : 0 < ENNReal.ofReal ((ρ / 2) ^ (-(5 * (1 - P / τ) / P))) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
    exact ENNReal.mul_lt_mul_right (ne_of_gt hcoef) ENNReal.ofReal_ne_top
      (ENNReal.rpow_lt_rpow hB₁₂ (one_div_pos.mpr hP))

/-- At a saturated established budget, the clipped clause is strictly larger than
the established constant whenever `R₁ > 1 / 3`. This is a failure of that budget to
prove the clause, not a lower bound on the actual pressure-gradient integral.
-/
theorem clipped_saturated_budget_exceeds_KP
    {q τ C_CZ R₀ R₁ ε : ℝ} {KU KD : ℝ≥0∞}
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτ' : τ ≤ 25)
    (hR₁third : 1 / 3 < R₁) (hR₁' : R₁ < 3 / 4)
    (hKU : KU < ⊤) (hKD : KD < ⊤) :
    oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD <
      oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q)
        ((1 - R₁) / 2)
        (ENNReal.ofReal (|C_CZ| + 1) *
          (3 * (3 * KU * KD + forceSourceMorreyBound q ε)))
        (ENNReal.ofReal (|C_CZ| + 1) *
          ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) := by
  let κ := min ((1 / τ + 8 / 25)⁻¹) q
  let θ := 5 * (1 - (6 / 5 : ℝ) / κ)
  let A := ENNReal.ofReal (|C_CZ| + 1) *
    (3 * (3 * KU * KD + forceSourceMorreyBound q ε))
  let B := ENNReal.ofReal (|C_CZ| + 1) *
    ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)
  have hrange := growth_exponent_mem_Icc hq hτ hτ'
  have hθpos : 0 < θ := by dsimp [θ, κ]; linarith only [hrange.1]
  have hR₁lt : R₁ < 1 := lt_trans hR₁' (by norm_num)
  have hρ₀ : 0 < (1 - R₁) / 2 := clipped_scale_pos hR₁lt
  have hratio : 1 < R₁ / ((1 - R₁) / 2) :=
    one_lt_clipped_scale_ratio hR₁third hR₁lt
  have hfactorReal : 1 < (R₁ / ((1 - R₁) / 2)) ^ θ :=
    Real.one_lt_rpow hratio hθpos
  have hfactor : 1 < ENNReal.ofReal ((R₁ / ((1 - R₁) / 2)) ^ θ) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff').2
      ⟨hfactorReal, lt_trans (by norm_num) hfactorReal⟩
  have hforce : forceSourceMorreyBound q ε < ⊤ :=
    forceSourceMorreyBound_lt_top q ε hq
  have hc : ENNReal.ofReal (|C_CZ| + 1) < ⊤ := ENNReal.ofReal_lt_top
  have hA : A < ⊤ := by
    dsimp [A]
    apply ENNReal.mul_lt_top hc
    apply ENNReal.mul_lt_top (by simp)
    apply ENNReal.add_lt_top.mpr
    constructor
    · apply ENNReal.mul_lt_top
      · exact ENNReal.mul_lt_top (by simp) hKU
      · exact hKD
    · exact hforce
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hBtop : B < ⊤ := by
    dsimp [B]
    exact ENNReal.mul_lt_top hc ENNReal.ofReal_lt_top
  have hBscaled : B < B * ENNReal.ofReal ((R₁ / ((1 - R₁) / 2)) ^ θ) := by
    calc
      B = B * 1 := (mul_one B).symm
      _ < B * ENNReal.ofReal ((R₁ / ((1 - R₁) / 2)) ^ θ) :=
        ENNReal.mul_lt_mul_right (ne_of_gt hBpos) hBtop.ne hfactor
  dsimp [oneSidedPressureGradientKP, κ, A, B]
  rw [oneSidedMorreyBound_scale_eq (P := 6 / 5) (τ := κ)
    (ρ₀ := (1 - R₁) / 2) (ρ₁ := R₁) (A := A) (B := B)
    (by norm_num) hρ₀ (by linarith only [hR₁third])]
  exact oneSidedMorreyBound_strict_mono_right (by norm_num) (by linarith only [hR₁third])
    hA hBscaled

end CKN.Core.Step4
