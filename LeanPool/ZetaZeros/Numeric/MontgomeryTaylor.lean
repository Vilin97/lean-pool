/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import LeanPool.ZetaZeros.Meta.Attr

/-!
# The Montgomery–Taylor constant is less than `1.3275`

The single numerical input to both headline bounds. Since `(1/√2)² = 1/2` exactly, the values
`cos(1/√2)` and `√2 sin(1/√2)` are alternating series with *rational* terms, so bounding them needs
no estimate at an irrational argument: five terms bound the first from above, four bound the second
from below, and the gap to `1.3275` is about `7 · 10⁻⁷`.
-/

@[expose] public section

namespace ZetaZeros

open Filter Finset

-- The factorial notation `n !` is scoped to `Nat`.
open scoped Nat

/-- The Montgomery–Taylor constant `1/2 + (1/√2) cot(1/√2) = 1.3274992963…`. -/
@[zz_tag "def_C_MT"]
noncomputable def montgomeryTaylorConst : ℝ :=
  1 / 2 + (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2)

/-- The proportion of zeros shown simple and on the critical line,
`3/2 - (1/√2) cot(1/√2) = 0.6725007037…`. -/
@[zz_tag "def_C0"]
noncomputable def simpleProportion : ℝ :=
  3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2)

/-- The proportion of zeros shown distinct, `5/4 - (1/(2√2)) cot(1/√2) = 0.8362503518…`. -/
@[zz_tag "def_C1"]
noncomputable def distinctProportion : ℝ :=
  5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2)

section Elementary

private lemma sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

/-- The whole point: `(1/√2)² = 1/2` on the nose, which is what makes the two series rational. -/
private lemma inv_sqrt_two_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

private lemma inv_sqrt_two_lt_one : 1 / Real.sqrt 2 < 1 := by
  rw [div_lt_one sqrt_two_pos, ← Real.sqrt_one]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

end Elementary

/-- `sin(1/√2) > 0`. -/
@[zz_tag "lem_sin_pos"]
theorem sin_inv_sqrt_two_pos : 0 < Real.sin (1 / Real.sqrt 2) :=
  Real.sin_pos_of_pos_of_le_one (by positivity) (le_of_lt inv_sqrt_two_lt_one)

/-- The `k`-th term of the rational series for `cos(1/√2)`. -/
noncomputable def cosTerm (k : ℕ) : ℝ := 1 / (2 ^ k * ((2 * k)! : ℝ))

/-- The `k`-th term of the rational series for `√2 sin(1/√2)`. -/
noncomputable def sinTerm (k : ℕ) : ℝ := 1 / (2 ^ k * ((2 * k + 1)! : ℝ))

/-- `cos(1/√2)` is the alternating sum of `1 / (2ᵏ (2k)!)`. -/
@[zz_tag "lem_cos_series"]
theorem hasSum_cosTerm :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * cosTerm k) (Real.cos (1 / Real.sqrt 2)) := by
  have h := Real.hasSum_cos (1 / Real.sqrt 2)
  have hfun : (fun n : ℕ => (-1 : ℝ) ^ n * (1 / Real.sqrt 2) ^ (2 * n) / ((2 * n)! : ℝ))
      = fun k : ℕ => (-1 : ℝ) ^ k * cosTerm k := by
    funext k
    rw [cosTerm, pow_mul, inv_sqrt_two_sq, div_pow, one_pow]
    have : ((2 * k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  rwa [hfun] at h

/-- `√2 sin(1/√2)` is the alternating sum of `1 / (2ᵏ (2k+1)!)`. -/
@[zz_tag "lem_sin_series"]
theorem hasSum_sinTerm :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * sinTerm k)
      (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)) := by
  have h := (Real.hasSum_sin (1 / Real.sqrt 2)).mul_left (Real.sqrt 2)
  have hfun : (fun n : ℕ => Real.sqrt 2 *
        ((-1 : ℝ) ^ n * (1 / Real.sqrt 2) ^ (2 * n + 1) / ((2 * n + 1)! : ℝ)))
      = fun k : ℕ => (-1 : ℝ) ^ k * sinTerm k := by
    funext k
    rw [sinTerm, pow_succ, pow_mul, inv_sqrt_two_sq, div_pow, one_pow]
    have hf : ((2 * k + 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hs : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt_two_pos
    field_simp
  rwa [hfun] at h

private lemma cosTerm_antitone : Antitone cosTerm := by
  refine antitone_nat_of_succ_le fun n => ?_
  have hpos : (0:ℝ) < 2 ^ n * ((2 * n)! : ℝ) := by
    have : (0:ℝ) < ((2 * n)! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    positivity
  have hle : (2:ℝ) ^ n * ((2 * n)! : ℝ) ≤ 2 ^ (n + 1) * ((2 * (n + 1))! : ℝ) := by
    have hf : ((2 * n)! : ℝ) ≤ ((2 * (n + 1))! : ℝ) :=
      Nat.cast_le.mpr (Nat.factorial_le (by omega))
    have hp : (2:ℝ) ^ n ≤ 2 ^ (n + 1) := by
      apply pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 : (0:ℝ) < (2:ℝ) ^ n := by positivity
    have h2 : (0:ℝ) < ((2 * n)! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    nlinarith
  simpa [cosTerm] using one_div_le_one_div_of_le hpos hle

private lemma sinTerm_antitone : Antitone sinTerm := by
  refine antitone_nat_of_succ_le fun n => ?_
  have hpos : (0:ℝ) < 2 ^ n * ((2 * n + 1)! : ℝ) := by
    have : (0:ℝ) < ((2 * n + 1)! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    positivity
  have hle : (2:ℝ) ^ n * ((2 * n + 1)! : ℝ) ≤ 2 ^ (n + 1) * ((2 * (n + 1) + 1)! : ℝ) := by
    have hf : ((2 * n + 1)! : ℝ) ≤ ((2 * (n + 1) + 1)! : ℝ) :=
      Nat.cast_le.mpr (Nat.factorial_le (by omega))
    have hp : (2:ℝ) ^ n ≤ 2 ^ (n + 1) := by
      apply pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 : (0:ℝ) < (2:ℝ) ^ n := by positivity
    have h2 : (0:ℝ) < ((2 * n + 1)! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    nlinarith
  simpa [sinTerm] using one_div_le_one_div_of_le hpos hle

/-- Five terms bound `cos(1/√2)` from above. The partial sum is `0.760244605…`. -/
@[zz_tag "lem_cos_upper"]
theorem cos_inv_sqrt_two_lt : Real.cos (1 / Real.sqrt 2) < 0.7602447 := by
  have h := Antitone.tendsto_le_alternating_series
    hasSum_cosTerm.tendsto_sum_nat cosTerm_antitone 2
  have hsum : ∑ i ∈ Finset.range (2 * 2 + 1), (-1 : ℝ) ^ i * cosTerm i < 0.7602447 := by
    norm_num [Finset.sum_range_succ, cosTerm, Nat.factorial]
  linarith

/-- Four terms bound `√2 sin(1/√2)` from below. The partial sum is `0.918725198…`. -/
@[zz_tag "lem_sin_lower"]
theorem sqrt_two_mul_sin_inv_sqrt_two_gt :
    0.9187251 < Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) := by
  have h := Antitone.alternating_series_le_tendsto
    hasSum_sinTerm.tendsto_sum_nat sinTerm_antitone 2
  have hsum : (0.9187251 : ℝ) < ∑ i ∈ Finset.range (2 * 2), (-1 : ℝ) ^ i * sinTerm i := by
    norm_num [Finset.sum_range_succ, sinTerm, Nat.factorial]
  linarith

/-- `(1/√2) cot(1/√2) < 0.8275`. -/
@[zz_tag "lem_cot_upper"]
theorem inv_sqrt_two_mul_cot_lt : (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) < 0.8275 := by
  have hs : 0 < Real.sin (1 / Real.sqrt 2) := sin_inv_sqrt_two_pos
  have hden : 0 < Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) := by positivity
  have hcot : (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2)
      = Real.cos (1 / Real.sqrt 2) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)) := by
    rw [Real.cot_eq_cos_div_sin]
    field_simp
  rw [hcot, div_lt_iff₀ hden]
  linarith [cos_inv_sqrt_two_lt, sqrt_two_mul_sin_inv_sqrt_two_gt]

/-- **The numerical input.** `C_MT < 1.3275`, which is exactly what both headline bounds need:
`2 - 1.3275 = 0.6725` and `3/2 - 1.3275/2 = 0.83625`. -/
@[zz_tag "lem_cmt_upper"]
theorem montgomeryTaylorConst_lt : montgomeryTaylorConst < 1.3275 := by
  have := inv_sqrt_two_mul_cot_lt
  rw [montgomeryTaylorConst]
  linarith

/-- `C₀ = 2 - C_MT`. -/
@[zz_tag "lem_C0_eq"]
theorem simpleProportion_eq : simpleProportion = 2 - montgomeryTaylorConst := by
  rw [simpleProportion, montgomeryTaylorConst]; ring

/-- `C₁ = 3/2 - C_MT/2`. -/
@[zz_tag "lem_C1_eq"]
theorem distinctProportion_eq : distinctProportion = 3 / 2 - montgomeryTaylorConst / 2 := by
  rw [distinctProportion, montgomeryTaylorConst]
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt_two_pos
  field_simp
  ring

end ZetaZeros
