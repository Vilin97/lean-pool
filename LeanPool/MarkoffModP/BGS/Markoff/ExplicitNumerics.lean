/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.NumberTheory.ExplicitDivisorBound
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.DivisorRange
public import LeanPool.MarkoffModP.BGS.Markoff.Endgame.PrimitiveInclusionExclusion

/-!
# Closed numerical bounds for explicit strong approximation

All constants in this file are closed natural-number expressions.  In
particular, no witness is extracted from an eventual or asymptotic theorem.
-/

@[expose] public section

namespace BGS.Markoff

open scoped Topology

/-! The first explicit record is retained in a namespace for comparison. -/
namespace Legacy

/-- Sealed data for the deliberately conservative project cutoff. -/
@[irreducible] noncomputable def explicitStrongApproximationCutoffData :
    {n : ℕ // n = BGS.NumberTheory.explicitDivisorConstant + 1} :=
  ⟨BGS.NumberTheory.explicitDivisorConstant + 1, rfl⟩

/-- The deliberately conservative project cutoff.  It is not the primorial
constant from arXiv:2308.07579. -/
noncomputable def explicitStrongApproximationCutoff : ℕ :=
  explicitStrongApproximationCutoffData.1

theorem explicitStrongApproximationCutoff_eq :
    explicitStrongApproximationCutoff =
      BGS.NumberTheory.explicitDivisorConstant + 1 :=
  explicitStrongApproximationCutoffData.2

private theorem fixedNumeral_pow_thirtyTwo_le_explicitDivisorConstant :
    100522 ^ 32 ≤ BGS.NumberTheory.explicitDivisorConstant := by
  rw [BGS.NumberTheory.explicitDivisorConstant_eq]
  calc
    100522 ^ 32 ≤ (32 ^ 32) ^ 32 :=
      Nat.pow_le_pow_left (by norm_num) 32
    _ ≤ (32 ^ 32) ^ (2 ^ 32) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)

theorem explicitCutoff_gt_one : 1 < explicitStrongApproximationCutoff := by
  have hconstant : 0 < BGS.NumberTheory.explicitDivisorConstant :=
    BGS.NumberTheory.explicitDivisorConstant_pos
  rw [explicitStrongApproximationCutoff_eq]
  exact Nat.succ_lt_succ hconstant

private theorem explicitCutoff_constant_lt
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    BGS.NumberTheory.explicitDivisorConstant < p := by
  rw [explicitStrongApproximationCutoff_eq] at hp
  exact (Nat.lt_succ_self _).trans_le hp

theorem fixed_lt_rpow_one_div_thirtyTwo_of_explicitCutoff
    {p fixed : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    (hfixed : fixed ^ 32 ≤ BGS.NumberTheory.explicitDivisorConstant) :
    (fixed : ℝ) < (p : ℝ) ^ (1 / 32 : ℝ) := by
  have hpPos : 0 < p :=
    Nat.zero_lt_one.trans (explicitCutoff_gt_one.trans_le hp)
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowNat : fixed ^ 32 < p :=
    hfixed.trans_lt (explicitCutoff_constant_lt hp)
  have hpowReal :
      (fixed : ℝ) ^ 32 < (p : ℝ) := by
    exact_mod_cast hpowNat
  have hrootPow : ((p : ℝ) ^ (1 / 32 : ℝ)) ^ 32 = (p : ℝ) := by
    calc
      ((p : ℝ) ^ (1 / 32 : ℝ)) ^ 32 =
          (p : ℝ) ^ ((1 / 32 : ℝ) * 32) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 32 : ℝ) 32).symm
      _ = (p : ℝ) := by norm_num
  apply lt_of_pow_lt_pow_left₀ 32 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

theorem small_fixed_lt_rpow_one_div_thirtyTwo_of_explicitCutoff
    {p fixed : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    (hfixed : fixed ≤ 100522) :
    (fixed : ℝ) < (p : ℝ) ^ (1 / 32 : ℝ) :=
  fixed_lt_rpow_one_div_thirtyTwo_of_explicitCutoff hp
    ((Nat.pow_le_pow_left hfixed 32).trans
      fixedNumeral_pow_thirtyTwo_le_explicitDivisorConstant)

private theorem explicitDivisorConstant_le_pred
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    BGS.NumberTheory.explicitDivisorConstant ≤ p - 1 := by
  have hconstant := explicitCutoff_constant_lt hp
  omega

private theorem explicitDivisorConstant_le_succ
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    BGS.NumberTheory.explicitDivisorConstant ≤ p + 1 := by
  have hconstant := explicitCutoff_constant_lt hp
  omega

/-- Both divisor counts occurring in the all-divisors Corvaja--Zannier
union bound are controlled by one sixteenth root of `p`. -/
theorem explicit_divisor_sum_le_three_mul_rpow
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) ≤
      3 * (p : ℝ) ^ (1 / 16 : ℝ) := by
  have hpOne : 1 ≤ p := (explicitCutoff_gt_one.trans_le hp).le
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hminusRaw := BGS.NumberTheory.card_divisors_le_rpow_one_div_sixteen
    (p - 1) (explicitDivisorConstant_le_pred hp)
  have hminusBase : (((p - 1 : ℕ) : ℝ) : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast Nat.sub_le p 1
  have hminus : ((p - 1).divisors.card : ℝ) ≤
      (p : ℝ) ^ (1 / 16 : ℝ) :=
    hminusRaw.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) hminusBase (by norm_num))
  have hplusRaw := BGS.NumberTheory.card_divisors_le_rpow_one_div_sixteen
    (p + 1) (explicitDivisorConstant_le_succ hp)
  have hplusBase : (((p + 1 : ℕ) : ℝ) : ℝ) ≤ 2 * (p : ℝ) := by
    exact_mod_cast (show p + 1 ≤ 2 * p by omega)
  have htwo : (2 : ℝ) ^ (1 / 16 : ℝ) ≤ 2 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hplus : ((p + 1).divisors.card : ℝ) ≤
      2 * (p : ℝ) ^ (1 / 16 : ℝ) := by
    calc
      ((p + 1).divisors.card : ℝ) ≤ (((p + 1 : ℕ) : ℝ) : ℝ) ^ (1 / 16 : ℝ) :=
        hplusRaw
      _ ≤ (2 * (p : ℝ)) ^ (1 / 16 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hplusBase (by norm_num)
      _ = (2 : ℝ) ^ (1 / 16 : ℝ) * (p : ℝ) ^ (1 / 16 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hpNonnegative]
      _ ≤ 2 * (p : ℝ) ^ (1 / 16 : ℝ) := by gcongr
  norm_num only [Nat.cast_add]
  linarith

/-- The coefficient-48 all-divisors term used by the middle game. -/
theorem explicit_corvajaZannier_divisor_term_le
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    ((corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) : ℕ) : ℝ) ≤
      144 * (p : ℝ) ^ (1 / 16 : ℝ) := by
  have h := explicit_divisor_sum_le_three_mul_rpow hp
  norm_num [corvajaZannierCorollaryTwoSafeCoefficient] at h ⊢
  linarith

end Legacy

/-! ## Ninth-moment adaptive cutoff -/

/-- The coefficient in the simultaneous ninth-moment bound for the divisor
counts of `p - 1` and `p + 1`. -/
@[irreducible] def explicitDivisorMomentConstantData :
    {n : ℕ // n = 2 ^ 9 * (9 ^ 9) ^ (2 ^ 9)} :=
  ⟨2 ^ 9 * (9 ^ 9) ^ (2 ^ 9), rfl⟩

def explicitDivisorMomentConstant : ℕ :=
  explicitDivisorMomentConstantData.1

theorem explicitDivisorMomentConstant_eq :
    explicitDivisorMomentConstant = 2 ^ 9 * (9 ^ 9) ^ (2 ^ 9) :=
  explicitDivisorMomentConstantData.2

theorem explicitDivisorMomentConstant_pos :
    0 < explicitDivisorMomentConstant := by
  rw [explicitDivisorMomentConstant_eq]
  positivity

/-- Sealed data for the improved project cutoff. -/
@[irreducible] noncomputable def explicitStrongApproximationCutoffData :
    {n : ℕ // n =
      2 ^ 9 * (48 ^ 3 + 1) ^ 18 * explicitDivisorMomentConstant ^ 8 + 1} :=
  ⟨2 ^ 9 * (48 ^ 3 + 1) ^ 18 * explicitDivisorMomentConstant ^ 8 + 1, rfl⟩

/-- The explicit project cutoff.  It is deliberately different from the
primorial constant in arXiv:2308.07579. -/
noncomputable def explicitStrongApproximationCutoff : ℕ :=
  explicitStrongApproximationCutoffData.1

theorem explicitStrongApproximationCutoff_eq :
    explicitStrongApproximationCutoff =
      2 ^ 9 * (48 ^ 3 + 1) ^ 18 * explicitDivisorMomentConstant ^ 8 + 1 :=
  explicitStrongApproximationCutoffData.2

theorem explicitCutoff_gt_one : 1 < explicitStrongApproximationCutoff := by
  rw [explicitStrongApproximationCutoff_eq]
  exact Nat.succ_lt_succ <|
    Nat.mul_pos (Nat.mul_pos (by positivity) (by positivity))
      (pow_pos explicitDivisorMomentConstant_pos _)

theorem explicitCutoff_constant_lt
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    2 ^ 9 * (48 ^ 3 + 1) ^ 18 * explicitDivisorMomentConstant ^ 8 < p := by
  rw [explicitStrongApproximationCutoff_eq] at hp
  omega

/-- The elementary factorization estimate, specialized to the simultaneous
ninth moment needed below. -/
theorem explicit_divisor_sum_pow_nine_le
    {p : ℕ} (hp : 2 ≤ p) :
    ((p - 1).divisors.card + (p + 1).divisors.card) ^ 9 ≤
      explicitDivisorMomentConstant * p := by
  have hminusNe : p - 1 ≠ 0 := by omega
  have hplusNe : p + 1 ≠ 0 := by omega
  have hminus := BGS.NumberTheory.card_divisors_pow_le_explicit_constant_mul
    9 (by norm_num) (p - 1) hminusNe
  have hplus := BGS.NumberTheory.card_divisors_pow_le_explicit_constant_mul
    9 (by norm_num) (p + 1) hplusNe
  calc
    ((p - 1).divisors.card + (p + 1).divisors.card) ^ 9 ≤
        2 ^ (9 - 1) *
          ((p - 1).divisors.card ^ 9 + (p + 1).divisors.card ^ 9) :=
      add_pow_le (Nat.zero_le _) (Nat.zero_le _) 9
    _ ≤ 2 ^ (9 - 1) * (((9 ^ 9) ^ (2 ^ 9) * (p - 1)) +
        ((9 ^ 9) ^ (2 ^ 9) * (p + 1))) := by
      gcongr
    _ = explicitDivisorMomentConstant * p := by
      let D := (9 ^ 9) ^ (2 ^ 9)
      have hsub : p - 1 + (p + 1) = 2 * p := by omega
      rw [explicitDivisorMomentConstant_eq]
      change 2 ^ (9 - 1) * (D * (p - 1) + D * (p + 1)) =
        (2 ^ 9 * D) * p
      calc
        2 ^ (9 - 1) * (D * (p - 1) + D * (p + 1)) =
            2 ^ 8 * D * (p - 1 + (p + 1)) := by norm_num; ring
        _ = 2 ^ 8 * D * (2 * p) := by rw [hsub]
        _ = (2 ^ 9 * D) * p := by norm_num; ring

private theorem explicitDivisorMomentConstant_pow_two_le_pow_eight :
    explicitDivisorMomentConstant ^ 2 ≤ explicitDivisorMomentConstant ^ 8 :=
  Nat.pow_le_pow_right explicitDivisorMomentConstant_pos (by norm_num)

/-- The complete coefficient-48 divisor term lies below the sixth root of
`p`.  This is the linear middle-game estimate used up to order `p^(5/6)`. -/
theorem explicit_corvajaZannier_divisor_term_lt_rpow_one_div_six
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) : ℕ) <
      (p : ℝ) ^ (1 / 6 : ℝ) := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpTwo : 2 ≤ p := by
    have hcutoffTwo : 2 ≤ explicitStrongApproximationCutoff :=
      explicitCutoff_gt_one
    omega
  have hmoment : T ^ 9 ≤ explicitDivisorMomentConstant * p :=
    explicit_divisor_sum_pow_nine_le hpTwo
  have hcoefficient :
      48 ^ 18 * explicitDivisorMomentConstant ^ 2 ≤
        2 ^ 9 * (48 ^ 3 + 1) ^ 18 * explicitDivisorMomentConstant ^ 8 := by
    exact Nat.mul_le_mul (by norm_num)
      explicitDivisorMomentConstant_pow_two_le_pow_eight
  have hconstant := explicitCutoff_constant_lt hp
  have hpowNat : (48 * T) ^ 18 < p ^ 3 := by
    calc
      (48 * T) ^ 18 = 48 ^ 18 * (T ^ 9) ^ 2 := by
        rw [mul_pow]
        congr 1
        rw [show (18 : ℕ) = 9 * 2 by norm_num, pow_mul]
      _ ≤ 48 ^ 18 * (explicitDivisorMomentConstant * p) ^ 2 := by gcongr
      _ = (48 ^ 18 * explicitDivisorMomentConstant ^ 2) * p ^ 2 := by
        rw [mul_pow]
        ring
      _ ≤ (2 ^ 9 * (48 ^ 3 + 1) ^ 18 *
          explicitDivisorMomentConstant ^ 8) * p ^ 2 :=
        Nat.mul_le_mul_right _ hcoefficient
      _ < p * p ^ 2 := by gcongr
      _ = p ^ 3 := by ring
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : ((48 * T : ℕ) : ℝ) ^ 18 < (p : ℝ) ^ 3 := by
    exact_mod_cast hpowNat
  have hrootPow : (((p : ℝ) ^ (1 / 6 : ℝ)) ^ 18 = (p : ℝ) ^ 3) := by
    calc
      ((p : ℝ) ^ (1 / 6 : ℝ)) ^ 18 =
          (p : ℝ) ^ ((1 / 6 : ℝ) * 18) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 6 : ℝ) 18).symm
      _ = (p : ℝ) ^ 3 := by norm_num
  norm_num only [corvajaZannierCorollaryTwoSafeCoefficient]
  change ((48 * T : ℕ) : ℝ) < (p : ℝ) ^ (1 / 6 : ℝ)
  apply lt_of_pow_lt_pow_left₀ 18 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

/-- The weighted square of the simultaneous divisor count lies below the
one-third power needed by the primitive endgame. -/
theorem explicit_weighted_divisor_sum_sq_lt_rpow_one_div_three
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    ((68 * ((p - 1).divisors.card + (p + 1).divisors.card) ^ 2 : ℕ) : ℝ) <
      (p : ℝ) ^ (1 / 3 : ℝ) := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpTwo : 2 ≤ p := by
    have hcutoffTwo : 2 ≤ explicitStrongApproximationCutoff :=
      explicitCutoff_gt_one
    omega
  have hmoment : T ^ 9 ≤ explicitDivisorMomentConstant * p :=
    explicit_divisor_sum_pow_nine_le hpTwo
  have hcoefficient :
      68 ^ 9 * explicitDivisorMomentConstant ^ 2 ≤
        2 ^ 9 * (48 ^ 3 + 1) ^ 18 * explicitDivisorMomentConstant ^ 8 := by
    exact Nat.mul_le_mul (by norm_num)
      explicitDivisorMomentConstant_pow_two_le_pow_eight
  have hconstant := explicitCutoff_constant_lt hp
  have hpowNat : (68 * T ^ 2) ^ 9 < p ^ 3 := by
    calc
      (68 * T ^ 2) ^ 9 = 68 ^ 9 * (T ^ 9) ^ 2 := by ring
      _ ≤ 68 ^ 9 * (explicitDivisorMomentConstant * p) ^ 2 := by gcongr
      _ = (68 ^ 9 * explicitDivisorMomentConstant ^ 2) * p ^ 2 := by
        rw [mul_pow]
        ring
      _ ≤ (2 ^ 9 * (48 ^ 3 + 1) ^ 18 *
          explicitDivisorMomentConstant ^ 8) * p ^ 2 :=
        Nat.mul_le_mul_right _ hcoefficient
      _ < p * p ^ 2 := by gcongr
      _ = p ^ 3 := by ring
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : ((68 * T ^ 2 : ℕ) : ℝ) ^ 9 < (p : ℝ) ^ 3 := by
    exact_mod_cast hpowNat
  have hrootPow : (((p : ℝ) ^ (1 / 3 : ℝ)) ^ 9 = (p : ℝ) ^ 3) := by
    calc
      ((p : ℝ) ^ (1 / 3 : ℝ)) ^ 9 =
          (p : ℝ) ^ ((1 / 3 : ℝ) * 9) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 3 : ℝ) 9).symm
      _ = (p : ℝ) ^ 3 := by norm_num
  change ((68 * T ^ 2 : ℕ) : ℝ) < (p : ℝ) ^ (1 / 3 : ℝ)
  apply lt_of_pow_lt_pow_left₀ 9 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

/-- The simultaneous divisor count itself remains below the eighth root of
`p`; this sharper unweighted estimate is retained for the cage. -/
theorem explicit_divisor_sum_lt_rpow_one_div_eight
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) <
      (p : ℝ) ^ (1 / 8 : ℝ) := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpTwo : 2 ≤ p := by
    have hcutoffTwo : 2 ≤ explicitStrongApproximationCutoff :=
      explicitCutoff_gt_one
    omega
  have hmoment : T ^ 9 ≤ explicitDivisorMomentConstant * p :=
    explicit_divisor_sum_pow_nine_le hpTwo
  have hcoefficient : explicitDivisorMomentConstant ^ 8 ≤
      2 ^ 9 * (48 ^ 3 + 1) ^ 18 * explicitDivisorMomentConstant ^ 8 := by
    have hfactor : 1 ≤ 2 ^ 9 * (48 ^ 3 + 1) ^ 18 := by norm_num
    simpa only [one_mul] using
      Nat.mul_le_mul_right (explicitDivisorMomentConstant ^ 8) hfactor
  have hconstant := explicitCutoff_constant_lt hp
  have hpowNat : T ^ 72 < p ^ 9 := by
    calc
      T ^ 72 = (T ^ 9) ^ 8 := by
        rw [show (72 : ℕ) = 9 * 8 by norm_num, pow_mul]
      _ ≤ (explicitDivisorMomentConstant * p) ^ 8 := by gcongr
      _ = explicitDivisorMomentConstant ^ 8 * p ^ 8 := by rw [mul_pow]
      _ ≤ (2 ^ 9 * (48 ^ 3 + 1) ^ 18 *
          explicitDivisorMomentConstant ^ 8) * p ^ 8 :=
        Nat.mul_le_mul_right _ hcoefficient
      _ < p * p ^ 8 := by gcongr
      _ = p ^ 9 := by ring
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : (T : ℝ) ^ 72 < (p : ℝ) ^ 9 := by exact_mod_cast hpowNat
  have hrootPow : (((p : ℝ) ^ (1 / 8 : ℝ)) ^ 72 = (p : ℝ) ^ 9) := by
    calc
      ((p : ℝ) ^ (1 / 8 : ℝ)) ^ 72 =
          (p : ℝ) ^ ((1 / 8 : ℝ) * 72) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 8 : ℝ) 72).symm
      _ = (p : ℝ) ^ 9 := by norm_num
  change (T : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ)
  apply lt_of_pow_lt_pow_left₀ 72 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

/-- Every fixed coefficient used by the explicit proof is also below the
eighth root of `p`. -/
theorem small_fixed_lt_rpow_one_div_eight_of_explicitCutoff
    {p fixed : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    (hfixed : fixed ≤ 100522) :
    (fixed : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) := by
  have hmomentOne : 1 ≤ explicitDivisorMomentConstant ^ 8 :=
    Nat.one_le_pow _ _ explicitDivisorMomentConstant_pos
  have hfixedPower : 100522 ^ 8 ≤
      2 ^ 9 * (48 ^ 3 + 1) ^ 18 * explicitDivisorMomentConstant ^ 8 := by
    have hnumeric : 100522 ^ 8 ≤ 2 ^ 9 * (48 ^ 3 + 1) ^ 18 := by norm_num
    simpa only [mul_one] using Nat.mul_le_mul hnumeric hmomentOne
  have hpowNat : fixed ^ 8 < p := by
    calc
      fixed ^ 8 ≤ 100522 ^ 8 := Nat.pow_le_pow_left hfixed _
      _ ≤ 2 ^ 9 * (48 ^ 3 + 1) ^ 18 * explicitDivisorMomentConstant ^ 8 :=
        hfixedPower
      _ < p := explicitCutoff_constant_lt hp
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : (fixed : ℝ) ^ 8 < (p : ℝ) := by exact_mod_cast hpowNat
  have hrootPow : ((p : ℝ) ^ (1 / 8 : ℝ)) ^ 8 = (p : ℝ) := by
    calc
      ((p : ℝ) ^ (1 / 8 : ℝ)) ^ 8 =
          (p : ℝ) ^ ((1 / 8 : ℝ) * 8) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 8 : ℝ) 8).symm
      _ = (p : ℝ) := by norm_num
  apply lt_of_pow_lt_pow_left₀ 8 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

end BGS.Markoff
