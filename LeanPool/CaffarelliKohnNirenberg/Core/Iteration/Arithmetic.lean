/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Monotonicity
public import LeanPool.CaffarelliKohnNirenberg.Statements.Theta
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RpowSquares
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The arithmetic core of the scale iteration

This file records the real arithmetic used after the analytic decay estimate
in `paper/ckn.tex`, equations `eq:theta-decay-2` and `eq:kappa-props`.  The
analytic estimate itself is supplied as a hypothesis to the iteration theorem.
The radius interpolation theorem likewise takes the finiteness hypotheses
required by the radius monotonicity API.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

/-! ### The numerical convention -/

/-- The fixed exponent `ε = 2/5` in `conv:kappa`. -/
def iterationEpsilon : ℝ := 2 / 5

/-- The fixed contraction factor in `conv:kappa`. -/
def iterationKappa (C₂₇ : ℝ) : ℝ :=
  min (1 / 2) ((8 * C₂₇) ^ (-1 / (2 / 3 - iterationEpsilon)))

/-- The initial smallness threshold `η` in `conv:kappa`. -/
def iterationEta (C₂₇ : ℝ) : ℝ :=
  min 1 ((iterationKappa C₂₇ ^ (5 + iterationEpsilon) / (16 * C₂₇)) ^ 2)

/-- The auxiliary threshold `ε_*` in `conv:kappa`. -/
def iterationEpsilonStar (C₂₇ : ℝ) : ℝ :=
  min 1 ((iterationKappa C₂₇ ^ (5 + iterationEpsilon) / (32 * C₂₇)) ^ 2)

/-- The force coefficient `C₂₉` in `eq:C29`. -/
def iterationC₂₉ (C₂₇ C₂₈ : ℝ) : ℝ :=
  2 * C₂₈ ^ 2 * iterationKappa C₂₇ ^ (-1 - 2 * iterationEpsilon)
    + C₂₈ * iterationKappa C₂₇ ^ (-3 - iterationEpsilon)

/-- The force smallness threshold `Λ₀` in `eq:C29`. -/
def iterationLambda₀ (C₂₇ C₂₈ : ℝ) : ℝ :=
  iterationEta C₂₇ / (2 * iterationC₂₉ C₂₇ C₂₈)

/-- The convention exponent is exactly the paper's `2/5`. -/
theorem iterationEpsilon_eq : iterationEpsilon = (2 / 5 : ℝ) := by
  rfl

/-- The contraction factor is positive when the absolute decay constant is positive. -/
theorem iterationKappa_pos {C₂₇ : ℝ} (hC₂₇ : 0 < C₂₇) :
    0 < iterationKappa C₂₇ := by
  unfold iterationKappa
  apply lt_min
  · norm_num
  · apply Real.rpow_pos_of_pos
    positivity

/-- The paper's convention gives `κ ≤ 1/2`. -/
theorem iterationKappa_le_half (C₂₇ : ℝ) : iterationKappa C₂₇ ≤ (1 / 2 : ℝ) := by
  unfold iterationKappa
  exact min_le_left _ _

private theorem iterationKappa_exponent_pos :
    0 < 2 / 3 - iterationEpsilon := by
  norm_num [iterationEpsilon]

private theorem iterationKappa_decay_bound {C₂₇ : ℝ} (hC₂₇ : 0 < C₂₇) :
    C₂₇ * iterationKappa C₂₇ ^ (2 / 3 - iterationEpsilon) ≤ (1 / 8 : ℝ) := by
  have hκ : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  have hκle : iterationKappa C₂₇ ≤ (8 * C₂₇) ^
      (-1 / (2 / 3 - iterationEpsilon)) := min_le_right _ _
  have hbase : 0 < 8 * C₂₇ := by positivity
  have hexp : 0 < 2 / 3 - iterationEpsilon := iterationKappa_exponent_pos
  have hpow : iterationKappa C₂₇ ^ (2 / 3 - iterationEpsilon) ≤
      ((8 * C₂₇) ^ (-1 / (2 / 3 - iterationEpsilon))) ^
        (2 / 3 - iterationEpsilon) :=
    Real.rpow_le_rpow (le_of_lt hκ) hκle hexp.le
  have hright : ((8 * C₂₇) ^ (-1 / (2 / 3 - iterationEpsilon))) ^
      (2 / 3 - iterationEpsilon) = (8 * C₂₇)⁻¹ := by
    rw [← Real.rpow_mul (le_of_lt hbase)]
    have he : (-1 / (2 / 3 - iterationEpsilon)) *
        (2 / 3 - iterationEpsilon) = (-1 : ℝ) := by
      norm_num [iterationEpsilon]
    rw [he, Real.rpow_neg hbase.le]
    norm_num
  rw [hright] at hpow
  calc
    C₂₇ * iterationKappa C₂₇ ^ (2 / 3 - iterationEpsilon) ≤
        C₂₇ * (8 * C₂₇)⁻¹ := mul_le_mul_of_nonneg_left hpow hC₂₇.le
    _ = (1 / 8 : ℝ) := by field_simp

/-- The first numerical inequality in `eq:kappa-props`. -/
theorem iterationKappa_prop₁ {C₂₇ : ℝ} (hC₂₇ : 0 < C₂₇) :
    C₂₇ * iterationKappa C₂₇ ^ (2 / 3 - iterationEpsilon) ≤ (1 / 8 : ℝ) :=
  iterationKappa_decay_bound hC₂₇

/-- The threshold `η` is positive. -/
theorem iterationEta_pos {C₂₇ : ℝ} (hC₂₇ : 0 < C₂₇) : 0 < iterationEta C₂₇ := by
  unfold iterationEta
  have hκ : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  apply lt_min
  · norm_num
  · positivity

/-- The threshold `η` is at most one. -/
theorem iterationEta_le_one (C₂₇ : ℝ) : iterationEta C₂₇ ≤ (1 : ℝ) := by
  unfold iterationEta
  exact min_le_left _ _

/-- The auxiliary threshold `ε_*` is positive. -/
theorem iterationEpsilonStar_pos {C₂₇ : ℝ} (hC₂₇ : 0 < C₂₇) :
    0 < iterationEpsilonStar C₂₇ := by
  unfold iterationEpsilonStar
  have hκ : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  apply lt_min
  · norm_num
  · positivity

/-- The auxiliary threshold `ε_*` is at most one. -/
theorem iterationEpsilonStar_le_one (C₂₇ : ℝ) :
    iterationEpsilonStar C₂₇ ≤ (1 : ℝ) := by
  unfold iterationEpsilonStar
  exact min_le_left _ _

/-- The coefficient `C₂₉` is positive when both decay constants are positive. -/
theorem iterationC₂₉_pos {C₂₇ C₂₈ : ℝ} (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈) :
    0 < iterationC₂₉ C₂₇ C₂₈ := by
  unfold iterationC₂₉
  have hκ : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  positivity

/-- The force threshold is positive under the convention hypotheses. -/
theorem iterationLambda₀_pos {C₂₇ C₂₈ : ℝ} (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈) :
    0 < iterationLambda₀ C₂₇ C₂₈ := by
  unfold iterationLambda₀
  have hη : 0 < iterationEta C₂₇ := iterationEta_pos hC₂₇
  have hC₂₉ : 0 < iterationC₂₉ C₂₇ C₂₈ := iterationC₂₉_pos hC₂₇ hC₂₈
  positivity

/-- The final convention identity is `C₂₉ Λ₀ = η/2`. -/
theorem iterationC₂₉_mul_Lambda₀ {C₂₇ C₂₈ : ℝ}
    (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈) :
    iterationC₂₉ C₂₇ C₂₈ * iterationLambda₀ C₂₇ C₂₈ =
      iterationEta C₂₇ / 2 := by
  unfold iterationLambda₀
  have hC₂₉ : 0 < iterationC₂₉ C₂₇ C₂₈ := iterationC₂₉_pos hC₂₇ hC₂₈
  field_simp

private lemma min_sq_sqrt {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private lemma min_one_sq {x : ℝ} (hx : 0 ≤ x) :
    (min 1 x) ^ 2 = min 1 (x ^ 2) := by
  by_cases hle : x ≤ 1
  · have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hx, hle]
    rw [min_eq_right hle, min_eq_right hx2]
  · have hx1 : 1 < x := lt_of_not_ge hle
    have hx2 : 1 ≤ x ^ 2 := by nlinarith only [hx, hx1]
    rw [min_eq_left (le_of_lt hx1), min_eq_left hx2]
    norm_num

private lemma min_sq_sqrt_bound {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) :
    2 * b * (min 1 (a / (16 * b)) ^ 2) ^ (1 / 2 : ℝ) ≤ (1 / 8 : ℝ) := by
  have hx : 0 ≤ a / (16 * b) := div_nonneg ha (by positivity)
  by_cases hle : a / (16 * b) ≤ 1
  · rw [min_eq_right hle, min_sq_sqrt hx]
    calc
      2 * b * (a / (16 * b)) = a / 8 := by field_simp; ring
      _ ≤ 1 / 8 := by nlinarith only [ha1]
  · have hx1 : 1 < a / (16 * b) := lt_of_not_ge hle
    rw [min_eq_left (le_of_lt hx1)]
    have hb16 : 0 < 16 * b := by positivity
    have hlt' : 16 * b < a := by
      simpa only [one_mul] using (lt_div_iff₀ hb16).mp hx1
    nlinarith only [ha1, hlt']

/-- The second numerical inequality in `eq:kappa-props`. -/
theorem iterationKappa_prop₂ {C₂₇ : ℝ} (hC₂₇ : 0 < C₂₇) :
    2 * C₂₇ * iterationKappa C₂₇ ^ (-5 - iterationEpsilon) *
        (iterationEta C₂₇) ^ (1 / 2 : ℝ) ≤ (1 / 8 : ℝ) := by
  have hκ : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  have hb : 0 < C₂₇ * iterationKappa C₂₇ ^ (-5 - iterationEpsilon) := by
    positivity
  have hbound := min_sq_sqrt_bound (a := (1 : ℝ))
    (b := C₂₇ * iterationKappa C₂₇ ^ (-5 - iterationEpsilon))
    (by norm_num) (by norm_num) hb
  have harg : (1 : ℝ) /
      (16 * (C₂₇ * iterationKappa C₂₇ ^ (-5 - iterationEpsilon))) =
      iterationKappa C₂₇ ^ (5 + iterationEpsilon) / (16 * C₂₇) := by
    have hneg : -5 - iterationEpsilon = -(5 + iterationEpsilon) := by ring
    rw [hneg, Real.rpow_neg hκ.le]
    field_simp
  rw [harg] at hbound
  have hmin : (min 1 (iterationKappa C₂₇ ^ (5 + iterationEpsilon) /
      (16 * C₂₇))) ^ 2 =
      min 1 ((iterationKappa C₂₇ ^ (5 + iterationEpsilon) / (16 * C₂₇)) ^ 2) := by
    exact min_one_sq (x := iterationKappa C₂₇ ^ (5 + iterationEpsilon) /
      (16 * C₂₇)) (by positivity)
  rw [hmin] at hbound
  simpa [iterationEta, mul_assoc] using hbound

/-- The third numerical inequality in `eq:kappa-props`. -/
theorem iterationKappa_prop₃ {C₂₇ : ℝ} (hC₂₇ : 0 < C₂₇) :
    2 * C₂₇ * iterationKappa C₂₇ ^ (-5 - iterationEpsilon) *
        ((iterationEpsilonStar C₂₇) ^ (1 / 2 : ℝ) + iterationEpsilonStar C₂₇) ≤
      (1 / 8 : ℝ) := by
  have hκ : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  have hb : 0 < C₂₇ * iterationKappa C₂₇ ^ (-5 - iterationEpsilon) := by
    positivity
  have hbound := min_sq_sqrt_bound (a := (1 : ℝ))
    (b := 2 * (C₂₇ * iterationKappa C₂₇ ^ (-5 - iterationEpsilon)))
    (by norm_num) (by norm_num) (by positivity)
  have harg : (1 : ℝ) /
      (16 * (2 * (C₂₇ * iterationKappa C₂₇ ^ (-5 - iterationEpsilon)))) =
      iterationKappa C₂₇ ^ (5 + iterationEpsilon) / (32 * C₂₇) := by
    have hneg : -5 - iterationEpsilon = -(5 + iterationEpsilon) := by ring
    rw [hneg, Real.rpow_neg hκ.le]
    field_simp
    norm_num
  rw [harg] at hbound
  have hstar : 0 ≤ iterationEpsilonStar C₂₇ :=
    (iterationEpsilonStar_pos hC₂₇).le
  have hstar_le : iterationEpsilonStar C₂₇ ≤ 1 :=
    iterationEpsilonStar_le_one C₂₇
  have hsqrt_le : iterationEpsilonStar C₂₇ ≤
      (iterationEpsilonStar C₂₇) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.le_sqrt hstar hstar).2
    nlinarith only [hstar, hstar_le]
  calc
    2 * C₂₇ * iterationKappa C₂₇ ^ (-5 - iterationEpsilon) *
          (iterationEpsilonStar C₂₇ ^ (1 / 2 : ℝ) + iterationEpsilonStar C₂₇) =
        2 * (C₂₇ * iterationKappa C₂₇ ^ (-5 - iterationEpsilon)) *
          (iterationEpsilonStar C₂₇ ^ (1 / 2 : ℝ) + iterationEpsilonStar C₂₇) := by ring
    _ ≤ 2 * (C₂₇ * iterationKappa C₂₇ ^ (-5 - iterationEpsilon)) *
          (iterationEpsilonStar C₂₇ ^ (1 / 2 : ℝ) +
            iterationEpsilonStar C₂₇ ^ (1 / 2 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right hsqrt_le (iterationEpsilonStar C₂₇ ^ (1 / 2 : ℝ)))
        (by positivity)
    _ = 2 * (2 * (C₂₇ * iterationKappa C₂₇ ^ (-5 - iterationEpsilon))) *
          (iterationEpsilonStar C₂₇ ^ (1 / 2 : ℝ)) := by ring
    _ ≤ (1 / 8 : ℝ) := by
      have hmin : (min 1 (iterationKappa C₂₇ ^ (5 + iterationEpsilon) /
          (32 * C₂₇))) ^ 2 =
          min 1 ((iterationKappa C₂₇ ^ (5 + iterationEpsilon) / (32 * C₂₇)) ^ 2) := by
        exact min_one_sq (x := iterationKappa C₂₇ ^ (5 + iterationEpsilon) /
          (32 * C₂₇)) (by positivity)
      rw [hmin] at hbound
      simpa [iterationEpsilonStar] using hbound

/-! ### The normalized induction -/

private lemma young_eighth {a b : ℝ} :
    a * b ≤ (1 / 8 : ℝ) * a ^ 2 + 2 * b ^ 2 := by
  nlinarith only [sq_nonneg (a - 4 * b)]

/-- The normalized four-term induction from `prop:iteration`.

Here `T` and `L` are the paper's normalized sequences, while `Θ` is the
unscaled quantity appearing in the quadratic term of `eq:theta-decay-2`.
The hypotheses are exactly the numerical smallness inequalities used in the
paper's induction. -/
theorem iteration_normalized_bound
    {T L Θ : ℕ → ℝ} {κ ε η C₂₇ C₂₈ C₂₉ Λ₀ : ℝ}
    (hκ : 0 < κ) (hη : 0 < η)
    (hC₂₇ : 0 ≤ C₂₇) (hC₂₈ : 0 ≤ C₂₈)
    (hA : C₂₇ * κ ^ (2 / 3 - ε) ≤ (1 / 8 : ℝ))
    (hB : 2 * C₂₇ * κ ^ (-5 - ε) * η ^ (1 / 2 : ℝ) ≤ (1 / 8 : ℝ))
    (hC₂₉ : C₂₉ = 2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε)
      + C₂₈ * κ ^ (-3 - ε))
    (hC₂₉_nonneg : 0 ≤ C₂₉) (hΛ : C₂₉ * Λ₀ ≤ η / 2)
    (hT₀ : T 0 ≤ η) (hT_nonneg : ∀ n, 0 ≤ T n)
    (hΘ_nonneg : ∀ n, 0 ≤ Θ n) (hΘ_le : ∀ n, Θ n ≤ η)
    (hL_nonneg : ∀ n, 0 ≤ L n) (hL_le : ∀ n, L n ≤ Λ₀)
    (hrec : ∀ n, T (n + 1) ≤
      C₂₇ * κ ^ (2 / 3 - ε) * T n
        + 2 * C₂₇ * κ ^ (-5 - ε) * Θ n ^ (1 / 2 : ℝ) * T n
        + C₂₈ * κ ^ (-1 / 2 - ε) * T n ^ (1 / 2 : ℝ) * L n ^ (1 / 2 : ℝ)
        + C₂₈ * κ ^ (-3 - ε) * L n) :
    ∀ n, T n ≤ η := by
  intro n
  induction n with
  | zero => exact hT₀
  | succ n ih =>
      have hfirst : C₂₇ * κ ^ (2 / 3 - ε) * T n ≤ (1 / 8 : ℝ) * T n :=
        mul_le_mul_of_nonneg_right hA (hT_nonneg n)
      have hΘsqrt : Θ n ^ (1 / 2 : ℝ) ≤ η ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (hΘ_nonneg n) (hΘ_le n) (by norm_num)
      have hsecond :
          2 * C₂₇ * κ ^ (-5 - ε) * Θ n ^ (1 / 2 : ℝ) * T n ≤
            (1 / 8 : ℝ) * T n := by
        calc
          2 * C₂₇ * κ ^ (-5 - ε) * Θ n ^ (1 / 2 : ℝ) * T n ≤
              2 * C₂₇ * κ ^ (-5 - ε) * η ^ (1 / 2 : ℝ) * T n := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hΘsqrt (by positivity)) (hT_nonneg n)
          _ ≤ (1 / 8 : ℝ) * T n :=
            mul_le_mul_of_nonneg_right hB (hT_nonneg n)
      have hyoung :
          C₂₈ * κ ^ (-1 / 2 - ε) * T n ^ (1 / 2 : ℝ) * L n ^ (1 / 2 : ℝ) ≤
            (1 / 8 : ℝ) * T n +
              2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε) * L n := by
        have ha : 0 ≤ T n ^ (1 / 2 : ℝ) := Real.rpow_nonneg (hT_nonneg n) _
        have hb : 0 ≤ C₂₈ * κ ^ (-1 / 2 - ε) * L n ^ (1 / 2 : ℝ) := by
          exact mul_nonneg
            (mul_nonneg hC₂₈ (Real.rpow_nonneg hκ.le _))
            (Real.rpow_nonneg (hL_nonneg n) _)
        have hy := young_eighth
          (a := T n ^ (1 / 2 : ℝ))
          (b := C₂₈ * κ ^ (-1 / 2 - ε) * L n ^ (1 / 2 : ℝ))
        have hκsq : (κ ^ (-1 / 2 - ε)) ^ 2 = κ ^ (-1 - 2 * ε) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
          congr 1
          ring
        have hLsq : (L n ^ (1 / 2 : ℝ)) ^ 2 = L n :=
          CKN.Foundation.Euclidean.rpow_half_sq_of_nonneg (hL_nonneg n)
        calc
          C₂₈ * κ ^ (-1 / 2 - ε) * T n ^ (1 / 2 : ℝ) * L n ^ (1 / 2 : ℝ) =
              T n ^ (1 / 2 : ℝ) *
                (C₂₈ * κ ^ (-1 / 2 - ε) * L n ^ (1 / 2 : ℝ)) := by ring
          _ ≤ (1 / 8 : ℝ) * (T n ^ (1 / 2 : ℝ)) ^ 2 +
                2 * (C₂₈ * κ ^ (-1 / 2 - ε) * L n ^ (1 / 2 : ℝ)) ^ 2 := hy
          _ = (1 / 8 : ℝ) * T n +
                2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε) * L n := by
              rw [CKN.Foundation.Euclidean.rpow_half_sq_of_nonneg (hT_nonneg n)]
              simp only [mul_pow, hκsq, hLsq]
              ring
      have hlast :
          2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε) * L n +
              C₂₈ * κ ^ (-3 - ε) * L n ≤ C₂₉ * L n := by
        rw [hC₂₉]
        ring_nf
        exact le_rfl
      have hstep : T (n + 1) ≤ (3 / 8 : ℝ) * T n + C₂₉ * L n := by
        calc
          T (n + 1) ≤
              C₂₇ * κ ^ (2 / 3 - ε) * T n
                + 2 * C₂₇ * κ ^ (-5 - ε) * Θ n ^ (1 / 2 : ℝ) * T n
                + C₂₈ * κ ^ (-1 / 2 - ε) * T n ^ (1 / 2 : ℝ) * L n ^ (1 / 2 : ℝ)
                + C₂₈ * κ ^ (-3 - ε) * L n := hrec n
          _ ≤ (3 / 8 : ℝ) * T n + C₂₉ * L n := by
            nlinarith only [hfirst, hsecond, hyoung, hlast]
      have hforce : C₂₉ * L n ≤ η / 2 := by
        exact (mul_le_mul_of_nonneg_left (hL_le n) hC₂₉_nonneg).trans hΛ
      calc
        T (n + 1) ≤ (3 / 8 : ℝ) * T n + C₂₉ * L n := hstep
        _ ≤ (3 / 8 : ℝ) * η + η / 2 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left ih (by norm_num)) hforce
        _ ≤ η := by nlinarith only [hη]

/-- Reconstructs the paper's bound `θ_n ≤ η κ^(nε)` from the normalized
iteration bound. -/
theorem theta_iteration_bound
    {θ T : ℕ → ℝ} {κ ε η : ℝ}
    (hκ : 0 < κ) (hscale : ∀ n, θ n = T n * κ ^ ((n : ℝ) * ε))
    (hT : ∀ n, T n ≤ η) :
    ∀ n, θ n ≤ η * κ ^ ((n : ℝ) * ε) := by
  intro n
  rw [hscale n]
  exact mul_le_mul_of_nonneg_right (hT n)
    (Real.rpow_nonneg hκ.le ((n : ℝ) * ε))

/-- The paper's force decay `λ_n ≤ κ^(nσ) λ₀` implies the normalized bound
`L_n = λ_n κ^(-nε) ≤ Λ₀` whenever `ε ≤ σ` and `λ₀ ≤ Λ₀`. -/
theorem force_normalized_bound
    {lam : ℕ → ℝ} {κ ε σ lamZero LamZero : ℝ}
    (hκ : 0 < κ) (hκle : κ ≤ 1) (hεσ : ε ≤ σ)
    (hlamZero : 0 ≤ lamZero) (hlamZeroLam : lamZero ≤ LamZero)
    (hlam : ∀ n, 0 ≤ lam n ∧ lam n ≤ κ ^ ((n : ℝ) * σ) * lamZero) :
    ∀ n, lam n / κ ^ ((n : ℝ) * ε) ≤ LamZero := by
  intro n
  have hden : 0 < κ ^ ((n : ℝ) * ε) := by positivity
  have hexp : 0 ≤ (n : ℝ) * (σ - ε) := by
    positivity
  have hpow : κ ^ ((n : ℝ) * (σ - ε)) ≤ 1 := by
    have h := Real.rpow_le_rpow hκ.le hκle hexp
    simpa using h
  calc
    lam n / κ ^ ((n : ℝ) * ε) ≤
        (κ ^ ((n : ℝ) * σ) * lamZero) / κ ^ ((n : ℝ) * ε) :=
      div_le_div_of_nonneg_right (hlam n).2 hden.le
    _ = κ ^ ((n : ℝ) * (σ - ε)) * lamZero := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hκ.le]
      have hκpow : κ ^ ((n : ℝ) * σ) *
          κ ^ (-((n : ℝ) * ε)) = κ ^ ((n : ℝ) * (σ - ε)) := by
        rw [← Real.rpow_add hκ]
        congr 1
        ring
      calc
        κ ^ ((n : ℝ) * σ) * lamZero * κ ^ (-((n : ℝ) * ε)) =
            (κ ^ ((n : ℝ) * σ) * κ ^ (-((n : ℝ) * ε))) * lamZero := by ring
        _ = κ ^ ((n : ℝ) * (σ - ε)) * lamZero := by rw [hκpow]
    _ ≤ 1 * lamZero := mul_le_mul_of_nonneg_right hpow hlamZero
    _ ≤ LamZero := by simpa using hlamZeroLam

/-! ### Radius interpolation -/

private lemma ratio_half_le_kappa_factor {κ x : ℝ} (hκ : 0 < κ) (hκle : κ ≤ 1)
    (hx : 0 ≤ x) (hxr : x ≤ κ⁻¹) :
    x ^ (1 / 2 : ℝ) ≤ κ ^ (-4 / 3 : ℝ) := by
  have h1 : x ^ (1 / 2 : ℝ) ≤ (κ⁻¹) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hxr (by norm_num)
  have hinv : (κ⁻¹) ^ (1 / 2 : ℝ) = κ ^ (-1 / 2 : ℝ) := by
    have hbase : κ⁻¹ = κ ^ (-1 : ℝ) := by
      rw [Real.rpow_neg hκ.le]
      norm_num
    rw [hbase, ← Real.rpow_mul hκ.le]
    norm_num
  have h2 : κ ^ (-1 / 2 : ℝ) ≤ κ ^ (-4 / 3 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_ge hκ hκle (by norm_num)
  rw [hinv] at h1
  exact h1.trans h2

private lemma ratio_four_thirds_le_kappa_factor {κ x : ℝ} (hκ : 0 < κ)
    (hx : 0 ≤ x) (hxr : x ≤ κ⁻¹) :
    x ^ (4 / 3 : ℝ) ≤ κ ^ (-4 / 3 : ℝ) := by
  have h1 : x ^ (4 / 3 : ℝ) ≤ (κ⁻¹) ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hxr (by norm_num)
  have hinv : (κ⁻¹) ^ (4 / 3 : ℝ) = κ ^ (-4 / 3 : ℝ) := by
    have hbase : κ⁻¹ = κ ^ (-1 : ℝ) := by
      rw [Real.rpow_neg hκ.le]
      norm_num
    rw [hbase, ← Real.rpow_mul hκ.le]
    norm_num
  rw [hinv] at h1
  exact h1

/-- The combined quantity has the radius comparison used in the intermediate
scale step of `prop:iteration`.  The three finiteness hypotheses are the
side conditions required by the established radius monotonicity theorems. -/
theorem theta_mono_radius_of_finite
    (κ : ℝ) (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (z : ParabolicPoint) {r ρ : ℝ}
    (hκ : 0 < κ) (hκle : κ ≤ 1) (hr : 0 < r) (hrr : r ≤ ρ)
    (hsmall : κ * ρ ≤ r)
    (hα : timeSliceEnergyEssSup z.1 z.2 ρ
      (fun w => vec3EuclideanNorm (u w)) ≠ ⊤)
    (hβ : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (spatialGradientSq u Du w)) ≠ ⊤)
    (hδ : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≠ ⊤) :
    theta κ u Du p z r ≤ κ ^ (-4 / 3 : ℝ) * theta κ u Du p z ρ := by
  have hρ : 0 < ρ := lt_of_lt_of_le hr hrr
  have hratio : 0 ≤ ρ / r := div_nonneg hρ.le hr.le
  have hratio_le : ρ / r ≤ κ⁻¹ := by
    apply (div_le_iff₀ hr).2
    calc
      ρ = κ⁻¹ * (κ * ρ) := by field_simp
      _ ≤ κ⁻¹ * r := mul_le_mul_of_nonneg_left hsmall (inv_nonneg.mpr hκ.le)
  have ha := alpha_mono_radius u z hr hrr hα
  have hb := beta_mono_radius u Du z hr hrr hβ
  have hd := delta_sq_mono_radius p z hr hrr hδ
  have hαfactor : (ρ / r) ^ (1 / 2 : ℝ) ≤ κ ^ (-4 / 3 : ℝ) :=
    ratio_half_le_kappa_factor hκ hκle hratio hratio_le
  have hδfactor : (ρ / r) ^ (4 / 3 : ℝ) ≤ κ ^ (-4 / 3 : ℝ) :=
    ratio_four_thirds_le_kappa_factor hκ hratio hratio_le
  have hαρ : 0 ≤ alpha u z ρ := by
    unfold alpha
    positivity
  have hβρ : 0 ≤ beta u Du z ρ := by
    unfold beta
    positivity
  have hα' : alpha u z r ≤ κ ^ (-4 / 3 : ℝ) * alpha u z ρ :=
    ha.trans (mul_le_mul_of_nonneg_right hαfactor hαρ)
  have hβ' : beta u Du z r ≤ κ ^ (-4 / 3 : ℝ) * beta u Du z ρ :=
    hb.trans (mul_le_mul_of_nonneg_right hαfactor hβρ)
  have hδ' : κ ^ (-4 : ℝ) * delta p z r ^ 2 ≤
      κ ^ (-4 / 3 : ℝ) * (κ ^ (-4 : ℝ) * delta p z ρ ^ 2) := by
    calc
      κ ^ (-4 : ℝ) * delta p z r ^ 2 ≤
          κ ^ (-4 : ℝ) * ((ρ / r) ^ (4 / 3 : ℝ) * delta p z ρ ^ 2) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ κ ^ (-4 : ℝ) * (κ ^ (-4 / 3 : ℝ) * delta p z ρ ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hδfactor (sq_nonneg _)) (by positivity)
      _ = κ ^ (-4 / 3 : ℝ) * (κ ^ (-4 : ℝ) * delta p z ρ ^ 2) := by ring
  unfold theta at *
  calc
    alpha u z r + beta u Du z r + κ ^ (-4 : ℝ) * delta p z r ^ 2 ≤
        κ ^ (-4 / 3 : ℝ) * alpha u z ρ +
          κ ^ (-4 / 3 : ℝ) * beta u Du z ρ +
          κ ^ (-4 / 3 : ℝ) * (κ ^ (-4 : ℝ) * delta p z ρ ^ 2) :=
      add_le_add (add_le_add hα' hβ') hδ'
    _ = κ ^ (-4 / 3 : ℝ) *
        (alpha u z ρ + beta u Du z ρ + κ ^ (-4 : ℝ) * delta p z ρ ^ 2) := by ring

private lemma scale_power_bound {κ ε r r₅ : ℝ} {n : ℕ}
    (hκ : 0 < κ) (hε : 0 < ε) (hr : 0 < r) (hr₅ : 0 < r₅)
    (hinterval : κ ^ (n + 1) * r₅ < r) :
    κ ^ ((n : ℝ) * ε) ≤ κ ^ (-ε) * r₅ ^ (-ε) * r ^ ε := by
  have hκn : 0 < κ ^ n := pow_pos hκ n
  have hden : 0 < κ * r₅ := mul_pos hκ hr₅
  have hpowlt : κ ^ n < r / (κ * r₅) := by
    apply (lt_div_iff₀ hden).2
    calc
      κ ^ n * (κ * r₅) = κ ^ (n + 1) * r₅ := by
        rw [pow_succ]
        ring
      _ < r := hinterval
  have hpowr : (κ ^ n) ^ ε < (r / (κ * r₅)) ^ ε :=
    Real.rpow_lt_rpow (by positivity) hpowlt hε
  have hleft : (κ ^ n) ^ ε = κ ^ ((n : ℝ) * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
  have hright : (r / (κ * r₅)) ^ ε =
      κ ^ (-ε) * r₅ ^ (-ε) * r ^ ε := by
    rw [Real.div_rpow hr.le hden.le]
    rw [div_eq_mul_inv, ← Real.rpow_neg hden.le]
    rw [Real.mul_rpow hκ.le hr₅.le]
    ring
  calc
    κ ^ ((n : ℝ) * ε) = (κ ^ n) ^ ε := hleft.symm
    _ ≤ (r / (κ * r₅)) ^ ε := hpowr.le
    _ = κ ^ (-ε) * r₅ ^ (-ε) * r ^ ε := hright

/-- The intermediate-scale estimate of `prop:iteration`, for a supplied index
`n` satisfying `κ^(n+1) r₅ < r ≤ κ^n r₅`. -/
theorem theta_intermediate_scale_bound
    (κ ε η r₅ r : ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
    (z : ParabolicPoint) {n : ℕ}
    (hκ : 0 < κ) (hκle : κ ≤ 1) (hε : 0 < ε) (hη : 0 ≤ η)
    (hr₅ : 0 < r₅) (hr : 0 < r)
    (hinterval₁ : κ ^ (n + 1) * r₅ < r)
    (hinterval₂ : r ≤ κ ^ n * r₅)
    (hdisc : theta κ u Du p z (κ ^ n * r₅) ≤ η * κ ^ ((n : ℝ) * ε))
    (hα : timeSliceEnergyEssSup z.1 z.2 (κ ^ n * r₅)
      (fun w => vec3EuclideanNorm (u w)) ≠ ⊤)
    (hβ : (∫⁻ w in parabolicCylinder z.1 z.2 (κ ^ n * r₅),
      ENNReal.ofReal (spatialGradientSq u Du w)) ≠ ⊤)
    (hδ : (∫⁻ w in parabolicCylinder z.1 z.2 (κ ^ n * r₅),
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≠ ⊤) :
    max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
        theta κ u Du p z r ∧
      theta κ u Du p z r ≤
        κ ^ (-4 / 3 - ε) * η * r₅ ^ (-ε) * r ^ ε := by
  have hκn : 0 < κ ^ n := pow_pos hκ n
  have hρ : 0 < κ ^ n * r₅ := mul_pos hκn hr₅
  have hrr : r ≤ κ ^ n * r₅ := hinterval₂
  have hsmall : κ * (κ ^ n * r₅) ≤ r := by
    calc
      κ * (κ ^ n * r₅) = κ ^ (n + 1) * r₅ := by
        rw [pow_succ]
        ring
      _ ≤ r := hinterval₁.le
  have hmono := theta_mono_radius_of_finite κ u Du p z hκ hκle hr hrr hsmall hα hβ hδ
  have hscale := scale_power_bound hκ hε hr hr₅ hinterval₁
  have hupper : theta κ u Du p z r ≤
      κ ^ (-4 / 3 : ℝ) * η * κ ^ ((n : ℝ) * ε) := by
    calc
      theta κ u Du p z r ≤
          κ ^ (-4 / 3 : ℝ) * theta κ u Du p z (κ ^ n * r₅) := hmono
      _ ≤ κ ^ (-4 / 3 : ℝ) * (η * κ ^ ((n : ℝ) * ε)) :=
        mul_le_mul_of_nonneg_left hdisc (by positivity)
      _ = κ ^ (-4 / 3 : ℝ) * η * κ ^ ((n : ℝ) * ε) := by ring
  have hscale' :
      κ ^ (-4 / 3 : ℝ) * η * κ ^ ((n : ℝ) * ε) ≤
        κ ^ (-4 / 3 : ℝ) * η *
          (κ ^ (-ε) * r₅ ^ (-ε) * r ^ ε) := by
    calc
      κ ^ (-4 / 3 : ℝ) * η * κ ^ ((n : ℝ) * ε) =
          κ ^ (-4 / 3 : ℝ) * (η * κ ^ ((n : ℝ) * ε)) := by ring
      _ ≤ κ ^ (-4 / 3 : ℝ) *
          (η * (κ ^ (-ε) * r₅ ^ (-ε) * r ^ ε)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hscale hη) (by positivity)
      _ = κ ^ (-4 / 3 : ℝ) * η *
          (κ ^ (-ε) * r₅ ^ (-ε) * r ^ ε) := by ring
  have hupper' : theta κ u Du p z r ≤
      κ ^ (-4 / 3 - ε) * η * r₅ ^ (-ε) * r ^ ε := by
    calc
      theta κ u Du p z r ≤
          κ ^ (-4 / 3 : ℝ) * η * κ ^ ((n : ℝ) * ε) := hupper
      _ ≤ κ ^ (-4 / 3 : ℝ) * η *
          (κ ^ (-ε) * r₅ ^ (-ε) * r ^ ε) := hscale'
      _ = κ ^ (-4 / 3 - ε) * η * r₅ ^ (-ε) * r ^ ε := by
        have hκpow : κ ^ (-4 / 3 : ℝ) * κ ^ (-ε) =
            κ ^ (-4 / 3 - ε) := by
          rw [← Real.rpow_add hκ]
          congr 1
        calc
          κ ^ (-4 / 3 : ℝ) * η *
              (κ ^ (-ε) * r₅ ^ (-ε) * r ^ ε) =
              (κ ^ (-4 / 3 : ℝ) * κ ^ (-ε)) * η *
                r₅ ^ (-ε) * r ^ ε := by ring
          _ = κ ^ (-4 / 3 - ε) * η * r₅ ^ (-ε) * r ^ ε := by rw [hκpow]
  have hαnonneg : 0 ≤ alpha u z r := by
    unfold alpha
    positivity
  have hβnonneg : 0 ≤ beta u Du z r := by
    unfold beta
    positivity
  have hδnonneg : 0 ≤ delta p z r ^ 2 := sq_nonneg _
  have hκfactor : 1 ≤ κ ^ (-4 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_ge hκ hκle (by norm_num : (-4 : ℝ) ≤ 0)
    simpa using this
  have hpressure : delta p z r ^ 2 ≤ κ ^ (-4 : ℝ) * delta p z r ^ 2 := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hκfactor hδnonneg)
  have hαtheta : alpha u z r ≤ theta κ u Du p z r := by
    unfold theta
    nlinarith only [hβnonneg, hpressure]
  have hβtheta : beta u Du z r ≤ theta κ u Du p z r := by
    unfold theta
    nlinarith only [hαnonneg, hpressure]
  have hδtheta : delta p z r ^ 2 ≤ theta κ u Du p z r := by
    unfold theta
    nlinarith only [hαnonneg, hβnonneg, hpressure]
  exact ⟨max_le (max_le hαtheta hβtheta) hδtheta, hupper'⟩

end CKN
