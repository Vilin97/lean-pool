/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.BetheBisection
public import LeanPool.BeyondBethe.BeyondBethe.DirectedCertificateValue
public import Mathlib.Tactic

/-! # Explicit Optimizer Scales -/

@[expose] public section

namespace BeyondBethe

/-!
# Explicit dyadic scales for the numerical optimizer

All parameters are rational functions of the normalized positive input and
the fixed structural error budget.  Their deliberately generous slack keeps
the later objective-to-KKT calculation transparent.
-/

/-- Half the numerical interior floor at the matrix dimension, entry bit bound, and
regularization scale. -/
def explicitOptimizerFloor {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : ℚ :=
  numericalInteriorFloor (m + 1) (rationalMatrixEntryBitBound A)
      (explicitRegularizationScale (m + 1)) / 2

/-- The optimizer distance scale: the coordinate floor times the KKT error allowance, divided by
48. -/
def explicitOptimizerRho {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : ℚ :=
  explicitOptimizerFloor A * explicitKKTError / 48

/-- The optimizer objective gap: one quarter of the regularization scale times the squared
distance scale. -/
def explicitOptimizerGap {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : ℚ :=
  explicitRegularizationScale (m + 1) * explicitOptimizerRho A ^ 2 / 4

/-- The mixing weight capped at one half and scaled by the objective gap and regularized
objective range. -/
def explicitOptimizerMix {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : ℚ :=
  min (1 / 2)
    (explicitOptimizerGap A /
      (4 * (rationalRegularizedObjectiveRange A + 1)))

/-- The optimizer inner radius, equal to the mixing weight divided by twice the matrix
dimension. -/
def explicitOptimizerInnerRadius {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : ℚ :=
  explicitOptimizerMix A / (2 * (m + 1))

/-- The evaluation precision budget from the encoded gap and KKT allowance, with
dimension-dependent slack. -/
def explicitOptimizerPrecision {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : ℕ :=
  encodedBitLength ℚ (explicitOptimizerGap A) +
    encodedBitLength ℚ explicitKKTError + 2 * (m + 1) + 10

/-- The width of the explicit initial Bethe bisection interval. -/
def explicitOptimizerInitialWidth {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : ℚ :=
  betheBisectionInitialHigh A (explicitOptimizerMix A)
      (explicitOptimizerInnerRadius A) -
    betheNegativeObjectiveLower m

/-- The bisection iteration count from the encoded initial width and target gap, with three
extra steps. -/
def explicitOptimizerBisectionSteps {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : ℕ :=
  encodedBitLength ℚ (explicitOptimizerInitialWidth A) +
    encodedBitLength ℚ (explicitOptimizerGap A) + 3

theorem explicitOptimizerFloor_pos {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    0 < explicitOptimizerFloor A := by
  rw [explicitOptimizerFloor]
  exact div_pos (numericalInteriorFloor_pos _ _ _) (by norm_num)

theorem explicitOptimizerRho_pos {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    0 < explicitOptimizerRho A := by
  rw [explicitOptimizerRho]
  exact div_pos
    (mul_pos (explicitOptimizerFloor_pos A) explicitKKTError_pos)
    (by norm_num)

theorem explicitOptimizerGap_pos {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    0 < explicitOptimizerGap A := by
  rw [explicitOptimizerGap]
  exact div_pos
    (mul_pos (explicitRegularizationScale_pos (by omega))
      (sq_pos_of_pos (explicitOptimizerRho_pos A))) (by norm_num)

theorem explicitOptimizerMix_pos {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    0 < explicitOptimizerMix A := by
  rw [explicitOptimizerMix, lt_min_iff]
  exact ⟨by norm_num, div_pos (explicitOptimizerGap_pos A) (by
    have h := rationalRegularizedObjectiveRange_nonneg A
    positivity)⟩

theorem explicitOptimizerMix_le_half {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    explicitOptimizerMix A ≤ 1 / 2 := by
  rw [explicitOptimizerMix]
  exact min_le_left _ _

theorem explicitOptimizerMix_le_one {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    explicitOptimizerMix A ≤ 1 :=
  (explicitOptimizerMix_le_half A).trans (by norm_num)

theorem explicitOptimizerInnerRadius_pos {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    0 < explicitOptimizerInnerRadius A := by
  rw [explicitOptimizerInnerRadius]
  exact div_pos (explicitOptimizerMix_pos A) (by positivity)

theorem explicitOptimizerFloor_le_smoothedFloor {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    explicitOptimizerFloor A ≤
      (1 - explicitOptimizerMix A) *
        numericalInteriorFloor (m + 1) (rationalMatrixEntryBitBound A)
          (explicitRegularizationScale (m + 1)) := by
  let δ0 := numericalInteriorFloor (m + 1)
    (rationalMatrixEntryBitBound A) (explicitRegularizationScale (m + 1))
  have hδ0 : 0 ≤ δ0 :=
    (numericalInteriorFloor_pos _ _ _).le
  have hmix := explicitOptimizerMix_le_half A
  rw [explicitOptimizerFloor]
  nlinarith

theorem explicitOptimizerInnerRadius_div_mix {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    explicitOptimizerInnerRadius A / explicitOptimizerMix A =
      1 / (2 * (m + 1) : ℚ) := by
  rw [explicitOptimizerInnerRadius]
  field_simp [(explicitOptimizerMix_pos A).ne']

theorem explicitOptimizerInnerRadius_spike {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    explicitOptimizerInnerRadius A / explicitOptimizerMix A ≤
      1 / (m + 1 : ℚ) := by
  rw [explicitOptimizerInnerRadius_div_mix]
  have hn : (0 : ℚ) < m + 1 := by positivity
  exact one_div_le_one_div_of_le hn (by nlinarith)

theorem explicitOptimizerRho_ratio {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    12 * explicitOptimizerRho A / explicitOptimizerFloor A =
      explicitKKTError / 4 := by
  rw [explicitOptimizerRho]
  field_simp [(explicitOptimizerFloor_pos A).ne']
  ring

theorem explicitOptimizerGap_scale {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    4 * explicitOptimizerGap A =
      explicitRegularizationScale (m + 1) * explicitOptimizerRho A ^ 2 := by
  rw [explicitOptimizerGap]
  ring

/-- The barycentric smoothing and inner-radius terms consume at most one
quarter of the objective-gap budget. -/
theorem explicitOptimizerSmoothingSlack_le {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    betheSmoothingSlack A (explicitOptimizerMix A)
        (explicitOptimizerInnerRadius A) ≤
      explicitOptimizerGap A / 4 := by
  let range := rationalRegularizedObjectiveRange A
  let mix := explicitOptimizerMix A
  have hrange : 0 ≤ range := rationalRegularizedObjectiveRange_nonneg A
  have hmix0 : 0 ≤ mix := (explicitOptimizerMix_pos A).le
  have hmixBound : mix ≤ explicitOptimizerGap A /
      (4 * (range + 1)) := by
    dsimp only [mix, range]
    rw [explicitOptimizerMix]
    exact min_le_right _ _
  have hn : (1 : ℚ) ≤ m + 1 := by exact_mod_cast (show 1 ≤ m + 1 by omega)
  have hradius : 2 * explicitOptimizerInnerRadius A ≤ mix := by
    rw [explicitOptimizerInnerRadius]
    have hden : (0 : ℚ) < 2 * (m + 1) := by positivity
    rw [div_eq_mul_inv]
    have hinv : (2 * (m + 1) : ℚ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  have hcombine : mix * range + 2 * explicitOptimizerInnerRadius A ≤
      mix * (range + 1) := by
    nlinarith
  have hdenpos : 0 < 4 * (range + 1) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hmixBound (by
    positivity : (0 : ℚ) ≤ range + 1)
  have hcancel : explicitOptimizerGap A / (4 * (range + 1)) *
      (range + 1) = explicitOptimizerGap A / 4 := by
    field_simp [show range + 1 ≠ 0 by positivity]
  rw [hcancel] at hscaled
  rw [betheSmoothingSlack]
  simpa only [mix, range] using hcombine.trans hscaled

theorem explicitOptimizerInitialWidth_pos {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    0 < explicitOptimizerInitialWidth A := by
  rw [explicitOptimizerInitialWidth, betheBisectionInitialHigh,
    betheNegativeObjectiveUpper, betheNegativeObjectiveLower]
  have hslack : 0 < betheSmoothingSlack A (explicitOptimizerMix A)
      (explicitOptimizerInnerRadius A) := by
    rw [betheSmoothingSlack]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (explicitOptimizerMix_pos A).le
        (rationalRegularizedObjectiveRange_nonneg A))
      (mul_pos (by norm_num) (explicitOptimizerInnerRadius_pos A))
  have hB : (0 : ℚ) ≤ rationalMatrixEntryBitBound A := by positivity
  have hn : (0 : ℚ) < m + 1 := by positivity
  push_cast
  nlinarith

/-- The precision exponent contains enough dyadic shift to absorb the
dimension factor in objective evaluation. -/
theorem explicitOptimizerPrecision_scaled_lt_gap {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    (2 : ℚ) ^ (2 * (m + 1) + 10) *
        (1 / 2 : ℚ) ^ explicitOptimizerPrecision A <
      explicitOptimizerGap A := by
  let Lg := encodedBitLength ℚ (explicitOptimizerGap A)
  let Le := encodedBitLength ℚ explicitKKTError
  let K := 2 * (m + 1) + 10
  have hgap := dyadic_encodedBitLength_lt_positive_rational
    (explicitOptimizerGap_pos A)
  have he : (1 / 2 : ℚ) ^ Le ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hcancel : (2 : ℚ) ^ K * (1 / 2 : ℚ) ^ K = 1 := by
    rw [← mul_pow]
    norm_num
  have hsplit : (1 / 2 : ℚ) ^ (Lg + Le + K) =
      (1 / 2 : ℚ) ^ Lg * (1 / 2 : ℚ) ^ Le *
        (1 / 2 : ℚ) ^ K := by
    rw [pow_add, pow_add]
  calc
    (2 : ℚ) ^ (2 * (m + 1) + 10) *
        (1 / 2 : ℚ) ^ explicitOptimizerPrecision A =
      (1 / 2 : ℚ) ^ Lg * (1 / 2 : ℚ) ^ Le := by
        rw [show 2 * (m + 1) + 10 = K by rfl]
        rw [show explicitOptimizerPrecision A = Lg + Le + K by
          simp only [explicitOptimizerPrecision, Lg, Le, K]; omega]
        rw [hsplit]
        rw [show
          (2 : ℚ) ^ K *
              ((1 / 2 : ℚ) ^ Lg * (1 / 2 : ℚ) ^ Le *
                (1 / 2 : ℚ) ^ K) =
            ((1 / 2 : ℚ) ^ Lg * (1 / 2 : ℚ) ^ Le) *
              ((2 : ℚ) ^ K * (1 / 2 : ℚ) ^ K) by ring,
          hcancel, mul_one]
    _ ≤ (1 / 2 : ℚ) ^ Lg :=
      mul_le_of_le_one_right (by positivity) he
    _ < explicitOptimizerGap A := by simpa only [Lg] using hgap

/-- Independently, the same precision exponent absorbs the fixed KKT error
scale. -/
theorem explicitOptimizerPrecision_scaled_lt_kktError {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    (2 : ℚ) ^ 10 *
        (1 / 2 : ℚ) ^ explicitOptimizerPrecision A <
      explicitKKTError := by
  let Lg := encodedBitLength ℚ (explicitOptimizerGap A)
  let Le := encodedBitLength ℚ explicitKKTError
  let K := 2 * (m + 1)
  have herr := dyadic_encodedBitLength_lt_positive_rational
    explicitKKTError_pos
  have hg : (1 / 2 : ℚ) ^ Lg ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hk : (1 / 2 : ℚ) ^ K ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hcancel : (2 : ℚ) ^ 10 * (1 / 2 : ℚ) ^ 10 = 1 := by
    rw [← mul_pow]
    norm_num
  have hsplit : (1 / 2 : ℚ) ^ (Lg + Le + K + 10) =
      ((1 / 2 : ℚ) ^ Lg * (1 / 2 : ℚ) ^ Le *
        (1 / 2 : ℚ) ^ K) * (1 / 2 : ℚ) ^ 10 := by
    rw [pow_add, pow_add, pow_add]
  calc
    (2 : ℚ) ^ 10 *
        (1 / 2 : ℚ) ^ explicitOptimizerPrecision A =
      (1 / 2 : ℚ) ^ Lg * (1 / 2 : ℚ) ^ Le *
        (1 / 2 : ℚ) ^ K := by
        rw [show explicitOptimizerPrecision A = Lg + Le + K + 10 by
          simp only [explicitOptimizerPrecision, Lg, Le, K]]
        rw [hsplit]
        rw [show (2 : ℚ) ^ 10 *
            (((1 / 2 : ℚ) ^ Lg * (1 / 2 : ℚ) ^ Le *
              (1 / 2 : ℚ) ^ K) * (1 / 2 : ℚ) ^ 10) =
          ((1 / 2 : ℚ) ^ Lg * (1 / 2 : ℚ) ^ Le *
            (1 / 2 : ℚ) ^ K) *
              ((2 : ℚ) ^ 10 * (1 / 2 : ℚ) ^ 10) by ring,
          hcancel, mul_one]
    _ ≤ (1 / 2 : ℚ) ^ Le := by
      have hnonneg : 0 ≤ (1 / 2 : ℚ) ^ Le := by positivity
      calc
        (1 / 2 : ℚ) ^ Lg * (1 / 2 : ℚ) ^ Le *
            (1 / 2 : ℚ) ^ K ≤
          1 * (1 / 2 : ℚ) ^ Le * 1 := by gcongr
        _ = (1 / 2 : ℚ) ^ Le := by ring
    _ < explicitKKTError := by simpa only [Le] using herr

theorem explicitOptimizerGradientEvaluationError_le {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    4 * (1 / 2 : ℚ) ^ explicitOptimizerPrecision A ≤
      explicitKKTError / 256 := by
  have hscaled := explicitOptimizerPrecision_scaled_lt_kktError A
  norm_num at hscaled
  linarith

/-- The full one-sided objective-evaluation loss uses at most one quarter of
the objective-gap budget. -/
theorem explicitOptimizerObjectiveEvaluationError_lt {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    betheObjectiveEvaluationError m (explicitOptimizerPrecision A) <
      explicitOptimizerGap A / 4 := by
  let n := m + 1
  let coeff : ℕ := 16 * m ^ 2 + 3 * n ^ 2
  have hmn : m ≤ n := by omega
  have hnpow : n ≤ 2 ^ n := n.lt_two_pow_self.le
  have hn2 : n ^ 2 ≤ 2 ^ (2 * n) := by
    calc
      n ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hnpow 2
      _ = 2 ^ (2 * n) := by
        rw [← pow_mul]
        congr 1
        omega
  have hcoeff : 4 * coeff ≤ 2 ^ (2 * n + 10) := by
    calc
      4 * coeff ≤ 76 * n ^ 2 := by
        dsimp only [coeff, n]
        nlinarith
      _ ≤ 76 * 2 ^ (2 * n) := Nat.mul_le_mul_left 76 hn2
      _ ≤ 1024 * 2 ^ (2 * n) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (2 * n + 10) := by
        rw [pow_add]
        norm_num
        ring
  have hcoeffQ : (4 : ℚ) * coeff ≤
      (2 : ℚ) ^ (2 * (m + 1) + 10) := by
    exact_mod_cast hcoeff
  have hdyadic : 0 ≤
      (1 / 2 : ℚ) ^ explicitOptimizerPrecision A := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hcoeffQ hdyadic
  have hgap := explicitOptimizerPrecision_scaled_lt_gap A
  have hfour : 4 * betheObjectiveEvaluationError m
      (explicitOptimizerPrecision A) < explicitOptimizerGap A := by
    rw [betheObjectiveEvaluationError]
    have hform :
        4 * (16 * (1 / 2 : ℚ) ^ explicitOptimizerPrecision A *
              (m * m) +
            3 * (m + 1) ^ 2 *
              (1 / 2 : ℚ) ^ explicitOptimizerPrecision A) =
          (4 : ℚ) * coeff *
            (1 / 2 : ℚ) ^ explicitOptimizerPrecision A := by
      dsimp only [coeff, n]
      push_cast
      ring
    rw [hform]
    exact hscaled.trans_lt hgap
  linarith

/-- The encoded-length bisection depth leaves less than one eighth of the
objective-gap budget. -/
theorem explicitOptimizerBisectionWidth_lt {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    explicitOptimizerInitialWidth A /
        2 ^ explicitOptimizerBisectionSteps A <
      explicitOptimizerGap A / 8 := by
  let W := explicitOptimizerInitialWidth A
  let g := explicitOptimizerGap A
  let LW := encodedBitLength ℚ W
  let Lg := encodedBitLength ℚ g
  have hW := positive_rational_lt_two_pow_encodedBitLength
    (explicitOptimizerInitialWidth_pos A)
  have hg := dyadic_encodedBitLength_lt_positive_rational
    (explicitOptimizerGap_pos A)
  have hdyadic : 0 < (1 / 2 : ℚ) ^ (Lg + 3) := by positivity
  have hdirect : W / 2 ^ (LW + Lg + 3) <
      (1 / 2 : ℚ) ^ Lg / 8 := by
    have hcancelLW : (2 : ℚ) ^ LW * (1 / 2 : ℚ) ^ LW = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      W / 2 ^ (LW + Lg + 3) =
          W * (1 / 2 : ℚ) ^ (LW + Lg + 3) := by
        simp [div_eq_mul_inv, one_div, inv_pow]
      _ < (2 : ℚ) ^ LW *
          (1 / 2 : ℚ) ^ (LW + Lg + 3) := by
        exact mul_lt_mul_of_pos_right hW (by positivity)
      _ = (1 / 2 : ℚ) ^ Lg / 8 := by
        rw [show LW + Lg + 3 = LW + (Lg + 3) by omega, pow_add]
        rw [show (2 : ℚ) ^ LW *
            ((1 / 2 : ℚ) ^ LW * (1 / 2 : ℚ) ^ (Lg + 3)) =
          ((2 : ℚ) ^ LW * (1 / 2 : ℚ) ^ LW) *
            (1 / 2 : ℚ) ^ (Lg + 3) by ring,
          hcancelLW, one_mul]
        rw [pow_add]
        norm_num
        ring
  rw [explicitOptimizerBisectionSteps]
  simpa only [W, g, LW, Lg] using hdirect.trans
    (div_lt_div_of_pos_right hg (by norm_num))

/-- Summing all three objective losses still stays below the chosen strong
concavity budget. -/
theorem explicitOptimizerTotalObjectiveError_lt {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    betheSmoothingSlack A (explicitOptimizerMix A)
        (explicitOptimizerInnerRadius A) +
      explicitOptimizerInitialWidth A /
        2 ^ explicitOptimizerBisectionSteps A +
      betheObjectiveEvaluationError m (explicitOptimizerPrecision A) <
        explicitOptimizerGap A := by
  have hs := explicitOptimizerSmoothingSlack_le A
  have hw := explicitOptimizerBisectionWidth_lt A
  have he := explicitOptimizerObjectiveEvaluationError_lt A
  have hg := explicitOptimizerGap_pos A
  linarith

/-- The gradient-evaluation and objective-proximity losses fit inside the
fixed approximate-KKT allowance. -/
theorem explicitOptimizerKKTError_le {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    4 * (1 / 2 : ℚ) ^ explicitOptimizerPrecision A +
        4 * (4 * (1 / 2 : ℚ) ^ explicitOptimizerPrecision A +
          3 * explicitOptimizerRho A / explicitOptimizerFloor A) ≤
      explicitKKTError := by
  have he := explicitOptimizerGradientEvaluationError_le A
  have hratio := explicitOptimizerRho_ratio A
  have hε := explicitKKTError_pos
  calc
    4 * (1 / 2 : ℚ) ^ explicitOptimizerPrecision A +
          4 * (4 * (1 / 2 : ℚ) ^ explicitOptimizerPrecision A +
            3 * explicitOptimizerRho A / explicitOptimizerFloor A) =
        5 * (4 * (1 / 2 : ℚ) ^ explicitOptimizerPrecision A) +
          12 * explicitOptimizerRho A / explicitOptimizerFloor A := by ring
    _ ≤ 5 * (explicitKKTError / 256) + explicitKKTError / 4 := by
      rw [hratio]
      gcongr
    _ ≤ explicitKKTError := by nlinarith

end BeyondBethe
