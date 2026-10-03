/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.AboveTwo

/-!
# Scalar two-level geometric amortization for the guarded controller

These lemmas are deliberately independent of the executable controller.  They
are the numerical engine used below: an inner radius-doubling geometric sum is
paid by its last radius, and the outer scale-doubling sum is paid by its last
scale.  In particular no estimate of the form "number of trials times the
last trial" occurs.
-/

public section

namespace O3

/-- The exponent in all three wrapper regimes is strictly positive. -/
noncomputable def WrapperExponent (p : ℝ) : ℝ :=
  if p ≤ 2 then (1 / 2 : ℝ) else aboveAlpha p

theorem wrapperExponent_pos {p : ℝ} :
    0 < WrapperExponent p := by
  unfold WrapperExponent
  split_ifs with h
  · norm_num
  · exact aboveAlpha_pos (lt_of_not_ge h)

/-- A convenient geometric-amortization coefficient. -/
noncomputable def geometricAmortizationConstant (a : ℝ) : ℝ :=
  (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)

theorem two_rpow_gt_one {a : ℝ} (ha : 0 < a) :
    1 < (2 : ℝ) ^ a := by
  exact (Real.one_lt_rpow (by norm_num) ha)

theorem geometricAmortizationConstant_pos {a : ℝ} (ha : 0 < a) :
    0 < geometricAmortizationConstant a := by
  unfold geometricAmortizationConstant
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (sub_pos.mpr (two_rpow_gt_one ha))

/-- Exact finite inner geometric summation, expressed through its endpoint. -/
theorem radius_geometric_sum_le_endpoint {a beta : ℝ}
    (ha : 0 < a) (hbeta : 0 ≤ beta) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j * beta) ^ a ≤
      geometricAmortizationConstant a * (((2 : ℝ) ^ J * beta) ^ a) := by
  by_cases hb : beta = 0
  · subst beta
    simp [Real.zero_rpow ha.ne']
  have hbetaPos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hb)
  have hratio : 1 < (2 : ℝ) ^ a := two_rpow_gt_one ha
  have hbetaPow : 0 ≤ beta ^ a := Real.rpow_nonneg hbeta _
  have hrewrite :
      ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j * beta) ^ a =
        ∑ j ∈ Finset.range (J + 1), beta ^ a * ((2 : ℝ) ^ a) ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.mul_rpow (pow_nonneg (by norm_num) _) hbeta]
    rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) a j]
    ring
  rw [hrewrite]
  have hgeom := aboveGeometricSum_le hbetaPow hratio (J + 1)
  have hend : (((2 : ℝ) ^ J * beta) ^ a) =
      beta ^ a * ((2 : ℝ) ^ a) ^ J := by
    rw [Real.mul_rpow (pow_nonneg (by norm_num) _) hbeta]
    rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) a J]
    ring
  unfold geometricAmortizationConstant
  rw [hend]
  calc
    ∑ j ∈ Finset.range (J + 1), beta ^ a * ((2 : ℝ) ^ a) ^ j
        ≤ beta ^ a * ((2 : ℝ) ^ a) ^ (J + 1) /
            ((2 : ℝ) ^ a - 1) := hgeom
    _ = (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) *
          (beta ^ a * ((2 : ℝ) ^ a) ^ J) := by rw [pow_succ]; ring

/-- The same genuine geometric sum across scale epochs. -/
theorem scale_geometric_sum_le_endpoint {a k0 : ℝ}
    (ha : 0 < a) (hk0 : 0 ≤ k0) (S : ℕ) :
    ∑ s ∈ Finset.range (S + 1), (((2 : ℝ) ^ s * k0) ^ a) ≤
      geometricAmortizationConstant a * (((2 : ℝ) ^ S * k0) ^ a) :=
  radius_geometric_sum_le_endpoint ha hk0 S

/-- The square-root cost weight used in the Euclidean controller analysis. -/
@[expose] noncomputable def euclideanWrapperWeight (x : ℝ) : ℝ := Real.sqrt x
/-- The power-law cost weight used for exponents above two. -/
@[expose] noncomputable def aboveWrapperWeight (a x : ℝ) : ℝ := x ^ a
/-- The square-root logarithmic cost weight used for exponents below two. -/
@[expose] noncomputable def belowWrapperWeight (x : ℝ) : ℝ :=
  Real.sqrt x * Real.log (Real.exp 1 + x)

end O3
