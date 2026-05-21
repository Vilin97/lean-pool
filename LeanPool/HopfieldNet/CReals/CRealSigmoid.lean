/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealExpKIndep

namespace Computable
namespace CReal

open scoped BigOperators

namespace Pre

set_option maxHeartbeats 0
/-!
## Sigmoid on small rationals

For `|x| ≤ 1/2`, define

`sigmoid(x) = 1 / (1 + exp(-x))`.

We implement this using the constructive inverse `Pre.inv` with an explicit
`InvWitness` showing the denominator is bounded away from `0`.
-/

lemma expPartial_lower_bound_at_four (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) :
    (1/16 : ℚ) ≤ expPartial (-x) 4 := by
  -- Expand the finite sum and bound the negative terms by absolute values.
  have hpoly :
      expPartial (-x) 4 =
        1 - x + x ^ 2 * (1/2 : ℚ) + x ^ 3 * (-1/6 : ℚ) + x ^ 4 * (1/24 : ℚ) := by
    -- expand the finite sum explicitly (only 5 terms)
    simp [expPartial, expCoeff, Finset.sum_range_succ]
    ring_nf
  -- Nonnegativity of the even-power terms.
  have hx2_nonneg : 0 ≤ x ^ 2 * (1/2 : ℚ) := by
    have : 0 ≤ x ^ 2 := by nlinarith
    nlinarith
  have hx4_nonneg : 0 ≤ x ^ 4 * (1/24 : ℚ) := by
    have : 0 ≤ x ^ 4 := by nlinarith
    nlinarith
  -- `1 - x ≥ 1 - |x|` since `x ≤ |x|`.
  have hx1 : 1 - x ≥ 1 - |x| := by
    have : x ≤ |x| := le_abs_self x
    linarith
  -- `x^3 * (-1/6) ≥ -( |x|^3 / 6 )`.
  have hx3_le : x ^ 3 ≤ |x| ^ 3 := by
    have h := le_abs_self (x ^ 3)
    simp only [abs_pow] at h
    exact h
  have hx3_div : x ^ 3 / (6 : ℚ) ≤ |x| ^ 3 / (6 : ℚ) :=
    div_le_div_of_nonneg_right hx3_le (by norm_num : (0 : ℚ) ≤ 6)
  have hx3_term : x ^ 3 * (-1/6 : ℚ) ≥ -(|x| ^ 3 / (6 : ℚ)) := by
    have heq : x ^ 3 * (-1/6 : ℚ) = -(x ^ 3 / (6 : ℚ)) := by ring
    have hle : -(|x| ^ 3 / (6 : ℚ)) ≤ -(x ^ 3 / (6 : ℚ)) := neg_le_neg hx3_div
    linarith
  -- Lower bound `expPartial(-x,4) ≥ 1 - |x| - |x|^3/6`.
  have hmain :
      1 - |x| - (|x| ^ 3 / (6 : ℚ)) ≤ expPartial (-x) 4 := by
    -- Use the explicit polynomial and drop nonnegative terms.
    rw [hpoly]
    linarith [hx2_nonneg, hx4_nonneg, hx1, hx3_term]
  -- Now use `|x| ≤ 1/2` to get a numerical lower bound.
  have hx' : |x| ≤ (1/2 : ℚ) := hx
  have hx3 : |x| ^ 3 ≤ (1/2 : ℚ) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg x) hx' 3
  have hx3_div' : |x| ^ 3 / (6 : ℚ) ≤ (1/2 : ℚ) ^ 3 / (6 : ℚ) :=
    div_le_div_of_nonneg_right hx3 (by norm_num : (0 : ℚ) ≤ 6)
  have hnum : 1 - (1/2 : ℚ) - ((1/2 : ℚ) ^ 3 / (6 : ℚ)) = (23/48 : ℚ) := by norm_num
  have hstep : (23/48 : ℚ) ≤ 1 - |x| - (|x| ^ 3 / (6 : ℚ)) := by
    -- monotonicity in `|x|` and `|x|^3/6`
    have : 1 - |x| - (|x| ^ 3 / (6 : ℚ)) ≥ 1 - (1/2 : ℚ) - ((1/2 : ℚ) ^ 3 / (6 : ℚ)) := by
      linarith [hx', hx3_div']
    linarith [this, hnum]
  have h16 : (1/16 : ℚ) ≤ (23/48 : ℚ) := by norm_num
  -- combine
  exact _root_.le_trans h16 (_root_.le_trans hstep hmain)

/-- Denominator pre-real for sigmoid: `1 + exp(-x)` (using the small-exp approximant). -/
def sigmoidDenomPre (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) : CReal.Pre :=
  CReal.Pre.add CReal.Pre.one (small_exp (-x) (by simpa [abs_neg] using hx))

def sigmoidDenom_witness (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) :
    CReal.Pre.InvWitness (sigmoidDenomPre x hx) := by
  -- take `N = 0`, so we need `1 < |approx 1|`
  refine ⟨0, ?_⟩
  -- `sigmoidDenomPre.approx 1 = 1 + expPartial (-x) 4`
  have hx' : |x| ≤ (1/2 : ℚ) := hx
  have hden :
      (sigmoidDenomPre x hx).approx 1 = 1 + expPartial (-x) (expTruncLevel 2) := by
    -- `Pre.add` shifts by `+1`; `small_exp` uses `expTruncLevel`.
    simp [sigmoidDenomPre, CReal.Pre.add, CReal.Pre.one, small_exp, expTruncLevel]
  -- `expTruncLevel 2 = 4`
  have hTL : expTruncLevel 2 = 4 := by simp [expTruncLevel]
  have hexp : (1/16 : ℚ) ≤ expPartial (-x) (expTruncLevel 2) := by
    -- rewrite to the `N=4` lemma
    simpa [hTL] using expPartial_lower_bound_at_four x hx'
  have hpos : (1 : ℚ) < |(sigmoidDenomPre x hx).approx (0 + 1)| := by
    -- `approx 1 ≥ 1 + 1/16 = 17/16`
    have hge : (17/16 : ℚ) ≤ (sigmoidDenomPre x hx).approx 1 := by
      have : (17/16 : ℚ) = 1 + (1/16 : ℚ) := by norm_num
      -- from `expPartial ≥ 1/16`
      rw [hden, hTL] at *
      linarith [hexp, this]
    have hge0 : 0 ≤ (sigmoidDenomPre x hx).approx 1 := _root_.le_trans (by norm_num) hge
    have habs : |(sigmoidDenomPre x hx).approx 1| = (sigmoidDenomPre x hx).approx 1 :=
      abs_of_nonneg hge0
    -- strict
    have : (1 : ℚ) < (sigmoidDenomPre x hx).approx 1 := lt_of_lt_of_le (by norm_num) hge
    simpa [habs] using this
  simpa using hpos

/-- Pre-level sigmoid for small rationals. -/
def small_sigmoid (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) : CReal.Pre :=
  CReal.Pre.inv (sigmoidDenomPre x hx) (sigmoidDenom_witness x hx)

end Pre

/-- Sigmoid on rationals for `|x| ≤ 1/2`. -/
def sigmoidRatSmall (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) : CReal :=
  ⟦Pre.small_sigmoid x hx⟧


end CReal
end Computable
