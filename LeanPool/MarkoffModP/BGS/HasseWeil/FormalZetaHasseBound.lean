/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaTrace

/-!
# The Hasse bound from formal zeta rationality

This module records the final analytic composition in the zeta-function
route.  Once the canonical formal point-count zeta series has curve-rational
form with numerator `P`, and the point-count error over the even extensions
has square-root growth, the base-field Hasse bound follows with coefficient
`P.natDegree`.

The two hypotheses are deliberately explicit.  In particular, this theorem
does not construct the zeta numerator or prove the geometric extension-point
estimate.
-/

namespace BGS.HasseWeil

open Filter Asymptotics

noncomputable section

/-- Formal point-count zeta rationality and a two-sided square-root estimate
over the even extensions imply the base-field Hasse bound. -/
theorem abs_pointCount_sub_card_sub_one_le_of_formalPointCountZeta_rational_and_evenError_isBigO
    (q : ℕ) (pointCount : ℕ → ℕ) (P : Polynomial ℂ)
    (hP0 : P.coeff 0 = 1)
    (hrational :
      HasCurveZetaRationalForm (formalPointCountZeta pointCount) q P)
    (herror :
      (fun n : ℕ ↦
        (pointCount (2 * n) : ℂ) - (q : ℂ) ^ (2 * n) - 1) =O[atTop]
          fun n : ℕ ↦ (q : ℝ) ^ n) :
    |(pointCount 1 : ℝ) - q - 1| ≤
      (P.natDegree : ℝ) * Real.sqrt q := by
  apply abs_pointCount_sub_card_sub_one_le_of_zetaNumerator_and_evenError_isBigO
      q pointCount P
  · exact
      hasZetaNumeratorPointCountFormula_of_formalPointCountZeta_rational
        q pointCount P hP0 hrational
  · exact herror

/-- Formal point-count zeta rationality and a two-sided square-root estimate
along any fixed positive divisible-even subsequence imply the base-field
Hasse bound. -/
theorem
    abs_pointCount_sub_card_sub_one_le_of_formalPointCountZeta_rational_and_divisibleEvenError_isBigO
    (q δ : ℕ) (pointCount : ℕ → ℕ) (P : Polynomial ℂ)
    (hq : 0 < q) (hδ : 0 < δ)
    (hP0 : P.coeff 0 = 1)
    (hrational :
      HasCurveZetaRationalForm (formalPointCountZeta pointCount) q P)
    (herror :
      (fun n : ℕ ↦
        (pointCount (2 * δ * n) : ℂ) - (q : ℂ) ^ (2 * δ * n) - 1) =O[atTop]
          fun n : ℕ ↦ ((q : ℝ) ^ δ) ^ n) :
    |(pointCount 1 : ℝ) - q - 1| ≤
      (P.natDegree : ℝ) * Real.sqrt q := by
  apply
    abs_pointCount_sub_card_sub_one_le_of_zetaNumerator_and_divisibleEvenError_isBigO
      q δ pointCount P hq hδ
  · exact
      hasZetaNumeratorPointCountFormula_of_formalPointCountZeta_rational
        q pointCount P hP0 hrational
  · exact herror

end

end BGS.HasseWeil
