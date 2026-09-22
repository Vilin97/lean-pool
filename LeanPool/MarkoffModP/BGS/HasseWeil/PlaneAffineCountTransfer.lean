/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-!
# Numerical transfer from normalization counts to affine counts

The geometric comparison between an affine plane curve and its normalization
is naturally expressed by two inequalities between natural-number
cardinalities.  This file isolates the real absolute-value bookkeeping needed
to combine those inequalities with the closed Hasse--Weil bound.
-/

namespace BGS.HasseWeil

/-- If the affine and normalization counts differ by at most `error` in both
directions, then a Hasse--Weil bound for the normalization transfers to the
affine count, with the affine/projective constant `1` and `error` added. -/
theorem abs_affine_sub_card_le_of_two_sided_count_comparison
    (affine normalization fieldCard error : ℕ)
    (upper : affine ≤ normalization + error)
    (lower : normalization ≤ affine + error)
    (bound : ℝ)
    (hnormalization :
      |(normalization : ℝ) - (fieldCard : ℝ) - 1| ≤ bound) :
    |(affine : ℝ) - (fieldCard : ℝ)| ≤ bound + error + 1 := by
  have hupperReal :
      (affine : ℝ) - normalization ≤ error := by
    have h : (affine : ℝ) ≤ normalization + error := by
      exact_mod_cast upper
    linarith
  have hlowerReal :
      -(error : ℝ) ≤ (affine : ℝ) - normalization := by
    have h : (normalization : ℝ) ≤ affine + error := by
      exact_mod_cast lower
    linarith
  have hcomparison :
      |(affine : ℝ) - normalization| ≤ error :=
    abs_le.mpr ⟨hlowerReal, hupperReal⟩
  calc
    |(affine : ℝ) - fieldCard| =
        |((affine : ℝ) - normalization) +
          ((normalization : ℝ) - fieldCard - 1) + 1| := by ring_nf
    _ ≤ |(affine : ℝ) - normalization| +
          |(normalization : ℝ) - fieldCard - 1| + |(1 : ℝ)| :=
      calc
        |((affine : ℝ) - normalization) +
            ((normalization : ℝ) - fieldCard - 1) + 1| ≤
            |((affine : ℝ) - normalization) +
              ((normalization : ℝ) - fieldCard - 1)| + |(1 : ℝ)| :=
          abs_add_le _ _
        _ ≤ (|(affine : ℝ) - normalization| +
              |(normalization : ℝ) - fieldCard - 1|) + |(1 : ℝ)| :=
          add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (error : ℝ) + bound + 1 := by
      exact add_le_add (add_le_add hcomparison hnormalization) (by norm_num)
    _ = bound + error + 1 := by ring

/-- Large-degree branch of the affine estimate.  A trivial fiber bound by
`fieldCard * smallDegree` already has Hasse--Weil scale whenever the other
coordinate degree is at least `sqrt fieldCard`. -/
theorem abs_pointCount_sub_card_le_two_mul_sqrt_of_fiber_bound
    (pointCount fieldCard smallDegree largeDegree : ℕ)
    (hsmall : 0 < smallDegree)
    (hcount : pointCount ≤ fieldCard * smallDegree)
    (hlarge : Real.sqrt (fieldCard : ℝ) ≤ largeDegree) :
    |(pointCount : ℝ) - fieldCard| ≤
      2 * Real.sqrt (fieldCard : ℝ) * smallDegree * largeDegree := by
  have hcountReal : (pointCount : ℝ) ≤ fieldCard * smallDegree := by
    exact_mod_cast hcount
  have hsmallReal : (1 : ℝ) ≤ smallDegree := by
    exact_mod_cast hsmall
  have hfieldNonneg : (0 : ℝ) ≤ fieldCard := by positivity
  have hsqrtNonneg : 0 ≤ Real.sqrt (fieldCard : ℝ) := Real.sqrt_nonneg _
  have hsqrtSquare :
      Real.sqrt (fieldCard : ℝ) * Real.sqrt (fieldCard : ℝ) = fieldCard :=
    Real.mul_self_sqrt hfieldNonneg
  calc
    |(pointCount : ℝ) - fieldCard| ≤
        |(pointCount : ℝ)| + |(fieldCard : ℝ)| := abs_sub _ _
    _ = (pointCount : ℝ) + fieldCard := by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg hfieldNonneg]
    _ ≤ (fieldCard : ℝ) * smallDegree + fieldCard := by gcongr
    _ ≤ 2 * (fieldCard : ℝ) * smallDegree := by nlinarith
    _ = 2 * (Real.sqrt (fieldCard : ℝ) *
          Real.sqrt (fieldCard : ℝ)) * smallDegree := by rw [hsqrtSquare]
    _ = (2 * Real.sqrt (fieldCard : ℝ) * smallDegree) *
          Real.sqrt (fieldCard : ℝ) := by ring
    _ ≤ (2 * Real.sqrt (fieldCard : ℝ) * smallDegree) * largeDegree :=
      mul_le_mul_of_nonneg_left hlarge (by positivity)
    _ = 2 * Real.sqrt (fieldCard : ℝ) * smallDegree * largeDegree := by ring

/-- In the small-degree branch, the explicit resultant bound for the
second-coordinate critical locus is already of Hasse--Weil scale. -/
theorem criticalCount_le_two_mul_sqrt
    (criticalCount fieldCard firstDegree secondDegree : ℕ)
    (hcritical : criticalCount ≤
      ((2 * secondDegree - 1) * firstDegree) * secondDegree)
    (hsecond : (secondDegree : ℝ) ≤ Real.sqrt (fieldCard : ℝ)) :
    (criticalCount : ℝ) ≤
      2 * Real.sqrt (fieldCard : ℝ) * firstDegree * secondDegree := by
  have hcoarseNat : criticalCount ≤
      (2 * secondDegree * firstDegree) * secondDegree := by
    calc
      criticalCount ≤ ((2 * secondDegree - 1) * firstDegree) * secondDegree :=
        hcritical
      _ ≤ (2 * secondDegree * firstDegree) * secondDegree :=
        Nat.mul_le_mul_right secondDegree
          (Nat.mul_le_mul_right firstDegree (Nat.sub_le _ _))
  have hcoarse : (criticalCount : ℝ) ≤
      (2 * secondDegree * firstDegree) * secondDegree := by
    exact_mod_cast hcoarseNat
  calc
    (criticalCount : ℝ) ≤
        (2 * secondDegree * firstDegree) * secondDegree := hcoarse
    _ = (2 * firstDegree * secondDegree) * secondDegree := by ring
    _ ≤ (2 * firstDegree * secondDegree) *
          Real.sqrt (fieldCard : ℝ) :=
      mul_le_mul_of_nonneg_left hsecond (by positivity)
    _ = 2 * Real.sqrt (fieldCard : ℝ) * firstDegree * secondDegree := by ring

/-- The coarse zeta numerator degree budget is bounded by three times the
bidegree product, which is sufficient for a universal affine coefficient. -/
theorem zetaDegree_mul_sqrt_le_three_mul_bidegree
    (zetaDegree fieldCard firstDegree secondDegree : ℕ)
    (hfirst : 0 < firstDegree) (hsecond : 0 < secondDegree)
    (hdegree : zetaDegree ≤
      2 * ((firstDegree - 1) * (secondDegree - 1)) + 1) :
    (zetaDegree : ℝ) * Real.sqrt (fieldCard : ℝ) ≤
      3 * Real.sqrt (fieldCard : ℝ) * firstDegree * secondDegree := by
  have hbudget : (firstDegree - 1) * (secondDegree - 1) ≤
      firstDegree * secondDegree :=
    Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have hone : 1 ≤ firstDegree * secondDegree := Nat.mul_pos hfirst hsecond
  have hdegreeCoarse : zetaDegree ≤ 3 * (firstDegree * secondDegree) := by
    calc
      zetaDegree ≤ 2 * ((firstDegree - 1) * (secondDegree - 1)) + 1 := hdegree
      _ ≤ 2 * (firstDegree * secondDegree) + 1 := by omega
      _ ≤ 3 * (firstDegree * secondDegree) := by omega
  have hdegreeReal : (zetaDegree : ℝ) ≤
      3 * (firstDegree * secondDegree : ℕ) := by exact_mod_cast hdegreeCoarse
  have hsqrtNonneg : 0 ≤ Real.sqrt (fieldCard : ℝ) := Real.sqrt_nonneg _
  calc
    (zetaDegree : ℝ) * Real.sqrt (fieldCard : ℝ) ≤
        (3 * (firstDegree * secondDegree : ℕ) : ℝ) *
          Real.sqrt (fieldCard : ℝ) :=
      mul_le_mul_of_nonneg_right hdegreeReal hsqrtNonneg
    _ = 3 * Real.sqrt (fieldCard : ℝ) * firstDegree * secondDegree := by
      push_cast
      ring

/-- The constant affine/projective correction `1` is absorbed by the
square-root bidegree scale over every nontrivial finite field. -/
theorem one_le_sqrt_mul_bidegree
    (fieldCard firstDegree secondDegree : ℕ)
    (hfield : 1 ≤ fieldCard)
    (hfirst : 0 < firstDegree) (hsecond : 0 < secondDegree) :
    (1 : ℝ) ≤ Real.sqrt (fieldCard : ℝ) * firstDegree * secondDegree := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (fieldCard : ℝ) := by
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hfield)
  have hfirstReal : (1 : ℝ) ≤ firstDegree := by exact_mod_cast hfirst
  have hsecondReal : (1 : ℝ) ≤ secondDegree := by exact_mod_cast hsecond
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hsqrt hfirstReal) hsecondReal

end BGS.HasseWeil
