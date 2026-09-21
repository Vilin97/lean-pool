/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.ChartLocalization

/-!
# Jacobian control on the Laurent trace cover

This file proves the algebraic nonsingularity calculation needed to identify the normalization
with the original trace curve away from the coordinate boundary.  The two formal partial
derivatives generate the unit ideal in the Laurent coordinate ring when `2`, `d`, and `e` are
nonzero and the paper's parameter condition `alpha * beta ≠ 1` holds.

The proof exposes the characteristic assumptions and gives an explicit ideal calculation.  It does
not assume smoothness or normality as a structure field.
-/

namespace BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

/-- The nonunit-free factor of the partial derivative with respect to `x`. -/
def weightedSplitTraceLaurentJacobianXFactor (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  algebraMap K _ alpha * weightedSplitTraceLaurentY alpha beta d e ^ (2 * e) +
    algebraMap K _ beta -
    2 * weightedSplitTraceLaurentX alpha beta d e ^ d *
      weightedSplitTraceLaurentY alpha beta d e ^ e

/-- The nonunit-free factor of the partial derivative with respect to `y`. -/
def weightedSplitTraceLaurentJacobianYFactor (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  2 * algebraMap K _ alpha * weightedSplitTraceLaurentX alpha beta d e ^ d *
      weightedSplitTraceLaurentY alpha beta d e ^ e -
    weightedSplitTraceLaurentX alpha beta d e ^ (2 * d) - 1

/-- Exact evaluation formula for the first formal partial derivative. -/
theorem splitTraceCoverPolynomial_pderiv_zero_eval
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (x y : K) :
    MvPolynomial.eval ![x, y]
        (MvPolynomial.pderiv 0 (splitTraceCoverPolynomial alpha beta d e)) =
      (d : K) * x ^ (d - 1) *
        (alpha * y ^ (2 * e) + beta - 2 * x ^ d * y ^ e) := by
  have htwoD : 2 * d - 1 = (d - 1) + d := by omega
  simp [splitTraceCoverPolynomial, htwoD, pow_add]
  ring

/-- Exact evaluation formula for the second formal partial derivative. -/
theorem splitTraceCoverPolynomial_pderiv_one_eval
    (alpha beta : K) (d e : ℕ) (he : 0 < e) (x y : K) :
    MvPolynomial.eval ![x, y]
        (MvPolynomial.pderiv 1 (splitTraceCoverPolynomial alpha beta d e)) =
      (e : K) * y ^ (e - 1) *
        (2 * alpha * x ^ d * y ^ e - x ^ (2 * d) - 1) := by
  have htwoE : 2 * e - 1 = (e - 1) + e := by omega
  simp [splitTraceCoverPolynomial, htwoE, pow_add]
  ring

/-- The first formal partial derivative evaluated in the Laurent coordinate ring. -/
def weightedSplitTraceLaurentPartialX (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  MvPolynomial.aeval
    ![weightedSplitTraceLaurentX alpha beta d e,
      weightedSplitTraceLaurentY alpha beta d e]
    (MvPolynomial.pderiv 0 (splitTraceCoverPolynomial alpha beta d e))

/-- The second formal partial derivative evaluated in the Laurent coordinate ring. -/
def weightedSplitTraceLaurentPartialY (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  MvPolynomial.aeval
    ![weightedSplitTraceLaurentX alpha beta d e,
      weightedSplitTraceLaurentY alpha beta d e]
    (MvPolynomial.pderiv 1 (splitTraceCoverPolynomial alpha beta d e))

theorem weightedSplitTraceLaurentPartialX_eq (alpha beta : K) (d e : ℕ) (hd : 0 < d) :
    weightedSplitTraceLaurentPartialX alpha beta d e =
      algebraMap K _ (d : K) * weightedSplitTraceLaurentX alpha beta d e ^ (d - 1) *
        weightedSplitTraceLaurentJacobianXFactor alpha beta d e := by
  have htwoD : 2 * d - 1 = (d - 1) + d := by omega
  simp [weightedSplitTraceLaurentPartialX, weightedSplitTraceLaurentJacobianXFactor, MvPolynomial.aeval_def,
    splitTraceCoverPolynomial, htwoD, pow_add]
  ring

theorem weightedSplitTraceLaurentPartialY_eq (alpha beta : K) (d e : ℕ) (he : 0 < e) :
    weightedSplitTraceLaurentPartialY alpha beta d e =
      algebraMap K _ (e : K) * weightedSplitTraceLaurentY alpha beta d e ^ (e - 1) *
        weightedSplitTraceLaurentJacobianYFactor alpha beta d e := by
  have htwoE : 2 * e - 1 = (e - 1) + e := by omega
  simp [weightedSplitTraceLaurentPartialY, weightedSplitTraceLaurentJacobianYFactor, MvPolynomial.aeval_def,
    splitTraceCoverPolynomial, htwoE, pow_add]
  ring

theorem weightedSplitTraceLaurentJacobianFactors_span_top
    (alpha beta : K) (hnondegenerate : alpha * beta ≠ 1)
    (htwo : (2 : K) ≠ 0) (d e : ℕ) :
    Ideal.span {weightedSplitTraceLaurentJacobianXFactor alpha beta d e,
        weightedSplitTraceLaurentJacobianYFactor alpha beta d e} = ⊤ := by
  let L := WeightedSplitTraceLaurentCoordinateRing alpha beta d e
  let x : L := weightedSplitTraceLaurentX alpha beta d e
  let y : L := weightedSplitTraceLaurentY alpha beta d e
  let X : L := x ^ d
  let Y : L := y ^ e
  let a : L := algebraMap K L alpha
  let b : L := algebraMap K L beta
  let A : L := weightedSplitTraceLaurentJacobianXFactor alpha beta d e
  let B : L := weightedSplitTraceLaurentJacobianYFactor alpha beta d e
  let I : Ideal L := Ideal.span {A, B}
  change I = ⊤
  have hAeq : A = a * Y ^ 2 + b - 2 * X * Y := by
    simp [A, a, b, X, Y, x, y, L, weightedSplitTraceLaurentJacobianXFactor, Nat.mul_comm, pow_mul]
  have hBeq : B = 2 * a * X * Y - X ^ 2 - 1 := by
    simp [B, a, X, Y, x, y, L, weightedSplitTraceLaurentJacobianYFactor, Nat.mul_comm, pow_mul]
  have hA : A ∈ I := Ideal.subset_span (by simp)
  have hB : B ∈ I := Ideal.subset_span (by simp)
  have hF : a * X * Y ^ 2 + b * X - X ^ 2 * Y - Y = 0 := by
    have h := weightedSplitTraceLaurentDefiningRelation alpha beta d e
    change a * x ^ d * y ^ (2 * e) + b * x ^ d -
        x ^ (2 * d) * y ^ e - y ^ e = 0 at h
    rw [show y ^ (2 * e) = Y ^ 2 by simp [Y, Nat.mul_comm, pow_mul],
      show x ^ (2 * d) = X ^ 2 by simp [X, Nat.mul_comm, pow_mul]] at h
    exact h
  have hYUnit : IsUnit Y := by
    exact (weightedSplitTraceLaurentY_isUnit alpha beta d e).pow e
  have hTwoUnit : IsUnit (2 : L) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr htwo).map (algebraMap K L)
  have hXSquare : X ^ 2 - 1 ∈ I := by
    apply (I.unit_mul_mem_iff_mem hYUnit).mp
    have hXA : X * A ∈ I := I.mul_mem_left X hA
    have : Y * (X ^ 2 - 1) = -(X * A) := by
      rw [hAeq]
      linear_combination hF
    rw [this]
    exact I.neg_mem hXA
  have hAlphaXY : a * X * Y - 1 ∈ I := by
    apply (I.unit_mul_mem_iff_mem hTwoUnit).mp
    have hsum : B + (X ^ 2 - 1) ∈ I := I.add_mem hB hXSquare
    rw [hBeq] at hsum
    convert hsum using 1
    all_goals ring
  have hAlphaSquareY : a ^ 2 * Y ^ 2 - 1 ∈ I := by
    have hproduct : (a * X * Y - 1) * (a * X * Y + 1) ∈ I :=
      I.mul_mem_right (a * X * Y + 1) hAlphaXY
    have hcorrection : a ^ 2 * Y ^ 2 * (X ^ 2 - 1) ∈ I :=
      I.mul_mem_left (a ^ 2 * Y ^ 2) hXSquare
    have hsub := I.sub_mem hproduct hcorrection
    convert hsub using 1
    all_goals ring
  have hProductMinusOne : a * b - 1 ∈ I := by
    have haA : a * A ∈ I := I.mul_mem_left a hA
    rw [hAeq] at haA
    have htwice : 2 * (a * X * Y - 1) ∈ I := I.mul_mem_left 2 hAlphaXY
    have hcombination := I.add_mem (I.sub_mem haA hAlphaSquareY) htwice
    convert hcombination using 1
    all_goals ring
  have hProductUnit : IsUnit (a * b - 1) := by
    have h : IsUnit (alpha * beta - 1) :=
      isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hnondegenerate)
    simpa [a, b, L] using h.map (algebraMap K L)
  exact I.eq_top_of_isUnit_mem hProductMinusOne hProductUnit

theorem weightedSplitTraceLaurentPartials_span_top
    (alpha beta : K) (hnondegenerate : alpha * beta ≠ 1)
    (htwo : (2 : K) ≠ 0) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hdChar : (d : K) ≠ 0) (heChar : (e : K) ≠ 0) :
    Ideal.span {weightedSplitTraceLaurentPartialX alpha beta d e,
        weightedSplitTraceLaurentPartialY alpha beta d e} = ⊤ := by
  let L := WeightedSplitTraceLaurentCoordinateRing alpha beta d e
  let J : Ideal L := Ideal.span {weightedSplitTraceLaurentPartialX alpha beta d e,
    weightedSplitTraceLaurentPartialY alpha beta d e}
  have hFactorTop := weightedSplitTraceLaurentJacobianFactors_span_top alpha beta hnondegenerate htwo d e
  apply le_antisymm le_top
  rw [← hFactorTop]
  apply Ideal.span_le.mpr
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · have hPartial : weightedSplitTraceLaurentPartialX alpha beta d e ∈ J :=
      Ideal.subset_span (by simp)
    rw [weightedSplitTraceLaurentPartialX_eq alpha beta d e hd] at hPartial
    have hDegreeUnit : IsUnit (algebraMap K L (d : K)) :=
      (isUnit_iff_ne_zero.mpr hdChar).map (algebraMap K L)
    have hXPowerUnit :
        IsUnit (weightedSplitTraceLaurentX alpha beta d e ^ (d - 1)) :=
      (weightedSplitTraceLaurentX_isUnit alpha beta d e).pow (d - 1)
    exact (J.unit_mul_mem_iff_mem (hDegreeUnit.mul hXPowerUnit)).mp hPartial
  · have hPartial : weightedSplitTraceLaurentPartialY alpha beta d e ∈ J :=
      Ideal.subset_span (by simp)
    rw [weightedSplitTraceLaurentPartialY_eq alpha beta d e he] at hPartial
    have hDegreeUnit : IsUnit (algebraMap K L (e : K)) :=
      (isUnit_iff_ne_zero.mpr heChar).map (algebraMap K L)
    have hYPowerUnit :
        IsUnit (weightedSplitTraceLaurentY alpha beta d e ^ (e - 1)) :=
      (weightedSplitTraceLaurentY_isUnit alpha beta d e).pow (e - 1)
    exact (J.unit_mul_mem_iff_mem (hDegreeUnit.mul hYPowerUnit)).mp hPartial

end

end BGS.Markoff
