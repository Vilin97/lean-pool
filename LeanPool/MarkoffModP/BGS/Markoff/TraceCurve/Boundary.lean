/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Geometry

/-!
# Affine boundary of the split trace cover

The split trace equation is naturally an equation on `G_m × G_m`, whereas
`splitTraceCoverPolynomial` is its denominator-cleared affine model.  Weil estimates are often
stated for an affine or projective model, so the points introduced on the coordinate axes must be
accounted for explicitly.  For positive covering exponents and nonzero second weight, the affine
model adds exactly the origin and no other coordinate-axis point.
-/

@[expose] public section

namespace BGS.Markoff

open Polynomial

section Boundary

variable {K : Type*} [Field K]

/-- A zero of the denominator-cleared split trace polynomial on either coordinate axis is the
origin.  The positivity hypotheses are essential: they ensure that clearing the Laurent
denominators really contributes powers of both coordinates. -/
theorem splitTraceCoverPolynomial_axis_zero_eq_origin
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (x y : K)
    (hzero : MvPolynomial.eval ![x, y] (splitTraceCoverPolynomial alpha beta d e) = 0)
    (haxis : x = 0 ∨ y = 0) :
    x = 0 ∧ y = 0 := by
  rw [eval_splitTraceCoverPolynomial] at hzero
  have htwoD : 2 * d ≠ 0 := by omega
  have htwoE : 2 * e ≠ 0 := by omega
  rcases haxis with rfl | rfl
  · constructor
    · rfl
    · have hyPow : y ^ e = 0 := by
        have hneg : -(y ^ e) = 0 := by
          simpa only [zero_pow hd.ne', zero_pow htwoD, zero_mul, mul_zero,
            add_zero, sub_zero, zero_sub] using hzero
        exact neg_eq_zero.mp hneg
      exact (pow_eq_zero_iff he.ne').mp hyPow
  · constructor
    · have hxPow : x ^ d = 0 := by
        have hbetaPow : beta * x ^ d = 0 := by
          simpa only [zero_pow he.ne', zero_pow htwoE, mul_zero,
            add_zero, sub_zero, zero_add] using hzero
        exact (mul_eq_zero.mp hbetaPow).resolve_left hbeta
      exact (pow_eq_zero_iff hd.ne').mp hxPow
    · rfl

/-- The origin is always the affine boundary point added by clearing denominators when both
covering exponents are positive. -/
theorem splitTraceCoverPolynomial_origin_zero
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    MvPolynomial.eval ![(0 : K), (0 : K)]
      (splitTraceCoverPolynomial alpha beta d e) = 0 := by
  rw [eval_splitTraceCoverPolynomial]
  have htwoD : 2 * d ≠ 0 := by omega
  have htwoE : 2 * e ≠ 0 := by omega
  simp only [zero_pow hd.ne', zero_pow he.ne',
    zero_pow htwoD, zero_pow htwoE, mul_zero,
    add_zero, sub_zero]

/-- Away from the single affine boundary point, every zero of the cleared polynomial has two
nonzero coordinates and therefore is genuinely a point of the original Laurent trace curve. -/
theorem splitTraceCoverPolynomial_nonorigin_has_nonzero_coordinates
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (x y : K)
    (hzero : MvPolynomial.eval ![x, y] (splitTraceCoverPolynomial alpha beta d e) = 0)
    (hnonorigin : (x, y) ≠ (0, 0)) :
    x ≠ 0 ∧ y ≠ 0 := by
  constructor
  · intro hx
    exact hnonorigin (Prod.ext hx
      (splitTraceCoverPolynomial_axis_zero_eq_origin alpha beta d e hd he hbeta x y hzero
        (Or.inl hx)).2)
  · intro hy
    exact hnonorigin (Prod.ext
      (splitTraceCoverPolynomial_axis_zero_eq_origin alpha beta d e hd he hbeta x y hzero
        (Or.inr hy)).1 hy)

end Boundary

section FiniteBoundaryCount

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- Affine zeros of the denominator-cleared split trace polynomial. -/
noncomputable def affineSplitTraceCoverZeros
    (alpha beta : K) (d e : ℕ) : Finset (K × K) := by
  classical
  exact Finset.univ.filter fun z =>
    MvPolynomial.eval ![z.1, z.2] (splitTraceCoverPolynomial alpha beta d e) = 0

/-- Zeros of the cleared polynomial that lie on the original two-dimensional torus. -/
noncomputable def torusSplitTraceCoverZeros
    (alpha beta : K) (d e : ℕ) : Finset (K × K) := by
  classical
  exact (affineSplitTraceCoverZeros K alpha beta d e).filter fun z =>
    z.1 ≠ 0 ∧ z.2 ≠ 0

/-- Solutions of the original Laurent trace equation, represented on `Kˣ × Kˣ` rather
than in the denominator-cleared affine plane. -/
noncomputable def splitTraceCurveSolutions
    (alpha beta : K) (d e : ℕ) : Finset (Kˣ × Kˣ) := by
  classical
  exact Finset.univ.filter fun z => SplitTraceCurveEquation alpha beta d e z.1 z.2

@[simp]
theorem mem_affineSplitTraceCoverZeros_iff
    (alpha beta : K) (d e : ℕ) (z : K × K) :
    z ∈ affineSplitTraceCoverZeros K alpha beta d e ↔
      MvPolynomial.eval ![z.1, z.2] (splitTraceCoverPolynomial alpha beta d e) = 0 := by
  classical
  simp [affineSplitTraceCoverZeros]

@[simp]
theorem mem_torusSplitTraceCoverZeros_iff
    (alpha beta : K) (d e : ℕ) (z : K × K) :
    z ∈ torusSplitTraceCoverZeros K alpha beta d e ↔
      MvPolynomial.eval ![z.1, z.2] (splitTraceCoverPolynomial alpha beta d e) = 0 ∧
        z.1 ≠ 0 ∧ z.2 ≠ 0 := by
  classical
  simp [torusSplitTraceCoverZeros]

@[simp]
theorem mem_splitTraceCurveSolutions_iff
    (alpha beta : K) (d e : ℕ) (z : Kˣ × Kˣ) :
    z ∈ splitTraceCurveSolutions K alpha beta d e ↔
      SplitTraceCurveEquation alpha beta d e z.1 z.2 := by
  classical
  simp [splitTraceCurveSolutions]

/-- The nonzero affine zeros of the cleared polynomial and the solutions of the original Laurent
equation have exactly the same cardinality.  This is the finite-field bridge needed before a
point estimate for one model can be used for the other. -/
theorem torusSplitTraceCoverZeros_card_eq_splitTraceCurveSolutions_card
    (alpha beta : K) (d e : ℕ) :
    (torusSplitTraceCoverZeros K alpha beta d e).card =
      (splitTraceCurveSolutions K alpha beta d e).card := by
  classical
  symm
  apply Finset.card_bij
      (fun z (_hz : z ∈ splitTraceCurveSolutions K alpha beta d e) =>
        (((z.1 : K), (z.2 : K)) : K × K))
  · intro z hz
    rw [mem_torusSplitTraceCoverZeros_iff]
    refine ⟨(eval_splitTraceCoverPolynomial_eq_zero_iff alpha beta d e z.1 z.2).2 ?_,
      z.1.ne_zero, z.2.ne_zero⟩
    exact (mem_splitTraceCurveSolutions_iff K alpha beta d e z).1 hz
  · intro z₁ hz₁ z₂ hz₂ heq
    apply Prod.ext
    · apply Units.ext
      exact congrArg Prod.fst heq
    · apply Units.ext
      exact congrArg Prod.snd heq
  · intro z hz
    rw [mem_torusSplitTraceCoverZeros_iff] at hz
    let ux : Kˣ := Units.mk0 z.1 hz.2.1
    let uy : Kˣ := Units.mk0 z.2 hz.2.2
    refine ⟨(ux, uy), ?_, ?_⟩
    · rw [mem_splitTraceCurveSolutions_iff]
      exact (eval_splitTraceCoverPolynomial_eq_zero_iff alpha beta d e ux uy).1 (by
        simpa [ux, uy] using hz.1)
    · simp [ux, uy]

/-- Erasing the unique coordinate-axis point from the affine zero set leaves exactly the genuine
torus zero set. -/
theorem affineSplitTraceCoverZeros_erase_origin
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0) :
    (affineSplitTraceCoverZeros K alpha beta d e).erase ((0, 0) : K × K) =
      torusSplitTraceCoverZeros K alpha beta d e := by
  classical
  ext z
  simp only [Finset.mem_erase, mem_affineSplitTraceCoverZeros_iff,
    mem_torusSplitTraceCoverZeros_iff]
  constructor
  · rintro ⟨hnonorigin, hz⟩
    exact ⟨hz,
        splitTraceCoverPolynomial_nonorigin_has_nonzero_coordinates alpha beta d e hd he hbeta
          z.1 z.2 hz (by simpa using hnonorigin)⟩
  · rintro ⟨hz, hx, hy⟩
    refine ⟨?_, hz⟩
    intro horigin
    exact hx (congrArg Prod.fst horigin)

/-- Clearing Laurent denominators adds exactly one affine point.  This is the exact boundary
correction required when a point estimate for the affine polynomial is converted to the torus
count used in the paper's endgame. -/
theorem affineSplitTraceCoverZeros_card_eq_torus_card_add_one
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0) :
    (affineSplitTraceCoverZeros K alpha beta d e).card =
      (torusSplitTraceCoverZeros K alpha beta d e).card + 1 := by
  classical
  have horiginMem : ((0, 0) : K × K) ∈
      affineSplitTraceCoverZeros K alpha beta d e := by
    rw [mem_affineSplitTraceCoverZeros_iff]
    exact splitTraceCoverPolynomial_origin_zero alpha beta d e hd he
  rw [← affineSplitTraceCoverZeros_erase_origin K alpha beta d e hd he hbeta]
  exact (Finset.card_erase_add_one horiginMem).symm

end FiniteBoundaryCount

end BGS.Markoff
