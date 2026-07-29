/-
Copyright (c) 2026 Victor Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Aguiar
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The full rational three-torsion obstruction

This file proves that the rational points of a Weierstrass curve over `ℚ`
cannot contain a subgroup isomorphic to `ZMod 3 × ZMod 3`. The proof derives
the three-division polynomial from the tangent formulas and uses its four
hypothetical rational roots to contradict the Weierstrass coefficient
relation.
-/

namespace LeanPool.MazurTorsionFoundations.ThreeTorsion

open WeierstrassCurve

lemma tangent_forces_three_division
    {a₁ a₂ a₃ a₄ a₆ x y slope : ℚ}
    (hcurve :
      y ^ 2 + a₁ * x * y + a₃ * y =
        x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hslope :
      slope * (2 * y + a₁ * x + a₃) =
        3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hx : slope ^ 2 + a₁ * slope - a₂ - 3 * x = 0) :
    3 * x ^ 4 + (a₁ ^ 2 + 4 * a₂) * x ^ 3 +
      3 * (a₁ * a₃ + 2 * a₄) * x ^ 2 +
      3 * (a₃ ^ 2 + 4 * a₆) * x +
      (a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ +
        a₂ * a₃ ^ 2 - a₄ ^ 2) = 0 := by
  linear_combination
    -(2 * y + a₁ * x + a₃) ^ 2 * hx +
    ((3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) +
      slope * (2 * y + a₁ * x + a₃) +
      a₁ * (2 * y + a₁ * x + a₃)) * hslope -
    (a₁ ^ 2 + 4 * a₂ + 12 * x) * hcurve

open scoped WeierstrassCurve.Affine

lemma nonzero_three_torsion_abscissa
    (W : WeierstrassCurve.Affine ℚ) (P : W.Point)
    (hthree : (3 : ℕ) • P = 0) (hne : P ≠ 0) :
    ∃ x y, ∃ hP : W.Nonsingular x y,
      P = .some x y hP ∧ Polynomial.eval x W.Ψ₃ = 0 := by
  cases P with
  | zero => exact (hne rfl).elim
  | some x y hP =>
      have hthree' :
          (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP +
            WeierstrassCurve.Affine.Point.some x y hP = 0 := by
        simpa [three_nsmul, two_nsmul, add_assoc] using hthree
      have hdouble :
          (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some x y hP := by
        rw [← add_eq_zero_iff_eq_neg]
        exact hthree'
      have hy : y ≠ W.negY x y := by
        intro hy
        have htwo :
            (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 := by
          rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
        have : WeierstrassCurve.Affine.Point.some x y hP = 0 := by
          rw [htwo, zero_add] at hthree'
          exact hthree'
        exact hne this
      let slope := W.slope x x y y
      have hadd :=
        WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
      have hxcoord : W.addX x x slope = x := by
        have hsum :
            WeierstrassCurve.Affine.Point.some x y hP +
                WeierstrassCurve.Affine.Point.some x y hP =
              -WeierstrassCurve.Affine.Point.some x y hP := by
          simpa [two_nsmul] using hdouble
        have hsome := hadd.symm.trans hsum
        exact (WeierstrassCurve.Affine.Point.some.inj hsome).1
      have hslope :
          slope * (2 * y + W.a₁ * x + W.a₃) =
            3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
        have hden : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
          simp only [WeierstrassCurve.Affine.negY]
          ring
        dsimp [slope]
        rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
          div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
      have hx : slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x = 0 := by
        have := hxcoord
        simp only [WeierstrassCurve.Affine.addX] at this
        linarith
      have hcurve := hP.1
      rw [WeierstrassCurve.Affine.equation_iff] at hcurve
      have hψ := tangent_forces_three_division hcurve hslope hx
      refine ⟨x, y, hP, rfl, ?_⟩
      simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring_nf at hψ ⊢
      exact hψ

lemma quartic_coefficients_of_four_distinct_roots
    {b₂ b₄ b₆ b₈ r₁ r₂ r₃ r₄ : ℚ}
    (hne₁₂ : r₁ ≠ r₂) (hne₁₃ : r₁ ≠ r₃) (hne₁₄ : r₁ ≠ r₄)
    (hne₂₃ : r₂ ≠ r₃) (hne₂₄ : r₂ ≠ r₄) (hne₃₄ : r₃ ≠ r₄)
    (h₁ : 3 * r₁ ^ 4 + b₂ * r₁ ^ 3 + 3 * b₄ * r₁ ^ 2 +
      3 * b₆ * r₁ + b₈ = 0)
    (h₂ : 3 * r₂ ^ 4 + b₂ * r₂ ^ 3 + 3 * b₄ * r₂ ^ 2 +
      3 * b₆ * r₂ + b₈ = 0)
    (h₃ : 3 * r₃ ^ 4 + b₂ * r₃ ^ 3 + 3 * b₄ * r₃ ^ 2 +
      3 * b₆ * r₃ + b₈ = 0)
    (h₄ : 3 * r₄ ^ 4 + b₂ * r₄ ^ 3 + 3 * b₄ * r₄ ^ 2 +
      3 * b₆ * r₄ + b₈ = 0) :
    b₂ = -3 * (r₁ + r₂ + r₃ + r₄) ∧
      b₄ = r₁ * r₂ + r₁ * r₃ + r₁ * r₄ +
        r₂ * r₃ + r₂ * r₄ + r₃ * r₄ ∧
      b₆ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ +
        r₁ * r₃ * r₄ + r₂ * r₃ * r₄) ∧
      b₈ = 3 * (r₁ * r₂ * r₃ * r₄) := by
  have g₁₂ :
      3 * (r₁ ^ 3 + r₁ ^ 2 * r₂ + r₁ * r₂ ^ 2 + r₂ ^ 3) +
        b₂ * (r₁ ^ 2 + r₁ * r₂ + r₂ ^ 2) +
        3 * b₄ * (r₁ + r₂) + 3 * b₆ = 0 := by
    have hfactor : (r₁ - r₂) * (
        3 * (r₁ ^ 3 + r₁ ^ 2 * r₂ + r₁ * r₂ ^ 2 + r₂ ^ 3) +
          b₂ * (r₁ ^ 2 + r₁ * r₂ + r₂ ^ 2) +
          3 * b₄ * (r₁ + r₂) + 3 * b₆) = 0 := by
      linear_combination h₁ - h₂
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₁₂)
  have g₁₃ :
      3 * (r₁ ^ 3 + r₁ ^ 2 * r₃ + r₁ * r₃ ^ 2 + r₃ ^ 3) +
        b₂ * (r₁ ^ 2 + r₁ * r₃ + r₃ ^ 2) +
        3 * b₄ * (r₁ + r₃) + 3 * b₆ = 0 := by
    have hfactor : (r₁ - r₃) * (
        3 * (r₁ ^ 3 + r₁ ^ 2 * r₃ + r₁ * r₃ ^ 2 + r₃ ^ 3) +
          b₂ * (r₁ ^ 2 + r₁ * r₃ + r₃ ^ 2) +
          3 * b₄ * (r₁ + r₃) + 3 * b₆) = 0 := by
      linear_combination h₁ - h₃
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₁₃)
  have g₁₄ :
      3 * (r₁ ^ 3 + r₁ ^ 2 * r₄ + r₁ * r₄ ^ 2 + r₄ ^ 3) +
        b₂ * (r₁ ^ 2 + r₁ * r₄ + r₄ ^ 2) +
        3 * b₄ * (r₁ + r₄) + 3 * b₆ = 0 := by
    have hfactor : (r₁ - r₄) * (
        3 * (r₁ ^ 3 + r₁ ^ 2 * r₄ + r₁ * r₄ ^ 2 + r₄ ^ 3) +
          b₂ * (r₁ ^ 2 + r₁ * r₄ + r₄ ^ 2) +
          3 * b₄ * (r₁ + r₄) + 3 * b₆) = 0 := by
      linear_combination h₁ - h₄
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₁₄)
  have q₁₂₃ :
      3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ +
        r₂ ^ 2 + r₂ * r₃ + r₃ ^ 2) +
        b₂ * (r₁ + r₂ + r₃) + 3 * b₄ = 0 := by
    have hfactor : (r₂ - r₃) * (
        3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ +
          r₂ ^ 2 + r₂ * r₃ + r₃ ^ 2) +
          b₂ * (r₁ + r₂ + r₃) + 3 * b₄) = 0 := by
      linear_combination g₁₂ - g₁₃
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₂₃)
  have q₁₂₄ :
      3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₄ +
        r₂ ^ 2 + r₂ * r₄ + r₄ ^ 2) +
        b₂ * (r₁ + r₂ + r₄) + 3 * b₄ = 0 := by
    have hfactor : (r₂ - r₄) * (
        3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₄ +
          r₂ ^ 2 + r₂ * r₄ + r₄ ^ 2) +
          b₂ * (r₁ + r₂ + r₄) + 3 * b₄) = 0 := by
      linear_combination g₁₂ - g₁₄
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₂₄)
  have hb₂ : b₂ = -3 * (r₁ + r₂ + r₃ + r₄) := by
    have hfactor : (r₃ - r₄) *
        (3 * (r₁ + r₂ + r₃ + r₄) + b₂) = 0 := by
      linear_combination q₁₂₃ - q₁₂₄
    have := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₃₄)
    linarith
  have hb₄ : b₄ = r₁ * r₂ + r₁ * r₃ + r₁ * r₄ +
      r₂ * r₃ + r₂ * r₄ + r₃ * r₄ := by
    have h := q₁₂₃
    rw [hb₂] at h
    linear_combination (1 : ℚ) / 3 * h
  have hb₆ : b₆ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ +
      r₁ * r₃ * r₄ + r₂ * r₃ * r₄) := by
    have h := g₁₂
    rw [hb₂, hb₄] at h
    linear_combination (1 : ℚ) / 3 * h
  have hb₈ : b₈ = 3 * (r₁ * r₂ * r₃ * r₄) := by
    have h := h₁
    rw [hb₂, hb₄, hb₆] at h
    linear_combination h
  exact ⟨hb₂, hb₄, hb₆, hb₈⟩

lemma four_distinct_roots_invariant_impossible
    {b₂ b₄ b₆ b₈ r₁ r₂ r₃ r₄ : ℚ}
    (hne₁₂ : r₁ ≠ r₂) (hne₃₄ : r₃ ≠ r₄)
    (hb₂ : b₂ = -3 * (r₁ + r₂ + r₃ + r₄))
    (hb₄ : b₄ =
      r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₂ * r₃ + r₂ * r₄ + r₃ * r₄)
    (hb₆ : b₆ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ +
      r₁ * r₃ * r₄ + r₂ * r₃ * r₄))
    (hb₈ : b₈ = 3 * (r₁ * r₂ * r₃ * r₄))
    (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) :
    False := by
  subst b₂
  subst b₄
  subst b₆
  subst b₈
  have hid :
      2 * (12 * (r₁ * r₂ * r₃ * r₄) -
          (-3 * (r₁ + r₂ + r₃ + r₄)) *
            (-(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ +
              r₁ * r₃ * r₄ + r₂ * r₃ * r₄)) +
          (r₁ * r₂ + r₁ * r₃ + r₁ * r₄ +
            r₂ * r₃ + r₂ * r₄ + r₃ * r₄) ^ 2) =
        ((r₁ - r₂) * (r₃ - r₄)) ^ 2 +
          ((r₁ - r₃) * (r₂ - r₄)) ^ 2 +
          ((r₁ - r₄) * (r₂ - r₃)) ^ 2 := by
    ring
  have hpair : (r₁ - r₂) * (r₃ - r₄) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hne₁₂) (sub_ne_zero.mpr hne₃₄)
  have hpos : 0 < ((r₁ - r₂) * (r₃ - r₄)) ^ 2 :=
    sq_pos_of_ne_zero hpair
  have hnonneg₁ : 0 ≤ ((r₁ - r₃) * (r₂ - r₄)) ^ 2 := sq_nonneg _
  have hnonneg₂ : 0 ≤ ((r₁ - r₄) * (r₂ - r₃)) ^ 2 := sq_nonneg _
  nlinarith

private lemma abscissa_ne_of_independent_images
    (W : WeierstrassCurve.Affine ℚ)
    (φ : (ZMod 3 × ZMod 3) →+ W.Point) (hφ : Function.Injective φ)
    {z w : ZMod 3 × ZMod 3} (hzw : z ≠ w) (hznegw : z ≠ -w)
    {xz yz xw yw : ℚ}
    {hz : W.Nonsingular xz yz} {hw : W.Nonsingular xw yw}
    (hPz : φ z = .some xz yz hz) (hPw : φ w = .some xw yw hw) :
    xz ≠ xw := by
  intro hx
  have hxrep :
      (WeierstrassCurve.Affine.Point.some xz yz hz).xRep =
        (WeierstrassCurve.Affine.Point.some xw yw hw).xRep := by
    simp [hx]
  rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
    with heq | heq
  · apply hzw
    exact hφ (hPz.trans (heq.trans hPw.symm))
  · apply hznegw
    apply hφ
    calc
      φ z = WeierstrassCurve.Affine.Point.some xz yz hz := hPz
      _ = -WeierstrassCurve.Affine.Point.some xw yw hw := heq
      _ = -φ w := congrArg Neg.neg hPw.symm
      _ = φ (-w) := (map_neg φ w).symm

/-- There is no full rational three-torsion subgroup on a Weierstrass curve
over `ℚ`. -/
theorem not_injective_zmod_three_square
    (E : WeierstrassCurve ℚ)
    (φ : (ZMod 3 × ZMod 3) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  let z₁ : ZMod 3 × ZMod 3 := (1, 0)
  let z₂ : ZMod 3 × ZMod 3 := (0, 1)
  let z₃ : ZMod 3 × ZMod 3 := (1, 1)
  let z₄ : ZMod 3 × ZMod 3 := (1, 2)
  let P₁ : (E⁄ℚ).Point := φ z₁
  let P₂ : (E⁄ℚ).Point := φ z₂
  let P₃ : (E⁄ℚ).Point := φ z₃
  let P₄ : (E⁄ℚ).Point := φ z₄
  have hthree (z : ZMod 3 × ZMod 3) : (3 : ℕ) • φ z = 0 := by
    have hz : (3 : ℕ) • z = 0 := by
      rcases z with ⟨a, b⟩
      apply Prod.ext
      · change (3 : ℕ) • a = 0
        rw [nsmul_eq_mul]
        rw [show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]
      · change (3 : ℕ) • b = 0
        rw [nsmul_eq_mul]
        rw [show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]
    rw [← map_nsmul, hz, map_zero]
  have hn₁ : P₁ ≠ 0 := by
    intro h
    exact (by decide : z₁ ≠ 0) (hφ (by simpa [P₁] using h))
  have hn₂ : P₂ ≠ 0 := by
    intro h
    exact (by decide : z₂ ≠ 0) (hφ (by simpa [P₂] using h))
  have hn₃ : P₃ ≠ 0 := by
    intro h
    exact (by decide : z₃ ≠ 0) (hφ (by simpa [P₃] using h))
  have hn₄ : P₄ ≠ 0 := by
    intro h
    exact (by decide : z₄ ≠ 0) (hφ (by simpa [P₄] using h))
  obtain ⟨r₁, y₁, hP₁, hP₁eq, hr₁⟩ :=
    nonzero_three_torsion_abscissa (E⁄ℚ) P₁ (hthree z₁) hn₁
  obtain ⟨r₂, y₂, hP₂, hP₂eq, hr₂⟩ :=
    nonzero_three_torsion_abscissa (E⁄ℚ) P₂ (hthree z₂) hn₂
  obtain ⟨r₃, y₃, hP₃, hP₃eq, hr₃⟩ :=
    nonzero_three_torsion_abscissa (E⁄ℚ) P₃ (hthree z₃) hn₃
  obtain ⟨r₄, y₄, hP₄, hP₄eq, hr₄⟩ :=
    nonzero_three_torsion_abscissa (E⁄ℚ) P₄ (hthree z₄) hn₄
  have hrepr₁ : φ z₁ = .some r₁ y₁ hP₁ := by simpa [P₁] using hP₁eq
  have hrepr₂ : φ z₂ = .some r₂ y₂ hP₂ := by simpa [P₂] using hP₂eq
  have hrepr₃ : φ z₃ = .some r₃ y₃ hP₃ := by simpa [P₃] using hP₃eq
  have hrepr₄ : φ z₄ = .some r₄ y₄ hP₄ := by simpa [P₄] using hP₄eq
  have hr₁₂ : r₁ ≠ r₂ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₁ hrepr₂
  have hr₁₃ : r₁ ≠ r₃ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₁ hrepr₃
  have hr₁₄ : r₁ ≠ r₄ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₁ hrepr₄
  have hr₂₃ : r₂ ≠ r₃ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₂ hrepr₃
  have hr₂₄ : r₂ ≠ r₄ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₂ hrepr₄
  have hr₃₄ : r₃ ≠ r₄ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₃ hrepr₄
  simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat] at hr₁ hr₂ hr₃ hr₄
  obtain ⟨hb₂, hb₄, hb₆, hb₈⟩ :=
    quartic_coefficients_of_four_distinct_roots
      hr₁₂ hr₁₃ hr₁₄ hr₂₃ hr₂₄ hr₃₄ hr₁ hr₂ hr₃ hr₄
  exact four_distinct_roots_invariant_impossible hr₁₂ hr₃₄
    hb₂ hb₄ hb₆ hb₈ (E⁄ℚ).b_relation

end LeanPool.MazurTorsionFoundations.ThreeTorsion
