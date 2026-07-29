/-
Copyright (c) 2026 Victor Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Aguiar
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The full rational four-torsion obstruction

This file proves that the rational points of an elliptic curve over `ℚ` cannot
contain a subgroup isomorphic to `ZMod 4 × ZMod 4`. The proof extracts the
three nonzero two-torsion points and uses the duplication formulas to force an
impossible product of rational squares.
-/

namespace LeanPool.MazurTorsionFoundations

open scoped WeierstrassCurve.Affine

namespace FullFour

/-- Coefficients of a cubic with known distinct roots. This is the
coefficient-comparison step for the two-division polynomial. -/
lemma cubic_coefficients_of_three_roots
    {b c d r₁ r₂ r₃ : ℚ}
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (hr₁ : 4 * r₁ ^ 3 + b * r₁ ^ 2 + c * r₁ + d = 0)
    (hr₂ : 4 * r₂ ^ 3 + b * r₂ ^ 2 + c * r₂ + d = 0)
    (hr₃ : 4 * r₃ ^ 3 + b * r₃ ^ 2 + c * r₃ + d = 0) :
    b = -4 * (r₁ + r₂ + r₃) ∧
      c = 4 * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) ∧
      d = -4 * (r₁ * r₂ * r₃) := by
  have h₁₂' :
      4 * (r₁ ^ 2 + r₁ * r₂ + r₂ ^ 2) + b * (r₁ + r₂) + c = 0 := by
    have hfactor :
        (r₁ - r₂) *
          (4 * (r₁ ^ 2 + r₁ * r₂ + r₂ ^ 2) + b * (r₁ + r₂) + c) = 0 := by
      linear_combination hr₁ - hr₂
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr h₁₂)
  have h₁₃' :
      4 * (r₁ ^ 2 + r₁ * r₃ + r₃ ^ 2) + b * (r₁ + r₃) + c = 0 := by
    have hfactor :
        (r₁ - r₃) *
          (4 * (r₁ ^ 2 + r₁ * r₃ + r₃ ^ 2) + b * (r₁ + r₃) + c) = 0 := by
      linear_combination hr₁ - hr₃
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr h₁₃)
  have hb : b = -4 * (r₁ + r₂ + r₃) := by
    have hfactor : (r₂ - r₃) * (4 * (r₁ + r₂ + r₃) + b) = 0 := by
      linear_combination h₁₂' - h₁₃'
    have := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr h₂₃)
    linarith
  have hc : c = 4 * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) := by
    linear_combination h₁₂' - (r₁ + r₂) * hb
  have hd : d = -4 * (r₁ * r₂ * r₃) := by
    linear_combination hr₁ - r₁ ^ 2 * hb - r₁ * hc
  exact ⟨hb, hc, hd⟩

/-- Algebraic halving identity for a nonzero two-torsion point. The hypotheses
are precisely the curve equation, the coefficients of the split two-division
cubic, and the tangent-doubling equations. -/
lemma halving_forces_square
    {a₁ a₂ a₃ a₄ a₆ x y slope r₁ r₂ r₃ : ℚ}
    (hcurve :
      y ^ 2 + a₁ * x * y + a₃ * y =
        x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hb : a₁ ^ 2 + 4 * a₂ = -4 * (r₁ + r₂ + r₃))
    (hc : 2 * a₁ * a₃ + 4 * a₄ =
      4 * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃))
    (hd : a₃ ^ 2 + 4 * a₆ = -4 * (r₁ * r₂ * r₃))
    (hslope :
      slope * (2 * y + a₁ * x + a₃) =
        3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hx : slope ^ 2 + a₁ * slope - a₂ - x - x = r₁) :
    (r₁ - r₂) * (r₁ - r₃) = (x - r₁) ^ 2 := by
  have hcurve_split :
      (2 * y + a₁ * x + a₃) ^ 2 =
        4 * ((x - r₁) * (x - r₂) * (x - r₃)) := by
    linear_combination 4 * hcurve + x ^ 2 * hb + x * hc + hd
  have htangent :
      (slope + a₁ / 2) * (2 * y + a₁ * x + a₃) =
        3 * x ^ 2 - 2 * (r₁ + r₂ + r₃) * x +
          (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) := by
    linear_combination hslope + x / 2 * hb + (1 : ℚ) / 4 * hc
  have hslope_sq :
      (slope + a₁ / 2) ^ 2 = 2 * x + r₁ - (r₁ + r₂ + r₃) := by
    linear_combination hx + (1 : ℚ) / 4 * hb
  have hdefect :
      ((x - r₁) ^ 2 - (r₁ - r₂) * (r₁ - r₃)) ^ 2 = 0 := by
    linear_combination
      (-(3 * x ^ 2 - 2 * (r₁ + r₂ + r₃) * x +
          (r₁ * r₂ + r₁ * r₃ + r₂ * r₃)) -
        (slope + a₁ / 2) * (2 * y + a₁ * x + a₃)) * htangent +
      (2 * y + a₁ * x + a₃) ^ 2 * hslope_sq +
      (2 * x + r₁ - (r₁ + r₂ + r₃)) * hcurve_split
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hdefect) |>.symm

/-- Extract affine coordinates and the tangent equations from a point whose
double is a nonzero point killed by two. -/
lemma exists_halving_data
    {W : WeierstrassCurve.Affine ℚ}
    (P T : W.Point) (hdouble : (2 : ℕ) • P = T)
    (htwo : (2 : ℕ) • T = 0) (hne : T ≠ 0) :
    ∃ r u x y slope : ℚ,
      (∃ hT : W.Nonsingular r u, T = .some r u hT) ∧
      W.Equation r u ∧ u = W.negY r u ∧
      W.Equation x y ∧
      slope * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y ∧
      slope ^ 2 + W.a₁ * slope - W.a₂ - x - x = r := by
  have hP : P ≠ 0 := by
    intro hP0
    rw [hP0] at hdouble
    exact hne (by simpa using hdouble.symm)
  cases T with
  | zero => exact (hne rfl).elim
  | some r u hT =>
      have hu : u = W.negY r u := by
        have hself :
            WeierstrassCurve.Affine.Point.some r u hT =
              -WeierstrassCurve.Affine.Point.some r u hT := by
          rw [← add_eq_zero_iff_eq_neg]
          simpa [two_nsmul] using htwo
        simpa only [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq, true_and] using hself
      cases P with
      | zero => exact (hP rfl).elim
      | some x y hPxy =>
          have hy : y ≠ W.negY x y := by
            intro hy
            have hz :
                (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hPxy = 0 := by
              rw [two_nsmul,
                WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
            exact hne (hdouble ▸ hz)
          let slope := W.slope x x y y
          have hadd :=
            WeierstrassCurve.Affine.Point.add_self_of_Y_ne
              (h₁ := hPxy) hy
          have hxcoord :
              W.addX x x slope = r := by
            have hsum :
                WeierstrassCurve.Affine.Point.some x y hPxy +
                    WeierstrassCurve.Affine.Point.some x y hPxy =
                  WeierstrassCurve.Affine.Point.some r u hT := by
              simpa [two_nsmul] using hdouble
            exact (WeierstrassCurve.Affine.Point.some.inj
              (hadd.symm.trans hsum)).1
          have hslope :
              slope * (2 * y + W.a₁ * x + W.a₃) =
                3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
            have hden :
                y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
              simp only [WeierstrassCurve.Affine.negY]
              ring
            dsimp [slope]
            rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
              div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
          have hxformula :
              slope ^ 2 + W.a₁ * slope - W.a₂ - x - x = r := by
            simpa only [WeierstrassCurve.Affine.addX] using hxcoord
          exact ⟨r, u, x, y, slope, ⟨hT, rfl⟩, hT.1, hu, hPxy.1,
            hslope, hxformula⟩

private lemma three_square_products_impossible
    {r₁ r₂ r₃ z₁ z₂ z₃ : ℚ}
    (hr₁₂ : r₁ ≠ r₂) (hr₁₃ : r₁ ≠ r₃) (hr₂₃ : r₂ ≠ r₃)
    (hk₁ : (r₁ - r₂) * (r₁ - r₃) = z₁ ^ 2)
    (hk₂ : (r₂ - r₁) * (r₂ - r₃) = z₂ ^ 2)
    (hk₃ : (r₃ - r₁) * (r₃ - r₂) = z₃ ^ 2) :
    False := by
  have hvandermonde :
      (r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hr₁₂)
      (sub_ne_zero.mpr hr₁₃)) (sub_ne_zero.mpr hr₂₃)
  have hnegative :
      (z₁ * z₂ * z₃) ^ 2 =
        -(((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2) := by
    linear_combination
      (-z₂ ^ 2 * z₃ ^ 2) * hk₁ -
      ((r₁ - r₂) * (r₁ - r₃) * z₃ ^ 2) * hk₂ -
      ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₁) * (r₂ - r₃)) * hk₃
  have hpositive :
      (0 : ℚ) <
        ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 :=
    sq_pos_of_ne_zero hvandermonde
  nlinarith [sq_nonneg (z₁ * z₂ * z₃)]

private theorem three_halvable_two_torsion_points_impossible
    (E : WeierstrassCurve ℚ)
    (P₁ P₂ P₃ T₁ T₂ T₃ : (E⁄ℚ).Point)
    (hd₁ : (2 : ℕ) • P₁ = T₁) (hd₂ : (2 : ℕ) • P₂ = T₂)
    (hd₃ : (2 : ℕ) • P₃ = T₃)
    (ht₁ : (2 : ℕ) • T₁ = 0) (ht₂ : (2 : ℕ) • T₂ = 0)
    (ht₃ : (2 : ℕ) • T₃ = 0)
    (hn₁ : T₁ ≠ 0) (hn₂ : T₂ ≠ 0) (hn₃ : T₃ ≠ 0)
    (hn₁₂ : T₁ ≠ T₂) (hn₁₃ : T₁ ≠ T₃) (hn₂₃ : T₂ ≠ T₃) :
    False := by
  obtain ⟨r₁, u₁, x₁, y₁, s₁, ⟨hT₁, hT₁eq⟩,
      hEr₁, hu₁, hEx₁, hs₁, hx₁⟩ :=
    exists_halving_data P₁ T₁ hd₁ ht₁ hn₁
  obtain ⟨r₂, u₂, x₂, y₂, s₂, ⟨hT₂, hT₂eq⟩,
      hEr₂, hu₂, hEx₂, hs₂, hx₂⟩ :=
    exists_halving_data P₂ T₂ hd₂ ht₂ hn₂
  obtain ⟨r₃, u₃, x₃, y₃, s₃, ⟨hT₃, hT₃eq⟩,
      hEr₃, hu₃, hEx₃, hs₃, hx₃⟩ :=
    exists_halving_data P₃ T₃ hd₃ ht₃ hn₃
  have hr₁₂ : r₁ ≠ r₂ := by
    intro h
    have hu : u₁ = u₂ := by
      simp only [WeierstrassCurve.Affine.negY] at hu₁ hu₂
      rw [h] at hu₁
      linarith
    apply hn₁₂
    calc
      T₁ = WeierstrassCurve.Affine.Point.some r₁ u₁ hT₁ := hT₁eq
      _ = WeierstrassCurve.Affine.Point.some r₂ u₂ hT₂ := by
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨h, hu⟩
      _ = T₂ := hT₂eq.symm
  have hr₁₃ : r₁ ≠ r₃ := by
    intro h
    have hu : u₁ = u₃ := by
      simp only [WeierstrassCurve.Affine.negY] at hu₁ hu₃
      rw [h] at hu₁
      linarith
    apply hn₁₃
    calc
      T₁ = WeierstrassCurve.Affine.Point.some r₁ u₁ hT₁ := hT₁eq
      _ = WeierstrassCurve.Affine.Point.some r₃ u₃ hT₃ := by
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨h, hu⟩
      _ = T₃ := hT₃eq.symm
  have hr₂₃ : r₂ ≠ r₃ := by
    intro h
    have hu : u₂ = u₃ := by
      simp only [WeierstrassCurve.Affine.negY] at hu₂ hu₃
      rw [h] at hu₂
      linarith
    apply hn₂₃
    calc
      T₂ = WeierstrassCurve.Affine.Point.some r₂ u₂ hT₂ := hT₂eq
      _ = WeierstrassCurve.Affine.Point.some r₃ u₃ hT₃ := by
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨h, hu⟩
      _ = T₃ := hT₃eq.symm
  simp only [WeierstrassCurve.Affine.negY] at hu₁ hu₂ hu₃
  rw [WeierstrassCurve.Affine.equation_iff] at hEr₁ hEr₂ hEr₃ hEx₁ hEx₂ hEx₃
  have hroot₁ :
      4 * r₁ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * r₁ ^ 2 +
        (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * r₁ +
        ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination
      (2 * u₁ + (E⁄ℚ).a₁ * r₁ + (E⁄ℚ).a₃) * hu₁ - 4 * hEr₁
  have hroot₂ :
      4 * r₂ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * r₂ ^ 2 +
        (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * r₂ +
        ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination
      (2 * u₂ + (E⁄ℚ).a₁ * r₂ + (E⁄ℚ).a₃) * hu₂ - 4 * hEr₂
  have hroot₃ :
      4 * r₃ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * r₃ ^ 2 +
        (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * r₃ +
        ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination
      (2 * u₃ + (E⁄ℚ).a₁ * r₃ + (E⁄ℚ).a₃) * hu₃ - 4 * hEr₃
  obtain ⟨hb, hc, hd⟩ :=
    cubic_coefficients_of_three_roots hr₁₂ hr₁₃ hr₂₃
      hroot₁ hroot₂ hroot₃
  have hk₁ : (r₁ - r₂) * (r₁ - r₃) = (x₁ - r₁) ^ 2 :=
    halving_forces_square hEx₁ hb hc hd hs₁ hx₁
  have hb₂ :
      (E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂ = -4 * (r₂ + r₁ + r₃) := by
    linear_combination hb
  have hc₂ :
      2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄ =
        4 * (r₂ * r₁ + r₂ * r₃ + r₁ * r₃) := by
    linear_combination hc
  have hd₂ :
      (E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆ = -4 * (r₂ * r₁ * r₃) := by
    linear_combination hd
  have hk₂ : (r₂ - r₁) * (r₂ - r₃) = (x₂ - r₂) ^ 2 :=
    halving_forces_square hEx₂ hb₂ hc₂ hd₂ hs₂ hx₂
  have hb₃ :
      (E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂ = -4 * (r₃ + r₁ + r₂) := by
    linear_combination hb
  have hc₃ :
      2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄ =
        4 * (r₃ * r₁ + r₃ * r₂ + r₁ * r₂) := by
    linear_combination hc
  have hd₃ :
      (E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆ = -4 * (r₃ * r₁ * r₂) := by
    linear_combination hd
  have hk₃ : (r₃ - r₁) * (r₃ - r₂) = (x₃ - r₃) ^ 2 :=
    halving_forces_square hEx₃ hb₃ hc₃ hd₃ hs₃ hx₃
  exact three_square_products_impossible hr₁₂ hr₁₃ hr₂₃ hk₁ hk₂ hk₃

/-- An elliptic curve over `ℚ` cannot have full rational `4`-torsion. -/
theorem not_injective_zmod_four_square
    (E : WeierstrassCurve ℚ)
    (φ : (ZMod 4 × ZMod 4) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  let P₁ : (E⁄ℚ).Point := φ (1, 0)
  let P₂ : (E⁄ℚ).Point := φ (0, 1)
  let P₃ : (E⁄ℚ).Point := φ (1, 1)
  let T₁ : (E⁄ℚ).Point := φ (2, 0)
  let T₂ : (E⁄ℚ).Point := φ (0, 2)
  let T₃ : (E⁄ℚ).Point := φ (2, 2)
  have hd₁ : (2 : ℕ) • P₁ = T₁ := by
    dsimp [P₁, T₁]
    rw [← map_nsmul]
    congr 1
  have hd₂ : (2 : ℕ) • P₂ = T₂ := by
    dsimp [P₂, T₂]
    rw [← map_nsmul]
    congr 1
  have hd₃ : (2 : ℕ) • P₃ = T₃ := by
    dsimp [P₃, T₃]
    rw [← map_nsmul]
    congr 1
  have ht₁ : (2 : ℕ) • T₁ = 0 := by
    dsimp [T₁]
    rw [← map_nsmul, show (2 : ℕ) • ((2 : ZMod 4), (0 : ZMod 4)) = 0 by decide,
      map_zero]
  have ht₂ : (2 : ℕ) • T₂ = 0 := by
    dsimp [T₂]
    rw [← map_nsmul, show (2 : ℕ) • ((0 : ZMod 4), (2 : ZMod 4)) = 0 by decide,
      map_zero]
  have ht₃ : (2 : ℕ) • T₃ = 0 := by
    dsimp [T₃]
    rw [← map_nsmul, show (2 : ℕ) • ((2 : ZMod 4), (2 : ZMod 4)) = 0 by decide,
      map_zero]
  have hn₁ : T₁ ≠ 0 := by
    intro h
    exact (by decide : ((2 : ZMod 4), (0 : ZMod 4)) ≠ 0)
      (hφ (by simpa [T₁] using h))
  have hn₂ : T₂ ≠ 0 := by
    intro h
    exact (by decide : ((0 : ZMod 4), (2 : ZMod 4)) ≠ 0)
      (hφ (by simpa [T₂] using h))
  have hn₃ : T₃ ≠ 0 := by
    intro h
    exact (by decide : ((2 : ZMod 4), (2 : ZMod 4)) ≠ 0)
      (hφ (by simpa [T₃] using h))
  have hn₁₂ : T₁ ≠ T₂ := by
    intro h
    exact (by decide :
      ((2 : ZMod 4), (0 : ZMod 4)) ≠ ((0 : ZMod 4), (2 : ZMod 4)))
      (hφ (by simpa [T₁, T₂] using h))
  have hn₁₃ : T₁ ≠ T₃ := by
    intro h
    exact (by decide :
      ((2 : ZMod 4), (0 : ZMod 4)) ≠ ((2 : ZMod 4), (2 : ZMod 4)))
      (hφ (by simpa [T₁, T₃] using h))
  have hn₂₃ : T₂ ≠ T₃ := by
    intro h
    exact (by decide :
      ((0 : ZMod 4), (2 : ZMod 4)) ≠ ((2 : ZMod 4), (2 : ZMod 4)))
      (hφ (by simpa [T₂, T₃] using h))
  exact three_halvable_two_torsion_points_impossible E
    P₁ P₂ P₃ T₁ T₂ T₃ hd₁ hd₂ hd₃ ht₁ ht₂ ht₃
    hn₁ hn₂ hn₃ hn₁₂ hn₁₃ hn₂₃

end FullFour

end LeanPool.MazurTorsionFoundations
