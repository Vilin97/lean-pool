/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Characteristic equation for the free--free beam

This file isolates the elementary ODE and determinant calculation beneath the
Section 9 analytic model.  For a positive fourth-root parameter `beta`, every
classical solution of `u'''' = beta^4 u` is a linear combination of cosine,
sine, hyperbolic cosine, and hyperbolic sine.  The free-end conditions
`u''(0)=u'''(0)=u''(1)=u'''(1)=0` reduce the coefficient system to a two by two
matrix whose determinant is

`2 * (1 - cos beta * cosh beta)`.

Consequently a nonzero positive-frequency mode satisfies
`cos beta * cosh beta = 1`.  This algebraic reduction is independent of the
Sobolev realization of the fourth-derivative operator.
-/

namespace TauCeti
namespace DavisKahan
namespace FreeBeam

noncomputable section

/-- Classical four-parameter solution of `u'''' = beta^4 u`. -/
def mode (beta a b c d x : ℝ) : ℝ :=
  a * Real.cos (beta * x) + b * Real.sin (beta * x) +
    c * Real.cosh (beta * x) + d * Real.sinh (beta * x)

/-- Closed form of the first derivative. -/
def modeD1 (beta a b c d x : ℝ) : ℝ :=
  beta * (-a * Real.sin (beta * x) + b * Real.cos (beta * x) +
    c * Real.sinh (beta * x) + d * Real.cosh (beta * x))

/-- Closed form of the second derivative. -/
def modeD2 (beta a b c d x : ℝ) : ℝ :=
  beta ^ 2 * (-a * Real.cos (beta * x) - b * Real.sin (beta * x) +
    c * Real.cosh (beta * x) + d * Real.sinh (beta * x))

/-- Closed form of the third derivative. -/
def modeD3 (beta a b c d x : ℝ) : ℝ :=
  beta ^ 3 * (a * Real.sin (beta * x) - b * Real.cos (beta * x) +
    c * Real.sinh (beta * x) + d * Real.cosh (beta * x))

/-- Closed form of the fourth derivative. -/
def modeD4 (beta a b c d x : ℝ) : ℝ := beta ^ 4 * mode beta a b c d x

-- `(try rfl) <;> ring` cannot become `(try rfl); ring`, which is what the
-- linter suggests: on the branches where `rfl` closes the goal, `<;>` over zero
-- goals is a no-op while `;` raises "No goals to be solved".  Verified by build.
/-- The displayed first derivative is correct. -/
theorem hasDerivAt_mode (beta a b c d x : ℝ) :
    HasDerivAt (mode beta a b c d) (modeD1 beta a b c d x) x := by
  unfold mode modeD1
  convert
    (((((Real.hasDerivAt_cos (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul a).add
      (((Real.hasDerivAt_sin (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul b)).add
      (((Real.hasDerivAt_cosh (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul c)).add
      (((Real.hasDerivAt_sinh (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul d)
    using 1 <;> (try rfl) <;> ring

-- `(try rfl) <;> ring` cannot become `(try rfl); ring`, which is what the
-- linter suggests: on the branches where `rfl` closes the goal, `<;>` over zero
-- goals is a no-op while `;` raises "No goals to be solved".  Verified by build.
/-- The displayed second derivative is the derivative of `modeD1`. -/
theorem hasDerivAt_modeD1 (beta a b c d x : ℝ) :
    HasDerivAt (modeD1 beta a b c d) (modeD2 beta a b c d x) x := by
  unfold modeD1 modeD2
  convert
    ((((((Real.hasDerivAt_sin (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul (-a)).add
      (((Real.hasDerivAt_cos (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul b)).add
      (((Real.hasDerivAt_sinh (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul c)).add
      (((Real.hasDerivAt_cosh (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul d)).const_mul beta
    using 1 <;> (try rfl) <;> ring

/-- The displayed third derivative is the derivative of `modeD2`. -/
theorem hasDerivAt_modeD2 (beta a b c d x : ℝ) :
    HasDerivAt (modeD2 beta a b c d) (modeD3 beta a b c d x) x := by
  unfold modeD2 modeD3
  convert
    ((((((Real.hasDerivAt_cos (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul (-a)).add
      (((Real.hasDerivAt_sin (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul (-b))).add
      (((Real.hasDerivAt_cosh (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul c)).add
      (((Real.hasDerivAt_sinh (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul d)).const_mul (beta ^ 2)
    using 1 <;> (try rfl) <;> (try funext y) <;> (try simp only [Function.comp_apply, Pi.add_apply]) <;> ring

/-- The displayed fourth derivative is the derivative of `modeD3`. -/
theorem hasDerivAt_modeD3 (beta a b c d x : ℝ) :
    HasDerivAt (modeD3 beta a b c d) (modeD4 beta a b c d x) x := by
  unfold modeD3 modeD4 mode
  convert
    ((((((Real.hasDerivAt_sin (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul a).add
      (((Real.hasDerivAt_cos (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul (-b))).add
      (((Real.hasDerivAt_sinh (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul c)).add
      (((Real.hasDerivAt_cosh (beta * x)).comp x
          ((hasDerivAt_const x beta).mul (hasDerivAt_id x))).const_mul d)).const_mul (beta ^ 3)
    using 1 <;> (try rfl) <;> (try funext y) <;> (try simp only [Function.comp_apply, Pi.add_apply]) <;> ring

/-- The mode solves the fourth-order eigenvalue equation. -/
theorem mode_fourth_derivative (beta a b c d x : ℝ) :
    deriv (modeD3 beta a b c d) x = beta ^ 4 * mode beta a b c d x := by
  exact (hasDerivAt_modeD3 beta a b c d x).deriv

/-- Free-end boundary conditions for a classical mode. -/
def FreeBoundary (beta a b c d : ℝ) : Prop :=
  modeD2 beta a b c d 0 = 0 ∧
  modeD3 beta a b c d 0 = 0 ∧
  modeD2 beta a b c d 1 = 0 ∧
  modeD3 beta a b c d 1 = 0

/-- At nonzero frequency the left free-end conditions identify the hyperbolic
coefficients with the trigonometric coefficients. -/
theorem left_boundary_coefficients
    {beta a b c d : ℝ} (hbeta : beta ≠ 0)
    (h2 : modeD2 beta a b c d 0 = 0)
    (h3 : modeD3 beta a b c d 0 = 0) :
    c = a ∧ d = b := by
  have hb2 : beta ^ 2 ≠ 0 := pow_ne_zero _ hbeta
  have hb3 : beta ^ 3 ≠ 0 := pow_ne_zero _ hbeta
  have hca : -a + c = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hb2
    simpa [modeD2] using h2
  have hdb : -b + d = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hb3
    simpa [modeD3] using h3
  constructor <;> linarith

/-- First row of the reduced right-end boundary matrix. -/
def boundaryA (beta : ℝ) : ℝ := Real.cosh beta - Real.cos beta

/-- Upper-right entry of the reduced right-end boundary matrix. -/
def boundaryB (beta : ℝ) : ℝ := Real.sinh beta - Real.sin beta

/-- Lower-left entry of the reduced right-end boundary matrix. -/
def boundaryC (beta : ℝ) : ℝ := Real.sinh beta + Real.sin beta

/-- Determinant of the reduced two by two boundary matrix. -/
def boundaryDet (beta : ℝ) : ℝ :=
  boundaryA beta ^ 2 - boundaryB beta * boundaryC beta

/-- The determinant reduces to the classical free--free characteristic
expression. -/
theorem boundaryDet_eq (beta : ℝ) :
    boundaryDet beta = 2 * (1 - Real.cos beta * Real.cosh beta) := by
  have htrig := Real.sin_sq_add_cos_sq beta
  have hhyper := Real.cosh_sq_sub_sinh_sq beta
  unfold boundaryDet boundaryA boundaryB boundaryC
  nlinarith

/-- Right-end boundary equations after eliminating the left-end coefficients. -/
theorem right_boundary_reduced
    {beta a b : ℝ} (hbeta : beta ≠ 0)
    (h2 : modeD2 beta a b a b 1 = 0)
    (h3 : modeD3 beta a b a b 1 = 0) :
    boundaryA beta * a + boundaryB beta * b = 0 ∧
      boundaryC beta * a + boundaryA beta * b = 0 := by
  have hb2 : beta ^ 2 ≠ 0 := pow_ne_zero _ hbeta
  have hb3 : beta ^ 3 ≠ 0 := pow_ne_zero _ hbeta
  constructor
  · apply (mul_eq_zero.mp ?_).resolve_left hb2
    simp only [modeD2, boundaryA, boundaryB, mul_one] at h2 ⊢
    linear_combination h2
  · apply (mul_eq_zero.mp ?_).resolve_left hb3
    simp only [modeD3, boundaryA, boundaryC, mul_one] at h3 ⊢
    linear_combination h3

/-- A nonzero vector in the kernel of a two by two matrix forces its
determinant to vanish. -/
theorem two_by_two_det_eq_zero_of_nontrivial_kernel
    {A B C a b : ℝ}
    (h1 : A * a + B * b = 0)
    (h2 : C * a + A * b = 0)
    (hnonzero : a ≠ 0 ∨ b ≠ 0) :
    A ^ 2 - B * C = 0 := by
  have ha : (A ^ 2 - B * C) * a = 0 := by
    calc
      (A ^ 2 - B * C) * a
          = A * (A * a + B * b) - B * (C * a + A * b) := by ring
      _ = 0 := by rw [h1, h2]; ring
  have hb : (A ^ 2 - B * C) * b = 0 := by
    calc
      (A ^ 2 - B * C) * b
          = A * (C * a + A * b) - C * (A * a + B * b) := by ring
      _ = 0 := by rw [h1, h2]; ring
  rcases hnonzero with ha0 | hb0
  · exact (mul_eq_zero.mp ha).resolve_right ha0
  · exact (mul_eq_zero.mp hb).resolve_right hb0

/-- Characteristic function for positive free-beam frequencies. -/
def characteristic (beta : ℝ) : ℝ :=
  Real.cos beta * Real.cosh beta - 1

/-- Every nontrivial nonzero-frequency free-end mode satisfies the classical
characteristic equation. -/
theorem characteristic_eq_zero_of_freeBoundary
    {beta a b c d : ℝ} (hbeta : beta ≠ 0)
    (hboundary : FreeBoundary beta a b c d)
    (hnonzero : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    characteristic beta = 0 := by
  rcases hboundary with ⟨h20, h30, h21, h31⟩
  obtain ⟨hc, hd⟩ := left_boundary_coefficients hbeta h20 h30
  subst c
  subst d
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    tauto
  obtain ⟨hr1, hr2⟩ := right_boundary_reduced hbeta h21 h31
  have hdet := two_by_two_det_eq_zero_of_nontrivial_kernel hr1 hr2 hab
  have hdet' : boundaryDet beta = 0 := hdet
  rw [boundaryDet_eq] at hdet'
  unfold characteristic
  linarith

/-- The rational number `4.73` has fourth power strictly above `500`. -/
theorem four_seventy_three_pow_four_gt_five_hundred :
    (500 : ℝ) < ((473 : ℝ) / 100) ^ 4 := by
  norm_num

/-- Exact analytic root-localization interface still required by the free-beam
spectral realization.  It isolates root localization from the operator-domain
and self-adjointness campaigns. -/
structure PositiveRootLocalization where
  /-- The smallest positive root of the free-beam characteristic equation. -/
  firstPositiveRoot : ℝ
  firstPositiveRoot_pos : 0 < firstPositiveRoot
  firstPositiveRoot_characteristic : characteristic firstPositiveRoot = 0
  minimal : ∀ beta : ℝ, 0 < beta → characteristic beta = 0 →
    firstPositiveRoot ≤ beta
  lower_bound : (473 : ℝ) / 100 < firstPositiveRoot

/-- Every positive characteristic root has fourth power above `500` once the
first root has been localized beyond `4.73`. -/
theorem positive_root_fourth_power_gt_five_hundred
    (L : PositiveRootLocalization) {beta : ℝ}
    (hbeta : 0 < beta) (hroot : characteristic beta = 0) :
    500 < beta ^ 4 := by
  have h473 : (473 : ℝ) / 100 < beta :=
    lt_of_lt_of_le L.lower_bound (L.minimal beta hbeta hroot)
  have hnonneg : 0 ≤ (473 : ℝ) / 100 := by norm_num
  have hpow : ((473 : ℝ) / 100) ^ 4 < beta ^ 4 := by
    exact pow_lt_pow_left₀ h473 hnonneg (by norm_num)
  exact four_seventy_three_pow_four_gt_five_hundred.trans hpow

end
end FreeBeam
end DavisKahan
end TauCeti
