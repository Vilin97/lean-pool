/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Data.Rat.Cast.Order

/-!
# Dense exact bivariate polynomials

The outer list records increasing powers of `x`; each inner list records increasing powers of
`y`. Transparent list arithmetic lets the kernel normalize small polynomial certificates.
-/

@[expose] public section

namespace LeanPool.Besicovitch

/-- A dense univariate polynomial with coefficients in increasing degree order. -/
abbrev DenseUnivariate := List ℚ

namespace DenseUnivariate

/-- Add coefficient lists, padding the shorter list by zeros. -/
def add : DenseUnivariate → DenseUnivariate → DenseUnivariate
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

/-- Multiply every coefficient by a rational scalar. -/
def scale (a : ℚ) (p : DenseUnivariate) : DenseUnivariate :=
  p.map (a * ·)

/-- Negate every coefficient. -/
def neg (p : DenseUnivariate) : DenseUnivariate :=
  p.map (-·)

/-- Exact polynomial multiplication by coefficient convolution. -/
def mul : DenseUnivariate → DenseUnivariate → DenseUnivariate
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

/-- Evaluate a dense polynomial over the reals by Horner's rule. -/
noncomputable def eval : DenseUnivariate → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => a + x * eval p x

/-- The sum of the absolute values of the coefficients. -/
def coefficientL1Norm (p : DenseUnivariate) : ℚ :=
  (p.map abs).sum

/-- Formal differentiation, using `P = a + x Q` and `P' = Q + x Q'`. -/
def deriv : DenseUnivariate → DenseUnivariate
  | [] => []
  | _ :: p => add p (0 :: deriv p)

theorem coefficientL1Norm_nonneg (p : DenseUnivariate) : 0 ≤ coefficientL1Norm p := by
  apply List.sum_nonneg
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨b, -, rfl⟩ := ha
  exact abs_nonneg b

theorem eval_add (p q : DenseUnivariate) (x : ℝ) :
    eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p hp =>
      cases q with
      | nil => simp [add, eval]
      | cons b q => simp [add, eval, hp]; ring

theorem eval_scale (a : ℚ) (p : DenseUnivariate) (x : ℝ) :
    eval (scale a p) x = a * eval p x := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p hp =>
      simp only [scale] at hp
      simp [scale, eval, hp]
      ring

theorem eval_neg (p : DenseUnivariate) (x : ℝ) : eval (neg p) x = -eval p x := by
  induction p with
  | nil => simp [neg, eval]
  | cons a p hp =>
      simp only [neg] at hp
      simp [neg, eval, hp]
      ring

theorem eval_mul (p q : DenseUnivariate) (x : ℝ) :
    eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p hp => simp [mul, eval, eval_add, eval_scale, hp]; ring

theorem eval_deriv_cons (a : ℚ) (p : DenseUnivariate) (x : ℝ) :
    eval (deriv (a :: p)) x = eval p x + x * eval (deriv p) x := by
  simp [deriv, eval_add, eval]

/-- Formal differentiation computes the derivative of dense evaluation. -/
theorem hasDerivAt_eval (p : DenseUnivariate) (x : ℝ) :
    letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
    letI : Module ℝ ℝ := NormedField.toNormedSpace.toModule
    HasDerivAt (eval p) (eval (deriv p) x) x := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := NormedField.toNormedSpace.toModule
  induction p with
  | nil => simpa [eval, deriv] using hasDerivAt_const x (0 : ℝ)
  | cons a p hp =>
      convert (hasDerivAt_const x (a : ℝ)).add ((hasDerivAt_id x).mul hp) using 1
      · ext z
        simp [eval]
      · simp [eval_deriv_cons]

/-- The coefficient norm bounds evaluation on the unit interval. -/
theorem abs_eval_le_coefficientL1Norm (p : DenseUnivariate) {x : ℝ} (hx : |x| ≤ 1) :
    |eval p x| ≤ (coefficientL1Norm p : ℝ) := by
  induction p with
  | nil => simp [eval, coefficientL1Norm]
  | cons a p hp =>
      rw [eval, coefficientL1Norm, List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_abs]
      calc
        |(a : ℝ) + x * eval p x| ≤ |(a : ℝ)| + |x| * |eval p x| := by
          simpa only [abs_mul] using abs_add_le (a : ℝ) (x * eval p x)
        _ ≤ |(a : ℝ)| + |eval p x| := by
          gcongr
          exact mul_le_of_le_one_left (abs_nonneg _) hx
        _ ≤ |(a : ℝ)| + (coefficientL1Norm p : ℝ) := add_le_add_right hp _

end DenseUnivariate

/-- A dense bivariate polynomial, with the outer index giving the first-variable degree. -/
abbrev DenseBivariatePolynomial := List DenseUnivariate

namespace DenseBivariatePolynomial

/-- Add two dense bivariate polynomials. -/
def add : DenseBivariatePolynomial → DenseBivariatePolynomial → DenseBivariatePolynomial
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => DenseUnivariate.add a b :: add p q

/-- Multiply by a rational scalar. -/
def scale (a : ℚ) (p : DenseBivariatePolynomial) : DenseBivariatePolynomial :=
  p.map (DenseUnivariate.scale a)

/-- Negate a dense bivariate polynomial. -/
def neg (p : DenseBivariatePolynomial) : DenseBivariatePolynomial :=
  p.map DenseUnivariate.neg

/-- Multiply each outer coefficient by a univariate polynomial. -/
def scaleRow (a : DenseUnivariate) (p : DenseBivariatePolynomial) : DenseBivariatePolynomial :=
  p.map (DenseUnivariate.mul a)

/-- Exact bivariate polynomial multiplication. -/
def mul : DenseBivariatePolynomial → DenseBivariatePolynomial → DenseBivariatePolynomial
  | [], _ => []
  | a :: p, q => add (scaleRow a q) ([] :: mul p q)

/-- A constant bivariate polynomial. -/
def constant (a : ℚ) : DenseBivariatePolynomial := [[a]]

/-- The first variable. -/
def first : DenseBivariatePolynomial := [[0], [1]]

/-- The second variable. -/
def second : DenseBivariatePolynomial := [[0, 1]]

/-- Natural powers of a dense bivariate polynomial. -/
def pow (p : DenseBivariatePolynomial) : ℕ → DenseBivariatePolynomial
  | 0 => constant 1
  | n + 1 => mul (pow p n) p

/-- Evaluate a dense bivariate polynomial by nested Horner rules. -/
noncomputable def eval : DenseBivariatePolynomial → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: p, x, y => DenseUnivariate.eval a y + x * eval p x y

/-- The sum of the absolute values of all coefficients. -/
def coefficientL1Norm (p : DenseBivariatePolynomial) : ℚ :=
  (p.map DenseUnivariate.coefficientL1Norm).sum

/-- Formal differentiation with respect to the first variable. -/
def derivFirst : DenseBivariatePolynomial → DenseBivariatePolynomial
  | [] => []
  | _ :: p => add p ([] :: derivFirst p)

/-- Formal differentiation with respect to the second variable. -/
def derivSecond (p : DenseBivariatePolynomial) : DenseBivariatePolynomial :=
  p.map DenseUnivariate.deriv

theorem coefficientL1Norm_nonneg (p : DenseBivariatePolynomial) : 0 ≤ coefficientL1Norm p := by
  apply List.sum_nonneg
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨b, -, rfl⟩ := ha
  exact DenseUnivariate.coefficientL1Norm_nonneg b

theorem eval_add (p q : DenseBivariatePolynomial) (x y : ℝ) :
    eval (add p q) x y = eval p x y + eval q x y := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p hp =>
      cases q with
      | nil => simp [add, eval]
      | cons b q => simp [add, eval, DenseUnivariate.eval_add, hp]; ring

theorem eval_scale (a : ℚ) (p : DenseBivariatePolynomial) (x y : ℝ) :
    eval (scale a p) x y = a * eval p x y := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p hp =>
      simp only [scale] at hp
      simp [scale, eval, DenseUnivariate.eval_scale, hp]
      ring

theorem eval_neg (p : DenseBivariatePolynomial) (x y : ℝ) :
    eval (neg p) x y = -eval p x y := by
  induction p with
  | nil => simp [neg, eval]
  | cons a p hp =>
      simp only [neg] at hp
      simp [neg, eval, DenseUnivariate.eval_neg, hp]
      ring

theorem eval_scaleRow (a : DenseUnivariate) (p : DenseBivariatePolynomial) (x y : ℝ) :
    eval (scaleRow a p) x y = DenseUnivariate.eval a y * eval p x y := by
  induction p with
  | nil => simp [scaleRow, eval]
  | cons b p hp =>
      simp only [scaleRow] at hp
      simp [scaleRow, eval, DenseUnivariate.eval_mul, hp]
      ring

theorem eval_mul (p q : DenseBivariatePolynomial) (x y : ℝ) :
    eval (mul p q) x y = eval p x y * eval q x y := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p hp => simp [mul, eval, eval_add, eval_scaleRow, hp, DenseUnivariate.eval]; ring

theorem eval_constant (a : ℚ) (x y : ℝ) : eval (constant a) x y = a := by
  simp [constant, eval, DenseUnivariate.eval]

theorem eval_first (x y : ℝ) : eval first x y = x := by
  simp [first, eval, DenseUnivariate.eval]

theorem eval_second (x y : ℝ) : eval second x y = y := by
  simp [second, eval, DenseUnivariate.eval]

theorem eval_pow (p : DenseBivariatePolynomial) (n : ℕ) (x y : ℝ) :
    eval (pow p n) x y = eval p x y ^ n := by
  induction n with
  | zero => simp [pow, eval_constant]
  | succ n hn => simp [pow, eval_mul, hn, pow_succ]

theorem eval_derivFirst_cons (a : DenseUnivariate) (p : DenseBivariatePolynomial)
    (x y : ℝ) :
    eval (derivFirst (a :: p)) x y = eval p x y + x * eval (derivFirst p) x y := by
  simp [derivFirst, eval_add, eval, DenseUnivariate.eval]

/-- `derivFirst` computes the derivative along a first-coordinate line. -/
theorem hasDerivAt_eval_first (p : DenseBivariatePolynomial) (x y : ℝ) :
    letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
    letI : Module ℝ ℝ := NormedField.toNormedSpace.toModule
    HasDerivAt (fun u ↦ eval p u y) (eval (derivFirst p) x y) x := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := NormedField.toNormedSpace.toModule
  induction p with
  | nil => simpa [eval, derivFirst] using hasDerivAt_const x (0 : ℝ)
  | cons a p hp =>
      convert (hasDerivAt_const x (DenseUnivariate.eval a y)).add
        ((hasDerivAt_id x).mul hp) using 1
      · ext z
        simp [eval]
      · simp [eval_derivFirst_cons]

/-- `derivSecond` computes the derivative along a second-coordinate line. -/
theorem hasDerivAt_eval_second (p : DenseBivariatePolynomial) (x y : ℝ) :
    letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
    letI : Module ℝ ℝ := NormedField.toNormedSpace.toModule
    HasDerivAt (fun v ↦ eval p x v) (eval (derivSecond p) x y) y := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := NormedField.toNormedSpace.toModule
  induction p with
  | nil => simpa [eval, derivSecond] using hasDerivAt_const y (0 : ℝ)
  | cons a p hp =>
      convert (DenseUnivariate.hasDerivAt_eval a y).add ((hasDerivAt_const y x).mul hp) using 1
      · ext z
        simp [eval]
      · simp [derivSecond, eval]

/-- The coefficient norm bounds evaluation on the real unit square. -/
theorem abs_eval_le_coefficientL1Norm (p : DenseBivariatePolynomial) {x y : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |eval p x y| ≤ (coefficientL1Norm p : ℝ) := by
  induction p with
  | nil => simp [eval, coefficientL1Norm]
  | cons a p hp =>
      rw [eval, coefficientL1Norm, List.map_cons, List.sum_cons, Rat.cast_add]
      calc
        |DenseUnivariate.eval a y + x * eval p x y| ≤
            |DenseUnivariate.eval a y| + |x| * |eval p x y| := by
          simpa only [abs_mul] using abs_add_le (DenseUnivariate.eval a y) (x * eval p x y)
        _ ≤ (DenseUnivariate.coefficientL1Norm a : ℝ) + |eval p x y| := by
          gcongr
          · exact DenseUnivariate.abs_eval_le_coefficientL1Norm a hy
          · exact mul_le_of_le_one_left (abs_nonneg _) hx
        _ ≤ (DenseUnivariate.coefficientL1Norm a : ℝ) +
            (coefficientL1Norm p : ℝ) := add_le_add_right hp _

/-- The first formal derivative bounds variation along a horizontal line in the unit square. -/
theorem abs_eval_sub_le_derivFirst (p : DenseBivariatePolynomial) {x₁ x₂ y : ℝ}
    (hx₁ : |x₁| ≤ 1) (hx₂ : |x₂| ≤ 1) (hy : |y| ≤ 1) :
    |eval p x₂ y - eval p x₁ y| ≤
      (coefficientL1Norm (derivFirst p) : ℝ) * |x₂ - x₁| := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := NormedField.toNormedSpace.toModule
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u ↦ eval p u y) (f' := fun u ↦ eval (derivFirst p) u y)
    (fun u _ ↦ (hasDerivAt_eval_first p u y).hasDerivWithinAt)
    (fun u hu ↦ abs_eval_le_coefficientL1Norm (derivFirst p)
      (abs_le.mpr ⟨by linarith [hu.1], hu.2⟩) hy) (abs_le.mp hx₁) (abs_le.mp hx₂)
  simpa only [Real.norm_eq_abs] using h

/-- The second formal derivative bounds variation along a vertical line in the unit square. -/
theorem abs_eval_sub_le_derivSecond (p : DenseBivariatePolynomial) {x y₁ y₂ : ℝ}
    (hx : |x| ≤ 1) (hy₁ : |y₁| ≤ 1) (hy₂ : |y₂| ≤ 1) :
    |eval p x y₂ - eval p x y₁| ≤
      (coefficientL1Norm (derivSecond p) : ℝ) * |y₂ - y₁| := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := NormedField.toNormedSpace.toModule
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun v ↦ eval p x v) (f' := fun v ↦ eval (derivSecond p) x v)
    (fun v _ ↦ (hasDerivAt_eval_second p x v).hasDerivWithinAt)
    (fun v hv ↦ abs_eval_le_coefficientL1Norm (derivSecond p) hx
      (abs_le.mpr ⟨by linarith [hv.1], hv.2⟩)) (abs_le.mp hy₁) (abs_le.mp hy₂)
  simpa only [Real.norm_eq_abs] using h

end DenseBivariatePolynomial

end LeanPool.Besicovitch
