/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Complex.Basic

/-! # Associated shifts and rational coefficient data -/


open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Integral shifts specifying a Carlson R-function associated to a fixed exponent and
Dirichlet parameter vector. -/
structure CarlsonRAssociatedShift (ι : Type*) where
  /-- Integral shift of the homogeneity parameter. -/
  exponent : ℤ
  /-- Integral shifts of the Dirichlet parameters. -/
  parameter : ι → ℤ

/-- Apply an associated shift to an R-function's exponent. -/
def CarlsonRAssociatedShift.exponentValue
    (s : CarlsonRAssociatedShift ι) (t : ℂ) : ℂ :=
  t + s.exponent

/-- Apply an associated shift to an R-function's Dirichlet parameters. -/
def CarlsonRAssociatedShift.parameterValue
    (s : CarlsonRAssociatedShift ι) (b : ι → ℂ) : ι → ℂ :=
  fun i => b i + s.parameter i

/-- A rational function in the Carlson variables, represented by a numerator and a nonzero
denominator polynomial. -/
structure CarlsonRRationalCoefficient (ι : Type*) where
  /-- Numerator polynomial. -/
  numerator : MvPolynomial ι ℂ
  /-- Denominator polynomial. -/
  denominator : MvPolynomial ι ℂ
  /-- The denominator is not the zero polynomial. -/
  denominator_ne_zero : denominator ≠ 0

/-- Evaluate a rational Carlson coefficient away from the zero set of its denominator. -/
def CarlsonRRationalCoefficient.eval
    (q : CarlsonRRationalCoefficient ι) (z : ι → ℂ) : ℂ :=
  q.numerator.eval z / q.denominator.eval z

end DirichletTransform
