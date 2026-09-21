/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.Basic
public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.Basic

/-! # Two-variable RPolynomial definitions -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

/-- The canonical two-variable specialization of the regularized Carlson polynomial. -/
abbrev regRPolynomial (n : ℕ) (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  regCarlsonRPolynomial n (pair b₀ b₁) (pair z₀ z₁)

end DirichletTransform.TwoVariable
