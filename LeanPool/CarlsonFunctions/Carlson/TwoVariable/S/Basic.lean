/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.Basic
public import LeanPool.CarlsonFunctions.Carlson.S.Series

/-! # Two-variable S definitions -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

/-- The canonical two-variable specialization of the native regularized Carlson S-integral. -/
abbrev regSIntegral (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  regCarlsonSIntegral (pair b₀ b₁) (pair z₀ z₁)

/-- The canonical two-variable specialization of the native Carlson S-integral. -/
abbrev sIntegral (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  carlsonSIntegral (pair b₀ b₁) (pair z₀ z₁)

/-- The canonical two-variable specialization of Carlson's entire regularized S-series. -/
abbrev regSSeries (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  regCarlsonSSeries (pair z₀ z₁) (pair b₀ b₁)

end DirichletTransform.TwoVariable
