/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SchwartzFourier
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ProblemStatement

/-! # Fourier test expressions used in pressure recovery -/

@[expose] public section



noncomputable section

open MeasureTheory

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- Complex test: an abbreviation for `SchwartzMap Space ℂ`. -/
abbrev ComplexTest := SchwartzMap Space ℂ

/-- Riesz symbol, given by `-(ξ i * ξ j) / ‖ξ‖ ^ 2`. -/
def rieszSymbol (i j : Fin 3) (ξ : Space) : ℝ :=
  -(ξ i * ξ j) / ‖ξ‖ ^ 2

/-- Riesz test, given by `FourierTransform.fourierInv (fun ξ : Space => (rieszSymbol i j ξ : ℂ)
* (EulerSobolev.schwartzFourier ψ) ξ)`. -/
def rieszTest (i j : Fin 3) (ψ : ComplexTest) : Space → ℂ :=
  FourierTransform.fourierInv (fun ξ : Space =>
    (rieszSymbol i j ξ : ℂ) * (EulerSobolev.schwartzFourier ψ) ξ)

/-- Pressure pair, given by `∫ x : Space, (g x : ℂ) * rieszTest i j ψ x`. -/
def pressurePair (i j : Fin 3) (g : Space → ℝ) (ψ : ComplexTest) : ℂ :=
  ∫ x : Space, (g x : ℂ) * rieszTest i j ψ x

/-- Fourier H norm sq, given by `∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ s * ‖(FourierTransform.fourierCLE
ℂ ComplexTest ψ) ξ‖ ^ 2`. -/
def fourierHNormSq (s : ℕ) (ψ : ComplexTest) : ℝ :=
  ∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ s * ‖(EulerSobolev.schwartzFourier ψ) ξ‖ ^ 2

end NavierStokesR3.Comparison
