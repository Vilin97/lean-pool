/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

@[expose] public section

/-! # Fourier test expressions used in pressure recovery -/


noncomputable section

open MeasureTheory

namespace NavierStokesR3.Comparison

open ProblemStatement

abbrev ComplexTest := SchwartzMap Space ℂ

def rieszSymbol (i j : Fin 3) (ξ : Space) : ℝ :=
  -(ξ i * ξ j) / ‖ξ‖ ^ 2

def rieszTest (i j : Fin 3) (ψ : ComplexTest) : Space → ℂ :=
  FourierTransform.fourierInv (fun ξ : Space =>
    (rieszSymbol i j ξ : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ)

def pressurePair (i j : Fin 3) (g : Space → ℝ) (ψ : ComplexTest) : ℂ :=
  ∫ x : Space, (g x : ℂ) * rieszTest i j ψ x

def fourierHNormSq (s : ℕ) (ψ : ComplexTest) : ℝ :=
  ∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ s * ‖(FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖ ^ 2

end NavierStokesR3.Comparison
