/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import LeanPool.SpectralTheory.Spectral.Spectral.Existence
import LeanPool.SpectralTheory.Spectral.PVM.Unbounded

/-!
# Measurable spectral functional calculus

This file defines the spectral functional calculus `spectralFuncCalc A hA f hf`
by applying a self-adjoint operator's representing PVM's unbounded integral to
a measurable function `f`, and shows it recovers `A` on the coordinate
function.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The measurable spectral functional calculus obtained from a spectral PVM representing `A`. -/
noncomputable def spectralFuncCalc
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (f : ℝ → ℂ) (hf : Measurable f) : E →ₗ.[ℂ] E :=
  (Classical.choose (spectral_theorem_existence A hA)).unboundedIntegral f hf

/-- Applying the spectral functional calculus to the coordinate function recovers `A`. -/
theorem spectralFuncCalc_coordinate
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    spectralFuncCalc A hA ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A := by
  unfold spectralFuncCalc
  exact Classical.choose_spec (spectral_theorem_existence A hA)
