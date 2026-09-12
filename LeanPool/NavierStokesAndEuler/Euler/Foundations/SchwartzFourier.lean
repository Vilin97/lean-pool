/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
The Fourier integral bundled with Schwartz regularity. Keeping the underlying function
explicit lets Sobolev norms expose their formula without exposing the analytic proofs
of Fourier inversion and rapid decay.
-/

@[expose] public section

noncomputable section

namespace EulerSobolev

open scoped SchwartzMap FourierTransform ContDiff

variable {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The ordinary Fourier integral with its Schwartz smoothness and decay proofs. -/
def schwartzFourier (f : 𝓢(V, E)) : 𝓢(V, E) where
  toFun := 𝓕 (f : V → E)
  smooth' := by
    have h : ContDiff ℝ ∞ ((𝓕 f : 𝓢(V, E)) : V → E) := (𝓕 f : 𝓢(V, E)).smooth'
    rw [SchwartzMap.fourier_coe] at h
    exact h
  decay' := by
    have h : ∀ k n : ℕ, ∃ C : ℝ, ∀ x : V,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ((𝓕 f : 𝓢(V, E)) : V → E) x‖ ≤ C :=
      (𝓕 f : 𝓢(V, E)).decay'
    rw [SchwartzMap.fourier_coe] at h
    exact h

private theorem schwartzFourier_eq (f : 𝓢(V, E)) :
    schwartzFourier f = (𝓕 f : 𝓢(V, E)) := rfl

/-- The bundled Schwartz transform has exactly the ordinary Fourier integral as its values. -/
theorem schwartzFourier_apply (f : 𝓢(V, E)) (x : V) :
    schwartzFourier f x = 𝓕 (f : V → E) x := rfl

end EulerSobolev
