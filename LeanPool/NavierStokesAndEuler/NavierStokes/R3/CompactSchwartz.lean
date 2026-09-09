/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ProblemStatement
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

@[expose] public section

/-!
# Compact smooth test functions as Schwartz functions

Compact support is preserved by iterated derivatives. Consequently each
polynomially weighted derivative norm is continuous with compact support and
is bounded, giving a Schwartz map with the original function as its coercion.
-/


noncomputable section

open Set
open scoped ContDiff

namespace NavierStokesR3.CompactSchwartz

open ProblemStatement

/-- Polynomially weighted derivative norms of compact smooth functions are
bounded on all of space. -/
theorem weighted_derivative_bound (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (k n : ℕ) :
    ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  have hcompact :
      HasCompactSupport (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
    (hc.iteratedFDeriv n).norm.mul_left
  have hcontinuous :
      Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
    (continuous_norm.pow k).mul (hf.continuous_iteratedFDeriv (mod_cast le_top)).norm
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hcontinuous
  exact ⟨C, fun x => (le_abs_self _).trans (hC x)⟩

/-- A compactly supported smooth function defines a Schwartz function. -/
def ofCompactSupport (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : SchwartzMap Space ℂ where
  toFun := f
  smooth' := hf
  decay' := weighted_derivative_bound f hf hc

@[simp] theorem coe_ofCompactSupport (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    (ofCompactSupport f hf hc : Space → ℂ) = f := rfl

@[simp] theorem ofCompactSupport_apply (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (x : Space) :
    ofCompactSupport f hf hc x = f x := rfl

/-- Passing to the Schwartz wrapper preserves topological support exactly. -/
@[simp] theorem tsupport_ofCompactSupport (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    tsupport (ofCompactSupport f hf hc) = tsupport f := rfl

/-- Each iterated derivative remains supported inside the original support. -/
theorem tsupport_iteratedFDeriv_subset (f : Space → ℂ) (n : ℕ) :
    tsupport (iteratedFDeriv ℝ n f) ⊆ tsupport f :=
  _root_.tsupport_iteratedFDeriv_subset n

/-- Each iterated derivative of a compactly supported test has compact support. -/
theorem hasCompactSupport_iteratedFDeriv (f : Space → ℂ)
    (hc : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedFDeriv ℝ n f) :=
  hc.iteratedFDeriv n

end NavierStokesR3.CompactSchwartz
