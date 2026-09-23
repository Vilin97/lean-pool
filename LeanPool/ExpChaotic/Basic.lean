/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exponential iterates and differentiation

Basic notation and differentiation of iterates. Normality is defined in
`LeanPool.ExpChaotic.Normality` using Mathlib's locally uniform convergence.

Part of Lasse Rempe's formalisation of Shen and Rempe-Gillen's exponential-map paper,
with generative AI assistance including Copilot, Claude, and particularly ChatGPT.
The initial proof architecture uses John Harrison's HOL Light formalisation.
See `LeanPool.ExpChaotic` for attribution and the upstream source.
-/

@[expose] public section

open Function Filter Set Metric
open scoped Topology NNReal Uniformity

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-- The complex exponential map. -/
abbrev exponentialMap : ℂ → ℂ := Complex.exp

/-- The `n`-th iterate of the complex exponential map. -/
abbrev expIterate (n : ℕ) : ℂ → ℂ := exponentialMap^[n]

/-- The zeroth iterate is the identity map. -/
@[simp]
theorem expIterate_zero (z : ℂ) :
    expIterate 0 z = z := by
  rfl

/-- Apply one more exponential after the `n`-th iterate. -/
@[simp]
theorem expIterate_succ (n : ℕ) (z : ℂ) :
    expIterate (n + 1) z =
      Complex.exp (expIterate n z) := by
  simp [expIterate, exponentialMap, Function.iterate_succ_apply']

/-- The closed horizontal strip used in Misiurewicz's proof. -/
def centralStrip : Set ℂ := {z | |z.im| ≤ Real.pi / 3}

/-- The right half-plane used in Misiurewicz's proof. -/
def rightHalfPlane : Set ℂ := {z | 4 < z.re}

/-- The wider closed strip occurring in Lemma 5. -/
def wideStrip : Set ℂ := {z | |z.im| ≤ 2 * Real.pi}

/-- A complex number lies on the embedded real axis. -/
def OnRealAxis (z : ℂ) : Prop := z.im = 0

/-- Some forward image of `V` meets the real axis. -/
def EventuallyMeetsRealAxis (V : Set ℂ) : Prop :=
  ∃ n : ℕ, ∃ z ∈ V, OnRealAxis (expIterate n z)

/-! ## Basic analytic infrastructure corresponding to the HOL preliminaries -/

/-- Chain rule for the exponential, corresponding to
`HAS_COMPLEX_DERIVATIVE_CEXP_COMPOSE` in HOL Light. -/
theorem hasDerivAt_exp_comp {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' z) :
    HasDerivAt (Complex.exp ∘ f)
      (f' * Complex.exp (f z)) z := by
  simpa [mul_comm] using
    (Complex.hasDerivAt_exp (f z)).comp z hf

/-- Composition with the exponential preserves complex differentiability at a point. -/
theorem differentiableAt_exp_comp
    {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ (fun w => Complex.exp (f w)) z := by
  exact Complex.differentiableAt_exp.comp z hf

/-- The exponential chain rule with the outer derivative written first. -/
theorem hasDerivAt_exp_comp'
    {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' z) :
    HasDerivAt (Complex.exp ∘ f)
      (Complex.exp (f z) * f') z := by
  exact (Complex.hasDerivAt_exp (f z)).comp z hf

/-- Every iterate of the exponential is complex differentiable. -/
theorem differentiable_expIterate (n : ℕ) :
    Differentiable ℂ (expIterate n) := by
  induction n with
  | zero => exact differentiable_id
  | succ n ih =>
      simpa [expIterate, Function.iterate_succ_apply] using
        ih.comp Complex.differentiable_exp

/-- Every iterate of the exponential is continuous. -/
theorem continuous_expIterate (n : ℕ) :
    Continuous (expIterate n) :=
  (differentiable_expIterate n).continuous

/-- Every iterate of the exponential is complex differentiable on every set. -/
theorem differentiableOn_expIterate (n : ℕ) (s : Set ℂ) :
    DifferentiableOn ℂ (expIterate n) s :=
  (differentiable_expIterate n).differentiableOn

end

end ExponentialJuliaSetMisiurewicz
