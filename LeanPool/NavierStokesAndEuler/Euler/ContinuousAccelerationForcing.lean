/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathComposition
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual continuous-time acceleration forcing

The expression `Q*(f-2 Q₁v)` is a genuine continuous path. Its smoothness and
factorial bound are proved in the uniform time norm and are shared by the
mean and transverse strong equations.
-/

@[expose] public section


noncomputable section


namespace EulerContinuousAccelerationForcing

open ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousPathCalculus
  EulerContinuousPathComposition EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

variable {K P U E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The literal continuous forcing in the projected acceleration equation. -/
def forcing (Q Q₁ : P → C(K, U →L[ℝ] E)) (f : P → C(K, E)) (v : P → C(K, U)) (x : P) : C(K,U) :=
  multiplier (adjointMap (Q x)) (f x - (2 : ℝ) • multiplier (Q₁ x) (v x))

/-- Actual uniform-time regularity of the acceleration forcing. -/
theorem forcing_contDiff (Q Q₁ : P → C(K, U →L[ℝ] E)) (f : P → C(K, E)) (v : P → C(K, U))
    {n : ℕ∞ω} (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁)
    (hf : ContDiff ℝ n f) (hv : ContDiff ℝ n v) : ContDiff ℝ n (forcing Q Q₁ f v) :=
  contDiff_apply (fun x => adjointMap (Q x)) _ (contDiff_adjoint Q hQ)
    (hf.sub ((contDiff_apply Q₁ v hQ₁ hv).const_smul (2 : ℝ)))

/-- One fixed amplitude controls the genuine derivatives at every order. -/
theorem forcing_bound (Q Q₁ : P → C(K, U →L[ℝ] E)) (f : P → C(K, E)) (v : P → C(K, U))
    (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁)
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (R C₀ C₁ F V : ℝ) (hR : 0 ≤ R) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hF : 0 ≤ F) (hV : 0 ≤ V) (d : ℕ)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant R 0 n)
    (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant R 0 n)
    (hbf : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ F * majorant R d n)
    (hbv : ∀ n x, ‖iteratedFDeriv ℝ n v x‖ ≤ V * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (forcing Q Q₁ f v) x‖ ≤ (3*C₀*(F+6*C₁*V))*majorant R d n := by
  let w := fun y => multiplier (Q₁ y) (v y)
  have hw : ContDiff ℝ ∞ w := contDiff_apply Q₁ v hQ₁ hv
  have hbw (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j w y‖ ≤ (3*C₁*V)*majorant R d j := by
    simpa only [Nat.zero_add] using apply_bound Q₁ v hQ₁ hv R C₁ V hR hC₁ hV 0 d hbQ₁ hbv j y
  have hb2w (j : ℕ) (y : P) :
      ‖iteratedFDeriv ℝ j (fun z => (2 : ℝ) • w z) y‖ ≤ (6*C₁*V)*majorant R d j := by
    rw [iteratedFDeriv_const_smul_apply' (hw.contDiffAt.of_le (by simp)), norm_smul]
    norm_num only [Real.norm_ofNat]
    nlinarith [hbw j y]
  let r := fun y => f y - (2 : ℝ) • w y
  have hr : ContDiff ℝ ∞ r := hf.sub (hw.const_smul (2 : ℝ))
  have hbr := sub_bound f (fun y => (2 : ℝ) • w y) hf (hw.const_smul (2 : ℝ))
    R F (6*C₁*V) d hbf hb2w
  have h := apply_bound (fun y => adjointMap (Q y)) r (contDiff_adjoint Q hQ) hr
    R C₀ (F+6*C₁*V) hR hC₀ (by positivity) 0 d
    (EulerContinuousPathComposition.adjoint_bound Q hQ R C₀ hR hC₀ 0 hbQ) hbr n x
  simp only [Nat.zero_add] at h
  convert h using 1
  rfl

end EulerContinuousAccelerationForcing
