/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/
module


/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import LeanPool.NashEmbedding.NashEmbedding.Torus.Basic
public import LeanPool.NashEmbedding.NashEmbedding.Torus.RealizableMetrics

/-!
# NashEmbedding tests: ContDiff encoding patch (smooth vs analytic)

Diagnostic tests for the `SmoothPeriodic.smooth` field encoding.

Background. In Mathlib v4.28's `WithTop ℕ∞` encoding a bare `⊤` means
analytic (`ω`), not C^∞ (`∞`). `SmoothPeriodic.smooth` was once typed
`ContDiff ℝ ⊤ f` by mistake and is now `ContDiff ℝ ∞ f`; these tests
guard against the encoding regressing.

Test X is the discriminating test:
 - With `smooth = ContDiff ℝ ⊤` (analytic), X fails to elaborate because
   the witness `expNegInvGlue ∘ sin` is not analytic.
 - With `smooth = ContDiff ℝ ∞` (C^∞, the current state), X elaborates.

Tests A1, W, Y, Z elaborate in either state — they exercise concrete
witnesses (zero, `flatTorusEmb`, `flatMetric`) all of which happen to
be analytic.
-/

@[expose] public section

open scoped ContDiff
open NashEmbedding NashEmbedding.Sobolev

noncomputable
section

namespace TorusNashTests

/-! ## Mathlib-level sanity -/

/-- **Test A1.** `expNegInvGlue` is in `ContDiff ℝ ∞`. Sanity check that
    the scoped notation `∞` (= the inner top, C^∞) is well-defined and
    `expNegInvGlue.contDiff` provides a witness. -/
example : ContDiff ℝ ∞ expNegInvGlue := expNegInvGlue.contDiff

/-! ## SmoothPeriodic baseline tests -/

/-- **Test W** (analytic baseline). `SmoothPeriodic` is inhabited by the
    constant-zero function. Elaborates pre- and post-patch. -/
example {n : ℕ} : SmoothPeriodic (fun _ : Fin n → ℝ => (0 : ℝ)) where
  smooth := contDiff_const
  periodic := fun _ _ => rfl

/-- **Test X** (regression test — distinguishes pre- vs post-patch).
    `SmoothPeriodic` of `f(x) = expNegInvGlue (sin x_0)`.
     - Smooth: composition of `expNegInvGlue` (C^∞, not analytic),
       `Real.sin` (analytic ⟹ C^∞), and coordinate projection.
     - 2πℤⁿ-periodic: `sin` has period 2π in `x_0`.
     - **NOT analytic**: `f` vanishes on the open set
       `{x : sin x_0 < 0}` without being identically zero.

    Pre-patch, the `smooth` field is `ContDiff ℝ ⊤ f = ContDiff ℝ ω f`
    (analytic); our proof produces `ContDiff ℝ ∞ f` and fails to
    elaborate. Post-patch, the field is `ContDiff ℝ ∞ f` and the test
    passes. -/
example {n : ℕ} (hn : 0 < n) :
    SmoothPeriodic
      (fun x : Fin n → ℝ => expNegInvGlue (Real.sin (x ⟨0, hn⟩))) where
  smooth :=
    expNegInvGlue.contDiff.comp
      (Real.contDiff_sin.comp (contDiff_apply ℝ ℝ (⟨0, hn⟩ : Fin n)))
  periodic := fun x k => by
    change expNegInvGlue (Real.sin ((x + periodicShift n k) ⟨0, hn⟩)) =
         expNegInvGlue (Real.sin (x ⟨0, hn⟩))
    congr 1
    have h : (x + periodicShift n k) ⟨0, hn⟩
        = x ⟨0, hn⟩ + (k ⟨0, hn⟩ : ℝ) * (2 * Real.pi) := by
      simp [periodicShift, Pi.add_apply]
      ring
    rw [h, Real.sin_add_int_mul_two_pi]

/-! ## Concrete-witness tests (analytic, work either state) -/

/-- **Test Y.** `flatTorusEmb n` is `SmoothPeriodic`. Cites
    `flatTorusEmb_smoothPeriodic` from `RealizableMetrics.lean`. -/
example {n : ℕ} : SmoothPeriodic (flatTorusEmb n) :=
  flatTorusEmb_smoothPeriodic

/-- **Test Z.** `flatMetric n` is `IsPosDefSmoothMetric`. Cites
    `flatMetric_isPosDefSmoothMetric` from `RealizableMetrics.lean`. -/
example {n : ℕ} : IsPosDefSmoothMetric (flatMetric n) :=
  flatMetric_isPosDefSmoothMetric

end TorusNashTests

end
