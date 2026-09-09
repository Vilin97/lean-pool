/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanScalarMollification
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.NoncompactTransport
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! A fixed shrinking compact mollifier and distributional scalar harmonicity. -/

@[expose] public section


noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerNoncompactTransport
open scoped ContDiff Convolution Topology

/-- Harmonicity tested against genuine smooth compactly supported scalar functions. -/
def ScalarWeakHarmonicOn (U : Set Space) (f : Space → ℝ) : Prop :=
  ∀ φ : Space → ℝ, HasCompactSupport φ → ContDiff ℝ ∞ φ → tsupport φ ⊆ U →
    (∫ x, f x * Δ φ x) = 0

/-- Interior mollifier, bundling `rIn`, `rOut`, `rIn_pos`, `rIn_lt_rOut` and the required
compatibility proofs. -/
def interiorMollifier (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := (1/16 : ℝ) * cutoffScale n
  rOut := (1/8 : ℝ) * cutoffScale n
  rIn_pos := mul_pos (by norm_num) (cutoffScale_pos n)
  rIn_lt_rOut := by
    have hc := cutoffScale_pos n
    nlinarith

theorem interiorMollifier_rOut_le (n : ℕ) : (interiorMollifier n).rOut ≤ 1/4 := by
  change (1/8 : ℝ) * cutoffScale n ≤ 1/4
  have hc := cutoffScale_le_one n
  linarith

theorem interiorMollifier_rOut_tendsto :
    Filter.Tendsto (fun n => (interiorMollifier n).rOut) Filter.atTop (𝓝 (0 : ℝ)) := by
  simpa only [interiorMollifier, mul_zero] using cutoffScale_tendsto.const_mul (1/8 : ℝ)

theorem interiorMollifier_shape (n : ℕ) :
    (interiorMollifier n).rOut ≤ 2 * (interiorMollifier n).rIn := by
  change (1/8 : ℝ) * cutoffScale n ≤ 2 * ((1/16 : ℝ) * cutoffScale n)
  ring_nf
  exact le_rfl

/-- The classical smooth convolutions recover every scalar L² function almost everywhere. -/
theorem scalarMollification_ae_tendsto (f : Space → ℝ) (hf : MemLp f 2 volume) :
    ∀ᵐ x ∂volume, Filter.Tendsto (fun n => scalarMollification (interiorMollifier n) f x)
      Filter.atTop (𝓝 (f x)) :=
  ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    interiorMollifier_rOut_tendsto (Filter.Eventually.of_forall interiorMollifier_shape)
    (hf.locallyIntegrable (by norm_num))

/-- A uniform squared pointwise bound passes from these genuine mollifiers to f. -/
theorem ae_bound_of_scalarMollification_bound (f : Space → ℝ) (hf : MemLp f 2 volume)
    (U : Set Space) (C : ℝ)
    (hbound : ∀ n x, x ∈ U → scalarMollification (interiorMollifier n) f x ^ 2 ≤ C) :
    ∀ᵐ x ∂volume, x ∈ U → f x ^ 2 ≤ C := by
  filter_upwards [scalarMollification_ae_tendsto f hf] with x hx
  intro hxU
  exact le_of_tendsto (hx.pow 2) (Filter.Eventually.of_forall fun n => hbound n x hxU)

end EulerMeanHarmonic
