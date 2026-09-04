/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic

/-!
# Exact calibration interfaces

This file contains the probability/calibration interfaces shared by the
Vlassis--Thomas theorem and the reduction to Feige's inequality.
-/

open MeasureTheory ProbabilityTheory

namespace Feige

/-- Abstract form of Theorem 2.1: `K` is super-uniform for every independent
family of nonnegative random variables whose coordinate means are at most
one. -/
def CalibrationProperty {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (K : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (Y : Fin n → Ω → ℝ),
    (∀ i, Measurable (Y i)) →
    (∀ i, Integrable (Y i) μ) →
    iIndepFun Y μ →
    (∀ i ω, 0 ≤ Y i ω) →
    (∀ i, (∫ ω, Y i ω ∂μ) ≤ 1) →
    ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      μ.real {ω | K (fun i ↦ Y i ω) ≤ α} ≤ α

/-- The calibration property, uniformly over all (small-universe)
probability spaces. -/
def UniversalCalibration {n : ℕ} (K : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ),
    CalibrationProperty μ K

end Feige
