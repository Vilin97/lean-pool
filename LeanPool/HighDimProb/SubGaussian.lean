/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Orlicz
import LeanPool.HighDimProb.Tail

/-!
# SubGaussian predicate forms

This file names the standard real-valued subGaussian formulations separately.
It does not choose a canonical `SubGaussian` predicate and does not prove
equivalence between formulations.

Verified Wikipedia references:
* Sub-Gaussian distribution: https://en.wikipedia.org/wiki/Sub-Gaussian_distribution
* Orlicz space: https://en.wikipedia.org/wiki/Orlicz_space
-/

namespace HighDimProb

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

/--
Two-sided subGaussian tail bound with scale `K`.

Formula reference: sub-Gaussian tails have the form
`P(|X| >= t) <= 2 * exp(-c*t^2)`; see
https://en.wikipedia.org/wiki/Sub-Gaussian_distribution
-/
def SubGaussianTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ t : ℝ, 0 ≤ t →
      absTailProb P X t ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / K ^ 2)))

/--
SubGaussian moment-growth formulation with Mathlib's `ENNReal` exponent type.

Formula reference: moment growth is one standard equivalent formulation of
sub-Gaussian behavior; see
https://en.wikipedia.org/wiki/Sub-Gaussian_distribution

The condition is stated only for finite `p` with `1 ≤ p`; it is a predicate
interface, not a theorem relating moments to tails or Orlicz bounds.
-/
def SubGaussianMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ p : ENNReal, 1 ≤ p → p ≠ ∞ →
      realLpNorm P X p ≤ ENNReal.ofReal (K * Real.sqrt (ENNReal.toReal p))

/--
Centered MGF-style subGaussian formulation with scale `K`.

Formula reference: variance-proxy sub-Gaussian control uses
`E[exp(lambda*(X-E[X]))] <= exp(s^2*lambda^2/2)`; see
https://en.wikipedia.org/wiki/Sub-Gaussian_distribution

This wraps Mathlib's `ProbabilityTheory.HasSubgaussianMGF`, which includes the
required exponential integrability assumptions. Centering is not proved here.
-/
def CenteredSubGaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  0 < K ∧ ProbabilityTheory.HasSubgaussianMGF X (⟨K ^ 2, sq_nonneg K⟩ : ℝ≥0) P

/--
Orlicz `psi_2` formulation, as a thin wrapper around `Psi2Bound`.

Formula reference: `psi_2` Orlicz control is an Orlicz-space formulation of
sub-Gaussian size; see https://en.wikipedia.org/wiki/Orlicz_space
-/
abbrev SubGaussianOrlicz {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  Psi2Bound P X K

/-- Finite Orlicz `ψ₂` formulation, as a thin wrapper around `HasFinitePsi2`. -/
abbrev HasSubGaussianOrlicz {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : Prop :=
  HasFinitePsi2 P X

@[simp]
theorem subGaussianOrlicz_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) :
    SubGaussianOrlicz P X K ↔ Psi2Bound P X K :=
  Iff.rfl

theorem hasSubGaussianOrlicz_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) :
    HasSubGaussianOrlicz P X ↔ HasFinitePsi2 P X :=
  Iff.rfl

end

end HighDimProb
