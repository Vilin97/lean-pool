/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomVector
import LeanPool.HighDimProb.SubGaussian

/-!
# High-dimensional subGaussian random-vector predicate forms

This file defines vector-level subGaussian vocabulary through one-dimensional
linear marginals. It does not choose a canonical `SubGaussianVector` predicate
and does not prove equivalence between the directional formulations.

Verified Wikipedia references:
* Sub-Gaussian distribution: https://en.wikipedia.org/wiki/Sub-Gaussian_distribution
* Multivariate random variable: https://en.wikipedia.org/wiki/Multivariate_random_variable
-/

namespace HighDimProb

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/--
Concrete Euclidean length of a deterministic coefficient vector.

Formula reference: `||a||_2 = sqrt(sum_i a_i^2)` is the Euclidean norm; see
https://en.wikipedia.org/wiki/Euclidean_distance
-/
def directionNorm {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (a i) ^ 2)

/--
Directional scale `K * ||a||_2` for vector subGaussian predicates.

Formula reference: sub-Gaussian vector predicates are tested through linear
marginals scaled by the direction norm; see
https://en.wikipedia.org/wiki/Sub-Gaussian_distribution
-/
def directionScale {n : ℕ} (K : ℝ) (a : Fin n → ℝ) : ℝ :=
  K * directionNorm a

/--
Directional Orlicz/`ψ₂` subGaussian vector formulation.

Formula reference: tests `psi_2`/sub-Gaussian control on every nonzero linear
marginal; see https://en.wikipedia.org/wiki/Sub-Gaussian_distribution

The zero direction is excluded because the scalar `SubGaussianOrlicz` predicate
expects a positive scale.
-/
def SubGaussianVectorOrlicz {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ a : Fin n → ℝ, a ≠ 0 →
      SubGaussianOrlicz P (marginal X a) (directionScale K a)

/-- Finite directional Orlicz/`ψ₂` vector subGaussianity. -/
def HasSubGaussianVectorOrlicz {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) : Prop :=
  ∃ K : ℝ, SubGaussianVectorOrlicz P X K

/--
Directional tail-form subGaussian vector predicate.

Formula reference: tail control is required for every nonzero linear marginal;
see https://en.wikipedia.org/wiki/Sub-Gaussian_distribution
-/
def SubGaussianVectorTail {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ a : Fin n → ℝ, a ≠ 0 →
      SubGaussianTail P (marginal X a) (directionScale K a)

/--
Directional moment-growth subGaussian vector predicate.

Formula reference: moment-growth control is another sub-Gaussian formulation;
see https://en.wikipedia.org/wiki/Sub-Gaussian_distribution
-/
def SubGaussianVectorMoment {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ a : Fin n → ℝ, a ≠ 0 →
      SubGaussianMoment P (marginal X a) (directionScale K a)

/--
Directional centered-MGF subGaussian vector predicate.

Formula reference: MGF control is checked on every nonzero linear marginal;
see https://en.wikipedia.org/wiki/Sub-Gaussian_distribution
-/
def CenteredSubGaussianVectorMGF {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ a : Fin n → ℝ, a ≠ 0 →
      CenteredSubGaussianMGF P (marginal X a) (directionScale K a)

theorem subGaussianVectorOrlicz_iff {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (K : ℝ) :
    SubGaussianVectorOrlicz P X K ↔
      0 < K ∧
        ∀ a : Fin n → ℝ, a ≠ 0 →
          SubGaussianOrlicz P (marginal X a) (directionScale K a) :=
  Iff.rfl

theorem hasSubGaussianVectorOrlicz_iff {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) :
    HasSubGaussianVectorOrlicz P X ↔
      ∃ K : ℝ, SubGaussianVectorOrlicz P X K :=
  Iff.rfl

theorem subGaussianVectorTail_iff {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (K : ℝ) :
    SubGaussianVectorTail P X K ↔
      0 < K ∧
        ∀ a : Fin n → ℝ, a ≠ 0 →
          SubGaussianTail P (marginal X a) (directionScale K a) :=
  Iff.rfl

theorem subGaussianVectorMoment_iff {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (K : ℝ) :
    SubGaussianVectorMoment P X K ↔
      0 < K ∧
        ∀ a : Fin n → ℝ, a ≠ 0 →
          SubGaussianMoment P (marginal X a) (directionScale K a) :=
  Iff.rfl

theorem centeredSubGaussianVectorMGF_iff {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : RandomVector Ω n) (K : ℝ) :
    CenteredSubGaussianVectorMGF P X K ↔
      0 < K ∧
        ∀ a : Fin n → ℝ, a ≠ 0 →
          CenteredSubGaussianMGF P (marginal X a) (directionScale K a) :=
  Iff.rfl

end

end HighDimProb
