/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.OverlapSufficiency

/-!
# Canonical finite exponential-tilt model

This file instantiates the quotient-sufficiency contract with a canonical
finite exponential family over a statistic on arbitrary full observations.
The model tilts a positive base law by `exp (θ * S ω)`.
-/

open scoped NNReal

namespace OrdvecFormalization

/-- A positive finite law has nonempty finite support. -/
theorem finiteLaw_univ_nonempty {Ω : Type} [Fintype Ω] (base : FiniteLaw Ω) :
    (Finset.univ : Finset Ω).Nonempty := by
  by_contra hne
  have hsum : Finset.univ.sum base.mass = 0 := by
    apply Finset.sum_eq_zero
    intro ω hω
    exact False.elim (hne ⟨ω, hω⟩)
  have hzero_one : (0 : ℝ≥0) = 1 := by
    simpa [hsum] using base.sum_one
  exact zero_ne_one hzero_one

/-- Unnormalized full-observation exponential-tilt weight. -/
noncomputable def finiteTiltWeight {Ω : Type} [Fintype Ω] {n : ℕ}
    (base : FiniteLaw Ω) (S : Ω → Support n) (θ : ℝ) (ω : Ω) : ℝ≥0 :=
  base.mass ω * nnexp (θ * (S ω).val)

/-- Full-observation tilt weights are strictly positive. -/
theorem finiteTiltWeight_pos {Ω : Type} [Fintype Ω] {n : ℕ}
    (base : FiniteLaw Ω) (S : Ω → Support n) (θ : ℝ) (ω : Ω) :
    0 < finiteTiltWeight base S θ ω := by
  exact mul_pos (base.pos ω) (nnexp_pos (θ * (S ω).val))

/-- Normalizing constant for a full-observation exponential tilt. -/
noncomputable def finiteTiltNormalizer {Ω : Type} [Fintype Ω] {n : ℕ}
    (base : FiniteLaw Ω) (S : Ω → Support n) (θ : ℝ) : ℝ≥0 :=
  Finset.univ.sum fun ω : Ω => finiteTiltWeight base S θ ω

@[simp]
theorem finiteTiltWeight_zero {Ω : Type} [Fintype Ω] {n : ℕ}
    (base : FiniteLaw Ω) (S : Ω → Support n) (ω : Ω) :
    finiteTiltWeight base S 0 ω = base.mass ω := by
  simp [finiteTiltWeight]

@[simp]
theorem finiteTiltNormalizer_zero {Ω : Type} [Fintype Ω] {n : ℕ}
    (base : FiniteLaw Ω) (S : Ω → Support n) :
    finiteTiltNormalizer base S 0 = 1 := by
  simp [finiteTiltNormalizer, base.sum_one]

/-- The full-observation tilt normalizer is strictly positive. -/
theorem finiteTiltNormalizer_pos {Ω : Type} [Fintype Ω] {n : ℕ}
    (base : FiniteLaw Ω) (S : Ω → Support n) (θ : ℝ) :
    0 < finiteTiltNormalizer base S θ := by
  unfold finiteTiltNormalizer
  refine Finset.sum_pos (fun ω _hω => finiteTiltWeight_pos base S θ ω)
    (finiteLaw_univ_nonempty base)

/-- The normalized finite exponential tilt over arbitrary full observations. -/
noncomputable def finiteExponentialTilt {Ω : Type} [Fintype Ω] {n : ℕ}
    (base : FiniteLaw Ω) (S : Ω → Support n) (θ : ℝ) : FiniteLaw Ω where
  mass ω := finiteTiltWeight base S θ ω / finiteTiltNormalizer base S θ
  pos ω := div_pos (finiteTiltWeight_pos base S θ ω) (finiteTiltNormalizer_pos base S θ)
  sum_one := by
    rw [← Finset.sum_div]
    change finiteTiltNormalizer base S θ / finiteTiltNormalizer base S θ = 1
    exact div_self (ne_of_gt (finiteTiltNormalizer_pos base S θ))

@[simp]
theorem finiteExponentialTilt_zero_mass {Ω : Type} [Fintype Ω] {n : ℕ}
    (base : FiniteLaw Ω) (S : Ω → Support n) (ω : Ω) :
    (finiteExponentialTilt base S 0).mass ω = base.mass ω := by
  simp [finiteExponentialTilt]

/-- Likelihood-ratio factor for two full-observation exponential tilts. -/
noncomputable def finiteExponentialTiltLikelihoodFactor {Ω : Type} [Fintype Ω]
    {n : ℕ} (base : FiniteLaw Ω) (S : Ω → Support n) (θ₀ θ₁ : ℝ)
    (x : Support n) : ℝ≥0 :=
  finiteTiltNormalizer base S θ₀ / finiteTiltNormalizer base S θ₁ *
    (nnexp (θ₁ * x.val) / nnexp (θ₀ * x.val))

/-- The likelihood ratio between two full-observation tilts depends only on `S`. -/
theorem finiteLikelihoodRatio_finiteExponentialTilt_eq_factor {Ω : Type} [Fintype Ω]
    {n : ℕ} (base : FiniteLaw Ω) (S : Ω → Support n) (θ₀ θ₁ : ℝ) (ω : Ω) :
    finiteLikelihoodRatio (finiteExponentialTilt base S θ₀)
        (finiteExponentialTilt base S θ₁) ω =
      finiteExponentialTiltLikelihoodFactor base S θ₀ θ₁ (S ω) := by
  have hb : base.mass ω ≠ 0 := ne_of_gt (base.pos ω)
  have hZ₀ : finiteTiltNormalizer base S θ₀ ≠ 0 :=
    ne_of_gt (finiteTiltNormalizer_pos base S θ₀)
  have hZ₁ : finiteTiltNormalizer base S θ₁ ≠ 0 :=
    ne_of_gt (finiteTiltNormalizer_pos base S θ₁)
  have he₀ : nnexp (θ₀ * (S ω).val) ≠ 0 := ne_of_gt (nnexp_pos (θ₀ * (S ω).val))
  calc
    finiteLikelihoodRatio (finiteExponentialTilt base S θ₀)
        (finiteExponentialTilt base S θ₁) ω =
        ((base.mass ω * nnexp (θ₁ * (S ω).val)) / finiteTiltNormalizer base S θ₁) /
          ((base.mass ω * nnexp (θ₀ * (S ω).val)) / finiteTiltNormalizer base S θ₀) := by
      simp [finiteLikelihoodRatio, finiteExponentialTilt, finiteTiltWeight]
    _ = (finiteTiltNormalizer base S θ₀ / finiteTiltNormalizer base S θ₁) *
          (nnexp (θ₁ * (S ω).val) / nnexp (θ₀ * (S ω).val)) := by
      field_simp [hb, hZ₀, hZ₁, he₀]
    _ = finiteExponentialTiltLikelihoodFactor base S θ₀ θ₁ (S ω) := by
      simp [finiteExponentialTiltLikelihoodFactor]

/-- Exponential ratios are monotone when the signal parameter increases. -/
theorem nnexp_ratio_monotone {n : ℕ} {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) :
    Monotone fun x : Support n => nnexp (θ₁ * x.val) / nnexp (θ₀ * x.val) := by
  intro x y hxy
  rw [div_le_div_iff₀ (nnexp_pos (θ₀ * x.val)) (nnexp_pos (θ₀ * y.val))]
  simpa using nnexp_factor_mlr hθ hxy

/-- The finite exponential-tilt likelihood factor is monotone in the statistic. -/
theorem finiteExponentialTiltLikelihoodFactor_monotone {Ω : Type} [Fintype Ω]
    {n : ℕ} (base : FiniteLaw Ω) (S : Ω → Support n)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) :
    Monotone (finiteExponentialTiltLikelihoodFactor base S θ₀ θ₁) := by
  intro x y hxy
  have hratio := nnexp_ratio_monotone hθ hxy
  simpa [finiteExponentialTiltLikelihoodFactor, mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_left hratio (finiteTiltNormalizer base S θ₀ / finiteTiltNormalizer base S θ₁)

/--
Canonical tilt instantiation of ordered-evidence factorization.

Tilting any positive finite base law by ordered evidence makes the likelihood
ratio a monotone function of that evidence.
-/
theorem finiteExponentialTilt_likelihoodRatioFactorsThroughOrderedEvidence
    {Ω Ωq : Type} [Fintype Ω] {n : ℕ}
    (base : FiniteLaw Ω) (Q : Ω → Ωq) (T : Ωq → Support n)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) :
    FiniteLikelihoodRatioFactorsThroughOrderedEvidence Q T
      (finiteExponentialTilt base (fun ω => T (Q ω)) θ₀)
      (finiteExponentialTilt base (fun ω => T (Q ω)) θ₁) := by
  refine ⟨finiteExponentialTiltLikelihoodFactor base (fun ω => T (Q ω)) θ₀ θ₁,
    finiteExponentialTiltLikelihoodFactor_monotone base (fun ω => T (Q ω)) hθ, ?_⟩
  intro ω
  exact finiteLikelihoodRatio_finiteExponentialTilt_eq_factor base (fun ω => T (Q ω)) θ₀ θ₁ ω

/-- Canonical tilt instantiation of overlap-evidence factorization. -/
theorem finiteExponentialTilt_likelihoodRatioFactorsThroughOverlapEvidence
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (base : FiniteLaw Ω) (Q : Ω → Ωq) (O : Ωq → p.support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) :
    FiniteLikelihoodRatioFactorsThroughOverlapEvidence p Q O
      (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
      (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁) :=
  finiteExponentialTilt_likelihoodRatioFactorsThroughOrderedEvidence base Q O hθ

/--
Canonical model theorem: under a finite exponential tilt by ordinal overlap
evidence, an actual-overlap threshold is Bayes-optimal among all
deterministic full-space rules.
-/
theorem exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_finiteExponentialTilt
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (base : FiniteLaw Ω) (Q : Ω → Ωq) (O : Ωq → p.support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (w0 w1 : ℝ≥0) (hw1 : 0 < w1) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteWeightedRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          w0 w1 (overlapQuotientThresholdSet p Q O cut) ≤
        finiteWeightedRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          w0 w1 R :=
  exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_likelihoodRatioFactor p Q O
    (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
    (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
    w0 w1 hw1
    (finiteExponentialTilt_likelihoodRatioFactorsThroughOverlapEvidence p base Q O hθ)

/-- Convenience wrapper for the canonical finite overlap-tilt model. -/
theorem exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_canonicalTilt
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (base : FiniteLaw Ω) (Q : Ω → Ωq) (O : Ωq → p.support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (w0 w1 : ℝ≥0) (hw1 : 0 < w1) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteWeightedRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          w0 w1 (overlapQuotientThresholdSet p Q O cut) ≤
        finiteWeightedRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          w0 w1 R :=
  exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_finiteExponentialTilt
    p base Q O hθ w0 w1 hw1

end OrdvecFormalization
