/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/

import LeanPool.HansonWright
import LeanPool.StatisticalLearningTheory.SubGaussian

/-!
# Hanson--Wright compatibility layer

This module exposes the small portion of the statistical-learning-theory
Hanson--Wright API used by the random-matrix development.  Its implementation
reuses the independently pooled Hanson--Wright formalization.
-/

namespace LeanPool.StatisticalLearningTheory.HansonWright

open MeasureTheory Real
open _root_.ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The quadratic form associated to a finite real matrix. -/
def quadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * x i * x j

/-- The random quadratic form associated to a coordinate family. -/
def randomQuadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => quadraticForm A fun i => X i ω

/-- A coordinate family regarded as a Euclidean random vector. -/
def randomVector {n : ℕ} (X : Fin n → Ω → ℝ) : Ω → EuclideanSpace ℝ (Fin n) :=
  fun ω => WithLp.toLp 2 fun i => X i ω

/-- The centered random quadratic form. -/
def centeredQuadraticForm {n : ℕ} (μ : Measure Ω) (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => randomQuadraticForm A X ω - ∫ ω, randomQuadraticForm A X ω ∂μ

/-- The squared Frobenius norm of a finite real matrix. -/
def frobeniusNormSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- The Frobenius norm of a finite real matrix. -/
def frobeniusNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sqrt (frobeniusNormSq A)

/-- The Euclidean operator norm of a finite real matrix. -/
def operatorNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

/-- The Frobenius norm is nonnegative. -/
lemma frobeniusNorm_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ frobeniusNorm A := by
  simpa only [frobeniusNorm, frobeniusNormSq,
    _root_.LeanPool.HansonWright.frobeniusNorm,
    _root_.LeanPool.HansonWright.frobeniusNormSq] using
    _root_.LeanPool.HansonWright.frobeniusNorm_nonneg A

/-- Squaring the Frobenius norm recovers its sum-of-squares definition. -/
lemma frobeniusNorm_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusNorm A ^ 2 = frobeniusNormSq A := by
  simpa only [frobeniusNorm, frobeniusNormSq,
    _root_.LeanPool.HansonWright.frobeniusNorm,
    _root_.LeanPool.HansonWright.frobeniusNormSq] using
    _root_.LeanPool.HansonWright.frobeniusNorm_sq A

/-- A second-moment estimate from a square-exponential estimate. -/
lemma integral_sq_le_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {C0 : ℝ}
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0) :
    ∫ ω, X ω ^ 2 ∂μ ≤ exp 1 * (C0 * exp 1) :=
  _root_.LeanPool.HansonWright.integral_sq_le_of_hasSubgaussianMGF_of_le h hC0 hc_le

/-- The Hanson--Wright tail bound for independent sub-Gaussian coordinates. -/
theorem hanson_wright_inequality {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C t : ℝ} (hK : 0 < K) (_hC : 0 < C)
    (_hC_domain : 4 * exp 1 ≤ C)
    (_hC_diag_quad : 8 * exp 1 ^ 3 ≤ C)
    (_hC_offdiag_domain : 16 * exp 1 ≤ C ^ 2)
    (hC_offdiag_quad : 64 * exp 1 ^ 2 ≤ C)
    (hF : 0 < frobeniusNorm A) (hOp : 0 < operatorNorm A)
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (ht : 0 ≤ t) :
    (μ {ω | t ≤ |centeredQuadraticForm μ A X ω|}).toReal ≤
      2 * exp (-(1 / (4 * C)) *
        min (t ^ 2 / (K ^ 4 * frobeniusNorm A ^ 2))
          (t / (K ^ 2 * operatorNorm A))) :=
  by
    have hcenter : centeredQuadraticForm μ A X =
        _root_.LeanPool.HansonWright.centeredQuadraticForm μ A X := by rfl
    have hfrobenius : frobeniusNorm A =
        _root_.LeanPool.HansonWright.frobeniusNorm A := by rfl
    have hoperator : operatorNorm A =
        _root_.LeanPool.HansonWright.operatorNorm A := by rfl
    simpa only [hcenter, hfrobenius, hoperator] using
      _root_.LeanPool.HansonWright.hanson_wright_inequality
        hK hC_offdiag_quad hF hOp h_indep hX_subG ht

end

end LeanPool.StatisticalLearningTheory.HansonWright
