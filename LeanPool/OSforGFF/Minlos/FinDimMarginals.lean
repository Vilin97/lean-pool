/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.OSforGFF.Bochner.Main

/-!
# Finite-Dimensional Marginals for Minlos' Theorem

For a continuous positive-definite normalized functional Φ on a TVS E, we
construct finite-dimensional marginal measures via Bochner's theorem.

Given test vectors f₁,...,fₙ ∈ E, the marginal characteristic function
Φ_F(t) = Φ(∑ tᵢfᵢ) is continuous PD on ℝⁿ, so Bochner gives a probability
measure μ_F on ℝⁿ.

## Main results

- `marginalCF` — the finite-dimensional marginal CF
- `marginalCF_continuous` — marginalCF is continuous
- `marginalCF_pd` — marginalCF is positive definite
- `marginalCF_normalized` — marginalCF(0) = 1
- `marginal_measure_exists` — Bochner gives a probability measure with matching CF
-/

open BigOperators MeasureTheory Complex

noncomputable section

/-! ## Marginal characteristic function -/

/-- The finite-dimensional marginal CF: Φ_F(t) = Φ(∑ tᵢ • fᵢ).

    Defined on `EuclideanSpace ℝ (Fin n)` (which is `PiLp 2 (fun _ => ℝ)`)
    so that we can apply Bochner's theorem (which requires inner product spaces).
-/
def marginalCF {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Φ : E → ℂ) {n : ℕ} (f : Fin n → E) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun t => Φ (∑ i, (t i) • f i)

/-- The marginal CF is continuous.

    Proof: Each summand `tᵢ • fᵢ` is continuous in t (scalar multiplication
    by a continuous coordinate projection), and a finite sum of continuous
    functions is continuous. Then compose with continuous Φ.
-/
theorem marginalCF_continuous {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (Φ : E → ℂ) {n : ℕ} (f : Fin n → E)
    (hΦ : Continuous Φ) : Continuous (marginalCF Φ f) := by
  apply hΦ.comp
  apply continuous_finsetSum
  intro i _
  exact (EuclideanSpace.proj i).continuous.smul continuous_const

/-- Helper: the map t ↦ ∑ tᵢ • fᵢ is linear from EuclideanSpace ℝ (Fin n) to E. -/
private def spanLinearMap {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (f : Fin n → E) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E where
  toFun t := ∑ i, (t i) • f i
  map_add' s t := by
    simp only [PiLp.add_apply, add_smul, ← Finset.sum_add_distrib]
  map_smul' r t := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, RingHom.id_apply]

/-- The marginal CF is positive definite.

    Uses `isPositiveDefinite_precomp_linear`: if Φ is PD on E and T : V →ₗ E
    is linear, then Φ ∘ T is PD on V.
-/
theorem marginalCF_pd {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Φ : E → ℂ) {n : ℕ} (f : Fin n → E)
    (hPD : IsPositiveDefinite Φ) : IsPositiveDefinite (marginalCF Φ f) :=
  isPositiveDefinite_precomp_linear Φ hPD (spanLinearMap f)

/-- The marginal CF is normalized: Φ_F(0) = Φ(0) = 1. -/
theorem marginalCF_normalized {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Φ : E → ℂ) {n : ℕ} (f : Fin n → E)
    (h_norm : Φ 0 = 1) : marginalCF Φ f 0 = 1 := by
  simp [marginalCF, h_norm]

/-- For each finite set of test vectors, Bochner's theorem gives a probability
    measure on ℝⁿ whose characteristic function equals the marginal CF.

    This is the core step connecting the infinite-dimensional Minlos problem
    to the finite-dimensional Bochner theorem.
-/
theorem marginal_measure_exists {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (Φ : E → ℂ) {n : ℕ} (f : Fin n → E)
    (hΦ_cont : Continuous Φ) (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) :
    ∃! μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      ∀ ξ, charFun (μ : Measure (EuclideanSpace ℝ (Fin n))) ξ =
        marginalCF Φ f ξ :=
  bochner_theorem (marginalCF Φ f)
    (marginalCF_continuous Φ f hΦ_cont)
    (marginalCF_pd Φ f hΦ_pd)
    (marginalCF_normalized Φ f hΦ_norm)

end
