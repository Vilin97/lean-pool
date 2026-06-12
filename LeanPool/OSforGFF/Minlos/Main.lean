/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.OSforGFF.Minlos.MeasurableModification

/-!
# Minlos' Theorem

Minlos' theorem: on a nuclear locally convex space E, a continuous positive-definite
normalized functional Φ : E → ℂ is the characteristic functional of a unique
probability measure on the topological dual E' = WeakDual ℝ E.

## Proof strategy

1. **Finite-dim marginals** (proved in FinDimMarginals.lean): For each finite
   F = {f₁,...,fₙ} ⊂ E, Bochner gives μ_F on ℝⁿ with charFun = Φ(∑ tᵢfᵢ).
2. **Projective family** (proved in ProjectiveFamily.lean): Transport marginals
   to `∀ j : J, ℝ` indexed by `Finset E`, forming an `IsProjectiveMeasureFamily`.
3. **Kolmogorov extension** (imported from KolmogorovExtension4):
   `projectiveLimit` gives measure ν on E → ℝ.
4. **Measurable projection** (MeasurableModification.lean): Push forward ν
   through a measurable map P : (E → ℝ) → WeakDual ℝ E to get μ = ν.map P.
5. **CF verification**: P(ω)(f) = ω(f) ν-a.e., so charFun(μ) = Φ.
6. **Uniqueness**: P ∘ embed = id, so μ' = (μ'.map embed).map P = ν.map P = μ.

## References

- Minlos, "Generalized random processes and their extension to measures" (1959)
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, Thm 3
- Billingsley, "Convergence of Probability Measures", Thm 36.1
- Degenne-Pfaffelhuber, KolmogorovExtension4 (formalized Kolmogorov extension)
-/

open BigOperators MeasureTheory Complex TopologicalSpace

noncomputable section

private lemma trans_symm_apply_eq' {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (e₁ : α ≃ᵐ β) (e₂ : β ≃ᵐ γ) (z : γ) :
    (e₁.trans e₂).symm z = e₁.symm (e₂.symm z) := rfl

/-! ## Main Theorem -/

/-- **Minlos' Theorem** (existence and uniqueness): On a nuclear, separable,
    locally convex space E, a continuous, positive definite, normalized functional
    Φ : E → ℂ is the characteristic functional of a unique probability measure μ
    on the topological dual E':

    Φ(f) = ∫_{E'} exp(i ω(f)) dμ(ω)

    **Proof**: Combine finite-dimensional Bochner (→ marginal measures), Kolmogorov
    extension (→ measure ν on E → ℝ), measurable projection P (→ μ = ν.map P on
    WeakDual ℝ E), CF verification (P(ω)(f) = ω(f) a.e.), and uniqueness
    (P ∘ embed = id).

    **References**: Minlos (1959), Gel'fand-Vilenkin Vol. 4, Billingsley,
    Degenne-Pfaffelhuber (KolmogorovExtension4).
-/
theorem minlos_theorem {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E] (Φ : E → ℂ)
    (h_continuous : Continuous Φ) (h_positive_definite : IsPositiveDefinite Φ)
    (h_normalized : Φ 0 = 1) :
    ∃! μ : ProbabilityMeasure (WeakDual ℝ E),
      ∀ f : E, Φ f = ∫ ω, exp (I * (ω f)) ∂μ.toMeasure := by
  -- Step 1: Build the projective family and Kolmogorov extension
  -- This gives us ν : Measure (E → ℝ), a probability measure on the algebraic dual
  let ν := marginalProjectiveLimit Φ h_continuous h_positive_definite h_normalized
  have hν_prob : IsProbabilityMeasure ν :=
    marginalProjectiveLimitIsProbability Φ h_continuous h_positive_definite h_normalized
  -- Step 2: The CF of ν equals Φ (hence is continuous)
  have hν_proj := marginalProjectiveLimit_isProjectiveLimit Φ h_continuous
    h_positive_definite h_normalized
  -- For each f : E, ∫ ω, exp(I * ω f) ∂ν = Φ f, via the singleton marginal
  have h_cf_eq : ∀ f : E, ∫ ω : E → ℝ, Complex.exp (Complex.I * ↑(ω f)) ∂ν = Φ f := by
    intro f
    -- g is the integrand on the singleton Pi type
    let g : (∀ j : ↥({f} : Finset E), ℝ) → ℂ :=
      fun x => Complex.exp (Complex.I * ↑(x ⟨f, Finset.mem_singleton_self f⟩))
    have hg_cont : Continuous g :=
      Complex.continuous_exp.comp
        (continuous_const.mul (continuous_ofReal.comp (continuous_apply _)))
    -- Step 1: Factor integrand through {f}.restrict and change variables
    change ∫ ω, g (({f} : Finset E).restrict ω) ∂ν = Φ f
    rw [← integral_map (Finset.measurable_restrict ({f} : Finset E)).aemeasurable
      hg_cont.aestronglyMeasurable, hν_proj {f}]
    -- Step 2: Unfold marginalFamily and change variables through equiv
    simp only [marginalFamily]
    rw [integral_map (finsetPiMeasEquiv ({f} : Finset E)).symm.measurable.aemeasurable
      hg_cont.aestronglyMeasurable]
    -- Step 3: Simplify the composed integrand
    set idx := ({f} : Finset E).equivFin ⟨f, Finset.mem_singleton_self f⟩ with idx_def
    have h_simp : ∀ y : EuclideanSpace ℝ (Fin ({f} : Finset E).card),
        g ((finsetPiMeasEquiv ({f} : Finset E)).symm y) =
        Complex.exp (Complex.I * ↑(y idx)) := by
      intro y
      simp only [g, finsetPiMeasEquiv, trans_symm_apply_eq',
        MeasurableEquiv.coe_toLp_symm, finsetReindexEquiv,
        MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk]
      rfl
    simp_rw [h_simp, mul_comm Complex.I _]
    -- Step 4: Connect y idx to inner product ⟪y, single idx 1⟫
    have h_inner : ∀ y : EuclideanSpace ℝ (Fin ({f} : Finset E).card),
        (y idx : ℝ) = @inner ℝ _ _ y (EuclideanSpace.single idx 1) := by
      intro y
      change _ = @inner ℝ (EuclideanSpace ℝ _) _ y (EuclideanSpace.single idx 1)
      erw [EuclideanSpace.inner_single_right]; simp
    simp_rw [h_inner, ← charFun_apply, marginalMeasure_charFun]
    -- Step 5: Simplify marginalCF for singleton
    simp [marginalCF, finsetTestVectors, PiLp.single_apply, idx_def]
  -- Step 2b: Joint characteristic function (generalizes h_cf_eq to n-point marginals)
  -- For any finite collection of test vectors and scalars, the joint CF equals Φ
  -- applied to the linear combination. Proved from the projective limit property
  -- (same structure as h_cf_eq but for a general Finset instead of a singleton).
  -- Joint characteristic function: generalizes h_cf_eq to n-point marginals.
  -- Strategy: factor through J = Finset.image x univ, use projective limit,
  -- change variables through finsetPiMeasEquiv, fiber-sum reindex to charFun.
  -- Factor through J = Finset.image x univ, change vars through finsetPiMeasEquiv.
  have h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, Complex.exp (Complex.I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i) := by
    intro n s x
    classical
    set J := Finset.image x Finset.univ with J_def
    have hx_mem : ∀ i, x i ∈ J :=
      fun i => Finset.mem_image_of_mem x (Finset.mem_univ i)
    -- The integrand depends on ω only at points in J
    let g : (∀ j : ↥J, ℝ) → ℂ := fun y =>
      Complex.exp (Complex.I * ↑(∑ i, s i * y ⟨x i, hx_mem i⟩))
    have hg_cont : Continuous g :=
      Complex.continuous_exp.comp (continuous_const.mul (continuous_ofReal.comp
        (continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply _)))))
    -- Step 1: Factor through J.restrict and use projective limit
    change ∫ ω, g (J.restrict ω) ∂ν = Φ (∑ i, s i • x i)
    rw [← integral_map (Finset.measurable_restrict J).aemeasurable
      hg_cont.aestronglyMeasurable, hν_proj J, marginalFamily,
      integral_map (finsetPiMeasEquiv J).symm.measurable.aemeasurable
        hg_cont.aestronglyMeasurable]
    -- fi maps each Fin n index to the position of x i in J's enumeration
    set fi : Fin n → Fin J.card :=
      fun i => J.equivFin ⟨x i, hx_mem i⟩ with fi_def
    -- Step 2: Simplify g ∘ (finsetPiMeasEquiv J).symm
    have h_simp : ∀ y : EuclideanSpace ℝ (Fin J.card),
        g ((finsetPiMeasEquiv J).symm y) =
        Complex.exp (Complex.I * ↑(∑ i : Fin n, s i * y (fi i))) := by
      intro y; simp only [g, finsetPiMeasEquiv, trans_symm_apply_eq',
        MeasurableEquiv.coe_toLp_symm, finsetReindexEquiv,
        MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk, fi_def]; rfl
    simp_rw [h_simp, mul_comm Complex.I _]
    -- Step 3: Define ξ = ∑ i, s i • single (fi i) 1 and rewrite sum as inner product
    set ξ : EuclideanSpace ℝ (Fin J.card) :=
      ∑ i : Fin n, (s i) • EuclideanSpace.single (fi i) (1 : ℝ) with ξ_def
    have h_inner : ∀ y : EuclideanSpace ℝ (Fin J.card),
        (∑ i : Fin n, s i * y (fi i) : ℝ) = @inner ℝ _ _ y ξ := by
      intro y
      simp only [ξ_def, inner_sum, inner_smul_right]
      congr 1; ext i
      have : @inner ℝ (EuclideanSpace ℝ _) _ y (EuclideanSpace.single (fi i) 1) = y (fi i) := by
        erw [EuclideanSpace.inner_single_right]; simp
      rw [this]
    simp_rw [h_inner, ← charFun_apply, marginalMeasure_charFun]
    -- Step 4: Unfold marginalCF and show sum equality
    simp only [marginalCF]
    congr 1
    -- Goal: ∑ k, ξ k • finsetTestVectors J k = ∑ i, s i • x i
    have h_tv : ∀ i : Fin n, (J.equivFin.symm (fi i) : E) = x i := by
      intro i; simp [fi_def]
    -- Expand ξ and reduce to ∑ i, s i • x i
    -- Goal after marginalCF/congr: ∑ k, ξ k • testVec k = ∑ i, s i • x i
    -- Convert to a form where we can compute ξ k directly
    change ∑ k : Fin J.card, ξ k • finsetTestVectors J k = ∑ i, s i • x i
    -- Compute ξ k = ∑ i, s i * ite (fi i = k) 1 0
    have h_coord : ∀ k : Fin J.card,
        ξ k = ∑ i : Fin n, s i * if fi i = k then 1 else 0 := by
      intro k
      simp [ξ_def, smul_eq_mul, Pi.single_apply, eq_comm]
    simp_rw [h_coord, Finset.sum_smul]
    -- Goal: ∑ k, ∑ i, (s i * ite (fi i = k) 1 0) • testVec k = ∑ i, s i • x i
    rw [Finset.sum_comm]
    -- Goal: ∑ i, ∑ k, (s i * ite (fi i = k) 1 0) • testVec k = ∑ i, s i • x i
    apply Finset.sum_congr rfl; intro i _
    simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
      finsetTestVectors]
    simp [fi_def]
  -- Step 3: Push forward ν through measurable projection P to get μ on WeakDual ℝ E
  have h_prob_map : IsProbabilityMeasure (ν.map measurableProjection) :=
    isProbabilityMeasure_map_projection ν
  let μ : ProbabilityMeasure (WeakDual ℝ E) := ⟨ν.map measurableProjection, h_prob_map⟩
  -- Existence: μ has the right characteristic functional
  refine ⟨μ, ?_, ?_⟩
  · -- Show ∀ f, Φ f = ∫ ω, exp(I * ω f) ∂μ
    intro f
    exact (charFunctional_map_projection Φ ν h_cf_joint h_continuous f).symm
  · -- Uniqueness: μ' = μ via pushforward factoring through embed
    intro μ' hμ'
    have h_eq := uniqueness_via_projection Φ h_continuous h_positive_definite h_normalized
      ν rfl μ' hμ'
    exact h_eq

/-! ## Derived results -/

/-- Derived uniqueness: two probability measures with the same characteristic functional
    on a nuclear space must be equal.
-/
theorem minlos_uniqueness {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E]
    {Φ : E → ℂ} (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1)
    {μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ E)}
    (h₁ : ∀ f : E, ∫ ω, exp (I * (ω f)) ∂μ₁.toMeasure = Φ f)
    (h₂ : ∀ f : E, ∫ ω, exp (I * (ω f)) ∂μ₂.toMeasure = Φ f) :
    μ₁ = μ₂ := by
  obtain ⟨μ₀, _, huniq⟩ := minlos_theorem Φ hΦ_cont hΦ_pd hΦ_norm
  exact (huniq μ₁ (fun f => (h₁ f).symm)).trans (huniq μ₂ (fun f => (h₂ f).symm)).symm

end
