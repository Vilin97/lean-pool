/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.OSforGFF.Minlos.FinDimMarginals
import LeanPool.OSforGFF.KolmogorovExtension4.KolmogorovExtension

/-!
# Bridge: Bochner Marginals → Projective Measure Family

Bridges the finite-dimensional Bochner marginals (measures on `EuclideanSpace ℝ (Fin n)`)
to the `IsProjectiveMeasureFamily` API from Mathlib (measures on `∀ j : J, ℝ` indexed
by `Finset E`), enabling application of the Kolmogorov extension theorem.

## Main definitions

- `marginalFamily` — for each `J : Finset E`, a probability measure on `∀ j : J, ℝ`
- `marginalFamily_isProjective` — the family is projective (consistent under restriction)
-/

open BigOperators MeasureTheory Complex

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-! ## Transport equivalence -/

/-- Measurable equivalence between `∀ j : J, ℝ` and `Fin |J| → ℝ` via `J.equivFin`. -/
def finsetReindexEquiv (J : Finset E) :
    (↥J → ℝ) ≃ᵐ (Fin J.card → ℝ) where
  toEquiv :=
    { toFun := fun x i => x (J.equivFin.symm i)
      invFun := fun t j => t (J.equivFin j)
      left_inv := fun x => by ext j; simp
      right_inv := fun t => by ext i; simp }
  measurable_toFun := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  measurable_invFun := measurable_pi_lambda _ (fun j => measurable_pi_apply _)

/-- Measurable equivalence between `∀ j : J, ℝ` and `EuclideanSpace ℝ (Fin |J|)`.
    Composition of reindexing by `J.equivFin` and `MeasurableEquiv.toLp`.
-/
def finsetPiMeasEquiv (J : Finset E) :
    (↥J → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin J.card) :=
  (finsetReindexEquiv J).trans (MeasurableEquiv.toLp 2 (Fin J.card → ℝ))

/-! ## Marginal family -/

/-- The test vectors for a finset `J`, as a function `Fin |J| → E`. -/
def finsetTestVectors (J : Finset E) : Fin J.card → E :=
  fun i => (J.equivFin.symm i : E)

/-- Choose the unique Bochner marginal measure for test vectors from a finset. -/
def marginalMeasure (Φ : E → ℂ) (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) (J : Finset E) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin J.card)) :=
  (marginal_measure_exists Φ (finsetTestVectors J) hΦ_cont hΦ_pd hΦ_norm).choose

theorem marginalMeasure_charFun (Φ : E → ℂ) (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) (J : Finset E) :
    ∀ ξ, charFun (marginalMeasure Φ hΦ_cont hΦ_pd hΦ_norm J : Measure _) ξ =
      marginalCF Φ (finsetTestVectors J) ξ :=
  (marginal_measure_exists Φ (finsetTestVectors J) hΦ_cont hΦ_pd hΦ_norm).choose_spec.1

/-- The projective family of measures indexed by `Finset E`. For each `J`, we take the
    Bochner marginal on `EuclideanSpace ℝ (Fin |J|)` and transport it to `∀ j : J, ℝ`
    via the `finsetPiMeasEquiv`.
-/
def marginalFamily (Φ : E → ℂ) (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) :
    ∀ J : Finset E, Measure (∀ j : ↥J, (fun (_ : E) => ℝ) ↑j) :=
  fun J => (marginalMeasure Φ hΦ_cont hΦ_pd hΦ_norm J).toMeasure.map
    (finsetPiMeasEquiv J).symm

instance marginalFamilyIsFiniteMeasure (Φ : E → ℂ) (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) (J : Finset E) :
    IsFiniteMeasure (marginalFamily Φ hΦ_cont hΦ_pd hΦ_norm J) :=
  Measure.isFiniteMeasure_map _ _

instance marginalFamilyIsProbabilityMeasure (Φ : E → ℂ) (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) (J : Finset E) :
    IsProbabilityMeasure (marginalFamily Φ hΦ_cont hΦ_pd hΦ_norm J) :=
  Measure.isProbabilityMeasure_map (finsetPiMeasEquiv J).symm.measurable.aemeasurable

/-! ## Projectivity

The marginal family is projective. The proof uses characteristic function uniqueness:
for `J ⊆ I`, the pushforward of `P(I)` along `Finset.restrict₂` has the same
characteristic function as `P(J)`, namely `ξ ↦ Φ(∑_{j∈J} ξⱼ fⱼ)`.
-/

/-- The injection from `Fin J.card` to `Fin I.card` induced by `J ⊆ I`. -/
private def finsetIndexInj (I J : Finset E) (hJI : J ⊆ I) (k : Fin J.card) : Fin I.card :=
  I.equivFin ⟨(J.equivFin.symm k : E), hJI (J.equivFin.symm k).prop⟩

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] in
private lemma finsetIndexInj_injective (I J : Finset E) (hJI : J ⊆ I) :
    Function.Injective (finsetIndexInj I J hJI) := by
  intro k₁ k₂ h
  simp only [finsetIndexInj, Equiv.apply_eq_iff_eq, Subtype.mk.injEq] at h
  exact J.equivFin.symm.injective (Subtype.ext h)

/-- The coordinate projection from `EuclideanSpace` indexed by `I` to `J`, for `J ⊆ I`.
    Must wrap/unwrap `WithLp` since `EuclideanSpace = PiLp 2`.
-/
private def euclideanProject (I J : Finset E) (hJI : J ⊆ I) :
    EuclideanSpace ℝ (Fin I.card) → EuclideanSpace ℝ (Fin J.card) :=
  fun x => (WithLp.equiv 2 _).symm
    (fun k => (WithLp.equiv 2 _ x) (finsetIndexInj I J hJI k))

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] in
private lemma euclideanProject_measurable (I J : Finset E) (hJI : J ⊆ I) :
    Measurable (euclideanProject I J hJI) := by
  apply (MeasurableEquiv.toLp 2 (Fin J.card → ℝ)).measurable.comp
  exact measurable_pi_lambda _ fun k =>
    (measurable_pi_apply (finsetIndexInj I J hJI k)).comp
      (MeasurableEquiv.toLp 2 (Fin I.card → ℝ)).symm.measurable

private lemma trans_symm_apply_eq {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (e₁ : α ≃ᵐ β) (e₂ : β ≃ᵐ γ) (z : γ) :
    (e₁.trans e₂).symm z = e₁.symm (e₂.symm z) := rfl

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] in
/-- `e_J.symm ∘ euclideanProject = restrict₂ ∘ e_I.symm` — relates the EuclideanSpace
    projection to the Pi-type restriction map.
-/
private lemma euclideanProject_restrict₂ (I J : Finset E) (hJI : J ⊆ I) :
    ⇑(finsetPiMeasEquiv J).symm ∘ euclideanProject I J hJI =
    (Finset.restrict₂ (π := fun (_ : E) => ℝ) hJI) ∘ ⇑(finsetPiMeasEquiv I).symm := by
  ext x (k : ↥J)
  simp only [Function.comp_apply, Finset.restrict₂,
    finsetPiMeasEquiv, trans_symm_apply_eq, MeasurableEquiv.coe_toLp_symm]
  simp only [finsetReindexEquiv, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk]
  simp only [euclideanProject, finsetIndexInj, WithLp.equiv]
  simp

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] in
/-- Test vectors are compatible with the index injection: `testVec I (σ k) = testVec J k`. -/
private lemma finsetTestVectors_comp_inj (I J : Finset E) (hJI : J ⊆ I) (k : Fin J.card) :
    finsetTestVectors I (finsetIndexInj I J hJI k) = finsetTestVectors J k := by
  simp [finsetTestVectors, finsetIndexInj]

/-- The marginal family is projective: for `J ⊆ I`, the restriction of `P(I)` to
    `J`-coordinates equals `P(J)`.
-/
theorem marginalFamily_isProjective (Φ : E → ℂ) (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) :
    IsProjectiveMeasureFamily (α := fun (_ : E) => ℝ)
      (marginalFamily Φ hΦ_cont hΦ_pd hΦ_norm) := by
  intro I J hJI
  classical
  -- Unfold marginalFamily and compose maps on RHS
  simp only [marginalFamily]
  conv_rhs => erw [Measure.map_map (Finset.measurable_restrict₂ hJI)
    (finsetPiMeasEquiv I).symm.measurable]
  -- Suffices: on EuclideanSpace, μ_J = μ_I.map (euclideanProject)
  suffices key : (marginalMeasure Φ hΦ_cont hΦ_pd hΦ_norm J : Measure _) =
      (marginalMeasure Φ hΦ_cont hΦ_pd hΦ_norm I : Measure _).map
        (euclideanProject I J hJI) by
    -- Derive Pi-type goal from EuclideanSpace result
    conv_lhs => rw [key]
    rw [Measure.map_map (finsetPiMeasEquiv J).symm.measurable
      (euclideanProject_measurable I J hJI)]
    congr 1
    exact euclideanProject_restrict₂ I J hJI
  -- On EuclideanSpace, use charFun uniqueness
  apply Measure.ext_of_charFun
  ext ξ
  -- Define the zero-extension of ξ from J-indices to I-indices
  set xi : EuclideanSpace ℝ (Fin I.card) := (WithLp.equiv 2 _).symm (fun i =>
    if h : (I.equivFin.symm i : E) ∈ J
    then ξ.ofLp (J.equivFin ⟨(I.equivFin.symm i : E), h⟩)
    else 0) with xi_def
  -- Key: xi vanishes outside J-indices
  have xi_ofLp : ∀ i, xi.ofLp i =
      if h : (I.equivFin.symm i : E) ∈ J
      then ξ.ofLp (J.equivFin ⟨(I.equivFin.symm i : E), h⟩)
      else 0 := by
    intro i; simp [xi_def]
  have xi_zero : ∀ i, (I.equivFin.symm i : E) ∉ J → xi.ofLp i = 0 := by
    intro i hi; rw [xi_ofLp]; simp [hi]
  -- Key: xi at σ(k) equals ξ at k
  have xi_val : ∀ k : Fin J.card,
      xi.ofLp (finsetIndexInj I J hJI k) = ξ.ofLp k := by
    intro k
    rw [xi_ofLp]
    have hJ : (I.equivFin.symm (finsetIndexInj I J hJI k) : E) ∈ J := by
      simp [finsetIndexInj]
    simp only [finsetIndexInj]
    simp
  -- Inner product identity: ⟪euclideanProject y, ξ⟫ = ⟪y, xi⟫
  have h_inner : ∀ y : EuclideanSpace ℝ (Fin I.card),
      @inner ℝ _ _ (euclideanProject I J hJI y) ξ = @inner ℝ _ _ y xi := by
    intro y
    simp only [PiLp.inner_apply]
    -- LHS: ∑ k, (euclideanProject y).ofLp k * ξ.ofLp k
    -- RHS: ∑ i, y.ofLp i * xi.ofLp i
    -- RHS has zero terms outside image of σ
    symm
    rw [← Finset.sum_subset (Finset.subset_univ
        (Finset.image (finsetIndexInj I J hJI) Finset.univ))]
    · rw [Finset.sum_image (fun k₁ _ k₂ _ h =>
        finsetIndexInj_injective I J hJI h)]
      congr 1; ext k
      rw [xi_val]
      -- (euclideanProject y).ofLp k = y.ofLp (σ k)
      simp [euclideanProject, finsetIndexInj]
    · intro i _ hi
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hi
      have : (I.equivFin.symm i : E) ∉ J := by
        intro hJ; exact hi (J.equivFin ⟨_, hJ⟩) (by simp [finsetIndexInj])
      simp [xi_zero i this]
  -- Rewrite charFun of pushforward using inner product identity
  -- Goal: charFun μ_J ξ = charFun (μ_I.map euclideanProject) ξ
  rw [marginalMeasure_charFun]
  -- Goal: marginalCF Φ (testVec J) ξ = charFun (μ_I.map euclideanProject) ξ
  -- Unfold charFun on RHS only
  conv_rhs => rw [charFun_apply]
  rw [integral_map (euclideanProject_measurable I J hJI).aemeasurable
      (by fun_prop : AEStronglyMeasurable _ _)]
  simp_rw [h_inner, ← charFun_apply, marginalMeasure_charFun]
  -- Now: marginalCF Φ (testVec J) ξ = marginalCF Φ (testVec I) xi
  simp only [marginalCF]
  congr 1
  -- Sum identity: ∑ k, ξ.ofLp k • testVec J k = ∑ i, xi.ofLp i • testVec I i
  symm
  -- Drop zero terms outside image of σ, then reindex
  rw [← Finset.sum_subset (Finset.subset_univ
      (Finset.image (finsetIndexInj I J hJI) Finset.univ))]
  · rw [Finset.sum_image (fun k₁ _ k₂ _ h =>
      finsetIndexInj_injective I J hJI h)]
    congr 1; ext k
    rw [xi_val, finsetTestVectors_comp_inj]
  · intro i _ hi
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hi
    have : (I.equivFin.symm i : E) ∉ J := by
      intro hJ; exact hi (J.equivFin ⟨_, hJ⟩) (by simp [finsetIndexInj])
    simp [xi_zero i this]

/-! ## Application of Kolmogorov Extension -/

/-- The Kolmogorov projective limit of the marginal family. -/
def marginalProjectiveLimit (Φ : E → ℂ) (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) [hE : Nonempty E] :
    Measure (E → ℝ) :=
  let _ := hE
  projectiveLimit (α := fun (_ : E) => ℝ)
    (marginalFamily Φ hΦ_cont hΦ_pd hΦ_norm)
    (marginalFamily_isProjective Φ hΦ_cont hΦ_pd hΦ_norm)

instance marginalProjectiveLimitIsProbability (Φ : E → ℂ) (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) [Nonempty E] :
    IsProbabilityMeasure (marginalProjectiveLimit Φ hΦ_cont hΦ_pd hΦ_norm) := by
  unfold marginalProjectiveLimit
  exact isProbabilityMeasureProjectiveLimit
    (marginalFamily_isProjective Φ hΦ_cont hΦ_pd hΦ_norm)

/-- The projective limit projects correctly onto each finite-dimensional marginal. -/
theorem marginalProjectiveLimit_isProjectiveLimit (Φ : E → ℂ) (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) [Nonempty E] :
    IsProjectiveLimit (marginalProjectiveLimit Φ hΦ_cont hΦ_pd hΦ_norm)
      (marginalFamily Φ hΦ_cont hΦ_pd hΦ_norm) :=
  isProjectiveLimit_projectiveLimit
    (marginalFamily_isProjective Φ hΦ_cont hΦ_pd hΦ_norm)

/-- The projective limit of the marginal family is unique. -/
theorem marginalProjectiveLimit_unique (Φ : E → ℂ) (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) [Nonempty E]
    {ν : Measure (E → ℝ)}
    (hν : IsProjectiveLimit ν (marginalFamily Φ hΦ_cont hΦ_pd hΦ_norm)) :
    ν = marginalProjectiveLimit Φ hΦ_cont hΦ_pd hΦ_norm :=
  hν.unique (marginalProjectiveLimit_isProjectiveLimit Φ hΦ_cont hΦ_pd hΦ_norm)

end
