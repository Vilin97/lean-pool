/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
import LeanPool.DavisKahan.Palomar.DKSectionTwo.SolutionPrelude
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SectionTwo

/-!
# Davis--Kahan 1970: Palomar solution bridge

The public vocabulary used by Comparator is elaborated in
`Palomar.DKSectionTwo.SolutionPrelude`, which imports Mathlib alone and is an
exact copy of the Challenge's definition prefix.  Keeping that vocabulary out
of the larger Davis--Kahan import environment makes its exported constants
identical to the Challenge constants.  This module then adds only the bridge to
the compiled formalization and the five proofs.
-/

namespace RotationOfEigenvectors

open scoped InnerProductSpace NNReal ENNReal

universe u v w

-- The Challenge has this named local instance active while its theorem
-- statements are elaborated. Reactivate the same imported constant here rather
-- than generating a Solution-specific instance.
attribute [local instance] instCompleteSpaceOfHasOrthogonalProjection

/-! ## 7. Bridge to the compiled Davis--Kahan development

The Challenge intentionally uses Mathlib-only vocabulary.  The Solution keeps
that public vocabulary unchanged and translates it once into the production
Section 2 API.  In particular, the tangent proofs use the scalar-generic
`RCLike` endpoints directly; there is no local real/complex proof split.
-/

open TauCeti
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Sylvester
open TauCeti.ApproximationNumber
open scoped InnerProductSpace TauCeti.CompleteSubspace

section NormBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's singular values are the development's approximation numbers. -/
theorem singularValue_eq_approximationNumber (T : E →L[𝕜] F) (n : ℕ) :
    singularValue T n = T.approximationNumber n := rfl

/-- Convert the Mathlib-only finite-dimensional UI seminorm to the production
rectangular UI-seminorm structure. -/
noncomputable def UISeminorm.toTauCeti {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] (N : UISeminorm G) :
    TauCeti.UnitarilyInvariantSeminorm ℂ G G where
  toSeminorm := Seminorm.of N.toFun N.add_le N.smul
  unitary_invariant' :=
    TauCeti.UnitarilyInvariantSeminorm.unitary_invariant_of_isometry N.invariant

omit [CompleteSpace E] [CompleteSpace F] in
/-- The diagonal operators used by the two finite gauges coincide. -/
theorem diagOp_eq {n : ℕ} {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G]
    (b : OrthonormalBasis (Fin n) ℂ G) (x : Fin n → ℝ) :
    diagOp b x = TauCeti.diagOp b x := rfl

/-- Hence the finite gauges coincide. -/
theorem UISeminorm.gauge_eq {n : ℕ} {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] (N : UISeminorm G)
    (b : OrthonormalBasis (Fin n) ℂ G) (x : Fin n → ℝ) :
    N.gauge b x = N.toTauCeti.gauge b x := rfl

/-- The Challenge symmetric norming function as the production source norm. -/
noncomputable def SymmetricNormingFunction.toSourceNorm (N : SymmetricNormingFunction) :
    TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction where
  finiteNorm n := (N.finiteNorm n).toTauCeti
  normalized := by
    change (N.finiteNorm 1).toTauCeti.gauge
      (EuclideanSpace.basisFun (Fin 1) ℂ) (fun _ => 1) = 1
    rw [← UISeminorm.gauge_eq]
    exact N.normalized
  zero_pad := by
    intro n x
    change (N.finiteNorm (n + 1)).toTauCeti.gauge
        (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
        (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) =
      (N.finiteNorm n).toTauCeti.gauge
        (EuclideanSpace.basisFun (Fin n) ℂ) x
    rw [← UISeminorm.gauge_eq, ← UISeminorm.gauge_eq]
    exact N.zero_pad x

omit [CompleteSpace E] [CompleteSpace F] in
/-- A sequence represented as the approximation-number sequence of an operator
has the same extended norm in the Challenge and production vocabularies. -/
theorem SymmetricNormingFunction.evalSeq_eq_of_approximationNumber
    (N : SymmetricNormingFunction) (s : ℕ → ℝ) (T : E →L[𝕜] F)
    (h : ∀ n, T.approximationNumber n = s n) :
    N.evalSeq s = N.toSourceNorm.extendedGauge T := by
  unfold SymmetricNormingFunction.evalSeq
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge
  refine iSup_congr fun n => ?_
  congr 1
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix
  change
    (N.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) (fun i => s (i : ℕ)) =
      (N.finiteNorm n).toTauCeti.gauge (EuclideanSpace.basisFun (Fin n) ℂ)
        (fun i => approximationSingularValue (i : ℕ) T)
  rw [← UISeminorm.gauge_eq]
  congr 1
  funext i
  change s (i : ℕ) = T.approximationNumber (i : ℕ)
  exact (h (i : ℕ)).symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- Operator evaluation agrees with production evaluation. -/
theorem SymmetricNormingFunction.eval_eq
    (N : SymmetricNormingFunction) (T : E →L[𝕜] F) :
    N.eval T = N.toSourceNorm.extendedGauge T := by
  unfold SymmetricNormingFunction.eval
  exact N.evalSeq_eq_of_approximationNumber _ T
    (fun n => (singularValue_eq_approximationNumber T n).symm)

/-- Ideal membership is the same proposition on both sides of the bridge. -/
theorem SymmetricNormingFunction.finite_iff
    (N : SymmetricNormingFunction) (T : E →L[𝕜] F) :
    N.Finite T ↔ N.toSourceNorm.Mem T := by
  unfold SymmetricNormingFunction.Finite
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem
  rw [N.eval_eq T]

/-- The real-valued operator norms agree. -/
theorem SymmetricNormingFunction.norm_eq
    (N : SymmetricNormingFunction) (T : E →L[𝕜] F) :
    N.norm T = N.toSourceNorm.gauge T := by
  unfold SymmetricNormingFunction.norm
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge
  rw [N.eval_eq T]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Pole exclusion from the approximation-number bound. -/
theorem tangentDefined_of_approximationNumber_lt_one (S : E →L[𝕜] F)
    (h : ∀ n, S.approximationNumber n < 1) : TangentDefined S := by
  intro n
  rw [Real.cos_arcsin]
  have h0 : 0 ≤ singularValue S n := S.approximationNumber_nonneg n
  have h1 : singularValue S n < 1 := h n
  exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith))

end NormBridge

section VocabularyBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

omit [CompleteSpace E] [CompleteSpace F] in
theorem isTrialResidual_iff (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F)
    (E₀ R : F →L[𝕜] E) :
    IsTrialResidual A A₀ E₀ R ↔
      _root_.TauCeti.DavisKahan1970.IsTrialResidual A A₀ E₀ R := by
  constructor
  · exact fun h => ⟨h.isometry, h.mapsDomain, h.residualEquation⟩
  · exact fun h => ⟨h.isometry, h.mapsDomain, h.residualEquation⟩

theorem isExactDecomposition_iff (A : E →ₗ.[𝕜] E) (Λ₁ : G →ₗ.[𝕜] G)
    (F₀ : K →L[𝕜] E) (F₁ : G →L[𝕜] E) :
    IsExactDecomposition A Λ₁ F₀ F₁ ↔
      _root_.TauCeti.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ := by
  constructor
  · exact fun h => ⟨h.desiredIsometry, h.complementIsometry, h.orthogonal, h.complete,
      h.mapsDomain, h.intertwines⟩
  · exact fun h => ⟨h.desiredIsometry, h.complementIsometry, h.orthogonal, h.complete,
      h.mapsDomain, h.intertwines⟩

omit [CompleteSpace E] in
theorem realResolventSet_eq (A : E →ₗ.[𝕜] E) :
    realResolventSet A = TauCeti.LinearPMap.realResolventSet A := by
  ext lam
  rw [TauCeti.LinearPMap.mem_realResolventSet_iff]
  rfl

omit [CompleteSpace E] in
theorem realSpectrum_eq (A : E →ₗ.[𝕜] E) :
    realSpectrum A = TauCeti.LinearPMap.realSpectrum A := by
  ext lam
  rw [TauCeti.LinearPMap.mem_realSpectrum_iff, realSpectrum, Set.mem_compl_iff,
    realResolventSet_eq]

omit [CompleteSpace E] in
theorem semiboundedBelow_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedBelow A c ↔ TauCeti.LinearPMap.SemiboundedBelow A c := by
  rw [TauCeti.LinearPMap.semiboundedBelow_iff]
  exact Iff.rfl

omit [CompleteSpace E] in
theorem semiboundedAbove_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedAbove A c ↔ TauCeti.LinearPMap.SemiboundedAbove A c := by
  rw [TauCeti.LinearPMap.semiboundedAbove_iff]
  exact Iff.rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem sylvesterGap_iff (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) :
    SylvesterGap A B δ ↔ FormBoundedSylvesterGap A B δ := by
  constructor
  · rintro (⟨hβα, hgap⟩ | ⟨c, hA, hB⟩ | ⟨c, hA, hB⟩)
    · refine .intervalExterior hβα ?_
      rw [RealSpectrumIntervalExteriorGap, ← realSpectrum_eq, ← realSpectrum_eq]
      exact hgap
    · exact .leftAboveRightBelow c ((semiboundedBelow_iff _ _).1 hA)
        ((semiboundedAbove_iff _ _).1 hB)
    · exact .leftBelowRightAbove c ((semiboundedAbove_iff _ _).1 hA)
        ((semiboundedBelow_iff _ _).1 hB)
  · rintro (⟨hβα, hgap⟩ | ⟨c, hA, hB⟩ | ⟨c, hA, hB⟩)
    · refine .intervalExterior hβα ?_
      rw [RealSpectrumIntervalExteriorGap] at hgap
      rw [← realSpectrum_eq, ← realSpectrum_eq] at hgap
      exact hgap
    · exact .leftAboveRightBelow c ((semiboundedBelow_iff _ _).2 hA)
        ((semiboundedAbove_iff _ _).2 hB)
    · exact .leftBelowRightAbove c ((semiboundedAbove_iff _ _).2 hA)
        ((semiboundedBelow_iff _ _).2 hB)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Forget the source-facing orientation of the `sin 2Θ` gap when entering the
more general internal Sylvester-gap API. -/
theorem SinTwoThetaGap.toSylvesterGap {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {δ : ℝ} :
    SinTwoThetaGap A B δ → SylvesterGap A B δ := by
  intro h
  cases h with
  | intervalExterior hβα hA hB =>
      exact .intervalExterior hβα (Or.inl ⟨hA, hB⟩)
  | leftBelowRightAbove c hA hB =>
      exact .leftBelowRightAbove c hA hB

end VocabularyBridge

section ReducingBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem reduces_iff (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    Reduces A U ↔ TauCeti.LinearPMap.ReducesSubspace A U := by
  constructor
  · exact fun h => TauCeti.LinearPMap.ReducesSubspace.of_components
      h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact fun h => ⟨h.projection_mem_domain, h.orthogonalProjection_mem_domain,
      h.invariant, h.orthogonal_invariant⟩

omit [CompleteSpace E] in
theorem block_eq (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (h : Reduces A U) :
    block A U h =
      TauCeti.LinearPMap.reducingRestriction A U ((reduces_iff A U).1 h) := by
  refine LinearPMap.ext ?_ ?_
  · refine Submodule.ext fun x => ?_
    rw [TauCeti.LinearPMap.reducingRestriction_domain,
      TauCeti.LinearPMap.mem_reducingRestrictionDomain_iff]
    exact Iff.rfl
  · intro x hf hg
    refine Subtype.ext ?_
    exact (TauCeti.LinearPMap.coe_reducingRestriction_apply A U
      ((reduces_iff A U).1 h) x hg).symm

omit [CompleteSpace E] in
theorem addBounded_eq (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    addBounded A V = TauCeti.LinearPMap.addBounded A V := by
  refine LinearPMap.ext ?_ ?_
  · rw [TauCeti.LinearPMap.addBounded_domain]
    rfl
  · intro x hf hg
    rw [TauCeti.LinearPMap.addBounded_apply]
    rfl

/-- A Challenge Ritz bundle as the production unbounded Ritz pair. -/
def RitzData.toUnboundedRitzPair {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (D : RitzData A U) :
    TauCeti.DavisKahan.UnboundedRitzPair A U where
  trial :=
    { compression := D.compression
      compression_isSelfAdjoint := D.compression_selfAdjoint
      residual := D.residual
      residual_orthogonal := D.residual_orthogonal }
  mem_domain := D.mem_domain
  action_eq := fun z => (D.action_eq z).symm

omit [CompleteSpace E] in
theorem isOddFor_of_offDiagonal {H : E →L[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection]
    (h₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (h₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0) :
    TauCeti.IsOddFor U H := by
  constructor
  · intro x hx
    refine (Submodule.starProjection_apply_eq_zero_iff U).1 ?_
    have hx0 := congrArg (fun T : E →L[𝕜] E => T x) h₀
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at hx0
    rwa [Submodule.starProjection_eq_self_iff.mpr hx] at hx0
  · intro x hx
    rw [← Submodule.orthogonal_orthogonal U]
    refine (Submodule.starProjection_apply_eq_zero_iff Uᗮ).1 ?_
    have hx1 := congrArg (fun T : E →L[𝕜] E => T x) h₁
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at hx1
    rwa [Submodule.starProjection_eq_self_iff.mpr hx] at hx1

omit [CompleteSpace E] in
/-- A reducing subspace of the bounded perturbation supplies the reflection
intertwining data used by the ambient double-angle theorem. -/
theorem reflectionIntertwines_of_reduces {A : E →ₗ.[𝕜] E} {H : E →L[𝕜] E}
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) :
    TauCeti.DavisKahan.ReflectionIntertwines A H V :=
  TauCeti.DavisKahan.ReflectionIntertwines.ofReducesSubspace
    (by rw [← addBounded_eq]; exact (reduces_iff _ _).1 hV)

omit [CompleteSpace E] in
theorem formBound_upper_of_semiboundedAbove {A : E →ₗ.[𝕜] E}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) {α : ℝ}
    (hupper : SemiboundedAbove (block A U hU) α) :
    ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ α * ‖(x : E)‖ ^ 2 :=
  fun x hxU => hupper ⟨⟨(x : E), hxU⟩, x.2⟩

omit [CompleteSpace E] in
theorem formBound_lower_of_semiboundedBelow {A : E →ₗ.[𝕜] E}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) {c : ℝ}
    (hlower : SemiboundedBelow (block A Uᗮ hU.orthogonal) c) :
    ∀ x : A.domain, (x : E) ∈ Uᗮ →
      c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜 :=
  fun x hxU => hlower ⟨⟨(x : E), hxU⟩, x.2⟩

omit [CompleteSpace E] in
theorem directedDoubleSine_eq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedDoubleSine U V = TauCeti.DavisKahan.sinTwoThetaIdealBlock U V := rfl

end ReducingBridge


/-! ## 8. The four theorem families of Section 2

The Palomar surface contains five ordinary theorem declarations.  The two
whole-space tangent bounds are consequences in the source proof and are not
repeated here; the two `sin 2Θ` clauses remain separate.
-/

section Theorems

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- **The `sin Θ` theorem, at the source where-defined norm boundary.** -/
theorem sinTheta (N : SymmetricNormingFunction)

    {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {Λ₁ : G →ₗ.[𝕜] G}
    {E₀ : F →L[𝕜] E} {F₀ : K →L[𝕜] E} {F₁ : G →L[𝕜] E} {R : F →L[𝕜] E}
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (hres : IsTrialResidual A A₀ E₀ R) (hdec : IsExactDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SylvesterGap A₀ Λ₁ δ)
    (_hSin : N.Finite (directedSine E₀ F₀)) (hR : N.Finite R) :
    δ * N.norm (directedSine E₀ F₀) ≤ N.norm R := by
  have hsrc :=
    _root_.TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_rclike
      N.toSourceNorm A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁
      ((isTrialResidual_iff A A₀ E₀ R).1 hres)
      ((isExactDecomposition_iff A Λ₁ F₀ F₁).1 hdec)
      hδ ((sylvesterGap_iff A₀ Λ₁ δ).1 hgap) ((N.finite_iff R).1 hR)
  rw [N.norm_eq, N.norm_eq]
  exact hsrc.2

/-- **The `tan Θ` theorem, in its stronger residual form.** -/
theorem tanTheta (N : SymmetricNormingFunction)

    {A : E →ₗ.[𝕜] E} (_hA : IsSelfAdjoint A)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : SemiboundedBelow (block A Vᗮ hV.orthogonal) (α + δ))
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (D : RitzData A U) (hupper : SemiboundedAbove D.compression α)
    (hR : N.Finite D.residual) :
    TangentDefined (directedSineBlock U V) ∧
      N.SeqFinite (tanSeq (directedSineBlock U V)) ∧
      δ * N.seqNorm (tanSeq (directedSineBlock U V)) ≤ N.norm D.residual := by
  let hVc : TauCeti.DavisKahan.ReducingComplement A V :=
    TauCeti.DavisKahan.ReducingComplement.ofReducesSubspace ((reduces_iff A V).1 hV)
  have hupper' : TauCeti.LinearPMap.SemiboundedAbove
      D.toUnboundedRitzPair.trial.compression α :=
    (semiboundedAbove_iff D.compression α).1 hupper
  have hunwanted' : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_𝕜 :=
    fun y hy hyA => formBound_lower_of_semiboundedBelow hV hunwanted ⟨y, hyA⟩ hy
  obtain ⟨hlt, tanTheta0, htan, hmem, hbound⟩ :=
    _root_.TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_exists_rclike
      N.toSourceNorm D.toUnboundedRitzPair hVc hδ hupper' hunwanted'
      ((N.finite_iff D.residual).1 hR)
  have hseq : ∀ n, tanTheta0.approximationNumber n =
      tanSeq (directedSineBlock U V) n := by
    intro n
    change tanTheta0.approximationNumber n =
      Real.tan (Real.arcsin ((TauCeti.DavisKahan.TanTheta.directedSineBlock U V).approximationNumber n))
    exact htan n
  have heval : N.evalSeq (tanSeq (directedSineBlock U V)) =
      N.toSourceNorm.extendedGauge tanTheta0 :=
    N.evalSeq_eq_of_approximationNumber _ tanTheta0 hseq
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ ?_, ?_, ?_⟩
  · intro n
    change (TauCeti.DavisKahan.TanTheta.directedSineBlock U V).approximationNumber n < 1
    exact hlt n
  · change N.evalSeq (tanSeq (directedSineBlock U V)) ≠ ⊤
    rw [heval]
    exact hmem
  · change δ * (N.evalSeq (tanSeq (directedSineBlock U V))).toReal ≤ N.norm D.residual
    rw [heval, N.norm_eq]
    exact hbound

/-- **The residual clause of the `sin 2Θ` theorem, at the source common-domain
scope.** -/
theorem sinTwoTheta_directed (N : SymmetricNormingFunction)

    {A T : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces T V)
    (R : U →L[𝕜] E)
    (hres : ∀ u : U, ∀ hu : (u : E) ∈ T.domain,
      T ⟨(u : E), hu⟩ =
        A ⟨(u : E), by rw [← hdom]; exact hu⟩ + R u)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SinTwoThetaGap (block T V hV) (block T Vᗮ hV.orthogonal) δ)
    (_hAngle : N.Finite (directedDoubleSine V U)) (hR : N.Finite R) :
    δ * N.norm (directedDoubleSine V U) ≤ 2 * N.norm R := by
  have hUred : TauCeti.LinearPMap.ReducesSubspace A U := (reduces_iff A U).1 hU
  have hVred : TauCeti.LinearPMap.ReducesSubspace T V := (reduces_iff T V).1 hV
  have hgap' : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction T V hVred)
      (TauCeti.LinearPMap.reducingRestriction T Vᗮ hVred.orthogonal) δ := by
    rw [← block_eq T V hV, ← block_eq T Vᗮ hV.orthogonal]
    exact (sylvesterGap_iff _ _ _).1 hgap.toSylvesterGap
  have hky : ∀ k : ℕ,
      δ * kyFanApproximationGauge k (TauCeti.DavisKahan.sinTwoThetaIdealBlock V U) ≤
        2 * kyFanApproximationGauge k R :=
    _root_.TauCeti.DavisKahan1970.sinTwoTheta_commonDomain_block_kyFan
      hA hT hdom hUred hVred R hres hδ hgap'
  -- Fan dominance compares operators with a common source and target.  The
  -- residual is naturally defined only on `U`, so extend it by zero on `Uᗮ`.
  -- This preserves every approximation singular value and hence the source norm.
  let R0 : E →L[𝕜] E := R ∘L U.subtypeL.adjoint
  have hsameR : SameApproximationSingularSequence R0 R :=
    TauCeti.DavisKahan.ExactSinTheta.sameApproximationSingularValues_extendDomainByZero U R
  obtain ⟨hmemR, hgaugeR⟩ :=
    SameApproximationSingularSequence.normingMem_iff_and_gauge_eq N.toSourceNorm hsameR
  have hRsrc : N.toSourceNorm.Mem R := (N.finite_iff R).1 hR
  have hR0src : N.toSourceNorm.Mem R0 := hmemR.mpr hRsrc
  have htwo : ‖(2 : 𝕜)‖ = 2 := by simp
  have hscaled : ∀ k : ℕ,
      δ * kyFanApproximationGauge k (TauCeti.DavisKahan.sinTwoThetaIdealBlock V U) ≤
        kyFanApproximationGauge k ((2 : 𝕜) • R0) := by
    intro k
    rw [kyFanApproximationGauge_smul, htwo, hsameR.kyFanApproximationGauge_eq k]
    exact hky k
  have hMem2 : N.toSourceNorm.Mem ((2 : 𝕜) • R0) := by
    intro htop
    rw [N.toSourceNorm.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hR0src h
    · exact absurd h (by simp)
  obtain ⟨_, hle⟩ := N.toSourceNorm.mul_gauge_le_of_all_mul_kyFan_le
    hδ hMem2 hscaled
  rw [N.toSourceNorm.gauge_smul _ hR0src, htwo, hgaugeR] at hle
  rw [directedDoubleSine_eq, N.norm_eq, N.norm_eq]
  exact hle

/-- **The whole-space clause of the `sin 2Θ` theorem, with the printed
operator roles.** -/
theorem sinTwoTheta_ambient (N : SymmetricNormingFunction)

    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SinTwoThetaGap
      (block (addBounded A H) V hV)
      (block (addBounded A H) Vᗮ hV.orthogonal) δ)
    (_hAngle : N.Finite (ambientDoubleSine U V)) (hHmem : N.Finite H) :
    δ * N.norm (ambientDoubleSine U V) ≤ 2 * N.norm H := by
  have hUred : TauCeti.LinearPMap.ReducesSubspace A U := (reduces_iff A U).1 hU
  have hVredLocal : TauCeti.LinearPMap.ReducesSubspace (addBounded A H) V :=
    (reduces_iff (addBounded A H) V).1 hV
  have hVred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A H) V := by
    simpa only [addBounded_eq] using hVredLocal
  have hgapLocal : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction (addBounded A H) V hVredLocal)
      (TauCeti.LinearPMap.reducingRestriction
        (addBounded A H) Vᗮ hVredLocal.orthogonal) δ := by
    rw [← block_eq (addBounded A H) V hV,
      ← block_eq (addBounded A H) Vᗮ hV.orthogonal]
    exact (sylvesterGap_iff _ _ _).1 hgap.toSylvesterGap
  have hgap' : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A H) V hVred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A H) Vᗮ hVred.orthogonal) δ := by
    simpa only [addBounded_eq] using hgapLocal
  have hHsym : H.IsSymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH
  have hsrc :=
    _root_.TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_rclike
      N.toSourceNorm hA H hHsym hUred hVred hδ hgap'
      ((N.finite_iff H).1 hHmem)
  have hsame :=
    _root_.TauCeti.DavisKahan.Angle.sinTwoAngleOperator_hasSameApproximationNumbers
      (𝕜 := 𝕜) U V
  obtain ⟨_, hgauge⟩ :=
    SameApproximationSingularSequence.normingMem_iff_and_gauge_eq N.toSourceNorm hsame
  rw [N.norm_eq, N.norm_eq]
  change δ * N.toSourceNorm.gauge
      ((U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection - U.starProjection) ≤
    2 * N.toSourceNorm.gauge H
  rw [← hgauge]
  exact hsrc.2

/-- **The `tan 2Θ` theorem, in its stronger residual form.** -/
theorem tanTwoTheta (N : SymmetricNormingFunction)

    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E) (_hH : IsSelfAdjoint H)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : SemiboundedAbove (block A U hU) α)
    (hhigh : SemiboundedBelow (block A Uᗮ hU.orthogonal) (α + δ))
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V)
    (hRmem : N.Finite (Uᗮ.starProjection ∘L H ∘L U.starProjection)) :
    TangentDefined (directedDoubleSine U V) ∧
      N.SeqFinite (tanSeq (directedDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (directedDoubleSine U V)) ≤
        2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
  have hUred : TauCeti.LinearPMap.ReducesSubspace A U := (reduces_iff A U).1 hU
  have hVred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A H) V := by
    rw [← addBounded_eq]
    exact (reduces_iff _ _).1 hV
  have hUa := formBound_upper_of_semiboundedAbove hU hlow
  have hUb := formBound_lower_of_semiboundedBelow hU hhigh
  have hblk : TauCeti.DavisKahan.ExactSinTheta.projectionBlock Uᗮ U H =
      Uᗮ.starProjection ∘L H ∘L U.starProjection := rfl
  have hext : N.toSourceNorm.extendedGauge
      (TauCeti.DavisKahan.ExactSinTheta.projectionBlock Uᗮ U H) =
      N.toSourceNorm.extendedGauge
        (TauCeti.DavisKahan.ExactSinTheta.blockCompression Uᗮ U H) :=
    N.toSourceNorm.extendedGauge_eq_of_hasSameApproximationNumbers
      (TauCeti.DavisKahan.ExactSinTheta.projectionBlock_same_compression Uᗮ U H)
  have hRproj : N.toSourceNorm.Mem
      (TauCeti.DavisKahan.ExactSinTheta.projectionBlock Uᗮ U H) := by
    rw [hblk]
    exact (N.finite_iff _).1 hRmem
  have hRblock : N.toSourceNorm.Mem
      (TauCeti.DavisKahan.ExactSinTheta.blockCompression Uᗮ U H) := by
    unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem at hRproj ⊢
    rwa [← hext]
  obtain ⟨hlt, T, htan, hmem, hbound⟩ :=
    _root_.TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_rclike
      N.toSourceNorm V hA hUred (isOddFor_of_offDiagonal hoffdiag₀ hoffdiag₁)
      hVred hUa hUb (by linarith) hRblock
  have hseq : ∀ n, T.approximationNumber n = tanSeq (directedDoubleSine U V) n := by
    intro n
    change T.approximationNumber n =
      Real.tan (Real.arcsin
        ((TauCeti.DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n))
    exact htan n
  have heval : N.evalSeq (tanSeq (directedDoubleSine U V)) =
      N.toSourceNorm.extendedGauge T :=
    N.evalSeq_eq_of_approximationNumber _ T hseq
  have hgauge : N.toSourceNorm.gauge
      (TauCeti.DavisKahan.ExactSinTheta.projectionBlock Uᗮ U H) =
      N.toSourceNorm.gauge
        (TauCeti.DavisKahan.ExactSinTheta.blockCompression Uᗮ U H) := by
    unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge
    rw [hext]
  have hδeq : α + δ - α = δ := by ring
  rw [hδeq] at hbound
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ ?_, ?_, ?_⟩
  · intro n
    change (TauCeti.DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n < 1
    exact hlt n
  · change N.evalSeq (tanSeq (directedDoubleSine U V)) ≠ ⊤
    rw [heval]
    exact hmem
  · change δ * (N.evalSeq (tanSeq (directedDoubleSine U V))).toReal ≤
      2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection)
    rw [heval, N.norm_eq]
    change δ * N.toSourceNorm.gauge T ≤
      2 * N.toSourceNorm.gauge (Uᗮ.starProjection ∘L H ∘L U.starProjection)
    calc
      δ * N.toSourceNorm.gauge T ≤
          2 * N.toSourceNorm.gauge
            (TauCeti.DavisKahan.ExactSinTheta.blockCompression Uᗮ U H) := hbound
      _ = 2 * N.toSourceNorm.gauge
            (TauCeti.DavisKahan.ExactSinTheta.projectionBlock Uᗮ U H) := by
          rw [hgauge]
      _ = 2 * N.toSourceNorm.gauge
            (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by rw [hblk]

end Theorems

end RotationOfEigenvectors
