/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.PositiveSqrt
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm


/-!
# Isometric range factorization of an injective trial map

Reusable finite-dimensional frame factorization for a rectangular linear map.
This module is independent of Davis--Kahan spectral-gap assumptions.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.FrameFactorization`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `b806b36`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- A quantitative lower frame bound for a not-necessarily-isometric trial
map.  Davis--Kahan's parameter `e` is this lower singular-value bound. -/
def LowerFrameBound (X : F →ₗ[𝕜] E) (ε : ℝ) : Prop :=
  ∀ y, ε * ‖y‖ ≤ ‖X y‖

/-- Davis--Kahan's Gram-operator lower bound
`X⋆ X ≥ ε² I`, written as its quadratic-form inequality.

The real part makes the definition uniform over `ℝ` and `ℂ`; for the positive
Gram operator the quadratic form is real and equals `‖X y‖²`. -/
def GramLowerBound (X : F →ₗ[𝕜] E) (ε : ℝ) : Prop :=
  ∀ y, ε ^ 2 * ‖y‖ ^ 2 ≤
    RCLike.re ⟪(X.adjoint ∘ₗ X) y, y⟫_𝕜

/-- The quadratic form of the Gram operator is the squared norm of the
rectangular map. -/
theorem gramQuadraticForm_eq_norm_sq (X : F →ₗ[𝕜] E) (y : F) :
    RCLike.re ⟪(X.adjoint ∘ₗ X) y, y⟫_𝕜 = ‖X y‖ ^ 2 := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
    ← norm_sq_eq_re_inner (𝕜 := 𝕜)]

/-- A nonnegative lower frame bound implies the corresponding Gram-operator
quadratic-form bound. -/
theorem LowerFrameBound.gramLowerBound {X : F →ₗ[𝕜] E} {ε : ℝ}
    (hframe : LowerFrameBound X ε) (hε : 0 ≤ ε) :
    GramLowerBound X ε := by
  intro y
  rw [gramQuadraticForm_eq_norm_sq]
  have hle : ε * ‖y‖ ≤ ‖X y‖ := hframe y
  have hleft : 0 ≤ ε * ‖y‖ := mul_nonneg hε (norm_nonneg y)
  have hdiff : 0 ≤ ‖X y‖ - ε * ‖y‖ := sub_nonneg.mpr hle
  have hsum : 0 ≤ ‖X y‖ + ε * ‖y‖ :=
    add_nonneg (norm_nonneg (X y)) hleft
  have hprod := mul_nonneg hdiff hsum
  nlinarith

/-- The Gram-operator lower bound implies the norm-form lower frame bound when
its parameter is nonnegative. -/
theorem GramLowerBound.lowerFrameBound {X : F →ₗ[𝕜] E} {ε : ℝ}
    (hgram : GramLowerBound X ε) (_hε : 0 ≤ ε) :
    LowerFrameBound X ε := by
  intro y
  have hsq := hgram y
  rw [gramQuadraticForm_eq_norm_sq] at hsq
  by_contra hnot
  have hlt : ‖X y‖ < ε * ‖y‖ := lt_of_not_ge hnot
  have hleft_pos : 0 < ε * ‖y‖ :=
    lt_of_le_of_lt (norm_nonneg (X y)) hlt
  have hdiff : 0 < ε * ‖y‖ - ‖X y‖ := sub_pos.mpr hlt
  have hsum : 0 < ε * ‖y‖ + ‖X y‖ :=
    add_pos_of_pos_of_nonneg hleft_pos (norm_nonneg (X y))
  have hprod := mul_pos hdiff hsum
  nlinarith

/-- For a nonnegative parameter, the paper's Gram lower bound and the norm-form
lower frame bound are equivalent. -/
theorem lowerFrameBound_iff_gramLowerBound (X : F →ₗ[𝕜] E) {ε : ℝ}
    (hε : 0 ≤ ε) :
    LowerFrameBound X ε ↔ GramLowerBound X ε := by
  constructor
  · intro hframe
    exact hframe.gramLowerBound hε
  · intro hgram
    exact hgram.lowerFrameBound hε

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- A positive lower frame bound implies injectivity. -/
theorem LowerFrameBound.injective {X : F →ₗ[𝕜] E} {ε : ℝ}
    (hframe : LowerFrameBound X ε) (hε : 0 < ε) :
    Function.Injective X := by
  intro x y hxy
  have hmul : ε * ‖x - y‖ ≤ 0 := by
    simpa [map_sub, hxy] using hframe (x - y)
  have hnorm : ‖x - y‖ ≤ 0 := by
    nlinarith [norm_nonneg (x - y)]
  apply sub_eq_zero.mp
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

/-- A positive Gram lower bound implies injectivity. -/
theorem GramLowerBound.injective {X : F →ₗ[𝕜] E} {ε : ℝ}
    (hgram : GramLowerBound X ε) (hε : 0 < ε) :
    Function.Injective X :=
  (hgram.lowerFrameBound hε.le).injective hε

/-- The positive square root of the Gram operator `X⋆ X`. -/
@[expose]
noncomputable def trialGramSqrt (X : F →ₗ[𝕜] E) : F →ₗ[𝕜] F :=
  X.isPositive_adjoint_comp_self.sqrt

/-- The Gram square root has the same pointwise norm as the original
rectangular map. -/
@[simp]
theorem norm_trialGramSqrt_apply (X : F →ₗ[𝕜] E) (x : F) :
    ‖trialGramSqrt X x‖ = ‖X x‖ := by
  have hsq : ‖trialGramSqrt X x‖ ^ 2 = ‖X x‖ ^ 2 :=
    (X.isPositive_adjoint_comp_self.sq_norm_sqrt_apply x).trans <| by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
        ← norm_sq_eq_re_inner (𝕜 := 𝕜)]
  rw [← Real.sqrt_sq (norm_nonneg (trialGramSqrt X x)),
    ← Real.sqrt_sq (norm_nonneg (X x)), hsq]

/-- The Gram square root has exactly the kernel of the original rectangular
map. -/
theorem ker_trialGramSqrt (X : F →ₗ[𝕜] E) :
    LinearMap.ker (trialGramSqrt X) = LinearMap.ker X := by
  calc
    LinearMap.ker (trialGramSqrt X) =
        LinearMap.ker (X.adjoint ∘ₗ X) :=
      X.isPositive_adjoint_comp_self.ker_sqrt
    _ = LinearMap.ker X := LinearMap.ker_adjoint_comp_self X

/-- Injectivity of `X` transfers to its positive Gram square root. -/
theorem trialGramSqrt_injective {X : F →ₗ[𝕜] E}
    (hX : Function.Injective X) : Function.Injective (trialGramSqrt X) := by
  rw [← LinearMap.ker_eq_bot, ker_trialGramSqrt X, LinearMap.ker_eq_bot]
  exact hX

/-- For an injective trial map, the positive Gram square root is an invertible
coordinate map. -/
@[expose]
noncomputable def trialGramSqrtEquiv (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) : F ≃ₗ[𝕜] F :=
  let hinj := trialGramSqrt_injective hX
  LinearEquiv.ofBijective (trialGramSqrt X)
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The equivalence is the Gram square root as a linear map, definitionally.
`trialGramSqrtEquiv` only adds the bijectivity that injectivity of `X` supplies
in finite dimensions; it does not change the map. -/
@[simp] theorem trialGramSqrtEquiv_toLinearMap (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) :
    (trialGramSqrtEquiv X hX).toLinearMap = trialGramSqrt X :=
  rfl

/-- The invertible coordinate factor has the same pointwise norm as the
original trial map. -/
@[simp]
theorem norm_trialGramSqrtEquiv_apply (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) (x : F) :
    ‖trialGramSqrtEquiv X hX x‖ = ‖X x‖ := by
  -- names the application so the norm bound applies to it directly.
  change ‖trialGramSqrt X x‖ = ‖X x‖
  exact norm_trialGramSqrt_apply X x

/-- Isometric polar factor of an injective rectangular trial map. -/
@[expose]
noncomputable def orthonormalizedEmbedding (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) : F →ₗᵢ[𝕜] E where
  toLinearMap := X ∘ₗ (trialGramSqrtEquiv X hX).symm.toLinearMap
  norm_map' y := by
    -- names the application so the norm bound applies to it directly.
    change ‖X ((trialGramSqrtEquiv X hX).symm y)‖ = ‖y‖
    rw [← norm_trialGramSqrt_apply X]
    -- names the application so the norm bound applies to it directly.
    change ‖(trialGramSqrtEquiv X hX)
      ((trialGramSqrtEquiv X hX).symm y)‖ = ‖y‖
    rw [(trialGramSqrtEquiv X hX).apply_symm_apply]

/-- The canonical polar factors recompose to the original rectangular map. -/
theorem orthonormalizedEmbedding_comp_trialGramSqrtEquiv
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    (orthonormalizedEmbedding X hX).toLinearMap ∘ₗ
        (trialGramSqrtEquiv X hX).toLinearMap = X := by
  ext x
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change X ((trialGramSqrtEquiv X hX).symm
    (trialGramSqrtEquiv X hX x)) = X x
  rw [(trialGramSqrtEquiv X hX).symm_apply_apply]

/-- The isometric polar factor and the original trial map have the same range. -/
theorem range_orthonormalizedEmbedding (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) :
    LinearMap.range (orthonormalizedEmbedding X hX).toLinearMap =
      LinearMap.range X := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨(trialGramSqrtEquiv X hX).symm x, ?_⟩
    rfl
  · rintro y ⟨x, rfl⟩
    refine ⟨trialGramSqrtEquiv X hX x, ?_⟩
    exact LinearMap.congr_fun
      (orthonormalizedEmbedding_comp_trialGramSqrtEquiv X hX) x

/-- Reusable proof-carrying isometric range factorization of a trial map. -/
structure TrialMapFrameFactorization (X : F →ₗ[𝕜] E) where
  /-- Isometric embedding representing the range of `X`. -/
  isometry : F →ₗᵢ[𝕜] E
  /-- Invertible coordinate distortion on the trial space. -/
  coordinate : F ≃ₗ[𝕜] F
  /-- Reconstruction of the original trial map. -/
  factor : isometry.toLinearMap ∘ₗ coordinate.toLinearMap = X
  /-- The isometric representative has exactly the original range. -/
  range_eq : LinearMap.range isometry.toLinearMap = LinearMap.range X

/-- The canonical Gram/polar factorization of an injective trial map. -/
@[expose]
noncomputable def trialMapFrameFactorization (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) : TrialMapFrameFactorization X where
  isometry := orthonormalizedEmbedding X hX
  coordinate := trialGramSqrtEquiv X hX
  factor := orthonormalizedEmbedding_comp_trialGramSqrtEquiv X hX
  range_eq := range_orthonormalizedEmbedding X hX

/-- The isometry factor of the frame factorization is the orthonormalized
embedding, definitionally. -/
@[simp] theorem trialMapFrameFactorization_isometry
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    (trialMapFrameFactorization X hX).isometry =
      orthonormalizedEmbedding X hX :=
  rfl

/-- The coordinate factor is the Gram square root, definitionally.  Together
with `trialMapFrameFactorization_isometry` this is the whole content of the
factorization `X = (orthonormalized embedding) ∘ (Gram square root)`: both
factors are the ones already named, so `simp` can eliminate the bundled record. -/
@[simp] theorem trialMapFrameFactorization_coordinate
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    (trialMapFrameFactorization X hX).coordinate =
      trialGramSqrtEquiv X hX :=
  rfl

/-- Pointwise bound for the inverse coordinate factor supplied by a positive
lower frame bound. -/
theorem norm_trialGramSqrtEquiv_symm_apply_le
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {ε : ℝ} (hframe : LowerFrameBound X ε) (hε : 0 < ε) (y : F) :
    ‖(trialGramSqrtEquiv X hX).symm y‖ ≤ ε⁻¹ * ‖y‖ := by
  have hraw :
      ε * ‖(trialGramSqrtEquiv X hX).symm y‖ ≤ ‖y‖ := by
    calc
      ε * ‖(trialGramSqrtEquiv X hX).symm y‖ ≤
          ‖X ((trialGramSqrtEquiv X hX).symm y)‖ :=
        hframe ((trialGramSqrtEquiv X hX).symm y)
      _ = ‖trialGramSqrtEquiv X hX
          ((trialGramSqrtEquiv X hX).symm y)‖ :=
        (norm_trialGramSqrtEquiv_apply X hX
          ((trialGramSqrtEquiv X hX).symm y)).symm
      _ = ‖y‖ := by
        rw [(trialGramSqrtEquiv X hX).apply_symm_apply]
  have hdiv :
      ‖(trialGramSqrtEquiv X hX).symm y‖ ≤ ‖y‖ / ε := by
    apply (le_div_iff₀ hε).2
    simpa [mul_comm] using hraw
  simpa [div_eq_mul_inv, mul_comm] using hdiv

/-- Operator-norm bound for the inverse coordinate factor.  This is the
quantitative conditioning statement extracted from the lower frame bound. -/
theorem opNorm_trialGramSqrtEquiv_symm_le
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {ε : ℝ} (hframe : LowerFrameBound X ε) (hε : 0 < ε) :
    ‖(trialGramSqrtEquiv X hX).symm.toLinearMap.toContinuousLinearMap‖ ≤ ε⁻¹ := by
  refine (trialGramSqrtEquiv X hX).symm.toLinearMap.toContinuousLinearMap.opNorm_le_bound
    (inv_nonneg.mpr hε.le) ?_
  intro y
  exact norm_trialGramSqrtEquiv_symm_apply_le X hX hframe hε y

/-- Right-composition by the inverse frame coordinate costs at most the inverse
lower-frame constant in every rectangular unitarily invariant norm. -/
theorem uiNorm_comp_trialGramSqrtEquiv_symm_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {ε : ℝ} (hframe : LowerFrameBound X ε) (hε : 0 < ε)
    (A : F →ₗ[𝕜] E) :
    N (A ∘ₗ (trialGramSqrtEquiv X hX).symm.toLinearMap) ≤
      N A * ε⁻¹ := by
  calc
    N (A ∘ₗ (trialGramSqrtEquiv X hX).symm.toLinearMap) ≤
        N A * ‖(trialGramSqrtEquiv X hX).symm.toLinearMap.toContinuousLinearMap‖ :=
      N.comp_le_mul_opNorm A (trialGramSqrtEquiv X hX).symm.toLinearMap
    _ ≤ N A * ε⁻¹ :=
      mul_le_mul_of_nonneg_left
        (opNorm_trialGramSqrtEquiv_symm_le X hX hframe hε)
        (N.nonneg A)

/-- Recomposition on the right by the inverse coordinate factor recovers the
isometric range representative. -/
theorem trialMap_comp_trialGramSqrtEquiv_symm
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    X ∘ₗ (trialGramSqrtEquiv X hX).symm.toLinearMap =
      (orthonormalizedEmbedding X hX).toLinearMap := by
  ext y
  have hfactor := LinearMap.congr_fun
    (orthonormalizedEmbedding_comp_trialGramSqrtEquiv X hX)
    ((trialGramSqrtEquiv X hX).symm y)
  calc
    X ((trialGramSqrtEquiv X hX).symm y) =
        (orthonormalizedEmbedding X hX)
          (trialGramSqrtEquiv X hX
            ((trialGramSqrtEquiv X hX).symm y)) :=
      hfactor.symm
    _ = (orthonormalizedEmbedding X hX) y := by
      rw [(trialGramSqrtEquiv X hX).apply_symm_apply]


end TauCeti
