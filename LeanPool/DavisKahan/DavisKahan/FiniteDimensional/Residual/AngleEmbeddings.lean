/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Residual.AngleEmbedding
public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.TanTheta.RitzResidual
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Internal.SpectralBounds
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.MoorePenroseInverse

/-!
# Coordinate tangent and double-angle embeddings

For an isometric trial map `X : F → E`, write

* `C = P_U X : F → E`,
* `S = P_{Uᗮ} X : F → E`,
* `|C| = (C⋆C)^(1/2) : F → F`.

The coordinate tangent is `S |C|⁺`.  The double-angle source cosine is
`C⋆C - S⋆S`, while the rectangular double-angle sine is `2 S |C|`.  These
choices put every denominator on the trial-coordinate space and avoid the
extra cosine factor produced by the former ambient pseudoinverse formulas.

The definitions below are totalized by Moore--Penrose inverses.  Singular-value
identifications still require a simultaneous CS decomposition and are not
asserted here merely from these definitions.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Trial-coordinate tangent map `S |C|⁺`.

Its nonzero singular values are intended to be the tangents of the principal
angles.  That identification is a separate CS-decomposition theorem; this
definition only fixes the canonical coordinate semantics. -/
noncomputable def tanThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  sinThetaEmbedding U X ∘ₗ
    TauCeti.moorePenroseInverse (cosThetaMagnitude U X)

/-- Transversality supplies the injectivity that makes the coordinate tangent
well defined.

This is what the retired `tanThetaEmbedding_eq_inverseOnRange_of_isTransverse`
actually contained.  Its stated conclusion was `rfl` — `inverseOnRange` was a
definitional alias for `moorePenroseInverse`, which is what `tanThetaEmbedding`
is already defined by — so the only content was this translation of
transversality into injectivity. -/
theorem cosThetaMagnitude_injective_of_isTransverse
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverse (approximateSubspace X) U) :
    Function.Injective (cosThetaMagnitude U X) :=
  cosThetaMagnitude_injective U X
    (LinearMap.ker_eq_bot.mp ((tanThetaEmbedding_defined_iff U X).mp htrans))

/-- Trial-coordinate double-angle sine `2 S |C|`.

On a simultaneous principal-angle basis this has singular values
`2 sin θᵢ cos θᵢ = sin (2 θᵢ)`. -/
noncomputable def sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  (2 : 𝕜) • (sinThetaEmbedding U X ∘ₗ cosThetaMagnitude U X)

/-- Every rectangular unitarily invariant norm of the coordinate double-angle
sine is at most twice the corresponding single-angle sine norm. -/
theorem sinTwoThetaEmbedding_uiNorm_le_two_mul
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E) :
    N (sinTwoThetaEmbedding U X) ≤ 2 * N (sinThetaEmbedding U X) := by
  rw [sinTwoThetaEmbedding, N.smul_eq, RCLike.norm_ofNat]
  have hcomp := N.comp_le_mul_opNorm
    (sinThetaEmbedding U X) (cosThetaMagnitude U X)
  calc
    2 * N (sinThetaEmbedding U X ∘ₗ cosThetaMagnitude U X)
        ≤ 2 * (N (sinThetaEmbedding U X) *
          ‖(cosThetaMagnitude U X).toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ ≤ 2 * (N (sinThetaEmbedding U X) * 1) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (cosThetaMagnitude_opNorm_le_one U X) (N.nonneg _))
        (by positivity)
    _ = 2 * N (sinThetaEmbedding U X) := by ring

/-- Totalized double-angle tangent
`(2 S |C|) (C⋆C - S⋆S)⁺`. -/
noncomputable def tanTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  sinTwoThetaEmbedding U X ∘ₗ
    TauCeti.moorePenroseInverse
      (cosTwoThetaSourceOperator U X)


/-! ## Tangent singular values and ordered residual graph bounds

The right singular basis of the directed sine block diagonalizes the positive
source cosine because `|C|² = I - S†S`.  The resulting CS-coordinate
calculation identifies the canonical tangent singular values.  Ordered Ritz
separation is then reduced to the accepted interval-gap theorem by choosing the
extreme Ritz eigenvalues.
-/

private theorem tangentScalar_mono {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    a / Real.sqrt (1 - a ^ 2) ≤ b / Real.sqrt (1 - b ^ 2) := by
  have hb0 : 0 ≤ b := ha.trans hab
  have ha1 : a < 1 := hab.trans_lt hb
  have hca : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hcb : 0 < Real.sqrt (1 - b ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  rw [div_le_div_iff₀ hca hcb]
  rw [← sq_le_sq₀ (mul_nonneg ha hcb.le) (mul_nonneg hb0 hca.le)]
  rw [mul_pow, mul_pow, Real.sq_sqrt (by nlinarith),
    Real.sq_sqrt (by nlinarith)]
  nlinarith [sq_nonneg (b - a)]

private theorem cosThetaMagnitude_apply_rightSingularBasis
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (i : Fin (finrank 𝕜 F)) :
    cosThetaMagnitude U X (rightSingularBasis (sinThetaEmbedding U X) i) =
      ((Real.sqrt
        (1 - (sinThetaEmbedding U X).singularValues i ^ 2) : ℝ) : 𝕜) •
        rightSingularBasis (sinThetaEmbedding U X) i := by
  let S := sinThetaEmbedding U X
  let C := cosThetaMagnitude U X
  let v := rightSingularBasis S i
  let σ := S.singularValues i
  let c := Real.sqrt (1 - σ ^ 2)
  have hσ0 : 0 ≤ σ := S.singularValues_nonneg i
  have hσ1 : σ ≤ 1 :=
    singularValues_le_one_of_contraction
      (sinThetaEmbedding_apply_norm_le U X) rfl i
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hSgram : sinThetaGram U X v = (((σ ^ 2 : ℝ) : 𝕜)) • v := by
    simpa [S, v, σ, sinThetaGram] using
      adjointCompSelf_apply_rightSingularBasis S i
  have hpartition := LinearMap.congr_fun
    (cosThetaGram_add_sinThetaGram_eq_id U X) v
  have hCgram : cosThetaGram U X v = (((1 - σ ^ 2 : ℝ) : 𝕜)) • v := by
    change cosThetaGram U X v + sinThetaGram U X v = v at hpartition
    rw [hSgram] at hpartition
    -- rewriting backwards would also hit the `v` inside the Gram block
    have hsub : cosThetaGram U X v = v - ((σ ^ 2 : ℝ) : 𝕜) • v :=
      eq_sub_of_add_eq hpartition
    rw [hsub, RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, one_smul]
  have hsq := LinearMap.congr_fun (cosThetaMagnitude_sq U X) v
  change C (C v) = cosThetaGram U X v at hsq
  rw [hCgram] at hsq
  have hcSq : c * c = 1 - σ ^ 2 := by
    change Real.sqrt (1 - σ ^ 2) * Real.sqrt (1 - σ ^ 2) = 1 - σ ^ 2
    rw [Real.mul_self_sqrt]
    nlinarith
  have hsq' : C (C v) = (((c : ℝ) : 𝕜) * ((c : ℝ) : 𝕜)) • v := by
    rw [hsq, ← RCLike.ofReal_mul, hcSq]
  have hpos : C.IsPositive := by
    simpa [C, cosThetaMagnitude, trialGramSqrt] using
      (cosThetaEmbedding U X).isPositive_adjoint_comp_self.sqrt_isPositive
  simpa [C, v, c, S, σ] using
    hpos.apply_eq_smul_of_apply_apply_eq_smul hc0 hsq'

private theorem moorePenroseInverse_cosThetaMagnitude_apply_rightSingularBasis
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverse (approximateSubspace X) U)
    (i : Fin (finrank 𝕜 F)) :
    TauCeti.moorePenroseInverse (cosThetaMagnitude U X)
        (rightSingularBasis (sinThetaEmbedding U X) i) =
      ((((Real.sqrt
        (1 - (sinThetaEmbedding U X).singularValues i ^ 2) : ℝ) : 𝕜)⁻¹) •
        rightSingularBasis (sinThetaEmbedding U X) i) := by
  let S := sinThetaEmbedding U X
  let C := cosThetaMagnitude U X
  let v := rightSingularBasis S i
  let σ := S.singularValues i
  let c := Real.sqrt (1 - σ ^ 2)
  have hσ1 : σ < 1 :=
    singularValues_sinThetaEmbedding_lt_one_of_isTransverse U X htrans i
  have hσ0 : 0 ≤ σ := S.singularValues_nonneg i
  have hc : 0 < c := Real.sqrt_pos.2 (by nlinarith)
  have hCv : C v = (((c : ℝ) : 𝕜)) • v := by
    simpa [C, v, c, S, σ] using
      cosThetaMagnitude_apply_rightSingularBasis U X i
  have hCinj : Function.Injective C :=
    cosThetaMagnitude_injective U X
      (LinearMap.ker_eq_bot.mp ((tanThetaEmbedding_defined_iff U X).mp htrans))
  have hleft := LinearMap.congr_fun
    (TauCeti.moorePenroseInverse_comp_eq_id_of_injective C hCinj) v
  change TauCeti.moorePenroseInverse C (C v) = v at hleft
  have hcK : (((c : ℝ) : 𝕜)) ≠ 0 := RCLike.ofReal_ne_zero.mpr hc.ne'
  calc
    TauCeti.moorePenroseInverse C v =
        TauCeti.moorePenroseInverse C
          (((((c : ℝ) : 𝕜))⁻¹) • C v) := by
            rw [hCv, inv_smul_smul₀ hcK]
    _ = (((((c : ℝ) : 𝕜))⁻¹) •
        TauCeti.moorePenroseInverse C (C v)) := by rw [map_smul]
    _ = (((((c : ℝ) : 𝕜))⁻¹) • v) := by rw [hleft]
    _ = _ := by rfl

private theorem tanThetaEmbedding_apply_rightSingularBasis
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverse (approximateSubspace X) U)
    (i : Fin (finrank 𝕜 F)) :
    tanThetaEmbedding U X (rightSingularBasis (sinThetaEmbedding U X) i) =
      ((((Real.sqrt
        (1 - (sinThetaEmbedding U X).singularValues i ^ 2) : ℝ) : 𝕜)⁻¹) •
        sinThetaEmbedding U X
          (rightSingularBasis (sinThetaEmbedding U X) i)) := by
  rw [tanThetaEmbedding, LinearMap.comp_apply,
    moorePenroseInverse_cosThetaMagnitude_apply_rightSingularBasis U X htrans i,
    map_smul]

/-- Under transversality, the coordinate tangent has the principal tangent
singular-value sequence. -/
theorem singularValues_tanThetaEmbedding
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverse (approximateSubspace X) U) :
    (tanThetaEmbedding U X).singularValues =
      principalTangents (approximateSubspace X) U := by
  classical
  let S := sinThetaEmbedding U X
  let T := tanThetaEmbedding U X
  let b := rightSingularBasis S
  let d : Fin (finrank 𝕜 F) → ℝ := fun i =>
    S.singularValues i / Real.sqrt (1 - S.singularValues i ^ 2)
  have hd0 : ∀ i, 0 ≤ d i := by
    intro i
    exact div_nonneg (S.singularValues_nonneg i) (Real.sqrt_nonneg _)
  have hdanti : Antitone d := by
    intro i j hij
    exact tangentScalar_mono (S.singularValues_nonneg j)
      (S.singularValues_antitone (Fin.le_def.mp hij))
      (singularValues_sinThetaEmbedding_lt_one_of_isTransverse U X htrans i)
  let D : F →ₗ[𝕜] F := diagOp b d
  have hgram : T.adjoint ∘ₗ T = D.adjoint ∘ₗ D := by
    apply b.toBasis.ext
    intro i
    apply b.repr.injective
    ext j
    -- the `i` side still reads `T (b.toBasis i)`; both the `let` and the
    -- `toBasis` coercion have to go before the rewrite can match it
    simp only [OrthonormalBasis.repr_apply_apply, LinearMap.comp_apply,
      OrthonormalBasis.coe_toBasis, T, b]
    rw [LinearMap.adjoint_inner_right]
    -- Left as a `rw` chain on purpose: `simp only` with this same list makes no progress: every
    -- lemma here needs the goal in the shape the previous rewrite leaves it, and simp matches
    -- against the original.
    rw [tanThetaEmbedding_apply_rightSingularBasis U X htrans j,
      tanThetaEmbedding_apply_rightSingularBasis U X htrans i,
      inner_smul_left, inner_smul_right, map_inv₀, RCLike.conj_ofReal,
      TauCeti.inner_apply_rightSingularBasis]
    -- the goal is an application, not a composition, so `diagOp_comp` cannot
    -- fire; apply the diagonal action twice instead
    rw [adjoint_diagOp]
    simp only [D, b, S, diagOp_apply_basis, map_smul, smul_smul]
    rw [inner_smul_right]
    by_cases hji : j = i
    · subst j
      have hσ1 := singularValues_sinThetaEmbedding_lt_one_of_isTransverse U X htrans i
      have hσ0 := S.singularValues_nonneg i
      have hc : 0 < Real.sqrt (1 - S.singularValues i ^ 2) :=
        Real.sqrt_pos.2 (by nlinarith)
      have hcK : ((((Real.sqrt (1 - S.singularValues i ^ 2) : ℝ) : 𝕜))) ≠ 0 :=
        RCLike.ofReal_ne_zero.mpr hc.ne'
      simp only [d, S]
      -- both sides are the same real quotient pushed through `ofReal`
      push_cast
      ring
    · have hbji : ⟪b j, b i⟫_𝕜 = 0 := by
        simp [orthonormal_iff_ite.mp b.orthonormal j i, ite_eq_right hji]
      rw [hbji, mul_zero]
      simp []
  have hTD : T.singularValues = D.singularValues := singularValues_eq_of_gram_eq hgram
  ext k
  rcases lt_or_ge k (finrank 𝕜 F) with hk | hk
  · let i : Fin (finrank 𝕜 F) := ⟨k, hk⟩
    calc
      T.singularValues k = D.singularValues k := by rw [hTD]
      _ = d i := by
        simpa [D, i] using singularValues_diagOp (𝕜 := 𝕜)
          (E := F) (n := finrank 𝕜 F) rfl b hdanti hd0 i
      _ = Real.tan (Real.arcsin (S.singularValues k)) := by
        rw [Real.tan_arcsin]
      _ = principalTangents (approximateSubspace X) U k := by
        simpa [S] using
          (principalTangents_approximateSubspace_apply U X k).symm
  · rw [T.singularValues_of_finrank_le hk]
    rw [principalTangents_approximateSubspace_apply U X k]
    rw [S.singularValues_of_finrank_le hk]
    simp


-- the top eigenvalue only exists on a nonzero coordinate space; every caller
-- splits on `subsingleton_or_nontrivial F` before reaching here
omit [FiniteDimensional 𝕜 E] in
private theorem exists_intervalGap_of_orderedGap
    {A : E →ₗ[𝕜] E} {U : Submodule 𝕜 E}
     [Nontrivial F]
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    ∃ β α, β ≤ α ∧ PointSpectrumIn M ⊤ (Set.Icc β α) ∧
      PointSpectrumIn A Uᗮ (Set.Ici (α + δ)) := by
  let : NeZero (finrank 𝕜 F) := ⟨Nat.ne_of_gt Module.finrank_pos⟩
  let iTop : Fin (finrank 𝕜 F) := ⟨0, Module.finrank_pos⟩
  let α : ℝ := hM.eigenvalues rfl iTop
  let β : ℝ := -‖M.toContinuousLinearMap‖
  have hupper : ∀ x : F, RCLike.re ⟪M x, x⟫_𝕜 ≤ α * ‖x‖ ^ 2 :=
    re_inner_le_of_eigenvalues_le hM fun i =>
      hM.eigenvalues_antitone rfl (Fin.zero_le i)
  have hlowerSpec : ∀ lam, lam ∈ restrictedPointSpectrum M ⊤ → β ≤ lam := by
    intro lam hlam
    rcases mem_restrictedPointSpectrum_iff.mp hlam with ⟨x, -, hx0, hxEig⟩
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hbound := M.toContinuousLinearMap.le_opNorm x
    change ‖M x‖ ≤ ‖M.toContinuousLinearMap‖ * ‖x‖ at hbound
    rw [hxEig, norm_smul, RCLike.norm_ofReal] at hbound
    -- cancel the strictly positive norm factor before comparing
    have habs : |lam| ≤ ‖M.toContinuousLinearMap‖ :=
      le_of_mul_le_mul_right hbound hxnorm
    dsimp [β]
    linarith [neg_abs_le lam]
  have hβα : β ≤ α :=
    hlowerSpec α (eigenvalue_mem_restrictedPointSpectrum_top hM iTop)
  have hMspec : PointSpectrumIn M ⊤ (Set.Icc β α) := by
    intro lam hlam
    rcases mem_restrictedPointSpectrum_iff.mp hlam with ⟨x, hxTop, hx0, hxEig⟩
    have hxnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
    have hray : RCLike.re ⟪M x, x⟫_𝕜 = lam * ‖x‖ ^ 2 := by
      rw [hxEig, inner_smul_left, RCLike.conj_ofReal,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    have hu := hupper x
    rw [hray] at hu
    exact ⟨hlowerSpec lam (mem_restrictedPointSpectrum hxTop hx0 hxEig), by nlinarith⟩
  have hAspec : PointSpectrumIn A Uᗮ (Set.Ici (α + δ)) := by
    intro μ hμ
    exact hgap α μ
      (eigenvalue_mem_restrictedPointSpectrum_top hM iTop) hμ
  exact ⟨β, α, hβα, hMspec, hAspec⟩

/-- An ordered Ritz-to-unwanted-spectrum gap forces transversality. -/
theorem isTransverse_of_orderedRitzGap
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    IsTransverse (approximateSubspace X) U := by
  rcases subsingleton_or_nontrivial F with _ | _
  · intro x hx hPx
    rcases hx with ⟨y, rfl⟩
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  · obtain ⟨β, α, hβα, hMspec, hAspec⟩ :=
      exists_intervalGap_of_orderedGap hM hgap
    subst M
    exact isTransverse_of_tanThetaIntervalGap hA hU X hδ
      ⟨hMspec, hAspec⟩

/-- Ordered-gap residual `tan Θ` theorem for the canonical coordinate tangent,
in every rectangular unitarily invariant norm. -/
theorem tanThetaEmbedding_residual_le_of_orderedGap
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (tanThetaEmbedding U X) ≤ N (residual A X M) := by
  rcases subsingleton_or_nontrivial F with _ | _
  · have hT : tanThetaEmbedding U X = 0 := by
      ext x
      -- `F` is the subsingleton here, not `E`
      have hx : x = 0 := Subsingleton.elim _ _
      simp [hx]
    rw [hT, N.apply_zero, mul_zero]
    exact N.nonneg _
  · obtain ⟨β, α, hβα, hMspec, hAspec⟩ :=
      exists_intervalGap_of_orderedGap hM hgap
    have htrans := isTransverse_of_orderedRitzGap
      hA hU X hM hGalerkin hδ hgap
    have htan := singularValues_tanThetaEmbedding U X htrans
    subst M
    simpa [ritzResidual] using
      tanTheta0_ritzResidual_le N hA hU X hβα hδ
        ⟨hMspec, hAspec⟩ (tanThetaEmbedding U X) htan


/-- The graph operator from trial coordinates to the complementary exact
subspace.  It is the totalized coordinate tangent `S |C|⁺`. -/
noncomputable def graphOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  tanThetaEmbedding U X

/-- The public graph name agrees definitionally with the coordinate tangent. -/
theorem graphOperator_eq_tanThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (_htrans : IsTransverse (approximateSubspace X) U) :
    graphOperator U X = tanThetaEmbedding U X :=
  rfl

/-- The graph operator has the directed principal-tangent singular values. -/
theorem singularValues_graphOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverse (approximateSubspace X) U) :
    (graphOperator U X).singularValues =
      principalTangents (approximateSubspace X) U := by
  simpa [graphOperator] using singularValues_tanThetaEmbedding U X htrans

/-- **Davis--Kahan `tan Θ`, ordered residual form, every UI norm.** -/
theorem tanTheta_residual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (tanThetaEmbedding U X) ≤ N (residual A X M) :=
  tanThetaEmbedding_residual_le_of_orderedGap
    N hA hU X hM hGalerkin hδ hgap

/-- The ordered residual hypotheses force transversality, so the coordinate
tangent has no pole. -/
theorem isTransverse_of_tanTheta_residual_gap
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    IsTransverse (approximateSubspace X) U :=
  isTransverse_of_orderedRitzGap
    hA hU X hM hGalerkin hδ hgap

/-- Pole-free pointwise residual form.  Unlike the historical proof, this is
obtained from the canonical operator-norm residual theorem and the exact
factorization `S = (S |C|⁺) |C|`; no normalization of the input vector is
silently assumed. -/
theorem tanTheta_vector_le
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ ρ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap M ⊤ A Uᗮ δ)
    (hres : ∀ y, ‖residual A X M y‖ ≤ ρ * ‖y‖) :
    ∀ y, δ * ‖sinThetaEmbedding U X y‖ ≤
      ρ * ‖cosThetaEmbedding U X y‖ := by
  rcases subsingleton_or_nontrivial F with _ | _
  · intro y
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  · have hρ : 0 ≤ ρ := by
      obtain ⟨y, hy⟩ := exists_ne (0 : F)
      have hyNorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hyr := hres y
      nlinarith [norm_nonneg (residual A X M y)]
    have htrans := isTransverse_of_tanTheta_residual_gap
      hA hU X hM hGalerkin hδ hgap
    have hCinj : Function.Injective (cosThetaMagnitude U X) :=
      cosThetaMagnitude_injective U X
        (LinearMap.ker_eq_bot.mp ((tanThetaEmbedding_defined_iff U X).mp htrans))
    have hleft :=
      TauCeti.moorePenroseInverse_comp_eq_id_of_injective
        (cosThetaMagnitude U X) hCinj
    have hfactor :
        tanThetaEmbedding U X ∘ₗ cosThetaMagnitude U X =
          sinThetaEmbedding U X := by
      -- the goal is already left-associated, so `comp_assoc` applies forwards
      rw [tanThetaEmbedding, LinearMap.comp_assoc, hleft]
      ext y
      simp
    have hRop :
        ‖(residual A X M).toContinuousLinearMap‖ ≤ ρ :=
      (residual A X M).toContinuousLinearMap.opNorm_le_bound hρ hres
    have hTop := tanTheta_residual_le
      (UnitarilyInvariantSeminorm.opNorm (𝕜 := 𝕜) (E := F) (F := E))
      hA hU X hM hGalerkin hδ hgap
    have hTbound :
        δ * ‖(tanThetaEmbedding U X).toContinuousLinearMap‖ ≤ ρ := by
      simpa [UnitarilyInvariantSeminorm.opNorm_apply] using
        hTop.trans hRop
    intro y
    have hSy := LinearMap.congr_fun hfactor y
    change tanThetaEmbedding U X (cosThetaMagnitude U X y) =
      sinThetaEmbedding U X y at hSy
    calc
      δ * ‖sinThetaEmbedding U X y‖ =
          δ * ‖tanThetaEmbedding U X (cosThetaMagnitude U X y)‖ := by rw [hSy]
      _ ≤ δ *
          (‖(tanThetaEmbedding U X).toContinuousLinearMap‖ *
            ‖cosThetaMagnitude U X y‖) := by
          gcongr
          exact (tanThetaEmbedding U X).toContinuousLinearMap.le_opNorm _
      _ = (δ * ‖(tanThetaEmbedding U X).toContinuousLinearMap‖) *
          ‖cosThetaMagnitude U X y‖ := by ring
      _ ≤ ρ * ‖cosThetaMagnitude U X y‖ :=
        mul_le_mul_of_nonneg_right hTbound (norm_nonneg _)
      _ = ρ * ‖cosThetaEmbedding U X y‖ := by
        rw [cosThetaMagnitude, norm_trialGramSqrt_apply]

end DavisKahan.FiniteDimensional
end TauCeti
