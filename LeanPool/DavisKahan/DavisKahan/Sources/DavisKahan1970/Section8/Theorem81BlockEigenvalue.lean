/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81EigenvalueSource
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.PrescribedSequence

/-!
# Theorem 8.1 (ii) and (iii) on the blocks themselves

Davis and Kahan index parts (ii) and (iii) by the ordered eigenvalues of the
*blocks*: `α_k` are the eigenvalues of `A₁`, `λ_k` those of `Λ₁`, and part
(iii)'s symmetric gauge acts on `n` numbers where `n` is the block dimension.
`upperBlockShift` and `lowerBlockShift` are those blocks **extended by zero to
the ambient space**, so their eigenvalue lists are the printed ones followed by
zeros and a gauge on them is quantified at `finrank H`.  That is a different
public object.

This module carries the blocks as operators on their own spaces and the three
facts that put the printed statements on them.

* `upperBlockCompression`, `lowerBlockCompression` — `A₁ − α` on `Pᗮ` and
  `(α + δ) − A₀` on `P`, as operators there.
* `approximationNumber_upperBlockCompression` — extending by zero does not move
  an approximation number, so the ambient estimates transfer verbatim.
* `finrank_orthogonal_eq_of_isAcute` — the two blocks live on *different* spaces
  `Pᗮ` and `Qᗮ`, and naming the right-hand list at the left-hand indices needs
  their dimensions to agree.  They do: Theorem 8.1's own conclusion puts the
  projection gap strictly inside the quarter turn, which is acuteness, which is
  injectivity of each projection on the other subspace in both directions.
-/

@[expose] public section

open TauCeti.DavisKahan.Angle

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open scoped InnerProductSpace
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Sylvester
open Module (finrank)
open scoped TauCeti.CompleteSubspace

noncomputable section

universe u

/-! ### The blocks on their own spaces -/

section Blocks

variable {𝕜 : Type*} [RCLike 𝕜] {G : Type u} [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- Extending a compression by zero and reading it on the ambient space is
conjugation by the orthogonal projection. -/
theorem subtypeL_comp_compressOperator_comp_orthogonalProjectionOnto
    (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] (T : G →L[𝕜] G) :
    U.subtypeL ∘L compressOperator U T ∘L U.orthogonalProjectionOnto =
      U.starProjection ∘L T ∘L U.starProjection :=
  rfl

/-- **`A₁ − α`, on `Pᗮ` itself.**  This is the operator whose ordered
eigenvalues Davis and Kahan write `α_k`. -/
def upperBlockCompression (A : G →L[𝕜] G) (P : Submodule 𝕜 G)
    [P.HasOrthogonalProjection] (alpha : ℝ) :
    (Pᗮ : Submodule 𝕜 G) →L[𝕜] (Pᗮ : Submodule 𝕜 G) :=
  compressOperator Pᗮ (upperBlockShift A P alpha)

/-- **`(α + δ) − A₀`, on `P` itself.** -/
def lowerBlockCompression (A : G →L[𝕜] G) (P : Submodule 𝕜 G)
    [P.HasOrthogonalProjection] (alpha delta : ℝ) :
    (P : Submodule 𝕜 G) →L[𝕜] (P : Submodule 𝕜 G) :=
  compressOperator P (lowerBlockShift A P alpha delta)

omit [CompleteSpace G] in
/-- The ambient upper block is its own compression extended by zero. -/
theorem subtypeL_comp_upperBlockCompression (A : G →L[𝕜] G) (P : Submodule 𝕜 G)
    [P.HasOrthogonalProjection] (alpha : ℝ) :
    Pᗮ.subtypeL ∘L upperBlockCompression A P alpha ∘L Pᗮ.orthogonalProjectionOnto =
      upperBlockShift A P alpha := by
  rw [upperBlockCompression, subtypeL_comp_compressOperator_comp_orthogonalProjectionOnto,
    upperBlockShift]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply]
  rw [Submodule.starProjection_eq_self_iff.mpr (Pᗮ.starProjection_apply_mem x),
    Submodule.starProjection_eq_self_iff.mpr (Pᗮ.starProjection_apply_mem _)]

omit [CompleteSpace G] in
/-- The ambient lower block is its own compression extended by zero. -/
theorem subtypeL_comp_lowerBlockCompression (A : G →L[𝕜] G) (P : Submodule 𝕜 G)
    [P.HasOrthogonalProjection] (alpha delta : ℝ) :
    P.subtypeL ∘L lowerBlockCompression A P alpha delta ∘L P.orthogonalProjectionOnto =
      lowerBlockShift A P alpha delta := by
  rw [lowerBlockCompression, subtypeL_comp_compressOperator_comp_orthogonalProjectionOnto,
    lowerBlockShift]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply]
  rw [Submodule.starProjection_eq_self_iff.mpr (P.starProjection_apply_mem x),
    Submodule.starProjection_eq_self_iff.mpr (P.starProjection_apply_mem _)]

omit [CompleteSpace G] in
/-- **Extending by zero moves no approximation number**, so every estimate the
ambient development proves about `upperBlockShift` is an estimate about the
block. -/
theorem approximationNumber_upperBlockCompression (A : G →L[𝕜] G) (P : Submodule 𝕜 G)
    [P.HasOrthogonalProjection] (alpha : ℝ) (n : ℕ) :
    (upperBlockCompression A P alpha).approximationNumber n =
      (upperBlockShift A P alpha).approximationNumber n := by
  rw [← subtypeL_comp_upperBlockCompression A P alpha,
    ApproximationNumber.approximationNumber_subtypeL_comp_comp_orthogonalProjectionOnto]

omit [CompleteSpace G] in
/-- The lower block's approximation numbers, likewise. -/
theorem approximationNumber_lowerBlockCompression (A : G →L[𝕜] G) (P : Submodule 𝕜 G)
    [P.HasOrthogonalProjection] (alpha delta : ℝ) (n : ℕ) :
    (lowerBlockCompression A P alpha delta).approximationNumber n =
      (lowerBlockShift A P alpha delta).approximationNumber n := by
  rw [← subtypeL_comp_lowerBlockCompression A P alpha delta,
    ApproximationNumber.approximationNumber_subtypeL_comp_comp_orthogonalProjectionOnto]

/-- The compression of a nonnegative ambient operator is nonnegative on the
subspace: its quadratic form on `U` is the ambient form restricted. -/
theorem nonneg_compressOperator_of_nonneg {T : G →L[𝕜] G}
    (hT : (0 : G →L[𝕜] G) ≤ T) (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] :
    (0 : U →L[𝕜] U) ≤ compressOperator U T := by
  have : CompleteSpace U :=
    (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe
  have hTpos := (ContinuousLinearMap.nonneg_iff_isPositive (f := T)).mp hT
  refine (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr
    (ContinuousLinearMap.isPositive_def'.mpr
      ⟨isSelfAdjoint_compressOperator hTpos.isSelfAdjoint U, fun x => ?_⟩)
  have hcoe : ((compressOperator U T x : U) : G) = U.starProjection (T (x : G)) := rfl
  have hval : ⟪((compressOperator U T x : U) : G), (x : G)⟫_𝕜 = ⟪T (x : G), (x : G)⟫_𝕜 := by
    rw [hcoe, Submodule.inner_starProjection_left_eq_right U,
      Submodule.starProjection_eq_self_iff.mpr x.2]
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, Submodule.coe_inner, hval]
  exact hTpos.2 (x : G)

/-- **`A₁ − α` is symmetric on `Pᗮ`.** -/
theorem isSymmetric_upperBlockCompression {A : G →L[𝕜] G} (hA : IsSelfAdjoint A)
    (P : Submodule 𝕜 G) [P.HasOrthogonalProjection] (alpha : ℝ) :
    ((upperBlockCompression A P alpha :
      (Pᗮ : Submodule 𝕜 G) →L[𝕜] (Pᗮ : Submodule 𝕜 G)) :
        (Pᗮ : Submodule 𝕜 G) →ₗ[𝕜] (Pᗮ : Submodule 𝕜 G)).IsSymmetric :=
  (isSelfAdjoint_compressOperator
    (upperBlockShift_isSelfAdjoint A P alpha hA) Pᗮ).isSymmetric

/-- **`(α + δ) − A₀` is symmetric on `P`.** -/
theorem isSymmetric_lowerBlockCompression {A : G →L[𝕜] G} (hA : IsSelfAdjoint A)
    (P : Submodule 𝕜 G) [P.HasOrthogonalProjection] (alpha delta : ℝ) :
    ((lowerBlockCompression A P alpha delta :
      (P : Submodule 𝕜 G) →L[𝕜] (P : Submodule 𝕜 G)) :
        (P : Submodule 𝕜 G) →ₗ[𝕜] (P : Submodule 𝕜 G)).IsSymmetric :=
  (isSelfAdjoint_compressOperator
    (lowerBlockShift_isSelfAdjoint A P alpha delta hA) P).isSymmetric

/-- **The upper block's approximation numbers are its ordered eigenvalues.**
Stated on `upperBlockCompression` so that the subspace's normed-space instances
are fixed once here rather than at every call site. -/
theorem approximationNumber_upperBlockCompression_eq_eigenvalues [FiniteDimensional 𝕜 G]
    {A : G →L[𝕜] G} (hA : IsSelfAdjoint A) (P : Submodule 𝕜 G)
    [P.HasOrthogonalProjection] (alpha : ℝ)
    (hnn : (0 : G →L[𝕜] G) ≤ upperBlockShift A P alpha)
    (i : Fin (finrank 𝕜 (Pᗮ : Submodule 𝕜 G))) :
    (upperBlockCompression A P alpha).approximationNumber (i : ℕ)
      = (isSymmetric_upperBlockCompression hA P alpha).eigenvalues rfl i :=
  approximationNumber_eq_eigenvalues_of_isPositive
    (isPositive_toLinearMap_of_nonneg (nonneg_compressOperator_of_nonneg hnn Pᗮ)) i

/-- **The lower block's approximation numbers are its ordered eigenvalues.** -/
theorem approximationNumber_lowerBlockCompression_eq_eigenvalues [FiniteDimensional 𝕜 G]
    {A : G →L[𝕜] G} (hA : IsSelfAdjoint A) (P : Submodule 𝕜 G)
    [P.HasOrthogonalProjection] (alpha delta : ℝ)
    (hnn : (0 : G →L[𝕜] G) ≤ lowerBlockShift A P alpha delta)
    (i : Fin (finrank 𝕜 (P : Submodule 𝕜 G))) :
    (lowerBlockCompression A P alpha delta).approximationNumber (i : ℕ)
      = (isSymmetric_lowerBlockCompression hA P alpha delta).eigenvalues rfl i :=
  approximationNumber_eq_eigenvalues_of_isPositive
    (isPositive_toLinearMap_of_nonneg (nonneg_compressOperator_of_nonneg hnn P)) i

end Blocks

/-! ### The two blocks have the same dimension

`A₁` lives on `Pᗮ` and `Λ₁` on `Qᗮ`, so the printed inequality `α_k ≤ ‖C₁‖² λ_k`
only names both lists if the two block dimensions agree.  They do, and Theorem
8.1's own conclusion is what says so: it puts the projection gap strictly inside
the quarter turn, which is acuteness, which is injectivity of each projection on
the other subspace in both directions. -/

section Dimension

variable {𝕜 : Type*} [RCLike 𝕜] {G : Type u} [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 G] [CompleteSpace G] [FiniteDimensional 𝕜 G]

omit [CompleteSpace G] in
/-- Half of the dimension comparison: if `P_V` is injective on `U` then `U` is no
bigger than `V`. -/
theorem finrank_le_finrank_of_isTransverse {U V : Submodule 𝕜 G}
     [V.HasOrthogonalProjection]
    (h : ∀ x ∈ U, V.starProjection x = 0 → x = 0) :
    finrank 𝕜 U ≤ finrank 𝕜 V := by
  have hinj : Function.Injective
      ((V.orthogonalProjectionOnto ∘L U.subtypeL : U →L[𝕜] V) : U →ₗ[𝕜] V) := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
    have hx0 : V.starProjection (x : G) = 0 := by
      have : (V.orthogonalProjectionOnto ((x : G)) : V) = 0 := hx
      exact congrArg Subtype.val this
    exact Subtype.ext (h (x : G) x.2 hx0)
  exact LinearMap.finrank_le_finrank_of_injective hinj

omit [CompleteSpace G] in
/-- **An acute pair has equal dimension.** -/
theorem finrank_eq_of_isAcute {U V : Submodule 𝕜 G}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : TauCeti.IsAcute U V) :
    finrank 𝕜 U = finrank 𝕜 V :=
  le_antisymm (finrank_le_finrank_of_isTransverse h.1)
    (finrank_le_finrank_of_isTransverse h.2)

omit [CompleteSpace G] in
/-- **An acute pair's complements have equal dimension**, which is what parts
(ii) and (iii) need: `A₁` is read on `Pᗮ` and `Λ₁` on `Qᗮ`. -/
theorem finrank_orthogonal_eq_of_isAcute {U V : Submodule 𝕜 G}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : TauCeti.IsAcute U V) :
    finrank 𝕜 (Uᗮ : Submodule 𝕜 G) = finrank 𝕜 (Vᗮ : Submodule 𝕜 G) := by
  have hU := Submodule.finrank_add_finrank_orthogonal (𝕜 := 𝕜) (K := U)
  have hV := Submodule.finrank_add_finrank_orthogonal (𝕜 := 𝕜) (K := V)
  have := finrank_eq_of_isAcute h
  omega

omit [CompleteSpace G] [FiniteDimensional 𝕜 G] in
/-- The Theorem 8.1 conclusion's quarter-acute clause is acuteness. -/
theorem isAcute_of_isQuarterAcute {U V : Submodule 𝕜 G}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : DavisKahan.IsQuarterAcute U V) : TauCeti.IsAcute U V := by
  refine TauCeti.isAcute_of_projectionGap_lt_one (lt_of_lt_of_le h ?_)
  have h2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  linarith

end Dimension

/-! ### Restricting a weak majorization to a smaller index set

Parts (ii) and (iii) are proved at the ambient dimension.  The block sequences
are the ambient ones read on the first `finrank Pᗮ` indices, and a weak
majorization restricts to an initial segment: the prefix sums agree below the
cut, and above it the block's prefix sum is the ambient one at the cut. -/

section Restriction

open FiniteVector

/-- Prefix sums of a restricted vector are prefix sums of the original, at the
truncated cut. -/
theorem prefixSum_comp_castLE {N n : ℕ} (h : n ≤ N) (x : Fin N → ℝ) (k : ℕ) :
    prefixSum k (fun i : Fin n => x (Fin.castLE h i)) = prefixSum (min k n) x := by
  classical
  have hmap : (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)).map (Fin.castLEEmb h)
      = Finset.univ.filter (fun j : Fin N => (j : ℕ) < min k n) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.castLEEmb_apply, lt_min_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hi, i.isLt⟩
    · rintro ⟨hk, hn⟩
      exact ⟨⟨(j : ℕ), hn⟩, hk, Fin.ext rfl⟩
  rw [prefixSum, prefixSum, ← hmap, Finset.sum_map]
  rfl

/-- **A weak majorization restricts to an initial segment of the indices.** -/
theorem weaklyMajorized_comp_castLE {N n : ℕ} (h : n ≤ N) {x y : Fin N → ℝ}
    (hxy : WeaklyMajorized x y) :
    WeaklyMajorized (fun i : Fin n => x (Fin.castLE h i))
      (fun i : Fin n => y (Fin.castLE h i)) where
  left_antitone := fun _ _ hab => hxy.left_antitone (by exact hab)
  right_antitone := fun _ _ hab => hxy.right_antitone (by exact hab)
  left_nonneg := fun i => hxy.left_nonneg _
  right_nonneg := fun i => hxy.right_nonneg _
  prefix_le := fun k => by
    rw [prefixSum_comp_castLE, prefixSum_comp_castLE]
    exact hxy.prefix_le _

end Restriction

/-! ### Parts (ii) and (iii) on the block eigenvalue lists, over `ℂ` -/

section Complex

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The branch `Q` of Theorem 8.1, named once. -/
abbrev branch (A K : H →L[ℂ] H) (alpha : ℝ) (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K) :
    Submodule ℂ H :=
  canonicalLowBranch (A + K)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha

/-- **The two blocks of Theorem 8.1 have the same dimension.**

`A₁` is read on `Pᗮ` and `Λ₁` on `Qᗮ`, and the printed inequality names both
lists at the same index.  Theorem 8.1's own conclusion supplies the equality:
the branch is strictly inside the quarter turn, hence acute. -/
theorem theorem8_1_finrank_orthogonal_branch_eq [FiniteDimensional ℂ H]
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    finrank ℂ (Pᗮ : Submodule ℂ H)
      = finrank ℂ ((branch A K alpha hA hK)ᗮ : Submodule ℂ H) :=
  finrank_orthogonal_eq_of_isAcute (isAcute_of_isQuarterAcute
    (theorem8_1_canonicalBranch (A := A) (H := K) (P := P) (alpha := alpha)
      (delta := delta) hdelta hA hK hAP hPlow hPhigh hKP hKPperp).quarter_acute)

/-- **The branches of Theorem 8.1 have the same dimension**, the form parts (ii)
and (iii) need for the lower block. -/
theorem theorem8_1_finrank_branch_eq [FiniteDimensional ℂ H]
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    finrank ℂ (P : Submodule ℂ H) = finrank ℂ (branch A K alpha hA hK) :=
  finrank_eq_of_isAcute (isAcute_of_isQuarterAcute
    (theorem8_1_canonicalBranch (A := A) (H := K) (P := P) (alpha := alpha)
      (delta := delta) hdelta hA hK hAP hPlow hPhigh hKP hKPperp).quarter_acute)

/-! ### Part (ii) on the printed block eigenvalue lists -/

variable (A K : H →L[ℂ] H) (P : Submodule ℂ H)
/-- **Davis--Kahan 1970, Theorem 8.1 (ii), upper block, on the printed block
eigenvalue lists.**

`α_k − α ≤ ‖C₁‖₁² (λ_k − α)`, where `α_k` are the ordered eigenvalues of `A₁`
*on `Pᗮ`* and `λ_k` those of `Λ₁` *on `Qᗮ`* — not of those operators extended by
zero to the ambient space, whose lists are these followed by zeros.  The index
runs over the block dimension, and the two blocks have the same dimension by
`theorem8_1_finrank_orthogonal_branch_eq`, which is Theorem 8.1's own acuteness
conclusion. -/
theorem theorem8_1_upperEigenvalueRepulsion_blockSourceExact [FiniteDimensional ℂ H]
    [P.HasOrthogonalProjection] {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (i : Fin (finrank ℂ (Pᗮ : Submodule ℂ H))) :
    (isSymmetric_upperBlockCompression hA P alpha).eigenvalues rfl i ≤
      TauCeti.principalCosines Pᗮ (branch A K alpha hA hK)ᗮ 0 ^ 2 *
        (isSymmetric_upperBlockCompression (hA.add hK)
            (branch A K alpha hA hK) alpha).eigenvalues rfl
          (Fin.cast (theorem8_1_finrank_orthogonal_branch_eq A K P hdelta hA hK hAP
            hPlow hPhigh hKP hKPperp) i) := by
  have heigA := approximationNumber_upperBlockCompression_eq_eigenvalues hA P alpha
    (upperBlockShift_nonneg A P hdelta.le hA hPhigh) i
  have heigQ := approximationNumber_upperBlockCompression_eq_eigenvalues (hA.add hK)
    (branch A K alpha hA hK) alpha
    (theorem8_1_perturbedUpperBlockShift_nonneg A K P hdelta hA hK hAP hPlow
      hPhigh hKP hKPperp)
    (Fin.cast (theorem8_1_finrank_orthogonal_branch_eq A K P hdelta hA hK hAP
      hPlow hPhigh hKP hKPperp) i)
  simp only [Fin.val_cast] at heigQ
  have h := theorem8_1_upperApproximationRepulsion_angle A K P hdelta hA hK hAP
    hPlow hPhigh hKP hKPperp (i : ℕ)
  rw [← approximationNumber_upperBlockCompression A P alpha,
    ← approximationNumber_upperBlockCompression (A + K) (branch A K alpha hA hK) alpha,
    heigA, heigQ] at h
  exact h
/-- **Davis--Kahan 1970, Theorem 8.1 (ii), lower block, on the printed block
eigenvalue lists.** -/
theorem theorem8_1_lowerEigenvalueRepulsion_blockSourceExact [FiniteDimensional ℂ H]
    [P.HasOrthogonalProjection] {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (i : Fin (finrank ℂ (P : Submodule ℂ H))) :
    (isSymmetric_lowerBlockCompression hA P alpha delta).eigenvalues rfl i ≤
      TauCeti.principalCosines P (branch A K alpha hA hK) 0 ^ 2 *
        (isSymmetric_lowerBlockCompression (hA.add hK)
            (branch A K alpha hA hK) alpha delta).eigenvalues rfl
          (Fin.cast (theorem8_1_finrank_branch_eq A K P hdelta hA hK hAP
            hPlow hPhigh hKP hKPperp) i) := by
  have heigA := approximationNumber_lowerBlockCompression_eq_eigenvalues hA P alpha delta
    (lowerBlockShift_nonneg A P hdelta.le hA hPlow) i
  have heigQ := approximationNumber_lowerBlockCompression_eq_eigenvalues (hA.add hK)
    (branch A K alpha hA hK) alpha delta
    (theorem8_1_perturbedLowerBlockShift_nonneg A K P hdelta hA hK hAP hPlow
      hPhigh hKP hKPperp)
    (Fin.cast (theorem8_1_finrank_branch_eq A K P hdelta hA hK hAP
      hPlow hPhigh hKP hKPperp) i)
  simp only [Fin.val_cast] at heigQ
  have h := theorem8_1_lowerApproximationRepulsion_angle A K P hdelta hA hK hAP
    hPlow hPhigh hKP hKPperp (i : ℕ)
  rw [← approximationNumber_lowerBlockCompression A P alpha delta,
    ← approximationNumber_lowerBlockCompression (A + K) (branch A K alpha hA hK) alpha delta,
    heigA, heigQ] at h
  exact h

/-! ### Part (iii) with the gauge at the block dimension -/
/-- **Davis--Kahan 1970, Theorem 8.1 (iii), upper block, with the symmetric gauge
at the block dimension.**

`Φ(α₁ − α, …, α_n − α) ≤ Φ((λ₁ − α)cos²θ₁, …, (λ_n − α)cos²θ_n)` where `n` is the
dimension of the block `Pᗮ` — the number of eigenvalues `A₁` has — and not the
ambient dimension.  The majorization the proof runs on is established at the
ambient dimension and restricted here, which is legitimate because the block
sequences are the ambient ones on an initial segment of indices. -/
theorem theorem8_1_upperSymmetricGaugeEigenvalue_blockSourceExact [FiniteDimensional ℂ H]
    [P.HasOrthogonalProjection] {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (Phi : FiniteSymmetricGauge (finrank ℂ (Pᗮ : Submodule ℂ H))) :
    Phi (fun i => (isSymmetric_upperBlockCompression hA P alpha).eigenvalues rfl i)
      ≤ Phi (fun i =>
        (isSymmetric_upperBlockCompression (hA.add hK)
            (branch A K alpha hA hK) alpha).eigenvalues rfl
          (Fin.cast (theorem8_1_finrank_orthogonal_branch_eq A K P hdelta hA hK hAP
            hPlow hPhigh hKP hKPperp) i) *
          TauCeti.principalCosines Pᗮ (branch A K alpha hA hK)ᗮ (i : ℕ) ^ 2) := by
  have hle : finrank ℂ (Pᗮ : Submodule ℂ H) ≤ finrank ℂ H := Submodule.finrank_le _
  have hmaj := theorem8_1_upperWeightedWeakMajorization A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp
  have hgauge := Phi.mono_weaklyMajorized (weaklyMajorized_comp_castLE hle hmaj)
  simp only [Fin.val_castLE] at hgauge
  have hfA : (fun i : Fin (finrank ℂ (Pᗮ : Submodule ℂ H)) =>
      (upperBlockShift A P alpha).approximationNumber (i : ℕ))
      = fun i => (isSymmetric_upperBlockCompression hA P alpha).eigenvalues rfl i := by
    funext i
    rw [← approximationNumber_upperBlockCompression A P alpha]
    exact approximationNumber_upperBlockCompression_eq_eigenvalues hA P alpha
      (upperBlockShift_nonneg A P hdelta.le hA hPhigh) i
  have hfQ : (fun i : Fin (finrank ℂ (Pᗮ : Submodule ℂ H)) =>
      (upperBlockShift (A + K) (branch A K alpha hA hK) alpha).approximationNumber (i : ℕ) *
        (cosineBlock P (branch A K alpha hA hK)).approximationNumber (i : ℕ) ^ 2)
      = fun i => (isSymmetric_upperBlockCompression (hA.add hK)
            (branch A K alpha hA hK) alpha).eigenvalues rfl
          (Fin.cast (theorem8_1_finrank_orthogonal_branch_eq A K P hdelta hA hK hAP
            hPlow hPhigh hKP hKPperp) i) *
          TauCeti.principalCosines Pᗮ (branch A K alpha hA hK)ᗮ (i : ℕ) ^ 2 := by
    funext i
    have heigQ := approximationNumber_upperBlockCompression_eq_eigenvalues (hA.add hK)
      (branch A K alpha hA hK) alpha
      (theorem8_1_perturbedUpperBlockShift_nonneg A K P hdelta hA hK hAP hPlow
        hPhigh hKP hKPperp)
      (Fin.cast (theorem8_1_finrank_orthogonal_branch_eq A K P hdelta hA hK hAP
        hPlow hPhigh hKP hKPperp) i)
    simp only [Fin.val_cast] at heigQ
    rw [← approximationNumber_upperBlockCompression (A + K) (branch A K alpha hA hK) alpha,
      heigQ, approximationNumber_cosineBlock_eq_principalCosines]
  exact (congrArg (fun f => Phi f) hfA.symm).trans_le
    (hgauge.trans_eq (congrArg (fun f => Phi f) hfQ))
/-- **Davis--Kahan 1970, Theorem 8.1 (iii), lower block, with the symmetric gauge
at the block dimension.** -/
theorem theorem8_1_lowerSymmetricGaugeEigenvalue_blockSourceExact [FiniteDimensional ℂ H]
    [P.HasOrthogonalProjection] {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (Phi : FiniteSymmetricGauge (finrank ℂ (P : Submodule ℂ H))) :
    Phi (fun i => (isSymmetric_lowerBlockCompression hA P alpha delta).eigenvalues rfl i)
      ≤ Phi (fun i =>
        (isSymmetric_lowerBlockCompression (hA.add hK)
            (branch A K alpha hA hK) alpha delta).eigenvalues rfl
          (Fin.cast (theorem8_1_finrank_branch_eq A K P hdelta hA hK hAP
            hPlow hPhigh hKP hKPperp) i) *
          TauCeti.principalCosines P (branch A K alpha hA hK) (i : ℕ) ^ 2) := by
  have hle : finrank ℂ (P : Submodule ℂ H) ≤ finrank ℂ H := Submodule.finrank_le _
  have hmaj := theorem8_1_lowerWeightedWeakMajorization A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp
  have hgauge := Phi.mono_weaklyMajorized (weaklyMajorized_comp_castLE hle hmaj)
  simp only [Fin.val_castLE] at hgauge
  have hfA : (fun i : Fin (finrank ℂ (P : Submodule ℂ H)) =>
      (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ))
      = fun i => (isSymmetric_lowerBlockCompression hA P alpha delta).eigenvalues rfl i := by
    funext i
    rw [← approximationNumber_lowerBlockCompression A P alpha delta]
    exact approximationNumber_lowerBlockCompression_eq_eigenvalues hA P alpha delta
      (lowerBlockShift_nonneg A P hdelta.le hA hPlow) i
  have hfQ : (fun i : Fin (finrank ℂ (P : Submodule ℂ H)) =>
      (lowerBlockShift (A + K) (branch A K alpha hA hK) alpha delta
        ).approximationNumber (i : ℕ) *
        (lowerCosineBlock P (branch A K alpha hA hK)).approximationNumber (i : ℕ) ^ 2)
      = fun i => (isSymmetric_lowerBlockCompression (hA.add hK)
            (branch A K alpha hA hK) alpha delta).eigenvalues rfl
          (Fin.cast (theorem8_1_finrank_branch_eq A K P hdelta hA hK hAP
            hPlow hPhigh hKP hKPperp) i) *
          TauCeti.principalCosines P (branch A K alpha hA hK) (i : ℕ) ^ 2 := by
    funext i
    have heigQ := approximationNumber_lowerBlockCompression_eq_eigenvalues (hA.add hK)
      (branch A K alpha hA hK) alpha delta
      (theorem8_1_perturbedLowerBlockShift_nonneg A K P hdelta hA hK hAP hPlow
        hPhigh hKP hKPperp)
      (Fin.cast (theorem8_1_finrank_branch_eq A K P hdelta hA hK hAP
        hPlow hPhigh hKP hKPperp) i)
    simp only [Fin.val_cast] at heigQ
    rw [← approximationNumber_lowerBlockCompression (A + K) (branch A K alpha hA hK)
      alpha delta, heigQ, approximationNumber_lowerCosineBlock_eq_principalCosines]
  exact (congrArg (fun f => Phi f) hfA.symm).trans_le
    (hgauge.trans_eq (congrArg (fun f => Phi f) hfQ))

end Complex

/-! ### Parts (ii) and (iii) on the block eigenvalue lists, over `ℝ` -/

section Real

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (A K : E →L[ℝ] E) (P : Submodule ℝ E)

/-- **The two blocks of Theorem 8.1 have the same dimension**, over `ℝ`.

The gap is unchanged by complexification and the real branch is the descent of
the complex one, so the complex quarter-acute conclusion transfers verbatim. -/
theorem theorem8_1_isAcute_branch_real [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    DavisKahan.IsQuarterAcute P
      (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp) := by
  have hAc : IsSelfAdjoint (RealComplexification.complexify A) :=
    (RealComplexification.complexify_isSelfAdjoint_iff A).2 hA
  have hKc : IsSelfAdjoint (RealComplexification.complexify K) :=
    (RealComplexification.complexify_isSelfAdjoint_iff K).2 hK
  have key : ∀ (Qc : Submodule ℂ (RealComplexification E)) [Qc.HasOrthogonalProjection],
      Qc = canonicalLowBranch (RealComplexification.complexify A +
            RealComplexification.complexify K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hAc.add hKc)) alpha →
      Submodule.projectionGap
          (Foundation.RealComplexification.complexifySubmodule P) Qc <
        Real.sqrt 2 / 2 := by
    rintro Qc _ rfl
    exact (theorem8_1_canonicalBranch_complexified A K P hdelta hA hK hAP hPlow
      hPhigh hKP hKPperp).quarter_acute
  have h := key (Foundation.RealComplexification.complexifySubmodule
      (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp))
    (complexifySubmodule_canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
      hPhigh hKP hKPperp)
  rwa [DavisKahan.Foundation.RealComplexification.subspaceGap_complexifySubmodule] at h

/-- The upper blocks' dimensions agree, over `ℝ`. -/
theorem theorem8_1_finrank_orthogonal_branch_eq_real [FiniteDimensional ℝ E]
    [P.HasOrthogonalProjection] {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    finrank ℝ (Pᗮ : Submodule ℝ E)
      = finrank ℝ ((canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
          hKPperp)ᗮ : Submodule ℝ E) :=
  finrank_orthogonal_eq_of_isAcute (isAcute_of_isQuarterAcute
    (theorem8_1_isAcute_branch_real A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp))

/-- The lower blocks' dimensions agree, over `ℝ`. -/
theorem theorem8_1_finrank_branch_eq_real [FiniteDimensional ℝ E]
    [P.HasOrthogonalProjection] {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    finrank ℝ (P : Submodule ℝ E)
      = finrank ℝ (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
          hKPperp) :=
  finrank_eq_of_isAcute (isAcute_of_isQuarterAcute
    (theorem8_1_isAcute_branch_real A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp))
/-- **Theorem 8.1 (ii), upper block, on the printed block eigenvalue lists, over
a real Hilbert space.** -/
theorem theorem8_1_upperEigenvalueRepulsion_blockSourceExact_real [FiniteDimensional ℝ E]
    [P.HasOrthogonalProjection] {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (i : Fin (finrank ℝ (Pᗮ : Submodule ℝ E))) :
    (isSymmetric_upperBlockCompression hA P alpha).eigenvalues rfl i ≤
      TauCeti.principalCosines Pᗮ (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
            hPhigh hKP hKPperp)ᗮ 0 ^ 2 *
        (isSymmetric_upperBlockCompression (hA.add hK) (canonicalLowBranchReal A K P hdelta hA hK
            hAP hPlow
              hPhigh hKP hKPperp) alpha).eigenvalues rfl
          (Fin.cast (theorem8_1_finrank_orthogonal_branch_eq_real A K P hdelta hA hK hAP
              hPlow hPhigh hKP hKPperp) i) := by
  have heigA := approximationNumber_upperBlockCompression_eq_eigenvalues hA P alpha
    (upperBlockShift_nonneg A P hdelta.le hA
      (by simpa only [RCLike.re_to_real] using hPhigh)) i
  have heigQ := approximationNumber_upperBlockCompression_eq_eigenvalues (hA.add hK)
    (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp) alpha
    (theorem8_1_perturbedUpperBlockShift_nonneg_real A K P hdelta hA hK hAP
        hPlow hPhigh hKP hKPperp)
    (Fin.cast (theorem8_1_finrank_orthogonal_branch_eq_real A K P hdelta hA hK hAP
        hPlow hPhigh hKP hKPperp) i)
  simp only [Fin.val_cast] at heigQ
  have h := theorem8_1_upperApproximationRepulsion_angle_real A K P hdelta hA hK hAP
      hPlow hPhigh hKP hKPperp (i : ℕ)
  rw [← approximationNumber_upperBlockCompression A P alpha,
    ← approximationNumber_upperBlockCompression (A + K) (canonicalLowBranchReal A K P hdelta hA hK
        hAP hPlow
          hPhigh hKP hKPperp) alpha,
    heigA, heigQ] at h
  exact h
/-- **Theorem 8.1 (ii), lower block, on the printed block eigenvalue lists, over
a real Hilbert space.** -/
theorem theorem8_1_lowerEigenvalueRepulsion_blockSourceExact_real [FiniteDimensional ℝ E]
    [P.HasOrthogonalProjection] {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (i : Fin (finrank ℝ (P : Submodule ℝ E))) :
    (isSymmetric_lowerBlockCompression hA P alpha delta).eigenvalues rfl i ≤
      TauCeti.principalCosines P (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
            hPhigh hKP hKPperp) 0 ^ 2 *
        (isSymmetric_lowerBlockCompression (hA.add hK) (canonicalLowBranchReal A K P hdelta hA hK
            hAP hPlow
              hPhigh hKP hKPperp) alpha delta).eigenvalues rfl
          (Fin.cast (theorem8_1_finrank_branch_eq_real A K P hdelta hA hK hAP
              hPlow hPhigh hKP hKPperp) i) := by
  have heigA := approximationNumber_lowerBlockCompression_eq_eigenvalues hA P alpha delta
    (lowerBlockShift_nonneg A P hdelta.le hA
      (by simpa only [RCLike.re_to_real] using hPlow)) i
  have heigQ := approximationNumber_lowerBlockCompression_eq_eigenvalues (hA.add hK)
    (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp) alpha delta
    (theorem8_1_perturbedLowerBlockShift_nonneg_real A K P hdelta hA hK hAP
        hPlow hPhigh hKP hKPperp)
    (Fin.cast (theorem8_1_finrank_branch_eq_real A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp) i)
  simp only [Fin.val_cast] at heigQ
  have h := theorem8_1_lowerApproximationRepulsion_angle_real A K P hdelta hA hK hAP
      hPlow hPhigh hKP hKPperp (i : ℕ)
  rw [← approximationNumber_lowerBlockCompression A P alpha delta,
    ← approximationNumber_lowerBlockCompression (A + K) (canonicalLowBranchReal A K P hdelta hA hK
        hAP hPlow
          hPhigh hKP hKPperp) alpha delta,
    heigA, heigQ] at h
  exact h
/-- **Theorem 8.1 (iii), upper block, with the symmetric gauge at the block
dimension, over a real Hilbert space.** -/
theorem theorem8_1_upperSymmetricGaugeEigenvalue_blockSourceExact_real
    [FiniteDimensional ℝ E]
    [P.HasOrthogonalProjection] {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (Phi : FiniteSymmetricGauge (finrank ℝ (Pᗮ : Submodule ℝ E))) :
    Phi (fun i => (isSymmetric_upperBlockCompression hA P alpha).eigenvalues rfl i)
      ≤ Phi (fun i =>
        (isSymmetric_upperBlockCompression (hA.add hK) (canonicalLowBranchReal A K P hdelta hA hK
            hAP hPlow
              hPhigh hKP hKPperp) alpha).eigenvalues rfl
          (Fin.cast (theorem8_1_finrank_orthogonal_branch_eq_real A K P hdelta hA hK hAP
              hPlow hPhigh hKP hKPperp) i) *
          TauCeti.principalCosines Pᗮ (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
                hPhigh hKP hKPperp)ᗮ (i : ℕ) ^ 2) := by
  have hle : finrank ℝ (Pᗮ : Submodule ℝ E) ≤ finrank ℝ E := Submodule.finrank_le _
  have hmaj := theorem8_1_upperWeightedWeakMajorization_real A K P hdelta hA hK hAP
      hPlow hPhigh hKP hKPperp
  have hgauge := Phi.mono_weaklyMajorized (weaklyMajorized_comp_castLE hle hmaj)
  simp only [Fin.val_castLE] at hgauge
  have hfA : (fun i : Fin (finrank ℝ (Pᗮ : Submodule ℝ E)) =>
      (upperBlockShift A P alpha).approximationNumber (i : ℕ))
      = fun i => (isSymmetric_upperBlockCompression hA P alpha).eigenvalues rfl i := by
    funext i
    rw [← approximationNumber_upperBlockCompression A P alpha]
    exact approximationNumber_upperBlockCompression_eq_eigenvalues hA P alpha
      (upperBlockShift_nonneg A P hdelta.le hA
        (by simpa only [RCLike.re_to_real] using hPhigh)) i
  have hfQ : (fun i : Fin (finrank ℝ (Pᗮ : Submodule ℝ E)) =>
      (upperBlockShift (A + K) (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
            hPhigh hKP hKPperp) alpha).approximationNumber (i : ℕ) *
        (cosineBlock P (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
              hPhigh hKP hKPperp)).approximationNumber (i : ℕ) ^ 2)
      = fun i => (isSymmetric_upperBlockCompression (hA.add hK)
          (canonicalLowBranchReal A K P hdelta hA hK
          hAP hPlow
            hPhigh hKP hKPperp) alpha).eigenvalues rfl
          (Fin.cast (theorem8_1_finrank_orthogonal_branch_eq_real A K P hdelta hA hK hAP
              hPlow hPhigh hKP hKPperp) i) *
          TauCeti.principalCosines Pᗮ (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
                hPhigh hKP hKPperp)ᗮ (i : ℕ) ^ 2 := by
    funext i
    have heigQ := approximationNumber_upperBlockCompression_eq_eigenvalues (hA.add hK)
      (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp) alpha
      (theorem8_1_perturbedUpperBlockShift_nonneg_real A K P hdelta hA hK hAP
          hPlow hPhigh hKP hKPperp)
      (Fin.cast (theorem8_1_finrank_orthogonal_branch_eq_real A K P hdelta hA hK hAP
          hPlow hPhigh hKP hKPperp) i)
    simp only [Fin.val_cast] at heigQ
    rw [← approximationNumber_upperBlockCompression (A + K)
        (canonicalLowBranchReal A K P hdelta hA hK
        hAP hPlow
          hPhigh hKP hKPperp) alpha, heigQ,
      approximationNumber_cosineBlock_eq_principalCosines]
  exact (congrArg (fun f => Phi f) hfA.symm).trans_le
    (hgauge.trans_eq (congrArg (fun f => Phi f) hfQ))
/-- **Theorem 8.1 (iii), lower block, with the symmetric gauge at the block
dimension, over a real Hilbert space.** -/
theorem theorem8_1_lowerSymmetricGaugeEigenvalue_blockSourceExact_real
    [FiniteDimensional ℝ E]
    [P.HasOrthogonalProjection] {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (Phi : FiniteSymmetricGauge (finrank ℝ (P : Submodule ℝ E))) :
    Phi (fun i => (isSymmetric_lowerBlockCompression hA P alpha delta).eigenvalues rfl i)
      ≤ Phi (fun i =>
        (isSymmetric_lowerBlockCompression (hA.add hK) (canonicalLowBranchReal A K P hdelta hA hK
            hAP hPlow
              hPhigh hKP hKPperp) alpha delta).eigenvalues rfl
          (Fin.cast (theorem8_1_finrank_branch_eq_real A K P hdelta hA hK hAP
              hPlow hPhigh hKP hKPperp) i) *
          TauCeti.principalCosines P (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
                hPhigh hKP hKPperp) (i : ℕ) ^ 2) := by
  have hle : finrank ℝ (P : Submodule ℝ E) ≤ finrank ℝ E := Submodule.finrank_le _
  have hmaj := theorem8_1_lowerWeightedWeakMajorization_real A K P hdelta hA hK hAP
      hPlow hPhigh hKP hKPperp
  have hgauge := Phi.mono_weaklyMajorized (weaklyMajorized_comp_castLE hle hmaj)
  simp only [Fin.val_castLE] at hgauge
  have hfA : (fun i : Fin (finrank ℝ (P : Submodule ℝ E)) =>
      (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ))
      = fun i => (isSymmetric_lowerBlockCompression hA P alpha delta).eigenvalues rfl i := by
    funext i
    rw [← approximationNumber_lowerBlockCompression A P alpha delta]
    exact approximationNumber_lowerBlockCompression_eq_eigenvalues hA P alpha delta
      (lowerBlockShift_nonneg A P hdelta.le hA
        (by simpa only [RCLike.re_to_real] using hPlow)) i
  have hfQ : (fun i : Fin (finrank ℝ (P : Submodule ℝ E)) =>
      (lowerBlockShift (A + K) (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
            hPhigh hKP hKPperp) alpha delta).approximationNumber (i : ℕ) *
        (lowerCosineBlock P (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
              hPhigh hKP hKPperp)).approximationNumber (i : ℕ) ^ 2)
      = fun i => (isSymmetric_lowerBlockCompression (hA.add hK)
          (canonicalLowBranchReal A K P hdelta hA hK
          hAP hPlow
            hPhigh hKP hKPperp) alpha delta
            ).eigenvalues rfl
          (Fin.cast (theorem8_1_finrank_branch_eq_real A K P hdelta hA hK hAP
              hPlow hPhigh hKP hKPperp) i) *
          TauCeti.principalCosines P (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
                hPhigh hKP hKPperp) (i : ℕ) ^ 2 := by
    funext i
    have heigQ := approximationNumber_lowerBlockCompression_eq_eigenvalues (hA.add hK)
      (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp) alpha delta
      (theorem8_1_perturbedLowerBlockShift_nonneg_real A K P hdelta hA hK hAP
          hPlow hPhigh hKP hKPperp)
      (Fin.cast (theorem8_1_finrank_branch_eq_real A K P hdelta hA hK hAP
          hPlow hPhigh hKP hKPperp) i)
    simp only [Fin.val_cast] at heigQ
    rw [← approximationNumber_lowerBlockCompression (A + K)
        (canonicalLowBranchReal A K P hdelta hA hK
        hAP hPlow
          hPhigh hKP hKPperp) alpha delta, heigQ,
      approximationNumber_lowerCosineBlock_eq_principalCosines]
  exact (congrArg (fun f => Phi f) hfA.symm).trans_le
    (hgauge.trans_eq (congrArg (fun f => Phi f) hfQ))

end Real

/-! ### An approximation-number extension of part (ii)

Part (ii) is printed "in finite dimensions … with the analogous lower-block
statement **and natural infinite-dimensional extensions**".  Part (iii) carries
no such clause.  So the phrase is Davis and Kahan's, and it is about (ii) alone.

**It does not identify a unique formal proposition, and nothing below claims to
be it.**  Section 1 offers two candidate readings of "the eigenvalues" in
infinite dimensions and does not choose: it gives the minimax sequence (1.10) and
says "the same minimax expression makes sense for general bounded operators", and
then says that *in the noncompact case spectral-multiplicity language may be more
appropriate*.  Theorem 8.1 prints no infinite-dimensional formula.  The counted
content of (ii) is therefore the finite-dimensional inequality, and the extension
phrase is a source assertion that is **accounted for by classification, not
discharged by proof** — see `dev/davis-kahan-1970-source-atom-inventory.json`
under `DK-8.1-thm.part-ii-eigenvalue`.

What follows is one concrete extension, offered as such: the printed inequality
on the blocks themselves with the ordered eigenvalue lists replaced by the
minimax sequence, no dimension hypothesis, bounded operators.  It is consistent
with Section 1's own machinery — for a positive operator in finite dimensions the
minimax sequence *is* the sorted eigenvalue list
(`approximationNumber_eq_eigenvalues_of_isPositive`), and every block here is
positive under Theorem 8.1's hypotheses — so it agrees with the printed statement
wherever both are defined.  It is **not** registered as source-exact evidence for
the phrase, and it is not evidence that this is what Davis and Kahan had in mind.

`‖C₁‖₁` is read here as the operator norm of the cosine block, its largest
singular value; `norm_cosineBlock_eq_principalCosines_zero` is the identification
with the largest principal cosine, and it needs finite dimension. -/

section ApproximationNumberExtension

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A K : H →L[ℂ] H) (P : Submodule ℂ H)

/-- **An approximation-number extension of Theorem 8.1 (ii), upper block, over
`ℂ`.**

The printed inequality on the blocks themselves, with the ordered eigenvalue
lists replaced by the minimax sequence (1.10), and no dimension hypothesis.  In
finite dimensions it specializes to the printed statement,
`theorem8_1_upperEigenvalueRepulsion_blockSourceExact`.

This is *an* extension, not *the* extension: the source asserts that natural
infinite-dimensional extensions exist without printing one, and Section 1 leaves
open whether the minimax sequence or spectral-multiplicity data is the right
object in the noncompact case.  See the section docstring. -/
theorem theorem8_1_upperApproximationRepulsion_blockExtension
     [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (upperBlockCompression A P alpha).approximationNumber n ≤
      ‖cosineBlock P (branch A K alpha hA hK)‖ ^ 2 *
        (upperBlockCompression (A + K) (branch A K alpha hA hK) alpha
          ).approximationNumber n := by
  rw [approximationNumber_upperBlockCompression A P alpha,
    approximationNumber_upperBlockCompression (A + K) (branch A K alpha hA hK) alpha]
  exact theorem8_1_upperApproximationRepulsion A K P hdelta hA hK hAP hPlow hPhigh
    hKP hKPperp n

/-- **An approximation-number extension of Theorem 8.1 (ii), lower block, over
`ℂ`.** -/
theorem theorem8_1_lowerApproximationRepulsion_blockExtension
     [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (lowerBlockCompression A P alpha delta).approximationNumber n ≤
      ‖lowerCosineBlock P (branch A K alpha hA hK)‖ ^ 2 *
        (lowerBlockCompression (A + K) (branch A K alpha hA hK) alpha delta
          ).approximationNumber n := by
  rw [approximationNumber_lowerBlockCompression A P alpha delta,
    approximationNumber_lowerBlockCompression (A + K) (branch A K alpha hA hK)
      alpha delta]
  exact theorem8_1_lowerApproximationRepulsion A K P hdelta hA hK hAP hPlow hPhigh
    hKP hKPperp n

end ApproximationNumberExtension

section ApproximationNumberExtensionReal

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (A K : E →L[ℝ] E) (P : Submodule ℝ E)

/-- **An approximation-number extension of Theorem 8.1 (ii), upper block, over
`ℝ`.** -/
theorem theorem8_1_upperApproximationRepulsion_blockExtension_real
     [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (upperBlockCompression A P alpha).approximationNumber n ≤
      ‖cosineBlock P (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh
        hKP hKPperp)‖ ^ 2 *
        (upperBlockCompression (A + K)
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp)
          alpha).approximationNumber n := by
  rw [approximationNumber_upperBlockCompression A P alpha,
    approximationNumber_upperBlockCompression (A + K)
      (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp) alpha]
  exact theorem8_1_upperApproximationRepulsion_real A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp n

/-- **An approximation-number extension of Theorem 8.1 (ii), lower block, over
`ℝ`.** -/
theorem theorem8_1_lowerApproximationRepulsion_blockExtension_real
     [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (lowerBlockCompression A P alpha delta).approximationNumber n ≤
      ‖lowerCosineBlock P (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
        hPhigh hKP hKPperp)‖ ^ 2 *
        (lowerBlockCompression (A + K)
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp)
          alpha delta).approximationNumber n := by
  rw [approximationNumber_lowerBlockCompression A P alpha delta,
    approximationNumber_lowerBlockCompression (A + K)
      (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp)
      alpha delta]
  exact theorem8_1_lowerApproximationRepulsion_real A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp n

end ApproximationNumberExtensionReal

end

end Section8
end DavisKahan1970
end TauCeti
