/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.TwoProjections
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SeparatedIntertwiner
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-! # Realization -/

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

/-!
# Davis--Kahan 1970, Theorem 3.1: the realization half

`GenericReconstruction.lean` and `CompactClassification.lean` prove the
*classification* half of Theorem 3.1: two ordered pairs of subspaces carrying the
same angle datum are unitarily equivalent as pairs.  This module proves the
*realization* half — the paper's sentence (ii): a prescribed admissible angle
datum is actually attained by a concrete pair of subspaces.

## The construction

Fix two Hilbert spaces `E` and `F` over an `RCLike` field `𝕜`, to be read as
`P H` and `Pᗮ H`, and work in their `L²` direct sum `WithLp 2 (E × F)`.  The
first subspace is the `E`-factor,

`U := range modelInl = {(x, 0)}`,

and the second is the image of `U` under the direct rotation, i.e. the range of
the isometry

`W₀ : E → WithLp 2 (E × F)`,  `W₀ x = (C₀ x, J S₀ x)`,

where `C₀ = cos Θ₀` and `S₀ = sin Θ₀` are the prescribed angle data on the
`P`-side and `J` is the intertwiner supplied by the spectral classification.
`W₀` is isometric because `J` is isometric on the range of `S₀`, so
`V := range W₀` is a closed subspace and `P_V = W₀ W₀⋆`.

## The block matrix

Writing `C₁ = cos Θ₁`, `S₁ = sin Θ₁` on the `Pᗮ`-side, the resulting projection is

```text
P_V = [[ C₀ C₀   , C₀ S₀ J⋆ ],
       [ J S₀ C₀ , S₁ S₁    ]]
```

which is `starProjection_targetSubspace_apply` below.  Both off-diagonal entries
are positive, as they must be for a self-adjoint operator; here that is
structural rather than checked, since `starProjection` is self-adjoint by
construction.

This agrees with the source.  Equation (3.7) of the original prints
`Q = U P U⁻¹ ≃ [[C₀², C₀S₀⋆], [S₀C₀, S₀S₀⋆]]`, with both off-diagonal entries
positive; the minus sign appears only in the second column of the direct
rotation `U` at (3.6).  An earlier campaign note claiming a sign defect here was
withdrawn after checking the original scan; see
`dev/external-literature-references.md`, "Known source errata".

## Why the angle `0` is exceptional and the angle `π/2` is not

This is the mathematical content of the hypothesis of Theorem 3.1, and it is
proved here rather than asserted.  The four elementary Halmos summands of the
constructed pair are computed exactly:

* `halmosCommonPart_eq`  : `U ⊓ V   = modelInl '' ker S₀`;
* `halmosExteriorPart_eq`: `Uᗮ ⊓ Vᗮ = modelInr '' ker S₁`;
* `halmosSourceDefect_eq`: `U ⊓ Vᗮ  = modelInl '' ker C₀`;
* `halmosTargetDefect_eq`: `Uᗮ ⊓ V  = modelInr '' ker C₁`.

For an angle operator with spectrum in `[0, π/2]`, `ker S₀` is the eigenspace at
`0` and `ker C₀` the eigenspace at `π/2`.  So:

* the two `0`-eigenspaces land in the two *uncrossed* intersections `U ⊓ V` and
  `Uᗮ ⊓ Vᗮ`, and nothing relates them — `trivialHalmosAngleDatum` realizes
  `ker S₀ = E` and `ker S₁ = F` for **arbitrary** `E` and `F`, so the
  multiplicity at angle `0` genuinely may differ between the two sides;
* the two `π/2`-eigenspaces land in the *crossed* defects `U ⊓ Vᗮ` and
  `Uᗮ ⊓ V`, and `J` restricts to a linear isometric equivalence
  `ker C₀ ≃ₗᵢ ker C₁` (`crossedDefectEquiv`), so the multiplicity at `π/2` must
  agree.  Geometrically this is forced: a unitary of the ambient space carrying
  `U` onto `V` exists only when `dim (U ⊓ Vᗮ) = dim (Uᗮ ⊓ V)`.

## Generality

Arbitrary Hilbert spaces `E`, `F` over an arbitrary `RCLike` field: no
compactness, no finite dimension, no separability, and — as it turns out — no
positivity.  In particular the real case is covered; nothing in the
construction is complex-specific.  The angle datum is recorded by the *pair*
`(cos Θ, sin Θ)` through the algebraic relations it satisfies (self-adjoint,
commuting, `C² + S² = 1`), which is all the construction consumes.  Positivity
of `C` and `S`, i.e. the restriction of the angle to `[0, π/2]`, is what makes
`ker S` the angle-`0` space and `ker C` the
angle-`π/2` space, and so belongs to the *reading* of the theorem rather than to
its proof.

## Main results

* `TauCeti.DavisKahan.HalmosAngleDatum`
* `..._starProjection_targetSubspace_apply` — the block matrix of (3.7)
* `..._compress_source_eq` and `..._compress_sourceOrthogonal_eq` — the realized
  pair has the prescribed `cos² Θ₀` and `cos² Θ₁`
* `..._halmosCommonPart_eq`, `..._halmosSourceDefect_eq`,
  `..._halmosTargetDefect_eq`, `..._halmosExteriorPart_eq`
* `..._crossedDefectEquiv` and
  `..._nonempty_halmosSourceDefect_equiv_targetDefect`
* `..._trivialHalmosAngleDatum` with `..._trivial_halmosCommonPart_eq` and
  `..._trivial_halmosExteriorPart_eq`
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

universe u v

/-! ## Preliminaries -/

section Preliminaries

variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace 𝕜 B]

/-- Two vectors of two inner product spaces with the same self-inner product have
the same norm.  Used repeatedly to promote an operator identity to an isometry
statement without leaving the inner product. -/
theorem norm_eq_norm_of_inner_self_eq {a : A} {b : B}
    (h : ⟪a, a⟫_𝕜 = ⟪b, b⟫_𝕜) : ‖a‖ = ‖b‖ := by
  have h2 : ‖a‖ ^ 2 = ‖b‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), norm_sq_eq_re_inner (𝕜 := 𝕜), h]
  exact (sq_eq_sq₀ (norm_nonneg a) (norm_nonneg b)).mp h2

end Preliminaries

/-! ## The model space `E ⊕₂ F` and its first factor -/

section Model

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (F : Type v) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The inclusion of the first factor into the `L²` direct sum. -/
noncomputable def modelInl : E →L[𝕜] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl 𝕜 E F

/-- The inclusion of the second factor into the `L²` direct sum. -/
noncomputable def modelInr : F →L[𝕜] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr 𝕜 E F

variable {𝕜 E F}

omit [CompleteSpace E] [CompleteSpace F] in
/-- The first inclusion in coordinates. -/
@[simp]
theorem modelInl_apply (x : E) : modelInl 𝕜 E F x = WithLp.toLp 2 (x, (0 : F)) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The second inclusion in coordinates. -/
@[simp]
theorem modelInr_apply (y : F) : modelInr 𝕜 E F y = WithLp.toLp 2 ((0 : E), y) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The first inclusion is isometric. -/
theorem norm_modelInl (x : E) : ‖modelInl 𝕜 E F x‖ = ‖x‖ :=
  norm_eq_norm_of_inner_self_eq (𝕜 := 𝕜) (by simp)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The second inclusion is isometric. -/
theorem norm_modelInr (y : F) : ‖modelInr 𝕜 E F y‖ = ‖y‖ :=
  norm_eq_norm_of_inner_self_eq (𝕜 := 𝕜) (by simp)

omit [CompleteSpace E] [CompleteSpace F] in
/-- A vector with vanishing second component is in the first factor. -/
theorem eq_modelInl_of_snd_eq_zero {z : WithLp 2 (E × F)} (h : (WithLp.ofLp z).2 = 0) :
    z = modelInl 𝕜 E F (WithLp.ofLp z).1 := by
  rw [modelInl_apply, ← h]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A vector with vanishing first component is in the second factor. -/
theorem eq_modelInr_of_fst_eq_zero {z : WithLp 2 (E × F)} (h : (WithLp.ofLp z).1 = 0) :
    z = modelInr 𝕜 E F (WithLp.ofLp z).2 := by
  rw [modelInr_apply, ← h]

/-- The adjoint of the first inclusion is the first projection. -/
theorem adjoint_modelInl :
    ContinuousLinearMap.adjoint (modelInl 𝕜 E F) = WithLp.fstL 2 𝕜 E F :=
  ((ContinuousLinearMap.eq_adjoint_iff (WithLp.fstL 2 𝕜 E F) (modelInl 𝕜 E F)).mpr
    (by intro z x; simp)).symm

/-- The adjoint of the second inclusion is the second projection. -/
theorem adjoint_modelInr :
    ContinuousLinearMap.adjoint (modelInr 𝕜 E F) = WithLp.sndL 2 𝕜 E F :=
  ((ContinuousLinearMap.eq_adjoint_iff (WithLp.sndL 2 𝕜 E F) (modelInr 𝕜 E F)).mpr
    (by intro z y; simp)).symm

/-- A norm-preserving continuous linear map out of a complete space has closed,
hence complete, range. -/
theorem completeSpace_range_of_norm_map {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [CompleteSpace G] (f : E →L[𝕜] G) (hf : ∀ x, ‖f x‖ = ‖x‖) :
    CompleteSpace (LinearMap.range (f : E →ₗ[𝕜] G)) := by
  have hiso : Isometry (f : E → G) := AddMonoidHomClass.isometry_of_norm f hf
  have hclosed : IsClosed (Set.range (f : E → G)) := hiso.isClosedEmbedding.isClosed_range
  have hcl : IsClosed ((LinearMap.range (f : E →ₗ[𝕜] G) : Submodule 𝕜 G) : Set G) := by
    simpa [LinearMap.coe_range] using hclosed
  exact hcl.completeSpace_coe

omit [CompleteSpace E] in
/-- A norm-preserving continuous linear map is injective. -/
theorem injective_of_norm_map {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (f : E →L[𝕜] G) (hf : ∀ x, ‖f x‖ = ‖x‖) :
    Function.Injective (f : E →ₗ[𝕜] G) := by
  intro a b hab
  have hz : ‖a - b‖ = 0 := by
    rw [← hf, map_sub]
    simp only [ContinuousLinearMap.coe_coe] at hab
    rw [hab, sub_self, norm_zero]
  simpa [sub_eq_zero] using norm_eq_zero.mp hz

/-- A norm-preserving continuous linear map carries a submodule isometrically onto
its image. -/
noncomputable def submoduleMapIsometry {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (f : E →L[𝕜] G) (hf : ∀ x, ‖f x‖ = ‖x‖) (K : Submodule 𝕜 E) :
    K ≃ₗᵢ[𝕜] Submodule.map (f : E →ₗ[𝕜] G) K :=
  { Submodule.equivMapOfInjective (f : E →ₗ[𝕜] G) (injective_of_norm_map f hf) K with
    norm_map' := fun x => by
      have h := Submodule.coe_equivMapOfInjective_apply (f : E →ₗ[𝕜] G)
        (injective_of_norm_map f hf) K x
      calc ‖(Submodule.equivMapOfInjective (f : E →ₗ[𝕜] G)
              (injective_of_norm_map f hf) K) x‖
          = ‖(((Submodule.equivMapOfInjective (f : E →ₗ[𝕜] G)
              (injective_of_norm_map f hf) K) x : Submodule.map (f : E →ₗ[𝕜] G) K) : G)‖ := rfl
        _ = ‖f (x : E)‖ := by rw [h]; simp
        _ = ‖(x : E)‖ := hf _
        _ = ‖x‖ := rfl }

variable (𝕜 E F)

/-- **The first subspace of the realized pair**: the `E`-factor, i.e. `P H`. -/
noncomputable def sourceSubspace : Submodule 𝕜 (WithLp 2 (E × F)) :=
  LinearMap.range (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))

/-- The `E`-factor is complete, being the isometric image of a complete space. -/
noncomputable instance : CompleteSpace (sourceSubspace 𝕜 E F) :=
  completeSpace_range_of_norm_map _ norm_modelInl

variable {𝕜 E F}

omit [CompleteSpace E] [CompleteSpace F] in
/-- Membership in the `E`-factor is the vanishing of the second component. -/
theorem mem_sourceSubspace_iff (z : WithLp 2 (E × F)) :
    z ∈ sourceSubspace 𝕜 E F ↔ (WithLp.ofLp z).2 = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp [modelInl]
  · intro h
    exact ⟨(WithLp.ofLp z).1, (eq_modelInl_of_snd_eq_zero h).symm⟩

/-- The orthogonal complement of the `E`-factor is the kernel of the first projection. -/
theorem sourceSubspace_orthogonal :
    (sourceSubspace 𝕜 E F)ᗮ = LinearMap.ker (WithLp.fstL 2 𝕜 E F : _ →ₗ[𝕜] E) := by
  rw [sourceSubspace, ContinuousLinearMap.orthogonal_range, adjoint_modelInl]

/-- Membership in the `F`-factor is the vanishing of the first component. -/
theorem mem_sourceSubspace_orthogonal_iff (z : WithLp 2 (E × F)) :
    z ∈ (sourceSubspace 𝕜 E F)ᗮ ↔ (WithLp.ofLp z).1 = 0 := by
  rw [sourceSubspace_orthogonal]
  simp [LinearMap.mem_ker]

/-- The orthogonal projection onto the `E`-factor discards the second component. -/
theorem starProjection_sourceSubspace (z : WithLp 2 (E × F)) :
    (sourceSubspace 𝕜 E F).starProjection z = modelInl 𝕜 E F (WithLp.ofLp z).1 := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ⟨(WithLp.ofLp z).1, rfl⟩ ?_
  rw [mem_sourceSubspace_orthogonal_iff]
  simp [modelInl]

/-- The orthogonal projection onto the `F`-factor discards the first component. -/
theorem starProjection_sourceSubspace_orthogonal (z : WithLp 2 (E × F)) :
    (sourceSubspace 𝕜 E F)ᗮ.starProjection z = modelInr 𝕜 E F (WithLp.ofLp z).2 := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · rw [mem_sourceSubspace_orthogonal_iff]
    simp [modelInr]
  · rw [Submodule.orthogonal_orthogonal, mem_sourceSubspace_iff]
    simp [modelInr]

end Model

/-! ## Block operators between two model spaces

A pair of operators on the two factors gives one operator on the `L²` direct
sums.  This is the calculus behind `HalmosAngleDatum.prod`: the direct sum of two
admissible angle data is admissible, with every block the direct sum of the
corresponding blocks. -/

section Block

variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace 𝕜 A] [CompleteSpace A]
variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace 𝕜 B] [CompleteSpace B]
variable {C : Type*} [NormedAddCommGroup C] [InnerProductSpace 𝕜 C] [CompleteSpace C]
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace 𝕜 D] [CompleteSpace D]

omit [CompleteSpace C] [CompleteSpace D] in
/-- Addition in the `L²` direct sum is coordinatewise. -/
@[simp]
theorem toLp_prod_add (a c : C) (b d : D) :
    WithLp.toLp 2 (a, b) + WithLp.toLp 2 (c, d) = WithLp.toLp 2 (a + c, b + d) := rfl

/-- **The block-diagonal operator `f ⊕ g`** from `A ⊕₂ B` to `C ⊕₂ D`. -/
noncomputable def blockMap (f : A →L[𝕜] C) (g : B →L[𝕜] D) :
    WithLp 2 (A × B) →L[𝕜] WithLp 2 (C × D) :=
  modelInl 𝕜 C D ∘L f ∘L WithLp.fstL 2 𝕜 A B +
    modelInr 𝕜 C D ∘L g ∘L WithLp.sndL 2 𝕜 A B

omit [CompleteSpace A] [CompleteSpace B] [CompleteSpace C] [CompleteSpace D] in
/-- A block operator acts blockwise. -/
@[simp]
theorem blockMap_apply (f : A →L[𝕜] C) (g : B →L[𝕜] D) (z : WithLp 2 (A × B)) :
    blockMap f g z =
      WithLp.toLp 2 (f (WithLp.ofLp z).1, g (WithLp.ofLp z).2) := by
  rw [blockMap]
  simp

omit [CompleteSpace A] [CompleteSpace B] [CompleteSpace C] [CompleteSpace D] in
/-- Block operators compose blockwise. -/
theorem blockMap_comp {A' : Type*} [NormedAddCommGroup A'] [InnerProductSpace 𝕜 A']
     {B' : Type*} [NormedAddCommGroup B'] [InnerProductSpace 𝕜 B']
     (f : A →L[𝕜] C) (g : B →L[𝕜] D) (f' : A' →L[𝕜] A)
    (g' : B' →L[𝕜] B) :
    blockMap f g ∘L blockMap f' g' = blockMap (f ∘L f') (g ∘L g') :=
  ContinuousLinearMap.ext fun z => by simp

omit [CompleteSpace A] [CompleteSpace B] [CompleteSpace C] [CompleteSpace D] in
/-- Block operators add blockwise. -/
theorem blockMap_add (f f' : A →L[𝕜] C) (g g' : B →L[𝕜] D) :
    blockMap f g + blockMap f' g' = blockMap (f + f') (g + g') :=
  ContinuousLinearMap.ext fun z => by simp

omit [CompleteSpace A] [CompleteSpace B] in
/-- The block-diagonal identity is the identity. -/
theorem blockMap_one : blockMap (1 : A →L[𝕜] A) (1 : B →L[𝕜] B) = 1 :=
  ContinuousLinearMap.ext fun z => by
    rw [blockMap_apply]
    simp only [one_apply_eq_self]

/-- Adjoints of block operators are taken blockwise. -/
theorem adjoint_blockMap (f : A →L[𝕜] C) (g : B →L[𝕜] D) :
    ContinuousLinearMap.adjoint (blockMap f g) =
      blockMap (ContinuousLinearMap.adjoint f) (ContinuousLinearMap.adjoint g) :=
  ((ContinuousLinearMap.eq_adjoint_iff
    (blockMap (ContinuousLinearMap.adjoint f) (ContinuousLinearMap.adjoint g))
    (blockMap f g)).mpr fun w z => by
      rw [blockMap_apply, blockMap_apply, WithLp.prod_inner_apply,
        WithLp.prod_inner_apply]
      rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]).symm

/-- A block-diagonal operator with self-adjoint blocks is self-adjoint. -/
theorem isSelfAdjoint_blockMap {f : A →L[𝕜] A} {g : B →L[𝕜] B}
    (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (blockMap f g) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', adjoint_blockMap,
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hf,
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hg]

omit [CompleteSpace A] [CompleteSpace B] [CompleteSpace C] [CompleteSpace D] in
/-- A block operator that kills the second factor factors through the first. -/
theorem blockMap_zero_right (f : A →L[𝕜] C) :
    blockMap f (0 : B →L[𝕜] D) = modelInl 𝕜 C D ∘L f ∘L WithLp.fstL 2 𝕜 A B :=
  ContinuousLinearMap.ext fun z => by simp

omit [CompleteSpace A] [CompleteSpace B] in
/-- The inclusion of the first factor is a contraction. -/
theorem norm_modelInl_le_one : ‖modelInl 𝕜 A B‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, norm_modelInl]

omit [CompleteSpace A] [CompleteSpace B] in
/-- The projection onto the first factor is a contraction. -/
theorem norm_fstL_le_one : ‖WithLp.fstL 2 𝕜 A B‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [one_mul]
    exact WithLp.norm_fst_le _ z

end Block

/-! ## Admissible angle data -/

/-- **A prescribed admissible angle datum for Davis--Kahan Theorem 3.1.**

`cos₀, sin₀` are `cos Θ₀, sin Θ₀` on the `P`-side, `cos₁, sin₁` are
`cos Θ₁, sin Θ₁` on the `Pᗮ`-side, and `intertwiner` is the map `J₀` supplied by
the spectral classification: a partial isometry whose initial space is
`(ker sin₀)ᗮ` and whose final space is `(ker sin₁)ᗮ`, intertwining the two angle
operators.

The last two fields record exactly the partial-isometry content that the
construction uses: `J₀` is isometric on the range of `sin₀` and co-isometric onto
the range of `sin₁`.  Together with the two intertwining fields they say that
`J₀` matches the spectral multiplicities of `Θ₀` and `Θ₁` at every angle *except*
`0`.  Angle `0` lies outside `J₀`'s initial and final spaces, which is exactly
why Theorem 3.1 permits the multiplicity at `0` to differ. -/
structure HalmosAngleDatum (𝕜 : Type*) [RCLike 𝕜] (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] where
  /-- `cos Θ₀`, the cosine of the angle operator on the `P`-side. -/
  cos₀ : E →L[𝕜] E
  /-- `sin Θ₀`, the sine of the angle operator on the `P`-side. -/
  sin₀ : E →L[𝕜] E
  /-- `cos Θ₁`, the cosine of the angle operator on the `Pᗮ`-side. -/
  cos₁ : F →L[𝕜] F
  /-- `sin Θ₁`, the sine of the angle operator on the `Pᗮ`-side. -/
  sin₁ : F →L[𝕜] F
  /-- `J₀`, the intertwiner supplied by the spectral classification. -/
  intertwiner : E →L[𝕜] F
  /-- `cos Θ₀` is self-adjoint. -/
  isSelfAdjoint_cos₀ : IsSelfAdjoint cos₀
  /-- `sin Θ₀` is self-adjoint. -/
  isSelfAdjoint_sin₀ : IsSelfAdjoint sin₀
  /-- `cos Θ₁` is self-adjoint. -/
  isSelfAdjoint_cos₁ : IsSelfAdjoint cos₁
  /-- `sin Θ₁` is self-adjoint. -/
  isSelfAdjoint_sin₁ : IsSelfAdjoint sin₁
  /-- The two `P`-side angle functions commute. -/
  commute₀ : cos₀ ∘L sin₀ = sin₀ ∘L cos₀
  /-- The two `Pᗮ`-side angle functions commute. -/
  commute₁ : cos₁ ∘L sin₁ = sin₁ ∘L cos₁
  /-- `cos² Θ₀ + sin² Θ₀ = 1`. -/
  pythagoras₀ : cos₀ ∘L cos₀ + sin₀ ∘L sin₀ = 1
  /-- `cos² Θ₁ + sin² Θ₁ = 1`. -/
  pythagoras₁ : cos₁ ∘L cos₁ + sin₁ ∘L sin₁ = 1
  /-- `J₀ cos Θ₀ = cos Θ₁ J₀`. -/
  map_cos : intertwiner ∘L cos₀ = cos₁ ∘L intertwiner
  /-- `J₀ sin Θ₀ = sin Θ₁ J₀`. -/
  map_sin : intertwiner ∘L sin₀ = sin₁ ∘L intertwiner
  /-- `J₀` is isometric on the range of `sin Θ₀`. -/
  isometry_on_sin₀ :
    ContinuousLinearMap.adjoint intertwiner ∘L intertwiner ∘L sin₀ = sin₀
  /-- `J₀` is co-isometric onto the range of `sin Θ₁`. -/
  coisometry_on_sin₁ :
    intertwiner ∘L ContinuousLinearMap.adjoint intertwiner ∘L sin₁ = sin₁

namespace HalmosAngleDatum

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable (d : HalmosAngleDatum 𝕜 E F)

/-! ### Pointwise forms of the datum's relations -/

/-- `cos Θ₀` moves across the inner product. -/
theorem inner_cos₀ (x y : E) : ⟪d.cos₀ x, y⟫_𝕜 = ⟪x, d.cos₀ y⟫_𝕜 := by
  conv_lhs => rw [← ContinuousLinearMap.isSelfAdjoint_iff'.mp d.isSelfAdjoint_cos₀]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- `sin Θ₀` moves across the inner product. -/
theorem inner_sin₀ (x y : E) : ⟪d.sin₀ x, y⟫_𝕜 = ⟪x, d.sin₀ y⟫_𝕜 := by
  conv_lhs => rw [← ContinuousLinearMap.isSelfAdjoint_iff'.mp d.isSelfAdjoint_sin₀]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- `cos Θ₁` moves across the inner product. -/
theorem inner_cos₁ (x y : F) : ⟪d.cos₁ x, y⟫_𝕜 = ⟪x, d.cos₁ y⟫_𝕜 := by
  conv_lhs => rw [← ContinuousLinearMap.isSelfAdjoint_iff'.mp d.isSelfAdjoint_cos₁]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- `sin Θ₁` moves across the inner product. -/
theorem inner_sin₁ (x y : F) : ⟪d.sin₁ x, y⟫_𝕜 = ⟪x, d.sin₁ y⟫_𝕜 := by
  conv_lhs => rw [← ContinuousLinearMap.isSelfAdjoint_iff'.mp d.isSelfAdjoint_sin₁]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- The `P`-side commutation, at a vector. -/
theorem commute₀_apply (x : E) : d.cos₀ (d.sin₀ x) = d.sin₀ (d.cos₀ x) :=
  congrArg (fun f : E →L[𝕜] E => f x) d.commute₀

/-- The `Pᗮ`-side commutation, at a vector. -/
theorem commute₁_apply (y : F) : d.cos₁ (d.sin₁ y) = d.sin₁ (d.cos₁ y) :=
  congrArg (fun f : F →L[𝕜] F => f y) d.commute₁

/-- The `P`-side Pythagorean identity, at a vector. -/
theorem pythagoras₀_apply (x : E) : d.cos₀ (d.cos₀ x) + d.sin₀ (d.sin₀ x) = x :=
  congrArg (fun f : E →L[𝕜] E => f x) d.pythagoras₀

/-- The `Pᗮ`-side Pythagorean identity, at a vector. -/
theorem pythagoras₁_apply (y : F) : d.cos₁ (d.cos₁ y) + d.sin₁ (d.sin₁ y) = y :=
  congrArg (fun f : F →L[𝕜] F => f y) d.pythagoras₁

/-- The cosine intertwining, at a vector. -/
theorem map_cos_apply (x : E) : d.intertwiner (d.cos₀ x) = d.cos₁ (d.intertwiner x) :=
  congrArg (fun f : E →L[𝕜] F => f x) d.map_cos

/-- The sine intertwining, at a vector. -/
theorem map_sin_apply (x : E) : d.intertwiner (d.sin₀ x) = d.sin₁ (d.intertwiner x) :=
  congrArg (fun f : E →L[𝕜] F => f x) d.map_sin

/-- `J₀⋆ J₀` is the identity on the range of `sin Θ₀`, at a vector. -/
theorem isometry_on_sin₀_apply (x : E) :
    ContinuousLinearMap.adjoint d.intertwiner (d.intertwiner (d.sin₀ x)) = d.sin₀ x :=
  congrArg (fun f : E →L[𝕜] E => f x) d.isometry_on_sin₀

/-- `J₀ J₀⋆` is the identity on the range of `sin Θ₁`, at a vector. -/
theorem coisometry_on_sin₁_apply (y : F) :
    d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ y)) = d.sin₁ y :=
  congrArg (fun f : F →L[𝕜] F => f y) d.coisometry_on_sin₁

/-- The angle-`π/2` eigenspace lies in the range of `sin Θ₀`. -/
theorem sin₀_sin₀_of_cos₀_eq_zero {x : E} (hx : d.cos₀ x = 0) :
    d.sin₀ (d.sin₀ x) = x := by
  have h := d.pythagoras₀_apply x
  rw [hx, map_zero, zero_add] at h
  exact h

/-- The angle-`π/2` eigenspace lies in the range of `sin Θ₁`. -/
theorem sin₁_sin₁_of_cos₁_eq_zero {y : F} (hy : d.cos₁ y = 0) :
    d.sin₁ (d.sin₁ y) = y := by
  have h := d.pythagoras₁_apply y
  rw [hy, map_zero, zero_add] at h
  exact h

/-- `J₀` preserves the norm on the range of `sin Θ₀`. -/
theorem norm_intertwiner_sin₀ (x : E) :
    ‖d.intertwiner (d.sin₀ x)‖ = ‖d.sin₀ x‖ := by
  refine norm_eq_norm_of_inner_self_eq (𝕜 := 𝕜) (A := F) (B := E) ?_
  rw [← ContinuousLinearMap.adjoint_inner_right, d.isometry_on_sin₀_apply]

/-! ### Adjoint transport

The intertwining relations, moved across the adjoint of `J₀`.  These are the
identities that make the `Pᗮ`-side of the construction close. -/

/-- `cos Θ₀ J₀⋆ = J₀⋆ cos Θ₁`. -/
theorem cos₀_adjoint_intertwiner (y : F) :
    d.cos₀ (ContinuousLinearMap.adjoint d.intertwiner y) =
      ContinuousLinearMap.adjoint d.intertwiner (d.cos₁ y) := by
  refine ext_inner_right 𝕜 fun x => ?_
  calc ⟪d.cos₀ (ContinuousLinearMap.adjoint d.intertwiner y), x⟫_𝕜
      = ⟪ContinuousLinearMap.adjoint d.intertwiner y, d.cos₀ x⟫_𝕜 := d.inner_cos₀ _ _
    _ = ⟪y, d.intertwiner (d.cos₀ x)⟫_𝕜 :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ⟪y, d.cos₁ (d.intertwiner x)⟫_𝕜 := by rw [d.map_cos_apply]
    _ = ⟪d.cos₁ y, d.intertwiner x⟫_𝕜 := (d.inner_cos₁ _ _).symm
    _ = ⟪ContinuousLinearMap.adjoint d.intertwiner (d.cos₁ y), x⟫_𝕜 :=
        (ContinuousLinearMap.adjoint_inner_left _ _ _).symm

/-- `sin Θ₀ J₀⋆ = J₀⋆ sin Θ₁`. -/
theorem sin₀_adjoint_intertwiner (y : F) :
    d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y) =
      ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ y) := by
  refine ext_inner_right 𝕜 fun x => ?_
  calc ⟪d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y), x⟫_𝕜
      = ⟪ContinuousLinearMap.adjoint d.intertwiner y, d.sin₀ x⟫_𝕜 := d.inner_sin₀ _ _
    _ = ⟪y, d.intertwiner (d.sin₀ x)⟫_𝕜 :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ⟪y, d.sin₁ (d.intertwiner x)⟫_𝕜 := by rw [d.map_sin_apply]
    _ = ⟪d.sin₁ y, d.intertwiner x⟫_𝕜 := (d.inner_sin₁ _ _).symm
    _ = ⟪ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ y), x⟫_𝕜 :=
        (ContinuousLinearMap.adjoint_inner_left _ _ _).symm

/-- The adjoint form of the co-isometry field: `sin Θ₁ J₀ J₀⋆ = sin Θ₁`. -/
theorem sin₁_intertwiner_adjoint (y : F) :
    d.sin₁ (d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner y)) = d.sin₁ y := by
  refine ext_inner_right 𝕜 fun w => ?_
  calc ⟪d.sin₁ (d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner y)), w⟫_𝕜
      = ⟪d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner y), d.sin₁ w⟫_𝕜 :=
        d.inner_sin₁ _ _
    _ = ⟪ContinuousLinearMap.adjoint d.intertwiner y,
          ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ w)⟫_𝕜 := by
        rw [← ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪y, d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ w))⟫_𝕜 :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ⟪y, d.sin₁ w⟫_𝕜 := by rw [d.coisometry_on_sin₁_apply]
    _ = ⟪d.sin₁ y, w⟫_𝕜 := (d.inner_sin₁ _ _).symm

/-! ### The realizing isometry and the second subspace -/

/-- **The direct rotation, applied to the first factor.**  `W₀ x = (C₀ x, J S₀ x)`. -/
noncomputable def realizingIsometry : E →L[𝕜] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L
    (d.cos₀.prod (d.intertwiner ∘L d.sin₀))

/-- The realizing isometry in coordinates. -/
@[simp]
theorem realizingIsometry_apply (x : E) :
    d.realizingIsometry x = WithLp.toLp 2 (d.cos₀ x, d.intertwiner (d.sin₀ x)) := rfl

/-- The adjoint of the realizing isometry: `W₀⋆ (x, y) = C₀ x + S₀ J⋆ y`. -/
noncomputable def realizingCoisometry : WithLp 2 (E × F) →L[𝕜] E :=
  d.cos₀ ∘L WithLp.fstL 2 𝕜 E F +
    d.sin₀ ∘L ContinuousLinearMap.adjoint d.intertwiner ∘L WithLp.sndL 2 𝕜 E F

/-- The realizing coisometry in coordinates. -/
@[simp]
theorem realizingCoisometry_apply (z : WithLp 2 (E × F)) :
    d.realizingCoisometry z =
      d.cos₀ (WithLp.ofLp z).1 +
        d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner (WithLp.ofLp z).2) := rfl

/-- `W₀⋆` is the operator written down as `realizingCoisometry`. -/
theorem adjoint_realizingIsometry :
    ContinuousLinearMap.adjoint d.realizingIsometry = d.realizingCoisometry := by
  refine ((ContinuousLinearMap.eq_adjoint_iff d.realizingCoisometry
    d.realizingIsometry).mpr ?_).symm
  intro z x
  rw [realizingCoisometry_apply, inner_add_left, realizingIsometry_apply,
    WithLp.prod_inner_apply]
  congr 1
  · exact d.inner_cos₀ _ _
  · rw [d.inner_sin₀, ContinuousLinearMap.adjoint_inner_left]

/-- `W₀⋆ W₀ = 1`: the realizing map is an isometry. -/
theorem realizingCoisometry_realizingIsometry (x : E) :
    d.realizingCoisometry (d.realizingIsometry x) = x := by
  rw [realizingIsometry_apply, realizingCoisometry_apply]
  rw [d.isometry_on_sin₀_apply, d.pythagoras₀_apply]

/-- `W₀` preserves norms. -/
theorem norm_realizingIsometry (x : E) : ‖d.realizingIsometry x‖ = ‖x‖ := by
  refine norm_eq_norm_of_inner_self_eq (𝕜 := 𝕜) ?_
  rw [← ContinuousLinearMap.adjoint_inner_right, d.adjoint_realizingIsometry,
    d.realizingCoisometry_realizingIsometry]

/-- **The second subspace of the realized pair**: the image of the first under the
direct rotation, i.e. `Q H`. -/
noncomputable def targetSubspace : Submodule 𝕜 (WithLp 2 (E × F)) :=
  LinearMap.range (d.realizingIsometry : E →ₗ[𝕜] WithLp 2 (E × F))

/-- The realized subspace is complete, being the isometric image of a complete space. -/
noncomputable instance : CompleteSpace d.targetSubspace :=
  completeSpace_range_of_norm_map _ d.norm_realizingIsometry

/-- Membership in `Vᗮ` is the vanishing of `W₀⋆`. -/
theorem mem_targetSubspace_orthogonal_iff (z : WithLp 2 (E × F)) :
    z ∈ (d.targetSubspace)ᗮ ↔
      d.cos₀ (WithLp.ofLp z).1 +
        d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner (WithLp.ofLp z).2) = 0 := by
  rw [targetSubspace, ContinuousLinearMap.orthogonal_range, d.adjoint_realizingIsometry]
  simp [LinearMap.mem_ker]

/-- **The projection onto the realized subspace is `W₀ W₀⋆`.** -/
theorem starProjection_targetSubspace (z : WithLp 2 (E × F)) :
    d.targetSubspace.starProjection z =
      d.realizingIsometry (d.realizingCoisometry z) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ⟨d.realizingCoisometry z, rfl⟩ ?_
  rw [mem_targetSubspace_orthogonal_iff]
  have h : d.realizingCoisometry (z - d.realizingIsometry (d.realizingCoisometry z)) = 0 := by
    rw [map_sub, d.realizingCoisometry_realizingIsometry, sub_self]
  simpa using h

/-- **Davis--Kahan 1970, the Theorem 3.1 realization matrix, with the source's sign
error corrected.**

`Q = [[C₀ C₀, C₀ S₀ J⋆], [J S₀ C₀, S₁ S₁]]`.  The printed matrix carries a minus
sign in the upper-right entry against a positive lower-left entry and is
therefore not self-adjoint; the minus belongs to the second column of the direct
rotation, not to the outer product defining `Q`.  Here the entries are read off a
genuine `starProjection`, so self-adjointness is not in question. -/
theorem starProjection_targetSubspace_apply (x : E) (y : F) :
    d.targetSubspace.starProjection (WithLp.toLp 2 (x, y)) =
      WithLp.toLp 2
        (d.cos₀ (d.cos₀ x) + d.cos₀ (d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y)),
          d.intertwiner (d.sin₀ (d.cos₀ x)) + d.sin₁ (d.sin₁ y)) := by
  have hkey : d.intertwiner (d.sin₀ (d.sin₀
      (ContinuousLinearMap.adjoint d.intertwiner y))) = d.sin₁ (d.sin₁ y) :=
    calc d.intertwiner (d.sin₀ (d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y)))
        = d.sin₁ (d.intertwiner (d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y))) :=
          d.map_sin_apply _
      _ = d.sin₁ (d.sin₁ (d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner y))) := by
          rw [d.map_sin_apply]
      _ = d.sin₁ (d.sin₁ y) := by rw [d.sin₁_intertwiner_adjoint]
  have hfst : d.cos₀ (d.cos₀ x + d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y))
      = d.cos₀ (d.cos₀ x) + d.cos₀ (d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y)) :=
    map_add _ _ _
  have hsnd : d.intertwiner (d.sin₀ (d.cos₀ x +
      d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y)))
      = d.intertwiner (d.sin₀ (d.cos₀ x)) + d.sin₁ (d.sin₁ y) := by
    rw [map_add, map_add, hkey]
  rw [d.starProjection_targetSubspace, realizingCoisometry_apply]
  simp only [realizingIsometry_apply]
  rw [hfst, hsnd]

/-! ### The realized pair has the prescribed angle operators -/

/-- **The `P`-side angle of the realized pair is the prescribed one**: the
compression of `P_V` to `U` is `cos² Θ₀`. -/
theorem compress_source_eq (x : E) :
    (sourceSubspace 𝕜 E F).starProjection
        (d.targetSubspace.starProjection (modelInl 𝕜 E F x)) =
      modelInl 𝕜 E F (d.cos₀ (d.cos₀ x)) := by
  rw [modelInl_apply, d.starProjection_targetSubspace_apply, starProjection_sourceSubspace]
  simp

/-- **The `Pᗮ`-side angle of the realized pair is the prescribed one**: the
compression of `P_Vᗮ` to `Uᗮ` is `cos² Θ₁`. -/
theorem compress_sourceOrthogonal_eq (y : F) :
    (sourceSubspace 𝕜 E F)ᗮ.starProjection
        ((d.targetSubspace)ᗮ.starProjection (modelInr 𝕜 E F y)) =
      modelInr 𝕜 E F (d.cos₁ (d.cos₁ y)) := by
  have hQ : d.targetSubspace.starProjection (modelInr 𝕜 E F y) =
      WithLp.toLp 2 (d.cos₀ (d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y)),
        d.sin₁ (d.sin₁ y)) := by
    rw [modelInr_apply, d.starProjection_targetSubspace_apply]
    simp
  have hperp : (d.targetSubspace)ᗮ.starProjection (modelInr 𝕜 E F y) =
      modelInr 𝕜 E F y - d.targetSubspace.starProjection (modelInr 𝕜 E F y) :=
    eq_sub_of_add_eq' (d.targetSubspace.starProjection_add_starProjection_orthogonal _)
  rw [hperp, hQ, starProjection_sourceSubspace_orthogonal]
  congr 1
  have hsnd : (WithLp.ofLp (modelInr 𝕜 E F y -
      WithLp.toLp 2 (d.cos₀ (d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y)),
        d.sin₁ (d.sin₁ y)))).2 = y - d.sin₁ (d.sin₁ y) := by
    simp
  rw [hsnd]
  exact (eq_sub_of_add_eq (d.pythagoras₁_apply y)).symm

/-! ### The two angle blocks as operators on the whole space

`compress_source_eq` reads the `P`-side angle off one vector at a time.  The two
statements below package the same fact as an operator identity on all of
`WithLp 2 (E × F)`, which is the form the compactness hypotheses of Corollary 3.1
are stated in: both blocks annihilate the `F`-factor, so each factors as
`modelInl ∘ (angle operator) ∘ fstL`. -/

/-- **The cosine block `P_U P_V P_U` of the realized pair is `cos² Θ₀`** on the
`E`-factor and zero on the `F`-factor. -/
theorem cosineBlock_eq :
    (sourceSubspace 𝕜 E F).starProjection ∘L d.targetSubspace.starProjection ∘L
        (sourceSubspace 𝕜 E F).starProjection =
      modelInl 𝕜 E F ∘L (d.cos₀ ∘L d.cos₀) ∘L WithLp.fstL 2 𝕜 E F := by
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [ContinuousLinearMap.comp_apply, starProjection_sourceSubspace z]
  exact d.compress_source_eq _

/-- **The defect block `P_U (1 - P_V) P_U` of the realized pair is `sin² Θ₀`** on
the `E`-factor and zero on the `F`-factor.

This is the block whose compactness Davis and Kahan assume in Corollary 3.1, and
the identity is what turns a prescribed angle sequence tending to `0` into that
hypothesis: `sin² Θ₀` inherits the decay. -/
theorem defectBlock_eq :
    (sourceSubspace 𝕜 E F).starProjection ∘L
        (ContinuousLinearMap.id 𝕜 (WithLp 2 (E × F)) -
          d.targetSubspace.starProjection) ∘L
        (sourceSubspace 𝕜 E F).starProjection =
      modelInl 𝕜 E F ∘L (d.sin₀ ∘L d.sin₀) ∘L WithLp.fstL 2 𝕜 E F := by
  refine ContinuousLinearMap.ext fun z => ?_
  have hfix : (sourceSubspace 𝕜 E F).starProjection
      (modelInl 𝕜 E F (WithLp.ofLp z).1) = modelInl 𝕜 E F (WithLp.ofLp z).1 := by
    rw [starProjection_sourceSubspace]
    rfl
  have hsin : (WithLp.ofLp z).1 - d.cos₀ (d.cos₀ (WithLp.ofLp z).1) =
      d.sin₀ (d.sin₀ (WithLp.ofLp z).1) :=
    (eq_sub_of_add_eq' (d.pythagoras₀_apply _)).symm
  simp only [ContinuousLinearMap.comp_apply, starProjection_sourceSubspace z,
    sub_apply, ContinuousLinearMap.id_apply, map_sub, hfix, d.compress_source_eq]
  rw [← map_sub, hsin]
  rfl

/-! ### The four elementary Halmos summands of the realized pair -/

/-- **`U ⊓ V` is the angle-`0` eigenspace on the `P`-side.** -/
theorem halmosCommonPart_eq :
    sourceSubspace 𝕜 E F ⊓ d.targetSubspace =
      Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
        (LinearMap.ker (d.sin₀ : E →ₗ[𝕜] E)) := by
  refine Submodule.ext fun z => ?_
  constructor
  · intro hz
    obtain ⟨hzU, a, rfl⟩ := Submodule.mem_inf.mp hz
    rw [mem_sourceSubspace_iff] at hzU
    simp only [ContinuousLinearMap.coe_coe, realizingIsometry_apply,
      WithLp.ofLp_toLp] at hzU
    have hsa : d.sin₀ a = 0 := by
      have hn := d.norm_intertwiner_sin₀ a
      rw [hzU, norm_zero] at hn
      exact norm_eq_zero.mp hn.symm
    refine ⟨d.cos₀ a, ?_, ?_⟩
    · simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [← d.commute₀_apply, hsa, map_zero]
    · simp only [ContinuousLinearMap.coe_coe, modelInl_apply, realizingIsometry_apply]
      rw [hzU]
  · rintro ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
    have h1 : d.sin₀ (d.cos₀ x) = 0 := by rw [← d.commute₀_apply, hx, map_zero]
    have h2 : d.cos₀ (d.cos₀ x) = x := by
      have h := d.pythagoras₀_apply x
      rw [hx, map_zero, add_zero] at h
      exact h
    refine Submodule.mem_inf.mpr ⟨?_, ⟨d.cos₀ x, ?_⟩⟩
    · rw [mem_sourceSubspace_iff]
      simp
    · simp only [realizingIsometry_apply, h1, h2, map_zero, ContinuousLinearMap.coe_coe,
        modelInl_apply]

/-- **`U ⊓ Vᗮ` is the angle-`π/2` eigenspace on the `P`-side.** -/
theorem halmosSourceDefect_eq :
    sourceSubspace 𝕜 E F ⊓ (d.targetSubspace)ᗮ =
      Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
        (LinearMap.ker (d.cos₀ : E →ₗ[𝕜] E)) := by
  refine Submodule.ext fun z => ?_
  constructor
  · intro hz
    obtain ⟨hzU, hzV⟩ := Submodule.mem_inf.mp hz
    rw [mem_sourceSubspace_iff] at hzU
    rw [d.mem_targetSubspace_orthogonal_iff, hzU] at hzV
    simp only [map_zero, add_zero] at hzV
    exact ⟨(WithLp.ofLp z).1, hzV, (eq_modelInl_of_snd_eq_zero hzU).symm⟩
  · rintro ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_sourceSubspace_iff]
      simp
    · rw [d.mem_targetSubspace_orthogonal_iff]
      simp [hx]

/-- **`Uᗮ ⊓ Vᗮ` is the angle-`0` eigenspace on the `Pᗮ`-side.** -/
theorem halmosExteriorPart_eq :
    (sourceSubspace 𝕜 E F)ᗮ ⊓ (d.targetSubspace)ᗮ =
      Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
        (LinearMap.ker (d.sin₁ : F →ₗ[𝕜] F)) := by
  refine Submodule.ext fun z => ?_
  constructor
  · intro hz
    obtain ⟨hzU, hzV⟩ := Submodule.mem_inf.mp hz
    rw [mem_sourceSubspace_orthogonal_iff] at hzU
    rw [d.mem_targetSubspace_orthogonal_iff, hzU] at hzV
    simp only [map_zero, zero_add] at hzV
    rw [d.sin₀_adjoint_intertwiner] at hzV
    have hs : d.sin₁ (WithLp.ofLp z).2 = 0 := by
      have h := d.coisometry_on_sin₁_apply (WithLp.ofLp z).2
      rw [hzV, map_zero] at h
      exact h.symm
    exact ⟨(WithLp.ofLp z).2, hs, (eq_modelInr_of_fst_eq_zero hzU).symm⟩
  · rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hy
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_sourceSubspace_orthogonal_iff]
      simp
    · rw [d.mem_targetSubspace_orthogonal_iff]
      simp only [ContinuousLinearMap.coe_coe, modelInr_apply, WithLp.ofLp_toLp, map_zero,
        zero_add]
      rw [d.sin₀_adjoint_intertwiner, hy, map_zero]

/-- **`Uᗮ ⊓ V` is the angle-`π/2` eigenspace on the `Pᗮ`-side.** -/
theorem halmosTargetDefect_eq :
    (sourceSubspace 𝕜 E F)ᗮ ⊓ d.targetSubspace =
      Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
        (LinearMap.ker (d.cos₁ : F →ₗ[𝕜] F)) := by
  refine Submodule.ext fun z => ?_
  constructor
  · intro hz
    obtain ⟨hzU, a, rfl⟩ := Submodule.mem_inf.mp hz
    rw [mem_sourceSubspace_orthogonal_iff] at hzU
    simp only [ContinuousLinearMap.coe_coe, realizingIsometry_apply,
      WithLp.ofLp_toLp] at hzU
    refine ⟨d.intertwiner (d.sin₀ a), ?_, ?_⟩
    · simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [← d.map_cos_apply, d.commute₀_apply, hzU, map_zero, map_zero]
    · simp only [ContinuousLinearMap.coe_coe, modelInr_apply, realizingIsometry_apply]
      rw [hzU]
  · rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hy
    have h1 : d.cos₀ (ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ y)) = 0 := by
      rw [d.cos₀_adjoint_intertwiner, d.commute₁_apply, hy, map_zero, map_zero]
    have h2 : d.intertwiner (d.sin₀
        (ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ y))) = y := by
      rw [d.sin₀_adjoint_intertwiner, d.coisometry_on_sin₁_apply]
      exact d.sin₁_sin₁_of_cos₁_eq_zero hy
    refine Submodule.mem_inf.mpr ⟨?_, ⟨ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ y), ?_⟩⟩
    · rw [mem_sourceSubspace_orthogonal_iff]
      simp
    · simp only [realizingIsometry_apply, h1, h2, ContinuousLinearMap.coe_coe, modelInr_apply]

/-! ### Why `0` is exceptional and `π/2` is not

The crossed defects are forced to agree; the uncrossed ones are not. -/

/-- **The intertwiner restricts to a linear isometric equivalence of the two
angle-`π/2` eigenspaces.**

This is where the paper's admissibility condition at `π/2` comes from.  The
angle-`π/2` space `ker cos₀` lies inside the range of `sin₀`, on which `J₀` is
isometric, and symmetrically on the other side — so the multiplicity at `π/2`
*must* agree.  Contrast `ker sin₀` and `ker sin₁`, which `J₀` annihilates,
respectively misses entirely. -/
noncomputable def crossedDefectEquiv :
    LinearMap.ker (d.cos₀ : E →ₗ[𝕜] E) ≃ₗᵢ[𝕜] LinearMap.ker (d.cos₁ : F →ₗ[𝕜] F) where
  toFun x := ⟨d.intertwiner (x : E), by
    have hx : d.cos₀ (x : E) = 0 := x.2
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    rw [← d.map_cos_apply, hx, map_zero]⟩
  invFun y := ⟨ContinuousLinearMap.adjoint d.intertwiner (y : F), by
    have hy : d.cos₁ (y : F) = 0 := y.2
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    rw [d.cos₀_adjoint_intertwiner, hy, map_zero]⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  left_inv x := by
    have hsq : d.sin₀ (d.sin₀ (x : E)) = (x : E) := d.sin₀_sin₀_of_cos₀_eq_zero x.2
    ext
    change ContinuousLinearMap.adjoint d.intertwiner (d.intertwiner (x : E)) = (x : E)
    conv_lhs => rw [← hsq]
    rw [d.isometry_on_sin₀_apply, hsq]
  right_inv y := by
    have hsq : d.sin₁ (d.sin₁ (y : F)) = (y : F) := d.sin₁_sin₁_of_cos₁_eq_zero y.2
    ext
    change d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner (y : F)) = (y : F)
    conv_lhs => rw [← hsq]
    rw [d.coisometry_on_sin₁_apply, hsq]
  norm_map' x := by
    have hsq : d.sin₀ (d.sin₀ (x : E)) = (x : E) := d.sin₀_sin₀_of_cos₀_eq_zero x.2
    change ‖d.intertwiner (x : E)‖ = ‖(x : E)‖
    conv_lhs => rw [← hsq]
    rw [d.norm_intertwiner_sin₀, hsq]

/-- **The two crossed defects of the realized pair are isometric.**

`U ⊓ Vᗮ ≃ₗᵢ Uᗮ ⊓ V`: the paper's admissibility condition at `π/2` is not an extra
hypothesis on the datum, it is a *consequence* of the construction.  It is also
exactly the condition for a unitary of the ambient space to carry `U` onto `V`. -/
theorem nonempty_halmosSourceDefect_equiv_targetDefect :
    Nonempty (↥(sourceSubspace 𝕜 E F ⊓ (d.targetSubspace)ᗮ) ≃ₗᵢ[𝕜]
      ↥((sourceSubspace 𝕜 E F)ᗮ ⊓ d.targetSubspace)) := by
  refine ⟨(LinearIsometryEquiv.ofEq _ _ d.halmosSourceDefect_eq).trans
    (((submoduleMapIsometry (modelInl 𝕜 E F) norm_modelInl
        (LinearMap.ker (d.cos₀ : E →ₗ[𝕜] E))).symm.trans d.crossedDefectEquiv).trans
      ((submoduleMapIsometry (modelInr 𝕜 E F) norm_modelInr
        (LinearMap.ker (d.cos₁ : F →ₗ[𝕜] F))).trans
        (LinearIsometryEquiv.ofEq _ _ d.halmosTargetDefect_eq.symm)))⟩

end HalmosAngleDatum

/-! ## The multiplicity at angle `0` is genuinely unconstrained -/

section Trivial

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (F : Type v) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The datum with every angle equal to `0`: `cos Θ = 1`, `sin Θ = 0`, and no
intertwiner at all.  Its two `0`-eigenspaces are all of `E` and all of `F`, which
are arbitrary and unrelated — the machine-checked witness that the multiplicity
at angle `0` may differ between the two sides. -/
noncomputable def trivialHalmosAngleDatum : HalmosAngleDatum 𝕜 E F where
  cos₀ := 1
  sin₀ := 0
  cos₁ := 1
  sin₁ := 0
  intertwiner := 0
  isSelfAdjoint_cos₀ := IsSelfAdjoint.one _
  isSelfAdjoint_sin₀ := IsSelfAdjoint.zero _
  isSelfAdjoint_cos₁ := IsSelfAdjoint.one _
  isSelfAdjoint_sin₁ := IsSelfAdjoint.zero _
  commute₀ := by ext x; simp
  commute₁ := by ext y; simp
  pythagoras₀ := by ext x; simp
  pythagoras₁ := by ext y; simp
  map_cos := by ext x; simp
  map_sin := by ext x; simp
  isometry_on_sin₀ := by ext x; simp
  coisometry_on_sin₁ := by ext y; simp

/-- The all-`0` datum has vanishing `sin Θ₀`. -/
@[simp]
theorem trivialHalmosAngleDatum_sin₀ :
    (trivialHalmosAngleDatum 𝕜 E F).sin₀ = 0 := rfl

/-- The all-`0` datum has vanishing `sin Θ₁`. -/
@[simp]
theorem trivialHalmosAngleDatum_sin₁ :
    (trivialHalmosAngleDatum 𝕜 E F).sin₁ = 0 := rfl

/-- For the all-`0` datum the two subspaces coincide, so `U ⊓ V` is the whole
`E`-factor: the multiplicity at angle `0` on the `P`-side is `dim E`. -/
theorem trivial_halmosCommonPart_eq :
    sourceSubspace 𝕜 E F ⊓ (trivialHalmosAngleDatum 𝕜 E F).targetSubspace =
      sourceSubspace 𝕜 E F := by
  rw [(trivialHalmosAngleDatum 𝕜 E F).halmosCommonPart_eq, trivialHalmosAngleDatum_sin₀,
    show LinearMap.ker ((0 : E →L[𝕜] E) : E →ₗ[𝕜] E) = ⊤ by ext x; simp,
    Submodule.map_top]
  rfl

/-- Symmetrically, `Uᗮ ⊓ Vᗮ` is the whole `F`-factor: the multiplicity at angle
`0` on the `Pᗮ`-side is `dim F`.  `E` and `F` are arbitrary, so the two
multiplicities are unrelated. -/
theorem trivial_halmosExteriorPart_eq :
    (sourceSubspace 𝕜 E F)ᗮ ⊓ ((trivialHalmosAngleDatum 𝕜 E F).targetSubspace)ᗮ =
      Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F)) ⊤ := by
  rw [(trivialHalmosAngleDatum 𝕜 E F).halmosExteriorPart_eq, trivialHalmosAngleDatum_sin₁,
    show LinearMap.ker ((0 : F →L[𝕜] F) : F →ₗ[𝕜] F) = ⊤ by ext y; simp]

end Trivial

/-! ## The direct sum of two angle data

Admissibility is a conjunction of operator identities, every one of which is
blockwise, so two admissible data can be added.  This is what lets a prescribed
angle *sequence* be combined with a prescribed angle-`0` multiplicity: the
sequence lives on one summand, the all-`0` datum on the other, and
`trivialHalmosAngleDatum` puts an arbitrary and independent Hilbert space on each
side of the second summand. -/

section Product

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']

/-- **The direct sum of two admissible angle data.**

Every block is the block-diagonal sum of the corresponding blocks, and every
axiom of `HalmosAngleDatum` is verified blockwise by `blockMap_comp`,
`blockMap_add` and `blockMap_one`.  In particular the intertwiner of the sum is
the sum of the intertwiners, so the `π/2` multiplicities of the two summands are
matched independently. -/
noncomputable def HalmosAngleDatum.prod (d : HalmosAngleDatum 𝕜 E F)
    (d' : HalmosAngleDatum 𝕜 E' F') :
    HalmosAngleDatum 𝕜 (WithLp 2 (E × E')) (WithLp 2 (F × F')) where
  cos₀ := blockMap d.cos₀ d'.cos₀
  sin₀ := blockMap d.sin₀ d'.sin₀
  cos₁ := blockMap d.cos₁ d'.cos₁
  sin₁ := blockMap d.sin₁ d'.sin₁
  intertwiner := blockMap d.intertwiner d'.intertwiner
  isSelfAdjoint_cos₀ := isSelfAdjoint_blockMap d.isSelfAdjoint_cos₀ d'.isSelfAdjoint_cos₀
  isSelfAdjoint_sin₀ := isSelfAdjoint_blockMap d.isSelfAdjoint_sin₀ d'.isSelfAdjoint_sin₀
  isSelfAdjoint_cos₁ := isSelfAdjoint_blockMap d.isSelfAdjoint_cos₁ d'.isSelfAdjoint_cos₁
  isSelfAdjoint_sin₁ := isSelfAdjoint_blockMap d.isSelfAdjoint_sin₁ d'.isSelfAdjoint_sin₁
  commute₀ := by rw [blockMap_comp, blockMap_comp, d.commute₀, d'.commute₀]
  commute₁ := by rw [blockMap_comp, blockMap_comp, d.commute₁, d'.commute₁]
  pythagoras₀ := by
    rw [blockMap_comp, blockMap_comp, blockMap_add, d.pythagoras₀, d'.pythagoras₀,
      blockMap_one]
  pythagoras₁ := by
    rw [blockMap_comp, blockMap_comp, blockMap_add, d.pythagoras₁, d'.pythagoras₁,
      blockMap_one]
  map_cos := by rw [blockMap_comp, blockMap_comp, d.map_cos, d'.map_cos]
  map_sin := by rw [blockMap_comp, blockMap_comp, d.map_sin, d'.map_sin]
  isometry_on_sin₀ := by
    rw [adjoint_blockMap, blockMap_comp, blockMap_comp, d.isometry_on_sin₀,
      d'.isometry_on_sin₀]
  coisometry_on_sin₁ := by
    rw [adjoint_blockMap, blockMap_comp, blockMap_comp, d.coisometry_on_sin₁,
      d'.coisometry_on_sin₁]

/-- The `P`-side sine of a direct sum is the direct sum of the sines. -/
@[simp]
theorem HalmosAngleDatum.prod_sin₀ (d : HalmosAngleDatum 𝕜 E F)
    (d' : HalmosAngleDatum 𝕜 E' F') :
    (d.prod d').sin₀ = blockMap d.sin₀ d'.sin₀ := rfl

/-- The `Pᗮ`-side sine of a direct sum is the direct sum of the sines. -/
@[simp]
theorem HalmosAngleDatum.prod_sin₁ (d : HalmosAngleDatum 𝕜 E F)
    (d' : HalmosAngleDatum 𝕜 E' F') :
    (d.prod d').sin₁ = blockMap d.sin₁ d'.sin₁ := rfl

end Product

/-! ## A datum built from a single pair of intertwined angle operators

`HalmosAngleDatum` records `cos Θ₀, sin Θ₀, cos Θ₁, sin Θ₁` and their
intertwiner as *independent* data, because that is the shape Theorem 3.1's
realization half consumes.  The mathematics behind the shape is smaller: there
is one angle operator on each side, and one map between them.  This section
supplies the constructor that says so.

Given self-adjoint `Θ₀ : E →L[𝕜] E` and `Θ₁ : F →L[𝕜] F` and a single
`J : E →L[𝕜] F` with `J Θ₀ = Θ₁ J`, six of the datum's twelve axioms are
*derived* rather than assumed:

* `commute₀`, `commute₁` — `cos` and `sin` commute as symbols, and the
  functional calculus is an algebra map;
* `pythagoras₀`, `pythagoras₁` — `cos² + sin² = 1` as symbols;
* `map_cos`, `map_sin` — `TauCeti.LinearPMap.cfc_intertwines_selfAdjoint`
  carries `J Θ₀ = Θ₁ J` to every symbol continuous on the union of the two real
  spectra, by Stone--Weierstrass.

The four self-adjointness axioms are `cfc_predicate`.  What is *not* derivable
is the last pair: `J` isometric on `ran sin Θ₀` and co-isometric onto
`ran sin Θ₁` is a statement about spectral *multiplicities*, invisible to a
functional calculus of one operator at a time, so those stay hypotheses.

**No confinement of the spectra is required.**  One expects to have to assume
`spectrum ℝ Θᵢ ⊆ [0, π/2]`, and for `Θᵢ` to *deserve the name* "angle operator"
one does — that is what makes `cos Θᵢ` and `sin Θᵢ` nonnegative, hence what lets
`Θᵢ` be recovered from the datum.  But `HalmosAngleDatum` records no
nonnegativity, and none of the six derived axioms uses one: `cos² + sin² = 1`
and `J f(Θ₀) = f(Θ₁) J` hold on all of `ℝ`.  Adding the hypothesis would narrow
the constructor without strengthening anything it produces, so it is omitted. -/

section OfIntertwinedAngles

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **The angle datum of a pair of intertwined self-adjoint angle operators.**

`cos Θᵢ` and `sin Θᵢ` are the continuous functional calculus of the two angle
operators, and the intertwiner is the given `J`.  Every axiom except the last
two is proved from the functional calculus; see the section preamble for which
and why.  The two partial-isometry axioms are the caller's, because they are
multiplicity statements that no functional calculus can supply.

The real functional calculi on `E` and `F` are supplied by the local `RCLike` operator
instances. -/
noncomputable def HalmosAngleDatum.ofIntertwinedAngles
    {Θ₀ : E →L[𝕜] E} {Θ₁ : F →L[𝕜] F}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (J : E →L[𝕜] F) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
    (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
    (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁) :
    HalmosAngleDatum 𝕜 E F where
  cos₀ := cfc Real.cos Θ₀
  sin₀ := cfc Real.sin Θ₀
  cos₁ := cfc Real.cos Θ₁
  sin₁ := cfc Real.sin Θ₁
  intertwiner := J
  isSelfAdjoint_cos₀ := cfc_predicate _ _
  isSelfAdjoint_sin₀ := cfc_predicate _ _
  isSelfAdjoint_cos₁ := cfc_predicate _ _
  isSelfAdjoint_sin₁ := cfc_predicate _ _
  commute₀ := by
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
      ← cfc_mul Real.cos Real.sin Θ₀ Real.continuous_cos.continuousOn
        Real.continuous_sin.continuousOn,
      ← cfc_mul Real.sin Real.cos Θ₀ Real.continuous_sin.continuousOn
        Real.continuous_cos.continuousOn]
    exact cfc_congr fun x _ => mul_comm _ _
  commute₁ := by
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
      ← cfc_mul Real.cos Real.sin Θ₁ Real.continuous_cos.continuousOn
        Real.continuous_sin.continuousOn,
      ← cfc_mul Real.sin Real.cos Θ₁ Real.continuous_sin.continuousOn
        Real.continuous_cos.continuousOn]
    exact cfc_congr fun x _ => mul_comm _ _
  pythagoras₀ := by
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
      ← cfc_mul Real.cos Real.cos Θ₀ Real.continuous_cos.continuousOn
        Real.continuous_cos.continuousOn,
      ← cfc_mul Real.sin Real.sin Θ₀ Real.continuous_sin.continuousOn
        Real.continuous_sin.continuousOn,
      ← cfc_add (a := Θ₀) (fun x => Real.cos x * Real.cos x)
        (fun x => Real.sin x * Real.sin x) (by fun_prop) (by fun_prop),
      ← cfc_one ℝ Θ₀ hΘ₀]
    exact cfc_congr fun x _ => by
      simpa [pow_two] using Real.cos_sq_add_sin_sq x
  pythagoras₁ := by
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
      ← cfc_mul Real.cos Real.cos Θ₁ Real.continuous_cos.continuousOn
        Real.continuous_cos.continuousOn,
      ← cfc_mul Real.sin Real.sin Θ₁ Real.continuous_sin.continuousOn
        Real.continuous_sin.continuousOn,
      ← cfc_add (a := Θ₁) (fun x => Real.cos x * Real.cos x)
        (fun x => Real.sin x * Real.sin x) (by fun_prop) (by fun_prop),
      ← cfc_one ℝ Θ₁ hΘ₁]
    exact cfc_congr fun x _ => by
      simpa [pow_two] using Real.cos_sq_add_sin_sq x
  map_cos :=
    TauCeti.LinearPMap.cfc_intertwines_selfAdjoint hΘ₁ hΘ₀ hJ
      Real.continuous_cos.continuousOn
  map_sin :=
    TauCeti.LinearPMap.cfc_intertwines_selfAdjoint hΘ₁ hΘ₀ hJ
      Real.continuous_sin.continuousOn
  isometry_on_sin₀ := hisom
  coisometry_on_sin₁ := hcoisom

variable {Θ₀ : E →L[𝕜] E} {Θ₁ : F →L[𝕜] F}
  (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁) (J : E →L[𝕜] F)
  (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
  (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
  (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁)

/-- The `P`-side cosine of the constructed datum is `cos Θ₀`. -/
@[simp]
theorem HalmosAngleDatum.ofIntertwinedAngles_cos₀ :
    (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).cos₀
      = cfc Real.cos Θ₀ := rfl

/-- The `P`-side sine of the constructed datum is `sin Θ₀`. -/
@[simp]
theorem HalmosAngleDatum.ofIntertwinedAngles_sin₀ :
    (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).sin₀
      = cfc Real.sin Θ₀ := rfl

/-- The `Pᗮ`-side cosine of the constructed datum is `cos Θ₁`. -/
@[simp]
theorem HalmosAngleDatum.ofIntertwinedAngles_cos₁ :
    (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).cos₁
      = cfc Real.cos Θ₁ := rfl

/-- The `Pᗮ`-side sine of the constructed datum is `sin Θ₁`. -/
@[simp]
theorem HalmosAngleDatum.ofIntertwinedAngles_sin₁ :
    (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).sin₁
      = cfc Real.sin Θ₁ := rfl

/-- The constructed datum's intertwiner is the given `J`. -/
@[simp]
theorem HalmosAngleDatum.ofIntertwinedAngles_intertwiner :
    (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).intertwiner
      = J := rfl

end OfIntertwinedAngles

end DavisKahan
end TauCeti
