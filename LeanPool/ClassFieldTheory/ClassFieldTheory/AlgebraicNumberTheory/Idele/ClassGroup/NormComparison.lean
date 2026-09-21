/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleClassBaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.EmbeddingNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
/-!
# Relative and ordinary idele-class norms

The determinant norm on relative ideles and the ordinary idele norm give
the same map after the canonical scalar-extension equivalence
`C(𝔸_K ⊗_K L) ≃ C_L`.  This comparison lets the cohomological results
proved in relative coordinates be stated with the usual norm
`N_{L/K} : C_L → C_K`.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace RelativeIdeleGroup

universe u v w

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]

/-- A field embedding into an ambient finite extension, descended from
relative ideles to the existing relative idele class groups. -/
noncomputable def classEmbedding
    (f : L →ₐ[K] M) :
    RelativeIdeleGroup.ClassGroup K L →*
      RelativeIdeleGroup.ClassGroup K M :=
  QuotientGroup.map
    (RelativeIdeleGroup.principalSubgroup K L)
    (RelativeIdeleGroup.principalSubgroup K M)
    (RelativeIdeleGroup.ideleEmbedding f)
    (by
      rintro _ ⟨x, rfl⟩
      refine ⟨Units.map f x, ?_⟩
      apply Units.ext
      rfl)

omit [FiniteDimensional K L] [FiniteDimensional K M] in
@[simp]
theorem classEmbedding_mk
    (f : L →ₐ[K] M)
    (a : RelativeIdeleGroup K L) :
    classEmbedding f
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (RelativeIdeleGroup.ideleEmbedding f a) :=
  rfl

omit [FiniteDimensional K L] [FiniteDimensional K M] in
/-- Scalar extension on relative idele classes respects composition. -/
theorem classEmbedding_comp {N : Type*} [Field N] [Algebra K N]
    (g : M →ₐ[K] N) (f : L →ₐ[K] M)
    (c : RelativeIdeleGroup.ClassGroup K L) :
    classEmbedding g (classEmbedding f c) = classEmbedding (g.comp f) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  apply congrArg (QuotientGroup.mk' (RelativeIdeleGroup.principalSubgroup K N))
  apply Units.ext
  exact congrArg (fun h => h (a : RelativeAdeleRing K L))
    (Algebra.TensorProduct.map_id_comp
      (S := NumberField.AdeleRing (𝓞 K) K)
      (A := NumberField.AdeleRing (𝓞 K) K) g f).symm

/-- The Galois product formula after descent to relative idele classes. -/
theorem classInclusion_ideleClassNorm_eq_prod_conjugates
    [IsGalois K L]
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classInclusion K L
        (RelativeIdeleGroup.classNorm K L c) =
      ∏ σ : L ≃ₐ[K] L, σ • c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)
        (RelativeIdeleGroup.inclusion K L
          (RelativeIdeleGroup.norm K L a)) =
      ∏ σ : L ≃ₐ[K] L,
        QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (σ • a)
  rw [RelativeIdeleGroup.inclusion_norm_eq_prod_conjugates]
  exact map_prod
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K L))
    (fun σ : L ≃ₐ[K] L => σ • a)
    Finset.univ

variable [Algebra L M] [IsScalarTower K L M] [IsGalois K M]

local instance fixingSubextensionQuotientFintype :
    Fintype
      ((M ≃ₐ[K] M) ⧸
        RelativeIdeleGroup.fixingSubextension
          (K := K) (L := L) (M := M)) :=
  Fintype.ofFinite _

/-- The embedded-subextension norm formula after descent to relative
idele classes.  No normality of `L / K` is assumed. -/
theorem classInclusion_ideleClassNorm_eq_prod_embeddings
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classInclusion K M
        (RelativeIdeleGroup.classNorm K L c) =
      ∏ f : L →ₐ[K] M,
        RelativeIdeleGroup.classEmbedding f c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (RelativeIdeleGroup.inclusion K M
          (RelativeIdeleGroup.norm K L a)) =
      ∏ f : L →ₐ[K] M,
        QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K M)
          (RelativeIdeleGroup.ideleEmbedding f a)
  rw [RelativeIdeleGroup.inclusion_norm_eq_prod_embeddings]
  exact map_prod
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K M))
    (fun f : L →ₐ[K] M =>
      RelativeIdeleGroup.ideleEmbedding f a)
    Finset.univ

/-- Coset form of the embedded-subextension norm formula on relative
idele classes. -/
theorem classInclusion_ideleClassNorm_eq_prod_galoisCosets
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classInclusion K M
        (RelativeIdeleGroup.classNorm K L c) =
      ∏ q :
          (M ≃ₐ[K] M) ⧸
            RelativeIdeleGroup.fixingSubextension
              (K := K) (L := L) (M := M),
        RelativeIdeleGroup.classEmbedding
          (RelativeIdeleGroup.cosetEquivEmbedding q) c := by
  calc
    RelativeIdeleGroup.classInclusion K M
        (RelativeIdeleGroup.classNorm K L c) =
        ∏ f : L →ₐ[K] M,
          RelativeIdeleGroup.classEmbedding f c :=
      RelativeIdeleGroup.classInclusion_ideleClassNorm_eq_prod_embeddings c
    _ =
        ∏ q :
            (M ≃ₐ[K] M) ⧸
              RelativeIdeleGroup.fixingSubextension
                (K := K) (L := L) (M := M),
          RelativeIdeleGroup.classEmbedding
            (RelativeIdeleGroup.cosetEquivEmbedding q) c := by
      exact
        ((RelativeIdeleGroup.cosetEquivEmbedding
          (K := K) (L := L) (M := M)).prod_comp
            (fun f ↦ RelativeIdeleGroup.classEmbedding f c)).symm

end RelativeIdeleGroup

variable
    {K L : Type*}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]

omit [IsGalois K L] in
/-- The relative determinant norm is the ordinary idele-class norm after
the canonical base-change equivalence. -/
@[simp]
theorem ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
    (c : RelativeIdeleGroup.ClassGroup K L) :
    _root_.ideleClassNorm K L
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L) c) =
      RelativeIdeleGroup.classNorm K L c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.norm K L
          (relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) a)) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (RelativeIdeleGroup.norm K L a)
  rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv]

omit [IsGalois K L] in
/-- The ordinary and relative presentations define the same norm subgroup
of `C_K`. -/
theorem ordinaryIdeleClassNorm_range_eq_relative :
    (_root_.ideleClassNorm K L).range =
      (RelativeIdeleGroup.classNorm K L).range := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    refine
      ⟨(relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L)).symm d, ?_⟩
    simpa using
      (ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
        (K := K) (L := L)
        ((relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L)).symm d)).symm
  · rintro ⟨d, rfl⟩
    exact
      ⟨relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L) d,
        ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
          (K := K) (L := L) d⟩
