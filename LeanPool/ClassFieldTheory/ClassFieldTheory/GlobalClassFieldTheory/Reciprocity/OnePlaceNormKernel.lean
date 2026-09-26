/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
/-!
# The one-place norm kernel

At the source level, the key calculation is that an idele supported at one
finite place is a global relative-idele norm exactly when its local component
is a norm from the corresponding local tensor algebra.  The determinant-norm
comparison then identifies this image with the norm group of any chosen
completion above the place.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The image of the global norm on relative ideles. -/
def ideleNormSubgroup :
    Subgroup (IdeleGroup K) :=
  (RelativeIdeleGroup.norm K L).range

/-- The raw idele norm quotient.  Passing further to principal-idèle
classes gives the class quotient used in the global reciprocity theorem. -/
abbrev IdeleNormQuotient :=
  IdeleGroup K ⧸ ideleNormSubgroup (K := K) (L := L)

/-- The projection to the raw global norm quotient. -/
def ideleNormClass :
    IdeleGroup K →* IdeleNormQuotient (K := K) (L := L) :=
  QuotientGroup.mk' (ideleNormSubgroup (K := K) (L := L))

omit [NumberField L] [IsGalois K L] in
/-- A relative idele supported at an archimedean place has norm equal
to the one-place idele of its local determinant norm. -/
theorem norm_relativeInfinitePlaceIdele
    (v : InfinitePlace K)
    (z : (v.Completion ⊗[K] L)ˣ) :
    RelativeIdeleGroup.norm K L
        (relativeInfinitePlaceIdele
          (K := K) (L := L) v z) =
      infinitePlaceIdele v
        (infiniteTensorDetNorm
          (K := K) (L := L) v z) := by
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      IdeleGroup.infiniteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeInfinitePlaceIdele
              (K := K) (L := L) v z)) =
        IdeleGroup.infiniteComponent w
          (infinitePlaceIdele v
            (infiniteTensorDetNorm
              (K := K) (L := L) v z))
    by_cases hw : w = v
    · subst w
      rw [RelativeIdeleGroup.infiniteComponent_norm,
        relativeInfinitePlaceIdele_infiniteComponent_same,
        infinitePlaceIdele_infiniteComponent_same]
      rfl
    · rw [RelativeIdeleGroup.infiniteComponent_norm,
        relativeInfinitePlaceIdele_infiniteComponent_of_ne
          v w z hw,
        map_one,
        infinitePlaceIdele_infiniteComponent_of_ne
          v w
          (infiniteTensorDetNorm
            (K := K) (L := L) v z) hw]
  · apply RestrictedProduct.ext
    intro w
    change
      IdeleGroup.finiteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeInfinitePlaceIdele
              (K := K) (L := L) v z)) =
        IdeleGroup.finiteComponent w
          (infinitePlaceIdele v
            (infiniteTensorDetNorm
              (K := K) (L := L) v z))
    rw [RelativeIdeleGroup.finiteComponent_norm,
      relativeInfinitePlaceIdele_finiteComponent,
      map_one,
      infinitePlaceIdele_finiteComponent]

omit [NumberField L] [IsGalois K L] in
/-- Exact archimedean one-place intersection before quotienting by
principal ideles:

`N(I_L) ∩ K_vˣ = N((K_v ⊗_K L)ˣ)`.
-/
theorem infinitePlaceIdele_mem_ideleNormSubgroup_iff
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    infinitePlaceIdele v x ∈
        ideleNormSubgroup (K := K) (L := L) ↔
      x ∈ infiniteTensorNormSubgroup
        (K := K) (L := L) v := by
  constructor
  · rintro ⟨a, ha⟩
    refine
      ⟨RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) v a, ?_⟩
    have hcomponent :=
      congrArg (IdeleGroup.infiniteComponent v) ha
    rw [RelativeIdeleGroup.infiniteComponent_norm,
      infinitePlaceIdele_infiniteComponent_same] at hcomponent
    exact hcomponent
  · rintro ⟨z, rfl⟩
    exact
      ⟨relativeInfinitePlaceIdele
          (K := K) (L := L) v z,
        norm_relativeInfinitePlaceIdele
          (K := K) (L := L) v z⟩

omit [NumberField L] [IsGalois K L] in
/-- Kernel-exact form of the archimedean one-place norm statement. -/
theorem ideleNormClass_comp_infinitePlaceIdele_ker
    (v : InfinitePlace K) :
    ((ideleNormClass (K := K) (L := L)).comp
        (infinitePlaceIdele v)).ker =
      infiniteTensorNormSubgroup
        (K := K) (L := L) v := by
  ext x
  change
    QuotientGroup.mk'
        (ideleNormSubgroup (K := K) (L := L))
        (infinitePlaceIdele v x) = 1 ↔
      x ∈ infiniteTensorNormSubgroup
        (K := K) (L := L) v
  exact
    (QuotientGroup.eq_one_iff
      (infinitePlaceIdele v x)).trans
      (infinitePlaceIdele_mem_ideleNormSubgroup_iff
        (K := K) (L := L) v x)

omit [NumberField L] [IsGalois K L] in
/-- A relative idele supported at `v` has norm equal to the one-place
idele of its local determinant norm. -/
theorem norm_relativeFinitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    RelativeIdeleGroup.norm K L
        (relativeFinitePlaceIdele (K := K) (L := L) v z) =
      finitePlaceIdele v
        (localTensorNorm (K := K) (L := L) v z) := by
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      IdeleGroup.infiniteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeFinitePlaceIdele
              (K := K) (L := L) v z)) =
        IdeleGroup.infiniteComponent w
          (finitePlaceIdele v
            (localTensorNorm (K := K) (L := L) v z))
    rw [RelativeIdeleGroup.infiniteComponent_norm,
      relativeFinitePlaceIdele_infiniteComponent,
      map_one, finitePlaceIdele_infiniteComponent]
  · apply RestrictedProduct.ext
    intro w
    change
      IdeleGroup.finiteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeFinitePlaceIdele
              (K := K) (L := L) v z)) =
        IdeleGroup.finiteComponent w
          (finitePlaceIdele v
            (localTensorNorm (K := K) (L := L) v z))
    by_cases hw : w = v
    · subst w
      rw [RelativeIdeleGroup.finiteComponent_norm,
        relativeFinitePlaceIdele_finiteComponent_same,
        finitePlaceIdele_finiteComponent_same]
    · rw [RelativeIdeleGroup.finiteComponent_norm,
        relativeFinitePlaceIdele_finiteComponent_of_ne v w z hw,
        map_one,
        finitePlaceIdele_finiteComponent_of_ne v w
          (localTensorNorm (K := K) (L := L) v z) hw]

omit [NumberField L] [IsGalois K L] in
/-- Exact one-place intersection before quotienting by principal ideles:

`N(I_L) ∩ K_vˣ = N((K_v ⊗_K L)ˣ)`.
-/
theorem finitePlaceIdele_mem_ideleNormSubgroup_iff
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    finitePlaceIdele v x ∈
        ideleNormSubgroup (K := K) (L := L) ↔
      x ∈ (localTensorNorm (K := K) (L := L) v).range := by
  constructor
  · rintro ⟨a, ha⟩
    refine
      ⟨RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) v a, ?_⟩
    have hcomponent :=
      congrArg (IdeleGroup.finiteComponent v) ha
    rw [RelativeIdeleGroup.finiteComponent_norm,
      finitePlaceIdele_finiteComponent_same] at hcomponent
    exact hcomponent
  · rintro ⟨z, rfl⟩
    exact
      ⟨relativeFinitePlaceIdele
          (K := K) (L := L) v z,
        norm_relativeFinitePlaceIdele
          (K := K) (L := L) v z⟩

omit [NumberField L] in
/-- The finite-place tensor form with the actual chosen completion
norm group. -/
theorem finitePlaceIdele_mem_ideleNormSubgroup_iff_chosenLocalNorm
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    finitePlaceIdele v x ∈
        ideleNormSubgroup (K := K) (L := L) ↔
      x ∈ chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  rw [finitePlaceIdele_mem_ideleNormSubgroup_iff
    (K := K) (L := L)]
  exact SetLike.ext_iff.mp
    (finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
      (K := K) (L := L) v) x

/-- A chosen local norm at one finite place gives an actual global
idele-class norm.  The witness is the relative idele supported at that
place, transported to an ordinary idele of the extension field. -/
theorem finitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_chosenLocalNorm
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (hx :
      x ∈ chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v) :
    IdeleGroup.finitePlaceIdeleClass v x ∈
      (_root_.ideleClassNorm K L).range := by
  have hnorm :
      IdeleGroup.finitePlaceIdele v x ∈
        ideleNormSubgroup (K := K) (L := L) :=
    (finitePlaceIdele_mem_ideleNormSubgroup_iff_chosenLocalNorm
      (K := K) (L := L) v x).2 hx
  obtain ⟨z, hz⟩ := hnorm
  refine
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (_root_.relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z), ?_⟩
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.norm K L
          (_root_.relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) z)) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.finitePlaceIdele v x)
  rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv, hz]

omit [NumberField L] in
/-- Kernel-exact form of the one-place norm statement. -/
theorem ideleNormClass_comp_finitePlaceIdele_ker
    (v : HeightOneSpectrum (𝓞 K)) :
    ((ideleNormClass (K := K) (L := L)).comp
        (finitePlaceIdele v)).ker =
      chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  ext x
  change
    ideleNormClass (K := K) (L := L)
        (finitePlaceIdele v x) = 1 ↔
      x ∈ chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v
  change
    QuotientGroup.mk'
        (ideleNormSubgroup (K := K) (L := L))
        (finitePlaceIdele v x) = 1 ↔
      x ∈ chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v
  constructor
  · intro hx
    have hmem :
        finitePlaceIdele v x ∈
          ideleNormSubgroup (K := K) (L := L) :=
      (QuotientGroup.eq_one_iff
        (N := ideleNormSubgroup (K := K) (L := L))
        (x := finitePlaceIdele v x)).mp hx
    exact
      (finitePlaceIdele_mem_ideleNormSubgroup_iff_chosenLocalNorm
        (K := K) (L := L) v x).mp hmem
  · intro hx
    apply
      (QuotientGroup.eq_one_iff
        (N := ideleNormSubgroup (K := K) (L := L))
        (x := finitePlaceIdele v x)).mpr
    exact
      (finitePlaceIdele_mem_ideleNormSubgroup_iff_chosenLocalNorm
        (K := K) (L := L) v x).mpr hx

end Reciprocity
end GlobalClassFieldTheory
