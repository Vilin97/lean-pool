/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
/-!
# Relative idele classes under an isomorphic realization

If two finite extensions of a number field are isomorphic over the base,
their tensor-product presentations of the relative adeles are canonically
isomorphic.  This file descends that canonical isomorphism to relative
ideles and idele classes and records compatibility with the determinant
norm.

The construction is the direct tensor-product congruence

`𝔸_K ⊗[K] L ≃ 𝔸_K ⊗[K] M`

induced by an algebra equivalence `L ≃ₐ[K] M`.  In particular, no second
model of relative adeles or of the idele-class norm is introduced.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField
open IsDedekindDomain

noncomputable
section

open RelativeIdeleGroup.Cohomology


universe u v w

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [Field M] [Algebra K M]

/-- A base-field algebra equivalence between two realizations of a finite
extension induces the canonical equivalence between their relative adele
algebras. -/
noncomputable def relativeAdeleCongr
    (e : L ≃ₐ[K] M) :
    RelativeAdeleRing K L ≃ₐ[NumberField.AdeleRing (𝓞 K) K]
      RelativeAdeleRing K M :=
  Algebra.TensorProduct.congr AlgEquiv.refl e

@[simp]
theorem relativeAdeleCongr_tmul
    (e : L ≃ₐ[K] M)
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L) :
    relativeAdeleCongr (K := K) e (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] e x :=
  rfl

/-- The canonical transport of relative ideles along an isomorphic
realization of the top field. -/
noncomputable def relativeIdeleCongr
    (e : L ≃ₐ[K] M) :
    RelativeIdeleGroup K L ≃*
      RelativeIdeleGroup K M :=
  Units.mapEquiv
    (relativeAdeleCongr (K := K) e).toMulEquiv

@[simp]
theorem relativeIdeleCongr_coe
    (e : L ≃ₐ[K] M)
    (a : RelativeIdeleGroup K L) :
    ((relativeIdeleCongr (K := K) e a :
        RelativeIdeleGroup K M) :
      RelativeAdeleRing K M) =
        relativeAdeleCongr (K := K) e
          (a : RelativeAdeleRing K L) :=
  rfl

/-- For an automorphism of the top field, canonical relative-idele
transport is the actual Galois action. -/
theorem relativeIdeleCongr_eq_smul
    (σ : L ≃ₐ[K] L)
    (a : RelativeIdeleGroup K L) :
    relativeIdeleCongr (K := K) σ a = σ • a :=
  rfl

/-- Transport of relative ideles sends a principal idele to the principal
idele of the transported field unit. -/
@[simp]
theorem relativeIdeleCongr_principalIdele
    (e : L ≃ₐ[K] M)
    (x : Lˣ) :
    relativeIdeleCongr (K := K) e
        (RelativeIdeleGroup.principalIdele K L x) =
      RelativeIdeleGroup.principalIdele K M
        (Units.mapEquiv e.toMulEquiv x) := by
  apply Units.ext
  change
    relativeAdeleCongr (K := K) e
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] (x : L)) =
      (1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] e (x : L)
  rfl

/-- The canonical transport identifies the two principal-relative-idele
subgroups. -/
theorem relativeIdelePrincipalSubgroup_map_congr
    (e : L ≃ₐ[K] M) :
    (RelativeIdeleGroup.principalSubgroup K L).map
        (relativeIdeleCongr (K := K) e) =
      RelativeIdeleGroup.principalSubgroup K M := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, rfl⟩
    rw [← hx]
    exact
      ⟨Units.mapEquiv e.toMulEquiv x,
        (relativeIdeleCongr_principalIdele
          (K := K) e x).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ :=
      (Units.mapEquiv e.toMulEquiv).surjective y
    exact
      ⟨RelativeIdeleGroup.principalIdele K L x,
        ⟨x, rfl⟩,
        relativeIdeleCongr_principalIdele
          (K := K) e x⟩

/-- The relative idele class group is unchanged when the top field is
replaced by an isomorphic realization. -/
noncomputable def relativeIdeleClassCongr
    (e : L ≃ₐ[K] M) :
    RelativeIdeleGroup.ClassGroup K L ≃*
      RelativeIdeleGroup.ClassGroup K M :=
  QuotientGroup.congr
    (RelativeIdeleGroup.principalSubgroup K L)
    (RelativeIdeleGroup.principalSubgroup K M)
    (relativeIdeleCongr (K := K) e)
    (relativeIdelePrincipalSubgroup_map_congr
      (K := K) e)

theorem relativeIdeleClassCongr_mk
    (e : L ≃ₐ[K] M)
    (a : RelativeIdeleGroup K L) :
    relativeIdeleClassCongr (K := K) e
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (relativeIdeleCongr (K := K) e a) :=
  rfl

/-- Transporting a relative idèle class along an equivalence and then
embedding it into a third relative idèle class group is the same as
embedding along the composite field embedding. -/
theorem RelativeIdeleGroup.classEmbedding_relativeIdeleClassCongr
    {N : Type*} [Field N] [Algebra K N]
    (e : L ≃ₐ[K] M)
    (f : M →ₐ[K] N)
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classEmbedding f
        (relativeIdeleClassCongr (K := K) e c) =
      RelativeIdeleGroup.classEmbedding
        (f.comp e.toAlgHom) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    RelativeIdeleGroup.classEmbedding f
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K M)
          (relativeIdeleCongr (K := K) e a)) =
      RelativeIdeleGroup.classEmbedding
        (f.comp e.toAlgHom)
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a)
  rw [RelativeIdeleGroup.classEmbedding_mk,
    RelativeIdeleGroup.classEmbedding_mk]
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K N))
  apply Units.ext
  change
    RelativeIdeleGroup.adeleEmbedding f
        (relativeAdeleCongr (K := K) e
          (a : RelativeAdeleRing K L)) =
      RelativeIdeleGroup.adeleEmbedding
        (f.comp e.toAlgHom)
        (a : RelativeAdeleRing K L)
  induction (a : RelativeAdeleRing K L) using
      TensorProduct.inductionOn with
  | tmul x y =>
      simp only [relativeAdeleCongr_tmul,
        RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul,
        AlgHom.coe_comp, Function.comp_apply]
      rfl
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The determinant norm on relative ideles is invariant under replacement
of the top field by an isomorphic realization. -/
@[simp]
theorem relativeIdeleCongr_norm
    (e : L ≃ₐ[K] M)
    (a : RelativeIdeleGroup K L) :
    RelativeIdeleGroup.norm K M
        (relativeIdeleCongr (K := K) e a) =
      RelativeIdeleGroup.norm K L a := by
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := K)).injective
  simp only [RelativeIdeleGroup.norm,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  apply Units.ext
  change
    Algebra.norm
        (NumberField.AdeleRing (𝓞 K) K)
        (relativeAdeleCongr (K := K) e
          (a : RelativeAdeleRing K L)) =
      Algebra.norm
        (NumberField.AdeleRing (𝓞 K) K)
        (a : RelativeAdeleRing K L)
  exact
    Algebra.norm_eq_of_algEquiv
      (relativeAdeleCongr (K := K) e)
      (a : RelativeAdeleRing K L)

section Norm

variable [FiniteDimensional K L] [FiniteDimensional K M]

/-- The descended idele-class norm is invariant under the canonical
transport of the relative idele class group. -/
@[simp]
theorem relativeIdeleClassCongr_ideleClassNorm
    (e : L ≃ₐ[K] M)
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classNorm K M
        (relativeIdeleClassCongr (K := K) e c) =
      RelativeIdeleGroup.classNorm K L c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (RelativeIdeleGroup.norm K M
          (relativeIdeleCongr (K := K) e a)) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (RelativeIdeleGroup.norm K L a)
  rw [relativeIdeleCongr_norm (K := K) e a]

/-- Isomorphic realizations of a finite extension have the same actual
idele-class norm subgroup in the base idele class group. -/
theorem ideleClassNorm_range_algEquiv
    (e : L ≃ₐ[K] M) :
    (RelativeIdeleGroup.classNorm K M).range =
      (RelativeIdeleGroup.classNorm K L).range := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    refine
      ⟨(relativeIdeleClassCongr
          (K := K) e).symm d, ?_⟩
    have h :=
      relativeIdeleClassCongr_ideleClassNorm
        (K := K) e
        ((relativeIdeleClassCongr
          (K := K) e).symm d)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  · rintro ⟨d, rfl⟩
    exact
      ⟨relativeIdeleClassCongr (K := K) e d,
        relativeIdeleClassCongr_ideleClassNorm
          (K := K) e d⟩

/-- Ordinary idele-class norm subgroups are invariant under a base-field equivalence. -/
theorem ordinaryIdeleClassNorm_range_algEquiv
    [NumberField L] [NumberField M] (e : L ≃ₐ[K] M) :
    (_root_.ideleClassNorm K L).range = (_root_.ideleClassNorm K M).range := by
  calc
    (_root_.ideleClassNorm K L).range = (RelativeIdeleGroup.classNorm K L).range :=
      ordinaryIdeleClassNorm_range_eq_relative (K := K) (L := L)
    _ = (RelativeIdeleGroup.classNorm K M).range :=
      (ideleClassNorm_range_algEquiv (K := K) e).symm
    _ = (_root_.ideleClassNorm K M).range :=
      (ordinaryIdeleClassNorm_range_eq_relative (K := K) (L := M)).symm

/-- The idele-class norm index is invariant under an isomorphic realization
of the top field. -/
theorem ideleClassNorm_index_algEquiv
    (e : L ≃ₐ[K] M) :
    (RelativeIdeleGroup.classNorm K M).range.index =
      (RelativeIdeleGroup.classNorm K L).range.index := by
  rw [ideleClassNorm_range_algEquiv
    (K := K) e]

end Norm

section Absolute

variable
    {K : Type u} {M : Type w}
    [Field K] [NumberField K] [Algebra ℚ K]
    [Field M] [NumberField M] [Algebra ℚ M]

/-- The canonical transport of ordinary adele rings along an equivalence
of number fields.  It is the existing relative-adele transport over `ℚ`,
conjugated by the relative-to-ordinary scalar-extension equivalences. -/
noncomputable def adeleCongr
    (e : K ≃ₐ[ℚ] M) :
    NumberField.AdeleRing (𝓞 K) K ≃+*
      NumberField.AdeleRing (𝓞 M) M :=
  (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).symm |>.trans
    ((relativeAdeleCongr (K := ℚ) e).toRingEquiv.trans
      (relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)))

/-- The relative-to-ordinary scalar-extension comparison is natural for
transport of the top number field. -/
theorem relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
    (e : K ≃ₐ[ℚ] M)
    (z : RelativeAdeleRing ℚ K) :
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e z) =
      adeleCongr e
        (relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) z) := by
  change
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e z) =
      relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e
          ((relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := K)).symm
            (relativeAdeleBaseChangeRingEquiv
              (K := ℚ) (L := K) z)))
  rw [RingEquiv.symm_apply_apply]

/-- Transport of ordinary adeles carries the diagonal field embedding to
the diagonal field embedding. -/
@[simp]
theorem adeleCongr_algebraMap
    (e : K ≃ₐ[ℚ] M)
    (x : K) :
    adeleCongr e
        (algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) x) =
      algebraMap M
        (NumberField.AdeleRing (𝓞 M) M) (e x) := by
  have hx :
      (relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K)).symm
          (algebraMap K
            (NumberField.AdeleRing (𝓞 K) K) x) =
        (1 : NumberField.AdeleRing (𝓞 ℚ) ℚ) ⊗ₜ[ℚ] x := by
    apply
      (relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := K)).injective
    rw [RingEquiv.apply_symm_apply,
      relativeAdeleBaseChangeRingEquiv_fieldInclusion]
  change
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e
          ((relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := K)).symm
              (algebraMap K
                (NumberField.AdeleRing (𝓞 K) K) x))) =
      algebraMap M
        (NumberField.AdeleRing (𝓞 M) M) (e x)
  rw [hx, relativeAdeleCongr_tmul,
    relativeAdeleBaseChangeRingEquiv_fieldInclusion]

/-- The permutation of finite places induced by an equivalence of number
fields. -/
noncomputable def finitePlaceCongr
    (e : K ≃ₐ[ℚ] M) :
    HeightOneSpectrum (𝓞 K) ≃
      HeightOneSpectrum (𝓞 M) :=
  HeightOneSpectrum.equivOfRingEquiv
    (NumberField.RingOfIntegers.mapRingEquiv
      e.toRingEquiv)

omit [NumberField K] [NumberField M] in
@[simp]
theorem finitePlaceCongr_asIdeal
    (e : K ≃ₐ[ℚ] M)
    (v : HeightOneSpectrum (𝓞 K)) :
    (finitePlaceCongr e v).asIdeal =
      v.asIdeal.map
        (NumberField.RingOfIntegers.mapRingEquiv
          e.toRingEquiv) := by
  ext x
  exact Ideal.symm_apply_mem_of_equiv_iff

private theorem finitePlaceBelow_eq_finitePlaceCongr_symm
    (e : K ≃ₐ[ℚ] M)
    (W : HeightOneSpectrum (𝓞 M)) :
    letI : Algebra K M := e.toRingHom.toAlgebra
    finitePlaceBelow (K := K) W =
      (finitePlaceCongr e).symm W := by
  apply HeightOneSpectrum.ext
  rfl

/-- The canonical map between corresponding finite completions induced by
an equivalence of number fields. -/
noncomputable def finitePlaceAdicCompletionCongrHom
    (e : K ≃ₐ[ℚ] M)
    (W : HeightOneSpectrum (𝓞 M)) :
    ((finitePlaceCongr e).symm W).adicCompletion K →+*
      W.adicCompletion M := by
  letI : Algebra K M := e.toRingHom.toAlgebra
  exact
    finitePlaceAdicCompletionMap K M
      ((finitePlaceCongr e).symm W)
      ⟨W, by exact finitePlaceBelow_eq_finitePlaceCongr_symm e W⟩

/-- On finite coordinates, canonical adelic transport is the completion
map at the corresponding finite places. -/
theorem adeleCongr_finiteComponent
    (e : K ≃ₐ[ℚ] M)
    (a : NumberField.AdeleRing (𝓞 K) K)
    (W : HeightOneSpectrum (𝓞 M)) :
    (adeleCongr e a).2 W =
      finitePlaceAdicCompletionCongrHom e W
        (a.2 ((finitePlaceCongr e).symm W)) := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let : IsScalarTower ℚ K M :=
    IsScalarTower.of_algHom e.toAlgHom
  let componentK :=
    (finiteAdeleComponentAlgHom
      ((finitePlaceCongr e).symm W)).toAddMonoidHom
  let componentM :=
    (finiteAdeleComponentAlgHom W).toAddMonoidHom
  change
    componentM (adeleCongr e a) =
      finitePlaceAdicCompletionCongrHom e W
        (componentK a)
  let z :=
    (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).symm a
  have ha :
      relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) z = a :=
    (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).apply_symm_apply a
  rw [← ha]
  have htransport :
      componentM
        (relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e z)) =
        componentM
          (adeleCongr e
          (relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := K) z)) :=
    congrArg
      componentM
      (relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
        e z)
  rw [← htransport]
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul b x =>
      let w : HeightOneSpectrum (𝓞 K) :=
        (finitePlaceCongr e).symm W
      have hW :
          finitePlaceBelow (K := K) W = w := by
        exact finitePlaceBelow_eq_finitePlaceCongr_symm e W
      have hq :
          finitePlaceBelow (K := ℚ) w =
            finitePlaceBelow (K := ℚ) W := by
        rw [← hW, finitePlaceBelow_finitePlaceBelow]
      have hcomponent
          (q' : HeightOneSpectrum (𝓞 ℚ))
          (hq' :
            q' = finitePlaceBelow (K := ℚ) W)
          (hwq :
            finitePlaceBelow (K := ℚ) w = q') :
          finitePlaceAdicCompletionMap ℚ M
                (finitePlaceBelow (K := ℚ) W) ⟨W, rfl⟩
                (b.2 (finitePlaceBelow (K := ℚ) W)) *
              algebraMap M (W.adicCompletion M) (e x) =
            finitePlaceAdicCompletionMap K M w ⟨W, hW⟩
              (finitePlaceAdicCompletionMap ℚ K q'
                    ⟨w, hwq⟩ (b.2 q') *
                algebraMap K (w.adicCompletion K) x) := by
        subst q'
        have hx :
            finitePlaceAdicCompletionMap K M w ⟨W, hW⟩
                (algebraMap K (w.adicCompletion K) x) =
              algebraMap M (W.adicCompletion M) (e x) := by
          change
            finitePlaceAdicCompletionMap K M w ⟨W, hW⟩
                (x : w.adicCompletion K) =
              (e x : W.adicCompletion M)
          exact
            finitePlaceAdicCompletionMap_coe K M w
              ⟨W, hW⟩ x
        rw [map_mul,
          finitePlaceAdicCompletionMap_comp ℚ M (M := K)
            (finitePlaceBelow (K := ℚ) W) w W
            hwq hW rfl,
          hx]
      rw [relativeAdeleCongr_tmul]
      change
        (relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := M)
          (b ⊗ₜ[ℚ] e x)).2 W =
          finitePlaceAdicCompletionCongrHom e W
            ((relativeAdeleBaseChangeRingEquiv
              (K := ℚ) (L := K)
              (b ⊗ₜ[ℚ] x)).2 w)
      rw [
        relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul,
        relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul]
      change
        finitePlaceAdicCompletionMap ℚ M
              (finitePlaceBelow (K := ℚ) W) ⟨W, rfl⟩
              (b.2 (finitePlaceBelow (K := ℚ) W)) *
            algebraMap M (W.adicCompletion M) (e x) =
          finitePlaceAdicCompletionMap K M w ⟨W, hW⟩
            (finitePlaceAdicCompletionMap ℚ K
                  (finitePlaceBelow (K := ℚ) w) ⟨w, rfl⟩
                  (b.2 (finitePlaceBelow (K := ℚ) w)) *
              algebraMap K (w.adicCompletion K) x)
      exact hcomponent
        (finitePlaceBelow (K := ℚ) w) hq rfl

/-- The canonical transport of ordinary ideles along an equivalence of
number fields.  It is obtained from the existing relative-idele transport
over `ℚ` and the canonical relative-to-ordinary base-change equivalences. -/
noncomputable def ideleCongr
    (e : K ≃ₐ[ℚ] M) :
    IdeleGroup K ≃* IdeleGroup M :=
  (IdeleGroup.equivAdeleRingUnits (K := K)).trans
    ((Units.mapEquiv (adeleCongr e).toMulEquiv).trans
      (IdeleGroup.equivAdeleRingUnits (K := M)).symm)

/-- The relative-to-ordinary scalar-extension comparison is natural for
transport of relative ideles along an equivalence of their top fields. -/
theorem relativeIdeleBaseChangeMulEquiv_relativeIdeleCongr
    (e : K ≃ₐ[ℚ] M)
    (a : RelativeIdeleGroup ℚ K) :
    relativeIdeleBaseChangeMulEquiv
        (K := ℚ) (L := M)
        (relativeIdeleCongr (K := ℚ) e a) =
      ideleCongr e
        (relativeIdeleBaseChangeMulEquiv
          (K := ℚ) (L := K) a) := by
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := M)).injective
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  simp only [ideleCongr, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply,
    relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  apply Units.ext
  exact
    relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
      e (a : RelativeAdeleRing ℚ K)

/-- Under the actual Galois action on relative ideles, the
relative-to-ordinary scalar-extension comparison is equivariant for the
canonical transport of ordinary ideles. -/
theorem relativeIdeleBaseChangeMulEquiv_smul_congr
    {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
    (σ : E ≃ₐ[ℚ] E)
    (a : RelativeIdeleGroup ℚ E) :
    relativeIdeleBaseChangeMulEquiv
        (K := ℚ) (L := E) (σ • a) =
      ideleCongr σ
        (relativeIdeleBaseChangeMulEquiv
          (K := ℚ) (L := E) a) := by
  rw [← relativeIdeleCongr_eq_smul (K := ℚ) σ a]
  exact
    relativeIdeleBaseChangeMulEquiv_relativeIdeleCongr
      σ a

/-- On finite coordinates, canonical idelic transport is the completion
map at the corresponding finite places. -/
theorem ideleCongr_finiteComponent
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K)
    (W : HeightOneSpectrum (𝓞 M)) :
    IdeleGroup.finiteComponent W (ideleCongr e a) =
      Units.map
        (finitePlaceAdicCompletionCongrHom e W).toMonoidHom
        (IdeleGroup.finiteComponent
          ((finitePlaceCongr e).symm W) a) := by
  apply Units.ext
  exact
    adeleCongr_finiteComponent e
      (((IdeleGroup.equivAdeleRingUnits
        (K := K) a :
          (NumberField.AdeleRing (𝓞 K) K)ˣ) :
        NumberField.AdeleRing (𝓞 K) K))
      W

omit [NumberField K] in
private theorem finitePlaceCongr_ramificationIdx
    (e : K ≃ₐ[ℚ] M)
    (W : HeightOneSpectrum (𝓞 M)) :
    letI : Algebra K M := e.toRingHom.toAlgebra
    ((finitePlaceCongr e).symm W).asIdeal.ramificationIdx'
        W.asIdeal = 1 := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let w : HeightOneSpectrum (𝓞 K) :=
    (finitePlaceCongr e).symm W
  have hmap :
      w.asIdeal.map (algebraMap (𝓞 K) (𝓞 M)) =
        W.asIdeal := by
    change
      w.asIdeal.map
          (NumberField.RingOfIntegers.mapRingEquiv
            e.toRingEquiv) =
        W.asIdeal
    rw [← finitePlaceCongr_asIdeal e w]
    simp [w]
  rw [← hmap]
  exact
    Ideal.ramificationIdx'_map_self_eq_one
      (p := w.asIdeal)
      (by rw [hmap]; exact W.isPrime.ne_top)
      (by rw [hmap]; exact W.ne_bot)

/-- Normalized local orders are unchanged by transport along a
number-field equivalence. -/
theorem ideleCongr_localOrder
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K)
    (W : HeightOneSpectrum (𝓞 M)) :
    (FiniteIdeleGroup.localOrder W
        (IdeleGroup.finiteComponent W
          (ideleCongr e a))).toAdd =
      (FiniteIdeleGroup.localOrder
        ((finitePlaceCongr e).symm W)
        (IdeleGroup.finiteComponent
          ((finitePlaceCongr e).symm W) a)).toAdd := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let w : HeightOneSpectrum (𝓞 K) :=
    (finitePlaceCongr e).symm W
  have hW :
      finitePlaceBelow (K := K) W = w :=
    finitePlaceBelow_eq_finitePlaceCongr_symm e W
  rw [ideleCongr_finiteComponent]
  have hr :
      w.asIdeal.ramificationIdx' W.asIdeal = 1 :=
    finitePlaceCongr_ramificationIdx e W
  change
    (FiniteIdeleGroup.localOrder W
      (Units.map
        (finitePlaceAdicCompletionMap K M w ⟨W, hW⟩).toMonoidHom
        (IdeleGroup.finiteComponent w a))).toAdd =
      (FiniteIdeleGroup.localOrder w
        (IdeleGroup.finiteComponent w a)).toAdd
  simpa only [hr, Nat.cast_one, one_mul] using
    localOrder_finitePlaceAdicCompletionMap K M w
      ⟨W, hW⟩
      (IdeleGroup.finiteComponent w a)

/-- An idele is integral at every finite place exactly when its transport
along a number-field equivalence is. -/
theorem ideleCongr_mem_integralAtFinitePlaces_iff
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K) :
    ideleCongr e a ∈
        IdeleGroup.integralAtFinitePlaces (K := M) ↔
      a ∈ IdeleGroup.integralAtFinitePlaces (K := K) := by
  change
    (∀ W : HeightOneSpectrum (𝓞 M),
        IdeleGroup.finiteComponent W (ideleCongr e a) ∈
          (W.adicCompletionIntegers M).units) ↔
      ∀ w : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent w a ∈
          (w.adicCompletionIntegers K).units
  constructor
  · intro h w
    let W : HeightOneSpectrum (𝓞 M) :=
      finitePlaceCongr e w
    apply
      (FiniteIdeleGroup.localOrder_eq_zero_iff w
        (IdeleGroup.finiteComponent w a)).1
    have horder := ideleCongr_localOrder e a W
    rw [show (finitePlaceCongr e).symm W = w by
      simp [W]] at horder
    rw [← horder]
    exact
      (FiniteIdeleGroup.localOrder_eq_zero_iff W
        (IdeleGroup.finiteComponent W
          (ideleCongr e a))).2 (h W)
  · intro h W
    apply
      (FiniteIdeleGroup.localOrder_eq_zero_iff W
        (IdeleGroup.finiteComponent W
          (ideleCongr e a))).1
    rw [ideleCongr_localOrder]
    exact
      (FiniteIdeleGroup.localOrder_eq_zero_iff
        ((finitePlaceCongr e).symm W)
        (IdeleGroup.finiteComponent
          ((finitePlaceCongr e).symm W) a)).2
        (h ((finitePlaceCongr e).symm W))

/-- Transport along a number-field equivalence identifies the subgroups
of ideles integral at every finite place. -/
theorem ideleIntegralAtFinitePlaces_map_congr
    (e : K ≃ₐ[ℚ] M) :
    (IdeleGroup.integralAtFinitePlaces (K := K)).map
        (ideleCongr e).toMonoidHom =
      IdeleGroup.integralAtFinitePlaces (K := M) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact
      (ideleCongr_mem_integralAtFinitePlaces_iff
        e a).2 ha
  · intro hb
    let a : IdeleGroup K := (ideleCongr e).symm b
    refine ⟨a, ?_, ?_⟩
    · exact
        (ideleCongr_mem_integralAtFinitePlaces_iff
          e a).1 (by simpa [a] using hb)
    · exact (ideleCongr e).apply_symm_apply b

/-- Transport along a number-field equivalence carries the diagonal idele
to the diagonal idele of the transported field unit. -/
@[simp]
theorem ideleCongr_principalIdele
    (e : K ≃ₐ[ℚ] M)
    (x : Kˣ) :
    ideleCongr e (IdeleGroup.principalIdele K x) =
      IdeleGroup.principalIdele M
        (Units.mapEquiv e.toMulEquiv x) := by
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := M)).injective
  apply Units.ext
  exact adeleCongr_algebraMap e (x : K)

/-- The ordinary principal-idele subgroups are identified by transport
along a number-field equivalence. -/
theorem idelePrincipalSubgroup_map_congr
    (e : K ≃ₐ[ℚ] M) :
    (IdeleGroup.principalSubgroup K).map
        (ideleCongr e) =
      IdeleGroup.principalSubgroup M := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, rfl⟩
    rw [← hx]
    exact
      ⟨Units.mapEquiv e.toMulEquiv x,
        (ideleCongr_principalIdele e x).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ :=
      (Units.mapEquiv e.toMulEquiv).surjective y
    exact
      ⟨IdeleGroup.principalIdele K x,
        ⟨x, rfl⟩,
        ideleCongr_principalIdele e x⟩

/-- Transport along a number-field equivalence identifies the subgroups
defining the ordinary ideal-class quotients. -/
theorem ordinaryIdealClassSubgroup_map_congr
    (e : K ≃ₐ[ℚ] M) :
    (IdeleGroup.ordinaryIdealClassSubgroup (K := K)).map
        (ideleCongr e).toMonoidHom =
      IdeleGroup.ordinaryIdealClassSubgroup (K := M) := by
  rw [IdeleGroup.ordinaryIdealClassSubgroup,
    IdeleGroup.ordinaryIdealClassSubgroup,
    Subgroup.map_sup,
    ideleIntegralAtFinitePlaces_map_congr]
  apply congrArg
    (fun H =>
      IdeleGroup.integralAtFinitePlaces (K := M) ⊔ H)
  change
    (IdeleGroup.principalSubgroup K).map
        (ideleCongr e) =
      IdeleGroup.principalSubgroup M
  exact idelePrincipalSubgroup_map_congr e

/-- The canonical transport of ordinary idele classes along an equivalence
of number fields.  This descends `ideleCongr`; it does not introduce a
second idele-class quotient. -/
noncomputable def ideleClassCongr
    (e : K ≃ₐ[ℚ] M) :
    IdeleClassGroup K ≃* IdeleClassGroup M :=
  QuotientGroup.congr
    (IdeleGroup.principalSubgroup K)
    (IdeleGroup.principalSubgroup M)
    (ideleCongr e)
    (idelePrincipalSubgroup_map_congr e)

/-- The ordinary idele-class transport is induced by `ideleCongr` on
quotient representatives. -/
theorem ideleClassCongr_mk
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K) :
    ideleClassCongr e
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup M)
        (ideleCongr e a) :=
  rfl

/-- The relative-to-ordinary scalar-extension comparison is natural for
transport of relative idèle classes along an equivalence of their top
fields. -/
theorem
    relativeIdeleClassBaseChangeMulEquiv_relativeIdeleClassCongr
    (e : K ≃ₐ[ℚ] M)
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := M)
        (relativeIdeleClassCongr (K := ℚ) e c) =
      ideleClassCongr e
        (relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := M)
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup ℚ M)
          (relativeIdeleCongr (K := ℚ) e a)) =
      ideleClassCongr e
        (relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K)
          (QuotientGroup.mk'
            (RelativeIdeleGroup.principalSubgroup ℚ K) a))
  rw [relativeIdeleClassBaseChangeMulEquiv_mk,
    relativeIdeleClassBaseChangeMulEquiv_mk,
    ideleClassCongr_mk,
    relativeIdeleBaseChangeMulEquiv_relativeIdeleCongr]

section GaloisBaseChangeNaturality

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]

/-- Rational Galois automorphisms act on relative idele classes. -/
local instance :
    MulDistribMulAction (E ≃ₐ[ℚ] E)
      (RelativeIdeleGroup.ClassGroup ℚ E) :=
  RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction ℚ E

/-- The actual Galois action on relative idele classes becomes canonical
ordinary idele-class transport under the relative-to-ordinary
scalar-extension comparison. -/
theorem relativeIdeleClassBaseChangeMulEquiv_smul_congr
    (σ : E ≃ₐ[ℚ] E)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E) (σ • c) =
      ideleClassCongr σ
        (relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E)
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup ℚ E)
          (σ • a)) =
      ideleClassCongr σ
        (relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E)
          (QuotientGroup.mk'
            (RelativeIdeleGroup.principalSubgroup ℚ E) a))
  rw [relativeIdeleClassBaseChangeMulEquiv_mk,
    relativeIdeleClassBaseChangeMulEquiv_mk,
    ideleClassCongr_mk,
    relativeIdeleBaseChangeMulEquiv_smul_congr]

end GaloisBaseChangeNaturality

/-- On idele class groups, transport identifies the images of the
ordinary ideal-class subgroups.  This is the subgroup-level naturality
used by the small Hilbert class field. -/
theorem ordinaryIdealClassSubgroup_image_map_ideleClassCongr
    (e : K ≃ₐ[ℚ] M) :
    (Subgroup.map
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K))
        (IdeleGroup.ordinaryIdealClassSubgroup (K := K))).map
          (ideleClassCongr e).toMonoidHom =
      Subgroup.map
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup M))
        (IdeleGroup.ordinaryIdealClassSubgroup (K := M)) := by
  have hcomp :
      (ideleClassCongr e).toMonoidHom.comp
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)) =
        (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup M)).comp
          (ideleCongr e).toMonoidHom := by
    ext a
    exact ideleClassCongr_mk e a
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    ordinaryIdealClassSubgroup_map_congr]

omit [Algebra ℚ K] in
private theorem
    relativeAdeleBaseChangeRingEquiv_self_tmul_one
    (a : NumberField.AdeleRing (𝓞 K) K) :
    relativeAdeleBaseChangeRingEquiv
        (K := K) (L := K) (a ⊗ₜ[K] (1 : K)) =
      a := by
  apply Prod.ext
  · funext W
    rw [relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul]
    simp only [map_one, mul_one]
    let V := infinitePlaceBelow (K := K) W
    have hV : V = W :=
      infinitePlaceBelow_self (K := K) W
    let : W.1.LiesOver V.1 := ⟨rfl⟩
    change
      NumberField.LiesOver.completionMap
          (v := V) (w := W) (a.1 V) =
        a.1 W
    subst V
    exact
      infinitePlaceCompletionMap_self_apply
        (K := K) W (a.1 W)
  · apply DFunLike.coe_injective
    funext W
    rw [relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul]
    simp only [map_one, mul_one]
    let v := finitePlaceBelow (K := K) W
    have hv : v = W :=
      finitePlaceBelow_self (K := K) W
    change
      finitePlaceAdicCompletionMap K K v
          ⟨W, by rfl⟩ (a.2 v) =
        a.2 W
    subst v
    exact
      finitePlaceAdicCompletionMap_self_apply
        K W (a.2 W)

omit [Algebra ℚ K] in
private theorem
    relativeAdeleBaseChangeRingEquiv_self_symm_apply
    (a : NumberField.AdeleRing (𝓞 K) K) :
    (relativeAdeleBaseChangeRingEquiv
        (K := K) (L := K)).symm a =
      a ⊗ₜ[K] (1 : K) := by
  apply
    (relativeAdeleBaseChangeRingEquiv
      (K := K) (L := K)).injective
  rw [RingEquiv.apply_symm_apply,
    relativeAdeleBaseChangeRingEquiv_self_tmul_one]

/-- Scalar extension from `ℚ` to a realization algebra-equivalent to
`ℚ` is the canonical transport of ordinary adele rings. -/
theorem rationalAdeleExtension_eq_adeleCongr
    (e : ℚ ≃ₐ[ℚ] M)
    (a : NumberField.AdeleRing (𝓞 ℚ) ℚ) :
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (RelativeIdeleGroup.adeleInclusion ℚ M a) =
      adeleCongr e a := by
  change
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (a ⊗ₜ[ℚ] (1 : M)) =
      relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e
          ((relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := ℚ)).symm a))
  rw [relativeAdeleBaseChangeRingEquiv_self_symm_apply]
  simp only [relativeAdeleCongr_tmul, map_one]

/-- Scalar extension from `ℚ` to a realization algebra-equivalent to
`ℚ` is the canonical transport of ordinary ideles. -/
theorem rationalIdeleExtension_eq_ideleCongr
    (e : ℚ ≃ₐ[ℚ] M) :
    IdeleGroup.extension ℚ M =
      (ideleCongr e).toMonoidHom := by
  apply MonoidHom.ext
  intro a
  change
    relativeIdeleBaseChangeMulEquiv
        (K := ℚ) (L := M)
        (RelativeIdeleGroup.inclusion ℚ M a) =
      ideleCongr e a
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := M)).injective
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  apply Units.ext
  exact
    rationalAdeleExtension_eq_adeleCongr e
      ((IdeleGroup.equivAdeleRingUnits
        (K := ℚ) a :
          (NumberField.AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        NumberField.AdeleRing (𝓞 ℚ) ℚ)

/-- Scalar extension from `ℚ` to a realization algebra-equivalent to
`ℚ` is the canonical transport of ordinary idele classes. -/
theorem rationalIdeleClassExtension_eq_ideleClassCongr
    (e : ℚ ≃ₐ[ℚ] M) :
    ideleClassExtension ℚ M =
      (ideleClassCongr e).toMonoidHom := by
  apply MonoidHom.ext
  intro c
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup M)
        (IdeleGroup.extension ℚ M a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup M)
        (ideleCongr e a)
  exact congrArg
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup M))
    (DFunLike.congr_fun
      (rationalIdeleExtension_eq_ideleCongr e) a)

section RelativeTowerCongr

variable
    {K L K' L' : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Field K'] [NumberField K']
    [Field L'] [NumberField L'] [Algebra K' L']

/-- The tensor-product map induced by compatible equivalences of both
fields in a finite extension.  The coefficient-ring equivalence is kept
explicit so the inverse uses that exact equivalence rather than a second
choice. -/
noncomputable def relativeAdeleMapOfCompatibleEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eA :
      NumberField.AdeleRing (𝓞 K) K ≃+*
        NumberField.AdeleRing (𝓞 K') K')
    (hA : ∀ x : K,
      eA
          (algebraMap K
            (NumberField.AdeleRing (𝓞 K) K) x) =
        algebraMap K'
          (NumberField.AdeleRing (𝓞 K') K') (eK x))
    (eL : L ≃ₐ[ℚ] L')
    (hL : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    RelativeAdeleRing K L →+*
      RelativeAdeleRing K' L' := by
  letI : Algebra K (RelativeAdeleRing K' L') :=
    ((algebraMap K' (RelativeAdeleRing K' L')).comp
      eK.toRingHom).toAlgebra
  let fA :
      NumberField.AdeleRing (𝓞 K) K →ₐ[K]
        RelativeAdeleRing K' L' :=
    { __ :=
        (RelativeIdeleGroup.adeleInclusion K' L').comp
          eA.toRingHom
      commutes' := by
        intro x
        change
          RelativeIdeleGroup.adeleInclusion K' L'
              (eA
                (algebraMap K
                  (NumberField.AdeleRing (𝓞 K) K) x)) =
            algebraMap K'
              (RelativeAdeleRing K' L') (eK x)
        rw [hA]
        simp [RelativeIdeleGroup.adeleInclusion] }
  let fL : L →ₐ[K] RelativeAdeleRing K' L' :=
    { __ :=
        (RelativeIdeleGroup.fieldInclusion K' L').comp
          eL.toRingHom
      commutes' := by
        intro x
        change
          RelativeIdeleGroup.fieldInclusion K' L'
              (eL (algebraMap K L x)) =
            algebraMap K'
              (RelativeAdeleRing K' L') (eK x)
        rw [hL]
        simp [RelativeIdeleGroup.fieldInclusion] }
  exact
    (Algebra.TensorProduct.lift
      fA fL (fun _ _ ↦ Commute.all _ _)).toRingHom

@[simp]
private theorem relativeAdeleMapOfCompatibleEquiv_tmul
    (eK : K ≃ₐ[ℚ] K')
    (eA :
      NumberField.AdeleRing (𝓞 K) K ≃+*
        NumberField.AdeleRing (𝓞 K') K')
    (hA : ∀ x : K,
      eA
          (algebraMap K
            (NumberField.AdeleRing (𝓞 K) K) x) =
        algebraMap K'
          (NumberField.AdeleRing (𝓞 K') K') (eK x))
    (eL : L ≃ₐ[ℚ] L')
    (hL : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L) :
    relativeAdeleMapOfCompatibleEquiv
        eK eA hA eL hL (a ⊗ₜ[K] x) =
      eA a ⊗ₜ[K'] eL x := by
  change
    Algebra.TensorProduct.includeLeft
          (R := K') (S := K')
          (A := NumberField.AdeleRing (𝓞 K') K') (B := L')
          (eA a) *
        Algebra.TensorProduct.includeRight
          (R := K')
          (A := NumberField.AdeleRing (𝓞 K') K') (B := L')
          (eL x) =
      eA a ⊗ₜ[K'] eL x
  rw [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- Compatible equivalences of number-field extensions induce the
canonical equivalence of their relative adele rings. -/
noncomputable def relativeAdeleCongrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    RelativeAdeleRing K L ≃+*
      RelativeAdeleRing K' L' := by
  let eA := adeleCongr eK
  have hA : ∀ x : K,
      eA
          (algebraMap K
            (NumberField.AdeleRing (𝓞 K) K) x) =
        algebraMap K'
          (NumberField.AdeleRing (𝓞 K') K') (eK x) :=
    adeleCongr_algebraMap eK
  have hA' : ∀ x : K',
      eA.symm
          (algebraMap K'
            (NumberField.AdeleRing (𝓞 K') K') x) =
        algebraMap K
          (NumberField.AdeleRing (𝓞 K) K)
          (eK.symm x) := by
    intro x
    apply eA.injective
    calc
      eA
          (eA.symm
            (algebraMap K'
              (NumberField.AdeleRing (𝓞 K') K') x)) =
          algebraMap K'
            (NumberField.AdeleRing (𝓞 K') K') x :=
        eA.apply_symm_apply _
      _ =
          algebraMap K'
            (NumberField.AdeleRing (𝓞 K') K')
            (eK (eK.symm x)) := by
        rw [eK.apply_symm_apply]
      _ =
          eA
            (algebraMap K
              (NumberField.AdeleRing (𝓞 K) K)
              (eK.symm x)) :=
        (hA (eK.symm x)).symm
  have h' : ∀ x : K',
      eL.symm (algebraMap K' L' x) =
        algebraMap K L (eK.symm x) := by
    intro x
    apply eL.injective
    calc
      eL (eL.symm (algebraMap K' L' x)) =
          algebraMap K' L' x :=
        eL.apply_symm_apply _
      _ = algebraMap K' L' (eK (eK.symm x)) := by
        rw [eK.apply_symm_apply]
      _ = eL (algebraMap K L (eK.symm x)) :=
        (h (eK.symm x)).symm
  let f :=
    relativeAdeleMapOfCompatibleEquiv
      eK eA hA eL h
  let g :=
    relativeAdeleMapOfCompatibleEquiv
      eK.symm eA.symm hA' eL.symm h'
  exact
    { f with
      invFun := g
      left_inv := by
        intro z
        induction z using TensorProduct.inductionOn with
        | add x y hx hy =>
            calc
              g (f (x + y)) =
                  g (f x + f y) :=
                congrArg g (map_add f x y)
              _ = g (f x) + g (f y) :=
                map_add g (f x) (f y)
              _ = x + y :=
                congrArg₂ (· + ·) hx hy
        | tmul a x =>
            calc
              g (f (a ⊗ₜ[K] x)) =
                  g (eA a ⊗ₜ[K'] eL x) :=
                congrArg g
                  (relativeAdeleMapOfCompatibleEquiv_tmul
                    eK eA hA eL h a x)
              _ = eA.symm (eA a) ⊗ₜ[K] eL.symm (eL x) :=
                relativeAdeleMapOfCompatibleEquiv_tmul
                  eK.symm eA.symm hA' eL.symm h'
                  (eA a) (eL x)
              _ = a ⊗ₜ[K] x := by simp
      right_inv := by
        intro z
        induction z using TensorProduct.inductionOn with
        | add x y hx hy =>
            calc
              f (g (x + y)) =
                  f (g x + g y) :=
                congrArg f (map_add g x y)
              _ = f (g x) + f (g y) :=
                map_add f (g x) (g y)
              _ = x + y :=
                congrArg₂ (· + ·) hx hy
        | tmul a x =>
            calc
              f (g (a ⊗ₜ[K'] x)) =
                  f (eA.symm a ⊗ₜ[K] eL.symm x) :=
                congrArg f
                  (relativeAdeleMapOfCompatibleEquiv_tmul
                    eK.symm eA.symm hA' eL.symm h' a x)
              _ = eA (eA.symm a) ⊗ₜ[K'] eL (eL.symm x) :=
                relativeAdeleMapOfCompatibleEquiv_tmul
                  eK eA hA eL h (eA.symm a) (eL.symm x)
              _ = a ⊗ₜ[K'] x := by simp }

@[simp]
theorem relativeAdeleCongrOfAlgEquiv_tmul
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L) :
    relativeAdeleCongrOfAlgEquiv eK eL h
        (a ⊗ₜ[K] x) =
      adeleCongr eK a ⊗ₜ[K'] eL x :=
  relativeAdeleMapOfCompatibleEquiv_tmul
    eK (adeleCongr eK)
    (adeleCongr_algebraMap eK) eL h a x

/-- Compatible equivalences of number-field extensions induce the
canonical equivalence of their relative idele groups. -/
noncomputable def relativeIdeleCongrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    RelativeIdeleGroup K L ≃*
      RelativeIdeleGroup K' L' :=
  Units.mapEquiv
    (relativeAdeleCongrOfAlgEquiv eK eL h).toMulEquiv

@[simp]
theorem relativeIdeleCongrOfAlgEquiv_principalIdele
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (x : Lˣ) :
    relativeIdeleCongrOfAlgEquiv eK eL h
        (RelativeIdeleGroup.principalIdele K L x) =
      RelativeIdeleGroup.principalIdele K' L'
        (Units.mapEquiv eL.toMulEquiv x) := by
  apply Units.ext
  change
    relativeAdeleCongrOfAlgEquiv eK eL h
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] (x : L)) =
      (1 : NumberField.AdeleRing (𝓞 K') K') ⊗ₜ[K'] eL (x : L)
  rw [relativeAdeleCongrOfAlgEquiv_tmul]
  simp

/-- The semilinear relative-idele transport identifies the principal
subgroups. -/
theorem relativeIdelePrincipalSubgroup_map_congrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    (RelativeIdeleGroup.principalSubgroup K L).map
        (relativeIdeleCongrOfAlgEquiv eK eL h) =
      RelativeIdeleGroup.principalSubgroup K' L' := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, rfl⟩
    rw [← hx]
    exact
      ⟨Units.mapEquiv eL.toMulEquiv x,
        (relativeIdeleCongrOfAlgEquiv_principalIdele
          eK eL h x).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ :=
      (Units.mapEquiv eL.toMulEquiv).surjective y
    exact
      ⟨RelativeIdeleGroup.principalIdele K L x,
        ⟨x, rfl⟩,
        relativeIdeleCongrOfAlgEquiv_principalIdele
          eK eL h x⟩

/-- Compatible equivalences of number-field extensions induce the
canonical equivalence of their existing relative idele class groups. -/
noncomputable def relativeIdeleClassCongrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    RelativeIdeleGroup.ClassGroup K L ≃*
      RelativeIdeleGroup.ClassGroup K' L' :=
  QuotientGroup.congr
    (RelativeIdeleGroup.principalSubgroup K L)
    (RelativeIdeleGroup.principalSubgroup K' L')
    (relativeIdeleCongrOfAlgEquiv eK eL h)
    (relativeIdelePrincipalSubgroup_map_congrOfAlgEquiv
      eK eL h)

theorem relativeIdeleClassCongrOfAlgEquiv_mk
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (a : RelativeIdeleGroup K L) :
    relativeIdeleClassCongrOfAlgEquiv eK eL h
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K' L')
        (relativeIdeleCongrOfAlgEquiv eK eL h a) :=
  rfl

section Norm

variable
    [FiniteDimensional K L]
    [FiniteDimensional K' L']

omit [FiniteDimensional K L] [FiniteDimensional K' L'] in
/-- Determinant norms on relative adele rings commute with compatible
equivalences of both fields in the extension. -/
theorem relativeAdeleCongrOfAlgEquiv_norm
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (z : RelativeAdeleRing K L) :
    adeleCongr eK
        (Algebra.norm
          (NumberField.AdeleRing (𝓞 K) K) z) =
      Algebra.norm
        (NumberField.AdeleRing (𝓞 K') K')
        (relativeAdeleCongrOfAlgEquiv eK eL h z) := by
  have hcompat :
      (algebraMap
          (NumberField.AdeleRing (𝓞 K') K')
          (RelativeAdeleRing K' L')).comp
          (adeleCongr eK).toRingHom =
        (relativeAdeleCongrOfAlgEquiv eK eL h).toRingHom.comp
          (algebraMap
            (NumberField.AdeleRing (𝓞 K) K)
            (RelativeAdeleRing K L)) := by
    ext a
    change
      (adeleCongr eK a) ⊗ₜ[K'] (1 : L') =
        relativeAdeleCongrOfAlgEquiv eK eL h
          (a ⊗ₜ[K] (1 : L))
    rw [relativeAdeleCongrOfAlgEquiv_tmul]
    simp
  have hnorm :=
    Algebra.norm_eq_of_equiv_equiv
      (adeleCongr eK)
      (relativeAdeleCongrOfAlgEquiv eK eL h)
      hcompat z
  simpa using congrArg (adeleCongr eK) hnorm

omit [FiniteDimensional K L] [FiniteDimensional K' L'] in
/-- The relative idele norm commutes with compatible equivalences of
number-field extensions. -/
theorem relativeIdeleCongrOfAlgEquiv_norm
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (a : RelativeIdeleGroup K L) :
    ideleCongr eK (RelativeIdeleGroup.norm K L a) =
      RelativeIdeleGroup.norm K' L'
        (relativeIdeleCongrOfAlgEquiv eK eL h a) := by
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := K')).injective
  apply Units.ext
  exact
    relativeAdeleCongrOfAlgEquiv_norm
      eK eL h (a : RelativeAdeleRing K L)

variable [IsGalois K L] [IsGalois K' L']

omit [IsGalois K L] [IsGalois K' L'] in
/-- The descended relative idele-class norm commutes with compatible
equivalences of number-field extensions. -/
theorem relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (c : RelativeIdeleGroup.ClassGroup K L) :
    ideleClassCongr eK
        (RelativeIdeleGroup.classNorm K L c) =
      RelativeIdeleGroup.classNorm K' L'
        (relativeIdeleClassCongrOfAlgEquiv
          eK eL h c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K'))
    (relativeIdeleCongrOfAlgEquiv_norm eK eL h a)

omit [IsGalois K L] [IsGalois K' L'] in
/-- Under compatible equivalences of number-field extensions, the
relative class-norm subgroup is carried exactly to the relative
class-norm subgroup of the transported extension. -/
theorem relativeIdeleClassNorm_range_map_congrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    (RelativeIdeleGroup.classNorm K L).range.map
        (ideleClassCongr eK).toMonoidHom =
      (RelativeIdeleGroup.classNorm K' L').range := by
  ext c
  constructor
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact
      ⟨relativeIdeleClassCongrOfAlgEquiv
          eK eL h d,
        (relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm
          eK eL h d).symm⟩
  · rintro ⟨d, rfl⟩
    let c :=
      (relativeIdeleClassCongrOfAlgEquiv
        eK eL h).symm d
    refine
      ⟨RelativeIdeleGroup.classNorm K L c,
        ⟨c, rfl⟩, ?_⟩
    simpa [c] using
      (relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm
        eK eL h c)

omit [FiniteDimensional K L] [FiniteDimensional K' L']
  [IsGalois K L] [IsGalois K' L'] in
/-- Under compatible equivalences of finite Galois number-field
extensions, the ordinary class-norm subgroup is carried exactly to the
ordinary class-norm subgroup of the transported extension. -/
theorem ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    (_root_.ideleClassNorm K L).range.map
        (ideleClassCongr eK).toMonoidHom =
      (_root_.ideleClassNorm K' L').range := by
  rw [ordinaryIdeleClassNorm_range_eq_relative
      (K := K) (L := L),
    ordinaryIdeleClassNorm_range_eq_relative
      (K := K') (L := L')]
  exact
    relativeIdeleClassNorm_range_map_congrOfAlgEquiv
      eK eL h

-- Fix the canonical commutativity proof used by the norm-range quotients.
local instance normIdeleClassGroup_isMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

/-- Compatible equivalences of finite Galois number-field extensions
induce the canonical equivalence of their ordinary idele-class norm
quotients. -/
noncomputable def ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃*
      (IdeleClassGroup K' ⧸
        (_root_.ideleClassNorm K' L').range) :=
  QuotientGroup.congr
    (_root_.ideleClassNorm K L).range
    (_root_.ideleClassNorm K' L').range
    (ideleClassCongr eK)
    (ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv
      eK eL h)

omit [FiniteDimensional K L] [FiniteDimensional K' L']
  [IsGalois K L] [IsGalois K' L'] in
/-- On an ordinary idele-class representative, transport of norm
quotients is induced by the existing idele-class transport. -/
theorem ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (c : IdeleClassGroup K) :
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
        eK eL h
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range c) =
      QuotientGroup.mk'
        (_root_.ideleClassNorm K' L').range
        (ideleClassCongr eK c) :=
  rfl

end Norm

end RelativeTowerCongr
