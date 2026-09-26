/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisNorm
public import Mathlib.FieldTheory.Normal.Basic
/-!
# Norms through an ambient Galois extension

This file proves the embedded-subextension determinant-norm formula.
If `L/K` is embedded in a finite Galois extension `M/K`, extending the
determinant norm of an element of `A ⊗[K] L` to `A ⊗[K] M` gives the
product over all `K`-embeddings `L → M`.
-/

@[expose] public section

open scoped BigOperators TensorProduct
open NumberField

noncomputable
section

namespace RelativeIdeleGroup

universe u v w z

section EmbeddingsIntoGaloisExtension

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]

/-- Extend a `K`-embedding `L → M` to the algebraic closure of `M`. -/
def embeddingToAlgebraicClosure :
    (L →ₐ[K] M) →
      (L →ₐ[K] AlgebraicClosure M) :=
  fun f =>
    (IsScalarTower.toAlgHom K M
      (AlgebraicClosure M)).comp f

omit [Algebra L M] [IsScalarTower K L M] in
theorem embeddingToAlgebraicClosure_injective :
    Function.Injective
      (embeddingToAlgebraicClosure
        (K := K) (L := L) (M := M)) := by
  intro f g h
  ext x
  exact
    (algebraMap M (AlgebraicClosure M)).injective
      (DFunLike.congr_fun h x)

theorem embeddingToAlgebraicClosure_surjective
    [Normal K M] :
    Function.Surjective
      (embeddingToAlgebraicClosure
        (K := K) (L := L) (M := M)) := by
  intro f
  let C := AlgebraicClosure M
  let e : C →ₐ[K] C := f.liftNormal C
  let r : M →ₐ[K] M := e.restrictNormal M
  let j : L →ₐ[K] M :=
    IsScalarTower.toAlgHom K L M
  refine ⟨r.comp j, ?_⟩
  ext x
  change algebraMap M C
      (r (algebraMap L M x)) = f x
  rw [AlgHom.restrictNormal_commutes]
  change e (algebraMap L C x) = f x
  exact f.liftNormal_commutes C x

/-- Embeddings of a subextension into a finite normal overfield are the
same as embeddings into an algebraic closure. -/
noncomputable def embeddingToAlgebraicClosureEquiv
    [FiniteDimensional K M] [Normal K M] :
    (L →ₐ[K] M) ≃
      (L →ₐ[K] AlgebraicClosure M) :=
  Equiv.ofBijective embeddingToAlgebraicClosure
    ⟨embeddingToAlgebraicClosure_injective,
      embeddingToAlgebraicClosure_surjective⟩

/-- The subgroup of `Gal(M/K)` fixing the embedded copy of `L`. -/
def fixingSubextension :
    Subgroup (M ≃ₐ[K] M) :=
  (IsScalarTower.toAlgHom K L M).fieldRange.fixingSubgroup

/-- Restriction of an automorphism of `M/K` to the embedded copy of `L`. -/
def restrictToSubextension
    (σ : M ≃ₐ[K] M) : L →ₐ[K] M :=
  σ.toAlgHom.comp
    (IsScalarTower.toAlgHom K L M)

/-- Extend an embedding `L →ₐ[K] M` to an automorphism of the normal
extension `M/K`. -/
noncomputable def liftSubextensionEmbedding
    [Normal K M] (f : L →ₐ[K] M) :
    M ≃ₐ[K] M :=
  AlgEquiv.ofBijective (f.liftNormal M)
    (AlgHom.normal_bijective K M M _)

theorem restrict_liftSubextensionEmbedding
    [Normal K M] (f : L →ₐ[K] M) :
    restrictToSubextension
        (liftSubextensionEmbedding f) = f := by
  ext x
  exact f.liftNormal_commutes M x

/-- The canonical map from right cosets of the fixing subgroup to
embeddings of the subextension. -/
noncomputable def cosetToEmbedding
    :
    (M ≃ₐ[K] M) ⧸
        fixingSubextension (K := K) (L := L) (M := M) →
      (L →ₐ[K] M) :=
  fun q ↦
    Quotient.liftOn' q restrictToSubextension (by
      intro σ τ hστ
      rw [QuotientGroup.leftRel_apply] at hστ
      ext x
      have hfix :=
        (IntermediateField.mem_fixingSubgroup_iff
          (IsScalarTower.toAlgHom K L M).fieldRange
          (σ⁻¹ * τ)).1 hστ
          (algebraMap L M x)
          (by exact ⟨x, rfl⟩)
      change σ (algebraMap L M x) =
        τ (algebraMap L M x)
      have ht : τ = σ * (σ⁻¹ * τ) := by
        group
      rw [ht, AlgEquiv.mul_apply, hfix])

/-- Right cosets `Gal(M/K)/Gal(M/L)` are canonically the `K`-embeddings
`L → M`. This is the index set in the coset form of the Galois product norm formula. -/
noncomputable def cosetEquivEmbedding
    [Normal K M] :
    (M ≃ₐ[K] M) ⧸
        fixingSubextension (K := K) (L := L) (M := M) ≃
      (L →ₐ[K] M) where
  toFun := cosetToEmbedding
  invFun f :=
    (liftSubextensionEmbedding f :
      (M ≃ₐ[K] M) ⧸
        fixingSubextension
          (K := K) (L := L) (M := M))
  right_inv f :=
    restrict_liftSubextensionEmbedding f
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro σ
    apply QuotientGroup.eq.mpr
    change
      (liftSubextensionEmbedding
          (restrictToSubextension σ))⁻¹ * σ ∈
        (IsScalarTower.toAlgHom K L M).fieldRange.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff
      (IsScalarTower.toAlgHom K L M).fieldRange]
    intro y hy
    rcases hy with ⟨x, rfl⟩
    change
      ((liftSubextensionEmbedding
          (restrictToSubextension σ))⁻¹ * σ)
          (algebraMap L M x) =
        algebraMap L M x
    rw [AlgEquiv.mul_apply]
    have hres :=
      DFunLike.congr_fun
        (restrict_liftSubextensionEmbedding
          (restrictToSubextension σ)) x
    change
      liftSubextensionEmbedding
          (restrictToSubextension σ)
          (algebraMap L M x) =
        σ (algebraMap L M x) at hres
    rw [← hres]
    exact
      (liftSubextensionEmbedding
        (restrictToSubextension σ)).symm_apply_apply
          (algebraMap L M x)

/-- The field norm of a subextension, computed in an ambient finite
Galois extension, is the product over all embeddings into that extension. -/
theorem norm_eq_prod_embeddings_in_galoisExtension
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M] (x : L) :
    algebraMap K M (Algebra.norm K x) =
      ∏ f : L →ₐ[K] M, f x := by
  let : Algebra.IsSeparable K L :=
    Algebra.isSeparable_tower_bot_of_isSeparable K L M
  apply
    (algebraMap M
      (AlgebraicClosure M)).injective
  rw [map_prod]
  calc
    algebraMap M (AlgebraicClosure M)
        (algebraMap K M (Algebra.norm K x)) =
      algebraMap K (AlgebraicClosure M)
        (Algebra.norm K x) := by
          rw [IsScalarTower.algebraMap_apply
            K M (AlgebraicClosure M)]
    _ = ∏ f : L →ₐ[K] AlgebraicClosure M, f x :=
      Algebra.norm_eq_prod_embeddings K
        (AlgebraicClosure M) x
    _ = ∏ f : L →ₐ[K] M,
        algebraMap M (AlgebraicClosure M) (f x) := by
      exact ((embeddingToAlgebraicClosureEquiv
          (K := K) (L := L) (M := M)).prod_comp
            (fun f ↦ f x)).symm

end EmbeddingsIntoGaloisExtension

section UniversalPolynomial

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M]

/-- The quotient by automorphisms fixing the intermediate field has a finite enumeration. -/
local instance :
    Fintype
      ((M ≃ₐ[K] M) ⧸
        fixingSubextension
          (K := K) (L := L) (M := M)) :=
  Fintype.ofFinite _

/-- The linear polynomial representing a chosen `K`-embedding `L → M`. -/
def embeddingPolynomial
    {ι : Type z} [Fintype ι]
    (b : Module.Basis ι K L) (f : L →ₐ[K] M) :
    MvPolynomial ι M :=
  ∑ i, MvPolynomial.X i *
    MvPolynomial.C (f (b i))

omit [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M] in
@[simp]
theorem eval_embeddingPolynomial
    {ι : Type z} [Fintype ι]
    (b : Module.Basis ι K L) (f : L →ₐ[K] M)
    (x : L) :
    MvPolynomial.eval
        (fun i ↦ algebraMap K M (b.repr x i))
        (embeddingPolynomial b f) =
      f x := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  rw [embeddingPolynomial, map_sum]
  simp only [map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_C]
  calc
    ∑ i, algebraMap K M (b.repr x i) *
        f (b i) =
      ∑ i, f ((b.repr x i) • b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Algebra.smul_def]
    _ = f (∑ i, (b.repr x i) • b i) := by
      rw [map_sum]
    _ = f x := by rw [b.sum_repr]

/-- The universal product over all embeddings `L →ₐ[K] M`. -/
def embeddingProductPolynomial
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) :
    MvPolynomial ι M :=
  ∏ f : L →ₐ[K] M, embeddingPolynomial b f

omit [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K M] [IsGalois K M] in
@[simp]
theorem eval_embeddingProductPolynomial
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (x : L) :
    MvPolynomial.eval
        (fun i ↦ algebraMap K M (b.repr x i))
        (embeddingProductPolynomial
          (M := M) b) =
      ∏ f : L →ₐ[K] M, f x := by
  simp [embeddingProductPolynomial]

/-- The determinant-norm polynomial becomes the product of all embeddings
after extending coefficients to the ambient Galois field. -/
theorem map_normPolynomial_eq_embeddingProductPolynomial
    [Infinite K]
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) :
    MvPolynomial.map (algebraMap K M)
        (normPolynomial b) =
      embeddingProductPolynomial (M := M) b := by
  apply MvPolynomial.funext_set
    (fun _ : ι ↦ Set.range (algebraMap K M))
  · intro i
    exact Set.infinite_range_of_injective
      (algebraMap K M).injective
  · intro c hc
    choose d hd using fun i ↦
      hc i (Set.mem_univ i)
    let x : L :=
      b.repr.symm (Finsupp.equivFunOnFinite.symm d)
    have hcoords :
        c = fun i ↦
          algebraMap K M (b.repr x i) := by
      funext i
      calc
        c i = algebraMap K M (d i) :=
          (hd i).symm
        _ = algebraMap K M (b.repr x i) := by
          simp [x]
    rw [hcoords, eval_embeddingProductPolynomial]
    rw [MvPolynomial.eval_map]
    change MvPolynomial.eval₂ (algebraMap K M)
        ((algebraMap K M) ∘
          fun i ↦ b.repr x i)
        (normPolynomial b) =
      _
    rw [← MvPolynomial.eval₂_comp]
    rw [eval_normPolynomial]
    exact
      norm_eq_prod_embeddings_in_galoisExtension x

/-- Scalar extension of an embedding `L → M` on tensor algebras. -/
def scalarEmbedding
    (A : Type*) [CommRing A] [Algebra K A]
    (f : L →ₐ[K] M) :
    A ⊗[K] L →ₐ[A] A ⊗[K] M :=
  Algebra.TensorProduct.map
    (AlgHom.id A A) f

omit [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M] in
@[simp]
theorem scalarEmbedding_tmul
    (A : Type*) [CommRing A] [Algebra K A]
    (f : L →ₐ[K] M) (a : A) (x : L) :
    scalarEmbedding A f (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] f x :=
  rfl

omit [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M] in
/-- Evaluation of an embedding polynomial after arbitrary scalar extension
is the corresponding tensor-algebra embedding. -/
theorem eval₂_embeddingPolynomial_baseChange
    (A : Type*) [CommRing A] [Algebra K A]
    {ι : Type z} [Fintype ι]
    (b : Module.Basis ι K L) (f : L →ₐ[K] M)
    (x : A ⊗[K] L) :
    MvPolynomial.eval₂
        ((Algebra.TensorProduct.includeRight
          (R := K) (A := A) (B := M)).toRingHom)
        (fun i ↦
          (Algebra.TensorProduct.includeLeft
            (R := K) (S := K) (A := A) (B := M))
            ((Algebra.TensorProduct.basis A b).repr x i))
        (embeddingPolynomial b f) =
      scalarEmbedding A f x := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  simp only [embeddingPolynomial,
    MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_C]
  calc
    ∑ i,
        (Algebra.TensorProduct.includeLeft
          (R := K) (S := K) (A := A) (B := M))
          ((Algebra.TensorProduct.basis A b).repr x i) *
        (Algebra.TensorProduct.includeRight
          (R := K) (A := A) (B := M))
          (f (b i)) =
      ∑ i, scalarEmbedding A f
        (((Algebra.TensorProduct.basis A b).repr x i) •
          Algebra.TensorProduct.basis A b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Algebra.TensorProduct.basis_apply,
          Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.smul_def]
    _ = scalarEmbedding A f
        (∑ i,
          ((Algebra.TensorProduct.basis A b).repr x i) •
            Algebra.TensorProduct.basis A b i) := by
      rw [map_sum]
    _ = scalarEmbedding A f x := by
      rw [(Algebra.TensorProduct.basis A b).sum_repr]

/-- Full scalar-extension norm formula for a subextension of a
finite Galois extension. -/
theorem includeLeft_norm_eq_prod_scalarEmbeddings
    [Infinite K]
    (A : Type*) [CommRing A] [Algebra K A]
    [Nontrivial A] (x : A ⊗[K] L) :
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A) (B := M))
        (Algebra.norm A x) =
      ∏ f : L →ₐ[K] M,
        scalarEmbedding A f x := by
  classical
  let b := Module.Free.chooseBasis K L
  let c : Module.Free.ChooseBasisIndex K L → A :=
    fun i ↦
      (Algebra.TensorProduct.basis A b).repr x i
  let iL : A →+* A ⊗[K] M :=
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A) (B := M)).toRingHom
  let iR : M →+* A ⊗[K] M :=
    (Algebra.TensorProduct.includeRight
      (R := K) (A := A) (B := M)).toRingHom
  have hmaps :
      iL.comp (algebraMap K A) =
        iR.comp (algebraMap K M) := by
    ext t
    simp [iL, iR]
  have hleft :
      MvPolynomial.eval₂ iR
          (fun i ↦ iL (c i))
          (MvPolynomial.map (algebraMap K M)
            (normPolynomial b)) =
        iL (Algebra.norm A x) := by
    rw [MvPolynomial.eval₂_map]
    rw [← hmaps]
    rw [← MvPolynomial.hom_eval₂]
    rw [eval₂_normPolynomial_baseChange]
  have hright :
      MvPolynomial.eval₂ iR
          (fun i ↦ iL (c i))
          (embeddingProductPolynomial
            (M := M) b) =
        ∏ f : L →ₐ[K] M,
          scalarEmbedding A f x := by
    rw [embeddingProductPolynomial,
      MvPolynomial.eval₂_prod]
    apply Finset.prod_congr rfl
    intro f hf
    exact
      eval₂_embeddingPolynomial_baseChange
        A b f x
  change iL (Algebra.norm A x) =
    ∏ f : L →ₐ[K] M,
      scalarEmbedding A f x
  rw [← hright, ← hleft,
    map_normPolynomial_eq_embeddingProductPolynomial b]

/-- Coset form of the scalar-extension formula.  The product is indexed
by `Gal(M/K) / Gal(M/L)`. -/
theorem includeLeft_norm_eq_prod_galoisCosets
    [Infinite K]
    (A : Type*) [CommRing A] [Algebra K A]
    [Nontrivial A] (x : A ⊗[K] L) :
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A) (B := M))
        (Algebra.norm A x) =
      ∏ q :
          (M ≃ₐ[K] M) ⧸
            fixingSubextension
              (K := K) (L := L) (M := M),
        scalarEmbedding A
          (cosetEquivEmbedding q) x := by
  calc
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A) (B := M))
        (Algebra.norm A x) =
      ∏ f : L →ₐ[K] M,
        scalarEmbedding A f x :=
      includeLeft_norm_eq_prod_scalarEmbeddings
        (K := K) (L := L) (M := M) A x
    _ = ∏ q :
          (M ≃ₐ[K] M) ⧸
            fixingSubextension
              (K := K) (L := L) (M := M),
        scalarEmbedding A
          (cosetEquivEmbedding q) x := by
      exact
        ((cosetEquivEmbedding
          (K := K) (L := L) (M := M)).prod_comp
            (fun f ↦ scalarEmbedding A f x)).symm

end UniversalPolynomial

section RelativeAdeles

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [NumberField K]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M]

/-- The cosets used to index relative idele embeddings have a finite enumeration. -/
local instance :
    Fintype
      ((M ≃ₐ[K] M) ⧸
        fixingSubextension
          (K := K) (L := L) (M := M)) :=
  Fintype.ofFinite _

/-- A field embedding inside an ambient Galois extension, extended to
relative adèles. -/
def adeleEmbedding (f : L →ₐ[K] M) :
    RelativeAdeleRing K L →ₐ[
      NumberField.AdeleRing (𝓞 K) K]
      RelativeAdeleRing K M :=
  scalarEmbedding
    (NumberField.AdeleRing (𝓞 K) K) f

/-- The induced homomorphism on relative idèles. -/
def ideleEmbedding (f : L →ₐ[K] M) :
    RelativeIdeleGroup K L →*
      RelativeIdeleGroup K M :=
  Units.map (adeleEmbedding f).toMonoidHom

/-- The embedded-subextension adèle form of the Galois product norm formula. -/
theorem adeleInclusion_norm_eq_prod_embeddings
    (x : RelativeAdeleRing K L) :
    adeleInclusion K M
        (Algebra.norm
          (NumberField.AdeleRing (𝓞 K) K) x) =
      ∏ f : L →ₐ[K] M,
        adeleEmbedding f x := by
  exact
    includeLeft_norm_eq_prod_scalarEmbeddings
      (K := K) (L := L) (M := M)
      (NumberField.AdeleRing (𝓞 K) K) x

/-- The embedded-subextension idèle form of the Galois product norm formula. -/
theorem inclusion_norm_eq_prod_embeddings
    (a : RelativeIdeleGroup K L) :
    inclusion K M (norm K L a) =
      ∏ f : L →ₐ[K] M,
        ideleEmbedding f a := by
  apply Units.ext
  simp only [inclusion, norm, MonoidHom.comp_apply,
    Units.coe_map, Units.coe_prod, ideleEmbedding,
    adeleEmbedding]
  exact
    adeleInclusion_norm_eq_prod_embeddings
      (K := K) (L := L) (M := M)
      (a : RelativeAdeleRing K L)

/-- The literal coset form for arbitrary relative idèles:

`i_{M/K}(N_{L/K}(a)) = ∏_{σ ∈ Gal(M/K)/Gal(M/L)} σ(a)`.
-/
theorem inclusion_norm_eq_prod_galoisCosets
    (a : RelativeIdeleGroup K L) :
    inclusion K M (norm K L a) =
      ∏ q :
          (M ≃ₐ[K] M) ⧸
            fixingSubextension
              (K := K) (L := L) (M := M),
        ideleEmbedding
          (cosetEquivEmbedding q) a := by
  calc
    inclusion K M (norm K L a) =
      ∏ f : L →ₐ[K] M,
        ideleEmbedding f a :=
      inclusion_norm_eq_prod_embeddings
        (K := K) (L := L) (M := M) a
    _ = ∏ q :
          (M ≃ₐ[K] M) ⧸
            fixingSubextension
              (K := K) (L := L) (M := M),
        ideleEmbedding
          (cosetEquivEmbedding q) a := by
      exact
        ((cosetEquivEmbedding
          (K := K) (L := L) (M := M)).prod_comp
            (fun f ↦ ideleEmbedding f a)).symm

end RelativeAdeles

end RelativeIdeleGroup
