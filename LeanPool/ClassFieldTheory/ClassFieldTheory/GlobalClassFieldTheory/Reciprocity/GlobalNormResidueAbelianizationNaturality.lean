/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueAbelianization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturality
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteTowerNormProof
/-!
# Naturality of finite-Galois global reciprocity in abelianizations

For a finite tower `K ⊆ M ⊆ N` with `N / K` Galois, this file proves
that ordinary idèle-class norm from `M` to `K` corresponds to restriction
from `Gal(N / M)` to `Gal(N / K)`, after passing both Galois groups to their
abelianizations.  The intermediate extension `M / K` is not assumed Galois.
-/

@[expose] public section

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open AlgebraicNumberTheory
open LocalClassFieldTheory
open KummerTheory
open CyclicCohomology

private theorem abelianizationNaturalityIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] abelianizationNaturalityIdeleClassIsMulCommutative

/-- Transport by an equality-induced field equivalence leaves the underlying
rational direct-limit idèle class unchanged. -/
private theorem rationalIdeleClassEquivFixed_congr_apply_val
    {A B : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (h : A = B)
    (e : B ≃ₐ[ℚ] A)
    (he : e.trans (IntermediateField.equivOfEq h) =
      (AlgEquiv.refl : B ≃ₐ[ℚ] B))
    (c : Additive (IdeleClassGroup B)) :
    ((rationalIdeleClassEquivFixed A)
        (MulEquiv.toAdditive (ideleClassCongr e) c)).1 =
      ((rationalIdeleClassEquivFixed B) c).1 := by
  cases h
  have he' : e = AlgEquiv.refl := by
    apply AlgEquiv.ext
    intro x
    have hx := DFunLike.congr_fun he x
    change e x = x at hx
    exact hx
  rw [he']
  have hc :
      MulEquiv.toAdditive
          (ideleClassCongr (AlgEquiv.refl : A ≃ₐ[ℚ] A)) c = c := by
    cases c with
    | ofMul c =>
        exact congrArg Additive.ofMul (ideleClassCongr_refl c)
  rw [hc]

private theorem rationalIdeleClassEquivFixed_transport_commonTop_val
    {T : Type} [Field T] [NumberField T]
    {A B : IntermediateField ℚ (SeparableClosure ℚ)}
    [hA : FiniteDimensional ℚ A] [hB : FiniteDimensional ℚ B]
    (h : A = B) (e : T ≃ₐ[ℚ] B) (c : IdeleClassGroup T) :
    ((rationalIdeleClassEquivFixed A)
        (Additive.ofMul (ideleClassCongr (K := T) (M := A)
          (e.trans (IntermediateField.equivOfEq h).symm) c))).1 =
      ((rationalIdeleClassEquivFixed B)
        (Additive.ofMul (ideleClassCongr (K := T) (M := B) e c))).1 := by
  cases h
  have he : e.trans (IntermediateField.equivOfEq (rfl : A = A)).symm = e := by
    ext x
    rfl
  rw [he]

section CommonTop

variable
    (K M N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra M N] [Algebra K N]
    [IsScalarTower K M N]

omit [NumberField M] [NumberField N] in
private theorem
    commonTopBaseIntermediateFiniteDimensional
    [FiniteDimensional K N] : FiniteDimensional K M :=
  FiniteDimensional.left K M N

omit [NumberField K] [NumberField M] [NumberField N] in
private theorem
    commonTopIntermediateTopFiniteDimensional
    [FiniteDimensional K N] : FiniteDimensional M N :=
  FiniteDimensional.right K M N

omit [NumberField K] [NumberField M] [NumberField N] in
private theorem
    commonTopIntermediateTopIsGalois
    [IsGalois K N] : IsGalois M N :=
  IsGalois.tower_top_of_isGalois K M N

/-- The two base fixing subgroups obtained from one embedding of the common
top field are nested in the direction dictated by `K ⊆ M`. -/
private theorem numberFieldEmbeddedBaseSubgroup_le_of_commonTop
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    (numberFieldEmbeddedBaseSubgroup M N j).toSubgroup ≤
      (numberFieldEmbeddedBaseSubgroup K N j).toSubgroup := by
  change
    (numberFieldEmbeddedLowerEmbedding M N j).fieldRange.fixingSubgroup ≤
      (numberFieldEmbeddedLowerEmbedding K N j).fieldRange.fixingSubgroup
  apply
    (numberFieldEmbeddedLowerEmbedding K N j).fieldRange.fixingSubgroup_le
  intro x hx
  rcases hx with ⟨y, rfl⟩
  refine ⟨algebraMap K M y, ?_⟩
  change
    j (algebraMap M N (algebraMap K M y)) =
      j (algebraMap K N y)
  rw [IsScalarTower.algebraMap_apply K M N]

/-- In a common finite Galois overfield, the quotient between the two base
fixing subgroups is finite even when the intermediate extension is not
Galois. -/
private theorem
    numberFieldEmbeddedBaseChangeExtensionQuotient_finite_of_commonTop
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    let H := numberFieldEmbeddedBaseSubgroup K N j
    let H' := numberFieldEmbeddedBaseSubgroup M N j
    let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
    Finite
      (H.toSubgroup ⧸
        extensionSubgroup H H' hH'H) := by
  dsimp only
  let H := numberFieldEmbeddedBaseSubgroup K N j
  let H' := numberFieldEmbeddedBaseSubgroup M N j
  let J := numberFieldEmbeddedTopSubgroup K N j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j
  let hJH' : J.toSubgroup ≤ H'.toSubgroup :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup M N j
  let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
  let lower := extensionSubgroup H J hJH
  let intermediate := extensionSubgroup H H' hH'H
  have hle : lower ≤ intermediate := by
    intro sigma hsigma
    rw [mem_extensionSubgroup_iff] at hsigma ⊢
    exact hJH' hsigma
  let : Finite (H.toSubgroup ⧸ lower) := by
    exact numberFieldEmbeddedExtensionQuotient_finite K N j
  let : lower.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let : intermediate.FiniteIndex :=
    Subgroup.finiteIndex_of_le hle
  exact Subgroup.finite_quotient_of_finiteIndex

/-- The abelianized quotient of an explicitly embedded finite Galois tower
is the abelianization of its actual Galois group. -/
noncomputable def
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    Additive
        (Abelianization
          (numberFieldEmbeddedFiniteGaloisSubextension K N j).extensionQuotient) ≃+
      Additive (Abelianization Gal(N/K)) :=
  MulEquiv.toAdditive
    (MulEquiv.abelianizationCongr
      (numberFieldEmbeddedExtensionQuotientEquivGaloisGroup K N j))

/-- The abstract norm-residue symbol followed by the actual Galois
abelianization comparison, with the public finite norm quotient's additive
structure fixed at this boundary. -/
private noncomputable def
    numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ)
    [hRelativeFinite : Finite
      ((numberFieldEmbeddedBaseSubgroup K N j).toSubgroup ⧸
        extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j))] :
    FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j) ≃+
      Additive (Abelianization Gal(N/K)) := by
  let _ : Finite _ :=
    (numberFieldEmbeddedFiniteAbstractField K N j).finite
  let _ :
      (extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K N j
  letI : AddCommGroup
      (FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)) :=
    finiteNormQuotientAddCommGroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K N j)
      (numberFieldEmbeddedTopSubgroup K N j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)
  exact
    @AddEquiv.trans
      (FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j))
      (Additive
        (Abelianization
          (numberFieldEmbeddedFiniteGaloisSubextension K N j).extensionQuotient))
      (Additive (Abelianization Gal(N/K)))
      inferInstance inferInstance inferInstance
      (rationalCyclotomicDegreeData.normResidueSymbol
        rationalIdeleClassRepresentation
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        (numberFieldEmbeddedFiniteAbstractField K N j)
        (numberFieldEmbeddedFiniteGaloisSubextension K N j))
      (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
        K N j)

/-- Evaluation of the typed embedded norm-residue/Galois comparison. -/
private theorem
    numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv_apply
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ)
    [hRelativeFinite : Finite
      ((numberFieldEmbeddedBaseSubgroup K N j).toSubgroup ⧸
        extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j))]
    (x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K N j)
      (numberFieldEmbeddedTopSubgroup K N j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)) :
    numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv K N j x =
      numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
        K N j
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K N j)
          (numberFieldEmbeddedFiniteGaloisSubextension K N j) x) := by
  let hBaseFinite :=
    (numberFieldEmbeddedFiniteAbstractField K N j).finite
  let hExtensionNormal :=
    numberFieldEmbeddedExtensionSubgroup_normal K N j
  rfl

/-- The finite-Galois norm-residue map built from an explicitly supplied
embedding of the top field, with target the actual Galois abelianization. -/
noncomputable def globalNormResidueAbelianizationMonoidHomOfEmbedding
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    IdeleClassGroup K →* Abelianization Gal(N/K) := by
  let hRelativeFinite : Finite
      ((numberFieldEmbeddedBaseSubgroup K N j).toSubgroup ⧸
        extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)) :=
    numberFieldEmbeddedExtensionQuotient_finite K N j
  let e :
      (IdeleClassGroup K ⧸ (_root_.ideleClassNorm K N).range) ≃*
        Abelianization Gal(N/K) :=
    AddEquiv.toMultiplicative
      ((numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K N j).symm.trans
        (numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv
          K N j (hRelativeFinite := hRelativeFinite)))
  exact e.toMonoidHom.comp
    (QuotientGroup.mk' (_root_.ideleClassNorm K N).range)

/-- Evaluation of the explicitly embedded abelianized norm-residue map on
an ordinary idèle class. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHomOfEmbedding_apply
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K) :
    letI _ : Finite
        ((numberFieldEmbeddedBaseSubgroup K N j).toSubgroup ⧸
          extensionSubgroup
            (numberFieldEmbeddedBaseSubgroup K N j)
            (numberFieldEmbeddedTopSubgroup K N j)
            (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)) :=
      numberFieldEmbeddedExtensionQuotient_finite K N j
    globalNormResidueAbelianizationMonoidHomOfEmbedding K N j c =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
          K N j
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldEmbeddedFiniteAbstractField K N j)
            (numberFieldEmbeddedFiniteGaloisSubextension K N j)
            (finiteNormClass rationalIdeleClassRepresentation
              (numberFieldEmbeddedBaseSubgroup K N j)
              (numberFieldEmbeddedTopSubgroup K N j)
              (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)
              (numberFieldEmbeddedIdeleClassEquivAmbientFixed
                K N j (Additive.ofMul c))))) := by
  dsimp only
  let hRelativeFinite : Finite
      ((numberFieldEmbeddedBaseSubgroup K N j).toSubgroup ⧸
        extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)) :=
    numberFieldEmbeddedExtensionQuotient_finite K N j
  have hclass :=
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K N j c
  let x :
      FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j) :=
    finiteNormClass rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K N j)
      (numberFieldEmbeddedTopSubgroup K N j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)
      (numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K N j (Additive.ofMul c))
  let q : Additive
      (IdeleClassGroup K ⧸ (_root_.ideleClassNorm K N).range) :=
    Additive.ofMul
      (QuotientGroup.mk' (_root_.ideleClassNorm K N).range c)
  have hclass' :
      numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K N j x = q :=
    hclass
  have htransport :
      (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K N j).symm q = x := by
    exact
      (congrArg
        (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K N j).symm hclass'.symm).trans
        ((numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K N j).symm_apply_apply x)
  calc
    globalNormResidueAbelianizationMonoidHomOfEmbedding K N j c =
        Additive.toMul
          (numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv
            K N j (hRelativeFinite := hRelativeFinite)
            ((numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
              K N j).symm q)) := by
      rfl
    _ =
        Additive.toMul
          (numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv
            K N j (hRelativeFinite := hRelativeFinite) x) :=
      congrArg
        (fun y =>
          Additive.toMul
            (numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv
              K N j (hRelativeFinite := hRelativeFinite) y))
        htransport
    _ =
        Additive.toMul
          (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
            K N j
            (rationalCyclotomicDegreeData.normResidueSymbol
              rationalIdeleClassRepresentation
              rationalCyclotomicIdeleClassValuationData
              rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
              (numberFieldEmbeddedFiniteAbstractField K N j)
              (numberFieldEmbeddedFiniteGaloisSubextension K N j) x)) := by
      exact congrArg Additive.toMul
        (numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv_apply
          K N j (hRelativeFinite := hRelativeFinite) x)

/-- The standard finite-Galois norm-residue map is the explicit construction
for the standard chosen embedding of the common top field. -/
theorem
    globalNormResidueAbelianizationMonoidHom_eq_ofEmbedding_standard
    [FiniteDimensional K N] [IsGalois K N] :
    globalNormResidueAbelianizationMonoidHom K N =
      globalNormResidueAbelianizationMonoidHomOfEmbedding K N
        (numberFieldSeparableClosureEmbedding N) := by
  let j := numberFieldSeparableClosureEmbedding N
  have hIdeleClassEquiv :
      numberFieldTowerIdeleClassEquivAmbientFixed K N =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed K N j := by
    exact numberFieldTowerIdeleClassEquivAmbientFixed_eq_embedded_standard K N
  have hFiniteAbstractField :
      numberFieldTowerReciprocityFiniteAbstractField K N =
        numberFieldEmbeddedFiniteAbstractField K N j := by
    rfl
  have hSubextension :
      numberFieldTowerFiniteGaloisSubextension K N =
        numberFieldEmbeddedFiniteGaloisSubextension K N j := by
    rfl
  have hGaloisComparison :
      numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization K N =
        numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
          K N j := by
    rfl
  apply MonoidHom.ext
  intro c
  have hTower :=
    globalNormResidueAbelianizationMonoidHom_finiteNormClass K N c
  have hEmbedded :=
    globalNormResidueAbelianizationMonoidHomOfEmbedding_apply K N j c
  exact hTower.trans
    ((show _ = _ by
      simp only [← hIdeleClassEquiv, ← hGaloisComparison]
      cases hFiniteAbstractField
      cases hSubextension
      rfl).trans hEmbedded.symm)

/-- In one common top-field embedding, the abstract relative norm between
the two base fixing subgroups is the ordinary idèle-class norm.  No
normality of the intermediate extension `M / K` is used. -/
theorem
    numberFieldEmbeddedIdeleClassEquivAmbientFixed_relativeNorm_of_commonTop
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup M) :
    letI _ : FiniteDimensional K M :=
      commonTopBaseIntermediateFiniteDimensional K M N
    let H := numberFieldEmbeddedBaseSubgroup K N j
    let H' := numberFieldEmbeddedBaseSubgroup M N j
    let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
    letI _ : Finite (rationalFixedFieldAbsoluteQuotient H) :=
      (numberFieldEmbeddedFiniteAbstractField K N j).finite
    letI _ : Finite
        (rationalFixedFieldRelativeQuotient H H' hH'H) :=
      numberFieldEmbeddedBaseChangeExtensionQuotient_finite_of_commonTop
        K M N j
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (numberFieldEmbeddedIdeleClassEquivAmbientFixed
          M N j (Additive.ofMul c)) =
      numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K N j
        (Additive.ofMul (_root_.ideleClassNorm K M c)) := by
  intro H H'
  let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
  let hHfinite : Finite (rationalFixedFieldAbsoluteQuotient H) := by
    exact (numberFieldEmbeddedFiniteAbstractField K N j).finite
  let hHH'finite : Finite
      (rationalFixedFieldRelativeQuotient H H' hH'H) :=
    numberFieldEmbeddedBaseChangeExtensionQuotient_finite_of_commonTop
      K M N j
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hH'H
  let : NumberField F := by
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H hHfinite
    exact NumberField.of_module_finite ℚ F
  let : NumberField E := by
    let : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H H' hH'H hHfinite hHH'finite
    exact NumberField.of_module_finite F E
  let hE :
      E.restrictScalars ℚ =
        abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    IntermediateField.extendScalars_restrictScalars
      (abstractFixedField_le ℚ (SeparableClosure ℚ) hH'H)
  let eRel :
      E ≃ₐ[ℚ] abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    IntermediateField.equivOfEq hE
  let eK : K ≃ₐ[ℚ] F :=
    numberFieldEmbeddedAbstractBaseFieldEquiv K N j
  let eMBase :
      M ≃ₐ[ℚ] abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    numberFieldEmbeddedAbstractBaseFieldEquiv M N j
  let eM : M ≃ₐ[ℚ] E := eMBase.trans eRel.symm
  have hcompat (x : K) :
      eM (algebraMap K M x) = algebraMap F E (eK x) := by
    apply eRel.injective
    apply Subtype.ext
    change
      j (algebraMap M N (algebraMap K M x)) =
        j (algebraMap K N x)
    rw [IsScalarTower.algebraMap_apply K M N]
  have hupper :
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H
          (Additive.ofMul (ideleClassCongr eM c)) =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed
          M N j (Additive.ofMul c) := by
    apply Subtype.ext
    exact rationalIdeleClassEquivFixed_transport_commonTop_val
      (hA := by change FiniteDimensional ℚ E; infer_instance)
      (hB := numberFieldEmbeddedAbstractFixedFieldFiniteDimensional M N j)
      hE eMBase c
  have hrelative :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm_ofFiniteTower
      H H' hH'H
  unfold rationalAbstractRelativeFixedFieldNormStatement at hrelative
  have hrelativec := hrelative (ideleClassCongr eM c)
  change
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H
          (Additive.ofMul (ideleClassCongr eM c))) =
      rationalAbstractFixedFieldIdeleClassEquivFixed H
        (Additive.ofMul
          (_root_.ideleClassNorm F E (ideleClassCongr eM c)))
    at hrelativec
  calc
    _ = relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed H H' hH'H
          (Additive.ofMul (ideleClassCongr eM c))) :=
      congrArg (relativeNorm rationalIdeleClassRepresentation H H' hH'H) hupper.symm
    _ = rationalAbstractFixedFieldIdeleClassEquivFixed H
        (Additive.ofMul (_root_.ideleClassNorm F E (ideleClassCongr eM c))) :=
      hrelativec
    _ = _ := by
      change
        rationalAbstractFixedFieldIdeleClassEquivFixed H
            (Additive.ofMul (_root_.ideleClassNorm F E (ideleClassCongr eM c))) =
          rationalAbstractFixedFieldIdeleClassEquivFixed H
            (Additive.ofMul (ideleClassCongr eK (_root_.ideleClassNorm K M c)))
      apply congrArg (rationalAbstractFixedFieldIdeleClassEquivFixed H)
      apply congrArg Additive.ofMul
      exact (ideleClassCongr_ideleClassNorm
        (K := K) (K' := F) (L := M) (L' := E) eK eM hcompat c).symm

/-- The canonical quotient-to-Galois comparisons for one common top-field
embedding intertwine abstract restriction with restriction on actual Galois
groups, after abelianization. -/
theorem
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization_restriction
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    letI _ : FiniteDimensional K M :=
      commonTopBaseIntermediateFiniteDimensional K M N
    letI _ : FiniteDimensional M N :=
      commonTopIntermediateTopFiniteDimensional K M N
    letI _ : IsGalois M N :=
      commonTopIntermediateTopIsGalois K M N
    ∀ z : Abelianization
        (numberFieldEmbeddedFiniteGaloisSubextension M N j).extensionQuotient,
    let H := numberFieldEmbeddedBaseSubgroup K N j
    let H' := numberFieldEmbeddedBaseSubgroup M N j
    let J := numberFieldEmbeddedTopSubgroup K N j
    let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j
    let hJH' : J.toSubgroup ≤ H'.toSubgroup :=
      numberFieldEmbeddedTopSubgroup_le_baseSubgroup M N j
    let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
    letI _ : (extensionSubgroup H J hJH).Normal :=
      numberFieldEmbeddedExtensionSubgroup_normal K N j
    letI _ : (extensionSubgroup H' J hJH').Normal :=
      numberFieldEmbeddedExtensionSubgroup_normal M N j
    Abelianization.map
        (AlgEquiv.restrictScalarsHom K : Gal(N/M) →* Gal(N/K))
        (Additive.toMul
          (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
            M N j (Additive.ofMul z))) =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
          K N j
          (MonoidHom.toAdditive
            (normResidueNaturalityAbelianizedRestriction
              H H' J J hJH hJH' hH'H le_rfl)
            (Additive.ofMul z))) := by
  dsimp only
  let : FiniteDimensional K M :=
    commonTopBaseIntermediateFiniteDimensional K M N
  let : FiniteDimensional M N :=
    commonTopIntermediateTopFiniteDimensional K M N
  let : IsGalois M N :=
    commonTopIntermediateTopIsGalois K M N
  intro z
  let H := numberFieldEmbeddedBaseSubgroup K N j
  let H' := numberFieldEmbeddedBaseSubgroup M N j
  let J := numberFieldEmbeddedTopSubgroup K N j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j
  let hJH' : J.toSubgroup ≤ H'.toSubgroup :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup M N j
  let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
  let hLowerNormal : (extensionSubgroup H J hJH).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K N j
  let hUpperNormal : (extensionSubgroup H' J hJH').Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal M N j
  let qLowerRaw :
      (H.toSubgroup ⧸ extensionSubgroup H J hJH) ≃* Gal(N/K) :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup K N j
  let qUpperRaw :
      (H'.toSubgroup ⧸ extensionSubgroup H' J hJH') ≃* Gal(N/M) :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup M N j
  let restrictActual : Gal(N/M) →* Gal(N/K) :=
    AlgEquiv.restrictScalarsHom K
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨sigma, rfl⟩ :=
    (numberFieldEmbeddedFiniteGaloisSubextension M N j).extensionQuotientMk_surjective q
  change
    Abelianization.map restrictActual
        (qUpperRaw.abelianizationCongr
          (Abelianization.of (QuotientGroup.mk sigma))) =
      qLowerRaw.abelianizationCongr
        (normResidueNaturalityAbelianizedRestriction
          H H' J J hJH hJH' hH'H le_rfl
          (Abelianization.of (QuotientGroup.mk sigma)))
  rw [normResidueNaturalityAbelianizedRestriction_of_mk,
    abelianizationCongr_of, abelianizationCongr_of,
    Abelianization.map_of]
  have hraw :
      restrictActual (qUpperRaw (QuotientGroup.mk sigma)) =
        qLowerRaw
          (QuotientGroup.mk (Subgroup.inclusion hH'H sigma)) := by
    apply AlgEquiv.ext
    intro x
    apply j.injective
    let hUpperAlgebra : Algebra M (SeparableClosure ℚ) :=
      numberFieldEmbeddedSeparableClosureAlgebra M N j
    let eUpper := numberFieldEmbeddedSeparableClosureEquiv M N j
    let hLowerAlgebra : Algebra K (SeparableClosure ℚ) :=
      numberFieldEmbeddedSeparableClosureAlgebra K N j
    let eLower := numberFieldEmbeddedSeparableClosureEquiv K N j
    calc
      j (restrictActual (qUpperRaw (QuotientGroup.mk sigma)) x) =
          sigma.1.1 (j x) := by
        exact
          ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
            ℚ M N j eUpper sigma x
      _ = (Subgroup.inclusion hH'H sigma).1.1 (j x) := rfl
      _ = j
          (qLowerRaw
            (QuotientGroup.mk (Subgroup.inclusion hH'H sigma)) x) := by
        exact
          (ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
            ℚ K N j eLower (Subgroup.inclusion hH'H sigma) x).symm
  exact congrArg Abelianization.of hraw

/-- For one embedding of a common finite Galois overfield, the
abelianization-valued global norm-residue maps commute with ordinary
idèle-class norm and restriction.  The intermediate extension need not be
Galois. -/
theorem
    globalNormResidueAbelianizationMonoidHomOfEmbedding_norm_restriction
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    letI _ : FiniteDimensional K M :=
      commonTopBaseIntermediateFiniteDimensional K M N
    letI _ : FiniteDimensional M N :=
      commonTopIntermediateTopFiniteDimensional K M N
    letI _ : IsGalois M N :=
      commonTopIntermediateTopIsGalois K M N
    (Abelianization.map
        (AlgEquiv.restrictScalarsHom K : Gal(N/M) →* Gal(N/K))).comp
        (globalNormResidueAbelianizationMonoidHomOfEmbedding M N j) =
      (globalNormResidueAbelianizationMonoidHomOfEmbedding K N j).comp
        (_root_.ideleClassNorm K M) := by
  let : FiniteDimensional K M :=
    commonTopBaseIntermediateFiniteDimensional K M N
  let : FiniteDimensional M N :=
    commonTopIntermediateTopFiniteDimensional K M N
  let : IsGalois M N :=
    commonTopIntermediateTopIsGalois K M N
  let H := numberFieldEmbeddedBaseSubgroup K N j
  let H' := numberFieldEmbeddedBaseSubgroup M N j
  let J := numberFieldEmbeddedTopSubgroup K N j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j
  let hJH' : J.toSubgroup ≤ H'.toSubgroup :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup M N j
  let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
  let hLowerNormal : (extensionSubgroup H J hJH).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K N j
  let hLowerFinite :
      Finite (H.toSubgroup ⧸ extensionSubgroup H J hJH) :=
    numberFieldEmbeddedExtensionQuotient_finite K N j
  let hUpperNormal : (extensionSubgroup H' J hJH').Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal M N j
  let hUpperFinite :
      Finite (H'.toSubgroup ⧸ extensionSubgroup H' J hJH') :=
    numberFieldEmbeddedExtensionQuotient_finite M N j
  let hHH'finite :=
    numberFieldEmbeddedBaseChangeExtensionQuotient_finite_of_commonTop
      K M N j
  let T :
      FiniteAbstractFieldExtension
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    { field := numberFieldEmbeddedFiniteAbstractField M N j
      base := numberFieldEmbeddedFiniteAbstractField K N j
      below := hH'H
      finiteQuotient := hHH'finite }
  let hTBaseNormal :
      (extensionSubgroup T.base.field J hJH).Normal := by
    change (extensionSubgroup H J hJH).Normal
    exact hLowerNormal
  let hTBaseFinite :
      Finite
        (T.base.field.toSubgroup ⧸
          extensionSubgroup T.base.field J hJH) := by
    change Finite (H.toSubgroup ⧸ extensionSubgroup H J hJH)
    exact hLowerFinite
  let hTFieldNormal :
      (extensionSubgroup T.field.field J hJH').Normal := by
    change (extensionSubgroup H' J hJH').Normal
    exact hUpperNormal
  let hTFieldFinite :
      Finite
        (T.field.field.toSubgroup ⧸
          extensionSubgroup T.field.field J hJH') := by
    change Finite (H'.toSubgroup ⧸ extensionSubgroup H' J hJH')
    exact hUpperFinite
  let restrictActual : Gal(N/M) →* Gal(N/K) :=
    AlgEquiv.restrictScalarsHom K
  apply MonoidHom.ext
  intro c
  let a :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed
      M N j (Additive.ofMul c)
  have hnat :=
    DegreeData.normResidueNaturality_norm_restriction
      (D := rationalCyclotomicDegreeData)
      (A := rationalIdeleClassRepresentation)
      (v := rationalCyclotomicIdeleClassValuationData)
      (hcf := rationalIdeleClassRepresentation_satisfiesClassFieldAxiom)
      (T := T) (L := J) (L' := J)
      (hLnormal := hTBaseNormal)
      (hL'normal := hTFieldNormal)
      (hLKfinite := hTBaseFinite)
      (hL'K'finite := hTFieldFinite)
      hJH hJH' le_rfl
  have hnatc :=
    DFunLike.congr_fun hnat
      (finiteNormClass rationalIdeleClassRepresentation
        H' J hJH' a)
  change _ =
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      T.base
      { field := J
        below := hJH
        normal := hTBaseNormal
        finite := hTBaseFinite }
      (finiteReciprocityNaturalityNormMap
        rationalIdeleClassRepresentation
        T.base.field T.field.field J J
        hJH hJH' T.below le_rfl
        (finiteNormClass rationalIdeleClassRepresentation
          T.field.field J hJH' a)) at hnatc
  rw [finiteReciprocityNaturalityNormMap_finiteNormClass] at hnatc
  have hnorm :
      relativeNorm rationalIdeleClassRepresentation H H' hH'H a =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed K N j
          (Additive.ofMul (_root_.ideleClassNorm K M c)) :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed_relativeNorm_of_commonTop
      K M N j c
  calc
    Abelianization.map restrictActual
        (globalNormResidueAbelianizationMonoidHomOfEmbedding M N j c) =
      Abelianization.map restrictActual
        (Additive.toMul
          (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
            M N j
            (rationalCyclotomicDegreeData.normResidueSymbol
              rationalIdeleClassRepresentation
              rationalCyclotomicIdeleClassValuationData
              rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
              (numberFieldEmbeddedFiniteAbstractField M N j)
              (numberFieldEmbeddedFiniteGaloisSubextension M N j)
              (finiteNormClass rationalIdeleClassRepresentation
                H' J hJH' a)))) := by
      rw [globalNormResidueAbelianizationMonoidHomOfEmbedding_apply]
    _ =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
          K N j
          (MonoidHom.toAdditive
            (normResidueNaturalityAbelianizedRestriction
              H H' J J hJH hJH' hH'H le_rfl)
            (rationalCyclotomicDegreeData.normResidueSymbol
              rationalIdeleClassRepresentation
              rationalCyclotomicIdeleClassValuationData
              rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
              (numberFieldEmbeddedFiniteAbstractField M N j)
              (numberFieldEmbeddedFiniteGaloisSubextension M N j)
              (finiteNormClass rationalIdeleClassRepresentation
                H' J hJH' a)))) := by
      exact
        numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization_restriction
          K M N j _
    _ =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
          K N j
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldEmbeddedFiniteAbstractField K N j)
            (numberFieldEmbeddedFiniteGaloisSubextension K N j)
            (finiteNormClass rationalIdeleClassRepresentation
              H J hJH
              (relativeNorm rationalIdeleClassRepresentation
                H H' hH'H a)))) := by
      exact congrArg
        (fun z =>
          Additive.toMul
            (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
              K N j z))
        hnatc
    _ =
      globalNormResidueAbelianizationMonoidHomOfEmbedding K N j
        (_root_.ideleClassNorm K M c) := by
      rw [hnorm,
        ← globalNormResidueAbelianizationMonoidHomOfEmbedding_apply]

/-- Global norm-residue naturality in Galois abelianizations for a finite
tower with a common Galois top field.  No Galois hypothesis is imposed on
the intermediate extension. -/
theorem globalNormResidueAbelianizationMonoidHom_norm_restriction
    [FiniteDimensional K N] [IsGalois K N] :
    letI _ : FiniteDimensional K M :=
      commonTopBaseIntermediateFiniteDimensional K M N
    letI _ : FiniteDimensional M N :=
      commonTopIntermediateTopFiniteDimensional K M N
    letI _ : IsGalois M N :=
      commonTopIntermediateTopIsGalois K M N
    (Abelianization.map
        (AlgEquiv.restrictScalarsHom K : Gal(N/M) →* Gal(N/K))).comp
        (globalNormResidueAbelianizationMonoidHom M N) =
      (globalNormResidueAbelianizationMonoidHom K N).comp
        (_root_.ideleClassNorm K M) := by
  let : FiniteDimensional K M :=
    commonTopBaseIntermediateFiniteDimensional K M N
  let : FiniteDimensional M N :=
    commonTopIntermediateTopFiniteDimensional K M N
  let : IsGalois M N :=
    commonTopIntermediateTopIsGalois K M N
  rw [globalNormResidueAbelianizationMonoidHom_eq_ofEmbedding_standard,
    globalNormResidueAbelianizationMonoidHom_eq_ofEmbedding_standard]
  exact
    globalNormResidueAbelianizationMonoidHomOfEmbedding_norm_restriction
      K M N (numberFieldSeparableClosureEmbedding N)

end CommonTop

end Reciprocity
end GlobalClassFieldTheory
