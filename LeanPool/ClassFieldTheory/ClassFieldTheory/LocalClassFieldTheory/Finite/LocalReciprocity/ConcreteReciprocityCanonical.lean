/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData

/-! # Concrete Reciprocity Canonical -/

@[expose] public section
namespace LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory

open LocalFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: canonicity of local reciprocity

The construction of local reciprocity realizes a finite Galois extension in
a fixed separable closure.  This file proves that the transported reciprocity
isomorphism is independent of that realization.  Two embeddings are extended
to an automorphism of the separable closure, and
the abstract reciprocity naturality theorem supplies the required naturality.
-/

noncomputable
section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

private abbrev G (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

private abbrev AG (K : Type) [Field K] : Rep ℤ (G K) :=
  intrinsicAbsoluteUnits K

private abbrev B (K : Type) [Field K] : ClosedSubgroup (G K) :=
  intrinsicAbstractBase K

/-! ## Conjugating two realizations -/

/-- An automorphism of the separable closure carrying the image of `i` to
the image of `j`. -/
def finiteGaloisEmbeddingConjugator
    (i j : L →ₐ[K] SeparableClosure K) : G K :=
  ((finiteGaloisFieldRangeEquivOfEmbedding K L i).symm.trans
    (finiteGaloisFieldRangeEquivOfEmbedding K L j)).liftNormal
      (SeparableClosure K)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The chosen absolute Galois conjugator carries one embedding to the other on every element. -/
@[simp]
theorem finiteGaloisEmbeddingConjugator_apply
    (i j : L →ₐ[K] SeparableClosure K) (x : L) :
    finiteGaloisEmbeddingConjugator K L i j (i x) = j x := by
  let ei := finiteGaloisFieldRangeEquivOfEmbedding K L i
  let ej := finiteGaloisFieldRangeEquivOfEmbedding K L j
  let e := ei.symm.trans ej
  have hi :
      algebraMap (finiteGaloisFieldRangeOfEmbedding K L i) (SeparableClosure K)
          (ei x) = i x := by
    rfl
  have hj :
      algebraMap (finiteGaloisFieldRangeOfEmbedding K L j) (SeparableClosure K)
          (e (ei x)) = j x := by
    dsimp only [e]
    rw [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    rfl
  change e.liftNormal (SeparableClosure K) (i x) = j x
  rw [← hi, e.liftNormal_commutes, hj]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Composing the first embedding with its conjugator gives the second embedding. -/
theorem finiteGaloisEmbeddingConjugator_comp
    (i j : L →ₐ[K] SeparableClosure K) :
    (finiteGaloisEmbeddingConjugator K L i j).toAlgHom.comp i = j := by
  ext x
  exact congrArg Subtype.val
    (finiteGaloisEmbeddingConjugator_apply K L i j x)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The two embedded field ranges are related by the chosen Galois conjugator. -/
theorem finiteGaloisFieldRange_conjugator
    (i j : L →ₐ[K] SeparableClosure K) :
    finiteGaloisFieldRangeOfEmbedding K L j =
      (finiteGaloisFieldRangeOfEmbedding K L i).map
        (finiteGaloisEmbeddingConjugator K L i j).toAlgHom := by
  let σ := finiteGaloisEmbeddingConjugator K L i j
  calc
    finiteGaloisFieldRangeOfEmbedding K L j =
        AlgHom.fieldRange (σ.toAlgHom.comp i) := by
      exact congrArg AlgHom.fieldRange
        (finiteGaloisEmbeddingConjugator_comp K L i j).symm
    _ = (finiteGaloisFieldRangeOfEmbedding K L i).map σ.toAlgHom :=
      (AlgHom.map_fieldRange i σ.toAlgHom).symm

omit [FiniteDimensional K L] [IsGalois K L] in
/-- With the right-exponent convention for abstract reciprocity, the conjugating
element is the inverse of the automorphism carrying `i` to `j`. -/
theorem finiteGaloisClosedFixingSubgroup_conjugator
    (i j : L →ₐ[K] SeparableClosure K) :
    conjugateClosedSubgroup
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
        (finiteGaloisEmbeddingConjugator K L i j)⁻¹ =
      finiteGaloisClosedFixingSubgroupOfEmbedding K L j := by
  let σ := finiteGaloisEmbeddingConjugator K L i j
  apply ClosedSubgroup.ext
  have hs :
      (conjugateClosedSubgroup
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) σ⁻¹).toSubgroup =
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L j).toSubgroup := by
    ext τ
    have hc : τ ∈ (conjugateClosedSubgroup
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) σ⁻¹).toSubgroup ↔
        σ⁻¹ * τ * (σ⁻¹)⁻¹ ∈
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup :=
      conjugateClosedSubgroup_mem
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) σ⁻¹ τ
    rw [hc]
    change σ⁻¹ * τ * (σ⁻¹)⁻¹ ∈
        (finiteGaloisFieldRangeOfEmbedding K L i).fixingSubgroup ↔
      τ ∈ (finiteGaloisFieldRangeOfEmbedding K L j).fixingSubgroup
    rw [finiteGaloisFieldRange_conjugator K L i j]
    have hmap := IsGalois.map_fixingSubgroup
      (finiteGaloisFieldRangeOfEmbedding K L i)
      (finiteGaloisEmbeddingConjugator K L i j)
    have hmapmem := congrArg (fun H : Subgroup (G K) => τ ∈ H) hmap
    have hmem := Subgroup.mem_pointwise_smul_iff_inv_smul_mem
      (a := MulAut.conj (finiteGaloisEmbeddingConjugator K L i j))
      (S := (finiteGaloisFieldRangeOfEmbedding K L i).fixingSubgroup)
      (x := τ)
    refine Iff.trans ?_ (Iff.of_eq hmapmem.symm)
    refine Iff.trans ?_ hmem.symm
    simp [σ, mul_assoc]
  exact congrArg (fun H : Subgroup (G K) => H.carrier) hs

/-- The abstract base field is the top subgroup and hence is fixed by every
conjugation. -/
theorem finiteGaloisBase_conjugator
    (σ : G K) : conjugateClosedSubgroup (B K) σ = B K := by
  change conjugateClosedSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K))) σ =
    closedFixingSubgroup K (SeparableClosure K)
      (⊥ : IntermediateField K (SeparableClosure K))
  apply ClosedSubgroup.ext
  have hs :
      (conjugateClosedSubgroup
        (closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K))) σ).toSubgroup =
        (closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup := by
    ext τ
    have hc : τ ∈ (conjugateClosedSubgroup
          (closedFixingSubgroup K (SeparableClosure K)
            (⊥ : IntermediateField K (SeparableClosure K))) σ).toSubgroup ↔
        σ * τ * σ⁻¹ ∈
          (closedFixingSubgroup K (SeparableClosure K)
            (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup :=
      conjugateClosedSubgroup_mem
        (closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K))) σ τ
    rw [hc]
    change σ * τ * σ⁻¹ ∈
        (⊥ : IntermediateField K (SeparableClosure K)).fixingSubgroup ↔
      τ ∈ (⊥ : IntermediateField K (SeparableClosure K)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    simp
  exact congrArg (fun H : Subgroup (G K) => H.carrier) hs

/-- The finite quotient attached to an explicit finite Galois realization. -/
private noncomputable instance
    finiteGaloisAbstractExtensionOfEmbedding_bundle_finite
    (i : L →ₐ[K] SeparableClosure K) :
    Finite ((B K).toSubgroup ⧸
      extensionSubgroup (B K)
        (finiteGaloisAbstractExtensionOfEmbedding K L i).field
        (finiteGaloisAbstractExtensionOfEmbedding K L i).below) :=
  (finiteGaloisAbstractExtensionOfEmbedding K L i).finite

/-- Raw quotient bridge for the explicit closed-fixing-subgroup presentation. -/
noncomputable instance finiteGaloisExtensionQuotientOfEmbedding_finite
    (i : L →ₐ[K] SeparableClosure K) :
    Finite ((B K).toSubgroup ⧸
      extensionSubgroup (B K)
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i))) :=
  baseFixingExtensionQuotient_finite K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)

/-- The representative in the base subgroup obtained by conjugating with
the automorphism carrying `i` to `j`. -/
def finiteGaloisConjugateBaseElement
    (i j : L →ₐ[K] SeparableClosure K) (τ : (B K).toSubgroup) :
    (B K).toSubgroup :=
  ⟨finiteGaloisEmbeddingConjugator K L i j * τ.1 *
      (finiteGaloisEmbeddingConjugator K L i j)⁻¹, by
    change _ ∈ (⊥ : IntermediateField K (SeparableClosure K)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top _⟩

/-! ## The two vertical maps of the abstract reciprocity naturality theorem -/

private noncomputable def extensionQuotientCongr
    {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {K L K' L' : ClosedSubgroup Γ}
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [hN : (extensionSubgroup K L hLK).Normal]
    [hN' : (extensionSubgroup K' L' hL'K').Normal]
    (hK : K = K') (hL : L = L') :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃*
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K') := by
  subst K'
  subst L'
  have hp : hLK = hL'K' := Subsingleton.elim _ _
  subst hL'K'
  exact MulEquiv.refl _

@[simp]
private theorem extensionQuotientCongr_mk
    {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {K L K' L' : ClosedSubgroup Γ}
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [hN : (extensionSubgroup K L hLK).Normal]
    [hN' : (extensionSubgroup K' L' hL'K').Normal]
    (hK : K = K') (hL : L = L') (x : K.toSubgroup) :
    extensionQuotientCongr hLK hL'K' hK hL (QuotientGroup.mk x) =
      QuotientGroup.mk
        (MulEquiv.subgroupCongr
          (congrArg (fun H : ClosedSubgroup Γ => H.toSubgroup) hK) x) := by
  subst K'
  subst L'
  have hp : hLK = hL'K' := Subsingleton.elim _ _
  subst hL'K'
  have hn : hN = hN' := Subsingleton.elim _ _
  subst hN'
  rfl

private noncomputable def finiteNormQuotientCongr
    {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (A : Rep ℤ Γ) {K L K' L' : ClosedSubgroup Γ}
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [hFinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hFinite' : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    (hK : K = K') (hL : L = L') :
    FiniteNormQuotient A K L hLK ≃+
      FiniteNormQuotient A K' L' hL'K' := by
  subst K'
  subst L'
  have hp : hLK = hL'K' := Subsingleton.elim _ _
  subst hL'K'
  exact AddEquiv.refl _

@[simp]
private theorem finiteNormQuotientCongr_finiteNormClass
    {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (A : Rep ℤ Γ) {K L K' L' : ClosedSubgroup Γ}
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [hFinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hFinite' : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    (hK : K = K') (hL : L = L')
    (a : ambientFixedAddSubgroup A K) :
    finiteNormQuotientCongr A hLK hL'K' hK hL
        (finiteNormClass A K L hLK a) =
      finiteNormClass A K' L' hL'K'
        (AddEquiv.addSubgroupCongr
          (congrArg (ambientFixedAddSubgroup A) hK) a) := by
  subst K'
  subst L'
  have hp : hLK = hL'K' := Subsingleton.elim _ _
  subst hL'K'
  have hf : hFinite = hFinite' := Subsingleton.elim _ _
  subst hFinite'
  rfl

/-- Equality transport of both sides of the norm-residue symbol.  This is
the dependent-type form of replacing equal abstract fields in the abstract
reciprocity naturality theorem. -/
private theorem normResidueSymbol_congr
    {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (D : DegreeData Γ) (A : Rep ℤ Γ) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
    [TotallyDisconnectedSpace Γ]
    (K L K' L' : ClosedSubgroup Γ)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [hNormal : (extensionSubgroup K L hLK).Normal]
    [hNormal' : (extensionSubgroup K' L' hL'K').Normal]
    [hFinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hFinite' : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    [hAbsolute : Finite ((baseField Γ).toSubgroup ⧸
      extensionSubgroup (baseField Γ) K (le_baseField K))]
    [hAbsolute' : Finite ((baseField Γ).toSubgroup ⧸
      extensionSubgroup (baseField Γ) K' (le_baseField K'))]
    (hK : K = K') (hL : L = L') :
    let E : FiniteGaloisSubextension K :=
      ⟨L, hLK, hNormal, hFinite⟩
    let E' : FiniteGaloisSubextension K' :=
      ⟨L', hL'K', hNormal', hFinite'⟩
    let KF : FiniteAbstractField Γ := ⟨K, hAbsolute⟩
    let K'F : FiniteAbstractField Γ := ⟨K', hAbsolute'⟩
    let q := MulEquiv.toAdditive
      ((extensionQuotientCongr hLK hL'K' hK hL).abelianizationCongr)
    let b := finiteNormQuotientCongr A
      (hFinite := hFinite) (hFinite' := hFinite')
      hLK hL'K' hK hL
    q.toAddMonoidHom.comp
        (D.normResidueSymbol A v hcf KF E).toAddMonoidHom =
      (D.normResidueSymbol A v hcf K'F E').toAddMonoidHom.comp
        b.toAddMonoidHom := by
  subst K'
  subst L'
  have hp : hLK = hL'K' := Subsingleton.elim _ _
  subst hL'K'
  have hn : hNormal = hNormal' := Subsingleton.elim _ _
  subst hNormal'
  have hf : hFinite = hFinite' := Subsingleton.elim _ _
  subst hFinite'
  have ha : hAbsolute = hAbsolute' := Subsingleton.elim _ _
  subst hAbsolute'
  simp only [extensionQuotientCongr, abelianizationCongr_refl, AddEquiv.toAddMonoidHom_eq_coe,
    finiteNormQuotientCongr, AddEquiv.coe_addMonoidHom_refl, AddMonoidHom.comp_id]
  apply AddMonoidHom.ext
  intro x
  rfl

section EmbeddingConjugation

private theorem finiteGaloisEmbeddingConjugate_normal
    (i : L →ₐ[K] SeparableClosure K) (s : G K) :
    (extensionSubgroup (conjugateClosedSubgroup (B K) s)
      (conjugateClosedSubgroup
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s)
      (conjugateClosedSubgroup_mono
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i)) s)).Normal :=
  conjugateExtension_normal (B K)
    (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
    (fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)) s
    (hLnormal := (finiteGaloisAbstractExtensionOfEmbedding K L i).normal)

attribute [local instance] finiteGaloisEmbeddingConjugate_normal

/-- Conjugation between the two concrete presentations of the abstract extension quotient. -/
def finiteGaloisConjugationOfEmbeddings
    (i j : L →ₐ[K] SeparableClosure K) :
    (finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotient ≃*
      (finiteGaloisAbstractExtensionOfEmbedding K L j).extensionQuotient := by
  let hLK : (finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup ≤
      (B K).toSubgroup :=
    fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)
  let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  have hB := finiteGaloisBase_conjugator K
    (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  have hH := finiteGaloisClosedFixingSubgroup_conjugator K L i j
  let e := finiteReciprocityNaturalityConjugation (B K)
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
      hLK s
  let c := extensionQuotientCongr
    (conjugateClosedSubgroup_mono hLK s)
    (fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L j)) hB hH
  exact
    ((finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotientMulEquiv.trans
      (e.trans c)).trans
        (finiteGaloisAbstractExtensionOfEmbedding K L j).extensionQuotientMulEquiv.symm

/-- Conjugation between embedding models sends a quotient representative to its conjugate class. -/
@[simp]
theorem finiteGaloisConjugationOfEmbeddings_mk
    (i j : L →ₐ[K] SeparableClosure K) (τ : (B K).toSubgroup) :
    finiteGaloisConjugationOfEmbeddings K L i j (QuotientGroup.mk τ) =
      QuotientGroup.mk (finiteGaloisConjugateBaseElement K L i j τ) := by
  let hLK := fixingSubgroupLeBase K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)
  change (finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup ≤
      (B K).toSubgroup at hLK
  let hLjK := fixingSubgroupLeBase K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L j)
  change (finiteGaloisClosedFixingSubgroupOfEmbedding K L j).toSubgroup ≤
      (B K).toSubgroup at hLjK
  let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  have hB := finiteGaloisBase_conjugator K s
  have hH : conjugateClosedSubgroup
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s =
      finiteGaloisClosedFixingSubgroupOfEmbedding K L j :=
    finiteGaloisClosedFixingSubgroup_conjugator K L i j
  change extensionQuotientCongr
      (conjugateClosedSubgroup_mono hLK s)
      hLjK hB hH
      (finiteReciprocityNaturalityConjugation (B K)
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s
        (QuotientGroup.mk τ)) = _
  rw [finiteReciprocityNaturalityConjugation_mk, extensionQuotientCongr_mk]
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  simp [finiteGaloisConjugateBaseElement,
    conjugateSubgroupEquiv_apply_coe, s, mul_assoc]

private theorem finiteGaloisConjugationOfEmbeddings_apply_factor
    (i j : L →ₐ[K] SeparableClosure K)
    (z : (finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotient) :
    let hLK := fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)
    let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
    let hB := finiteGaloisBase_conjugator K s
    let hH := finiteGaloisClosedFixingSubgroup_conjugator K L i j
    finiteGaloisConjugationOfEmbeddings K L i j z =
      extensionQuotientCongr
        (conjugateClosedSubgroup_mono hLK s)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L j)) hB hH
        (finiteReciprocityNaturalityConjugation (B K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s z) := by
  dsimp only
  unfold finiteGaloisConjugationOfEmbeddings
  rfl

private theorem finiteGaloisConjugationOfEmbeddings_abelianization_factor
    (i j : L →ₐ[K] SeparableClosure K)
    (z : Abelianization
      (finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotient) :
    let hLK := fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)
    let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
    let hB := finiteGaloisBase_conjugator K s
    let hH := finiteGaloisClosedFixingSubgroup_conjugator K L i j
    (finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr z =
      (extensionQuotientCongr
        (conjugateClosedSubgroup_mono hLK s)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L j)) hB hH).abelianizationCongr
        ((finiteReciprocityNaturalityConjugation (B K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
          hLK s).abelianizationCongr z) := by
  dsimp only
  let hLK : (finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup ≤
      (B K).toSubgroup :=
    fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)
  let hLjK : (finiteGaloisClosedFixingSubgroupOfEmbedding K L j).toSubgroup ≤
      (B K).toSubgroup :=
    fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L j)
  let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  let e := finiteReciprocityNaturalityConjugation (B K)
    (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s
  let c := extensionQuotientCongr
    (K := conjugateClosedSubgroup (B K) s)
    (L := conjugateClosedSubgroup
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s)
    (K' := B K) (L' := finiteGaloisClosedFixingSubgroupOfEmbedding K L j)
    (conjugateClosedSubgroup_mono hLK s) hLjK
    (finiteGaloisBase_conjugator K s)
    (finiteGaloisClosedFixingSubgroup_conjugator K L i j)
  refine QuotientGroup.induction_on z ?_
  intro x
  change
    (finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr
        (Abelianization.of x) =
      c.abelianizationCongr (e.abelianizationCongr (Abelianization.of x))
  exact (abelianizationCongr_of
      (finiteGaloisConjugationOfEmbeddings K L i j) x).trans
    ((congrArg Abelianization.of
      (finiteGaloisConjugationOfEmbeddings_apply_factor K L i j x)).trans
      ((abelianizationCongr_of c (e x)).symm.trans
        (congrArg c.abelianizationCongr (abelianizationCongr_of e x).symm)))

section EmbeddingNormConjugation

@[instance_reducible]
private def finiteGaloisEmbeddingNormAddZeroClass
    (i : L →ₐ[K] SeparableClosure K) :=
  letI : Finite ((B K).toSubgroup ⧸
      extensionSubgroup (B K)
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i))) :=
    finiteGaloisExtensionQuotientOfEmbedding_finite K L i
  show AddZeroClass (FiniteNormQuotient (AG K) (B K)
    (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
    (fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i))) from
    (finiteNormQuotientAddCommGroup (AG K) (B K)
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
      (fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))).toAddZeroClass

attribute [local instance] finiteGaloisEmbeddingNormAddZeroClass

/-- Conjugation on the finite norm quotients, rewritten so that both its
source and target use the fixed concrete base subgroup. -/
def finiteGaloisNormConjugationOfEmbeddings
    (i j : L →ₐ[K] SeparableClosure K) :
    FiniteNormQuotient (AG K) (B K)
        (finiteGaloisAbstractExtensionOfEmbedding K L i).field
        (finiteGaloisAbstractExtensionOfEmbedding K L i).below →+
      FiniteNormQuotient (AG K) (B K)
        (finiteGaloisAbstractExtensionOfEmbedding K L j).field
        (finiteGaloisAbstractExtensionOfEmbedding K L j).below := by
  let hLK : (finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup ≤
      (B K).toSubgroup :=
    fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)
  let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  have hB := finiteGaloisBase_conjugator K
    (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  have hH := finiteGaloisClosedFixingSubgroup_conjugator K L i j
  let e := finiteReciprocityNaturalityConjugationNormMap (AG K) (B K)
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
      hLK s
  letI := finite_conjugateExtension (B K)
    (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s
  let c := finiteNormQuotientCongr (AG K)
    (K := conjugateClosedSubgroup (B K) s)
    (L := conjugateClosedSubgroup
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s)
    (K' := B K) (L' := finiteGaloisClosedFixingSubgroupOfEmbedding K L j)
    (hFinite := finite_conjugateExtension (B K)
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s)
    (hFinite' := finiteGaloisExtensionQuotientOfEmbedding_finite K L j)
    (conjugateClosedSubgroup_mono hLK s)
    (fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L j)) hB hH
  have hi :
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field =
        finiteGaloisClosedFixingSubgroupOfEmbedding K L i := rfl
  have hj :
      finiteGaloisClosedFixingSubgroupOfEmbedding K L j =
        (finiteGaloisAbstractExtensionOfEmbedding K L j).field := rfl
  let pre := finiteNormQuotientCongr (AG K)
    (hFinite :=
      finiteGaloisAbstractExtensionOfEmbedding_bundle_finite K L i)
    (hFinite' := finiteGaloisExtensionQuotientOfEmbedding_finite K L i)
    (finiteGaloisAbstractExtensionOfEmbedding K L i).below hLK rfl hi
  let post := finiteNormQuotientCongr (AG K)
    (hFinite := finiteGaloisExtensionQuotientOfEmbedding_finite K L j)
    (hFinite' :=
      finiteGaloisAbstractExtensionOfEmbedding_bundle_finite K L j)
    (fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L j))
    (finiteGaloisAbstractExtensionOfEmbedding K L j).below rfl hj
  exact post.toAddMonoidHom.comp
    (c.toAddMonoidHom.comp (e.comp pre.toAddMonoidHom))

end EmbeddingNormConjugation

private theorem finiteGaloisNormConjugationOfEmbeddings_apply_factor
    (i j : L →ₐ[K] SeparableClosure K)
    (a : FiniteNormQuotient (AG K) (B K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field
      (finiteGaloisAbstractExtensionOfEmbedding K L i).below) :
    let hLK := fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)
    let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
    let hB := finiteGaloisBase_conjugator K s
    let hH := finiteGaloisClosedFixingSubgroup_conjugator K L i j
    finiteGaloisNormConjugationOfEmbeddings K L i j a =
      finiteNormQuotientCongr (AG K)
        (hFinite := finite_conjugateExtension (B K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s)
        (hFinite' := finiteGaloisExtensionQuotientOfEmbedding_finite K L j)
        (conjugateClosedSubgroup_mono hLK s)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L j)) hB hH
        (finiteReciprocityNaturalityConjugationNormMap (AG K) (B K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s a) := by
  dsimp only
  unfold finiteGaloisNormConjugationOfEmbeddings
  rfl

/-! ## Concrete comparison on representatives -/

private theorem baseFixingExtensionQuotientEquivGaloisGroup_mk_apply
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    (τ : (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup) (x : E) :
    E.val ((baseFixingExtensionQuotientEquivGaloisGroup K Ω E
      (QuotientGroup.mk τ)) x) = τ.1 (E.val x) := by
  have hq :
      baseFixingExtensionQuotientEquivAmbient K Ω E
          (QuotientGroup.mk τ) =
        QuotientGroup.mk' (closedFixingSubgroup K Ω E).toSubgroup τ.1 := by
    rfl
  have hn := InfiniteGalois.normalAutEquivQuotient_apply
    (closedFixingSubgroup K Ω E) τ.1
  change InfiniteGalois.normalAutEquivQuotient (closedFixingSubgroup K Ω E)
      (QuotientGroup.mk' _ τ.1) = _ at hn
  rw [baseFixingExtensionQuotientEquivGaloisGroup, MulEquiv.trans_apply, hq,
    MulEquiv.trans_apply, hn, AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, IntermediateField.equivOfEq_symm,
    IntermediateField.equivOfEq_apply]
  change
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) τ.1)
      ⟨E.val x, _⟩ : IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) : Ω) =
      τ.1 (E.val x)
  calc
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) τ.1)
      ⟨E.val x, _⟩ : IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) : Ω) =
        τ.1 (E.val x) := by
      rw [AlgEquiv.restrictNormalHom_apply]

/-- Formula for the quotient equivalence on a representative, expressed
without mentioning the auxiliary fixed-field equality used internally. -/
@[simp]
theorem finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
    (i : L →ₐ[K] SeparableClosure K) (τ : (B K).toSubgroup) (x : L) :
    i ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
      (QuotientGroup.mk τ)) x) = τ.1 (i x) := by
  let E := finiteGaloisFieldRangeOfEmbedding K L i
  let e := finiteGaloisFieldRangeEquivOfEmbedding K L i
  let g := baseFixingExtensionQuotientEquivGaloisGroup
    K (SeparableClosure K) E (QuotientGroup.mk τ)
  have hb := baseFixingExtensionQuotientEquivGaloisGroup_mk_apply
    K (SeparableClosure K) E τ (e x)
  have he (y : E) : i (e.symm y) = E.val y := by
    exact congrArg Subtype.val (e.apply_symm_apply y)
  change i (((e.autCongr).symm g) x) = τ.1 (i x)
  calc
    i (((e.autCongr).symm g) x) = E.val (g (e x)) := by
      simpa only [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply,
        AlgEquiv.trans_apply, AlgEquiv.symm_symm] using he (g (e x))
    _ = τ.1 (E.val (e x)) := hb
    _ = τ.1 (i x) := rfl

/-- The explicit norm-quotient comparison sends a base-unit representative
to the same representative in the ordinary field norm quotient. -/
@[simp]
theorem finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit
    (i : L →ₐ[K] SeparableClosure K) (x : Kˣ) :
    finiteNormQuotientEquivEmbeddedNormQuotient
        K (SeparableClosure K) L i
        (finiteNormClass (AG K) (B K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
          (fixingSubgroupLeBase K (SeparableClosure K)
            (finiteGaloisFieldRangeOfEmbedding K L i))
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
            (Additive.ofMul x))) =
      (MonoidHom.toAdditive (normClass K L))
        (Additive.ofMul x) := by
  calc
    finiteNormQuotientEquivEmbeddedNormQuotient
        K (SeparableClosure K) L i
        (finiteNormClass (AG K) (B K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
          (fixingSubgroupLeBase K (SeparableClosure K)
            (finiteGaloisFieldRangeOfEmbedding K L i))
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
            (Additive.ofMul x))) =
      (MulEquiv.toAdditive
        (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
          (localNormSubgroup_fieldRange_eq K (SeparableClosure K) L i)))
        ((MonoidHom.toAdditive (normClass K (AlgHom.fieldRange i)))
          (Additive.ofMul x)) := by
      simp [AG, B, finiteGaloisClosedFixingSubgroupOfEmbedding,
        finiteGaloisFieldRangeOfEmbedding]
    _ = (MonoidHom.toAdditive (normClass K L)) (Additive.ofMul x) := by
      change Additive.ofMul
          ((normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
            (localNormSubgroup_fieldRange_eq K (SeparableClosure K) L i))
              (normClass K (AlgHom.fieldRange i) x)) =
        Additive.ofMul (normClass K L x)
      exact congrArg Additive.ofMul
        (normQuotientEquivOfNormSubgroupEq_normClass K (AlgHom.fieldRange i) L
          (localNormSubgroup_fieldRange_eq K (SeparableClosure K) L i) x)

/-- On a base unit, conjugation of finite norm classes is the identity after
the target base subgroup is identified with the original base subgroup. -/
@[simp]
theorem finiteGaloisNormConjugationOfEmbeddings_finiteNormClass_baseUnit
    (i j : L →ₐ[K] SeparableClosure K) (x : Kˣ) :
    finiteGaloisNormConjugationOfEmbeddings K L i j
        (finiteNormClass (AG K) (B K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
          (fixingSubgroupLeBase K (SeparableClosure K)
            (finiteGaloisFieldRangeOfEmbedding K L i))
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
            (Additive.ofMul x))) =
      finiteNormClass (AG K) (B K)
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L j)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L j))
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul x)) := by
  let hLK := fixingSubgroupLeBase K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)
  let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  have hB := finiteGaloisBase_conjugator K s
  have hH : conjugateClosedSubgroup
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s =
      finiteGaloisClosedFixingSubgroupOfEmbedding K L j :=
    finiteGaloisClosedFixingSubgroup_conjugator K L i j
  let hConjFinite := finite_conjugateExtension (B K)
    (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s
  let a := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
    (Additive.ofMul x)
  have ha :
      AddEquiv.addSubgroupCongr
          (congrArg (ambientFixedAddSubgroup (AG K)) hB)
          (conjugateFixedElement (AG K) (B K) s a) =
      baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
        (Additive.ofMul x) := by
    apply Subtype.ext
    rw [AddEquiv.addSubgroupCongr_apply,
      conjugateFixedElement_coe]
    apply Additive.ext
    apply Units.ext
    change finiteGaloisEmbeddingConjugator K L i j
        (algebraMap K (SeparableClosure K) (x : K)) =
      algebraMap K (SeparableClosure K) (x : K)
    exact (finiteGaloisEmbeddingConjugator K L i j).commutes (x : K)
  let hLjK : (finiteGaloisClosedFixingSubgroupOfEmbedding K L j).toSubgroup ≤
      (B K).toSubgroup :=
    fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L j)
  let c := finiteNormQuotientCongr (AG K)
    (K := conjugateClosedSubgroup (B K) s)
    (L := conjugateClosedSubgroup
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s)
    (K' := B K) (L' := finiteGaloisClosedFixingSubgroupOfEmbedding K L j)
    (hFinite := hConjFinite)
    (hFinite' := finiteGaloisExtensionQuotientOfEmbedding_finite K L j)
    (conjugateClosedSubgroup_mono hLK s) hLjK hB hH
  have hfactor := finiteGaloisNormConjugationOfEmbeddings_apply_factor K L i j
    (finiteNormClass (AG K) (B K)
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK a)
  have hnorm := finiteReciprocityNaturalityConjugationNormMap_finiteNormClass
    (AG K) (B K) (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s a
  have hclass := finiteNormQuotientCongr_finiteNormClass (AG K)
    (K := conjugateClosedSubgroup (B K) s)
    (L := conjugateClosedSubgroup
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s)
    (K' := B K) (L' := finiteGaloisClosedFixingSubgroupOfEmbedding K L j)
    (hFinite := hConjFinite)
    (hFinite' := finiteGaloisExtensionQuotientOfEmbedding_finite K L j)
    (conjugateClosedSubgroup_mono hLK s) hLjK hB hH
    (conjugateFixedElement (AG K) (B K) s a)
  exact hfactor.trans ((congrArg c hnorm).trans
    (hclass.trans (congrArg (finiteNormClass (AG K) (B K)
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L j) hLjK) ha)))

/-! ## The two outer comparison squares -/

/-- The concrete quotient identification is unchanged by conjugating the
chosen realization. -/
theorem finiteGaloisAbstractQuotientEquivGaloisGroup_conjugation
    (i j : L →ₐ[K] SeparableClosure K)
    (z : Abelianization
      (finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotient) :
    (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr
        ((finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr z) =
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).abelianizationCongr z := by
  refine QuotientGroup.induction_on z ?_
  intro q
  have hraw :
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j
          (finiteGaloisConjugationOfEmbeddings K L i j q) =
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q := by
    refine QuotientGroup.induction_on q ?_
    intro τ
    rw [finiteGaloisConjugationOfEmbeddings_mk]
    apply AlgEquiv.ext
    intro x
    apply j.injective
    let σ := finiteGaloisEmbeddingConjugator K L i j
    calc
      j ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j
          (QuotientGroup.mk
            (finiteGaloisConjugateBaseElement K L i j τ))) x) =
          (finiteGaloisConjugateBaseElement K L i j τ).1 (j x) :=
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
          K L j (finiteGaloisConjugateBaseElement K L i j τ) x
      _ = σ (τ.1 (i x)) := by
        have hinv : σ⁻¹ (j x) = i x := by
          apply σ.injective
          simp [σ]
        simp [finiteGaloisConjugateBaseElement, σ, hinv]
      _ = σ (i ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
          (QuotientGroup.mk τ)) x)) := by
        exact congrArg σ
          (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
            K L i τ x).symm
      _ = j ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
          (QuotientGroup.mk τ)) x) :=
        finiteGaloisEmbeddingConjugator_apply K L i j _
  calc
    (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr
        ((finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr
          (Abelianization.of q)) =
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr
        (Abelianization.of
          (finiteGaloisConjugationOfEmbeddings K L i j q)) :=
      congrArg
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr
        (abelianizationCongr_of
          (finiteGaloisConjugationOfEmbeddings K L i j) q)
    _ = Abelianization.of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j
          (finiteGaloisConjugationOfEmbeddings K L i j q)) :=
      abelianizationCongr_of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j) _
    _ = Abelianization.of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q) :=
      congrArg Abelianization.of hraw
    _ = (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).abelianizationCongr
        (Abelianization.of q) :=
      (abelianizationCongr_of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i) q).symm

/-- Additive form of the preceding source comparison. -/
theorem finiteGaloisAbstractQuotientEquivGaloisGroup_conjugation_additive
    (i j : L →ₐ[K] SeparableClosure K)
    (z : Additive (Abelianization
      (finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotient)) :
    MulEquiv.toAdditive
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr)
        (MulEquiv.toAdditive
          ((finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr) z) =
      MulEquiv.toAdditive
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).abelianizationCongr) z
          := by
  apply Additive.toMul.injective
  exact finiteGaloisAbstractQuotientEquivGaloisGroup_conjugation
    K L i j z.toMul

/-- The concrete norm-quotient identification is unchanged by conjugating
the chosen realization. -/
theorem finiteNormQuotientEquivEmbeddedNormQuotient_conjugation
    (i j : L →ₐ[K] SeparableClosure K)
    (a : FiniteNormQuotient (AG K) (B K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field
      (finiteGaloisAbstractExtensionOfEmbedding K L i).below) :
    finiteNormQuotientEquivEmbeddedNormQuotient
        K (SeparableClosure K) L j
        (finiteGaloisNormConjugationOfEmbeddings K L i j a) =
      finiteNormQuotientEquivEmbeddedNormQuotient
        K (SeparableClosure K) L i a := by
  refine FiniteNormQuotient.induction_on (AG K) (B K)
    (finiteGaloisAbstractExtensionOfEmbedding K L i).field
    (finiteGaloisAbstractExtensionOfEmbedding K L i).below a ?_
  intro a₀
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  let x : Additive Kˣ := e.symm a₀
  have hx : e x = a₀ := e.apply_symm_apply a₀
  rw [← hx]
  cases x with
  | ofMul x =>
      change finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L j
          (finiteGaloisNormConjugationOfEmbeddings K L i j
            (finiteNormClass (AG K) (B K)
              (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
              (fixingSubgroupLeBase K (SeparableClosure K)
                (finiteGaloisFieldRangeOfEmbedding K L i))
              (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
                (Additive.ofMul x)))) =
        finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L i
          (finiteNormClass (AG K) (B K)
            (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
            (fixingSubgroupLeBase K (SeparableClosure K)
              (finiteGaloisFieldRangeOfEmbedding K L i))
            (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
              (Additive.ofMul x)))
      rw [finiteGaloisNormConjugationOfEmbeddings_finiteNormClass_baseUnit,
        finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit,
        finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit]

/-! ## The abstract reciprocity naturality theorem and embedding independence -/

/-- The final pointwise diagram chase: the source, middle, and target squares
determine the transported value without any further unfolding. -/
private theorem reciprocityTransport_pointwise
    {A B C D E F : Type}
    (q : A → B) (b : C → D)
    (ri : A ≃ C) (rj : B ≃ D)
    (ni : C → E) (nj : D → E)
    (si : A ≃ F) (sj : B ≃ F)
    (hsource : ∀ z, sj (q z) = si z)
    (hnorm : ∀ a, nj (b a) = ni a)
    (hforward : ∀ z, b (ri z) = rj (q z))
    (x : F) :
    ni (ri (si.symm x)) = nj (rj (sj.symm x)) := by
  have hq : q (si.symm x) = sj.symm x := by
    apply sj.injective
    calc
      sj (q (si.symm x)) = si (si.symm x) := hsource (si.symm x)
      _ = x := si.apply_symm_apply x
      _ = sj (sj.symm x) := (sj.apply_symm_apply x).symm
  calc
    ni (ri (si.symm x)) = nj (b (ri (si.symm x))) :=
      (hnorm (ri (si.symm x))).symm
    _ = nj (rj (q (si.symm x))) := congrArg nj (hforward (si.symm x))
    _ = nj (rj (sj.symm x)) := congrArg (fun z ↦ nj (rj z)) hq

/-- The additive transported reciprocity equivalence is independent of the
embedding into the fixed separable closure. -/
theorem concreteReciprocityAddEquivOfEmbedding_eq
    (i j : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (G K)) (v : ValuationData D (AG K))
    (hcf : SatisfiesClassFieldAxiom (AG K)) :
    concreteReciprocityAddEquivOfEmbedding K L i D v hcf =
      concreteReciprocityAddEquivOfEmbedding K L j D v hcf := by
  let Ei := finiteGaloisAbstractExtensionOfEmbedding K L i
  let Ej := finiteGaloisAbstractExtensionOfEmbedding K L j
  let hBAbsolute : Finite ((baseField (G K)).toSubgroup ⧸
      extensionSubgroup (baseField (G K)) (B K) (le_baseField (B K))) := by
    exact (intrinsicFiniteAbstractBase K).finite
  let hEiNormal :
      (extensionSubgroup
        (intrinsicFiniteAbstractBase K).field Ei.field Ei.below).Normal :=
    Ei.normal
  let hEjNormal :
      (extensionSubgroup
        (intrinsicFiniteAbstractBase K).field Ej.field Ej.below).Normal :=
    Ej.normal
  let q := MulEquiv.toAdditive
    ((finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr)
  let b := finiteGaloisNormConjugationOfEmbeddings K L i j
  let ri := D.abstractReciprocityEquiv
    (AG K) v hcf (intrinsicFiniteAbstractBase K) Ei
  let rj := D.abstractReciprocityEquiv
    (AG K) v hcf (intrinsicFiniteAbstractBase K) Ej
  let ni := finiteNormQuotientEquivEmbeddedNormQuotient
    K (SeparableClosure K) L i
  let nj := finiteNormQuotientEquivEmbeddedNormQuotient
    K (SeparableClosure K) L j
  let si := MulEquiv.toAdditive
    ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).abelianizationCongr)
  let sj := MulEquiv.toAdditive
    ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr)
  have hsource (z : Additive (Abelianization Ei.extensionQuotient)) :
      sj (q z) = si z := by
    exact finiteGaloisAbstractQuotientEquivGaloisGroup_conjugation_additive
      K L i j z
  have hnorm (a : FiniteNormQuotient (AG K) (B K) Ei.field Ei.below) :
      nj (b a) = ni a := by
    exact finiteNormQuotientEquivEmbeddedNormQuotient_conjugation
      K L i j a
  have hinv :
      q.toAddMonoidHom.comp
          (D.normResidueSymbol (AG K) v hcf
            (intrinsicFiniteAbstractBase K) Ei).toAddMonoidHom =
        (D.normResidueSymbol (AG K) v hcf
          (intrinsicFiniteAbstractBase K) Ej).toAddMonoidHom.comp b := by
    let σ := finiteGaloisEmbeddingConjugator K L i j
    let Hi := finiteGaloisClosedFixingSubgroupOfEmbedding K L i
    let Hj := finiteGaloisClosedFixingSubgroupOfEmbedding K L j
    let hLK : Hi.toSubgroup ≤ (B K).toSubgroup :=
      fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i)
    let hLjK : Hj.toSubgroup ≤ (B K).toSubgroup :=
      fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L j)
    let s := σ⁻¹
    have hB := finiteGaloisBase_conjugator K σ⁻¹
    have hH := finiteGaloisClosedFixingSubgroup_conjugator K L i j
    let hConj := conjugateClosedSubgroup_mono hLK s
    let hHiNormal :
        (extensionSubgroup
          (intrinsicFiniteAbstractBase K).field Hi hLK).Normal := by
      exact (finiteGaloisAbstractExtensionOfEmbedding K L i).normal
    let hHiFinite : Finite
        ((intrinsicFiniteAbstractBase K).field.toSubgroup ⧸
          extensionSubgroup (intrinsicFiniteAbstractBase K).field Hi hLK) := by
      exact finiteGaloisExtensionQuotientOfEmbedding_finite K L i
    let hConjNormal :
        (extensionSubgroup ((intrinsicFiniteAbstractBase K).conjugate s).field
          (conjugateClosedSubgroup Hi s) hConj).Normal := by
      exact finiteGaloisEmbeddingConjugate_normal K L i s
    let hConjFinite := finite_conjugateExtension (B K) Hi hLK s
    let hConjAbsolute : Finite ((baseField (G K)).toSubgroup ⧸
        extensionSubgroup (baseField (G K))
          (conjugateClosedSubgroup (B K) s)
          (le_baseField (conjugateClosedSubgroup (B K) s))) :=
      Finite.of_equiv
        ((baseField (G K)).toSubgroup ⧸
          extensionSubgroup (baseField (G K)) (B K) (le_baseField (B K)))
        (by
          simpa [baseField] using
            (absoluteConjugateCosetEquiv (B K) s).symm)
    let q₀ := MonoidHom.toAdditive
      (normResidueNaturalityAbelianizedConjugation (B K) Hi hLK s).toMonoidHom
    let b₀ := finiteReciprocityNaturalityConjugationNormMap (AG K) (B K) Hi hLK s
    let qt := MulEquiv.toAdditive
      ((extensionQuotientCongr hConj hLjK hB hH).abelianizationCongr)
    let bt := finiteNormQuotientCongr (AG K)
      (hFinite := hConjFinite)
      (hFinite' := finiteGaloisExtensionQuotientOfEmbedding_finite K L j)
      hConj hLjK hB hH
    have hraw := D.normResidueNaturality_conjugation (AG K) v hcf
      (intrinsicFiniteAbstractBase K) Hi hLK s
    have htransport := normResidueSymbol_congr D (AG K) v hcf
      (conjugateClosedSubgroup (B K) s)
      (conjugateClosedSubgroup Hi s) (B K) Hj hConj hLjK hB hH
    apply AddMonoidHom.ext
    intro a
    have hrawa := DFunLike.congr_fun hraw a
    have htransporta := DFunLike.congr_fun htransport (b₀ a)
    have hcombined :
        qt (q₀ (D.normResidueSymbol (AG K) v hcf
          (intrinsicFiniteAbstractBase K) Ei a)) =
          D.normResidueSymbol (AG K) v hcf
            (intrinsicFiniteAbstractBase K) Ej (bt (b₀ a)) := by
      exact (congrArg qt hrawa).trans htransporta
    have hqfactor :
        q (D.normResidueSymbol (AG K) v hcf
          (intrinsicFiniteAbstractBase K) Ei a) =
          qt (q₀ (D.normResidueSymbol (AG K) v hcf
            (intrinsicFiniteAbstractBase K) Ei a)) := by
      change Additive.ofMul
          ((finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr
            (D.normResidueSymbol (AG K) v hcf
              (intrinsicFiniteAbstractBase K) Ei a).toMul) =
        Additive.ofMul
          ((extensionQuotientCongr hConj hLjK hB hH).abelianizationCongr
            ((finiteReciprocityNaturalityConjugation (B K) Hi hLK s).abelianizationCongr
              (D.normResidueSymbol (AG K) v hcf
                (intrinsicFiniteAbstractBase K) Ei a).toMul))
      exact congrArg Additive.ofMul
        (finiteGaloisConjugationOfEmbeddings_abelianization_factor
          K L i j
          (D.normResidueSymbol (AG K) v hcf
            (intrinsicFiniteAbstractBase K) Ei a).toMul)
    have hbfactor : b a = bt (b₀ a) := by
      exact finiteGaloisNormConjugationOfEmbeddings_apply_factor K L i j a
    change q (D.normResidueSymbol (AG K) v hcf
      (intrinsicFiniteAbstractBase K) Ei a) =
      D.normResidueSymbol (AG K) v hcf
        (intrinsicFiniteAbstractBase K) Ej (b a)
    exact hqfactor.trans (hcombined.trans
      (congrArg (D.normResidueSymbol (AG K) v hcf
        (intrinsicFiniteAbstractBase K) Ej) hbfactor.symm))
  have hforward (z : Additive (Abelianization Ei.extensionQuotient)) :
      b (ri z) = rj (q z) := by
    have hz := DFunLike.congr_fun hinv (ri z)
    change q (ri.symm (ri z)) = rj.symm (b (ri z)) at hz
    calc
      b (ri z) = rj (rj.symm (b (ri z))) :=
        (rj.apply_symm_apply (b (ri z))).symm
      _ = rj (q (ri.symm (ri z))) := congrArg rj hz.symm
      _ = rj (q z) := by rw [ri.symm_apply_apply]
  apply AddEquiv.ext
  intro x
  change ni (ri (si.symm x)) = nj (rj (sj.symm x))
  exact reciprocityTransport_pointwise q b ri.toEquiv rj.toEquiv ni nj
    si.toEquiv sj.toEquiv hsource hnorm hforward x

end EmbeddingConjugation

/-- Public multiplicative form of embedding independence. -/
theorem concreteReciprocityEquivOfEmbedding_eq
    (i j : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (G K)) (v : ValuationData D (AG K))
    (hcf : SatisfiesClassFieldAxiom (AG K)) :
    concreteReciprocityEquivOfEmbedding K L i D v hcf =
      concreteReciprocityEquivOfEmbedding K L j D v hcf := by
  apply MulEquiv.ext
  intro x
  have h := DFunLike.congr_fun
    (concreteReciprocityAddEquivOfEmbedding_eq K L i j D v hcf)
    (Additive.ofMul x)
  exact congrArg Additive.toMul h

/-- Consequently the norm-residue symbol is also independent of the chosen
embedding. -/
theorem concreteNormResidueSymbolOfEmbedding_eq
    (i j : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (G K)) (v : ValuationData D (AG K))
    (hcf : SatisfiesClassFieldAxiom (AG K)) :
    concreteNormResidueSymbolOfEmbedding K L i D v hcf =
      concreteNormResidueSymbolOfEmbedding K L j D v hcf := by
  rw [concreteNormResidueSymbolOfEmbedding,
    concreteNormResidueSymbolOfEmbedding,
    concreteReciprocityEquivOfEmbedding_eq K L i j D v hcf]

end
end LocalClassFieldTheory
