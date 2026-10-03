/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Basic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedInertiaComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldNormResidueNaturality
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient
/-!
# Fixed-field norm quotients

This module compares cohomological finite norm quotients with ordinary field-norm quotients and
  records their compatibility with fixed-field norm-residue symbols.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The fixed-field units equivalence sends the cohomological finite norm
subgroup to the additive form of the ordinary field-norm subgroup. -/
theorem map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroup
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsSepClosed Ω]
    (K L : ClosedSubgroup Gal(Ω/k))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField Gal(Ω/k)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/k)) K
          (le_baseField K))] :
    (finiteNormSubgroup (galoisAmbientUnitsRep k Ω) K L hLK).map
        (abstractFixedFieldUnitsEquivGaloisFixed
          k Ω K).symm.toAddMonoidHom =
      additiveNormSubgroup
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) := by
  let F : IntermediateField k Ω :=
    abstractFixedField k Ω K
  let E : IntermediateField F Ω :=
    abstractRelativeFixedField k Ω hLK
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  let e := abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨b, rfl⟩
    let u : Eˣ := Additive.toMul
      ((abstractRelativeFixedFieldUnitsEquivGaloisFixed
        k Ω K L hLK).symm b)
    have hb :
        abstractRelativeFixedFieldUnitsEquivGaloisFixed
            k Ω K L hLK (Additive.ofMul u) = b := by
      change
        abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
            ((abstractRelativeFixedFieldUnitsEquivGaloisFixed
              k Ω K L hLK).symm b) = b
      exact
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK).apply_symm_apply b
    rw [← hb,
      relativeNorm_abstractFixedFieldUnit_eq_normUnits
        k Ω K L hLK]
    change e.symm
        (e (Additive.ofMul (normUnits F E u))) ∈ additiveNormSubgroup F E
    rw [e.symm_apply_apply]
    exact ⟨u, rfl⟩
  · intro hy
    change Additive.toMul y ∈ localNormSubgroup F E at hy
    rcases hy with ⟨u, hu⟩
    refine
      ⟨e (Additive.ofMul (normUnits F E u)), ?_, ?_⟩
    · refine
        ⟨abstractRelativeFixedFieldUnitsEquivGaloisFixed
            k Ω K L hLK (Additive.ofMul u), ?_⟩
      exact
        relativeNorm_abstractFixedFieldUnit_eq_normUnits
          k Ω K L hLK u
    · change e.symm
        (e (Additive.ofMul (normUnits F E u))) = y
      rw [e.symm_apply_apply]
      exact congrArg Additive.ofMul hu

/-- The cohomological finite norm quotient for a pair of closed subgroups is
additively equivalent to the ordinary norm quotient of their fixed fields. -/
noncomputable def fixedFieldFiniteNormQuotientEquivNormQuotient
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsSepClosed Ω]
    (K L : ClosedSubgroup Gal(Ω/k))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField Gal(Ω/k)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/k)) K
          (le_baseField K))] :
    FiniteNormQuotient (galoisAmbientUnitsRep k Ω) K L hLK ≃+
      Additive
        (NormQuotient
          (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK)) := by
  let F : IntermediateField k Ω :=
    abstractFixedField k Ω K
  let E : IntermediateField F Ω :=
    abstractRelativeFixedField k Ω hLK
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  let S := finiteNormSubgroup (galoisAmbientUnitsRep k Ω) K L hLK
  let normAdd : Additive Fˣ →+ Additive (NormQuotient F E) :=
    MonoidHom.toAdditive (normClass F E)
  let T := normAdd.ker
  let e := abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  have hmap : S.map e.symm.toAddMonoidHom = T := by
    simpa [S, T, normAdd, e] using
      (map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroup
        k Ω K L hLK).trans
        (additiveNormSubgroup_eq_ker_quotient_map F E)
  have hforward : S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro x hx
    change e.symm x ∈ T
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hinverse : T ≤ AddSubgroup.comap e.toAddMonoidHom S := by
    intro y hy
    change e y ∈ S
    have hy' : y ∈ S.map e.symm.toAddMonoidHom := by
      rw [hmap]
      exact hy
    rcases hy' with ⟨x, hx, hxy⟩
    have heq : e y = x := by
      apply e.symm.injective
      simpa using hxy.symm
    rw [heq]
    exact hx
  let f :
      (ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) K ⧸ S) →+
        (Additive Fˣ ⧸ T) :=
    QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
  let g :
      (Additive Fˣ ⧸ T) →+
        (ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) K ⧸ S) :=
    QuotientAddGroup.map T S e.toAddMonoidHom hinverse
  let modelEquiv :
      (ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) K ⧸ S) ≃+
        (Additive Fˣ ⧸ T) :=
    { toFun := f
      invFun := g
      left_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change ↑(e (e.symm x)) =
          (↑x : ambientFixedAddSubgroup
            (galoisAmbientUnitsRep k Ω) K ⧸ S)
        rw [e.apply_symm_apply]
      right_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change ↑(e.symm (e x)) = (↑x : Additive Fˣ ⧸ T)
        rw [e.symm_apply_apply]
      map_add' := f.map_add }
  let quotientEquiv :
      (Additive Fˣ ⧸ T) ≃+ Additive (NormQuotient F E) :=
    QuotientAddGroup.quotientKerEquivOfSurjective normAdd
      (QuotientGroup.mk'_surjective
        (localNormSubgroup
          (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK)))
  exact
    (finiteNormQuotientConcreteEquiv
      (galoisAmbientUnitsRep k Ω) K L hLK).trans
      (modelEquiv.trans quotientEquiv)

/-- The fixed-field norm-quotient equivalence sends a cohomological finite norm
class to the ordinary norm class of the corresponding fixed-field unit. -/
theorem fixedFieldFiniteNormQuotientEquivNormQuotient_finiteNormClass
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsSepClosed Ω]
    (K L : ClosedSubgroup Gal(Ω/k))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField Gal(Ω/k)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/k)) K
          (le_baseField K))]
    (a : ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) K) :
    fixedFieldFiniteNormQuotientEquivNormQuotient
        k Ω K L hLK
        (finiteNormClass (galoisAmbientUnitsRep k Ω) K L hLK a) =
      MonoidHom.toAdditive
        (normClass
          (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK))
        ((abstractFixedFieldUnitsEquivGaloisFixed k Ω K).symm a) := by
  let F : IntermediateField k Ω :=
    abstractFixedField k Ω K
  let E : IntermediateField F Ω :=
    abstractRelativeFixedField k Ω hLK
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  let S := finiteNormSubgroup (galoisAmbientUnitsRep k Ω) K L hLK
  let normAdd : Additive Fˣ →+ Additive (NormQuotient F E) :=
    MonoidHom.toAdditive (normClass F E)
  let T := normAdd.ker
  let e := abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  have hmap : S.map e.symm.toAddMonoidHom = T := by
    simpa [S, T, normAdd, e] using
      (map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroup
        k Ω K L hLK).trans
        (additiveNormSubgroup_eq_ker_quotient_map F E)
  have hforward : S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro x hx
    change e.symm x ∈ T
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  simp only [fixedFieldFiniteNormQuotientEquivNormQuotient,
    finiteNormQuotientConcreteEquiv_finiteNormClass,
    AddEquiv.trans_apply,
    QuotientAddGroup.quotientKerEquivOfSurjective,
    QuotientAddGroup.quotientKerEquivOfRightInverse]
  change QuotientAddGroup.kerLift normAdd
      (QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
        (QuotientAddGroup.mk' S a)) =
    normAdd (e.symm a)
  rw [QuotientAddGroup.map_mk', QuotientAddGroup.kerLift_mk]
  rfl

/-- The abstract fixed-field norm-residue symbol of the relative norm of a
prime element is the prescribed Frobenius quotient class. -/
theorem abstractFixedFieldNormResidueSymbol_apply_primeNorm
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω]
    (D : DegreeData Gal(Ω/k))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k Ω))
    (K L : ClosedSubgroup Gal(Ω/k))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField Gal(Ω/k)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/k)) K
          (le_baseField K))]
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (σ : D.FrobeniusElements
      ((⟨K, hKabsolute⟩ : FiniteAbstractField
        Gal(Ω/k)).toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      ((⟨K, hKabsolute⟩ : FiniteAbstractField
        Gal(Ω/k)).toFiniteResidueAbstractField D) L hLK σ = q)
    (π : ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω)
      (D.frobeniusFixedField
        ((⟨K, hKabsolute⟩ : FiniteAbstractField
          Gal(Ω/k)).toFiniteResidueAbstractField D)
        L hLK σ))
    (hπ :
      let KF : FiniteAbstractField Gal(Ω/k) :=
        ⟨K, hKabsolute⟩
      let KR := KF.toFiniteResidueAbstractField D
      let S := D.frobeniusFixedField KR L hLK σ
      let hSK := D.frobeniusFixedField_le KR L hLK σ
      letI : Finite
          (K.toSubgroup ⧸ extensionSubgroup K S hSK) :=
        D.frobeniusFixedField_finite KR L hLK σ
      let Sigma : FiniteAbstractField Gal(Ω/k) :=
        ⟨S, D.frobeniusFixedField_absoluteFinite KF L hLK σ⟩
      v.IsPrimeElement Sigma π) :
    let KF : FiniteAbstractField Gal(Ω/k) :=
      ⟨K, hKabsolute⟩
    let KR := KF.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.toSubgroup ⧸ extensionSubgroup K S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    let x : (abstractFixedField k Ω K)ˣ :=
      Additive.toMul
        ((abstractFixedFieldUnitsEquivGaloisFixed k Ω K).symm
          (relativeNorm (galoisAmbientUnitsRep k Ω)
            K S hSK π))
    abstractFixedFieldNormResidueSymbol
        k Ω D v hcf K L hLK (Additive.ofMul x) =
      Additive.ofMul
        ((abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).abelianizationCongr
          (Abelianization.of q)) := by
  dsimp only
  let KF : FiniteAbstractField Gal(Ω/k) :=
    ⟨K, hKabsolute⟩
  let E : FiniteGaloisSubextension KF.field :=
    ⟨L, hLK, hnormal, hfinite⟩
  let KR := KF.toFiniteResidueAbstractField D
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK := D.frobeniusFixedField_le KR L hLK σ
  let hSfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let qGal :=
    abstractExtensionQuotientEquivGaloisGroup
      k Ω K L hLK hnormal
  let b :=
    abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  let a :=
    relativeNorm (galoisAmbientUnitsRep k Ω) K S hSK π
  let x : (abstractFixedField k Ω K)ˣ :=
    Additive.toMul (b.symm a)
  have hbase : b (Additive.ofMul x) = a := by
    change b (b.symm a) = a
    exact b.apply_symm_apply a
  have hprime :
      D.finiteReciprocityHom
          (galoisAmbientUnitsRep k Ω) v
          (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
          KF L hLK (Additive.ofMul q) =
        finiteNormClass (galoisAmbientUnitsRep k Ω)
          K L hLK a := by
    simpa only [KF, KR, S, hSK, a] using
      D.finiteReciprocityHom_apply_eq_primeNormClass
        (galoisAmbientUnitsRep k Ω) v
        (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
        KF L hLK (Additive.ofMul q) σ hσ π hπ
  change
    (MulEquiv.toAdditive qGal.abelianizationCongr)
        (D.normResidueSymbol
          (galoisAmbientUnitsRep k Ω) v hcf KF E
          (finiteNormClass (galoisAmbientUnitsRep k Ω)
            K L hLK (b (Additive.ofMul x)))) =
      Additive.ofMul
        (qGal.abelianizationCongr (Abelianization.of q))
  rw [hbase, ← hprime]
  exact congrArg
    (fun z : Additive (Abelianization E.extensionQuotient) =>
      MulEquiv.toAdditive qGal.abelianizationCongr z)
    (D.normResidueSymbol_finiteReciprocityHom
      (galoisAmbientUnitsRep k Ω) v hcf KF E
      (show E.extensionQuotient from q))

/-- The abstract fixed-field norm-residue symbol depends only on the norm
class of the input unit. -/
theorem abstractFixedFieldNormResidueSymbol_eq_of_normClass_eq
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsSepClosed Ω]
    (D : DegreeData Gal(Ω/k))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k Ω))
    (K L : ClosedSubgroup Gal(Ω/k))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField Gal(Ω/k)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/k)) K
          (le_baseField K))]
    (x y : (abstractFixedField k Ω K)ˣ)
    (hxy :
      normClass (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK) x =
        normClass (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK) y) :
    abstractFixedFieldNormResidueSymbol
        k Ω D v hcf K L hLK (Additive.ofMul x) =
      abstractFixedFieldNormResidueSymbol
        k Ω D v hcf K L hLK (Additive.ofMul y) := by
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω hLK
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  let b :=
    abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  have hfiniteClass :
      finiteNormClass (galoisAmbientUnitsRep k Ω)
          K L hLK (b (Additive.ofMul x)) =
        finiteNormClass (galoisAmbientUnitsRep k Ω)
          K L hLK (b (Additive.ofMul y)) := by
    apply
      (fixedFieldFiniteNormQuotientEquivNormQuotient
        k Ω K L hLK).injective
    rw [
      fixedFieldFiniteNormQuotientEquivNormQuotient_finiteNormClass,
      fixedFieldFiniteNormQuotientEquivNormQuotient_finiteNormClass]
    simpa [b, F, E] using congrArg Additive.ofMul hxy
  change
    (MulEquiv.toAdditive
      (abstractExtensionQuotientEquivGaloisGroup
        k Ω K L hLK hnormal).abelianizationCongr)
        (D.normResidueSymbol
          (galoisAmbientUnitsRep k Ω) v hcf
          (⟨K, hKabsolute⟩ : FiniteAbstractField
            Gal(Ω/k))
          (⟨L, hLK, hnormal, hfinite⟩ :
            FiniteGaloisSubextension K)
          (finiteNormClass (galoisAmbientUnitsRep k Ω)
            K L hLK (b (Additive.ofMul x)))) =
      (MulEquiv.toAdditive
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).abelianizationCongr)
        (D.normResidueSymbol
          (galoisAmbientUnitsRep k Ω) v hcf
          (⟨K, hKabsolute⟩ : FiniteAbstractField
            Gal(Ω/k))
          (⟨L, hLK, hnormal, hfinite⟩ :
            FiniteGaloisSubextension K)
          (finiteNormClass (galoisAmbientUnitsRep k Ω)
            K L hLK (b (Additive.ofMul y))))
  rw [hfiniteClass]

/-- The ambient abstract quotient equivalence and the intrinsic finite-Galois
quotient equivalence agree on classes transported through a separable-closure
equivalence. -/
theorem fixedFieldQuotientEquiv_mk_compatibility
    (K : Type) [Field K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (τ : (intrinsicAbstractBase F).toSubgroup),
    let E := abstractRelativeFixedField K (SeparableClosure K) hJH
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        K (SeparableClosure K) H.field J hJH H.finite hJfinite
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        K (SeparableClosure K) H.field J hJH hJnormal
    let i : E →ₐ[F] SeparableClosure F :=
      e.symm.toAlgHom.comp E.val
    let φ :
        Gal(SeparableClosure F/F) ≃*
          H.field.toSubgroup :=
      (AlgEquiv.autCongr e).trans
        (abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H.field).symm
    abstractExtensionQuotientEquivGaloisGroup
          K (SeparableClosure K) H.field J hJH hJnormal
          (QuotientGroup.mk (φ τ.1)) =
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          F E i (QuotientGroup.mk τ) := by
  dsimp only
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  intro e τ
  let E := abstractRelativeFixedField K (SeparableClosure K) hJH
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field J hJH H.finite hJfinite
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field J hJH hJnormal
  let i : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp E.val
  let φ :
      Gal(SeparableClosure F/F) ≃*
        H.field.toSubgroup :=
    (AlgEquiv.autCongr e).trans
      (abstractSubgroupEquivGaloisGroup
        K (SeparableClosure K) H.field).symm
  let qH :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H.field J hJH hJnormal
  let qF :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      F E i
  apply AlgEquiv.ext
  intro x
  apply E.val.injective
  have hφ :
      abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H.field (φ τ.1) =
        AlgEquiv.autCongr e τ.1 :=
    by
      let A :=
        abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H.field
      change A (A.symm (AlgEquiv.autCongr e τ.1)) =
        AlgEquiv.autCongr e τ.1
      exact A.apply_symm_apply (AlgEquiv.autCongr e τ.1)
  calc
    E.val (qH (QuotientGroup.mk (φ τ.1)) x) =
        (φ τ.1).1 (E.val x) :=
      (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
        K (SeparableClosure K) H.field J hJH hJnormal
        (φ τ.1) x).symm
    _ =
        abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H.field (φ τ.1) (E.val x) := by
      exact
        (abstractSubgroupEquivGaloisGroup_apply
          K (SeparableClosure K) H.field (φ τ.1) (E.val x)).symm
    _ = (AlgEquiv.autCongr e τ.1) (E.val x) := by
      exact DFunLike.congr_fun hφ (E.val x)
    _ = e (τ.1 (e.symm (E.val x))) := rfl
    _ = e (τ.1 (i x)) := rfl
    _ = e (i (qF (QuotientGroup.mk τ) x)) := by
      exact congrArg e
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
          F E i τ x).symm
    _ = E.val (qF (QuotientGroup.mk τ) x) :=
      e.apply_symm_apply (E.val (qF (QuotientGroup.mk τ) x))

end LocalClassFieldTheory
