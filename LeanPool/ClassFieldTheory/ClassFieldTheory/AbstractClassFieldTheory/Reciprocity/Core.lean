/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension

/-! # Core -/
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# Abstract reciprocity, the unramified cohomology consequence

The class field axiom implies the unit-cohomology axiom for every finite unramified
extension.  The proof follows: degree minus one is reduced to
the corresponding assertion for `A_L`, after correcting a primitive by an
element of `A_K` with the same valuation; in degree zero, valuation induces
a surjection from `A_K / N A_L` to `Z / [L : K] Z`, and equality of the two
orders makes this map injective.
-/

noncomputable section

open CategoryTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

private theorem valueModulo_nsmul
    (v : ValuationData D A) (n : ℕ) (hn : 0 < n)
    (z : v.valueGroup) :
    v.valueModulo n hn (n • z) = 0 := by
  have hq :
      (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) (n • z) = 0 := by
    apply (QuotientAddGroup.eq_zero_iff _).2
    exact ⟨z, rfl⟩
  change (v.cyclicValueQuotients n hn)
      ((QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) (n • z)) = 0
  rw [hq, map_zero]

private theorem classFieldAxiom_unramifiedUnits_hMinusOne
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (hUnramified : E.IsUnramified D)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := Fintype.ofFinite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below)
    Limits.IsZero
      (tateCohomology (v.unitRepresentation E hnormal) (-1)) := by
  let K := E.base.field
  let L := E.field.field
  let hLK := E.below
  let := hnormal
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  let : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let U := v.unitRepresentation E hnormal
  let M := extensionFixedRepresentation A K L hLK hnormal
  let S := Rep.FiniteCyclicGroup.subCompNormHom U g
  let Kcf : FiniteAbstractField G := E.base
  let Ecf : FiniteCyclicSubextension Kcf :=
    { field := L
      below := hLK
      normal := hnormal
      finite := inferInstance
      generator := g
      generates := hg }
  have hMzero : Limits.IsZero (tateCohomology M (-1)) :=
    by
      simpa [Kcf, Ecf,
        FiniteCyclicSubextension.fixedRepresentation] using
          hcf.tateHMinusOne_isZero Kcf Ecf
  have hExact : S.Exact := by
    rw [S.moduleCat_exact_iff]
    intro u hu
    have huNorm : U.norm.hom u = 0 := by
      simpa [S] using hu
    let uM : M.V :=
      (extensionFixedRepresentationEquiv A K L hLK hnormal).symm u.1
    have huMNorm : M.norm.hom uM = 0 := by
      apply Subtype.ext
      calc
        (M.norm.hom uM).1 =
            ((relativeNorm A K L hLK
              (extensionFixedRepresentationEquiv A K L hLK hnormal uM) :
                ambientFixedAddSubgroup A K) : A.V) :=
          extensionFixedRepresentation_norm_coe A K L hLK hnormal uM
        _ = ((relativeNorm A K L hLK u.1 :
                ambientFixedAddSubgroup A K) : A.V) := by
          rfl
        _ = ((((U.norm.hom u).1 : ambientFixedAddSubgroup A L)) : A.V) :=
          (v.unitRepresentation_norm_coe E hnormal u).symm
        _ = 0 := by rw [huNorm]; rfl
    obtain ⟨a, ha⟩ :=
      CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
        M g hg hMzero uM huMNorm
    let aL : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal a
    obtain ⟨b, hb⟩ :=
      v.normalizedValuation_surjective E.base (v.valuationAt E.field aL)
    let bL : ambientFixedAddSubgroup A L :=
      fixedFieldInclusion A K L hLK b
    let eL : ambientFixedAddSubgroup A L := aL - bL
    have heL : v.valuationAt E.field eL = 0 := by
      change v.valuationAt E.field (aL - bL) = 0
      rw [map_sub,
        v.valuationAt_fixedFieldInclusion_of_unramified E hUnramified b,
        hb, sub_self]
    let e : U.V := ⟨eL, (v.mem_unitAddSubgroup_iff E.field eL).2 heL⟩
    refine ⟨e, ?_⟩
    have hactionSub :
        relativeCosetAction A K L hLK eL g =
          relativeCosetAction A K L hLK aL g -
            relativeCosetAction A K L hLK bL g := by
      refine Quotient.inductionOn' g ?_
      intro k
      rw [relativeCosetAction_mk, relativeCosetAction_mk,
        relativeCosetAction_mk]
      exact map_sub (A.ρ k.1) aL.1 bL.1
    have hactionB :
        relativeCosetAction A K L hLK bL g = bL.1 := by
      refine Quotient.inductionOn' g ?_
      intro k
      rw [relativeCosetAction_mk]
      exact b.2 k
    have hUaction :
        (((U.ρ g e).1 : ambientFixedAddSubgroup A L) : A.V) =
          relativeCosetAction A K L hLK eL g := by
      simpa [U] using
        v.unitRepresentation_action_coe E hnormal g e
    have hMaction :
        (M.ρ g a).1 = relativeCosetAction A K L hLK aL g := by
      simpa [M, aL] using
        extensionFixedRepresentation_action_coe A K L hLK hnormal g a
    apply Subtype.ext
    apply Subtype.ext
    calc
      ((((U.ρ g e - e).1 : ambientFixedAddSubgroup A L)) : A.V) =
          relativeCosetAction A K L hLK eL g - eL.1 := by
        change (((U.ρ g e).1 : ambientFixedAddSubgroup A L) : A.V) -
            ((e.1 : ambientFixedAddSubgroup A L) : A.V) = _
        rw [hUaction]
      _ = relativeCosetAction A K L hLK aL g - aL.1 := by
        rw [hactionSub, hactionB]
        change (_ - bL.1) - (aL.1 - bL.1) = _ - aL.1
        abel
      _ = (M.ρ g a - a).1 := by
        change _ = (M.ρ g a).1 - a.1
        rw [hMaction]
        rfl
      _ = uM.1 := congrArg Subtype.val ha
      _ = u.1.1 := rfl
  have hzeroS : Limits.IsZero S.homology :=
    (S.exact_iff_isZero_homology).1 hExact
  exact Limits.IsZero.of_iso hzeroS
    (TateCohomology.isoFiniteCyclicNegOne U g hg)

private theorem classFieldAxiom_unramifiedUnits_hZero
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (hUnramified : E.IsUnramified D)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := Fintype.ofFinite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below)
    Limits.IsZero
      (tateCohomology (v.unitRepresentation E hnormal) 0) := by
  let K := E.base.field
  let L := E.field.field
  let hLK := E.below
  let := hnormal
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  let : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let n := (E.degree : ℕ)
  have hn : 0 < n := E.degree.property
  let M := extensionFixedRepresentation A K L hLK hnormal
  let instM : Module ℤ M.V := M.hV2
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let instTCycles : Module ℤ (LinearMap.ker T.g.hom) :=
    (LinearMap.ker T.g.hom).module
  let C := LinearMap.ker T.g.hom
  let cycleValAdd : C →+ ZMod n :=
    (v.valueModulo n hn).comp <|
      (v.valuationAt E.field).comp <|
        (extensionFixedRepresentationEquiv A K L hLK hnormal).toAddMonoidHom.comp
          C.subtype.toAddMonoidHom
  let cycleVal : C →ₗ[ℤ] ZMod n :=
    { toFun := cycleValAdd
      map_add' := cycleValAdd.map_add
      map_smul' := by
        intro m x
        simp only [RingHom.id_apply]
        convert! cycleValAdd.map_zsmul m x using 1
        exact congrArg cycleValAdd (int_smul_eq_zsmul ..) }
  have hcycleValNorm :
      LinearMap.range T.moduleCatToCycles ≤ LinearMap.ker cycleVal := by
    rintro x ⟨y, rfl⟩
    let yL : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal y
    let normK : ambientFixedAddSubgroup A K :=
      relativeNorm A K L hLK yL
    have hnormM :
        extensionFixedRepresentationEquiv A K L hLK hnormal (M.norm.hom y) =
          fixedFieldInclusion A K L hLK normK := by
      apply Subtype.ext
      exact extensionFixedRepresentation_norm_coe A K L hLK hnormal y
    have htower := v.normalizedValuation_tower E yL
    change (E.residueDegree D : ℕ) •
        ((v.valuationAt E.field yL : v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below yL) :
          v.valueGroup) : ZHat) at htower
    rw [E.residueDegree_eq_degree_of_isUnramified D hUnramified] at htower
    have hvalNorm :
        v.valuationAt E.field
            (extensionFixedRepresentationEquiv A K L hLK hnormal
              (M.norm.hom y)) =
          n • v.valuationAt E.field yL := by
      rw [hnormM,
        v.valuationAt_fixedFieldInclusion_of_unramified E hUnramified normK]
      apply Subtype.ext
      exact htower.symm
    change v.valueModulo n hn
        (v.valuationAt E.field
          (extensionFixedRepresentationEquiv A K L hLK hnormal
            (M.norm.hom y))) = 0
    rw [hvalNorm]
    exact v.valueModulo_nsmul n hn (v.valuationAt E.field yL)
  let H := T.moduleCatLeftHomologyData.H
  let fieldVal : H →ₗ[ℤ] ZMod n :=
    (LinearMap.range T.moduleCatToCycles).liftQ cycleVal hcycleValNorm
  have hfieldValSurjective : Function.Surjective fieldVal := by
    intro z
    obtain ⟨c, hc⟩ := v.valueModulo_surjective n hn z
    obtain ⟨aK, haK⟩ := v.normalizedValuation_surjective E.base c
    let aL : ambientFixedAddSubgroup A L :=
      fixedFieldInclusion A K L hLK aK
    let aM : M.V :=
      (extensionFixedRepresentationEquiv A K L hLK hnormal).symm aL
    have haMfixed : M.ρ g aM = aM := by
      refine Quotient.inductionOn' g ?_
      intro k
      apply Subtype.ext
      change A.ρ k.1 aK.1 = aK.1
      exact aK.2 k
    have haMcycle : T.g aM = 0 := by
      change M.ρ g aM - aM = 0
      exact sub_eq_zero.mpr haMfixed
    let aCycle : C := ⟨aM, haMcycle⟩
    refine ⟨Submodule.mkQ (LinearMap.range T.moduleCatToCycles) aCycle, ?_⟩
    change v.valueModulo n hn (v.valuationAt E.field aL) = z
    rw [v.valuationAt_fixedFieldInclusion_of_unramified E hUnramified aK,
      haK]
    exact hc
  let homologyEquiv : H ≃ T.homology :=
    { toFun := fun x => T.moduleCatLeftHomologyData.homologyIso.inv x
      invFun := fun x => T.moduleCatLeftHomologyData.homologyIso.hom x
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  let eHTate : H ≃ tateCohomology M 0 :=
    homologyEquiv.trans
      (TateCohomology.isoFiniteCyclicZero M g hg).symm.toLinearEquiv.toEquiv
  let Kcf : FiniteAbstractField G := E.base
  let Ecf : FiniteCyclicSubextension Kcf :=
    { field := E.field.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }
  let hEcfTateFinite :
      Finite (tateCohomology (Ecf.fixedRepresentation A) 0) :=
    (hcf Kcf Ecf).finiteTateHZero
  let hMTateFinite : Finite (tateCohomology M 0) := by
    simpa [M, K, L, hLK, Kcf, Ecf,
      FiniteCyclicSubextension.fixedRepresentation] using hEcfTateFinite
  let hHFinite : Finite H :=
    Finite.of_equiv (tateCohomology M 0) eHTate.symm
  have hcardT : Nat.card H = n := by
    calc
      Nat.card H = Nat.card (tateCohomology M 0) :=
        Nat.card_congr eHTate
      _ = n := by
        convert hcf.tateHZero_card Kcf Ecf using 1 <;>
          simp [n, M, K, L, Kcf, Ecf,
            FiniteCyclicSubextension.fixedRepresentation,
            FiniteCyclicSubextension.toFiniteAbstractExtension,
            FiniteAbstractFieldExtension.degree,
            FiniteAbstractFieldExtension.toFiniteAbstractExtension]
  have hfieldValInjective : Function.Injective fieldVal :=
    ((Nat.bijective_iff_surjective_and_card fieldVal).2
      ⟨hfieldValSurjective, hcardT.trans (Nat.card_zmod n).symm⟩).1
  let U := v.unitRepresentation E hnormal
  let S := Rep.FiniteCyclicGroup.normHomCompSub U g
  have hExact : S.Exact := by
    rw [S.moduleCat_exact_iff]
    intro u hu
    have huFixed : U.ρ g u = u := by
      apply sub_eq_zero.mp
      simpa [S, Rep.sub_hom, Rep.applyAsHom_apply] using hu
    let uM : M.V :=
      (extensionFixedRepresentationEquiv A K L hLK hnormal).symm u.1
    have huMFixed : M.ρ g uM = uM := by
      have hUaction :
          (((U.ρ g u).1 : ambientFixedAddSubgroup A L) : A.V) =
            relativeCosetAction A K L hLK u.1 g := by
        simpa [U] using
          v.unitRepresentation_action_coe E hnormal g u
      have hMaction :
          (M.ρ g uM).1 = relativeCosetAction A K L hLK u.1 g := by
        simpa [M, uM] using
          extensionFixedRepresentation_action_coe A K L hLK hnormal g uM
      apply Subtype.ext
      calc
        (M.ρ g uM).1 = relativeCosetAction A K L hLK u.1 g := hMaction
        _ = (((U.ρ g u).1 : ambientFixedAddSubgroup A L) : A.V) :=
          hUaction.symm
        _ = u.1.1 := by rw [huFixed]
        _ = uM.1 := rfl
    have huMcycle : T.g uM = 0 := by
      change M.ρ g uM - uM = 0
      exact sub_eq_zero.mpr huMFixed
    let uCycle : C := ⟨uM, huMcycle⟩
    have huClassVal :
        fieldVal (Submodule.mkQ (LinearMap.range T.moduleCatToCycles) uCycle) = 0 := by
      change v.valueModulo n hn (v.valuationAt E.field u.1) = 0
      rw [(v.mem_unitAddSubgroup_iff E.field u.1).1 u.2, map_zero]
    have huClass :
        Submodule.mkQ (LinearMap.range T.moduleCatToCycles) uCycle = 0 := by
      apply hfieldValInjective
      exact huClassVal.trans (map_zero fieldVal).symm
    have huCycleRange :
        uCycle ∈ LinearMap.range T.moduleCatToCycles := by
      exact (Submodule.Quotient.mk_eq_zero _).1 huClass
    obtain ⟨y, hy⟩ := huCycleRange
    have hyNorm : M.norm.hom y = uM := by
      exact congrArg Subtype.val hy
    let yL : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal y
    let normK : ambientFixedAddSubgroup A K :=
      relativeNorm A K L hLK yL
    have hnormInclusion :
        fixedFieldInclusion A K L hLK normK = u.1 := by
      apply Subtype.ext
      calc
        normK.1 = (M.norm.hom y).1 :=
          (extensionFixedRepresentation_norm_coe A K L hLK hnormal y).symm
        _ = uM.1 := congrArg Subtype.val hyNorm
        _ = u.1.1 := rfl
    have huVal : v.valuationAt E.field u.1 = 0 :=
      (v.mem_unitAddSubgroup_iff E.field u.1).1 u.2
    have htower := v.normalizedValuation_tower E yL
    change (E.residueDegree D : ℕ) •
        ((v.valuationAt E.field yL : v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below yL) :
          v.valueGroup) : ZHat) at htower
    rw [E.residueDegree_eq_degree_of_isUnramified D hUnramified] at htower
    have hyVal : v.valuationAt E.field yL = 0 := by
      apply Subtype.ext
      apply zHatMulNat_injective hn
      calc
        n • ((v.valuationAt E.field yL : v.valueGroup) : ZHat) =
            ((v.valuationAt E.base normK : v.valueGroup) : ZHat) := htower
        _ = ((v.valuationAt E.field
              (fixedFieldInclusion A K L hLK normK) : v.valueGroup) : ZHat) := by
          rw [v.valuationAt_fixedFieldInclusion_of_unramified E hUnramified normK]
        _ = ((v.valuationAt E.field u.1 : v.valueGroup) : ZHat) := by
          rw [hnormInclusion]
        _ = 0 := congrArg Subtype.val huVal
        _ = n • (0 : ZHat) := (nsmul_zero n).symm
    let yU : U.V :=
      ⟨yL, (v.mem_unitAddSubgroup_iff E.field yL).2 hyVal⟩
    refine ⟨yU, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    calc
      ((((U.norm.hom yU).1 : ambientFixedAddSubgroup A L)) : A.V) =
          normK.1 := v.unitRepresentation_norm_coe E hnormal yU
      _ = (M.norm.hom y).1 :=
        (extensionFixedRepresentation_norm_coe A K L hLK hnormal y).symm
      _ = uM.1 := congrArg Subtype.val hyNorm
      _ = u.1.1 := rfl
  have hzeroS : Limits.IsZero S.homology :=
    (S.exact_iff_isZero_homology).1 hExact
  exact Limits.IsZero.of_iso hzeroS
    (TateCohomology.isoFiniteCyclicZero U g hg)

/-- **the unramified cohomology consequence.**  The class field axiom implies the
unit-cohomology axiom: for every
finite unramified Galois extension `L / K`, both
`H⁰(G(L/K), U_L)` and `H⁻¹(G(L/K), U_L)` vanish. -/
theorem classFieldAxiom_implies_unramifiedUnitCohomology
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A) :
    SatisfiesUnramifiedUnitCohomology D v := by
  intro K E
  constructor
  · simpa [FiniteUnramifiedCyclicExtension.unitRepresentation] using
      v.classFieldAxiom_unramifiedUnits_hZero hcf
        E.toFiniteAbstractFieldExtension E.normal
        E.toFiniteAbstractFieldExtension_isUnramified E.generator E.generates
  · simpa [FiniteUnramifiedCyclicExtension.unitRepresentation] using
      v.classFieldAxiom_unramifiedUnits_hMinusOne hcf
        E.toFiniteAbstractFieldExtension E.normal
        E.toFiniteAbstractFieldExtension_isUnramified E.generator E.generates

end ValuationData

/-!
# Abstract reciprocity, the abstract reciprocity theorem: the two exact rows

The proof of the abstract reciprocity theorem starts with a finite Galois tower
`L | M | K`.  This file constructs the two rows of that diagram on the
actual finite Galois groups and finite norm quotients:

`1 → G(L/M) → G(L/K) → G(M/K) → 1`,

`A_M / N_{L/M} A_L → A_K / N_{L/K} A_L
    → A_K / N_{M/K} A_M → 0`.

It also records the canonical factorization of an additive reciprocity map
through the abelianization.  No exactness or bijectivity statement is taken
as an input; both rows are proved directly from quotient membership and norm
transitivity.
-/

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The restriction `G(L/K) → G(M/K)` in the upper row. -/
def abstractReciprocityRestriction
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal] :
    (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK)) →*
      (K.toSubgroup ⧸ extensionSubgroup K M hMK) := by
  apply QuotientGroup.map
    (extensionSubgroup K L (hLM.trans hMK))
    (extensionSubgroup K M hMK)
    (MonoidHom.id K.toSubgroup)
  intro k hk
  exact hLM hk

/--
Establishes the identity `abstractReciprocityRestriction K M L hLM hMK (QuotientGroup.mk k) =
QuotientGroup.mk k`.
-/
@[simp]
theorem abstractReciprocityRestriction_mk
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    (k : K.toSubgroup) :
    abstractReciprocityRestriction K M L hLM hMK (QuotientGroup.mk k) =
      QuotientGroup.mk k :=
  rfl

/-- Restriction to the intermediate Galois extension is surjective. -/
theorem abstractReciprocityRestriction_surjective
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal] :
    Function.Surjective (abstractReciprocityRestriction K M L hLM hMK) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  exact ⟨QuotientGroup.mk k, rfl⟩

/-- With equal base fields, norm--conjugation naturality's Galois-side restriction is
the restriction in the reciprocity reduction exact row's exact row. -/
theorem finiteReciprocityNaturalityRestriction_sameBase_eq_restriction
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal] :
    finiteReciprocityNaturalityRestriction K K M L hMK (hLM.trans hMK) le_rfl hLM =
      abstractReciprocityRestriction K M L hLM hMK := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  rfl

/-- Finiteness of `L | K` implies finiteness of the quotient `G(M/K)`.
This is derived from the actual surjective restriction map. -/
theorem abstractReciprocity_intermediateQuotient_finite
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
  Finite.of_surjective (abstractReciprocityRestriction K M L hLM hMK)
    (abstractReciprocityRestriction_surjective K M L hLM hMK)

/-- The inclusion `G(L/M) → G(L/K)` in the upper row.
Normality of `L | M` is derived from normality of `L | K`. -/
def abstractReciprocityInclusion
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal] :
    letI : (extensionSubgroup M L hLM).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hLM hMK
    (M.toSubgroup ⧸ extensionSubgroup M L hLM) →*
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK)) := by
  letI : (extensionSubgroup M L hLM).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hLM hMK
  exact transferNormNaturalityIntermediateInclusion K M L hLM hMK

/--
On quotient representatives, the abstract reciprocity inclusion is induced by inclusion of the
intermediate subgroup.
-/
@[simp]
theorem abstractReciprocityInclusion_mk
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    (m : M.toSubgroup) :
    letI : (extensionSubgroup M L hLM).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hLM hMK
    abstractReciprocityInclusion K M L hLM hMK (QuotientGroup.mk m) =
      QuotientGroup.mk (Subgroup.inclusion hMK m) := by
  let : (extensionSubgroup M L hLM).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hLM hMK
  rfl

/-- The upper row is exact at `G(L/K)`: the image of `G(L/M)` is exactly
the kernel of restriction to `G(M/K)`. -/
theorem abstractReciprocity_galois_exact
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal] :
    letI : (extensionSubgroup M L hLM).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hLM hMK
    (abstractReciprocityRestriction K M L hLM hMK).ker =
      (abstractReciprocityInclusion K M L hLM hMK).range := by
  let : (extensionSubgroup M L hLM).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hLM hMK
  ext q
  refine QuotientGroup.induction_on q ?_
  intro k
  constructor
  · intro hk
    change abstractReciprocityRestriction K M L hLM hMK
      (QuotientGroup.mk k) = 1 at hk
    have hkM : k ∈ extensionSubgroup K M hMK :=
      (QuotientGroup.eq_one_iff k).1 hk
    let m : M.toSubgroup := ⟨k.1, hkM⟩
    refine ⟨QuotientGroup.mk m, ?_⟩
    exact congrArg
      (fun t : K.toSubgroup =>
        (QuotientGroup.mk t :
          K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK)))
      (Subtype.ext rfl)
  · rintro ⟨q, hq⟩
    rw [← hq]
    refine QuotientGroup.induction_on q ?_
    intro m
    change (QuotientGroup.mk (Subgroup.inclusion hMK m) :
      K.toSubgroup ⧸ extensionSubgroup K M hMK) = 1
    exact (QuotientGroup.eq_one_iff _).2 m.2

/-- Finiteness of `L | K` also implies finiteness of `L | M`. -/
theorem abstractReciprocity_lowerExtension_finite
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) := by
  let inclusion :
      (M.toSubgroup ⧸ extensionSubgroup M L hLM) →
        (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK)) :=
    Quotient.map' (Subgroup.inclusion hMK) (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      apply (mem_extensionSubgroup_iff K L (hLM.trans hMK) _).2
      simpa using (mem_extensionSubgroup_iff M L hLM _).1 hxy)
  apply Finite.of_injective inclusion
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro m
  refine QuotientGroup.induction_on y ?_
  intro n h
  apply QuotientGroup.eq.mpr
  apply (mem_extensionSubgroup_iff M L hLM (m⁻¹ * n)).2
  have h' :
      (QuotientGroup.mk (Subgroup.inclusion hMK m) :
          K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK)) =
        QuotientGroup.mk (Subgroup.inclusion hMK n) := by
    simpa [inclusion] using h
  have hmem := QuotientGroup.eq.mp h'
  have hG := (mem_extensionSubgroup_iff K L (hLM.trans hMK)
    ((Subgroup.inclusion hMK m)⁻¹ * Subgroup.inclusion hMK n)).1 hmem
  simpa using hG

/-- Norm transitivity identifies the norm image from `L` with a subgroup
of the norm image from `M`. -/
theorem abstractReciprocity_finiteNormSubgroup_le
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hKMfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M hMK)]
    [hMLfinite : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L hLM)]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    finiteNormSubgroup A K L (hLM.trans hMK) ≤
      finiteNormSubgroup A K M hMK := by
  let T : DegreeData.FiniteTower G :=
    { top := L
      middle := M
      base := K
      top_le_middle := hLM
      middle_le_base := hMK
      finiteTopQuotient := hMLfinite
      finiteBaseQuotient := hKMfinite }
  rintro _ ⟨a, rfl⟩
  refine ⟨relativeNorm A M L hLM a, ?_⟩
  exact T.norm_trans_apply A a

/-- The first arrow in the lower row, induced by `N_{M/K}`. -/
def abstractReciprocityNormMap
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    FiniteNormQuotient A M L hLM →+
      FiniteNormQuotient A K L (hLM.trans hMK) := by
  letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  exact finiteReciprocityNaturalityNormMap A K M L L (hLM.trans hMK) hLM hMK le_rfl

/--
The abstract reciprocity norm map sends a finite norm class to the class of the corresponding
relative norm.
-/
@[simp]
theorem abstractReciprocityNormMap_finiteNormClass
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))]
    (a : ambientFixedAddSubgroup A M) :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    abstractReciprocityNormMap A K M L hLM hMK
        (finiteNormClass A M L hLM a) =
      finiteNormClass A K L (hLM.trans hMK)
        (relativeNorm A K M hMK a) := by
  let : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  exact finiteReciprocityNaturalityNormMap_finiteNormClass A K M L L
    (hLM.trans hMK) hLM hMK le_rfl a

/-- The quotient projection
`A_K/N_{L/K}A_L → A_K/N_{M/K}A_M` in the lower row. -/
def abstractReciprocityNormProjection
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    FiniteNormQuotient A K L (hLM.trans hMK) →+
      FiniteNormQuotient A K M hMK := by
  letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  apply finiteNormQuotientLift A K L (hLM.trans hMK)
    (finiteNormClassHom A K M hMK)
  intro a ha
  exact (finiteNormClass_eq_zero_iff A K M hMK a).2
    (abstractReciprocity_finiteNormSubgroup_le A K M L hLM hMK ha)

/--
The abstract reciprocity norm projection preserves the representative while passing to the
intermediate norm quotient.
-/
@[simp]
theorem abstractReciprocityNormProjection_finiteNormClass
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))]
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    abstractReciprocityNormProjection A K M L hLM hMK
        (finiteNormClass A K L (hLM.trans hMK) a) =
      finiteNormClass A K M hMK a := by
  let : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  simp [abstractReciprocityNormProjection]
  rfl

/-- When the two base fields in norm--conjugation naturality coincide, its norm map is
the ordinary projection between the two actual finite norm quotients. -/
theorem finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K K le_rfl) :=
      (FiniteGaloisSubextension.refl K).finite
    finiteReciprocityNaturalityNormMap A K K M L hMK (hLM.trans hMK) le_rfl hLM =
      abstractReciprocityNormProjection A K M L hLM hMK := by
  let : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K K le_rfl) :=
    (FiniteGaloisSubextension.refl K).finite
  apply AddMonoidHom.ext
  intro q
  refine FiniteNormQuotient.induction_on A K L (hLM.trans hMK) q ?_
  intro a
  have hmap := finiteReciprocityNaturalityNormMap_finiteNormClass
    A K K M L hMK (hLM.trans hMK) le_rfl hLM a
  have hnorm := congrArg (finiteNormClass A K M hMK) (relativeNorm_self A K a)
  exact hmap.trans (hnorm.trans
    (abstractReciprocityNormProjection_finiteNormClass A K M L hLM hMK a).symm)

/-- The quotient projection in the lower row is surjective. -/
theorem abstractReciprocityNormProjection_surjective
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    Function.Surjective (abstractReciprocityNormProjection A K M L hLM hMK) := by
  let : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  intro q
  refine FiniteNormQuotient.induction_on A K M hMK q ?_
  intro a
  exact ⟨finiteNormClass A K L (hLM.trans hMK) a, by
    rw [abstractReciprocityNormProjection_finiteNormClass]⟩

/-- The lower row is exact at `A_K/N_{L/K}A_L`. -/
theorem abstractReciprocity_normQuotient_exact
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    Function.Exact (abstractReciprocityNormMap A K M L hLM hMK)
      (abstractReciprocityNormProjection A K M L hLM hMK) := by
  let : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  rw [AddMonoidHom.exact_iff]
  ext q
  refine FiniteNormQuotient.induction_on A K L (hLM.trans hMK) q ?_
  intro a
  constructor
  · intro ha
    change abstractReciprocityNormProjection A K M L hLM hMK
        (finiteNormClass A K L (hLM.trans hMK) a) = 0 at ha
    rw [abstractReciprocityNormProjection_finiteNormClass] at ha
    have haM : a ∈ finiteNormSubgroup A K M hMK :=
      (finiteNormClass_eq_zero_iff A K M hMK a).1 ha
    obtain ⟨b, rfl⟩ := haM
    exact ⟨finiteNormClass A M L hLM b, by
      rw [abstractReciprocityNormMap_finiteNormClass]⟩
  · rintro ⟨q, hq⟩
    rw [← hq]
    refine FiniteNormQuotient.induction_on A M L hLM q ?_
    intro b
    change abstractReciprocityNormProjection A K M L hLM hMK
        (abstractReciprocityNormMap A K M L hLM hMK
          (finiteNormClass A M L hLM b)) = 0
    rw [abstractReciprocityNormMap_finiteNormClass,
      abstractReciprocityNormProjection_finiteNormClass]
    exact (finiteNormClass_eq_zero_iff A K M hMK _).2 ⟨b, rfl⟩

/-- An additive homomorphism from a (possibly noncommutative) Galois group
to an additive commutative group factors canonically through its
abelianization.  This is the factor map used in the first reduction once the finite reciprocity
  equivalence supplies the reciprocity homomorphism. -/
def abstractReciprocityAbelianizationFactor
    {Q : Type*} {B : Type*} [Group Q] [AddCommGroup B]
    (f : Additive Q →+ B) : Additive (Abelianization Q) →+ B := by
  let fMul : Q →* Multiplicative B :=
    { toFun := fun q => Multiplicative.ofAdd (f (Additive.ofMul q))
      map_one' := f.map_zero
      map_mul' := f.map_add }
  let fAb : Abelianization Q →* Multiplicative B :=
    Abelianization.lift fMul
  exact
    { toFun := fun q => Multiplicative.toAdd (fAb q.toMul)
      map_zero' := fAb.map_one
      map_add' := fAb.map_mul }

/--
Establishes the identity `abstractReciprocityAbelianizationFactor f (Additive.ofMul
(Abelianization.of q)) = f (Additive.ofMul q)`.
-/
@[simp]
theorem abstractReciprocityAbelianizationFactor_of
    {Q : Type*} {B : Type*} [Group Q] [AddCommGroup B]
    (f : Additive Q →+ B) (q : Q) :
    abstractReciprocityAbelianizationFactor f
        (Additive.ofMul (Abelianization.of q)) =
      f (Additive.ofMul q) := by
  exact Abelianization.lift_apply_of
    ({ toFun := fun q => Multiplicative.ofAdd (f (Additive.ofMul q))
       map_one' := f.map_zero
       map_mul' := f.map_add } : Q →* Multiplicative B) q

/-- Restriction also induces the canonical map on abelianizations. -/
def abstractReciprocityAbelianizedRestriction
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal] :
    Abelianization
        (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK)) →*
      Abelianization (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
  Abelianization.map (abstractReciprocityRestriction K M L hLM hMK)

/-- The identity `N_{M/K} ∘ i = [M:K]` used in the Sylow argument of the
first reduction.  Here `i` is the actual inclusion of finite norm
quotients constructed in transfer--norm naturality. -/
theorem abstractReciprocity_normMap_comp_normQuotientInclusion
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))]
    (q : FiniteNormQuotient A K L (hLM.trans hMK)) :
    letI : (extensionSubgroup M L hLM).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hLM hMK
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    abstractReciprocityNormMap A K M L hLM hMK
        (transferNormNaturalityNormQuotientInclusion A K M L hLM hMK q) =
      ((DegreeData.FiniteAbstractExtension.ofInclusion M K hMK).degree : ℕ) • q := by
  let : (extensionSubgroup M L hLM).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hLM hMK
  let : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  refine FiniteNormQuotient.induction_on A K L (hLM.trans hMK) q ?_
  intro a
  rw [transferNormNaturality_normQuotientInclusion_finiteNormClass,
    abstractReciprocityNormMap_finiteNormClass]
  have hnorm :
      relativeNorm A K M hMK
          (fixedFieldInclusion A K M hMK a) =
          ((DegreeData.FiniteAbstractExtension.ofInclusion M K hMK).degree :
            ℕ) • a := by
    let E := DegreeData.FiniteAbstractExtension.ofInclusion M K hMK
    change relativeNorm A E.base E.field E.below
        (fixedFieldInclusion A E.base E.field E.below a) =
      (E.degree : ℕ) • a
    exact relativeNorm_fixedFieldInclusion A E a
  rw [hnorm, finiteNormClass_nsmul]

/-- In the cyclic case, the class-field axiom upgrades surjectivity of the actual
reciprocity-shaped homomorphism to bijectivity.  The converse is formal;
the forward implication uses the equality of the two actual finite orders,
not an assumed cardinality certificate. -/
theorem abstractReciprocity_cyclic_surjective_iff_bijective
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))]
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (r : Additive (K.toSubgroup ⧸ extensionSubgroup K L hLK) →+
      FiniteNormQuotient A K L hLK) :
    Function.Surjective r ↔ Function.Bijective r := by
  let E : DegreeData.FiniteAbstractExtension G :=
    DegreeData.FiniteAbstractExtension.ofInclusion L K hLK
  let hEbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base)) := by
    simpa [E, DegreeData.FiniteAbstractExtension.ofInclusion] using hKabsolute
  let : Finite (FiniteNormQuotient A K L hLK) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf E hnormal g hg
  constructor
  · intro hr
    apply (Nat.bijective_iff_surjective_and_card r).2
    exact ⟨hr, cyclicReciprocity_card_equality
      A hcf E hnormal g hg⟩
  · exact fun hr => hr.2

/-- In a cyclic tower, the first norm map in the lower exact row is
injective.  This is the order calculation in the third reduction:
the three norm quotients have orders `[L:M]`, `[L:K]`, and `[M:K]`, and
the tower law cancels the last factor. -/
theorem abstractReciprocity_cyclicTower_normMap_injective
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hKabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))]
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))]
    (gKL : K.toSubgroup ⧸
      extensionSubgroup K L (hLM.trans hMK))
    (hgKL : ∀ q, q ∈ Subgroup.zpowers gKL)
    (gML :
      letI : (extensionSubgroup M L hLM).Normal :=
        transferNormNaturality_intermediateExtension_normal K M L hLM hMK
      M.toSubgroup ⧸ extensionSubgroup M L hLM)
    (hgML :
      letI : (extensionSubgroup M L hLM).Normal :=
        transferNormNaturality_intermediateExtension_normal K M L hLM hMK
      ∀ q, q ∈ Subgroup.zpowers gML)
    (gKM : K.toSubgroup ⧸ extensionSubgroup K M hMK)
    (hgKM : ∀ q, q ∈ Subgroup.zpowers gKM) :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    Function.Injective (abstractReciprocityNormMap A K M L hLM hMK) := by
  let hMLnormal : (extensionSubgroup M L hLM).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hLM hMK
  let hMLfinite : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let hKMfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  let hMabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M (le_baseField M)) :=
    relativeTowerQuotientFinite (baseField G) K M hMK (le_baseField K)
  let ELM : DegreeData.FiniteAbstractExtension G :=
    DegreeData.FiniteAbstractExtension.ofInclusion L M hLM
  let EMK : DegreeData.FiniteAbstractExtension G :=
    DegreeData.FiniteAbstractExtension.ofInclusion M K hMK
  let ELK : DegreeData.FiniteAbstractExtension G :=
    DegreeData.FiniteAbstractExtension.ofInclusion L K (hLM.trans hMK)
  let hELMbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) ELM.base (le_baseField ELM.base)) := by
    simpa [ELM, DegreeData.FiniteAbstractExtension.ofInclusion] using hMabsolute
  let hEMKbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) EMK.base (le_baseField EMK.base)) := by
    simpa [EMK, DegreeData.FiniteAbstractExtension.ofInclusion] using hKabsolute
  let hELKbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) ELK.base (le_baseField ELK.base)) := by
    simpa [ELK, DegreeData.FiniteAbstractExtension.ofInclusion] using hKabsolute
  let f := abstractReciprocityNormMap A K M L hLM hMK
  let p := abstractReciprocityNormProjection A K M L hLM hMK
  let : Finite (FiniteNormQuotient A M L hLM) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf ELM hMLnormal gML hgML
  let : Finite (FiniteNormQuotient A K L (hLM.trans hMK)) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf ELK hLnormal gKL hgKL
  let : Finite (FiniteNormQuotient A K M hMK) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf EMK hMnormal gKM hgKM
  have hexact : p.ker = f.range :=
    (AddMonoidHom.exact_iff).1
      (abstractReciprocity_normQuotient_exact A K M L hLM hMK)
  have hpsurjective : Function.Surjective p :=
    abstractReciprocityNormProjection_surjective A K M L hLM hMK
  have hmiddle :
      Nat.card (FiniteNormQuotient A K L (hLM.trans hMK)) =
        Nat.card f.range *
          Nat.card (FiniteNormQuotient A K M hMK) := by
    calc
      Nat.card (FiniteNormQuotient A K L (hLM.trans hMK)) =
          Nat.card p.ker * p.ker.index :=
        (AddSubgroup.card_mul_index p.ker).symm
      _ = Nat.card f.range * Nat.card p.range := by
        rw [AddSubgroup.index_ker, hexact]
      _ = Nat.card f.range *
          Nat.card (FiniteNormQuotient A K M hMK) := by
        have hpRange : p.range = ⊤ :=
          (AddMonoidHom.range_eq_top).2 hpsurjective
        rw [hpRange]
        simp
  have hdegree :
      (ELM.degree : ℕ) * (EMK.degree : ℕ) = (ELK.degree : ℕ) := by
    rw [← ELM.relIndex_eq_degree, ← EMK.relIndex_eq_degree,
      ← ELK.relIndex_eq_degree]
    exact Subgroup.relIndex_mul_relIndex L.toSubgroup M.toSubgroup
      K.toSubgroup hLM hMK
  have hKMpositive : 0 < (EMK.degree : ℕ) := EMK.degree.property
  have hcardML :
      Nat.card (FiniteNormQuotient A M L hLM) =
        (ELM.degree : ℕ) := by
    simpa [ELM, DegreeData.FiniteAbstractExtension.ofInclusion] using
      finiteNormQuotient_card_of_classFieldAxiom
        A hcf ELM hMLnormal gML hgML
  have hcardKL :
      Nat.card (FiniteNormQuotient A K L (hLM.trans hMK)) =
        (ELK.degree : ℕ) := by
    simpa [ELK, DegreeData.FiniteAbstractExtension.ofInclusion] using
      finiteNormQuotient_card_of_classFieldAxiom
        A hcf ELK hLnormal gKL hgKL
  have hcardKM :
      Nat.card (FiniteNormQuotient A K M hMK) =
        (EMK.degree : ℕ) := by
    simpa [EMK, DegreeData.FiniteAbstractExtension.ofInclusion] using
      finiteNormQuotient_card_of_classFieldAxiom
        A hcf EMK hMnormal gKM hgKM
  have hcardRange :
      Nat.card (FiniteNormQuotient A M L hLM) =
        Nat.card f.range := by
    apply Nat.mul_right_cancel hKMpositive
    calc
      Nat.card (FiniteNormQuotient A M L hLM) *
          (EMK.degree : ℕ) =
          (ELM.degree : ℕ) * (EMK.degree : ℕ) := by
        rw [hcardML]
      _ = (ELK.degree : ℕ) := hdegree
      _ = Nat.card (FiniteNormQuotient A K L (hLM.trans hMK)) := by
        rw [hcardKL]
      _ = Nat.card f.range *
          Nat.card (FiniteNormQuotient A K M hMK) := hmiddle
      _ = Nat.card f.range * (EMK.degree : ℕ) := by
        rw [hcardKM]
  have hRangeBijective : Function.Bijective f.rangeRestrict :=
    (Nat.bijective_iff_surjective_and_card f.rangeRestrict).2
      ⟨AddMonoidHom.rangeRestrict_surjective f, hcardRange⟩
  intro x y hxy
  apply hRangeBijective.1
  exact Subtype.ext hxy

/-- An elementary profinite-integer step:
if `n z = k` in `ℤ̂`, with `0 ≤ k < n`, then `k = 0`. -/
theorem abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero
    (n k : ℕ) (hn : 0 < n) (hk : k < n) (z : ZHat)
    (h : n • z =
      Int.castRingHom ZHat (k : ℤ)) :
    k = 0 := by
  have hkmod : (k : ZMod n) = 0 := by
    have hkmodInt : ((k : ℤ) : ZMod n) = 0 := by
      calc
        ((k : ℤ) : ZMod n) = zHatReduction n hn
          (Int.castRingHom ZHat (k : ℤ)) :=
              (zHatReduction_int n hn (k : ℤ)).symm
        _ =
          zHatReduction n hn (n • z) := congrArg (zHatReduction n hn) h.symm
        _ = n • zHatReduction n hn z := map_nsmul (zHatReduction n hn) n z
        _ = 0 := by simp
    simpa using hkmodInt
  exact Nat.eq_zero_of_dvd_of_lt
    ((ZMod.natCast_eq_zero_iff k n).1 hkmod) hk

/-- In a finite totally ramified extension, the normalized valuation of an
element from the lower field is multiplied by the extension degree after
inclusion into the upper field.  This is the valuation identity used for
`M/M⁰`. -/
theorem abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified
    {D : DegreeData G} {A : Rep ℤ G} (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (x : ambientFixedAddSubgroup A E.base.field) :
    ((v.valuationAt E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below x) :
      v.valueGroup) : ZHat) =
      (E.degree : ℕ) •
        ((v.valuationAt E.base x : v.valueGroup) : ZHat) := by
  let EF := E.toFiniteAbstractExtension
  let hEFfinite : Finite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
    EF.finiteQuotient
  have htower := v.normalizedValuation_tower E
    (fixedFieldInclusion A E.base.field E.field.field E.below x)
  have hresidue : (E.residueDegree D : ℕ) = 1 :=
    EF.residueDegree_eq_one_of_isTotallyRamified D hTot
  change (E.residueDegree D : ℕ) •
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
          v.valueGroup) : ZHat) =
    ((v.valuationAt E.base
      (relativeNorm A E.base.field E.field.field E.below
        (fixedFieldInclusion A E.base.field E.field.field E.below x)) :
          v.valueGroup) : ZHat) at htower
  rw [hresidue, one_nsmul] at htower
  have hbelow : E.below = EF.below := Subsingleton.elim _ _
  rw [hbelow] at htower
  change
    ((v.valuationAt E.field
      (fixedFieldInclusion A EF.base EF.field EF.below x) :
        v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A EF.base EF.field EF.below
          (fixedFieldInclusion A EF.base EF.field EF.below x)) :
            v.valueGroup) : ZHat) at htower
  rw [relativeNorm_fixedFieldInclusion A EF x] at htower
  have hfixedFieldInclusion :
      fixedFieldInclusion A EF.base EF.field EF.below x =
        fixedFieldInclusion A E.base.field E.field.field E.below x := by
    apply Subtype.ext
    rfl
  rw [hfixedFieldInclusion] at htower
  have htower' :
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
          v.valueGroup) : ZHat) =
        ((v.valuationAt E.base ((E.degree : ℕ) • x) :
          v.valueGroup) : ZHat) := by
    simpa [EF, FiniteAbstractFieldExtension.degree] using htower
  calc
    ((v.valuationAt E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below x) :
        v.valueGroup) : ZHat) =
        ((v.valuationAt E.base ((E.degree : ℕ) • x) :
          v.valueGroup) : ZHat) := htower'
    _ = (E.degree : ℕ) •
        ((v.valuationAt E.base x : v.valueGroup) : ZHat) :=
      congrArg Subtype.val
        (map_nsmul (v.valuationAt E.base) (E.degree : ℕ) x)

/-- The exact `k = 0` valuation endpoint of the totally ramified argument.  Here `K = M⁰`, `L =
M`, and `x` is the element constructed in
the fixed subgroup. -/
theorem abstractReciprocity_totallyRamified_valuation_forces_exponent_zero
    {D : DegreeData G} {A : Rep ℤ G} (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (k : ℕ) (hk : k < (E.degree : ℕ))
    (x : ambientFixedAddSubgroup A E.base.field)
    (hx :
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
        v.valueGroup) : ZHat) =
        Int.castRingHom ZHat (k : ℤ)) :
    k = 0 := by
  have hn : 0 < (E.degree : ℕ) := E.degree.property
  apply abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero
    (E.degree : ℕ) k hn hk
    (((v.valuationAt E.base x : v.valueGroup) : ZHat))
  rw [← abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified
    v E hTot]
  exact hx

end
end
end ClassFormation
