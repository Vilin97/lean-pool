/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Sylow
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FrobeniusLift
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionCosets
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FrobeniusNorms
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FixedSource
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.Conclusion
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse

/-! # Main -/

@[expose] public section
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity theorem

This file assembles the three reductions.  The terminal
cyclic totally ramified calculation is proved in
`AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase`.
-/

noncomputable
section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Additive exactness of the finite Galois row attached to an intermediate
Galois field. -/
private theorem abstractReciprocity_galois_functionExact
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal] :
    letI : (extensionSubgroup M L hLM).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hLM hMK
    Function.Exact
      (MonoidHom.toAdditive (abstractReciprocityInclusion K M L hLM hMK))
      (MonoidHom.toAdditive (abstractReciprocityRestriction K M L hLM hMK)) := by
  let : (extensionSubgroup M L hLM).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hLM hMK
  intro q
  constructor
  · intro hq
    have hmul : abstractReciprocityRestriction K M L hLM hMK q.toMul = 1 := by
      exact Additive.ofMul.injective (by simpa using hq)
    have hmem : q.toMul ∈
        (abstractReciprocityRestriction K M L hLM hMK).ker := hmul
    rw [abstractReciprocity_galois_exact K M L hLM hMK] at hmem
    obtain ⟨x, hx⟩ := hmem
    refine ⟨Additive.ofMul x, ?_⟩
    exact Additive.toMul.injective hx
  · rintro ⟨x, rfl⟩
    have hmem : abstractReciprocityInclusion K M L hLM hMK x.toMul ∈
        (abstractReciprocityInclusion K M L hLM hMK).range :=
      ⟨x.toMul, rfl⟩
    rw [← abstractReciprocity_galois_exact K M L hLM hMK] at hmem
    exact Additive.ofMul.injective (by simpa using hmem)

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
private theorem abstractReciprocity_subgroup_card_lt_of_ne_top
    {Q : Type*} [Group Q] [Finite Q] (S : Subgroup Q) (hS : S ≠ ⊤) :
    Nat.card S < Nat.card Q := by
  by_contra hlt
  have hsurj : Function.Surjective S.subtype :=
    (S.subtype_injective.bijective_of_nat_card_le (Nat.le_of_not_gt hlt)).2
  apply hS
  rw [eq_top_iff]
  intro q _
  obtain ⟨s, hs⟩ := hsurj q
  rw [← hs]
  exact s.property

/-- Quotienting a finite group by a nontrivial normal subgroup strictly
decreases its cardinality. -/
private theorem abstractReciprocity_quotient_card_lt_of_ne_bot
    {Q : Type*} [Group Q] [Finite Q] (S : Subgroup Q) [S.Normal]
    (hS : S ≠ ⊥) :
    Nat.card (Q ⧸ S) < Nat.card Q := by
  by_contra hlt
  have hinj : Function.Injective (QuotientGroup.mk' S) :=
    ((QuotientGroup.mk'_surjective S).bijective_of_nat_card_le
      (Nat.le_of_not_gt hlt)).1
  apply hS
  rw [← QuotientGroup.ker_mk' S]
  exact (MonoidHom.ker_eq_bot_iff (QuotientGroup.mk' S)).2 hinj

/-- A subgroup of a finite commutative group which contains every Sylow
subgroup is the whole group. -/
private theorem abstractReciprocity_subgroup_eq_top_of_sylow_le
    {B : Type*} [CommGroup B] [Finite B]
    (H : Subgroup B)
    (hSylow : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p B),
      (P : Subgroup B) ≤ H) :
    H = ⊤ := by
  classical
  apply (Subgroup.index_eq_one (H := H)).1
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpdvd
  let : Fact p.Prime := ⟨hp⟩
  let quotientMap : B →* B ⧸ H := QuotientGroup.mk' H
  have hquotientMap : Function.Surjective quotientMap :=
    QuotientGroup.mk'_surjective H
  let Q : Sylow p (B ⧸ H) := default
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective
    hquotientMap p Q
  have hmapBot : (P : Subgroup B).map quotientMap = ⊥ := by
    exact (Subgroup.map_eq_bot_iff (P : Subgroup B)).2 (by
      simpa [quotientMap, QuotientGroup.ker_mk'] using hSylow P)
  have hQBot : (Q : Subgroup (B ⧸ H)) = ⊥ := by
    have hco := congrArg (fun S : Sylow p (B ⧸ H) =>
      (S : Subgroup (B ⧸ H))) hP
    simpa [hmapBot] using hco.symm
  exact (Q.ne_bot_of_dvd_card hpdvd) hQBot

/-- If a commutative group has finite exponent and an additive subgroup
contains every Sylow subgroup, then it is the whole group.  Only the finite
cyclic subgroup generated by the element under consideration is made
finite; no finiteness of the ambient group is assumed. -/
private theorem abstractReciprocity_addSubgroup_eq_top_of_exponent_and_sylow_le
    {B : Type*} [AddCommGroup B]
    (d : ℕ) (hd : 0 < d) (hexponent : ∀ b : B, d • b = 0)
    (H : AddSubgroup B)
    (hSylow : ∀ {p : ℕ} [Fact p.Prime]
      (P : Sylow p (Multiplicative B)),
      Subgroup.toAddSubgroup'
        (P : Subgroup (Multiplicative B)) ≤ H) :
    H = ⊤ := by
  apply AddSubgroup.toSubgroup.injective
  apply top_unique
  intro g _
  let b : B := g.toAdd
  have hgfinite : IsOfFinOrder g :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd, by
      apply Multiplicative.toAdd.injective
      simpa [b] using hexponent b⟩
  let C := Subgroup.zpowers g
  let : Fintype C :=
    Fintype.ofEquiv (Fin (orderOf g)) (finEquivZPowers hgfinite)
  let J : Subgroup C := H.toSubgroup.comap C.subtype
  have hJ : J = ⊤ := by
    apply abstractReciprocity_subgroup_eq_top_of_sylow_le J
    intro p _ Q x hx
    have hQp : IsPGroup p ((Q : Subgroup C).map C.subtype) :=
      Q.isPGroup'.map C.subtype
    obtain ⟨P, hQP⟩ := hQp.exists_le_sylow
    have hxmap : (x : Multiplicative B) ∈
        (Q : Subgroup C).map C.subtype :=
      ⟨x, hx, rfl⟩
    exact hSylow P (hQP hxmap)
  let x : C := ⟨g, Subgroup.mem_zpowers g⟩
  have hxJ : x ∈ J := by rw [hJ]; exact Subgroup.mem_top x
  exact hxJ

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The common reciprocity square used by the cyclic and intermediate-field
reductions in the abstract reciprocity theorem. -/
private theorem abstractReciprocity_finiteReciprocityHom_diagram
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K M : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.field.toSubgroup)
    (hMK : M.field.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L (hLM.trans hMK)).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L (hLM.trans hMK))]
    [hMnormal : (extensionSubgroup K.field M.field hMK).Normal]
    [hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field hMK)]
    [hLMnormal : (extensionSubgroup M.field L hLM).Normal]
    [hLMfinite : Finite
      (M.field.toSubgroup ⧸ extensionSubgroup M.field L hLM)] :
    let r₀ := D.finiteReciprocityHom A v hAxiom M L hLM
    let r := D.finiteReciprocityHom A v hAxiom K L (hLM.trans hMK)
    let r₁ := D.finiteReciprocityHom A v hAxiom K M.field hMK
    let i := MonoidHom.toAdditive
      (abstractReciprocityInclusion K.field M.field L hLM hMK)
    let q := MonoidHom.toAdditive
      (abstractReciprocityRestriction K.field M.field L hLM hMK)
    let n := abstractReciprocityNormMap A K.field M.field L hLM hMK
    let p := abstractReciprocityNormProjection A K.field M.field L hLM hMK
    Function.Surjective q ∧
      (∀ x, r (i x) = n (r₀ x)) ∧
      (∀ x, p (r x) = r₁ (q x)) := by
  dsimp only
  let EMK : FiniteAbstractFieldExtension G :=
    { field := M
      base := K
      below := hMK
      finiteQuotient := hMfinite }
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  let r₀ := D.finiteReciprocityHom A v hAxiom M L hLM
  let r := D.finiteReciprocityHom A v hAxiom K L (hLM.trans hMK)
  let r₁ := D.finiteReciprocityHom A v hAxiom K M.field hMK
  let i := MonoidHom.toAdditive
    (abstractReciprocityInclusion K.field M.field L hLM hMK)
  let q := MonoidHom.toAdditive
    (abstractReciprocityRestriction K.field M.field L hLM hMK)
  let n := abstractReciprocityNormMap A K.field M.field L hLM hMK
  let p := abstractReciprocityNormProjection A K.field M.field L hLM hMK
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := abstractReciprocityRestriction_surjective
      K.field M.field L hLM hMK y.toMul
    refine ⟨Additive.ofMul x, ?_⟩
    exact Additive.toMul.injective hx
  have hleft : ∀ x, r (i x) = n (r₀ x) := by
    intro x
    have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EMK L L (hLM.trans hMK) hLM le_rfl
    simpa only [r, r₀, n, i, abstractReciprocityNormMap,
      abstractReciprocityInclusion, transferNormNaturalityIntermediateInclusion,
      AddMonoidHom.comp_apply] using
        (congrArg (fun f => f x) hcomm).symm
  have hright : ∀ x, p (r x) = r₁ (q x) := by
    intro x
    have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK M.field L hMK (hLM.trans hMK) hLM
    rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection,
      finiteReciprocityNaturalityRestriction_sameBase_eq_restriction] at hcomm
    simpa only [r, r₁, p, q, AddMonoidHom.comp_apply] using
      congrArg (fun f => f x) hcomm
  exact ⟨hq, hleft, hright⟩

/-- The third reduction: the reciprocity homomorphism is
bijective for every cyclic finite Galois extension, by splitting it into
its maximal unramified and totally ramified parts. -/
theorem abstractReciprocity_cyclic_finiteReciprocityHom_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    [hCyclic : IsCyclic L.extensionQuotient] :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let S := L.inertiaImage D
  let M := L.maximalUnramifiedSubextension D
  let hLM : L.field.toSubgroup ≤ M.toSubgroup :=
    L.field_le_intermediateField S
  let hMK : M.toSubgroup ≤ K.field.toSubgroup :=
    L.intermediateField_le_base S
  let hLnormal :
      (extensionSubgroup K.field L.field (hLM.trans hMK)).Normal := by
    simpa only using L.normal
  let hLfinite : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field (hLM.trans hMK)) := by
    simpa only using L.finite
  let hMnormal : (extensionSubgroup K.field M hMK).Normal :=
    L.intermediateField_normal S inferInstance
  let hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK) :=
    L.intermediateField_finite S
  let hLMnormal : (extensionSubgroup M L.field hLM).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  let hLMfinite : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.extension_over_intermediate_finite S
  let hMabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M (le_baseField M)) :=
    FiniteGaloisSubextension.finite_extension_trans hMK (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
  let hLowerCyclic : IsCyclic
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.lowerQuotient_isCyclic S
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
    (α := M.toSubgroup ⧸ extensionSubgroup M L.field hLM)
  let Ecyc : FiniteCyclicSubextension MF :=
    { field := L.field
      below := hLM
      normal := hLMnormal
      finite := hLMfinite
      generator := g
      generates := hg }
  let r₀ := D.finiteReciprocityHom A v hAxiom MF L.field hLM
  let r := D.finiteReciprocityHom A v hAxiom K L.field (hLM.trans hMK)
  let r₁ := D.finiteReciprocityHom A v hAxiom K M hMK
  have hr₀ : Function.Bijective r₀ :=
    v.abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_bijective
      hcf hAxiom MF Ecyc
        (L.maximalUnramifiedSubextension_isTotallyRamified D)
  have hr₁ : Function.Bijective r₁ :=
    (v.unramifiedReciprocityEquiv hAxiom K M hMK
      (L.maximalUnramifiedSubextension_isUnramified D)).bijective
  obtain ⟨hpQ, hleft, hright⟩ :=
    abstractReciprocity_finiteReciprocityHom_diagram
      v hAxiom K MF L.field hLM hMK
  exact abstractReciprocity_bijective_of_exact_diagram
    (MonoidHom.toAdditive
      (abstractReciprocityInclusion K.field M L.field hLM hMK))
    (MonoidHom.toAdditive
      (abstractReciprocityRestriction K.field M L.field hLM hMK))
    (abstractReciprocityNormMap A K.field M L.field hLM hMK)
    (abstractReciprocityNormProjection A K.field M L.field hLM hMK)
    r₀ r r₁
    (abstractReciprocity_galois_functionExact K.field M L.field hLM hMK)
    (abstractReciprocity_normQuotient_exact A K.field M L.field hLM hMK)
    hpQ (L.maximalUnramified_normMap_injective A hcf D)
    hleft hright hr₀ hr₁

/-- Surjectivity ascends through a normal intermediate field.  This is the
diagram chase used in the degree induction of the first reduction. -/
private theorem abstractReciprocity_finiteReciprocityHom_surjective_of_intermediate
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (S : Subgroup L.extensionQuotient) [hSnormal : S.Normal] :
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    let hMK := L.intermediateField_le_base S
    letI : (extensionSubgroup K.field M hMK).Normal :=
      L.intermediateField_normal S hSnormal
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK) :=
      L.intermediateField_finite S
    letI : (extensionSubgroup M L.field hLM).Normal :=
      L.extensionSubgroup_over_intermediate_normal S
    letI : Finite
        (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
      L.extension_over_intermediate_finite S
    letI : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) M (le_baseField M)) :=
      FiniteGaloisSubextension.finite_extension_trans hMK (le_baseField K.field)
    let MF : FiniteAbstractField G := ⟨M, inferInstance⟩
    Function.Surjective
        (D.finiteReciprocityHom A v hAxiom MF L.field hLM) →
      Function.Surjective
        (D.finiteReciprocityHom A v hAxiom K M hMK) →
      letI : Finite
          (K.field.toSubgroup ⧸
            extensionSubgroup K.field L.field L.below) := L.finite
      Function.Surjective
        (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  dsimp only
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  let hLnormal :
      (extensionSubgroup K.field L.field (hLM.trans hMK)).Normal := by
    simpa only using L.normal
  let hLfinite : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field (hLM.trans hMK)) := by
    simpa only using L.finite
  let hMnormal : (extensionSubgroup K.field M hMK).Normal :=
    L.intermediateField_normal S hSnormal
  let hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK) :=
    L.intermediateField_finite S
  let hLMnormal : (extensionSubgroup M L.field hLM).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  let hLMfinite : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.extension_over_intermediate_finite S
  let hMabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M (le_baseField M)) :=
    FiniteGaloisSubextension.finite_extension_trans hMK (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
  intro hr₀ hr₁
  let r₀ := D.finiteReciprocityHom A v hAxiom MF L.field hLM
  let r := D.finiteReciprocityHom A v hAxiom K L.field (hLM.trans hMK)
  let r₁ := D.finiteReciprocityHom A v hAxiom K M hMK
  obtain ⟨hpQ, hleft, hright⟩ :=
    abstractReciprocity_finiteReciprocityHom_diagram
      v hAxiom K MF L.field hLM hMK
  exact abstractReciprocity_surjective_of_exact_diagram
    (MonoidHom.toAdditive
      (abstractReciprocityInclusion K.field M L.field hLM hMK))
    (MonoidHom.toAdditive
      (abstractReciprocityRestriction K.field M L.field hLM hMK))
    (abstractReciprocityNormMap A K.field M L.field hLM hMK)
    (abstractReciprocityNormProjection A K.field M L.field hLM hMK)
    r₀ r r₁
    (abstractReciprocity_normQuotient_exact A K.field M L.field hLM hMK)
    hpQ hleft hright hr₀ hr₁

section SolvableReciprocity

local notation "IsSolvable" => Group.IsSolvable

/-- The degree induction in the first reduction for solvable
Galois groups.  In the abelian noncyclic case one cuts out one of the
faithful cyclic coordinates; in the nonabelian case one cuts out the
commutator subgroup. -/
private theorem abstractReciprocity_solvable_finiteReciprocityHom_surjective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    [hsolvable : IsSolvable L.extensionQuotient] :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Function.Surjective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  classical
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let Q := L.extensionQuotient
  by_cases hcyclic : IsCyclic Q
  · let : IsCyclic Q := hcyclic
    exact (v.abstractReciprocity_cyclic_finiteReciprocityHom_bijective
      hcf hAxiom K L).2
  have hQnotSubsingleton : ¬ Subsingleton Q := by
    intro hQ
    let : Subsingleton Q := hQ
    exact hcyclic inferInstance
  let hQnontrivial : Nontrivial Q :=
    not_subsingleton_iff_nontrivial.mp hQnotSubsingleton
  by_cases hcommutative : IsMulCommutative Q
  · let : IsMulCommutative Q := hcommutative
    obtain ⟨I, hIfinite, _, _, f, _, hfaithful, hfactorCyclic,
        _⟩ := L.exists_cyclicIntermediateFields
    let : Fintype I := hIfinite
    obtain ⟨q, hq⟩ := exists_ne (1 : Q)
    have hnotAll : ¬ ∀ i, f i q = 1 := by
      intro hall
      have hmem : q ∈ ⨅ i, MonoidHom.ker (f i) := by
        rw [Subgroup.mem_iInf]
        intro i
        exact (MonoidHom.mem_ker).2 (hall i)
      rw [hfaithful, Subgroup.mem_bot] at hmem
      exact hq hmem
    push Not at hnotAll
    obtain ⟨i, hi⟩ := hnotAll
    let S := MonoidHom.ker (f i)
    let hSnormal : S.Normal := inferInstance
    have hSneTop : S ≠ ⊤ := by
      intro htop
      have hmem : q ∈ S := by rw [htop]; trivial
      exact hi ((MonoidHom.mem_ker).1 hmem)
    let M := L.intermediateField S
    let N := L.lowerFiniteGalois S
    let U := L.intermediateFiniteGalois S hSnormal
    let hMabsolute : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) M (le_baseField M)) :=
      FiniteGaloisSubextension.finite_extension_trans
        (L.intermediateField_le_base S) (le_baseField K.field)
    let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
    let hNsolvable : Group.IsSolvable N.extensionQuotient :=
      Group.isSolvable_of_isSolvable_injective
        (f := (L.lowerQuotientEquiv S).toMonoidHom)
        (L.lowerQuotientEquiv S).injective
    let hUcyclic : IsCyclic U.extensionQuotient := hfactorCyclic i
    let : Finite
        (MF.field.toSubgroup ⧸
          extensionSubgroup MF.field N.field N.below) := N.finite
    let : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field U.field U.below) := U.finite
    have hNcard : Nat.card N.extensionQuotient < Nat.card Q := by
      calc
        Nat.card N.extensionQuotient = Nat.card S :=
          Nat.card_congr (L.lowerQuotientEquiv S).toEquiv
        _ < Nat.card Q :=
          abstractReciprocity_subgroup_card_lt_of_ne_top S hSneTop
    have hrN : Function.Surjective
        (D.finiteReciprocityHom A v hAxiom MF N.field N.below) :=
      abstractReciprocity_solvable_finiteReciprocityHom_surjective
        v hcf hAxiom MF N
    have hrU : Function.Surjective
        (D.finiteReciprocityHom A v hAxiom K U.field U.below) :=
      (v.abstractReciprocity_cyclic_finiteReciprocityHom_bijective
        hcf hAxiom K U).2
    exact abstractReciprocity_finiteReciprocityHom_surjective_of_intermediate
      v hAxiom K L S hrN hrU
  · let S := commutator Q
    let hSnormal : S.Normal := inferInstance
    have hSneBot : S ≠ ⊥ := by
      intro hbot
      apply hcommutative
      have hcenter : Subgroup.center Q = ⊤ :=
        (commutator_eq_bot_iff_center_eq_top Q).1 hbot
      let hcommGroup : CommGroup Q :=
        Group.commGroupOfCenterEqTop hcenter
      exact ⟨⟨fun x y => hcommGroup.mul_comm x y⟩⟩
    have hSlt : S < ⊤ :=
      Group.IsSolvable.commutator_lt_top_of_nontrivial Q
    let M := L.intermediateField S
    let N := L.lowerFiniteGalois S
    let U := L.intermediateFiniteGalois S hSnormal
    let hMfinite : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field M
          (L.intermediateField_le_base S)) :=
      L.intermediateField_finite S
    let hMabsolute : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) M (le_baseField M)) :=
      FiniteGaloisSubextension.finite_extension_trans
        (L.intermediateField_le_base S) (le_baseField K.field)
    let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
    let hNsolvable : Group.IsSolvable N.extensionQuotient :=
      Group.isSolvable_of_isSolvable_injective
        (f := (L.lowerQuotientEquiv S).toMonoidHom)
        (L.lowerQuotientEquiv S).injective
    let hUpperSolvable : Group.IsSolvable (L.upperQuotient S) := by
      change Group.IsSolvable (Q ⧸ S)
      infer_instance
    let hUsolvable : Group.IsSolvable U.extensionQuotient :=
      Group.isSolvable_of_isSolvable_injective
        (f := (L.upperQuotientEquiv S).symm.toMonoidHom)
        (L.upperQuotientEquiv S).symm.injective
    let : Finite
        (MF.field.toSubgroup ⧸
          extensionSubgroup MF.field N.field N.below) := N.finite
    let : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field U.field U.below) := U.finite
    have hNcard : Nat.card N.extensionQuotient < Nat.card Q := by
      calc
        Nat.card N.extensionQuotient = Nat.card S :=
          Nat.card_congr (L.lowerQuotientEquiv S).toEquiv
        _ < Nat.card Q :=
          abstractReciprocity_subgroup_card_lt_of_ne_top S hSlt.ne
    have hUcard : Nat.card U.extensionQuotient < Nat.card Q := by
      calc
        Nat.card U.extensionQuotient = Nat.card (Q ⧸ S) :=
          Nat.card_congr (L.upperQuotientEquiv S).symm.toEquiv
        _ < Nat.card Q :=
          abstractReciprocity_quotient_card_lt_of_ne_bot S hSneBot
    have hrN : Function.Surjective
        (D.finiteReciprocityHom A v hAxiom MF N.field N.below) :=
      abstractReciprocity_solvable_finiteReciprocityHom_surjective
        v hcf hAxiom MF N
    have hrU : Function.Surjective
        (D.finiteReciprocityHom A v hAxiom K U.field U.below) :=
      abstractReciprocity_solvable_finiteReciprocityHom_surjective
        v hcf hAxiom K U
    exact abstractReciprocity_finiteReciprocityHom_surjective_of_intermediate
      v hAxiom K L S hrN hrU
termination_by Nat.card L.extensionQuotient
decreasing_by all_goals assumption

end SolvableReciprocity

/-- The Sylow step in the first reduction.  The norm quotient
need not be known finite here: the unramified cohomology consequence kills every element by the
extension degree, so the Sylow argument is performed inside the finite
cyclic subgroup generated by that element. -/
theorem abstractReciprocity_finiteReciprocityHom_surjective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Function.Surjective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  classical
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let r := D.finiteReciprocityHom A v hAxiom K L.field L.below
  apply (AddMonoidHom.range_eq_top (f := r)).1
  have hdegreePos : 0 < (L.toFiniteAbstractExtension.degree : ℕ) :=
    L.toFiniteAbstractExtension.degree.property
  apply abstractReciprocity_addSubgroup_eq_top_of_exponent_and_sylow_le
    (L.toFiniteAbstractExtension.degree : ℕ) hdegreePos
    (finiteNormQuotient_degree_nsmul_eq_zero
      A L.toFiniteAbstractExtension) r.range
  intro p _ Ptarget x hx
  let Psource : Sylow p L.extensionQuotient := default
  let S : Subgroup L.extensionQuotient :=
    (Psource : Subgroup L.extensionQuotient)
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  let N := L.lowerFiniteGalois S
  let hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK) :=
    L.intermediateField_finite S
  let hLMnormal : (extensionSubgroup M L.field hLM).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  let hLMfinite : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.extension_over_intermediate_finite S
  let hMabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M (le_baseField M)) :=
    FiniteGaloisSubextension.finite_extension_trans hMK (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
  let EMK : FiniteAbstractFieldExtension G :=
    { field := MF
      base := K
      below := hMK
      finiteQuotient := hMfinite }
  let hNsolvable : Group.IsSolvable N.extensionQuotient :=
    L.abstractReciprocity_sylow_lowerQuotient_isSolvable Psource
  let rLower := D.finiteReciprocityHom A v hAxiom MF L.field hLM
  have hrLower : Function.Surjective rLower :=
    abstractReciprocity_solvable_finiteReciprocityHom_surjective
      v hcf hAxiom MF N
  have hxNsmul :=
    L.abstractReciprocity_sylowAddSubgroup_le_intermediateDegree_nsmul_range
      Psource Ptarget hx
  obtain ⟨y, hy⟩ := hxNsmul
  obtain ⟨g, hg⟩ := hrLower
    (L.intermediateNormQuotientInclusion A S y)
  refine ⟨MonoidHom.toAdditive
    (finiteReciprocityNaturalityRestriction K.field M L.field L.field
      L.below hLM hMK le_rfl) g, ?_⟩
  have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
    A v hAxiom EMK L.field L.field
      L.below hLM le_rfl
  have hrecip : r (MonoidHom.toAdditive
        (finiteReciprocityNaturalityRestriction K.field M L.field L.field
          L.below hLM hMK le_rfl) g) =
      L.intermediateNormMap A S (rLower g) := by
    change r (MonoidHom.toAdditive
        (finiteReciprocityNaturalityRestriction K.field M L.field L.field
          L.below hLM hMK le_rfl) g) =
      finiteReciprocityNaturalityNormMap A K.field M L.field L.field
        L.below hLM hMK le_rfl (rLower g)
    simpa only [r, rLower, AddMonoidHom.comp_apply] using
      (congrArg (fun f => f g) hcomm).symm
  exact hrecip.trans ((congrArg (L.intermediateNormMap A S) hg).trans
    ((L.intermediateNormMap_comp_inclusion A S y).trans hy))

/-- The second reduction: for an abelian Galois group, the
cyclic quotient coordinates are jointly faithful, hence the reciprocity
homomorphism is injective. -/
theorem abstractReciprocity_abelian_finiteReciprocityHom_injective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    [hcommutative : IsMulCommutative L.extensionQuotient] :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Function.Injective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  classical
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  obtain ⟨I, hIfinite, _, _, f, _, hfaithful, hfactorCyclic,
      _⟩ := L.exists_cyclicIntermediateFields
  let : Fintype I := hIfinite
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hrestriction (i : I) :
      L.upperRestrictionHom (MonoidHom.ker (f i)) q.toMul = 1 := by
    let S := MonoidHom.ker (f i)
    let hSnormal : S.Normal := inferInstance
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    let hMK := L.intermediateField_le_base S
    let U := L.intermediateFiniteGalois S hSnormal
    let hMnormal : (extensionSubgroup K.field M hMK).Normal :=
      L.intermediateField_normal S hSnormal
    let hMfinite : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK) :=
      L.intermediateField_finite S
    let hUcyclic : IsCyclic U.extensionQuotient := hfactorCyclic i
    let rFactor := D.finiteReciprocityHom A v hAxiom K M hMK
    have hrFactor : Function.Injective rFactor :=
      (v.abstractReciprocity_cyclic_finiteReciprocityHom_bijective
        hcf hAxiom K U).1
    have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK M L.field hMK L.below hLM
    rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection,
      finiteReciprocityNaturalityRestriction_sameBase_eq_restriction] at hcomm
    have hzero : rFactor (MonoidHom.toAdditive
        (abstractReciprocityRestriction K.field M L.field hLM hMK) q) = 0 := by
      calc
        rFactor (MonoidHom.toAdditive
            (abstractReciprocityRestriction K.field M L.field hLM hMK) q) =
            abstractReciprocityNormProjection A K.field M L.field hLM hMK
              (D.finiteReciprocityHom A v hAxiom
                K L.field L.below q) := by
                  simpa only [rFactor, AddMonoidHom.comp_apply] using
                    (congrArg (fun h => h q) hcomm).symm
        _ = 0 := by rw [hq, map_zero]
    have hadd : MonoidHom.toAdditive
        (abstractReciprocityRestriction K.field M L.field hLM hMK) q = 0 := by
      apply hrFactor
      simpa only [map_zero] using hzero
    have hbridge (z : L.extensionQuotient) :
        L.upperRestrictionHom S z =
          abstractReciprocityRestriction K.field M L.field hLM hMK z := by
      refine QuotientGroup.induction_on z ?_
      intro k
      rw [L.upperRestrictionHom_mk,
        abstractReciprocityRestriction_mk]
    have hmul :
        abstractReciprocityRestriction K.field M L.field hLM hMK q.toMul = 1 :=
      congrArg Additive.toMul hadd
    exact (hbridge (show L.extensionQuotient from q.toMul)).trans hmul
  have hqone : q.toMul = 1 :=
    (L.upperRestrictionHom_jointlyFaithful f hfaithful q.toMul).1
      hrestriction
  exact Additive.toMul.injective (by simpa using hqone)

/-- The first reduction: the factor of the finite reciprocity equivalence
through the maximal abelian quotient is bijective. -/
theorem abstractReciprocity_abelianizedReciprocity_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Function.Bijective
      (D.transferNormNaturalityAbelianizedReciprocity
        A v hAxiom K L.field L.below) := by
  classical
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let Q := L.extensionQuotient
  let S := commutator Q
  let hSnormal : S.Normal := inferInstance
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  let U := L.intermediateFiniteGalois S hSnormal
  let hMnormal : (extensionSubgroup K.field M hMK).Normal :=
    L.intermediateField_normal S hSnormal
  let hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK) :=
    L.intermediateField_finite S
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  let upperEquiv := L.upperQuotientEquiv S
  let hUpperCommutative : IsMulCommutative (Q ⧸ S) := by
    dsimp only [S]
    exact
      (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 le_rfl
  let hUcommutative : IsMulCommutative U.extensionQuotient :=
    ⟨⟨fun x y => by
      obtain ⟨x', rfl⟩ := upperEquiv.surjective x
      obtain ⟨y', rfl⟩ := upperEquiv.surjective y
      calc
        upperEquiv x' * upperEquiv y' =
            upperEquiv (x' * y') := (map_mul upperEquiv x' y').symm
        _ = upperEquiv (y' * x') := congrArg upperEquiv
          (Std.Commutative.comm
            (op := fun a b : Q ⧸ S => a * b) x' y')
        _ = upperEquiv y' * upperEquiv x' := map_mul upperEquiv y' x'⟩⟩
  let factor := D.transferNormNaturalityAbelianizedReciprocity
    A v hAxiom K L.field L.below
  let r := D.finiteReciprocityHom A v hAxiom K L.field L.below
  let p := abstractReciprocityNormProjection A K.field M L.field hLM hMK
  let rAb := D.finiteReciprocityHom A v hAxiom K M hMK
  have hrAb : Function.Injective rAb :=
    v.abstractReciprocity_abelian_finiteReciprocityHom_injective
      hcf hAxiom K U
  have hrestrictionEq (q : Q) :
      abstractReciprocityRestriction K.field M L.field hLM hMK q =
        L.abelianRestrictionHom q := by
    refine QuotientGroup.induction_on q ?_
    intro k
    rw [abstractReciprocityRestriction_mk]
    rfl
  have hright (q : Q) :
      p (r (Additive.ofMul q)) =
        rAb (Additive.ofMul (L.abelianRestrictionHom q)) := by
    have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK M L.field hMK L.below hLM
    rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection,
      finiteReciprocityNaturalityRestriction_sameBase_eq_restriction] at hcomm
    have hq := congrArg (fun h => h (Additive.ofMul q)) hcomm
    calc
      p (r (Additive.ofMul q)) =
          rAb (Additive.ofMul
            (abstractReciprocityRestriction K.field M L.field hLM hMK q)) := by
        change
          p (r (Additive.ofMul q)) =
            rAb (Additive.ofMul
              (abstractReciprocityRestriction K.field M L.field hLM hMK q)) at hq
        exact hq
      _ = rAb (Additive.ofMul (L.abelianRestrictionHom q)) := by
        rw [hrestrictionEq]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    change factor (Additive.ofMul z.toMul) = 0 at hz
    change Additive.ofMul z.toMul = 0
    revert hz
    refine QuotientGroup.induction_on z.toMul ?_
    intro q hz
    have hrq : r (Additive.ofMul q) = 0 := by
      calc
        r (Additive.ofMul q) =
            factor (Additive.ofMul (Abelianization.of q)) :=
          (D.transferNormNaturalityAbelianizedReciprocity_of
            A v hAxiom K L.field L.below q).symm
        _ = 0 := by
          change factor (Additive.ofMul (Abelianization.of q)) = 0 at hz
          exact hz
    have hcommutator : q ∈ commutator Q :=
      (abstractReciprocity_abelianReduction_kernel
        L p r rAb hright hrAb q).1 hrq
    have hof : Abelianization.of q = 1 :=
      (QuotientGroup.eq_one_iff q).2 hcommutator
    change Additive.ofMul (Abelianization.of q) = Additive.ofMul 1
    exact congrArg Additive.ofMul hof
  · intro b
    obtain ⟨q, hq⟩ :=
      v.abstractReciprocity_finiteReciprocityHom_surjective
        hcf hAxiom K L b
    refine ⟨Additive.ofMul (Abelianization.of q.toMul), ?_⟩
    calc
      factor (Additive.ofMul (Abelianization.of q.toMul)) =
          r (Additive.ofMul q.toMul) :=
        D.transferNormNaturalityAbelianizedReciprocity_of
          A v hAxiom K L.field L.below q.toMul
      _ = r q := by rw [ofMul_toMul]
      _ = b := hq

end ValuationData

namespace DegreeData

/-- **the abstract reciprocity theorem (reciprocity isomorphism).**  For a finite Galois
extension `L/K`, the reciprocity homomorphism identifies the abelianized
Galois group with the finite norm quotient. -/
noncomputable def abstractReciprocityEquiv
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Additive (Abelianization L.extensionQuotient) ≃+
      FiniteNormQuotient A K.field L.field L.below := by
  letI : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let hAxiom := v.classFieldAxiom_implies_unramifiedUnitCohomology hcf
  exact AddEquiv.ofBijective
    (D.transferNormNaturalityAbelianizedReciprocity
      A v hAxiom K L.field L.below)
    (v.abstractReciprocity_abelianizedReciprocity_bijective
      hcf hAxiom K L)

/-- On a Galois element, the abstract reciprocity theorem is the reciprocity homomorphism of
the finite reciprocity equivalence. -/
@[simp]
theorem abstractReciprocityEquiv_apply_of
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (q : L.extensionQuotient) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    D.abstractReciprocityEquiv A v hcf K L
        (Additive.ofMul (Abelianization.of q)) =
      D.finiteReciprocityHom A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
        K L.field L.below
        (Additive.ofMul q) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  exact D.transferNormNaturalityAbelianizedReciprocity_of
    A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf) K L.field L.below
      q

/-- The norm-residue symbol `(·, L/K)`, defined in this construction as the inverse
of the reciprocity isomorphism in the abstract reciprocity theorem. -/
noncomputable def normResidueSymbol
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    FiniteNormQuotient A K.field L.field L.below ≃+
      Additive (Abelianization L.extensionQuotient) := by
  letI : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  exact (D.abstractReciprocityEquiv A v hcf K L).symm

/-- The norm-residue symbol sends the reciprocity class of a Galois
element back to its class in the abelianization. -/
@[simp]
theorem normResidueSymbol_finiteReciprocityHom
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (q : L.extensionQuotient) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    D.normResidueSymbol A v hcf K L
        (D.finiteReciprocityHom A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
          K L.field L.below
          (Additive.ofMul q)) =
      Additive.ofMul (Abelianization.of q) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  rw [← D.abstractReciprocityEquiv_apply_of A v hcf K L q]
  exact (D.abstractReciprocityEquiv A v hcf K L).symm_apply_apply _

/-- Reciprocity followed by the norm-residue symbol inverse is the
identity on the finite norm quotient. -/
@[simp]
theorem abstractReciprocity_normResidueSymbol
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    ∀ a : FiniteNormQuotient A K.field L.field L.below,
    D.abstractReciprocityEquiv A v hcf K L
        (D.normResidueSymbol A v hcf K L a) = a := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  intro a
  exact (D.abstractReciprocityEquiv A v hcf K L).apply_symm_apply a

end DegreeData

/-!
# Abstract reciprocity, reciprocity naturality: the three naturality diagrams

Reciprocity naturality states three diagrams for the norm residue
symbol.  Before taking the inverse of reciprocity, their vertical arrows are
exactly the maps already constructed in norm--conjugation and transfer--norm naturality:

* restriction on Galois groups together with the relative norm;
* conjugation on both sides;
* transfer together with inclusion of fixed elements.

This file applies abelianization to the Galois arrows and combines each pair
of vertical arrows into one map between the products
`Additive G(L/K)ᵃᵇ × A_K/N_{L/K}A_L`.  The formulas on quotient
representatives are proved from the actual maps.  Finally, the abstract reciprocity theorem and
norm--conjugation and transfer--norm naturality turn those reciprocity squares into the three
printed
commutative diagrams for the inverse norm-residue symbol.
-/

noncomputable
section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- A commutative square of additive isomorphisms remains commutative after
replacing both horizontal isomorphisms by their inverses. -/
private theorem normResidueNaturality_symm_naturality
    {Q B Q' B' : Type*}
    [AddCommGroup Q] [AddCommGroup B]
    [AddCommGroup Q'] [AddCommGroup B']
    (r : Q ≃+ B) (r' : Q' ≃+ B')
    (q : Q →+ Q') (b : B →+ B')
    (h : b.comp r.toAddMonoidHom =
      r'.toAddMonoidHom.comp q) :
    q.comp r.symm.toAddMonoidHom =
      r'.symm.toAddMonoidHom.comp b := by
  apply AddMonoidHom.ext
  intro x
  apply r'.injective
  change r' (q (r.symm x)) = r' (r'.symm (b x))
  rw [r'.apply_symm_apply]
  have hx := DFunLike.congr_fun h (r.symm x)
  change b (r (r.symm x)) = r' (q (r.symm x)) at hx
  rw [r.apply_symm_apply] at hx
  exact hx.symm

/-! ## The norm/restriction diagram -/

/-- Restriction in the first diagram of reciprocity naturality, after applying
abelianization. -/
def normResidueNaturalityAbelianizedRestriction
    {G : Type*} [Group G] [TopologicalSpace G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal] :
    Abelianization
        (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K') →*
      Abelianization (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
  Abelianization.map
    (finiteReciprocityNaturalityRestriction K K' L L' hLK hL'K' hK'K hL'L)

/--
Establishes the identity `normResidueNaturalityAbelianizedRestriction K K' L L' hLK hL'K' hK'K
hL'L (Abelianization.of (QuotientGroup.mk k')) = Abelianization.of (QuotientGroup.mk
(Subgroup.inclusion hK'K k'))`.
-/
@[simp]
theorem normResidueNaturalityAbelianizedRestriction_of_mk
    {G : Type*} [Group G] [TopologicalSpace G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal]
    (k' : K'.toSubgroup) :
    normResidueNaturalityAbelianizedRestriction K K' L L'
        hLK hL'K' hK'K hL'L
        (Abelianization.of (QuotientGroup.mk k')) =
      Abelianization.of
        (QuotientGroup.mk (Subgroup.inclusion hK'K k')) := by
  change
    (Abelianization.lift
      (Abelianization.of.comp
        (finiteReciprocityNaturalityRestriction K K' L L'
          hLK hL'K' hK'K hL'L)))
        (Abelianization.of (QuotientGroup.mk k')) = _
  rw [Abelianization.lift_apply_of]
  rfl

/-- The two vertical arrows of the first diagram, assembled into one actual
additive homomorphism.  Its second component is `N_{K'/K}` on finite norm
quotients from norm--conjugation naturality. -/
def normResidueNaturalityNormRestrictionPairMap
    (A : Rep ℤ G)
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal]
    [hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hL'K'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K K' hK'K)] :
    Additive (Abelianization
        (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')) ×
        FiniteNormQuotient A K' L' hL'K' →+
      Additive (Abelianization
        (K.toSubgroup ⧸ extensionSubgroup K L hLK)) ×
        FiniteNormQuotient A K L hLK :=
  AddMonoidHom.prodMap
    (MonoidHom.toAdditive
      (normResidueNaturalityAbelianizedRestriction K K' L L'
        hLK hL'K' hK'K hL'L))
    (finiteReciprocityNaturalityNormMap A K K' L L'
      hLK hL'K' hK'K hL'L)

/--
On representatives, norm-restriction naturality applies subgroup inclusion to the Galois class and
relative norm to the field element.
-/
@[simp]
theorem normResidueNaturalityNormRestrictionPairMap_on_representatives
    (A : Rep ℤ G)
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal]
    [hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hL'K'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K K' hK'K)]
    (k' : K'.toSubgroup) (a : ambientFixedAddSubgroup A K') :
    normResidueNaturalityNormRestrictionPairMap A K K' L L'
        hLK hL'K' hK'K hL'L
        (Additive.ofMul (Abelianization.of (QuotientGroup.mk k')),
          finiteNormClass A K' L' hL'K' a) =
      (Additive.ofMul
          (Abelianization.of
            (QuotientGroup.mk (Subgroup.inclusion hK'K k'))),
        finiteNormClass A K L hLK (relativeNorm A K K' hK'K a)) := by
  ext
  · exact normResidueNaturalityAbelianizedRestriction_of_mk
      K K' L L' hLK hL'K' hK'K hL'L k'
  · exact finiteReciprocityNaturalityNormMap_finiteNormClass A K K' L L'
      hLK hL'K' hK'K hL'L a

/-! ## The conjugation diagram -/

/-- The right vertical isomorphism `σ*` in the second diagram of
reciprocity naturality, obtained by abelianizing the actual conjugation isomorphism
from norm--conjugation naturality. -/
noncomputable def normResidueNaturalityAbelianizedConjugation
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    Abelianization (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃*
      Abelianization
        ((conjugateClosedSubgroup K s).toSubgroup ⧸
          extensionSubgroup (conjugateClosedSubgroup K s)
            (conjugateClosedSubgroup L s)
            (conjugateClosedSubgroup_mono hLK s)) :=
  (finiteReciprocityNaturalityConjugation K L hLK s).abelianizationCongr

/--
Establishes the identity `normResidueNaturalityAbelianizedConjugation K L hLK s (Abelianization.of
(QuotientGroup.mk k)) = Abelianization.of (QuotientGroup.mk (conjugateSubgroupEquiv K s k))`.
-/
@[simp]
theorem normResidueNaturalityAbelianizedConjugation_of_mk
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) :
    normResidueNaturalityAbelianizedConjugation K L hLK s
        (Abelianization.of (QuotientGroup.mk k)) =
      Abelianization.of
        (QuotientGroup.mk (conjugateSubgroupEquiv K s k)) := by
  calc
    normResidueNaturalityAbelianizedConjugation K L hLK s
        (Abelianization.of (QuotientGroup.mk k)) =
      Abelianization.of
        (finiteReciprocityNaturalityConjugation K L hLK s (QuotientGroup.mk k)) :=
      abelianizationCongr_of (finiteReciprocityNaturalityConjugation K L hLK s)
        (QuotientGroup.mk k)
    _ = Abelianization.of
        (QuotientGroup.mk (conjugateSubgroupEquiv K s k)) := by
      rw [finiteReciprocityNaturalityConjugation_mk]

/-- The two vertical conjugation arrows in reciprocity naturality, assembled into
one additive homomorphism.  The second component is the actual descended
map `a ↦ a^s` from norm--conjugation naturality. -/
def normResidueNaturalityConjugationPairMap
    [ContinuousMul G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    let hConjLK := conjugateClosedSubgroup_mono hLK s
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConjLK) :=
      finite_conjugateExtension K L hLK s
    Additive (Abelianization
        (K.toSubgroup ⧸ extensionSubgroup K L hLK)) ×
        FiniteNormQuotient A K L hLK →+
      Additive (Abelianization
        ((conjugateClosedSubgroup K s).toSubgroup ⧸
          extensionSubgroup (conjugateClosedSubgroup K s)
            (conjugateClosedSubgroup L s) hConjLK)) ×
        FiniteNormQuotient A (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConjLK := by
  dsimp only
  letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)) :=
    finite_conjugateExtension K L hLK s
  exact AddMonoidHom.prodMap
    (MonoidHom.toAdditive
      (normResidueNaturalityAbelianizedConjugation K L hLK s).toMonoidHom)
    (finiteReciprocityNaturalityConjugationNormMap A K L hLK s)

/--
On representatives, the conjugation pair map conjugates both the Galois class and the fixed-field
element.
-/
@[simp]
theorem normResidueNaturalityConjugationPairMap_on_representatives
    [ContinuousMul G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A K) :
    let hConjLK := conjugateClosedSubgroup_mono hLK s
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConjLK) :=
      finite_conjugateExtension K L hLK s
    normResidueNaturalityConjugationPairMap A K L hLK s
        (Additive.ofMul (Abelianization.of (QuotientGroup.mk k)),
          finiteNormClass A K L hLK a) =
      (Additive.ofMul
          (Abelianization.of
            (QuotientGroup.mk (conjugateSubgroupEquiv K s k))),
        finiteNormClass A (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConjLK
          (conjugateFixedElement A K s a)) := by
  dsimp only
  let : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)) :=
    finite_conjugateExtension K L hLK s
  ext
  · exact normResidueNaturalityAbelianizedConjugation_of_mk K L hLK s k
  · exact finiteReciprocityNaturalityConjugationNormMap_finiteNormClass
      A K L hLK s a

/-! ## The inclusion/transfer diagram -/

/-- The two upward arrows in the third diagram of reciprocity naturality.  The
first component is Mathlib's actual transfer, transported to
`G(L/K')ᵃᵇ` in transfer--norm naturality; the second is inclusion
`A_K → A_{K'}` descended to finite norm quotients. -/
def normResidueNaturalityTransferInclusionPairMap
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K))] :
    letI : (extensionSubgroup K' L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
    letI : Finite
        (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hLK' hK'K)
    Additive (Abelianization
        (K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K))) ×
        FiniteNormQuotient A K L (hLK'.trans hK'K) →+
      Additive (Abelianization
        (K'.toSubgroup ⧸ extensionSubgroup K' L hLK')) ×
        FiniteNormQuotient A K' L hLK' := by
  letI : (extensionSubgroup K' L hLK').Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
  letI : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hLK' hK'K)
  exact AddMonoidHom.prodMap
    (MonoidHom.toAdditive
      (transferNormNaturalityTransfer K K' L hLK' hK'K))
    (transferNormNaturalityNormQuotientInclusion A K K' L hLK' hK'K)

/--
On representatives, the transfer-inclusion pair map applies transfer to the Galois class and
fixed-field inclusion to the norm class.
-/
@[simp]
theorem normResidueNaturalityTransferInclusionPairMap_on_representatives
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K))]
    (σ : K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))
    (a : ambientFixedAddSubgroup A K) :
    letI : (extensionSubgroup K' L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
    letI : Finite
        (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hLK' hK'K)
    normResidueNaturalityTransferInclusionPairMap A K K' L hLK' hK'K
        (Additive.ofMul (Abelianization.of σ),
          finiteNormClass A K L (hLK'.trans hK'K) a) =
      (Additive.ofMul
          (transferNormNaturalityTransfer K K' L hLK' hK'K
            (Abelianization.of σ)),
        finiteNormClass A K' L hLK'
          (fixedFieldInclusion A K K' hK'K a)) := by
  let : (extensionSubgroup K' L hLK').Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
  let : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hLK' hK'K)
  ext
  · rfl
  · exact transferNormNaturality_normQuotientInclusion_finiteNormClass
      A K K' L hLK' hK'K a

/-! ## The three norm-residue diagrams -/

namespace DegreeData

/-- **Reciprocity naturality, first diagram.**  The norm-residue symbol
commutes with restriction on Galois groups and the relative norm on norm
quotients. -/
theorem normResidueNaturality_norm_restriction
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (T : FiniteAbstractFieldExtension G) (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ T.base.field.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ T.field.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup T.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup T.field.field L' hL'K').Normal]
    [hLKfinite : Finite
      (T.base.field.toSubgroup ⧸ extensionSubgroup T.base.field L hLK)]
    [hL'K'finite : Finite
      (T.field.field.toSubgroup ⧸
        extensionSubgroup T.field.field L' hL'K')] :
    let E : FiniteGaloisSubextension T.base.field :=
      ⟨L, hLK, hLnormal, hLKfinite⟩
    let E' : FiniteGaloisSubextension T.field.field :=
      ⟨L', hL'K', hL'normal, hL'K'finite⟩
    (MonoidHom.toAdditive
        (normResidueNaturalityAbelianizedRestriction
          T.base.field T.field.field L L'
          hLK hL'K' T.below hL'L)).comp
      (D.normResidueSymbol A v hcf T.field E').toAddMonoidHom =
      (D.normResidueSymbol A v hcf T.base E).toAddMonoidHom.comp
        (finiteReciprocityNaturalityNormMap A
          T.base.field T.field.field L L'
          hLK hL'K' T.below hL'L) := by
  dsimp only
  let E : FiniteGaloisSubextension T.base.field :=
    ⟨L, hLK, hLnormal, hLKfinite⟩
  let E' : FiniteGaloisSubextension T.field.field :=
    ⟨L', hL'K', hL'normal, hL'K'finite⟩
  let q := MonoidHom.toAdditive
    (normResidueNaturalityAbelianizedRestriction
      T.base.field T.field.field L L'
      hLK hL'K' T.below hL'L)
  let b := finiteReciprocityNaturalityNormMap A
    T.base.field T.field.field L L' hLK hL'K' T.below hL'L
  have hRec :
      b.comp (D.abstractReciprocityEquiv A v hcf T.field E').toAddMonoidHom =
        (D.abstractReciprocityEquiv A v hcf T.base E).toAddMonoidHom.comp q := by
    apply AddMonoidHom.ext
    intro x
    change b (D.abstractReciprocityEquiv A v hcf T.field E'
        (Additive.ofMul x.toMul)) =
      D.abstractReciprocityEquiv A v hcf T.base E
        (q (Additive.ofMul x.toMul))
    refine QuotientGroup.induction_on x.toMul ?_
    intro z
    change b (D.abstractReciprocityEquiv A v hcf T.field E'
        (Additive.ofMul (Abelianization.of z))) =
      D.abstractReciprocityEquiv A v hcf T.base E
        (Additive.ofMul (Abelianization.of
          (finiteReciprocityNaturalityRestriction
            T.base.field T.field.field L L'
            hLK hL'K' T.below hL'L z)))
    rw [D.abstractReciprocityEquiv_apply_of A v hcf T.field E' z]
    rw [D.abstractReciprocityEquiv_apply_of A v hcf T.base E
      (finiteReciprocityNaturalityRestriction
        T.base.field T.field.field L L'
        hLK hL'K' T.below hL'L z)]
    have h := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
      T L L' hLK hL'K' hL'L
    exact DFunLike.congr_fun h (Additive.ofMul z)
  exact normResidueNaturality_symm_naturality
    (D.abstractReciprocityEquiv A v hcf T.field E')
    (D.abstractReciprocityEquiv A v hcf T.base E) q b hRec

/-- **Reciprocity naturality, second diagram.**  The norm-residue symbol
commutes with conjugation of the extension and of norm classes. -/
theorem normResidueNaturality_conjugation
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    let Ks := K.conjugate s
    let Ls := conjugateClosedSubgroup L s
    let hLsKs := conjugateClosedSubgroup_mono hLK s
    letI : Finite (Ks.field.toSubgroup ⧸
        extensionSubgroup Ks.field Ls hLsKs) :=
      finite_conjugateExtension K.field L hLK s
    let E : FiniteGaloisSubextension K.field :=
      ⟨L, hLK, hLnormal, hLfinite⟩
    let Es : FiniteGaloisSubextension Ks.field :=
      ⟨Ls, hLsKs, inferInstance, inferInstance⟩
    (MonoidHom.toAdditive
        (normResidueNaturalityAbelianizedConjugation
          K.field L hLK s).toMonoidHom).comp
      (D.normResidueSymbol A v hcf K E).toAddMonoidHom =
      (D.normResidueSymbol A v hcf Ks Es).toAddMonoidHom.comp
        (finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s) := by
  dsimp only
  let hLsfinite : Finite
      ((conjugateClosedSubgroup K.field s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K.field s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
    finite_conjugateExtension K.field L hLK s
  let Ks := K.conjugate s
  let E : FiniteGaloisSubextension K.field :=
    ⟨L, hLK, hLnormal, hLfinite⟩
  let Es : FiniteGaloisSubextension Ks.field :=
    ⟨conjugateClosedSubgroup L s, conjugateClosedSubgroup_mono hLK s,
      inferInstance, hLsfinite⟩
  let q := MonoidHom.toAdditive
    (normResidueNaturalityAbelianizedConjugation K.field L hLK s).toMonoidHom
  let b := finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s
  have hRec :
      b.comp (D.abstractReciprocityEquiv A v hcf K E).toAddMonoidHom =
        (D.abstractReciprocityEquiv A v hcf Ks Es).toAddMonoidHom.comp q := by
    apply AddMonoidHom.ext
    intro x
    change b (D.abstractReciprocityEquiv A v hcf K E
        (Additive.ofMul x.toMul)) =
      D.abstractReciprocityEquiv A v hcf Ks Es
        (q (Additive.ofMul x.toMul))
    refine QuotientGroup.induction_on x.toMul ?_
    intro z
    change b (D.abstractReciprocityEquiv A v hcf K E
        (Additive.ofMul (Abelianization.of z))) =
      D.abstractReciprocityEquiv A v hcf Ks Es
        (Additive.ofMul (Abelianization.of
          (finiteReciprocityNaturalityConjugation K.field L hLK s z)))
    rw [D.abstractReciprocityEquiv_apply_of A v hcf K E z]
    rw [D.abstractReciprocityEquiv_apply_of A v hcf
      Ks Es
      (finiteReciprocityNaturalityConjugation K.field L hLK s z)]
    have h := D.finiteReciprocityNaturality_conjugation_commutes
      A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf) K L hLK s
    exact DFunLike.congr_fun h (Additive.ofMul z)
  exact normResidueNaturality_symm_naturality
    (D.abstractReciprocityEquiv A v hcf K E)
    (D.abstractReciprocityEquiv A v hcf Ks Es) q b hRec

/-- **Reciprocity naturality, third diagram.**  The norm-residue symbol
commutes with transfer on abelianized Galois groups and inclusion on norm
quotients. -/
theorem normResidueNaturality_transfer_inclusion
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (T : FiniteAbstractFieldExtension G) (L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ T.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup T.base.field L (hLK'.trans T.below)).Normal]
    [hLfinite : Finite
      (T.base.field.toSubgroup ⧸
        extensionSubgroup T.base.field L (hLK'.trans T.below))] :
    letI : (extensionSubgroup T.field.field L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal
        T.base.field T.field.field L hLK' T.below
    letI : Finite
        (T.field.field.toSubgroup ⧸
          extensionSubgroup T.field.field L hLK') :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion
          T.base.field T.field.field L hLK' T.below)
        (transferNormNaturalityIntermediateInclusion_injective
          T.base.field T.field.field L hLK' T.below)
    let E : FiniteGaloisSubextension T.base.field :=
      ⟨L, hLK'.trans T.below, hLnormal, hLfinite⟩
    let E' : FiniteGaloisSubextension T.field.field :=
      ⟨L, hLK', inferInstance, inferInstance⟩
    (MonoidHom.toAdditive
        (transferNormNaturalityTransfer
          T.base.field T.field.field L hLK' T.below)).comp
      (D.normResidueSymbol A v hcf T.base E).toAddMonoidHom =
      (D.normResidueSymbol A v hcf T.field E').toAddMonoidHom.comp
        (transferNormNaturalityNormQuotientInclusion A
          T.base.field T.field.field L hLK' T.below) := by
  dsimp only
  let : (extensionSubgroup T.field.field L hLK').Normal :=
    transferNormNaturality_intermediateExtension_normal
      T.base.field T.field.field L hLK' T.below
  let : Finite
      (T.field.field.toSubgroup ⧸
        extensionSubgroup T.field.field L hLK') :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion
        T.base.field T.field.field L hLK' T.below)
      (transferNormNaturalityIntermediateInclusion_injective
        T.base.field T.field.field L hLK' T.below)
  let E : FiniteGaloisSubextension T.base.field :=
    ⟨L, hLK'.trans T.below, hLnormal, hLfinite⟩
  let E' : FiniteGaloisSubextension T.field.field :=
    ⟨L, hLK', inferInstance, inferInstance⟩
  let q := MonoidHom.toAdditive
    (transferNormNaturalityTransfer
      T.base.field T.field.field L hLK' T.below)
  let b := transferNormNaturalityNormQuotientInclusion A
    T.base.field T.field.field L hLK' T.below
  have hRec :
      b.comp (D.abstractReciprocityEquiv A v hcf T.base E).toAddMonoidHom =
        (D.abstractReciprocityEquiv A v hcf T.field E').toAddMonoidHom.comp q := by
    apply AddMonoidHom.ext
    intro x
    change
      b
          (D.transferNormNaturalityAbelianizedReciprocity
            A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
            T.base L (hLK'.trans T.below) x) =
        D.transferNormNaturalityAbelianizedReciprocity
          A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
          T.field L hLK' (q x)
    have h := congrArg (fun f => f x)
      (D.transferNormNaturality A v
        (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
        T L hLK').symm
    exact h
  exact normResidueNaturality_symm_naturality
    (D.abstractReciprocityEquiv A v hcf T.base E)
    (D.abstractReciprocityEquiv A v hcf T.field E') q b hRec

end DegreeData

end
end
end ClassFormation
