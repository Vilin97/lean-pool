/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FixedTowerUnitDescent
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteFieldUnitMaps

/-! # Infinite Unit Descent -/

@[expose] public section
universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Infinite-level unit descent

This module bundles finite intermediate fields over a finite base, defines
the infinite unit subgroup, proves its action and norm stability, and
descends maximal-unramified norm equations from finite support.
-/

noncomputable
section

open CategoryTheory
open scoped BigOperators

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- The canonical finite-field extension bundle carried by a finite
intermediate field over a bundled finite base. -/
noncomputable def toFiniteAbstractFieldExtension
    {E : ClosedSubgroup G} (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) :
    FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) :=
    M.finite
  exact FiniteAbstractFieldExtension.ofInclusion M.field K M.below

/-- The upper endpoint of the canonical finite-field extension bundle. -/
noncomputable def toFiniteAbstractField
    {E : ClosedSubgroup G} (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) : FiniteAbstractField G :=
  (M.toFiniteAbstractFieldExtension K).field

end FiniteIntermediateField

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- Unit-valued strengthening of finite-support descent.  If the chosen
finite support is a unit, the descended K-rational element is a unit as
well. -/
theorem descend_maximalUnramified_fixed_unit_of_finiteSupport
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hφ : D.frobeniusExponent
      (K.toFiniteResidueAbstractField D) L hLK φ = 1)
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    [hPnormal : (extensionSubgroup K.field P.field P.below).Normal]
    (aI : ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field))
    (aP : v.unitAddSubgroup (P.toFiniteAbstractField K))
    (hsupport :
      fixedFieldInclusion A P.field (D.maximalUnramifiedField L) P.above aP.1 =
        fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI)
    (hfixed :
      D.frobeniusQuotientAction A K.field L hLK φ.1
          (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI) =
        fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI) :
    ∃ aK : v.unitAddSubgroup K,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField_le K.field) aK.1 = aI := by
  obtain ⟨bK, hbK⟩ :=
    D.descend_maximalUnramified_fixed_of_finiteSupport
      A (K.toFiniteResidueAbstractField D) L hLK φ hφ
        P aI aP.1 hsupport hfixed
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) :=
    P.finite
  let EP := P.toFiniteAbstractFieldExtension K
  have hKP :
      fixedFieldInclusion A K.field P.field P.below bK = aP.1 := by
    apply Subtype.ext
    have hsupportVal := congrArg
      (fun z : ambientFixedAddSubgroup A (D.maximalUnramifiedField L) => z.1)
      hsupport
    have hbKVal := congrArg
      (fun z : ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field) => z.1)
      hbK
    exact hbKVal.trans hsupportVal.symm
  have htower := v.normalizedValuation_tower EP
    (fixedFieldInclusion A K.field P.field P.below bK)
  have hvalP :
      v.valuationAt EP.field
        (fixedFieldInclusion A K.field P.field P.below bK) = 0 := by
    rw [hKP]
    exact aP.2
  have hmul :
      (EP.degree : ℕ) •
        ((v.valuationAt K bK : v.valueGroup) : ZHat) = 0 := by
    let ER := EP.toFiniteResidueAbstractExtension D
    change (ER.residueDegree : ℕ) •
        ((v.valuationAt EP.field
          (fixedFieldInclusion A K.field P.field P.below bK) :
            v.valueGroup) : ZHat) =
      ((v.valuationAt K
        (relativeNorm A K.field P.field P.below
          (fixedFieldInclusion A K.field P.field P.below bK)) :
            v.valueGroup) : ZHat) at htower
    rw [hvalP] at htower
    rw [show relativeNorm A K.field P.field P.below
        (fixedFieldInclusion A K.field P.field P.below bK) =
          (EP.degree : ℕ) • bK by
      exact relativeNorm_fixedFieldInclusion A EP.toFiniteAbstractExtension bK,
      map_nsmul] at htower
    simpa using htower.symm
  have hbKunit : bK ∈ v.unitAddSubgroup K := by
    rw [v.mem_unitAddSubgroup_iff]
    apply Subtype.ext
    apply zHatMulNat_injective EP.degree.property
    change (EP.degree : ℕ) •
        ((v.valuationAt K bK : v.valueGroup) : ZHat) =
      (EP.degree : ℕ) • ((0 : v.valueGroup) : ZHat)
    simpa using hmul
  exact ⟨⟨bK, hbKunit⟩, hbK⟩

/-- An element of an infinite algebraic extension is a unit when it is
already a unit at some finite intermediate stage.  This is the literal
finite-support meaning of `U_E = \bigcup_M U_M` used. -/
def IsFiniteStageUnit
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A E) : Prop :=
  ∃ M : FiniteIntermediateField E K.field,
    ∃ u : v.unitAddSubgroup (M.toFiniteAbstractField K),
      fixedFieldInclusion A M.field E M.above u.1 = a

/-- The actual finite-stage unit group `U_E` inside `A_E`. -/
noncomputable def infiniteUnitAddSubgroup
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (hEK : E.toSubgroup ≤ K.field.toSubgroup) :
    AddSubgroup (ambientFixedAddSubgroup A E) where
  carrier := {a | v.IsFiniteStageUnit E K a}
  zero_mem' := by
    let M := FiniteIntermediateField.base E K.field hEK
    refine ⟨M, 0, ?_⟩
    rfl
  add_mem' := by
    intro a b ha hb
    rcases ha with ⟨M, u, hu⟩
    rcases hb with ⟨N, w, hw⟩
    let P := M.compositum N
    let hPfinite : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) :=
      P.finite
    let hPM : P.field.toSubgroup ≤ M.field.toSubgroup := M.compositum_le_left N
    let hPN : P.field.toSubgroup ≤ N.field.toSubgroup := M.compositum_le_right N
    let hPMfinite : Finite
        (M.field.toSubgroup ⧸ extensionSubgroup M.field P.field hPM) :=
      FiniteIntermediateField.finite_extension_of_le
        P.below M.below hPM
    let hPNfinite : Finite
        (N.field.toSubgroup ⧸ extensionSubgroup N.field P.field hPN) :=
      FiniteIntermediateField.finite_extension_of_le
        P.below N.below hPN
    let : Finite
        ((M.toFiniteAbstractField K).field.toSubgroup ⧸
          extensionSubgroup (M.toFiniteAbstractField K).field P.field hPM) := by
      change Finite
        (M.field.toSubgroup ⧸ extensionSubgroup M.field P.field hPM)
      exact hPMfinite
    let : Finite
        ((N.toFiniteAbstractField K).field.toSubgroup ⧸
          extensionSubgroup (N.toFiniteAbstractField K).field P.field hPN) := by
      change Finite
        (N.field.toSubgroup ⧸ extensionSubgroup N.field P.field hPN)
      exact hPNfinite
    let EMP : FiniteAbstractFieldExtension G :=
      FiniteAbstractFieldExtension.ofInclusion
        P.field (M.toFiniteAbstractField K) hPM
    let ENP : FiniteAbstractFieldExtension G :=
      FiniteAbstractFieldExtension.ofInclusion
        P.field (N.toFiniteAbstractField K) hPN
    let hEMPfield : EMP.field = P.toFiniteAbstractField K :=
      FiniteAbstractField.eq_of_field_eq _ _ rfl
    let hENPfield : ENP.field = P.toFiniteAbstractField K :=
      FiniteAbstractField.eq_of_field_eq _ _ rfl
    let uP : v.unitAddSubgroup (P.toFiniteAbstractField K) :=
      hEMPfield ▸ v.finiteUnitInclusion EMP u
    let wP : v.unitAddSubgroup (P.toFiniteAbstractField K) :=
      hENPfield ▸ v.finiteUnitInclusion ENP w
    refine ⟨P, uP + wP, ?_⟩
    apply Subtype.ext
    have huval : u.1.1 = a.1 :=
      congrArg (fun x : ambientFixedAddSubgroup A E => x.1) hu
    have hwval : w.1.1 = b.1 :=
      congrArg (fun x : ambientFixedAddSubgroup A E => x.1) hw
    change uP.1.1 + wP.1.1 = a.1 + b.1
    have huP : uP.1.1 = u.1.1 :=
      v.finiteUnitInclusion_transport_coe EMP
        (P.toFiniteAbstractField K) hEMPfield u
    have hwP : wP.1.1 = w.1.1 :=
      v.finiteUnitInclusion_transport_coe ENP
        (P.toFiniteAbstractField K) hENPfield w
    rw [huP, hwP, huval, hwval]
  neg_mem' := by
    intro a ha
    rcases ha with ⟨M, u, hu⟩
    refine ⟨M, -u, ?_⟩
    apply Subtype.ext
    exact congrArg Neg.neg (congrArg Subtype.val hu)

/--
Characterizes `a ∈ v.infiniteUnitAddSubgroup E K hEK` by the equivalent condition
`v.IsFiniteStageUnit E K a`.
-/
@[simp]
theorem mem_infiniteUnitAddSubgroup_iff
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (hEK : E.toSubgroup ≤ K.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E) :
    a ∈ v.infiniteUnitAddSubgroup E K hEK ↔
      v.IsFiniteStageUnit E K a :=
  Iff.rfl

/-- The actual `G(\widetilde L/K)`-action preserves the finite-stage unit
group `U_{\widetilde L}`.  A unit is first moved to a finite Galois
refinement of its support; that refinement is stable under the chosen
representative, so the translated element still has finite unit support. -/
theorem frobeniusQuotientAction_mem_infiniteUnitAddSubgroup
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (ha : a ∈ v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK)) :
    D.frobeniusQuotientAction A K.field L hLK q a ∈
      v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
        (D.maximalUnramifiedField_le_of_le hLK) := by
  let E := D.maximalUnramifiedField L
  let hEK := D.maximalUnramifiedField_le_of_le hLK
  let hEnormal : (extensionSubgroup K.field E hEK).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L hLK
  rcases ha with ⟨M, u, hu⟩
  let R := M.galoisRefinement
  have hRM : R.field.toSubgroup ≤ M.field.toSubgroup :=
    M.galoisRefinement_le_field
  let hRfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field R.field R.below) :=
    R.finite
  let hRMfinite : Finite
      (M.field.toSubgroup ⧸ extensionSubgroup M.field R.field hRM) :=
    FiniteIntermediateField.finite_extension_of_le R.below M.below hRM
  let : Finite
      ((M.toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup (M.toFiniteAbstractField K).field R.field hRM) := by
    change Finite
      (M.field.toSubgroup ⧸ extensionSubgroup M.field R.field hRM)
    exact hRMfinite
  let k : K.field.toSubgroup := Quotient.out q
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  let EMR : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      R.field (M.toFiniteAbstractField K) hRM
  let ER := R.toFiniteAbstractFieldExtension K
  let hEMRfield : EMR.field = R.toFiniteAbstractField K :=
    FiniteAbstractField.eq_of_field_eq _ _ rfl
  let uR : v.unitAddSubgroup (R.toFiniteAbstractField K) :=
    hEMRfield ▸ v.finiteUnitInclusion EMR u
  let uR' : v.unitAddSubgroup (R.toFiniteAbstractField K) :=
    v.unitActionLinearMap ER
      (inferInstance : (extensionSubgroup K.field R.field R.below).Normal) k uR
  refine ⟨R, uR', ?_⟩
  rw [← hkq]
  apply Subtype.ext
  have huval : u.1.1 = a.1 :=
    congrArg (fun z : ambientFixedAddSubgroup A E => z.1) hu
  change A.ρ k.1 uR.1.1 = A.ρ k.1 a.1
  have huR : uR.1.1 = u.1.1 :=
    v.finiteUnitInclusion_transport_coe EMR
      (R.toFiniteAbstractField K) hEMRfield u
  rw [huR, huval]

/-- The Frobenius power sum used preserves the finite-stage unit
group of the maximal unramified extension. -/
theorem frobeniusPowerSum_mem_infiniteUnit_universalNormDescent
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (n : ℕ)
    (x : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (hx : x ∈ v.infiniteUnitAddSubgroup
      (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK)) :
    D.frobeniusPowerSum A K.field L hLK φ n x ∈
      v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
        (D.maximalUnramifiedField_le_of_le hLK) := by
  unfold DegreeData.frobeniusPowerSum
  apply AddSubgroup.sum_mem
  intro i _
  exact v.frobeniusQuotientAction_mem_infiniteUnitAddSubgroup
    K L hLK (φ ^ i.1) x hx

/-- The relative norm from `\widetilde L` to `\widetilde K`, included back
in `A_{\widetilde L}`, preserves finite-stage units. -/
theorem maximalUnramifiedNorm_mem_infiniteUnitAddSubgroup
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (ha : a ∈ v.infiniteUnitAddSubgroup
      (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK)) :
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    fixedFieldInclusion A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a)
      ∈ v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
        (D.maximalUnramifiedField_le_of_le hLK) := by
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let I := D.maximalUnramifiedField K.field
  let E := D.maximalUnramifiedField L
  let hEI := D.maximalUnramifiedField_mono hLK
  let N := relativeNorm A I E hEI
  let : Fintype (I.toSubgroup ⧸ extensionSubgroup I E hEI) :=
    Fintype.ofFinite _
  let qK (q : I.toSubgroup ⧸ extensionSubgroup I E hEI) :
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK :=
    let r : I.toSubgroup := Quotient.out q
    let k : K.field.toSubgroup :=
      ⟨r.1, (D.maximalUnramifiedField_le K.field) r.2⟩
    QuotientGroup.mk k
  let f (q : I.toSubgroup ⧸ extensionSubgroup I E hEI) :
      ambientFixedAddSubgroup A E :=
    D.frobeniusQuotientAction A K.field L hLK (qK q) a
  have hterm (q : I.toSubgroup ⧸ extensionSubgroup I E hEI) :
      f q ∈ v.infiniteUnitAddSubgroup E K
        (D.maximalUnramifiedField_le_of_le hLK) := by
    exact
      v.frobeniusQuotientAction_mem_infiniteUnitAddSubgroup
        K L hLK (qK q) a ha
  have hsum :
      ∑ q : I.toSubgroup ⧸ extensionSubgroup I E hEI, f q ∈
        v.infiniteUnitAddSubgroup E K
          (D.maximalUnramifiedField_le_of_le hLK) :=
    AddSubgroup.sum_mem _ (fun q _ => hterm q)
  have heq :
      fixedFieldInclusion A I E hEI (N a) =
        ∑ q : I.toSubgroup ⧸ extensionSubgroup I E hEI, f q := by
    apply Subtype.ext
    rw [fixedFieldInclusion_coe, relativeNorm_apply_coe]
    rw [relativeNormValue]
    change
      ∑ q : I.toSubgroup ⧸ extensionSubgroup I E hEI,
          relativeCosetAction A I E hEI a q =
        (AddSubgroup.subtype (ambientFixedAddSubgroup A E))
          (∑ q : I.toSubgroup ⧸ extensionSubgroup I E hEI, f q)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q _
    let r : I.toSubgroup := Quotient.out q
    have hrq : (QuotientGroup.mk r :
        I.toSubgroup ⧸ extensionSubgroup I E hEI) = q :=
      Quotient.out_eq' q
    change relativeCosetAction A I E hEI a q = (f q).1
    calc
      relativeCosetAction A I E hEI a q =
          relativeCosetAction A I E hEI a (QuotientGroup.mk r) :=
        congrArg (relativeCosetAction A I E hEI a) hrq.symm
      _ = A.ρ r.1 a.1 := relativeCosetAction_mk A I E hEI a r
      _ = (f q).1 := by rfl
  rw [heq]
  exact hsum

/-- A maximal-unramified norm of a finite-stage unit descends to a genuine
unit of `K` once it is fixed by a degree-one Frobenius lift. -/
theorem descend_maximalUnramifiedNorm_unit
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hφ : D.frobeniusExponent
      (K.toFiniteResidueAbstractField D) L hLK φ = 1)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (ha : a ∈ v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (hfixed :
      letI : Finite
          ((D.maximalUnramifiedField K.field).toSubgroup ⧸
            extensionSubgroup (D.maximalUnramifiedField K.field)
              (D.maximalUnramifiedField L)
              (D.maximalUnramifiedField_mono hLK)) :=
        D.maximalUnramifiedExtension_finite K.field L hLK
      let N := relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      let J := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      D.frobeniusQuotientAction A K.field L hLK φ.1 (J (N a)) = J (N a)) :
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    ∃ aK : v.unitAddSubgroup K,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField_le K.field) aK.1 =
        relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a := by
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let I := D.maximalUnramifiedField K.field
  let E := D.maximalUnramifiedField L
  let hEI := D.maximalUnramifiedField_mono hLK
  let N := relativeNorm A I E hEI
  let J := fixedFieldInclusion A I E hEI
  let hEnormal : (extensionSubgroup K.field E
      (D.maximalUnramifiedField_le_of_le hLK)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L hLK
  have hmem : J (N a) ∈ v.infiniteUnitAddSubgroup E K
      (D.maximalUnramifiedField_le_of_le hLK) :=
    v.maximalUnramifiedNorm_mem_infiniteUnitAddSubgroup K L hLK a ha
  rcases hmem with ⟨Q, aQ, haQ⟩
  let R := Q.galoisRefinement
  let hRQ : R.field.toSubgroup ≤ Q.field.toSubgroup :=
    Q.galoisRefinement_le_field
  let hQabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) Q.field (le_baseField Q.field)) :=
    Q.absoluteFinite
  let hRfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field R.field R.below) :=
    R.finite
  let hRQfinite : Finite
      (Q.field.toSubgroup ⧸ extensionSubgroup Q.field R.field hRQ) :=
    FiniteIntermediateField.finite_extension_of_le R.below Q.below hRQ
  let : Finite
      ((Q.toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup (Q.toFiniteAbstractField K).field R.field hRQ) := by
    change Finite
      (Q.field.toSubgroup ⧸ extensionSubgroup Q.field R.field hRQ)
    exact hRQfinite
  let hRnormal : (extensionSubgroup K.field R.field R.below).Normal :=
    FiniteIntermediateField.galoisRefinement_normal Q
  let EQR : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      R.field (Q.toFiniteAbstractField K) hRQ
  let hEQRfield : EQR.field = R.toFiniteAbstractField K :=
    FiniteAbstractField.eq_of_field_eq _ _ rfl
  let aR : v.unitAddSubgroup (R.toFiniteAbstractField K) :=
    hEQRfield ▸ v.finiteUnitInclusion EQR aQ
  have haR : fixedFieldInclusion A R.field E R.above aR.1 = J (N a) := by
    apply Subtype.ext
    change aR.1.1 = (J (N a)).1
    have haRcoe : aR.1.1 = aQ.1.1 :=
      v.finiteUnitInclusion_transport_coe EQR
        (R.toFiniteAbstractField K) hEQRfield aQ
    rw [haRcoe]
    exact congrArg Subtype.val haQ
  exact v.descend_maximalUnramified_fixed_unit_of_finiteSupport
    K L hLK φ hφ R (N a) aR haR hfixed

end ValuationData
end

end ClassFormation
