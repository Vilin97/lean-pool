/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitNormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateFieldCompositum
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusFixedFieldAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusQuotientDescent
/-!
Proves the universal norm-descent argument from maximal-unramified units to finite intermediate
norm subgroups.
-/

namespace ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section
open CategoryTheory
open scoped BigOperators
-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
namespace ValuationData
variable {D : DegreeData G} {A : Rep ℤ G}

/-- The universal norm-descent lemma, first descent step: the maximal-unramified norm of `u`
is represented by a genuine unit over `K`. -/
theorem universalNormDescent_endpoint_descent
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hφ : D.frobeniusExponent
      (K.toFiniteResidueAbstractField D) L hLK φ = 1)
    {ι : Type*} (s : Finset ι)
    (τ : ι →
      (D.extensionNormalizedDegreeContinuous
        (K.toFiniteResidueAbstractField D) L hLK).toMonoidHom.ker)
    (u : v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (uᵢ : ι → v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (hstar : D.frobeniusQuotientAction A K.field L hLK φ.1 u.1 - u.1 =
      ∑ i ∈ s,
        (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i).1 -
          (uᵢ i).1)) :
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
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u.1 := by
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  have hfixed := D.maximalUnramifiedNorm_fixed_of_hstar A
    (K.toFiniteResidueAbstractField D) L hLK
    s φ.1 τ u.1 (fun i => (uᵢ i).1) hstar
  exact v.descend_maximalUnramifiedNorm_unit K L hLK φ hφ u.1 u.2 hfixed

private theorem finiteUnitNormRange_of_norm_add_quotientCard_smul
    (v : ValuationData D A) [IsTopologicalGroup G]
    (E : ClosedSubgroup G) (K : FiniteAbstractField G)
    (M P : FiniteIntermediateField E K.field)
    (hPM : P.field.toSubgroup ≤ M.field.toSubgroup)
    (SF : FiniteAbstractField G)
    (hSP : SF.field.toSubgroup ≤ P.field.toSubgroup)
    (hSK : SF.field.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field SF.field hSK)]
    (aK zK : v.unitAddSubgroup K) (yS : v.unitAddSubgroup SF)
    (hbaseRelation : aK.1 = relativeNorm A K.field SF.field hSK yS.1 +
      P.quotientCard • zK.1) :
    aK.1 ∈ v.finiteIntermediateUnitNormRange E K M := by
  let : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) := P.finite
  let hPSfinite : Finite
      (P.field.toSubgroup ⧸ extensionSubgroup P.field SF.field hSP) :=
    FiniteIntermediateField.finite_extension_of_le hSK P.below hSP
  let : Finite
      ((P.toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup (P.toFiniteAbstractField K).field SF.field hSP) := by
    change Finite
      (P.field.toSubgroup ⧸ extensionSubgroup P.field SF.field hSP)
    exact hPSfinite
  let EPS : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      SF.field (P.toFiniteAbstractField K) hSP
  let yP : v.unitAddSubgroup (P.toFiniteAbstractField K) := by
    simpa [EPS, FiniteAbstractFieldExtension.ofInclusion] using
        v.finiteUnitNorm EPS yS
  let EP := P.toFiniteAbstractFieldExtension K
  let zP : v.unitAddSubgroup (P.toFiniteAbstractField K) :=
    v.finiteUnitInclusion EP zK
  let aP : v.unitAddSubgroup (P.toFiniteAbstractField K) := yP + zP
  let FT : DegreeData.FiniteTower G := {
    top := SF.field
    middle := P.field
    base := K.field
    top_le_middle := hSP
    middle_le_base := P.below
    finiteTopQuotient := hPSfinite
    finiteBaseQuotient := P.finite }
  have hnDegree : (EP.degree : ℕ) = P.quotientCard := by
    change (EP.toFiniteAbstractExtension.degree : ℕ) = P.quotientCard
    rw [EP.toFiniteAbstractExtension.degree_coe]
    change
      Nat.card
        (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) = P.quotientCard
    rfl
  let yPraw : ambientFixedAddSubgroup A P.field :=
    ⟨yP.1.1, by
      intro g
      apply yP.1.2⟩
  let zPraw : ambientFixedAddSubgroup A P.field :=
    ⟨zP.1.1, by
      intro g
      apply zP.1.2⟩
  let aPraw : ambientFixedAddSubgroup A P.field :=
    ⟨aP.1.1, by
      intro g
      apply aP.1.2⟩
  have haPnorm : relativeNorm A K.field P.field P.below aP.1 = aK.1 := by
    change relativeNorm A K.field P.field P.below aPraw = aK.1
    have haPraw : aPraw = yPraw + zPraw := by
      apply Subtype.ext
      rfl
    rw [haPraw, map_add]
    have hyTower := FT.norm_trans_apply A yS.1
    have hzNorm := relativeNorm_fixedFieldInclusion A
      EP.toFiniteAbstractExtension zK.1
    change relativeNorm A K.field P.field P.below
        (fixedFieldInclusion A K.field P.field P.below zK.1) =
      (EP.degree : ℕ) • zK.1 at hzNorm
    change relativeNorm A K.field P.field P.below yPraw +
      relativeNorm A K.field P.field P.below zPraw = aK.1
    change relativeNorm A K.field P.field P.below
        (relativeNorm A P.field SF.field hSP yS.1) +
      relativeNorm A K.field P.field P.below
        (fixedFieldInclusion A K.field P.field P.below zK.1) = aK.1
    rw [hyTower]
    rw [hzNorm, hnDegree]
    exact hbaseRelation.symm
  exact v.mem_finiteIntermediateUnitNormRange_of_overfield
    E K M P hPM aP aK.1 haPnorm

private theorem exists_unit_lift_of_field_le
    (v : ValuationData D A) [IsTopologicalGroup G]
    (B F : FiniteAbstractField G) (h : F.field.toSubgroup ≤ B.field.toSubgroup)
    (u : v.unitAddSubgroup B) :
    ∃ x : v.unitAddSubgroup F, x.1.1 = u.1.1 := by
  let E : FiniteAbstractFieldExtension G :=
    { base := B
      field := F
      below := h
      finiteQuotient := FiniteIntermediateField.finite_extension_of_le
        (le_baseField F.field) (le_baseField B.field) h }
  exact ⟨v.finiteUnitInclusion E u, rfl⟩

private theorem fixedFieldInclusion_unit_mem_infinite
    (v : ValuationData D A) [IsTopologicalGroup G]
    (E : ClosedSubgroup G) (K F : FiniteAbstractField G)
    (hFE : E.toSubgroup ≤ F.field.toSubgroup)
    (hFK : F.field.toSubgroup ≤ K.field.toSubgroup)
    (hEK : E.toSubgroup ≤ K.field.toSubgroup)
    (u : v.unitAddSubgroup F) :
    fixedFieldInclusion A F.field E hFE u.1 ∈ v.infiniteUnitAddSubgroup E K hEK := by
  let M : FiniteIntermediateField E K.field :=
    { field := F.field
      above := hFE
      below := hFK
      finite := FiniteIntermediateField.finite_extension_of_le
        (le_baseField F.field) (le_baseField K.field) hFK }
  have h : F = M.toFiniteAbstractField K := FiniteAbstractField.eq_of_field_eq _ _ rfl
  refine ⟨M, h ▸ u, ?_⟩
  apply Subtype.ext
  change (h ▸ u : v.unitAddSubgroup (M.toFiniteAbstractField K)).1.1 = u.1.1
  dsimp only

private theorem powerTower_corrected_norm_relation
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (powerTower : DegreeData.FrobeniusPowerFixedFieldTower D)
    (uS : v.unitAddSubgroup powerTower.toFrobeniusFixedFieldTower.base)
    (uBar yBar : v.unitAddSubgroup powerTower.toFrobeniusFixedFieldTower.field)
    (u : ambientFixedAddSubgroup A
      (D.maximalUnramifiedField powerTower.ambient.field)) :
  let KR := powerTower.ambientBase
  let L := powerTower.ambient.field
  let hLK := powerTower.ambient.below
  letI : Finite (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) :=
    powerTower.ambient.finite
  let φ := powerTower.frobenius
  let n := powerTower.n
  let σ := powerTower.baseFrobenius
  let σn := powerTower.fieldFrobenius
  let fixedTower := powerTower.toFrobeniusFixedFieldTower
  let SF := fixedTower.base
  let TF := fixedTower.field
  let S := SF.field
  let T := TF.field
  let hTS := powerTower.field_le_base
  letI : Finite (S.toSubgroup ⧸ extensionSubgroup S T hTS) :=
    powerTower.relativeFinite
  let hTE := D.fieldInertia_le_frobeniusFixedField KR L hLK σn
  let hSE := D.fieldInertia_le_frobeniusFixedField KR L hLK σ
  let E := D.maximalUnramifiedField L
  let I := D.maximalUnramifiedField KR.field
  let hEI := D.maximalUnramifiedField_mono hLK
  letI : Finite (I.toSubgroup ⧸ extensionSubgroup I E hEI) :=
    D.maximalUnramifiedExtension_finite KR.field L hLK
  let N := relativeNorm A I E hEI
  let J := fixedFieldInclusion A I E hEI
  let φnyBarE := D.frobeniusPowerSum A KR.field L hLK φ.1 n
    (fixedFieldInclusion A T E hTE yBar.1)
  let w := fixedFieldInclusion A T E hTE uBar.1 - φnyBarE
  relativeNorm A S T hTS uBar.1 = uS.1 → uS.1.1 = u.1 →
    D.frobeniusQuotientAction A KR.field L hLK φ.1 (J (N w)) = J (N w) →
    ∃ yS : v.unitAddSubgroup SF,
      J (N u) = J (N (D.frobeniusPowerSum A KR.field L hLK φ.1 n
        (fixedFieldInclusion A S E hSE yS.1))) + n • J (N w) := by
  dsimp only
  intro huBar huSval hfixedZ
  let KR := powerTower.ambientBase
  let L := powerTower.ambient.field
  let hLK := powerTower.ambient.below
  let : Finite (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) :=
    powerTower.ambient.finite
  let φ := powerTower.frobenius
  let hφ := powerTower.exponent_one
  let n := powerTower.n
  let hn := powerTower.n_pos
  let σ := powerTower.baseFrobenius
  let σn := powerTower.fieldFrobenius
  let fixedTower := powerTower.toFrobeniusFixedFieldTower
  let finiteFixedTower := powerTower.toFiniteAmbientFrobeniusFixedFieldTower
  let SF := fixedTower.base
  let TF := fixedTower.field
  let S := SF.field
  let T := TF.field
  let hTS := powerTower.field_le_base
  let : Finite (S.toSubgroup ⧸ extensionSubgroup S T hTS) :=
    powerTower.relativeFinite
  let hTE := D.fieldInertia_le_frobeniusFixedField KR L hLK σn
  let hSE := D.fieldInertia_le_frobeniusFixedField KR L hLK σ
  let E := D.maximalUnramifiedField L
  let I := D.maximalUnramifiedField KR.field
  let hEI := D.maximalUnramifiedField_mono hLK
  let : Finite (I.toSubgroup ⧸ extensionSubgroup I E hEI) :=
    D.maximalUnramifiedExtension_finite KR.field L hLK
  let N := relativeNorm A I E hEI
  let J := fixedFieldInclusion A I E hEI
  let φnyBarE := D.frobeniusPowerSum A KR.field L hLK φ.1 n
    (fixedFieldInclusion A T E hTE yBar.1)
  let w := fixedFieldInclusion A T E hTE uBar.1 - φnyBarE
  have hφσ := powerTower.frobenius_commute_base
  have hφσn := powerTower.frobenius_commute_field
  let powerT : ambientFixedAddSubgroup A T :=
    ∑ i : Fin n, D.frobeniusFixedFieldAction A KR L hLK σn
      (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar.1
  let powerTUnit : v.unitAddSubgroup TF :=
    ∑ i : Fin n, v.frobeniusFixedFieldUnitAction KR L hLK σn
      (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar
  have hpowerTUnit : powerTUnit.1 = powerT :=
    map_sum (v.unitAddSubgroup TF).subtype _ Finset.univ
  let wBar : v.unitAddSubgroup TF := uBar - powerTUnit
  have hwBarIncl : fixedFieldInclusion A T E hTE wBar.1 = w := by
    have hpIncl := D.fixedFieldPowerSum_inclusion A KR L hLK σn
      φ.1 hφσn n yBar.1
    apply Subtype.ext
    have hpVal := congrArg Subtype.val hpIncl
    change uBar.1.1 - powerTUnit.1.1 = uBar.1.1 - φnyBarE.1
    rw [hpowerTUnit]
    exact congrArg (fun z => uBar.1.1 - z) hpVal
  let EST : FiniteAbstractFieldExtension G := fixedTower.extension
  let yS : v.unitAddSubgroup SF := v.finiteUnitNorm EST yBar
  let uSraw : ambientFixedAddSubgroup A S := uS.1
  let ySraw : ambientFixedAddSubgroup A S := yS.1
  let uBarraw : ambientFixedAddSubgroup A T := uBar.1
  let wBarraw : ambientFixedAddSubgroup A T := wBar.1
  let powerS : ambientFixedAddSubgroup A S :=
    ∑ i : Fin n, D.frobeniusFixedFieldAction A KR L hLK σ
      (φ.1 ^ i.1) (Commute.pow_left hφσ i.1) ySraw
  have hpowerNorm := D.fixedFieldPowerSum_relativeNorm A KR L hLK
    σ σn hTS φ.1 hφσ hφσn n yBar.1
  have huBarraw : relativeNorm A S T hTS uBarraw = uSraw := huBar
  have hySraw : relativeNorm A S T hTS yBar.1 = ySraw := rfl
  have hpowerNormRaw : relativeNorm A S T hTS powerT = powerS := by
    change relativeNorm A S T hTS powerT =
      ∑ i : Fin n, D.frobeniusFixedFieldAction A KR L hLK σ
        (φ.1 ^ i.1) (Commute.pow_left hφσ i.1)
        (relativeNorm A S T hTS yBar.1) at hpowerNorm
    rw [hySraw] at hpowerNorm
    exact hpowerNorm
  have hwBarNorm : relativeNorm A S T hTS wBarraw = uSraw - powerS := by
    have hwBarCoe : wBarraw = uBarraw - powerT := by
      apply Subtype.ext
      change uBar.1.1 - powerTUnit.1.1 = uBar.1.1 - powerT.1
      exact congrArg (fun z => uBar.1.1 - z)
        (congrArg Subtype.val hpowerTUnit)
    rw [hwBarCoe]
    rw [map_sub, huBarraw]
    exact congrArg (fun z => uSraw - z) hpowerNormRaw
  obtain ⟨gS, hgClosure, _hgDegree, hg⟩ :=
    D.frobeniusPowerFixedField_generator KR L hLK φ hφ n n hn hn
  let fixedGenerator :
      finiteFixedTower.toFrobeniusFixedFieldTower.CyclicGenerator :=
    { element := gS
      mapsToFrobenius := hgClosure
      generates := hg }
  have hcard := D.frobeniusPowerFixedField_quotientCard
    KR L hLK φ hφ n n hn hn
  have hdegree : (finiteFixedTower.extension.degree : ℕ) = n := by
    calc
      (finiteFixedTower.extension.degree : ℕ) =
          Nat.card
            finiteFixedTower.extension.toFiniteAbstractExtension.quotient :=
        finiteFixedTower.extension.toFiniteAbstractExtension.degree_coe
      _ = n := hcard
  have hnormW := v.maximalNorm_relativeNorm_fixedTower
    finiteFixedTower fixedGenerator n hdegree wBar
  have hnormWraw :
      J (N (fixedFieldInclusion A S E hSE
        (relativeNorm A S T hTS wBarraw))) =
      D.frobeniusPowerSum A KR.field L hLK σ.1 n
        (J (N (fixedFieldInclusion A T E hTE wBarraw))) := hnormW
  have hσfixedZ : D.frobeniusQuotientAction A KR.field L hLK σ.1 (J (N w)) =
      J (N w) := by
    let B := D.frobeniusQuotientRepresentation A KR.field L hLK
    have hpow := rep_action_pow_fixed
      B φ.1 (J (N w)) hfixedZ n
    change D.frobeniusQuotientAction A KR.field L hLK
      (φ.1 ^ n) (J (N w)) = J (N w) at hpow
    simpa only [σ, DegreeData.FrobeniusPowerFixedFieldTower.baseFrobenius,
      D.frobeniusPowerOfDegreeOne_coe] using hpow
  have hpowerZ : D.frobeniusPowerSum A KR.field L hLK σ.1 n (J (N w)) =
      n • J (N w) :=
    D.frobeniusPowerSum_eq_nsmul_of_fixed A KR.field L hLK
      σ.1 n (J (N w)) hσfixedZ
  have hnormW' :
      J (N (fixedFieldInclusion A S E hSE (uSraw - powerS))) =
        n • J (N w) := by
    rw [← hwBarNorm, hnormWraw]
    have hwBarInclRaw : fixedFieldInclusion A T E hTE wBarraw = w := by
      apply Subtype.ext
      exact congrArg Subtype.val hwBarIncl
    rw [hwBarInclRaw, hpowerZ]
  have hpowerSIncl := D.fixedFieldPowerSum_inclusion A KR L hLK σ
    φ.1 hφσ n ySraw
  have huSIncl : fixedFieldInclusion A S E hSE uSraw = u := by
    apply Subtype.ext
    change uSraw.1 = u.1
    exact huSval
  refine ⟨yS, ?_⟩
  have h := hnormW'
  simp only [map_sub] at h
  have hpowerSInclRaw : fixedFieldInclusion A S E hSE powerS =
      D.frobeniusPowerSum A KR.field L hLK φ.1 n
        (fixedFieldInclusion A S E hSE ySraw) := hpowerSIncl
  rw [huSIncl, hpowerSInclRaw] at h
  calc
    J (N u) = n • J (N w) +
        J (N (D.frobeniusPowerSum A KR.field L hLK φ.1 n
          (fixedFieldInclusion A S E hSE ySraw))) :=
      sub_eq_iff_eq_add.mp h
    _ = _ := add_comm _ _


/-- The universal norm-descent lemma, finite target step.  After placing the finite support in a
common finite Galois overfield, the descended unit is a norm from every
prescribed finite intermediate field. -/
theorem universalNormDescent_mem_finiteUnitNormRange
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hφ : D.frobeniusExponent
      (K.toFiniteResidueAbstractField D) L hLK φ = 1)
    {ι : Type*} (s : Finset ι)
    (τ : ι →
      (D.extensionNormalizedDegreeContinuous
        (K.toFiniteResidueAbstractField D) L hLK).toMonoidHom.ker)
    (u : v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (uᵢ : ι → v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (hstar : D.frobeniusQuotientAction A K.field L hLK φ.1 u.1 - u.1 =
      ∑ i ∈ s,
        (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i).1 -
          (uᵢ i).1))
    (aK : v.unitAddSubgroup K)
    (haK :
      letI : Finite
          ((D.maximalUnramifiedField K.field).toSubgroup ⧸
            extensionSubgroup (D.maximalUnramifiedField K.field)
              (D.maximalUnramifiedField L)
              (D.maximalUnramifiedField_mono hLK)) :=
        D.maximalUnramifiedExtension_finite K.field L hLK
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField_le K.field) aK.1 =
        relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u.1)
    (M : FiniteIntermediateField (D.maximalUnramifiedField L) K.field) :
    aK.1 ∈ v.finiteIntermediateUnitNormRange
      (D.maximalUnramifiedField L) K M := by
  classical
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let KR := K.toFiniteResidueAbstractField D
  let I := D.maximalUnramifiedField K.field
  let E := D.maximalUnramifiedField L
  let hEI := D.maximalUnramifiedField_mono hLK
  let N := relativeNorm A I E hEI
  let J := fixedFieldInclusion A I E hEI
  let hEK := D.maximalUnramifiedField_le_of_le hLK
  let hEnormal : (extensionSubgroup K.field E hEK).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L hLK
  rcases u.2 with ⟨Mu, uMu, huMu⟩
  let ιs := {i : ι // i ∈ s}
  have huᵢsupport (j : ιs) := (uᵢ j.1).2
  choose Mi uMi huMi using huᵢsupport
  let ML : FiniteIntermediateField E K.field :=
    { field := L
      above := D.maximalUnramifiedField_le L
      below := hLK
      finite := hLfinite }
  let B₀ := M.compositum ML
  let B := B₀.compositum Mu
  obtain ⟨Q, hQB, hQMi⟩ :=
    FiniteIntermediateField.exists_common_compositum B
      (Finset.univ : Finset ιs) Mi
  let P := Q.galoisRefinement
  let hPQ : P.field.toSubgroup ≤ Q.field.toSubgroup :=
    Q.galoisRefinement_le_field
  let hPB : P.field.toSubgroup ≤ B.field.toSubgroup := hPQ.trans hQB
  let hPM : P.field.toSubgroup ≤ M.field.toSubgroup :=
    hPB.trans ((B₀.compositum_le_left Mu).trans (M.compositum_le_left ML))
  let hPL : P.field.toSubgroup ≤ L.toSubgroup :=
    hPB.trans ((B₀.compositum_le_left Mu).trans (M.compositum_le_right ML))
  let hPMu : P.field.toSubgroup ≤ Mu.field.toSubgroup :=
    hPB.trans (B₀.compositum_le_right Mu)
  let hPMi (j : ιs) : P.field.toSubgroup ≤ (Mi j).field.toSubgroup :=
    hPQ.trans (hQMi j (Finset.mem_univ j))
  let hPfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) := P.finite
  let hPnormal : (extensionSubgroup K.field P.field P.below).Normal :=
    FiniteIntermediateField.galoisRefinement_normal Q
  let n := P.quotientCard
  have hn : 0 < n := P.quotientCard_pos
  let σ := D.frobeniusPowerOfDegreeOne KR L hLK φ hφ n hn
  let σn := D.frobeniusPowerOfDegreeOne KR L hLK φ hφ (n * n)
    (Nat.mul_pos hn hn)
  let S := D.frobeniusFixedField KR L hLK σ
  let T := D.frobeniusFixedField KR L hLK σn
  let hSP : S.toSubgroup ≤ P.field.toSubgroup :=
    D.frobeniusPowerFixedField_le_finiteField KR L hLK P φ hφ
  let hSK := D.frobeniusFixedField_le KR L hLK σ
  let hTK := D.frobeniusFixedField_le KR L hLK σn
  let hTS := D.frobeniusPowerFixedField_le KR L hLK φ hφ n n hn hn
  let hTE := D.fieldInertia_le_frobeniusFixedField KR L hLK σn
  let hSE := D.fieldInertia_le_frobeniusFixedField KR L hLK σ
  let hSfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let hTabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) T (le_baseField T)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σn
  let hTSfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S T hTS) :=
    D.frobeniusPowerFixedField_finite KR L hLK φ hφ n n hn hn
  let hTSnormal : (extensionSubgroup S T hTS).Normal :=
    D.frobeniusPowerFixedField_normal KR L hLK φ hφ n n hn hn
  let : (extensionSubgroup S T hTS).Normal := hTSnormal
  let ambientExtension : FiniteGaloisSubextension KR.field :=
    { field := L
      below := hLK
      normal := hLnormal
      finite := hLfinite }
  let powerTower : DegreeData.FrobeniusPowerFixedFieldTower D :=
    { ambientBase := KR
      ambient := ambientExtension
      frobenius := φ
      exponent_one := hφ
      n := n
      n_pos := hn
      baseAbsoluteFinite := hSabsolute
      fieldAbsoluteFinite := hTabsolute
      relativeFinite := hTSfinite }
  let fixedTower := powerTower.toFrobeniusFixedFieldTower
  let SF := fixedTower.base
  let TF := fixedTower.field
  obtain ⟨uS, huStransport⟩ := v.exists_unit_lift_of_field_le
    (Mu.toFiniteAbstractField K) SF (hSP.trans hPMu) uMu
  have hlift (j : ιs) := v.exists_unit_lift_of_field_le
    ((Mi j).toFiniteAbstractField K) SF (hSP.trans (hPMi j)) (uMi j)
  choose uᵢS huᵢStransport using hlift
  have huSval : uS.1.1 = u.1.1 := huStransport.trans (congrArg Subtype.val huMu)
  have huᵢSval (j : ιs) : (uᵢS j).1.1 = (uᵢ j.1).1.1 :=
    (huᵢStransport j).trans (congrArg Subtype.val (huMi j))
  have hstarVal :
      (D.frobeniusQuotientAction A K.field L hLK φ.1 u.1).1 - u.1.1 =
        ∑ i ∈ s,
          ((D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i).1).1 -
            (uᵢ i).1.1) := by
    have h := congrArg
      (AddSubgroup.subtype
        (ambientFixedAddSubgroup A (D.maximalUnramifiedField L))) hstar
    rw [map_sub, map_sum] at h
    exact h
  simp_rw [D.frobeniusQuotientAction_coe_out] at hstarVal
  have hstarS :
      A.ρ (Quotient.out φ.1).1 uS.1.1 - uS.1.1 =
        ∑ j : ιs,
          (A.ρ (Quotient.out (τ j.1).1).1 (uᵢS j).1.1 - (uᵢS j).1.1) := by
    rw [huSval]
    calc
      A.ρ (Quotient.out φ.1).1 u.1.1 - u.1.1 =
          ∑ i ∈ s,
            (A.ρ (Quotient.out (τ i).1).1 (uᵢ i).1.1 - (uᵢ i).1.1) := hstarVal
      _ = ∑ j : ιs,
            (A.ρ (Quotient.out (τ j.1).1).1 (uᵢ j.1).1.1 -
              (uᵢ j.1).1.1) :=
        Finset.sum_subtype s (fun _ => Iff.rfl) _
      _ = _ := by simp_rw [huᵢSval]
  let τs : ιs →
      (D.extensionNormalizedDegreeContinuous KR L hLK).toMonoidHom.ker :=
    fun j => τ j.1
  have hφσn : φ.1 * σn.1 = σn.1 * φ.1 :=
    powerTower.frobenius_commute_field
  have hτσ (j : ιs) : (τs j).1 * (φ.1 ^ n) =
      (φ.1 ^ n) * (τs j).1 := by
    exact (D.quotientPower_card_commutes_degreeZero KR L hLK P hPL
      φ.1 (τs j).1 (τs j).2).symm
  have hτσn (j : ιs) : (τs j).1 * (φ.1 ^ (n * n)) =
      (φ.1 ^ (n * n)) * (τs j).1 := by
    have hcomm : Commute (τs j).1 (φ.1 ^ n) := hτσ j
    simpa only [pow_mul] using (hcomm.pow_right n).eq
  have hσσn : σ.1 * σn.1 = σn.1 * σ.1 :=
    fixedTower.commute
  obtain ⟨uBar, uBarᵢ, yBar, huBar, huBarᵢ, hyBar⟩ :=
    v.universalNormDescent_fixedTower_solution hAxiom powerTower
      (Finset.univ : Finset ιs) τs hτσ hτσn uS uᵢS hstarS
  let uBarE := fixedFieldInclusion A T E hTE uBar.1
  let uBarᵢE := fun j : ιs => fixedFieldInclusion A T E hTE (uBarᵢ j).1
  let yBarE := fixedFieldInclusion A T E hTE yBar.1
  let φnyBarE := D.frobeniusPowerSum A K.field L hLK φ.1 n yBarE
  let w := uBarE - φnyBarE
  have hstarW := v.universalNormDescent_correctedEquation KR L hLK σ σn
    (Finset.univ : Finset ιs) φ.1 hφσn (fun j => (τs j).1) hτσn
      hσσn n rfl uBar uBarᵢ yBar hyBar
  have huBarEmem : uBarE ∈ v.infiniteUnitAddSubgroup E K hEK :=
    v.fixedFieldInclusion_unit_mem_infinite E K TF hTE hTK hEK uBar
  have hyBarEmem : yBarE ∈ v.infiniteUnitAddSubgroup E K hEK :=
    v.fixedFieldInclusion_unit_mem_infinite E K TF hTE hTK hEK yBar
  have hφnyMem : φnyBarE ∈ v.infiniteUnitAddSubgroup E K hEK :=
    v.frobeniusPowerSum_mem_infiniteUnit_universalNormDescent K L hLK φ.1 n yBarE hyBarEmem
  have hwMem : w ∈ v.infiniteUnitAddSubgroup E K hEK :=
    (v.infiniteUnitAddSubgroup E K hEK).sub_mem huBarEmem hφnyMem
  have hfixedZ := D.maximalUnramifiedNorm_fixed_of_hstar A KR L hLK
    (Finset.univ : Finset ιs) φ.1 τs w uBarᵢE hstarW
  obtain ⟨zK, hzK⟩ :=
    v.descend_maximalUnramifiedNorm_unit K L hLK φ hφ w hwMem hfixedZ
  obtain ⟨yS, hnormRelationE⟩ := v.powerTower_corrected_norm_relation
    powerTower uS uBar yBar u.1 huBar huSval hfixedZ
  let ySraw : ambientFixedAddSubgroup A S := yS.1
  have hlemma53 := (D.frobeniusNormIdentities A KR L hLK φ σ hφ ySraw).1
  have hbaseRelation :
      aK.1 = relativeNorm A K.field S hSK ySraw + n • zK.1 := by
    apply Subtype.ext
    have haKval := congrArg Subtype.val haK
    have hzKval := congrArg Subtype.val hzK
    have hrelVal := congrArg Subtype.val hnormRelationE
    have h53' := hlemma53.symm
    rw [D.frobeniusExponent_powerOfDegreeOne KR L hLK φ hφ n hn] at h53'
    change aK.1.1 =
      (relativeNorm A K.field S hSK ySraw).1 + n • zK.1.1
    change aK.1.1 = (N u.1).1 at haKval
    change zK.1.1 = (N w).1 at hzKval
    change (N u.1).1 =
      (N (D.frobeniusPowerSum A K.field L hLK φ.1 n
        (fixedFieldInclusion A S E hSE ySraw))).1 + n • (N w).1 at hrelVal
    rw [haKval, hrelVal, ← hzKval]
    exact congrArg (fun z => z + n • zK.1.1) h53'
  let : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field SF.field hSK) := by
    change Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK)
    exact hSfinite
  exact v.finiteUnitNormRange_of_norm_add_quotientCard_smul E K M P hPM
    SF hSP hSK aK zK yS hbaseRelation

/-- **The universal norm-descent lemma.**  A finite Frobenius coboundary
relation for an infinite-level unit forces its maximal-unramified norm to
descend to a `K`-unit which is a unit norm from every finite intermediate
field. -/
theorem universalNormDescent
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hφ : D.frobeniusExponent
      (K.toFiniteResidueAbstractField D) L hLK φ = 1)
    {ι : Type*} (s : Finset ι)
    (τ : ι →
      (D.extensionNormalizedDegreeContinuous
        (K.toFiniteResidueAbstractField D) L hLK).toMonoidHom.ker)
    (u : v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (uᵢ : ι → v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (hstar : D.frobeniusQuotientAction A K.field L hLK φ.1 u.1 - u.1 =
      ∑ i ∈ s,
        (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i).1 -
          (uᵢ i).1)) :
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
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) u.1 ∧
      aK.1 ∈ v.infiniteUnitNormSubgroup (D.maximalUnramifiedField L) K := by
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  obtain ⟨aK, haK⟩ := v.universalNormDescent_endpoint_descent K L hLK φ hφ
    s τ u uᵢ hstar
  refine ⟨aK, haK, ?_⟩
  rw [v.mem_infiniteUnitNormSubgroup_iff]
  intro M
  exact v.universalNormDescent_mem_finiteUnitNormRange hAxiom K L hLK φ hφ
    s τ u uᵢ hstar aK haK M

end ValuationData

end
end ClassFormation
