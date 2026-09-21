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
  let finiteFixedTower :=
    powerTower.toFiniteAmbientFrobeniusFixedFieldTower
  let SF := fixedTower.base
  let TF := fixedTower.field
  let hSMu : S.toSubgroup ≤ Mu.field.toSubgroup := hSP.trans hPMu
  let hSMufinite : Finite
      (Mu.field.toSubgroup ⧸ extensionSubgroup Mu.field S hSMu) :=
    FiniteIntermediateField.finite_extension_of_le hSK Mu.below hSMu
  let : Finite
      ((Mu.toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup (Mu.toFiniteAbstractField K).field S hSMu) := by
    change Finite
      (Mu.field.toSubgroup ⧸ extensionSubgroup Mu.field S hSMu)
    exact hSMufinite
  let ESMu : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      S (Mu.toFiniteAbstractField K) hSMu
  have hESMuField : ESMu.field = SF :=
    FiniteAbstractField.eq_of_field_eq _ _ rfl
  let uS : v.unitAddSubgroup SF :=
    hESMuField ▸ v.finiteUnitInclusion ESMu uMu
  let hSMi (j : ιs) : S.toSubgroup ≤ (Mi j).field.toSubgroup :=
    hSP.trans (hPMi j)
  let hSMifinite (j : ιs) : Finite
      ((Mi j).field.toSubgroup ⧸ extensionSubgroup (Mi j).field S (hSMi j)) :=
    FiniteIntermediateField.finite_extension_of_le hSK (Mi j).below (hSMi j)
  let hSMifiniteBundled (j : ιs) : Finite
      (((Mi j).toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup ((Mi j).toFiniteAbstractField K).field S (hSMi j)) := by
    change Finite
      ((Mi j).field.toSubgroup ⧸
        extensionSubgroup (Mi j).field S (hSMi j))
    exact hSMifinite j
  let ESMi (j : ιs) : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      S ((Mi j).toFiniteAbstractField K) (hSMi j)
  have hESMiField (j : ιs) : (ESMi j).field = SF :=
    FiniteAbstractField.eq_of_field_eq _ _ rfl
  let uᵢS (j : ιs) : v.unitAddSubgroup SF :=
    hESMiField j ▸ v.finiteUnitInclusion (ESMi j) (uMi j)
  have huSval : uS.1.1 = u.1.1 := by
    have huMuVal := congrArg Subtype.val huMu
    change uMu.1.1 = u.1.1 at huMuVal
    have huStransport : uS.1.1 = uMu.1.1 := by
      dsimp only [uS]
      cases hESMuField
      rfl
    calc
      uS.1.1 = uMu.1.1 := huStransport
      _ = u.1.1 := huMuVal
  have huᵢSval (j : ιs) : (uᵢS j).1.1 = (uᵢ j.1).1.1 := by
    have huMiVal := congrArg Subtype.val (huMi j)
    change (uMi j).1.1 = (uᵢ j.1).1.1 at huMiVal
    have huᵢStransport : (uᵢS j).1.1 = (uMi j).1.1 := by
      dsimp only [uᵢS]
      cases hESMiField j
      rfl
    calc
      (uᵢS j).1.1 = (uMi j).1.1 := huᵢStransport
      _ = (uᵢ j.1).1.1 := huMiVal
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
  have hφσ : φ.1 * σ.1 = σ.1 * φ.1 :=
    powerTower.frobenius_commute_base
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
  have huBarEmem : uBarE ∈ v.infiniteUnitAddSubgroup E K hEK := by
    let MT := D.frobeniusFixedIntermediateField KR L hLK σn
    have hTFMT : TF = MT.toFiniteAbstractField K :=
      FiniteAbstractField.eq_of_field_eq _ _ rfl
    let uBarMT : v.unitAddSubgroup (MT.toFiniteAbstractField K) :=
      hTFMT ▸ uBar
    refine ⟨MT, uBarMT, ?_⟩
    apply Subtype.ext
    change uBarMT.1.1 = uBar.1.1
    dsimp only [uBarMT]
  have hyBarEmem : yBarE ∈ v.infiniteUnitAddSubgroup E K hEK := by
    let MT := D.frobeniusFixedIntermediateField KR L hLK σn
    have hTFMT : TF = MT.toFiniteAbstractField K :=
      FiniteAbstractField.eq_of_field_eq _ _ rfl
    let yBarMT : v.unitAddSubgroup (MT.toFiniteAbstractField K) :=
      hTFMT ▸ yBar
    refine ⟨MT, yBarMT, ?_⟩
    apply Subtype.ext
    change yBarMT.1.1 = yBar.1.1
    dsimp only [yBarMT]
  have hφnyMem : φnyBarE ∈ v.infiniteUnitAddSubgroup E K hEK :=
    v.frobeniusPowerSum_mem_infiniteUnit_universalNormDescent K L hLK φ.1 n yBarE hyBarEmem
  have hwMem : w ∈ v.infiniteUnitAddSubgroup E K hEK :=
    (v.infiniteUnitAddSubgroup E K hEK).sub_mem huBarEmem hφnyMem
  have hfixedZ := D.maximalUnramifiedNorm_fixed_of_hstar A KR L hLK
    (Finset.univ : Finset ιs) φ.1 τs w uBarᵢE hstarW
  obtain ⟨zK, hzK⟩ :=
    v.descend_maximalUnramifiedNorm_unit K L hLK φ hφ w hwMem hfixedZ
  let powerT : ambientFixedAddSubgroup A T :=
    ∑ i : Fin n, D.frobeniusFixedFieldAction A KR L hLK σn
      (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar.1
  let powerTUnit : v.unitAddSubgroup TF :=
    ∑ i : Fin n, v.frobeniusFixedFieldUnitAction KR L hLK σn
      (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar
  have hsumUnit (f : Fin n → v.unitAddSubgroup TF) :
      ((∑ i, f i).1.1 : A.V) = ∑ i, (f i).1.1 := by
    calc
      ((∑ i, f i).1.1 : A.V) =
          (ambientFixedAddSubgroup A TF.field).subtype
            (∑ i, (v.unitAddSubgroup TF).subtype (f i)) := by
        exact congrArg (ambientFixedAddSubgroup A TF.field).subtype
          (map_sum (v.unitAddSubgroup TF).subtype f Finset.univ)
      _ = _ :=
        map_sum (ambientFixedAddSubgroup A TF.field).subtype
          (fun i => (v.unitAddSubgroup TF).subtype (f i)) Finset.univ
  have hsumAmbient (f : Fin n → ambientFixedAddSubgroup A T) :
      ((∑ i, f i).1 : A.V) = ∑ i, (f i).1 :=
    map_sum (ambientFixedAddSubgroup A T).subtype f Finset.univ
  have hpowerTUnit : powerTUnit.1 = powerT := by
    apply Subtype.ext
    calc
      (powerTUnit.1.1 : A.V) =
          ∑ i : Fin n, (v.frobeniusFixedFieldUnitAction KR L hLK σn
            (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar).1.1 :=
        hsumUnit (fun i : Fin n =>
          v.frobeniusFixedFieldUnitAction KR L hLK σn
            (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar)
      _ = ∑ i : Fin n,
          (D.frobeniusFixedFieldAction A KR L hLK σn
            (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar.1).1 := rfl
      _ = powerT.1 :=
        (hsumAmbient (fun i : Fin n =>
          D.frobeniusFixedFieldAction A KR L hLK σn
            (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar.1)).symm
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
  let uSraw : ambientFixedAddSubgroup A S :=
    ⟨uS.1.1, by
      intro g
      have hg : g.1 ∈ SF.field := by
        change g.1 ∈ D.frobeniusFixedField KR L hLK σ
        exact g.2
      exact uS.1.2 ⟨g.1, hg⟩⟩
  let ySraw : ambientFixedAddSubgroup A S :=
    ⟨yS.1.1, by
      intro g
      have hg : g.1 ∈ SF.field := by
        change g.1 ∈ D.frobeniusFixedField KR L hLK σ
        exact g.2
      exact yS.1.2 ⟨g.1, hg⟩⟩
  let uBarraw : ambientFixedAddSubgroup A T :=
    ⟨uBar.1.1, by
      intro g
      have hg : g.1 ∈
          (D.frobeniusFixedAbstractField KR L hLK σn).field := by
        change g.1 ∈ D.frobeniusFixedField KR L hLK σn
        exact g.2
      exact uBar.1.2 ⟨g.1, hg⟩⟩
  let wBarraw : ambientFixedAddSubgroup A T :=
    ⟨wBar.1.1, by
      intro g
      have hg : g.1 ∈ TF.field := by
        change g.1 ∈ D.frobeniusFixedField KR L hLK σn
        exact g.2
      exact wBar.1.2 ⟨g.1, hg⟩⟩
  let powerS : ambientFixedAddSubgroup A S :=
    ∑ i : Fin n, D.frobeniusFixedFieldAction A KR L hLK σ
      (φ.1 ^ i.1) (Commute.pow_left hφσ i.1) ySraw
  have hpowerNorm := D.fixedFieldPowerSum_relativeNorm A KR L hLK
    σ σn hTS φ.1 hφσ hφσn n yBar.1
  have huBarraw : relativeNorm A S T hTS uBarraw = uSraw := by
    apply Subtype.ext
    have h := congrArg Subtype.val huBar
    change
      (relativeNorm A S T hTS uBar.1).1 = uS.1.1 at h
    change
      (relativeNorm A S T hTS uBarraw).1 = uSraw.1
    exact h
  have hySraw : relativeNorm A S T hTS yBar.1 = ySraw := by
    apply Subtype.ext
    rfl
  have hpowerNormRaw : relativeNorm A S T hTS powerT = powerS := by
    simpa [powerT, powerS, S, T, σ, σn, hySraw] using hpowerNorm
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
      D.frobeniusPowerSum A K.field L hLK σ.1 n
        (J (N (fixedFieldInclusion A T E hTE wBarraw))) := by
    change
      J (N (fixedFieldInclusion A S E hSE
        (relativeNorm A S T hTS wBar.1))) =
      D.frobeniusPowerSum A K.field L hLK σ.1 n
        (J (N (fixedFieldInclusion A T E hTE wBar.1))) at hnormW
    exact hnormW
  have hσfixedZ : D.frobeniusQuotientAction A K.field L hLK σ.1 (J (N w)) =
      J (N w) := by
    let B := D.frobeniusQuotientRepresentation A K.field L hLK
    have hpow := rep_action_pow_fixed
      B φ.1 (J (N w)) hfixedZ n
    change D.frobeniusQuotientAction A K.field L hLK
      (φ.1 ^ n) (J (N w)) = J (N w) at hpow
    simpa only [σ, D.frobeniusPowerOfDegreeOne_coe] using hpow
  have hpowerZ : D.frobeniusPowerSum A K.field L hLK σ.1 n (J (N w)) =
      n • J (N w) :=
    D.frobeniusPowerSum_eq_nsmul_of_fixed A K.field L hLK
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
  have huSIncl : fixedFieldInclusion A S E hSE uSraw = u.1 := by
    apply Subtype.ext
    change uSraw.1 = u.1.1
    exact huSval
  have hnormRelationE :
      J (N u.1) =
        J (N (D.frobeniusPowerSum A K.field L hLK φ.1 n
          (fixedFieldInclusion A S E hSE ySraw))) + n • J (N w) := by
    have h := hnormW'
    simp only [map_sub] at h
    rw [huSIncl, hpowerSIncl] at h
    calc
      J (N u.1) = n • J (N w) +
          J (N (D.frobeniusPowerSum A K.field L hLK φ.1 n
            (fixedFieldInclusion A S E hSE ySraw))) :=
        sub_eq_iff_eq_add.mp h
      _ = _ := add_comm _ _
  have hlemma53 := (D.frobeniusNormIdentities A KR L hLK φ σ hφ ySraw).1
  have hbaseRelation :
      aK.1 = relativeNorm A K.field S hSK ySraw + n • zK.1 := by
    apply Subtype.ext
    have haKval := congrArg Subtype.val haK
    have hzKval := congrArg Subtype.val hzK
    have hrelVal := congrArg Subtype.val hnormRelationE
    have h53 := hlemma53
    have h53' :
        (N (D.frobeniusPowerSum A K.field L hLK φ.1 n
          (fixedFieldInclusion A S E hSE ySraw))).1 =
          (relativeNorm A K.field S hSK ySraw).1 := by
      have h53' := h53.symm
      have hσexp : D.frobeniusExponent KR L hLK σ = n :=
        D.frobeniusExponent_powerOfDegreeOne KR L hLK φ hφ n hn
      rw [hσexp] at h53'
      change
        (N (D.frobeniusPowerSum A K.field L hLK φ.1 n
          (fixedFieldInclusion A S E hSE ySraw))).1 =
          (relativeNorm A K.field S hSK ySraw).1 at h53'
      exact h53'
    change aK.1.1 =
      (relativeNorm A K.field S hSK ySraw).1 + n • zK.1.1
    change aK.1.1 = (N u.1).1 at haKval
    change zK.1.1 = (N w).1 at hzKval
    change (N u.1).1 =
      (N (D.frobeniusPowerSum A K.field L hLK φ.1 n
        (fixedFieldInclusion A S E hSE ySraw))).1 + n • (N w).1 at hrelVal
    rw [haKval, hrelVal, ← hzKval]
    rw [h53']
  let hPSfinite : Finite
      (P.field.toSubgroup ⧸ extensionSubgroup P.field S hSP) :=
    FiniteIntermediateField.finite_extension_of_le hSK P.below hSP
  let : Finite
      ((P.toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup (P.toFiniteAbstractField K).field S hSP) := by
    change Finite
      (P.field.toSubgroup ⧸ extensionSubgroup P.field S hSP)
    exact hPSfinite
  let EPS : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      S (P.toFiniteAbstractField K) hSP
  let yP : v.unitAddSubgroup (P.toFiniteAbstractField K) := by
    simpa [SF, EPS, FiniteAbstractFieldExtension.ofInclusion,
      DegreeData.frobeniusFixedAbstractField] using
        v.finiteUnitNorm EPS yS
  let EP := P.toFiniteAbstractFieldExtension K
  let zP : v.unitAddSubgroup (P.toFiniteAbstractField K) :=
    v.finiteUnitInclusion EP zK
  let aP : v.unitAddSubgroup (P.toFiniteAbstractField K) := yP + zP
  let FT : DegreeData.FiniteTower G := {
    top := S
    middle := P.field
    base := K.field
    top_le_middle := hSP
    middle_le_base := P.below
    finiteTopQuotient := hPSfinite
    finiteBaseQuotient := P.finite }
  have hnDegree : (EP.degree : ℕ) = n := by
    change (EP.toFiniteAbstractExtension.degree : ℕ) = n
    rw [EP.toFiniteAbstractExtension.degree_coe]
    change
      Nat.card
        (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) = n
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
        (relativeNorm A P.field S hSP yS.1) +
      relativeNorm A K.field P.field P.below
        (fixedFieldInclusion A K.field P.field P.below zK.1) = aK.1
    rw [hyTower]
    rw [hzNorm, hnDegree]
    exact hbaseRelation.symm
  exact v.mem_finiteIntermediateUnitNormRange_of_overfield
    E K M P hPM aP aK.1 haPnorm

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
