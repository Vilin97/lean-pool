/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitDescent

/-! # Infinite Unit Norm Subgroup -/
universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Infinite unit norm subgroups

This module defines the finite-level and infinite unit norm ranges, proves
their tower compatibility, and compares them with the ambient norm
subgroups.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The image `N_{M/K} U_M` from one finite intermediate field. -/
def finiteIntermediateUnitNormRange
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) := by
  letI : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) :=
    M.finite
  exact ((relativeNorm A K.field M.field M.below).comp
    (v.unitAddSubgroup (M.toFiniteAbstractField K)).subtype).range

/-- A unit norm obtained from a finite overfield of `M` already lies in the
unit norm range attached to `M`, by transitivity of the actual norm. -/
theorem mem_finiteIntermediateUnitNormRange_of_overfield
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M P : FiniteIntermediateField E K.field)
    (hPM : P.field.toSubgroup ≤ M.field.toSubgroup)
    [hPfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below)]
    (uP : v.unitAddSubgroup (P.toFiniteAbstractField K))
    (aK : ambientFixedAddSubgroup A K.field)
    (haK : relativeNorm A K.field P.field P.below uP.1 = aK) :
    aK ∈ v.finiteIntermediateUnitNormRange E K M := by
  let hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) :=
    M.finite
  let hPMfinite : Finite
      (M.field.toSubgroup ⧸ extensionSubgroup M.field P.field hPM) :=
    FiniteIntermediateField.finite_extension_of_le P.below M.below hPM
  let : Finite
      ((M.toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup (M.toFiniteAbstractField K).field P.field hPM) := by
    change Finite
      (M.field.toSubgroup ⧸ extensionSubgroup M.field P.field hPM)
    exact hPMfinite
  let EMP : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      P.field (M.toFiniteAbstractField K) hPM
  let uM : v.unitAddSubgroup (M.toFiniteAbstractField K) :=
    by
      simpa [EMP, FiniteAbstractFieldExtension.ofInclusion] using
        v.finiteUnitNorm EMP uP
  let T : DegreeData.FiniteTower G := {
    top := P.field
    middle := M.field
    base := K.field
    top_le_middle := hPM
    middle_le_base := M.below
    finiteTopQuotient := hPMfinite
    finiteBaseQuotient := hMfinite }
  simp only [finiteIntermediateUnitNormRange]
  change aK ∈ ((relativeNorm A K.field M.field M.below).comp
    (v.unitAddSubgroup (M.toFiniteAbstractField K)).subtype).range
  refine ⟨uM, ?_⟩
  change relativeNorm A K.field M.field M.below
      (relativeNorm A M.field P.field hPM uP.1) = aK
  calc
    _ = relativeNorm A K.field P.field (hPM.trans M.below) uP.1 :=
      T.norm_trans_apply A uP.1
    _ = relativeNorm A K.field P.field P.below uP.1 := by rfl
    _ = aK := haK

/-- The universal unit norm group
`N_{E/K} U_E = ⋂_M N_{M/K} U_M`. -/
def infiniteUnitNormSubgroup
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) :=
  ⨅ M : FiniteIntermediateField E K.field,
    v.finiteIntermediateUnitNormRange E K M

/--
Characterizes `a ∈ v.infiniteUnitNormSubgroup E K` by the equivalent condition `∀ M :
FiniteIntermediateField E K.field, a ∈ v.finiteIntermediateUnitNormRange E K M`.
-/
@[simp]
theorem mem_infiniteUnitNormSubgroup_iff
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    a ∈ v.infiniteUnitNormSubgroup E K ↔
      ∀ M : FiniteIntermediateField E K.field,
        a ∈ v.finiteIntermediateUnitNormRange E K M := by
  simp [infiniteUnitNormSubgroup]

/--
Proves the bound `v.finiteIntermediateUnitNormRange E K M ≤ finiteIntermediateNormRange A E
K.field M`.
-/
theorem finiteIntermediateUnitNormRange_le_normRange
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) :
    v.finiteIntermediateUnitNormRange E K M ≤
      finiteIntermediateNormRange A E K.field M := by
  let hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) :=
    M.finite
  change
    ((relativeNorm A K.field M.field M.below).comp
      (v.unitAddSubgroup (M.toFiniteAbstractField K)).subtype).range ≤
        (relativeNorm A K.field M.field M.below).range
  rintro a ⟨u, hu⟩
  refine ⟨u.1, ?_⟩
  change relativeNorm A K.field M.field M.below u.1 = a at hu
  exact hu

/-- Proves the bound `v.infiniteUnitNormSubgroup E K ≤ infiniteNormSubgroup A E K.field`. -/
theorem infiniteUnitNormSubgroup_le_normSubgroup
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G) :
    v.infiniteUnitNormSubgroup E K ≤ infiniteNormSubgroup A E K.field := by
  intro a ha
  rw [mem_infiniteNormSubgroup_iff]
  intro M
  exact v.finiteIntermediateUnitNormRange_le_normRange E K M
    ((v.mem_infiniteUnitNormSubgroup_iff E K a).1 ha M)

end ValuationData
end

end ClassFormation
