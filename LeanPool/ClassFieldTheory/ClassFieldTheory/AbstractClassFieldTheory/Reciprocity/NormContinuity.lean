/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormTopology
/-!
# Continuity of norms

For a finite extension `L / K`, the base change to `L` of a finite Galois
extension `M / K` is finite Galois.  Norm transitivity then sends its norm
subgroup into , providing the key continuity input.
-/

noncomputable section

namespace ClassFormation

open ClassFormation CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The norm from a finite extension is continuous for the norm topologies
of its source and target (continuity of norms). -/
theorem normTopology_norm_continuous
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    IsNormContinuous A L K (relativeNorm A K L hLK) := by
  unfold IsNormContinuous
  let : TopologicalSpace (ambientFixedAddSubgroup A L) := normTopology A L
  let : TopologicalSpace (ambientFixedAddSubgroup A K) := normTopology A K
  let : IsTopologicalAddGroup (ambientFixedAddSubgroup A L) :=
    (normFilterBasis A L).isTopologicalAddGroup
  let : IsTopologicalAddGroup (ambientFixedAddSubgroup A K) :=
    (normFilterBasis A K).isTopologicalAddGroup
  apply continuous_of_continuousAt_zero (relativeNorm A K L hLK)
  rw [ContinuousAt, map_zero]
  rw [(normFilterBasis A L).nhds_zero_hasBasis.tendsto_iff
    (normFilterBasis A K).nhds_zero_hasBasis]
  intro U hU
  rcases hU with ⟨M, rfl⟩
  let P : ClosedSubgroup G := L ⊓ M.field
  let ML : FiniteGaloisSubextension L := M.baseChange L hLK
  let hMKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M.field M.below) := M.finite
  refine ⟨(FiniteGaloisSubextension.normSubgroup A ML : Set (ambientFixedAddSubgroup A L)),
    ⟨ML, rfl⟩, ?_⟩
  intro x hx
  change x ∈ FiniteGaloisSubextension.normSubgroup A ML at hx
  rcases hx with ⟨a, rfl⟩
  let hMLfinite : Finite
      (L.toSubgroup ⧸ extensionSubgroup L P inf_le_left) := ML.finite
  let hPKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K P (inf_le_left.trans hLK)) :=
    FiniteGaloisSubextension.finite_extension_trans inf_le_left hLK
  let hPMfinite : Finite
      (M.field.toSubgroup ⧸
        extensionSubgroup M.field P inf_le_right) :=
    FiniteGaloisSubextension.finite_extension_over_intermediate
      (inf_le_left.trans hLK) M.below inf_le_right
  let TM : DegreeData.FiniteTower G := {
    top := P
    middle := M.field
    base := K
    top_le_middle := inf_le_right
    middle_le_base := M.below
    finiteTopQuotient := hPMfinite
    finiteBaseQuotient := hMKfinite }
  let TL : DegreeData.FiniteTower G := {
    top := P
    middle := L
    base := K
    top_le_middle := inf_le_left
    middle_le_base := hLK
    finiteTopQuotient := hMLfinite
    finiteBaseQuotient := hLKfinite }
  change relativeNorm A K L hLK
      (relativeNorm A L P inf_le_left a) ∈ FiniteGaloisSubextension.normSubgroup A M
  refine ⟨relativeNorm A M.field P inf_le_right a, ?_⟩
  calc
    relativeNorm A K M.field M.below
        (relativeNorm A M.field P inf_le_right a) =
      relativeNorm A K P (inf_le_right.trans M.below) a :=
        TM.norm_trans_apply A a
    _ = relativeNorm A K P (inf_le_left.trans hLK) a := by
      congr 2
    _ = relativeNorm A K L hLK
      (relativeNorm A L P inf_le_left a) :=
      (TL.norm_trans_apply A a).symm

end ClassFormation
