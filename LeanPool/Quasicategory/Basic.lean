/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.CategoryTheory.SmallObject.Basic
import LeanPool.Quasicategory.MorphismProperty
import LeanPool.Quasicategory.Terminal
import LeanPool.Quasicategory.TopCatModelCategory.SSet.SmallObject

universe u

namespace SSet

open CategoryTheory Simplicial MorphismProperty

inductive BoundaryInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk n : BoundaryInclusion ∂Δ[n].ι

/-- The class of all boundary inclusions. -/
def boundaryInclusions : MorphismProperty SSet := fun _ _ p ↦ BoundaryInclusion p

lemma boundaryInclusions_le_monomorphisms : boundaryInclusions ≤ monomorphisms SSet :=
  fun _ _ _ ⟨_⟩ ↦ monomorphisms.infer_property _

inductive InnerHornInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (h0 : 0 < i) (hn : i < Fin.last (n+2)) :
    InnerHornInclusion Λ[n + 2, i].ι

/-- The class of all inner horn inclusions. -/
def innerHornInclusions : MorphismProperty SSet := fun _ _ p ↦ InnerHornInclusion p

/-- alternate definition for compatibility -/
def innerHornInclusions_ofHoms : MorphismProperty SSet :=
  ⨆ n, ofHoms (fun (j : { i : Fin (n + 3) // 0 < i ∧ i < Fin.last (n + 2) }) ↦ Λ[n + 2, j.1].ι)

lemma innerHornInclusions_ofHoms_eq : innerHornInclusions_ofHoms = innerHornInclusions := by
  apply le_antisymm
  · intro _ _ _ ⟨_, h⟩
    simp at h
    obtain ⟨⟨_, h⟩, hw⟩ := h
    obtain ⟨⟨i, ⟨h0, hn⟩⟩⟩ := h.2 hw
    exact .mk h0 hn
  · intro _ _ f ⟨h0, hn⟩
    simp_rw [innerHornInclusions_ofHoms, iSup_iff, ofHoms_iff]
    exact ⟨_, ⟨⟨_, ⟨h0, hn⟩⟩, rfl⟩⟩

abbrev trivialFibration := boundaryInclusions.rlp

abbrev innerFibration := innerHornInclusions.rlp

abbrev innerAnodyne := innerFibration.llp

attribute [local instance] Cardinal.fact_isRegular_aleph0

attribute [local instance] Cardinal.aleph0_isRegular
  Cardinal.orderbot_aleph0_ord_to_type

instance isCardinalForSmallObjectArgument_innerHornInclusions :
    innerHornInclusions.{u}.IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} where
  hasIterationOfShape := by infer_instance
  preservesColimit i hi f hf := by
    simp only [innerHornInclusions, iSup_iff] at hi
    cases hi with
    | mk n i =>
    infer_instance
  isSmall := by
    rw [← innerHornInclusions_ofHoms_eq, innerHornInclusions_ofHoms]
    infer_instance

instance : HasSmallObjectArgument.{u} innerHornInclusions.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, inferInstance⟩

lemma innerAnodyne_eq_saturation_innerHornInclusions :
    innerAnodyne.{u} = saturation.{u} innerHornInclusions :=
  llp_rlp_eq_saturation

lemma innerFibration_eq_rlp_innerAnodyne :
    innerFibration = innerAnodyne.rlp := by
  rw [innerAnodyne_eq_saturation_innerHornInclusions, ← llp_rlp_eq_saturation, rlp_llp_rlp]
