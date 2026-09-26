/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.OpenFiniteIndexSubgroup
public import Mathlib.Topology.Algebra.Group.Units
/-!
# Open finite-index subgroups under a small field equivalence

The topological field equivalence between `K` and its small representative
induces an order equivalence between their open finite-index subgroups of
units.
-/

@[expose] public section

noncomputable
section

namespace LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The multiplicative groups of a local field and its small representative
are topologically isomorphic. -/
def shrinkUnitsContinuousMulEquiv :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    (Shrink.{0} K)ˣ ≃ₜ* Kˣ := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let h : Shrink.{0} K ≃ₜ K := (Shrink.homeomorph K).symm
  exact Units.mapContinuousMulEquiv {
    toMulEquiv := (Shrink.ringEquiv K).toMulEquiv
    continuous_toFun := h.continuous
    continuous_invFun := h.symm.continuous
  }

/-- Open finite-index subgroups correspond along the topological group
equivalence of unit groups. -/
def shrinkOpenFiniteIndexOrderIso :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    ClassFieldTheory.OpenFiniteIndexSubgroup (Shrink.{0} K) ≃o
      ClassFieldTheory.OpenFiniteIndexSubgroup K := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let e := shrinkUnitsContinuousMulEquiv K
  exact {
    toEquiv := {
      toFun := fun H => ⟨H.1.map e.toMulEquiv.toMonoidHom, by
        change IsOpen (e '' (H.1 : Set (Shrink.{0} K)ˣ))
        exact e.toHomeomorph.isOpenMap _ H.2.1, by
        let : H.1.FiniteIndex := H.2.2
        exact Subgroup.FiniteIndex.map_of_surjective H.1 e.surjective⟩
      invFun := fun H => ⟨H.1.map e.symm.toMulEquiv.toMonoidHom, by
        change IsOpen (e.symm '' (H.1 : Set Kˣ))
        exact e.symm.toHomeomorph.isOpenMap _ H.2.1, by
        let : H.1.FiniteIndex := H.2.2
        exact Subgroup.FiniteIndex.map_of_surjective H.1 e.symm.surjective⟩
      left_inv := by
        intro H
        apply Subtype.ext
        exact (e.toMulEquiv.mapSubgroup).symm_apply_apply H.1
      right_inv := by
        intro H
        apply Subtype.ext
        exact (e.toMulEquiv.mapSubgroup).apply_symm_apply H.1
    }
    map_rel_iff' := by
      intro H J
      change e '' (H.1 : Set (Shrink.{0} K)ˣ) ⊆
          e '' (J.1 : Set (Shrink.{0} K)ˣ) ↔
        (H.1 : Set (Shrink.{0} K)ˣ) ⊆ J.1
      exact Set.image_subset_image_iff e.injective
  }

end LocalFieldTheory
