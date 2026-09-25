/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence

/-! # Finite Intermediate Compositum -/

@[expose] public section
namespace ClassFormation

open CyclicCohomology

/-!
# Finite intermediate fields: composita and absolute finiteness

These are the finite-stage closure facts used in the proof of the universal norm-descent lemma.
  The compositum of two finite intermediate fields is their
intersection on the Galois-group side.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- The compositum of two finite intermediate fields of `E / K`. -/
def compositum {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    FiniteIntermediateField E K where
  field := M.field ⊓ N.field
  above := fun x hx => ⟨M.above hx, N.above hx⟩
  below := (inf_le_left :
    (M.field ⊓ N.field).toSubgroup ≤ M.field.toSubgroup).trans M.below
  finite := by
    let : Finite
        (K.toSubgroup ⧸ extensionSubgroup K N.field N.below) := N.finite
    exact M.compositumWith_finite_over_base N.field N.below

/-- Proves the bound `(M.compositum N).field.toSubgroup ≤ M.field.toSubgroup`. -/
theorem compositum_le_left {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    (M.compositum N).field.toSubgroup ≤ M.field.toSubgroup :=
  inf_le_left

/-- Proves the bound `(M.compositum N).field.toSubgroup ≤ N.field.toSubgroup`. -/
theorem compositum_le_right {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    (M.compositum N).field.toSubgroup ≤ N.field.toSubgroup :=
  inf_le_right

/-- A finite intermediate field over a finite abstract base field is itself
finite over the global base field. -/
theorem absoluteFinite {E K : ClosedSubgroup G}
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))]
    (M : FiniteIntermediateField E K) :
    Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M.field (le_baseField M.field)) := by
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M.field M.below) := M.finite
  exact relativeTowerQuotientFinite (baseField G) K M.field M.below
    (le_baseField K)

end FiniteIntermediateField

end
end ClassFormation
