/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.CoreFrobeniusNorm

/-! # Finite Intermediate Field Compositum -/

@[expose] public section
universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Finite intermediate-field composita

This module records the quotient cardinal and common-compositum facts for
finite intermediate fields used by the norm-descent tower.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

section finiteIntermediateFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- Cardinality of the finite relative Galois quotient attached to a finite
intermediate field.  Recording the supplied `Finite` instance in the
definition lets later fixed-field constructions use the cardinality without
adding a second finiteness parameter. -/
noncomputable def quotientCard {E K : ClosedSubgroup G}
    (M : FiniteIntermediateField E K) : ℕ := by
  letI : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M.field M.below) := M.finite
  exact Nat.card
    (K.toSubgroup ⧸ extensionSubgroup K M.field M.below)

/-- The finite quotient used in the descent construction has positive cardinality. -/
theorem quotientCard_pos {E K : ClosedSubgroup G}
    (M : FiniteIntermediateField E K) : 0 < M.quotientCard := by
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M.field M.below) := M.finite
  exact Nat.card_pos

/-- An initial finite stage and finitely many further stages have a common
finite overfield.  This existential form avoids choosing an artificial
ordering of the finite family. -/
theorem exists_common_compositum {E K : ClosedSubgroup G} {ι : Type v}
    (M : FiniteIntermediateField E K) (s : Finset ι)
    (F : ι → FiniteIntermediateField E K) :
    ∃ P : FiniteIntermediateField E K,
      P.field.toSubgroup ≤ M.field.toSubgroup ∧
        ∀ i ∈ s, P.field.toSubgroup ≤ (F i).field.toSubgroup := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨M, le_rfl, by simp⟩
  | @insert i s hi ih =>
      rcases ih with ⟨P, hPM, hPF⟩
      let Q := P.compositum (F i)
      refine ⟨Q, (P.compositum_le_left (F i)).trans hPM, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with hji | hj
      · simpa [hji] using P.compositum_le_right (F i)
      · exact (P.compositum_le_left (F i)).trans (hPF j hj)

end FiniteIntermediateField

end finiteIntermediateFields

end

end ClassFormation
