/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianLeftJustification
public import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianReducedBridge
public import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianSurjectivity

/-!
# The banana Jacobian presentation

This closes the kernel calculation in Proposition 2.14.  The reduction
algorithm supplies a paper-reduced representative modulo the displayed
relations, while reduced-coordinate kernel triviality forces that
representative to vanish.  The first isomorphism theorem then identifies the
displayed quotient with the range of the graph-level divisor-class map.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- **Proposition 2.14, relation-lattice equality.**  The diagonal and
strand-length relations displayed in the paper generate every relation of
the banana coordinate map to divisor classes. -/
theorem bananaCoordinateRelations_eq_displayedRelations
    {g : ℕ} (B : Banana g) :
    bananaCoordinateRelations B = bananaDisplayedRelations B := by
  apply le_antisymm
  · intro a ha
    obtain ⟨p, hpReduced, hReduction⟩ :=
      exists_paperReducedPositionCoordinates_mod_displayedRelations B a
    have hReductionKernel :
        a - bananaPositionCoordinates B p ∈ bananaCoordinateRelations B :=
      bananaDisplayedRelations_le_coordinateRelations B hReduction
    have hPositionKernel :
        bananaPositionCoordinates B p ∈ bananaCoordinateRelations B := by
      have hDifference := (bananaCoordinateRelations B).sub_mem
        ha hReductionKernel
      convert hDifference using 1
      abel
    have hPositionZero :=
      bananaPositionCoordinates_eq_zero_of_paperReduced_of_mem_relations
        B p hpReduced hPositionKernel
    have hReduction' : a ∈ bananaDisplayedRelations B := by
      convert hReduction using 1
      rw [hPositionZero]
      simp
    exact hReduction'
  · exact bananaDisplayedRelations_le_coordinateRelations B

/-- The divisor-class image of the banana coordinate map.  By the
degree-zero surjectivity theorem, this is the graph Jacobian component; using
the range here avoids introducing a second, redundant model of that group. -/
abbrev bananaCoordinateClassRange {g : ℕ} (B : Banana g) :=
  AddMonoidHom.mrange (bananaCoordinateClassHom B)

/-- The displayed-quotient map to the coordinate class range. -/
def bananaDisplayedClassRangeHom {g : ℕ} (B : Banana g) :
    ((Fin (g + 1) → ℤ) ⧸ bananaDisplayedRelations B) →+
      bananaCoordinateClassRange B :=
  QuotientAddGroup.lift (bananaDisplayedRelations B)
    ((bananaCoordinateClassHom B).codRestrict
      (bananaCoordinateClassRange B) (fun a => ⟨a, rfl⟩)) (by
        intro a ha
        rw [AddMonoidHom.mem_ker]
        apply Subtype.ext
        change bananaCoordinateClassHom B a = 0
        change a ∈ bananaCoordinateRelations B
        rw [bananaCoordinateRelations_eq_displayedRelations B]
        exact ha)

theorem bananaDisplayedClassRangeHom_bijective
    {g : ℕ} (B : Banana g) :
    Function.Bijective (bananaDisplayedClassRangeHom B) := by
  constructor
  · intro x
    refine QuotientAddGroup.induction_on x ?_
    intro a y
    refine QuotientAddGroup.induction_on y ?_
    intro b hxy
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    rw [← bananaCoordinateRelations_eq_displayedRelations B,
      bananaCoordinateRelations, AddMonoidHom.mem_ker]
    have hValues := congrArg Subtype.val hxy
    change bananaCoordinateClassHom B a = bananaCoordinateClassHom B b at hValues
    rw [map_sub, hValues, sub_self]
  · intro c
    obtain ⟨c, a, rfl⟩ := c
    exact ⟨QuotientAddGroup.mk' (bananaDisplayedRelations B) a, rfl⟩

/-- **Proposition 2.14, quotient form.**  Coordinates modulo the paper's
displayed lattice are additively isomorphic to the degree-zero divisor-class
range of the banana graph. -/
noncomputable def bananaDisplayedQuotientEquivClassRange
    {g : ℕ} (B : Banana g) :
    ((Fin (g + 1) → ℤ) ⧸ bananaDisplayedRelations B) ≃+
      bananaCoordinateClassRange B :=
  AddEquiv.ofBijective (bananaDisplayedClassRangeHom B)
    (bananaDisplayedClassRangeHom_bijective B)

@[simp] theorem bananaDisplayedQuotientEquivClassRange_mk
    {g : ℕ} (B : Banana g) (a : Fin (g + 1) → ℤ) :
    bananaDisplayedQuotientEquivClassRange B
        (QuotientAddGroup.mk' (bananaDisplayedRelations B) a) =
      ⟨bananaCoordinateClassHom B a, ⟨a, rfl⟩⟩ := by
  rfl

end Bananas
