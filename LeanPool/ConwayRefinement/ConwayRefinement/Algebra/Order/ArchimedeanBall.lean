/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/

module

public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Convex Archimedean balls

Closed Archimedean balls are convex additive subgroups of the exponent group.
-/

public section

namespace FiniteArchimedeanClass

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

private theorem archimedeanClosedBall_ordConnected (c : ArchimedeanClass G) :
    (ArchimedeanClass.closedBallAddSubgroup c : Set G).OrdConnected := by
  constructor
  intro g hg h hh k hk
  change g ∈ ArchimedeanClass.closedBallAddSubgroup c at hg
  change h ∈ ArchimedeanClass.closedBallAddSubgroup c at hh
  change k ∈ ArchimedeanClass.closedBallAddSubgroup c
  rw [ArchimedeanClass.mem_closedBallAddSubgroup_iff] at hg hh ⊢
  exact (le_min hg hh).trans (ArchimedeanClass.min_le_mk_of_le_of_le hk.1 hk.2)

private theorem finiteClosedBall_eq_closedBall (c : FiniteArchimedeanClass G) :
    (FiniteArchimedeanClass.closedBallAddSubgroup c : Set G) =
      (ArchimedeanClass.closedBallAddSubgroup c.1 : Set G) := by
  ext g
  rw [SetLike.mem_coe, SetLike.mem_coe,
    FiniteArchimedeanClass.mem_closedBallAddSubgroup_iff,
    ArchimedeanClass.mem_closedBallAddSubgroup_iff]
  by_cases hg : g = 0
  · subst g
    simp
  · exact ⟨fun h ↦ h hg, fun h _ ↦ h⟩

/-- A finite Archimedean closed ball is order-connected. -/
theorem closedBall_ordConnected (c : FiniteArchimedeanClass G) :
    (closedBallAddSubgroup c : Set G).OrdConnected := by
  rw [finiteClosedBall_eq_closedBall]
  exact archimedeanClosedBall_ordConnected c.1

end FiniteArchimedeanClass
