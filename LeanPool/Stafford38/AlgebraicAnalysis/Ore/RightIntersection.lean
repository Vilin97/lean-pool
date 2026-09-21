/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic

/-!
# Finite intersections in a right Ore domain

Right ideals are represented as left modules over the opposite ring.  The
right Ore condition is kept as an explicit common-right-multiple hypothesis;
this module does not depend on a particular localization construction.
-/

namespace AlgebraicAnalysis.OreRightIntersection

variable {R : Type*} [Ring R] [IsDomain R]

/-- Every pair of nonzero elements has a nonzero common right multiple. -/
def RightOreCondition (R : Type*) [SemigroupWithZero R] : Prop :=
  ∀ ⦃a b : R⦄, a ≠ 0 → b ≠ 0 →
    ∃ x y : R, a * x = b * y ∧ a * x ≠ 0

/-- A finite family of nonzero right ideals has a nonzero common element.

The right ideals are left `Rᵐᵒᵖ`-submodules, so multiplying a member on the
right is expressed by scalar multiplication by `MulOpposite.op`. -/
theorem exists_mem_finset_rightIdeals
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (I : ι → Submodule Rᵐᵒᵖ R)
    (hI : ∀ i ∈ s, ∃ x ∈ I i, x ≠ 0)
    (hOre : RightOreCondition R) :
    ∃ x : R, x ≠ 0 ∧ ∀ i ∈ s, x ∈ I i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, one_ne_zero, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨m, hm0, hm⟩ := ih (fun j hj => hI j (Finset.mem_insert_of_mem hj))
      obtain ⟨n, hnI, hn0⟩ := hI i (Finset.mem_insert_self i s)
      obtain ⟨x, y, hxy, hmx0⟩ := hOre hm0 hn0
      refine ⟨m * x, hmx0, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        rw [hxy]
        exact (I i).smul_mem (MulOpposite.op y) hnI
      · exact (I j).smul_mem (MulOpposite.op x) (hm j hj)

/- The theorem is intentionally stated with an explicit nonzero witness;
   this is the usual meaning of ``the intersection is nonzero''. -/

end AlgebraicAnalysis.OreRightIntersection
