/-
Copyright (c) 2026 Matevz Miščič, Maša Žaucer, Job Petrovčič. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matevz Miščič, Maša Žaucer, Job Petrovčič
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# Promoting a non-unital ring with a unit element to a unital ring

If a non-unital ring `R` has an element `e` that is both a left and a right
identity, then `R` admits a (unital) ring structure with `1 = e`.
-/

namespace LeanPool.ArtinWedderburn

variable {R : Type*} [NonUnitalRing R]
variable (e : R)

/-- Designate `e` as the `1` element when building a unital `Ring` structure
on `R` via `Ring.ofMinimalAxioms`. -/
@[reducible]
def e_one : One R := ⟨e⟩

variable (is_left_unit : ∀ x : R, e * x = x)
variable (is_right_unit : ∀ x : R, x * e = x)

-- if we have a nonunital ring where one element is the left and right unit simultaneously
-- then it is a regular ring
/-- Promote a non-unital ring `R` with a two-sided identity `e` to a unital `Ring R`. -/
@[reducible]
def non_unital_w_e_is_ring : Ring R :=
  @Ring.ofMinimalAxioms R (by exact inferInstance) (by exact inferInstance) (by exact inferInstance)
    (by exact inferInstance) (by exact e_one e)
    (by intro a b c; rw [add_assoc])
    (by intro a; exact AddZeroClass.zero_add a)
    (by intro a; exact neg_add_cancel a)
    (by intro a b c; exact mul_assoc a b c)
    is_left_unit is_right_unit
    (by intro a b c; exact LeftDistribClass.left_distrib a b c)
    (by intro a b c; exact RightDistribClass.right_distrib a b c)

end LeanPool.ArtinWedderburn
