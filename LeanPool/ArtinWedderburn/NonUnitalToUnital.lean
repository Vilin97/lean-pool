/-
Copyright (c) 2026 Matevz Miščič, Maša Žaucer, Job Petrovčič. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matevz Miščič, Maša Žaucer, Job Petrovčič
-/
import Mathlib.Algebra.Ring.Basic

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
def eOne : One R := ⟨e⟩

variable (is_left_unit : ∀ x : R, e * x = x)
variable (is_right_unit : ∀ x : R, x * e = x)

-- if we have a nonunital ring where one element is the left and right unit simultaneously
-- then it is a regular ring
/-- Promote a non-unital ring `R` with a two-sided identity `e` to a unital `Ring R`. -/
@[reducible]
def nonUnitalWEIsRing : Ring R :=
  { ‹NonUnitalRing R›, eOne e with
    one_mul := is_left_unit
    mul_one := is_right_unit }

end LeanPool.ArtinWedderburn
