/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.Algebra.Ring.Opposite
import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Two-sided ideal compatibility helpers

This file restores upstream scalar-action helpers for two-sided ideals.
-/

namespace TwoSidedIdeal

variable {R : Type*}

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing R] {I : TwoSidedIdeal R} {x : R}

lemma smul_mem (r : R) (hx : x ∈ I) : r • x ∈ I := by
  exact I.mul_mem_left r x hx

end NonUnitalNonAssocRing

section Ring

variable [Ring R] {I : TwoSidedIdeal R}

instance instModuleMulOppositeSubtypeMemLeanPool : Module Rᵐᵒᵖ I where
  smul r x := ⟨x.1 * r.unop, I.mul_mem_right _ _ x.2⟩
  one_smul x := by ext; simp
  mul_smul x y z := by ext; simp [mul_assoc]
  smul_zero x := by ext; simp
  zero_smul x := by ext; simp
  add_smul x y z := by ext; simp [left_distrib]
  smul_add x y z := by ext; simp [right_distrib]

end Ring

end TwoSidedIdeal
