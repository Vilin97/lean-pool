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
  one_smul _ := Subtype.ext <| mul_one _
  mul_smul _ _ _ := Subtype.ext <| (mul_assoc _ _ _).symm
  smul_zero _ := Subtype.ext <| zero_mul _
  zero_smul _ := Subtype.ext <| mul_zero _
  add_smul _ _ _ := Subtype.ext <| mul_add _ _ _
  smul_add _ _ _ := Subtype.ext <| add_mul _ _ _

end Ring

end TwoSidedIdeal
