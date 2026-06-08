/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.RingTheory.Congruence.Defs

/-!
# Ring congruence induction compatibility

This file restores the upstream eliminator name used by the Brauer group port.
-/

namespace RingCon

variable {R : Type*} [Ring R]

@[elab_as_elim]
lemma quot_ind (r : RingCon R) {motive : r.Quotient → Prop}
    (basic : ∀ x : R, motive (r.mk' x)) : ∀ x : r.Quotient, motive x := by
  intro x
  induction x using Quotient.inductionOn' with
  | h x => exact basic x

end RingCon
