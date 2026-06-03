/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
import Mathlib.RingTheory.NonUnitalSubsemiring.Defs

/-!
# LeanPool.BrauerGroupNew.Mathlib.RingTheory.NonUnitalSubsemiring.Defs

Imported Lean Pool material for
`LeanPool.BrauerGroupNew.Mathlib.RingTheory.NonUnitalSubsemiring.Defs`.
-/

variable {R : Type*} [NonUnitalSemiring R]

@[simp]
lemma NonUnitalSubsemiring.carrier_eq_coe (S : NonUnitalSubsemiring R) : S.carrier = S := rfl
