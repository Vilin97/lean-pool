/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
import Mathlib.RingTheory.NonUnitalSubring.Defs

/-!
# LeanPool.BrauerGroupNew.Mathlib.RingTheory.NonUnitalSubring.Defs

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Mathlib.RingTheory.NonUnitalSubring.Defs`.
-/

variable {R : Type*} [NonUnitalRing R]

@[simp] lemma NonUnitalSubring.carrier_eq_coe (S : NonUnitalSubring R) : S.carrier = S := rfl
