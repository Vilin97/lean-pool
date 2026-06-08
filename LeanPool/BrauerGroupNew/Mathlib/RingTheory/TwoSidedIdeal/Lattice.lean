/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
import Mathlib.RingTheory.TwoSidedIdeal.Lattice

/-!
# LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Lattice

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Lattice`.
-/

namespace TwoSidedIdeal
variable {R : Type*} [NonUnitalNonAssocRing R] {I J : TwoSidedIdeal R} {x : R}

@[simp] lemma ringCon_inj : I.ringCon = J.ringCon ↔ I = J := ringCon_injective.eq_iff

@[simp] lemma ringCon_eq_top : I.ringCon = ⊤ ↔ I = ⊤ := by rw [← top_ringCon, ringCon_inj]

end TwoSidedIdeal
