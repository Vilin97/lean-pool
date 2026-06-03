/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Subalgebra.Basic

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Subalgebra.Basic`.
-/

namespace Subalgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {L S T U : Subalgebra R A}

lemma le_centralizer_self : L ≤ centralizer R L ↔ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := forall₂_comm
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {S T U : Subalgebra R A}

@[simp] lemma inclusion_comp_inclusion (hST : S ≤ T) (hTU : T ≤ U) :
    (inclusion hTU).comp (inclusion hST) = inclusion (hST.trans hTU) := rfl

end Subalgebra
