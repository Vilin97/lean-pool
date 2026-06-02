/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# LeanPool.BrauerGroupNew.Mathlib.LinearAlgebra.LinearIndependent.Defs

Imported Lean Pool material for
`LeanPool.BrauerGroupNew.Mathlib.LinearAlgebra.LinearIndependent.Defs`.
-/

variable {ι R M : Type*} {v : ι → M} [Semiring R] [AddCommMonoid M] [Module R M]

-- TODO: Replace `linearIndependent_iff_finset_linearIndependent`
lemma linearIndependent_iff_linearIndepOn_finset :
    LinearIndependent R v ↔ ∀ s : Finset ι, LinearIndepOn R v s :=
  linearIndependent_iff_finset_linearIndependent
