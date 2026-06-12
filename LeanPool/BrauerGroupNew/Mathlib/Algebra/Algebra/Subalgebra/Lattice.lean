/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Subalgebra.Lattice

Imported Lean Pool material for
`LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Subalgebra.Lattice`.
-/

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

lemma Subalgebra.map_centralizer_le_centralizer_image (s : Set A) (f : A →ₐ[R] B) :
    (centralizer _ s).map f ≤ centralizer _ (f '' s) := by
  rintro - ⟨g, hg, rfl⟩ - ⟨h, hh, rfl⟩
  dsimp only [RingHom.coe_coe]
  rw [← map_mul, ← map_mul, hg h hh]
