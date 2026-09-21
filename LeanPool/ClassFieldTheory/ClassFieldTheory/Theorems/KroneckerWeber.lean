/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.NumberTheory.Cyclotomic.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.Algebra.AbelianGaloisEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.Core
/-!
# Kronecker--Weber theorem

Let `L` be a number field that is finite abelian over `ℚ`.  Kronecker--Weber
asserts that `L` is contained in a cyclotomic extension: there is a positive
integer `n` and a `ℚ`-algebra embedding of `L` into `ℚ(ζₙ)`.  The positivity
condition excludes the degenerate order-zero cyclotomic construction.
-/

namespace ClassFieldTheory

universe u

/-- **Kronecker--Weber.** Every finite abelian extension of `ℚ` embeds in a
cyclotomic field of positive order. -/
theorem kroneckerWeber
    (L : Type u) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) := by
  let : Small.{0} L := numberField_small L
  let S := Shrink.{0} L
  let : NumberField S := numberField_shrink L
  let e : S ≃ₐ[ℚ] L := (Shrink.ringEquiv L).toRatAlgEquiv
  let : IsAbelianGalois ℚ S := by
    apply isAbelianGalois_of_equiv_equiv
      (f := RingEquiv.refl ℚ) (g := e.symm.toRingEquiv)
    apply RingHom.ext
    intro x
    change algebraMap ℚ S x = e.symm (algebraMap ℚ L x)
    exact (e.symm.commutes x).symm
  obtain ⟨n, hn, ⟨i⟩⟩ :=
    KroneckerWeber.exists_cyclotomicEmbedding S
  exact ⟨n, hn, ⟨i.comp e.symm.toAlgHom⟩⟩

end ClassFieldTheory
