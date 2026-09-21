/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.FieldTheory.Galois.Basic

/-!
# A common factorial degree for Galois groups in a field tower

For `R ⊆ L ⊆ N`, the order of `Gal(N/L)` is at most `[N:R]`.
Consequently every such intermediate Galois-group order divides the
factorial of the top degree.  This supplies one auxiliary constant-extension
degree that works simultaneously for the rational base and the original
compositum in the Frobenius-twist argument.
-/

namespace BGS.HasseWeil

noncomputable section

/-- The Galois group over the bottom field itself divides the factorial of
the extension degree. -/
theorem natCard_aut_dvd_finrank_factorial
    (R N : Type*) [Field R] [Field N] [Algebra R N]
    [FiniteDimensional R N] [IsGalois R N] :
    Nat.card (N ≃ₐ[R] N) ∣ (Module.finrank R N).factorial := by
  rw [IsGalois.card_aut_eq_finrank]
  exact Nat.dvd_factorial Module.finrank_pos le_rfl

variable (R L N : Type*) [Field R] [Field L] [Field N]
  [Algebra R L] [Algebra L N] [Algebra R N]
  [IsScalarTower R L N]
  [FiniteDimensional R L] [FiniteDimensional L N]
  [IsGalois L N]

/-- The intermediate Galois group order is bounded by the degree over the
bottom field. -/
theorem natCard_aut_le_finrank_of_tower :
    Nat.card (N ≃ₐ[L] N) ≤ Module.finrank R N := by
  rw [IsGalois.card_aut_eq_finrank]
  calc
    Module.finrank L N ≤
        Module.finrank R L * Module.finrank L N :=
      Nat.le_mul_of_pos_left _ Module.finrank_pos
    _ = Module.finrank R N := Module.finrank_mul_finrank R L N

/-- A single factorial of the top degree is divisible by the order of every
intermediate Galois group in the tower. -/
theorem natCard_aut_dvd_finrank_factorial_of_tower :
    Nat.card (N ≃ₐ[L] N) ∣ (Module.finrank R N).factorial := by
  exact Nat.dvd_factorial
    (Nat.card_pos : 0 < Nat.card (N ≃ₐ[L] N))
    (natCard_aut_le_finrank_of_tower R L N)

end

end BGS.HasseWeil
