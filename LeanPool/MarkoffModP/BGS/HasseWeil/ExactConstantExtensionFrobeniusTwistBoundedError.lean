/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistRationalPlaceAverage

/-!
# Two-sided Frobenius-twist errors from the bounded average

The exact average of the infinity-place contributions is not needed to obtain
a two-sided estimate for an individual Frobenius twist.  The already-proved
bounded aggregate error, together with a common one-sided Stepanov bound for
all twists, suffices by finite averaging.

This is the direct function-field specialization of
`abs_le_of_uniform_upper_and_abs_sum_le`.
-/

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open scoped BigOperators

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [IsGalois (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance boundedErrorBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance boundedErrorBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A common upper bound for all Frobenius-twist point-count errors gives a
two-sided bound for every twist.  The additive term is uniform in the
auxiliary constant extension `S`: it depends only on the original Galois
group and the degree of `N / C(X)`.

Consequently, the exact infinity-place average is not a prerequisite for the
two-sided estimate used in a Hasse--Weil argument. -/
theorem abs_frobeniusTwistFieldRationalPlaceError_le_of_uniform_upper
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S)
    (g : N ≃ₐ[RatFunc C] N) (B : ℝ)
    (hB : 0 ≤ B)
    (hupper : ∀ τ : N ≃ₐ[RatFunc C] N,
      (frobeniusTwistFieldRationalPlaceCount C S N hExact τ : ℝ) -
          (Nat.card C : ℝ) - 1 ≤ B) :
    |(frobeniusTwistFieldRationalPlaceCount C S N hExact g : ℝ) -
        (Nat.card C : ℝ) - 1| ≤
      (Nat.card (N ≃ₐ[RatFunc C] N) : ℝ) *
          Module.finrank (RatFunc C) N +
        (Nat.card (N ≃ₐ[RatFunc C] N) - 1 : ℕ) * B := by
  classical
  have hsum := abs_sum_frobeniusTwistFieldRationalPlaceError_le
    C S N hExact hdiv
  have hbound := abs_le_of_uniform_upper_and_abs_sum_le
    (fun τ : N ≃ₐ[RatFunc C] N ↦
      (frobeniusTwistFieldRationalPlaceCount C S N hExact τ : ℝ) -
        (Nat.card C : ℝ) - 1)
    g
    ((Nat.card (N ≃ₐ[RatFunc C] N) : ℝ) *
      Module.finrank (RatFunc C) N)
    B hB hupper hsum
  simpa only [Nat.card_eq_fintype_card] using hbound

end

end BGS.HasseWeil
