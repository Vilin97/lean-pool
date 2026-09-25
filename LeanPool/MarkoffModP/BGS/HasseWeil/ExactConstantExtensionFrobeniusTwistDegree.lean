/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistRiemannLower
public import LeanPool.MarkoffModP.BGS.HasseWeil.GeneralSquareFieldStepanovCount

/-!
# Degrees of exact-constant Frobenius twists

For an exact constant extension `S \otimes[C] N`, every Frobenius-twist
fixed field has the same degree over `C(X)` as the original function field
`N`.  This file records the rational-function specialization used by the
Hasse--Weil averaging argument and combines it with the general bound on
rational places above infinity.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

variable (C N S : Type*) [Field C] [Fintype C] [DecidableEq C]
  [DecidableEq (RatFunc C)]
  [Field N] [Algebra (RatFunc C) N] [Algebra C N]
  [IsScalarTower C (RatFunc C) N]
  [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Field S] [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [Finite S]

omit [DecidableEq C] [DecidableEq (RatFunc C)]
  [Algebra.IsSeparable (RatFunc C) N] in
/-- A Frobenius-twist fixed field has the same `C(X)`-degree as the original
function field. -/
theorem finrank_frobeniusTwistField_over_ratFunc_eq_original
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N)
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    Module.finrank (RatFunc C)
        (exactConstantExtensionFrobeniusTwistField
          C (RatFunc C) N S hExact g) =
      Module.finrank (RatFunc C) N := by
  exact finrank_frobeniusTwistField_over_base
    C (RatFunc C) N S hExact g hdiv

/-- The number of rational infinity places on a Frobenius-twist fixed field
is bounded uniformly by the degree of the original function field. -/
theorem rationalInfinityPlace_card_frobeniusTwistField_le_original_finrank
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N)
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let F := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact g
    Nat.card (FiniteExtensionRationalInfinityPlace C F) ≤
      Module.finrank (RatFunc C) N := by
  let := exactConstantExtensionField C N S hExact
  let := exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  let : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  let : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  calc
    Nat.card (FiniteExtensionRationalInfinityPlace C F) ≤
        Module.finrank (RatFunc C) F :=
      rationalInfinityPlace_card_le_finrank C F
    _ = Module.finrank (RatFunc C) N :=
      finrank_frobeniusTwistField_over_ratFunc_eq_original
        C N S hExact g hdiv

end

end BGS.HasseWeil
