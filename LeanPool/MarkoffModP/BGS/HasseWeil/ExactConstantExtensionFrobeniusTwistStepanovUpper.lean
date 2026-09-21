/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistDegree
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistBoundedError
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistGenus
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannLowerFromGenus
import LeanPool.MarkoffModP.BGS.HasseWeil.GeneralSquareFieldStepanovCount

/-!
# A uniform Stepanov upper bound for exact-constant Frobenius twists

For one fixed exact extension of the constants, the Frobenius-twist fixed
fields have a common finite-place Riemann budget and exact constant field.
When the ground constant field is a square, the intrinsic one-point
Stepanov theorem therefore applies to every twist with the same numerical
budget.  The degree theorem for the twists replaces the residual
function-field degree term by the degree of the original field.

This is the uniform upper estimate used in the fixed-field averaging route to
Hasse--Weil.  It does not require a separate genus-invariance hypothesis: the
common Riemann budget is the exact input consumed by the Stepanov theorem.
-/

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier


variable (K C N S : Type*)
  [Field K] [Fintype K]
  [Field C] [Fintype C] [DecidableEq C] [Algebra K C]
  [DecidableEq (RatFunc C)]
  [Field N] [Algebra (RatFunc C) N]
  [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N] [IsGalois (RatFunc C) N]
  [Field S] [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [Finite S]

local instance twistStepanovBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance twistStepanovBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10000) twistStepanovFieldDecidableEq
    (F : Type*) [Field F] : DecidableEq F := Classical.decEq _

local instance (priority := 10001) twistStepanovRatFuncDecidableEq
    (F : Type*) [Field F] : DecidableEq (RatFunc F) := Classical.decEq _

/-- A single Stepanov budget gives the square-field rational-place upper
bound for every Frobenius-twist fixed field.  The final degree term is uniform:
it is the degree of the original function field `N / C(X)`.

The divisibility condition is exactly the one used to prove that every twist
has the same degree as `N`; in the Stichtenoth construction it is ensured by
the chosen constant-extension degree. -/
theorem exists_uniform_frobeniusTwistField_squareFieldStepanov_budget
    (hcard : Fintype.card C = (Fintype.card K) ^ 2)
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    let T := ExactConstantExtension C N S
    letI : Field T := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) T :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) T := Algebra.toSMul
    letI : Module (RatFunc C) T := Algebra.toModule
    letI : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
    letI : MulAction (RatFunc C) T := DistribMulAction.toMulAction
    ∃ budget : ℕ,
      ∀ (g : N ≃ₐ[RatFunc C] N),
        let F := exactConstantExtensionFrobeniusTwistField
          C (RatFunc C) N S hExact g
        letI : Algebra (RatFunc C) F :=
          SubalgebraClass.toAlgebra F.toSubalgebra
        letI : SMul (RatFunc C) F := Algebra.toSMul
        letI : Module (RatFunc C) F := Algebra.toModule
        letI : FiniteDimensional (RatFunc C) F :=
          finiteDimensional_frobeniusTwistField_over_ratFunc
            C N S hExact g
        letI : Algebra.IsSeparable (RatFunc C) F :=
          isSeparable_frobeniusTwistField_over_ratFunc
            C N S hExact g
        (budget + 1) * (budget + 2) ≤ Fintype.card K →
          finiteExtensionRationalPlaceCount C F ≤
            Fintype.card C + (2 * budget + 1) * Fintype.card K +
              Module.finrank (RatFunc C) N := by
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  letI : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  obtain ⟨budget, hbudget⟩ :=
    exists_common_frobeniusTwistField_exactConstants_and_riemann_budget
      C N S hExact
  refine ⟨budget, ?_⟩
  intro g
  dsimp only
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  letI : Algebra (RatFunc C) F :=
    SubalgebraClass.toAlgebra F.toSubalgebra
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc
      C N S hExact g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc
      C N S hExact g
  letI : Algebra C F := Algebra.restrictScalars C (RatFunc C) F
  intro hlarge
  have hstepanov :=
    finiteExtensionRationalPlaceCount_le_squareFieldStepanov_of_finitePlaceRiemann
      K C F budget hcard (hbudget g).1 (fun Q poleOrder => by
        have h := (hbudget g).2 Q.1 poleOrder
        have hdeg : finiteExtensionPlaceDegree C F (.inl Q.1) = 1 := Q.2
        change poleOrder * finiteExtensionPlaceDegree C F (.inl Q.1) + 1 ≤ _ at h
        rw [hdeg, Nat.mul_one] at h
        exact h) hlarge
  calc
    finiteExtensionRationalPlaceCount C F ≤
        Fintype.card C + (2 * budget + 1) * Fintype.card K +
          Module.finrank (RatFunc C) F := hstepanov
    _ = Fintype.card C + (2 * budget + 1) * Fintype.card K +
          Module.finrank (RatFunc C) N := by
      rw [finrank_frobeniusTwistField_over_ratFunc_eq_original
        C N S hExact g hdiv]

/-- The uniform twist estimate with the intrinsic genus of the original
field as its fixed budget.  Unlike the existential compatibility theorem
above, every constant in this statement is independent of the auxiliary
constant extension `S`. -/
theorem frobeniusTwistFieldRationalPlaceCount_le_squareField_of_genus
    (hcard : Fintype.card C = (Fintype.card K) ^ 2)
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S)
    (g : N ≃ₐ[RatFunc C] N)
    (hlarge : (FunctionField.genus C N + 1) *
        (FunctionField.genus C N + 2) ≤ Fintype.card K) :
    frobeniusTwistFieldRationalPlaceCount C S N hExact g ≤
      Fintype.card C + (2 * FunctionField.genus C N + 1) *
        Fintype.card K + Module.finrank (RatFunc C) N := by
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  letI : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  letI : Algebra (RatFunc C) F := SubalgebraClass.toAlgebra F.toSubalgebra
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra C F := Algebra.restrictScalars C (RatFunc C) F
  letI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hExactF : algebraicClosure C F =
      (⊥ : IntermediateField C F) :=
    exactConstantExtensionFrobeniusTwistField_algebraicClosure_eq_bot
      C (RatFunc C) N S hExact g
  letI : FunctionField.IsFullConstantField C F :=
    (FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot C F).2
      hExactF
  have hgenus : FunctionField.genus C F = FunctionField.genus C N :=
    genus_frobeniusTwistField_eq_original C S N hExact hdiv g
  have hriemann : ∀ (Q : FiniteExtensionRationalFinitePlace C F) m,
      m + 1 ≤ Module.finrank C
          (finiteExtensionOnePointRiemannSpace C F (.inl Q.1) m) +
        FunctionField.genus C N := by
    intro Q m
    have h := finiteExtension_onePoint_riemann_lower_of_genus
      C F (.inl Q.1) m
    simpa only [Q.2, Nat.mul_one, hgenus] using h
  have hstepanov :=
    finiteExtensionRationalPlaceCount_le_squareFieldStepanov_of_finitePlaceRiemann
      K C F (FunctionField.genus C N) hcard hExactF hriemann hlarge
  rw [← frobeniusTwistFieldRationalPlaceCount_eq_finiteExtensionRationalPlaceCount
    C S N hExact g] at hstepanov
  calc
    frobeniusTwistFieldRationalPlaceCount C S N hExact g ≤
        Fintype.card C + (2 * FunctionField.genus C N + 1) *
          Fintype.card K + Module.finrank (RatFunc C) F := hstepanov
    _ = Fintype.card C + (2 * FunctionField.genus C N + 1) *
          Fintype.card K + Module.finrank (RatFunc C) N := by
      rw [finrank_frobeniusTwistField_over_ratFunc_eq_original
        C N S hExact g hdiv]

/-- Combining the genus-uniform Stepanov upper bound with the bounded
complete-place average gives a two-sided estimate for every rational-base
twist.  All constants shown here are independent of `S`. -/
theorem abs_frobeniusTwistFieldRationalPlaceError_le_squareField_of_genus
    (hcard : Fintype.card C = (Fintype.card K) ^ 2)
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S)
    (hlarge : (FunctionField.genus C N + 1) *
        (FunctionField.genus C N + 2) ≤ Fintype.card K)
    (g : N ≃ₐ[RatFunc C] N) :
    |(frobeniusTwistFieldRationalPlaceCount C S N hExact g : ℝ) -
        (Nat.card C : ℝ) - 1| ≤
      (Nat.card (N ≃ₐ[RatFunc C] N) : ℝ) *
          Module.finrank (RatFunc C) N +
        (Nat.card (N ≃ₐ[RatFunc C] N) - 1 : ℕ) *
          (((2 * FunctionField.genus C N + 1) * Fintype.card K +
            Module.finrank (RatFunc C) N : ℕ) : ℝ) := by
  let B : ℝ :=
    (((2 * FunctionField.genus C N + 1) * Fintype.card K +
      Module.finrank (RatFunc C) N : ℕ) : ℝ)
  apply abs_frobeniusTwistFieldRationalPlaceError_le_of_uniform_upper
    C S N hExact hdiv g B
  · dsimp only [B]
    positivity
  · intro τ
    have hnat :=
      frobeniusTwistFieldRationalPlaceCount_le_squareField_of_genus
        K C N S hcard hExact hdiv τ hlarge
    have hreal :
        (frobeniusTwistFieldRationalPlaceCount C S N hExact τ : ℝ) ≤
          (Fintype.card C : ℝ) +
            (((2 * FunctionField.genus C N + 1) * Fintype.card K +
              Module.finrank (RatFunc C) N : ℕ) : ℝ) := by
      have hnat' :
          frobeniusTwistFieldRationalPlaceCount C S N hExact τ ≤
            Fintype.card C +
              ((2 * FunctionField.genus C N + 1) * Fintype.card K +
                Module.finrank (RatFunc C) N) := by
        simpa only [Nat.add_assoc] using hnat
      exact_mod_cast hnat'
    dsimp only [B]
    rw [Nat.card_eq_fintype_card]
    linarith

end

end BGS.HasseWeil
