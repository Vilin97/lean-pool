/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionIntermediateFrobeniusTwistRationalPlaceAverage
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistStepanovUpper
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionPlaceAlgEquiv
public import LeanPool.MarkoffModP.BGS.HasseWeil.GaloisTowerFactorialDegree

/-!
# A fixed-tower Hasse bound from intermediate Frobenius twists

The complete intermediate-base twist average is combined with the uniform
square-field Stepanov estimate for the corresponding rational-base twists.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open scoped BigOperators


variable (K C S N : Type*)
  [Field K] [Fintype K]
  [Field C] [Fintype C] [DecidableEq C] [Algebra K C]
  [Field S] [Finite S] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Field N] [Algebra (RatFunc C) N]
  [FiniteDimensional (RatFunc C) N] [IsGalois (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance intermediateHasseBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance intermediateHasseBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

variable (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))

section IntermediateBase

variable (L : Type*) [Field L]
  [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  [Algebra L N] [IsScalarTower (RatFunc C) L N]
  [FiniteDimensional L N] [IsGalois L N]

local instance intermediateHasseConstantAlgebra : Algebra C L :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) L).comp
    (algebraMap C (RatFunc C)))

local instance intermediateHasseConstantTower : IsScalarTower C L N := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  change algebraMap (RatFunc C) N (algebraMap C (RatFunc C) c) =
    algebraMap L N (algebraMap (RatFunc C) L (algebraMap C (RatFunc C) c))
  exact IsScalarTower.algebraMap_apply (RatFunc C) L N _

omit [Fintype C] [DecidableEq C] [Finite S] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional (RatFunc C) N] [IsGalois (RatFunc C) N]
  [FiniteDimensional C S] [IsGalois C S] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L] [FiniteDimensional L N] [IsGalois L N] in
private theorem intermediateHasseRatFuncBaseTower :
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) := Algebra.toModule
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    IsScalarTower (RatFunc C) L (ExactConstantExtension C N S) := by
  let T := ExactConstantExtension C N S
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let : Algebra N T := exactConstantExtensionAlgebra C N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  change (1 : S) ⊗ₜ algebraMap (RatFunc C) N x =
    (1 : S) ⊗ₜ algebraMap L N (algebraMap (RatFunc C) L x)
  congr 1
  exact IsScalarTower.algebraMap_apply (RatFunc C) L N x

/-- The complete point count of an intermediate-base twist agrees with that
of its rational-base incarnation. -/
theorem intermediateFrobeniusTwistFieldRationalPlaceCount_eq_rationalBase
    (g : N ≃ₐ[L] N) :
    intermediateFrobeniusTwistFieldRationalPlaceCount C S N hExact L g =
      frobeniusTwistFieldRationalPlaceCount C S N hExact
        (g.restrictScalars (RatFunc C)) := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  let : IsScalarTower (RatFunc C) L T :=
    intermediateHasseRatFuncBaseTower C S N L
  let Fₗ := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  let Fᵣ := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact (g.restrictScalars (RatFunc C))
  let : Algebra L Fₗ := SubalgebraClass.toAlgebra Fₗ.toSubalgebra
  let : SMul L Fₗ := Algebra.toSMul
  let : Module L Fₗ := Algebra.toModule
  let : Algebra (RatFunc C) Fₗ :=
    intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
  let : SMul (RatFunc C) Fₗ := Algebra.toSMul
  let : Module (RatFunc C) Fₗ := Algebra.toModule
  let : FiniteDimensional (RatFunc C) Fₗ :=
    finiteDimensional_intermediateFrobeniusTwistField_over_ratFunc
      C S N hExact L g
  let : Algebra.IsSeparable (RatFunc C) Fₗ :=
    isSeparable_intermediateFrobeniusTwistField_over_ratFunc
      C S N hExact L g
  let : Algebra (RatFunc C) Fᵣ := SubalgebraClass.toAlgebra Fᵣ.toSubalgebra
  let : SMul (RatFunc C) Fᵣ := Algebra.toSMul
  let : Module (RatFunc C) Fᵣ := Algebra.toModule
  let e :=
    intermediateFrobeniusTwistField_algEquiv_rationalBaseFrobeniusTwistField
      C S N hExact L g
  let : FiniteDimensional (RatFunc C) Fᵣ :=
    Module.Finite.equiv (e.toLinearEquiv : Fₗ ≃ₗ[RatFunc C] Fᵣ)
  let : Algebra.IsSeparable (RatFunc C) Fᵣ :=
    isSeparable_frobeniusTwistField_over_ratFunc
      C N S hExact (g.restrictScalars (RatFunc C))
  calc
    intermediateFrobeniusTwistFieldRationalPlaceCount C S N hExact L g =
        finiteExtensionRationalPlaceCount C Fₗ :=
      intermediateFrobeniusTwistFieldRationalPlaceCount_eq_finiteExtensionRationalPlaceCount
        C S N hExact L g
    _ = finiteExtensionRationalPlaceCount C Fᵣ :=
      finiteExtensionRationalPlaceCount_eq_of_algEquiv C Fₗ Fᵣ e
    _ = frobeniusTwistFieldRationalPlaceCount C S N hExact
        (g.restrictScalars (RatFunc C)) :=
      (frobeniusTwistFieldRationalPlaceCount_eq_finiteExtensionRationalPlaceCount
        C S N hExact (g.restrictScalars (RatFunc C))).symm

/-- The complete twist average and the pointwise Stepanov estimate give a
two-sided rational-place bound for the fixed intermediate field. -/
theorem abs_intermediateBaseRationalPlaceError_le_squareField_of_genus_exact
    (hcard : Fintype.card C = (Fintype.card K) ^ 2)
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))
    (hdivL : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S)
    (hdivBase : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S)
    (hlarge : (FunctionField.genus C N + 1) *
        (FunctionField.genus C N + 2) ≤ Fintype.card K) :
    |(finiteExtensionRationalPlaceCount C L : ℝ) -
        (Nat.card C : ℝ) - 1| ≤
      2 * (Module.finrank (RatFunc C) N : ℝ) ^ 2 +
        (Nat.card (N ≃ₐ[L] N) : ℝ) *
          ((Nat.card (N ≃ₐ[RatFunc C] N) : ℝ) *
              Module.finrank (RatFunc C) N +
            (Nat.card (N ≃ₐ[RatFunc C] N) - 1 : ℕ) *
              (((2 * FunctionField.genus C N + 1) * Fintype.card K +
                Module.finrank (RatFunc C) N : ℕ) : ℝ)) := by
  let : DecidableEq (N ≃ₐ[L] N) := Classical.decEq _
  let A : ℝ := 2 * (Module.finrank (RatFunc C) N : ℝ) ^ 2
  let B : ℝ :=
    (Nat.card (N ≃ₐ[RatFunc C] N) : ℝ) *
        Module.finrank (RatFunc C) N +
      (Nat.card (N ≃ₐ[RatFunc C] N) - 1 : ℕ) *
        (((2 * FunctionField.genus C N + 1) * Fintype.card K +
          Module.finrank (RatFunc C) N : ℕ) : ℝ)
  have haverage :
      |∑ g : N ≃ₐ[L] N,
          (intermediateFrobeniusTwistFieldRationalPlaceCount
            C S N hExact L g : ℝ) -
        (Fintype.card (N ≃ₐ[L] N) : ℝ) *
          finiteExtensionRationalPlaceCount C L| ≤ A := by
    simpa only [A, Nat.card_eq_fintype_card] using
      abs_sum_intermediateFrobeniusTwistFieldRationalPlaceCount_sub_card_mul_base_le
        C S N hExact L hdivL
  have hpointwise : ∀ g : N ≃ₐ[L] N,
      |(intermediateFrobeniusTwistFieldRationalPlaceCount
          C S N hExact L g : ℝ) - ((Nat.card C : ℝ) + 1)| ≤ B := by
    intro g
    rw [intermediateFrobeniusTwistFieldRationalPlaceCount_eq_rationalBase
      C S N hExact L g]
    have h :=
      abs_frobeniusTwistFieldRationalPlaceError_le_squareField_of_genus
        K C N S hcard hExact hdivBase hlarge
          (g.restrictScalars (RatFunc C))
    dsimp only [B]
    have hcenter :
        (frobeniusTwistFieldRationalPlaceCount C S N hExact
            (g.restrictScalars (RatFunc C)) : ℝ) -
              ((Nat.card C : ℝ) + 1) =
          (frobeniusTwistFieldRationalPlaceCount C S N hExact
            (g.restrictScalars (RatFunc C)) : ℝ) -
              (Nat.card C : ℝ) - 1 := by
      ring
    rw [hcenter]
    exact h
  have hbound := abs_base_sub_center_le_of_average_and_pointwise
    (x := fun g : N ≃ₐ[L] N ↦
      (intermediateFrobeniusTwistFieldRationalPlaceCount
        C S N hExact L g : ℝ))
    (base := (finiteExtensionRationalPlaceCount C L : ℝ))
    (center := (Nat.card C : ℝ) + 1) (A := A) (B := B)
    (by dsimp only [A]; positivity) (by dsimp only [B]; positivity)
    haverage hpointwise
  dsimp only [A, B] at hbound ⊢
  have hcardGal : Nat.card (N ≃ₐ[L] N) =
      Fintype.card (N ≃ₐ[L] N) := Nat.card_eq_fintype_card
  rw [← hcardGal] at hbound
  have hcenter :
      (finiteExtensionRationalPlaceCount C L : ℝ) -
          ((Nat.card C : ℝ) + 1) =
        (finiteExtensionRationalPlaceCount C L : ℝ) -
          (Nat.card C : ℝ) - 1 := by
    ring
  rw [hcenter] at hbound
  exact hbound

/-- A degree-only version of the fixed-tower estimate.  Both Galois-group
orders in the exact bound are at most the degree of the top field over
`C(X)`; this deliberately looser polynomial bound is the form used by the
normal-closure argument. -/
theorem abs_intermediateBaseRationalPlaceError_le_squareField_of_genus
    (hcard : Fintype.card C = (Fintype.card K) ^ 2)
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))
    (hdivL : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S)
    (hdivBase : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S)
    (hlarge : (FunctionField.genus C N + 1) *
        (FunctionField.genus C N + 2) ≤ Fintype.card K) :
    |(finiteExtensionRationalPlaceCount C L : ℝ) -
        (Nat.card C : ℝ) - 1| ≤
      2 * (Module.finrank (RatFunc C) N : ℝ) ^ 2 +
        2 * (Module.finrank (RatFunc C) N : ℝ) ^ 3 +
        (Module.finrank (RatFunc C) N : ℝ) ^ 2 *
          (((2 * FunctionField.genus C N + 1) * Fintype.card K : ℕ) : ℝ) := by
  have hbound :=
    abs_intermediateBaseRationalPlaceError_le_squareField_of_genus_exact
      K C S N L hcard hExact hdivL hdivBase hlarge
  have hL :
      (Nat.card (N ≃ₐ[L] N) : ℝ) ≤
        (Module.finrank (RatFunc C) N : ℝ) := by
    exact_mod_cast natCard_aut_le_finrank_of_tower (RatFunc C) L N
  have hD :
      (1 : ℝ) ≤ (Module.finrank (RatFunc C) N : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := RatFunc C) (M := N)
  rw [IsGalois.card_aut_eq_finrank (RatFunc C) N] at hbound
  have hsub :
      ((Module.finrank (RatFunc C) N - 1 : ℕ) : ℝ) ≤
        (Module.finrank (RatFunc C) N : ℝ) := by
    exact_mod_cast Nat.sub_le (Module.finrank (RatFunc C) N) 1
  have hsum :
      (((2 * FunctionField.genus C N + 1) * Fintype.card K +
          Module.finrank (RatFunc C) N : ℕ) : ℝ) =
        (((2 * FunctionField.genus C N + 1) * Fintype.card K : ℕ) : ℝ) +
          (Module.finrank (RatFunc C) N : ℝ) := by
    norm_num
  have hinnerNonneg :
      0 ≤
        (Module.finrank (RatFunc C) N : ℝ) *
            Module.finrank (RatFunc C) N +
          ((Module.finrank (RatFunc C) N - 1 : ℕ) : ℝ) *
            (((2 * FunctionField.genus C N + 1) * Fintype.card K +
              Module.finrank (RatFunc C) N : ℕ) : ℝ) := by
    positivity
  have hsumNonneg :
      0 ≤
        (((2 * FunctionField.genus C N + 1) * Fintype.card K : ℕ) : ℝ) +
          (Module.finrank (RatFunc C) N : ℝ) :=
    add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hinner :
      (Module.finrank (RatFunc C) N : ℝ) *
            Module.finrank (RatFunc C) N +
          ((Module.finrank (RatFunc C) N - 1 : ℕ) : ℝ) *
            (((2 * FunctionField.genus C N + 1) * Fintype.card K +
              Module.finrank (RatFunc C) N : ℕ) : ℝ) ≤
        (Module.finrank (RatFunc C) N : ℝ) *
            Module.finrank (RatFunc C) N +
          (Module.finrank (RatFunc C) N : ℝ) *
            ((((2 * FunctionField.genus C N + 1) * Fintype.card K : ℕ) : ℝ) +
              Module.finrank (RatFunc C) N) := by
    rw [hsum]
    exact add_le_add_right
      (mul_le_mul_of_nonneg_right hsub hsumNonneg) _
  have houter :
      (Nat.card (N ≃ₐ[L] N) : ℝ) *
          ((Module.finrank (RatFunc C) N : ℝ) *
              Module.finrank (RatFunc C) N +
            ((Module.finrank (RatFunc C) N - 1 : ℕ) : ℝ) *
              (((2 * FunctionField.genus C N + 1) * Fintype.card K +
                Module.finrank (RatFunc C) N : ℕ) : ℝ)) ≤
        2 * (Module.finrank (RatFunc C) N : ℝ) ^ 3 +
          (Module.finrank (RatFunc C) N : ℝ) ^ 2 *
            (((2 * FunctionField.genus C N + 1) * Fintype.card K : ℕ) : ℝ) := by
    calc
      (Nat.card (N ≃ₐ[L] N) : ℝ) *
            ((Module.finrank (RatFunc C) N : ℝ) *
                Module.finrank (RatFunc C) N +
              ((Module.finrank (RatFunc C) N - 1 : ℕ) : ℝ) *
                (((2 * FunctionField.genus C N + 1) * Fintype.card K +
                  Module.finrank (RatFunc C) N : ℕ) : ℝ)) ≤
          (Module.finrank (RatFunc C) N : ℝ) *
            ((Module.finrank (RatFunc C) N : ℝ) *
                Module.finrank (RatFunc C) N +
              ((Module.finrank (RatFunc C) N - 1 : ℕ) : ℝ) *
                (((2 * FunctionField.genus C N + 1) * Fintype.card K +
                  Module.finrank (RatFunc C) N : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hL hinnerNonneg
      _ ≤ (Module.finrank (RatFunc C) N : ℝ) *
            ((Module.finrank (RatFunc C) N : ℝ) *
                Module.finrank (RatFunc C) N +
              (Module.finrank (RatFunc C) N : ℝ) *
                ((((2 * FunctionField.genus C N + 1) * Fintype.card K : ℕ) : ℝ) +
                  Module.finrank (RatFunc C) N)) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 2 * (Module.finrank (RatFunc C) N : ℝ) ^ 3 +
          (Module.finrank (RatFunc C) N : ℝ) ^ 2 *
            (((2 * FunctionField.genus C N + 1) * Fintype.card K : ℕ) : ℝ) := by
        ring
  nlinarith

end IntermediateBase

end

end BGS.HasseWeil
