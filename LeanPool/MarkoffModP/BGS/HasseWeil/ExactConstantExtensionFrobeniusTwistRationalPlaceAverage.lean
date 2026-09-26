/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistDegree
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistFinitePlaceAverage
public import LeanPool.MarkoffModP.BGS.HasseWeil.GaloisAverage

/-!
# Complete rational-place averaging for Frobenius twists

The finite-place Frobenius average is exact, including above ramified base
places.  Passing from finite rational places to the complete rational-place
count therefore introduces only the places above infinity.  Their number on
each twist is bounded by the degree of the original function field, uniformly
in the auxiliary constant extension.

This file records both the exact aggregate identity and the resulting uniform
bound for the centered aggregate error.  No branch-locus estimate is needed at
this boundary.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open scoped BigOperators TensorProduct


variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [IsGalois (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance rationalPlaceAverageBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance rationalPlaceAverageBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The number of rational places above infinity on one Frobenius-twist
field. -/
noncomputable def frobeniusTwistFieldRationalInfinityPlaceCount
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N) : ℕ :=
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  letI : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  letI : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : IsGalois (RatFunc C) T :=
    exactConstantExtension_isGalois C (RatFunc C) N S hExact
  letI : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  letI : Algebra (RatFunc C) F :=
    SubalgebraClass.toAlgebra F.toSubalgebra
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  Nat.card (FiniteExtensionRationalInfinityPlace C F)

/-- The complete rational-place count of one Frobenius-twist field, split
into its finite and infinity parts. -/
noncomputable def frobeniusTwistFieldRationalPlaceCount
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N) : ℕ :=
  frobeniusTwistFieldRationalFinitePlaceCount C S N hExact g +
    frobeniusTwistFieldRationalInfinityPlaceCount C S N hExact g

omit [Finite S] [DecidableEq S] [DecidableEq (RatFunc S)] in
/-- The split definition is the actual complete degree-one place count of
the twist field. -/
theorem frobeniusTwistFieldRationalPlaceCount_eq_finiteExtensionRationalPlaceCount
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N) :
    let T := ExactConstantExtension C N S
    letI : Field T := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) T :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) T := Algebra.toSMul
    letI : Module (RatFunc C) T := Algebra.toModule
    letI : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
    letI : MulAction (RatFunc C) T := DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C) T :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : IsGalois (RatFunc C) T :=
      exactConstantExtension_isGalois C (RatFunc C) N S hExact
    letI : Algebra.IsSeparable (RatFunc C) T :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    let F := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact g
    letI : Algebra (RatFunc C) F :=
      SubalgebraClass.toAlgebra F.toSubalgebra
    letI : SMul (RatFunc C) F := Algebra.toSMul
    letI : Module (RatFunc C) F := Algebra.toModule
    letI : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
    frobeniusTwistFieldRationalPlaceCount C S N hExact g =
      finiteExtensionRationalPlaceCount C F := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  let : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  let : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : IsGalois (RatFunc C) T :=
    exactConstantExtension_isGalois C (RatFunc C) N S hExact
  let : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  let : Algebra (RatFunc C) F :=
    SubalgebraClass.toAlgebra F.toSubalgebra
  let : SMul (RatFunc C) F := Algebra.toSMul
  let : Module (RatFunc C) F := Algebra.toModule
  let : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  let : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  let : Finite (FiniteExtensionRationalFinitePlace C F) := inferInstance
  let : Finite (FiniteExtensionRationalInfinityPlace C F) := inferInstance
  unfold frobeniusTwistFieldRationalPlaceCount
  rw [frobeniusTwistFieldRationalFinitePlaceCount,
    frobeniusTwistFieldRationalInfinityPlaceCount]
  change Nat.card (FiniteExtensionRationalFinitePlace C F) +
      Nat.card (FiniteExtensionRationalInfinityPlace C F) =
    Nat.card (FiniteExtensionRationalFinitePlace C F ⊕
      FiniteExtensionRationalInfinityPlace C F)
  exact Nat.card_sum.symm

omit [DecidableEq S] [DecidableEq (RatFunc S)] in
/-- The infinity contribution of each twist is bounded by the degree of the
original function field, independently of the auxiliary constant extension.
-/
theorem frobeniusTwistFieldRationalInfinityPlaceCount_le_original_finrank
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N)
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    frobeniusTwistFieldRationalInfinityPlaceCount C S N hExact g ≤
      Module.finrank (RatFunc C) N := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  let : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  let : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : IsGalois (RatFunc C) T :=
    exactConstantExtension_isGalois C (RatFunc C) N S hExact
  let : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  let : Algebra (RatFunc C) F :=
    SubalgebraClass.toAlgebra F.toSubalgebra
  let : SMul (RatFunc C) F := Algebra.toSMul
  let : Module (RatFunc C) F := Algebra.toModule
  let : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  let : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  change Nat.card (FiniteExtensionRationalInfinityPlace C F) ≤
    Module.finrank (RatFunc C) N
  calc
    Nat.card (FiniteExtensionRationalInfinityPlace C F) ≤
        Module.finrank (RatFunc C) F :=
      rationalInfinityPlace_card_le_finrank C F
    _ = Module.finrank (RatFunc C) N :=
      finrank_frobeniusTwistField_over_ratFunc_eq_original
        C N S hExact g hdiv

omit [DecidableEq S] [DecidableEq (RatFunc S)] in
/-- The total infinity contribution of all twists is uniformly bounded by
the Galois-group order times the original function-field degree. -/
theorem sum_frobeniusTwistFieldRationalInfinityPlaceCount_le
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    (∑ g : N ≃ₐ[RatFunc C] N,
      frobeniusTwistFieldRationalInfinityPlaceCount C S N hExact g) ≤
      Nat.card (N ≃ₐ[RatFunc C] N) *
        Module.finrank (RatFunc C) N := by
  calc
    (∑ g : N ≃ₐ[RatFunc C] N,
        frobeniusTwistFieldRationalInfinityPlaceCount C S N hExact g) ≤
        ∑ _g : N ≃ₐ[RatFunc C] N,
          Module.finrank (RatFunc C) N := by
      exact Finset.sum_le_sum fun g _ =>
        frobeniusTwistFieldRationalInfinityPlaceCount_le_original_finrank
          C S N hExact g hdiv
    _ = Nat.card (N ≃ₐ[RatFunc C] N) *
        Module.finrank (RatFunc C) N := by
      simp [Nat.card_eq_fintype_card]

/-- Exact finite-plus-infinity aggregate identity.  All finite rational
places contribute exactly `|Gal(N/C(X))| * |C|`; the displayed infinity sum
is the entire correction to the complete rational-place count. -/
theorem sum_frobeniusTwistFieldRationalPlaceCount_eq
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    (∑ g : N ≃ₐ[RatFunc C] N,
      frobeniusTwistFieldRationalPlaceCount C S N hExact g) =
      Nat.card (N ≃ₐ[RatFunc C] N) * Nat.card C +
        ∑ g : N ≃ₐ[RatFunc C] N,
          frobeniusTwistFieldRationalInfinityPlaceCount C S N hExact g := by
  simp_rw [frobeniusTwistFieldRationalPlaceCount]
  rw [Finset.sum_add_distrib,
    sum_frobeniusTwistFieldRationalFinitePlaceCount_eq_card_galois_mul_card
      C S N hExact hdiv]

/-- Exact centered aggregate-error identity over the reals.  It makes
explicit that the complete-place error is the infinity contribution minus
one point for each twist. -/
theorem sum_frobeniusTwistFieldRationalPlaceError_eq
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    (∑ g : N ≃ₐ[RatFunc C] N,
        ((frobeniusTwistFieldRationalPlaceCount C S N hExact g : ℝ) -
          (Nat.card C : ℝ) - 1)) =
      (∑ g : N ≃ₐ[RatFunc C] N,
          (frobeniusTwistFieldRationalInfinityPlaceCount
            C S N hExact g : ℝ)) -
        (Nat.card (N ≃ₐ[RatFunc C] N) : ℝ) := by
  have htotal := sum_frobeniusTwistFieldRationalPlaceCount_eq
    C S N hExact hdiv
  have htotalReal :
      (∑ g : N ≃ₐ[RatFunc C] N,
          (frobeniusTwistFieldRationalPlaceCount C S N hExact g : ℝ)) =
        (Nat.card (N ≃ₐ[RatFunc C] N) : ℝ) *
            (Nat.card C : ℝ) +
          ∑ g : N ≃ₐ[RatFunc C] N,
            (frobeniusTwistFieldRationalInfinityPlaceCount
              C S N hExact g : ℝ) := by
    exact_mod_cast htotal
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, htotalReal]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, Nat.card_eq_fintype_card]
  ring

/-- The centered aggregate error is bounded uniformly in the auxiliary
constant extension.  The sharper factor `finrank`, rather than
`finrank + 1`, follows because the original function-field degree is positive.
-/
theorem abs_sum_frobeniusTwistFieldRationalPlaceError_le
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    |∑ g : N ≃ₐ[RatFunc C] N,
        ((frobeniusTwistFieldRationalPlaceCount C S N hExact g : ℝ) -
          (Nat.card C : ℝ) - 1)| ≤
      (Nat.card (N ≃ₐ[RatFunc C] N) : ℝ) *
        Module.finrank (RatFunc C) N := by
  rw [sum_frobeniusTwistFieldRationalPlaceError_eq C S N hExact hdiv]
  let infinitySum : ℝ :=
    ∑ g : N ≃ₐ[RatFunc C] N,
      (frobeniusTwistFieldRationalInfinityPlaceCount C S N hExact g : ℝ)
  let groupCard : ℝ := Nat.card (N ≃ₐ[RatFunc C] N)
  let degree : ℝ := Module.finrank (RatFunc C) N
  have hinfinity_nonneg : 0 ≤ infinitySum := by
    dsimp only [infinitySum]
    positivity
  have hgroup_nonneg : 0 ≤ groupCard := by
    dsimp only [groupCard]
    positivity
  have hdegree_one : 1 ≤ degree := by
    dsimp only [degree]
    exact_mod_cast (Module.finrank_pos (R := RatFunc C) (M := N))
  have hinfinity_le : infinitySum ≤ groupCard * degree := by
    dsimp only [infinitySum, groupCard, degree]
    exact_mod_cast
      (sum_frobeniusTwistFieldRationalInfinityPlaceCount_le
        C S N hExact hdiv)
  apply abs_le.mpr
  constructor <;> nlinarith

end

end BGS.HasseWeil
