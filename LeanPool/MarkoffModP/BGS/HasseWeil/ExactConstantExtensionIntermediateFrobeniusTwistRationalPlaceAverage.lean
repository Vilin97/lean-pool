/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionIntermediateFrobeniusTwistFinitePlaceAverage
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistRationalPlaceAverage

/-!
# Complete rational-place averaging over an intermediate base

The finite-place average over `Gal(N/L)` is exact.  Complete rational-place
counts differ from it only at infinity, and both the twists and `L` have at
most the original degree `[N : C(X)]` rational infinity places.  This gives a
uniform aggregate error independent of the auxiliary constant extension.
-/

@[expose] public section

namespace BGS.HasseWeil

private theorem finrank_mul_finrank_of_fields
    (K F E : Type*) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E] :
    Module.finrank K F * Module.finrank F E = Module.finrank K E :=
  Module.finrank_mul_finrank K F E

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

local instance intermediateRationalAverageBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance intermediateRationalAverageBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

variable (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))

section IntermediateBase

variable (L : Type*) [Field L]
  [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  [Algebra L N] [IsScalarTower (RatFunc C) L N]
  [FiniteDimensional L N] [IsGalois L N]

local instance intermediateRationalAverageConstantAlgebra : Algebra C L :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) L).comp
    (algebraMap C (RatFunc C)))

local instance intermediateRationalAverageConstantTower : IsScalarTower C L N := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  change algebraMap (RatFunc C) N (algebraMap C (RatFunc C) c) =
    algebraMap L N (algebraMap (RatFunc C) L (algebraMap C (RatFunc C) c))
  exact IsScalarTower.algebraMap_apply (RatFunc C) L N _

omit [Fintype C] [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional (RatFunc C) N] [IsGalois (RatFunc C) N]
  [FiniteDimensional C S] [IsGalois C S] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L] [FiniteDimensional L N] [IsGalois L N] in
/-- Compatibility of the rational-function and intermediate-base algebra maps
on the exact constant extension. -/
private theorem intermediateRationalAverageRatFuncBaseTower :
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

/-- The rational infinity-place count of one intermediate-base twist. -/
noncomputable def intermediateFrobeniusTwistFieldRationalInfinityPlaceCount
    (g : N ≃ₐ[L] N) : ℕ :=
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  letI : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
  letI : Algebra (RatFunc C) F :=
    intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_intermediateFrobeniusTwistField_over_ratFunc
      C S N hExact L g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_intermediateFrobeniusTwistField_over_ratFunc
      C S N hExact L g
  Nat.card (FiniteExtensionRationalInfinityPlace C F)

/-- The complete rational-place count of one intermediate-base twist, split
into finite and infinity parts. -/
noncomputable def intermediateFrobeniusTwistFieldRationalPlaceCount
    (g : N ≃ₐ[L] N) : ℕ :=
  intermediateFrobeniusTwistFieldRationalFinitePlaceCount
      C S N hExact L g +
    intermediateFrobeniusTwistFieldRationalInfinityPlaceCount
      C S N hExact L g

/-- The split definition is the actual complete rational-place count. -/
theorem intermediateFrobeniusTwistFieldRationalPlaceCount_eq_finiteExtensionRationalPlaceCount
    (g : N ≃ₐ[L] N) :
    let T := ExactConstantExtension C N S
    letI : Field T := exactConstantExtensionField C N S hExact
    letI : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
    let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
    letI : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
    letI : Algebra (RatFunc C) F :=
      intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
    letI : SMul (RatFunc C) F := Algebra.toSMul
    letI : Module (RatFunc C) F := Algebra.toModule
    letI : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_intermediateFrobeniusTwistField_over_ratFunc
        C S N hExact L g
    letI : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_intermediateFrobeniusTwistField_over_ratFunc
        C S N hExact L g
    intermediateFrobeniusTwistFieldRationalPlaceCount C S N hExact L g =
      finiteExtensionRationalPlaceCount C F := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  let : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
  let : Algebra (RatFunc C) F :=
    intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
  let : SMul (RatFunc C) F := Algebra.toSMul
  let : Module (RatFunc C) F := Algebra.toModule
  let : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_intermediateFrobeniusTwistField_over_ratFunc
      C S N hExact L g
  let : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_intermediateFrobeniusTwistField_over_ratFunc
      C S N hExact L g
  let : Finite (FiniteExtensionRationalFinitePlace C F) := inferInstance
  let : Finite (FiniteExtensionRationalInfinityPlace C F) := inferInstance
  unfold intermediateFrobeniusTwistFieldRationalPlaceCount
  rw [intermediateFrobeniusTwistFieldRationalFinitePlaceCount,
    intermediateFrobeniusTwistFieldRationalInfinityPlaceCount]
  change Nat.card (FiniteExtensionRationalFinitePlace C F) +
      Nat.card (FiniteExtensionRationalInfinityPlace C F) =
    Nat.card (FiniteExtensionRationalFinitePlace C F ⊕
      FiniteExtensionRationalInfinityPlace C F)
  exact Nat.card_sum.symm

/-- Each intermediate twist has at most `[N : C(X)]` rational infinity
places, provided its intermediate Galois order divides the constant degree. -/
theorem intermediateFrobeniusTwistFieldRationalInfinityPlaceCount_le_original_finrank
    (hdivL : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S)
    (g : N ≃ₐ[L] N) :
    intermediateFrobeniusTwistFieldRationalInfinityPlaceCount
        C S N hExact L g ≤ Module.finrank (RatFunc C) N := by
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
    intermediateRationalAverageRatFuncBaseTower C S N L
  let Fₗ := exactConstantExtensionFrobeniusTwistField C L N S hExact g
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
  let : IsScalarTower (RatFunc C) L Fₗ :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite L Fₗ :=
    Module.Finite.of_restrictScalars_finite (RatFunc C) L Fₗ
  change Nat.card (FiniteExtensionRationalInfinityPlace C Fₗ) ≤ _
  calc
    Nat.card (FiniteExtensionRationalInfinityPlace C Fₗ) ≤
        Module.finrank (RatFunc C) Fₗ :=
      rationalInfinityPlace_card_le_finrank C Fₗ
    _ = Module.finrank (RatFunc C) L * Module.finrank L Fₗ :=
      (finrank_mul_finrank_of_fields (RatFunc C) L Fₗ).symm
    _ = Module.finrank (RatFunc C) L * Module.finrank L N := by
      rw [finrank_frobeniusTwistField_over_base C L N S hExact g hdivL]
    _ = Module.finrank (RatFunc C) N :=
      finrank_mul_finrank_of_fields (RatFunc C) L N

omit [Fintype C] [FiniteDimensional L N] [IsGalois L N] in
/-- Rational infinity places of the intermediate field itself are bounded by
the original degree. -/
theorem intermediateBaseRationalInfinityPlaceCount_le_original_finrank :
    Nat.card (FiniteExtensionRationalInfinityPlace C L) ≤
      Module.finrank (RatFunc C) N := by
  calc
    Nat.card (FiniteExtensionRationalInfinityPlace C L) ≤
        Module.finrank (RatFunc C) L := rationalInfinityPlace_card_le_finrank C L
    _ ≤ Module.finrank (RatFunc C) N := by
      apply Nat.le_of_dvd Module.finrank_pos
      rw [← finrank_mul_finrank_of_fields (RatFunc C) L N]
      exact dvd_mul_right _ _

/-- The total infinity contribution of the twists is bounded by the group
order times the original degree. -/
theorem sum_intermediateFrobeniusTwistFieldRationalInfinityPlaceCount_le
    (hdivL : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S) :
    (∑ g : N ≃ₐ[L] N,
      intermediateFrobeniusTwistFieldRationalInfinityPlaceCount
        C S N hExact L g) ≤
      Nat.card (N ≃ₐ[L] N) * Module.finrank (RatFunc C) N := by
  calc
    (∑ g : N ≃ₐ[L] N,
        intermediateFrobeniusTwistFieldRationalInfinityPlaceCount
          C S N hExact L g) ≤
        ∑ _g : N ≃ₐ[L] N, Module.finrank (RatFunc C) N := by
      exact Finset.sum_le_sum fun g _ ↦
        intermediateFrobeniusTwistFieldRationalInfinityPlaceCount_le_original_finrank
          C S N hExact L hdivL g
    _ = Nat.card (N ≃ₐ[L] N) * Module.finrank (RatFunc C) N := by
      simp [Nat.card_eq_fintype_card]

/-- Exact finite-plus-infinity aggregate identity over `Gal(N/L)`. -/
theorem sum_intermediateFrobeniusTwistFieldRationalPlaceCount_eq
    (hdivL : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S) :
    (∑ g : N ≃ₐ[L] N,
      intermediateFrobeniusTwistFieldRationalPlaceCount
        C S N hExact L g) =
      Nat.card (N ≃ₐ[L] N) *
          Nat.card (FiniteExtensionRationalFinitePlace C L) +
        ∑ g : N ≃ₐ[L] N,
          intermediateFrobeniusTwistFieldRationalInfinityPlaceCount
            C S N hExact L g := by
  simp_rw [intermediateFrobeniusTwistFieldRationalPlaceCount]
  rw [Finset.sum_add_distrib,
    sum_intermediateFrobeniusTwistFieldRationalFinitePlaceCount_eq_card_galois_mul_card
      C S N hExact L hdivL]

/-- The complete rational-place aggregate is uniformly close to the group
order times the complete rational-place count of `L`. -/
theorem abs_sum_intermediateFrobeniusTwistFieldRationalPlaceCount_sub_card_mul_base_le
    (hdivL : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S) :
    |∑ g : N ≃ₐ[L] N,
        (intermediateFrobeniusTwistFieldRationalPlaceCount
          C S N hExact L g : ℝ) -
      (Nat.card (N ≃ₐ[L] N) : ℝ) *
        finiteExtensionRationalPlaceCount C L| ≤
      2 * (Module.finrank (RatFunc C) N : ℝ) ^ 2 := by
  let G : ℕ := Nat.card (N ≃ₐ[L] N)
  let D : ℕ := Module.finrank (RatFunc C) N
  let Iₗ : ℕ := ∑ g : N ≃ₐ[L] N,
    intermediateFrobeniusTwistFieldRationalInfinityPlaceCount
      C S N hExact L g
  let Iₒ : ℕ := Nat.card (FiniteExtensionRationalInfinityPlace C L)
  have htotal := sum_intermediateFrobeniusTwistFieldRationalPlaceCount_eq
    C S N hExact L hdivL
  have hbase : finiteExtensionRationalPlaceCount C L =
      Nat.card (FiniteExtensionRationalFinitePlace C L) + Iₒ := by
    unfold finiteExtensionRationalPlaceCount
    rw [Nat.card_sum]
  have herr :
      (∑ g : N ≃ₐ[L] N,
          (intermediateFrobeniusTwistFieldRationalPlaceCount
            C S N hExact L g : ℝ)) -
        (G : ℝ) * finiteExtensionRationalPlaceCount C L =
      (Iₗ : ℝ) - (G : ℝ) * Iₒ := by
    have htotalReal :
        (∑ g : N ≃ₐ[L] N,
            (intermediateFrobeniusTwistFieldRationalPlaceCount
              C S N hExact L g : ℝ)) =
          (G : ℝ) * Nat.card (FiniteExtensionRationalFinitePlace C L) +
            (Iₗ : ℝ) := by
      exact_mod_cast htotal
    rw [htotalReal, hbase]
    push_cast
    ring
  have hIₗ : Iₗ ≤ G * D := by
    exact sum_intermediateFrobeniusTwistFieldRationalInfinityPlaceCount_le
      C S N hExact L hdivL
  have hIₒ : Iₒ ≤ D :=
    intermediateBaseRationalInfinityPlaceCount_le_original_finrank C N L
  have hG : G ≤ D := by
    dsimp only [G, D]
    rw [IsGalois.card_aut_eq_finrank]
    apply Nat.le_of_dvd Module.finrank_pos
    rw [← finrank_mul_finrank_of_fields (RatFunc C) L N]
    exact dvd_mul_left _ _
  rw [herr]
  have hIₗ' : (Iₗ : ℝ) ≤ (G : ℝ) * D := by exact_mod_cast hIₗ
  have hIₒ' : (Iₒ : ℝ) ≤ D := by exact_mod_cast hIₒ
  have hG' : (G : ℝ) ≤ D := by exact_mod_cast hG
  have hD : (0 : ℝ) ≤ D := by positivity
  have hGnonneg : (0 : ℝ) ≤ G := by positivity
  have hIₗnonneg : (0 : ℝ) ≤ Iₗ := by positivity
  have hIₒnonneg : (0 : ℝ) ≤ Iₒ := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith

end IntermediateBase

end

end BGS.HasseWeil
