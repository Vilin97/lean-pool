/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms
public import Mathlib.FieldTheory.Galois.Abelian
/-!
# Abelian standard Lubin--Tate level fields

The finite unit parameter group

`O_F^* / U_F^(n + 1)`

acts multiplicatively and faithfully on the primitive level-`n + 1`
division point.  The finite-level automorphism calculation identifies this
parameter group bijectively with the full Galois group.  We package that
identification as a multiplicative equivalence and transport commutativity
to the Galois group.
-/

@[expose] public section

noncomputable
section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The multiplicative map from finite unit parameters to automorphisms of
the standard Lubin--Tate level field. -/
noncomputable def standardLubinTateUnitParameterToGalHom
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateUnitParameter F n →*
      Gal((standardLubinTateLevelField hπ n)/K) where
  toFun := standardLubinTateUnitParameterToGal F hπ n
  map_one' := standardLubinTateUnitParameterToGal_one F hπ n
  map_mul' := standardLubinTateUnitParameterToGal_mul F hπ n

/-- The homomorphism has the original parameter-to-Galois map as its
underlying function. -/
@[simp]
theorem standardLubinTateUnitParameterToGalHom_apply
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterToGalHom F hπ n a =
      standardLubinTateUnitParameterToGal F hπ n a :=
  rfl

/-- Finite unit parameters are multiplicatively equivalent to the full
Galois group of the standard level field. -/
noncomputable def standardLubinTateUnitParameterEquivGal
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateUnitParameter F n ≃*
      Gal((standardLubinTateLevelField hπ n)/K) :=
  MulEquiv.ofBijective
    (standardLubinTateUnitParameterToGalHom F hπ n)
    (by
      change Function.Bijective
        (standardLubinTateUnitParameterToGal F hπ n)
      exact standardLubinTateUnitParameterToGal_bijective F hπ n)

/-- The multiplicative equivalence evaluates as the original explicit
parameter automorphism. -/
@[simp]
theorem standardLubinTateUnitParameterEquivGal_apply
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterEquivGal F hπ n a =
      standardLubinTateUnitParameterToGal F hπ n a :=
  rfl

/-- The inverse of the explicit unit-parameter automorphism acts on the
chosen primitive generator through the inverse Lubin--Tate unit action.

This is the pointwise `[u⁻¹]` target needed for the later comparison with
the actual local Artin map; it does not identify the two maps merely from
their kernels. -/
theorem standardLubinTateUnitParameterEquivGal_inv_class_apply_gen
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (u : F.valuationSubringˣ) :
    (standardLubinTateUnitParameterEquivGal F hπ n
        (standardLubinTateUnitParameterClass F n u))⁻¹
        (standardLubinTateLevelPowerBasis hπ n).gen =
      standardLubinTatePrimitiveLevelAction hπ n u⁻¹ := by
  have hgal :
      (standardLubinTateUnitParameterEquivGal F hπ n
          (standardLubinTateUnitParameterClass F n u))⁻¹ =
        standardLubinTateUnitParameterEquivGal F hπ n
          (standardLubinTateUnitParameterClass F n u)⁻¹ :=
    ((standardLubinTateUnitParameterEquivGal F hπ n).map_inv _).symm
  rw [hgal]
  have hclass :
      (standardLubinTateUnitParameterClass F n u)⁻¹ =
        standardLubinTateUnitParameterClass F n u⁻¹ :=
    ((standardLubinTateUnitParameterClass F n).map_inv u).symm
  rw [hclass, standardLubinTateUnitParameterEquivGal_apply]
  change
    standardLubinTateUnitParameterAlgEquiv F hπ n
        (standardLubinTateUnitParameterClass F n u⁻¹)
        (standardLubinTateLevelPowerBasis hπ n).gen =
      standardLubinTatePrimitiveLevelAction hπ n u⁻¹
  rw [standardLubinTateUnitParameterAlgEquiv_apply_gen]
  apply Subtype.ext
  rw [standardLubinTateUnitParameterLevelRoot_coe,
    standardLubinTatePrimitiveLevelAction_coe,
    standardLubinTateUnitParameterRoot_class]

/-- The full Galois group of a standard finite Lubin--Tate level is
commutative. -/
theorem standardLubinTateLevelField_gal_comm
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
    (σ τ : Gal((standardLubinTateLevelField hπ n)/K)) :
    σ * τ = τ * σ := by
  let e := standardLubinTateUnitParameterEquivGal F hπ n
  apply e.symm.injective
  calc
    e.symm (σ * τ) = e.symm σ * e.symm τ := e.symm.map_mul σ τ
    _ = e.symm τ * e.symm σ := mul_comm _ _
    _ = e.symm (τ * σ) := (e.symm.map_mul τ σ).symm

/-- The Galois group of the standard level field is a commutative group. -/
instance standardLubinTateLevelField_isMulCommutative
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    IsMulCommutative
      (Gal((standardLubinTateLevelField hπ n)/K)) :=
  ⟨⟨standardLubinTateLevelField_gal_comm F hπ n⟩⟩

/-- Every standard finite Lubin--Tate level is abelian Galois over its base
local field. -/
instance standardLubinTateLevelField_isAbelianGalois
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    IsAbelianGalois K (standardLubinTateLevelField hπ n) where
  toIsGalois :=
    standardLubinTateLevelField_isGalois (F := F) hπ n
  toIsMulCommutative :=
    standardLubinTateLevelField_isMulCommutative F hπ n

end LubinTate

end
