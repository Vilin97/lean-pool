/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubring
public import Mathlib.RingTheory.Localization.FractionRing

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedDivisibility
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGradedDomain
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.OrdinalValueDegree

/-!
# The fraction field of $\widehat{\mathrm P}$

This module defines the fraction field `Frac(P̂)` occurring in LM24, Lemmas 6.3.3--6.3.4. The
ring `P̂` is the intrinsic direct sum of the spaces `P_α`, and its canonical map to the
fraction field is injective.

The coefficient-field algebra structure is obtained by composing `K → P̂` with the canonical
localization map `P̂ → Frac(P̂)`. It is kept distinct from the localization algebra structure,
so the two scalar structures are not conflated.
-/

universe v

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K]

/-- The intrinsic direct sum `P̂` is an integral domain: the exponent-valued order valuation is
multiplicative (Berarducci, Theorem 9.7), so its associated graded ring has no zero divisors. -/
instance principalSubringIsDomain :
    IsDomain (PrincipalSubring K) :=
  NoZeroDivisors.to_isDomain _

variable (K) in
/-- The canonical fraction field of `P̂`. -/
def PrincipalSubringFractionField :=
  FractionRing (PrincipalSubring K)

omit [CharZero K] in
variable (K) in
/-- The principal graded fraction field is the canonical fraction-ring construction. -/
theorem principalSubringFractionField_eq_fractionRing :
    PrincipalSubringFractionField K =
      FractionRing (PrincipalSubring K) :=
  (rfl)

/-- The canonical field structure on the fraction field of `P̂`. -/
noncomputable instance principalSubringFractionFieldInstance :
    Field (PrincipalSubringFractionField K) :=
  (principalSubringFractionField_eq_fractionRing K).symm ▸
    (inferInstance : Field (FractionRing (PrincipalSubring K)))

variable (K) in
/-- The canonical ring equivalence from the defined fraction field to the fraction-ring
construction. -/
def principalSubringFractionRingEquiv :
    PrincipalSubringFractionField K ≃+*
      FractionRing (PrincipalSubring K) := by
  let h := principalSubringFractionField_eq_fractionRing K
  exact
    { toFun := fun x ↦ h.mp x
      invFun := fun x ↦ h.mpr x
      left_inv := fun x ↦ by cases h; rfl
      right_inv := fun x ↦ by cases h; rfl
      map_add' := by
        intro x y
        cases h
        rfl
      map_mul' := by
        intro x y
        cases h
        rfl }

variable (K) in
/-- The canonical localization algebra structure `P̂ → Frac(P̂)`. -/
noncomputable abbrev principalSubringFractionSelfAlgebra :
    Algebra (PrincipalSubring K)
      (PrincipalSubringFractionField K) :=
  RingHom.toAlgebra
    ((principalSubringFractionRingEquiv K).symm.toRingHom.comp
      (algebraMap (PrincipalSubring K)
        (FractionRing (PrincipalSubring K))))

/-- The principal graded subring acts canonically on its explicitly constructed fraction field. -/
local instance principalSubringFractionSelfAlgebraInstance :
    Algebra (PrincipalSubring K)
      (PrincipalSubringFractionField K) :=
  principalSubringFractionSelfAlgebra K

variable (K) in
/-- The defined fraction field is canonically equivalent, as a `P̂`-algebra, to the fraction-ring
construction. -/
def principalSubringFractionAlgEquiv :
    FractionRing (PrincipalSubring K) ≃ₐ[PrincipalSubring K]
      PrincipalSubringFractionField K where
  toRingEquiv := (principalSubringFractionRingEquiv K).symm
  commutes' _ := rfl

local instance principalSubringFractionIsFractionRing :
    IsFractionRing (PrincipalSubring K)
      (PrincipalSubringFractionField K) := by
  exact IsFractionRing.of_algEquiv (principalSubringFractionAlgEquiv K)

variable (K) in
/-- The canonical inclusion `P̂ → Frac(P̂)`. -/
def principalSubringToFraction :
    PrincipalSubring K →+* PrincipalSubringFractionField K :=
  algebraMap _ _

/-- The canonical inclusion is the localization algebra map on each element of `P̂`. -/
@[simp]
theorem principalSubringToFraction_apply (B : PrincipalSubring K) :
    principalSubringToFraction K B =
      @algebraMap (PrincipalSubring K)
        (PrincipalSubringFractionField K) _ _
      (principalSubringFractionSelfAlgebra K) B :=
  (rfl)

/-- Construct an element of `Frac(P̂)` from a numerator and a non-zero-divisor denominator. -/
def principalSubringFractionMk (B : PrincipalSubring K)
    (C : nonZeroDivisors (PrincipalSubring K)) :
    PrincipalSubringFractionField K :=
  IsLocalization.mk' (PrincipalSubringFractionField K) B C

/-- The canonical inclusion sends `B` to the localization fraction `B / 1`. -/
theorem principalSubringToFraction_apply_eq_mk (B : PrincipalSubring K) :
    principalSubringToFraction K B =
      principalSubringFractionMk B
        (1 : nonZeroDivisors (PrincipalSubring K)) := by
  rw [principalSubringFractionMk, IsLocalization.mk'_one]
  rfl

variable (K) in
/-- A localization representative in `Frac(P̂)` is zero exactly when its numerator is zero. -/
@[simp]
theorem principalSubringFractionMk_eq_zero_iff {B : PrincipalSubring K}
    {C : nonZeroDivisors (PrincipalSubring K)} :
    principalSubringFractionMk B C = 0 ↔ B = 0 := by
  rw [principalSubringFractionMk]
  exact IsFractionRing.mk'_eq_zero_iff_eq_zero

variable (K) in
/-- The canonical inclusion of `P̂` in its fraction field is injective. -/
theorem principalSubringToFraction_injective :
    Function.Injective (principalSubringToFraction K) :=
  IsFractionRing.injective _ _

/-- Every element of `Frac(P̂)` has a localization representative with denominator in the
non-zero-divisor submonoid of `P̂`. -/
theorem principalSubringFraction_exists_mk (x : PrincipalSubringFractionField K) :
    ∃ (B : PrincipalSubring K)
      (C : nonZeroDivisors (PrincipalSubring K)),
      x = principalSubringFractionMk B C := by
  obtain ⟨B, C, hBC⟩ :=
    IsLocalization.exists_mk'_eq
      (nonZeroDivisors (PrincipalSubring K)) x
  exact ⟨B, C, by simpa only [principalSubringFractionMk] using hBC.symm⟩

/-- Every nonzero element of `Frac(P̂)` has a localization representative with nonzero
numerator. -/
theorem principalSubringFraction_exists_mk_of_ne_zero
    {x : PrincipalSubringFractionField K} (hx : x ≠ 0) :
    ∃ (B : PrincipalSubring K)
      (C : nonZeroDivisors (PrincipalSubring K)),
      B ≠ 0 ∧ x = principalSubringFractionMk B C := by
  obtain ⟨B, C, hBC⟩ := principalSubringFraction_exists_mk x
  refine ⟨B, C, ?_, hBC⟩
  intro hB
  apply hx
  rw [hBC, hB]
  exact (principalSubringFractionMk_eq_zero_iff K).mpr rfl

variable (K) in
/-- The coefficient-field algebra structure on `Frac(P̂)`, induced through `K → P̂`. -/
noncomputable abbrev principalSubringFractionAlgebra :
    Algebra K (PrincipalSubringFractionField K) :=
  RingHom.toAlgebra
    ((principalSubringToFraction K).comp
      (algebraMap K (PrincipalSubring K)))

/-- The coefficient-field algebra structure on the explicitly constructed principal-subring
fraction field. -/
local instance principalSubringFractionAlgebraInstance :
    Algebra K (PrincipalSubringFractionField K) :=
  principalSubringFractionAlgebra K

/-- The coefficient-field embedding in `Frac(P̂)` is the composite `K → P̂ → Frac(P̂)`. -/
@[simp]
theorem principalSubringFraction_algebraMap_apply (k : K) :
    algebraMap K (PrincipalSubringFractionField K) k =
      principalSubringToFraction K
        (algebraMap K (PrincipalSubring K) k) :=
  (rfl)

variable (K) in
/-- The coefficient, principal-graded, and fraction-field algebra structures form the canonical
scalar tower `K → P̂ → Frac(P̂)`. -/
theorem principalSubringFraction_isScalarTower :
    @IsScalarTower K (PrincipalSubring K)
      (PrincipalSubringFractionField K)
      inferInstance
      (principalSubringFractionSelfAlgebra K).toSMul
      (principalSubringFractionAlgebra K).toSMul := by
  apply @IsScalarTower.of_algebraMap_eq K (PrincipalSubring K)
    (PrincipalSubringFractionField K) _ _ _ _
    (principalSubringFractionSelfAlgebra K)
    (principalSubringFractionAlgebra K)
  intro k
  rw [principalSubringFraction_algebraMap_apply,
    principalSubringToFraction_apply]

variable (K) in
/-- The coefficient-field embedding into `Frac(P̂)` is injective. -/
theorem principalSubringFraction_algebraMap_injective :
    Function.Injective
      (algebraMap K (PrincipalSubringFractionField K)) := by
  intro k l hkl
  apply principalSubring_algebraMap_injective K
  apply principalSubringToFraction_injective K
  simpa only [principalSubringFraction_algebraMap_apply] using hkl

attribute [irreducible] PrincipalSubringFractionField

end Berarducci
