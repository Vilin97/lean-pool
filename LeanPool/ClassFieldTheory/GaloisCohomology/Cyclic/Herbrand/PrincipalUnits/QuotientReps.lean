/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients
/-! Provides the public declarations in the `CyclicCohomology.Herbrand.PrincipalUnits.QuotientReps` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Integer units modulo the `n`-th principal-unit subgroup.

This named type is the representation boundary: downstream code uses its
quotient interface rather than unfolding the concrete quotient. -/
def IntegerUnitsModPrincipalUnitsAtLevel
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Type u :=
  𝒪[K]ˣ ⧸ principalUnits K n

/-- Integer units modulo level principal units form a commutative group. -/
instance integerUnitsModPrincipalUnitsAtLevelCommGroup
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    CommGroup (IntegerUnitsModPrincipalUnitsAtLevel K n) := by
  change CommGroup (𝒪[K]ˣ ⧸ principalUnits K n)
  infer_instance

/-- Explicit comparison with the concrete quotient implementation. -/
def integerUnitsModPrincipalUnitsAtLevelConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    IntegerUnitsModPrincipalUnitsAtLevel K n ≃*
      (𝒪[K]ˣ ⧸ principalUnits K n) := by
  change (𝒪[K]ˣ ⧸ principalUnits K n) ≃*
    (𝒪[K]ˣ ⧸ principalUnits K n)
  exact MulEquiv.refl _

/-- The canonical class of an integer unit modulo `U_K^n`. -/
def integerUnitsModPrincipalUnitsAtLevelMk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    𝒪[K]ˣ →* IntegerUnitsModPrincipalUnitsAtLevel K n := by
  change 𝒪[K]ˣ →* (𝒪[K]ˣ ⧸ principalUnits K n)
  exact QuotientGroup.mk' (principalUnits K n)

/-- The concrete quotient equivalence sends a unit to its canonical class. -/
@[simp]
theorem integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K n
        (integerUnitsModPrincipalUnitsAtLevelMk K n x) =
      QuotientGroup.mk x :=
  rfl

/-- Every integer-unit quotient class has a representative. -/
theorem integerUnitsModPrincipalUnitsAtLevelMk_surjective
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Function.Surjective (integerUnitsModPrincipalUnitsAtLevelMk K n) := by
  change Function.Surjective (QuotientGroup.mk' (principalUnits K n))
  exact QuotientGroup.mk'_surjective (principalUnits K n)

/-- Eliminate a level quotient through its canonical representatives. -/
protected theorem IntegerUnitsModPrincipalUnitsAtLevel.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : IntegerUnitsModPrincipalUnitsAtLevel K n → Prop}
    (q : IntegerUnitsModPrincipalUnitsAtLevel K n)
    (h : ∀ x : 𝒪[K]ˣ,
      motive (integerUnitsModPrincipalUnitsAtLevelMk K n x)) :
    motive q := by
  change motive (show 𝒪[K]ˣ ⧸ principalUnits K n from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

/-- Descend a homomorphism that kills `U_K^n`. -/
def integerUnitsModPrincipalUnitsAtLevelLift
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker) :
    IntegerUnitsModPrincipalUnitsAtLevel K n →* M := by
  change (𝒪[K]ˣ ⧸ principalUnits K n) →* M
  exact QuotientGroup.lift (principalUnits K n) f h

/-- A map lifted from the integer-unit quotient agrees on representatives. -/
@[simp]
theorem integerUnitsModPrincipalUnitsAtLevelLift_mk
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelLift n f h
        (integerUnitsModPrincipalUnitsAtLevelMk K n x) = f x :=
  rfl

/-- A unit represents the identity exactly when it lies in the level principal-unit subgroup. -/
theorem integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelMk K n x = 1 ↔
      x ∈ principalUnits K n := by
  change (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K n) = 1 ↔ _
  exact QuotientGroup.eq_one_iff x

/-- Two units represent the same class exactly when their quotient is a level principal unit. -/
@[simp]
theorem integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (x y : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelMk K n x =
        integerUnitsModPrincipalUnitsAtLevelMk K n y ↔
      x / y ∈ principalUnits K n := by
  change
    (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K n) =
      QuotientGroup.mk y ↔ _
  exact QuotientGroup.eq_iff_div_mem

end

end CyclicCohomology
