/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive

/-!
# Coefficientwise ring homomorphisms of Hahn series

A ring homomorphism on coefficients acts coefficientwise on Hahn series and on their
nonpositive-support subrings. Injective coefficient maps preserve support exactly. These bundled
maps provide the module-safe interface needed when a bounded Hahn field is embedded in the full
Hahn field.
-/

public noncomputable section

namespace HahnSeries

universe u v w

section Full

variable {Γ : Type u} {R : Type v} {S : Type w}
variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
variable [Semiring R] [Semiring S]

/-- Apply a ring homomorphism to every coefficient of a Hahn series. -/
def coefficientMapRingHom (f : R →+* S) : R⟦Γ⟧ →+* S⟦Γ⟧ where
  toFun x := x.map f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero f.toMonoidWithZeroHom.toZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom

/-- Coefficientwise mapping evaluates by applying the coefficient homomorphism. -/
@[simp]
theorem coefficientMapRingHom_coeff (f : R →+* S) (x : R⟦Γ⟧) (g : Γ) :
    (coefficientMapRingHom f x).coeff g = f (x.coeff g) :=
  (rfl)

/-- An injective coefficient homomorphism preserves Hahn-series support. -/
theorem support_coefficientMapRingHom (f : R →+* S) (hf : Function.Injective f)
    (x : R⟦Γ⟧) :
    (coefficientMapRingHom f x).support = x.support := by
  ext g
  rw [mem_support, mem_support, coefficientMapRingHom_coeff]
  exact not_congr (map_eq_zero_iff f hf)

end Full

namespace Nonpositive

variable {Γ : Type u} {R : Type v} {S : Type w}
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
variable [Ring R] [Ring S]

/-- Apply a ring homomorphism coefficientwise to a nonpositive Hahn series. -/
def coefficientMapRingHom (f : R →+* S) : Nonpositive Γ R →+* Nonpositive Γ S where
  toFun x := ⟨HahnSeries.coefficientMapRingHom f (x : R⟦Γ⟧),
    (HahnSeries.support_map_subset (x : R⟦Γ⟧) f.toZeroHom).trans (support_subset x)⟩
  map_one' := Subtype.ext (map_one (HahnSeries.coefficientMapRingHom f))
  map_mul' x y := Subtype.ext
    (map_mul (HahnSeries.coefficientMapRingHom f) (x : R⟦Γ⟧) (y : R⟦Γ⟧))
  map_zero' := Subtype.ext (map_zero (HahnSeries.coefficientMapRingHom f))
  map_add' x y := Subtype.ext
    (map_add (HahnSeries.coefficientMapRingHom f) (x : R⟦Γ⟧) (y : R⟦Γ⟧))

/-- The nonpositive coefficient map acts coefficientwise. -/
@[simp]
theorem coe_coefficientMapRingHom (f : R →+* S) (x : Nonpositive Γ R) :
    (coefficientMapRingHom f x : S⟦Γ⟧) = HahnSeries.coefficientMapRingHom f x :=
  (rfl)

/-- An injective coefficient homomorphism preserves nonpositive Hahn-series support. -/
theorem support_coefficientMapRingHom (f : R →+* S) (hf : Function.Injective f)
    (x : Nonpositive Γ R) :
    (coefficientMapRingHom f x : S⟦Γ⟧).support = (x : R⟦Γ⟧).support := by
  rw [coe_coefficientMapRingHom, HahnSeries.support_coefficientMapRingHom f hf]

end Nonpositive

end HahnSeries
