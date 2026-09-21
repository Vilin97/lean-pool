/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Generic Ore-localization facts

This file records unconditional fraction and denominator results used by a
stage argument.  The common-denominator lemma is proved directly from the
Ore condition.  No flatness, Noetherianity, or freeness of a localized ring
over a stage ring is assumed.
-/

namespace AlgebraicAnalysis
namespace OreStageLocalization

open OreLocalization
open nonZeroDivisors

universe u

section CommonDenominators

variable {R : Type u} [Monoid R]
variable {S : Submonoid R} [OreSet S]

/-- A finite family of Ore denominators has a common left multiple. -/
theorem exists_common_left_multiple (s : Finset S) :
    ∃ t : S, ∀ a ∈ s, ∃ u : R, (t : R) = u * (a : R) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_⟩
      simp
  | @insert a s ha ih =>
      rcases ih with ⟨t, ht⟩
      rcases oreCondition (t : R) a with ⟨u, v, huv⟩
      refine ⟨v * t, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨u, huv⟩
      · rcases ht b hb with ⟨w, hw⟩
        refine ⟨(v : R) * w, ?_⟩
        simpa [Submonoid.coe_mul, hw, mul_assoc]

end CommonDenominators

section FractionRepresentation

variable {R : Type u} [Ring R] [Nontrivial R] [NoZeroDivisors R]
variable {S : Submonoid R} [OreSet S]

/-- Every element of an Ore localization has an explicit numerator/denominator form. -/
theorem exists_fraction (x : R[S⁻¹]) :
    ∃ r : R, ∃ s : S, x = r /ₒ s := by
  induction x using OreLocalization.ind with
  | _ r s => exact ⟨r, s, rfl⟩

/-- A nonzero localized element has a representative with nonzero numerator. -/
theorem exists_ne_zero_numerator {x : R[S⁻¹]} (hx : x ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ ∃ s : S, x = r /ₒ s := by
  induction x using OreLocalization.ind with
  | _ r s =>
      refine ⟨r, ?_, s, rfl⟩
      intro hr
      apply hx
      subst r
      exact OreLocalization.zero_oreDiv' s

/-- Under a right non-zero-divisor hypothesis, the numerator embedding is injective. -/
theorem numerator_injective (hS : S ≤ nonZeroDivisorsRight R) :
    Function.Injective (OreLocalization.numeratorHom : R → R[S⁻¹]) :=
  OreLocalization.numeratorHom_inj <| by
    intro s hs
    rw [mem_nonZeroDivisorsLeft_iff]
    intro y hsy
    have hs0 : (s : R) ≠ 0 := by
      intro hs0
      have h1 : (1 : R) = 0 := hS hs 1 (by simp [hs0])
      exact one_ne_zero h1
    exact (mul_eq_zero.mp hsy).resolve_left hs0

/-- Every chosen denominator becomes a unit in an Ore localization. -/
theorem denominator_isUnit (s : S) :
    IsUnit (OreLocalization.numeratorHom (s : R) : R[S⁻¹]) :=
  OreLocalization.numerator_isUnit s

end FractionRepresentation

section FullFractionRing

variable {R : Type u} [Ring R] [Nontrivial R] [NoZeroDivisors R]
variable [OreLocalization.OreSet R⁰]

/-- Every nonzero numerator is a unit in the full Ore division-ring localization. -/
theorem nonzero_numerator_isUnit {r : R} (hr : r ≠ 0) :
    IsUnit (OreLocalization.numeratorHom r : R[R⁰⁻¹]) := by
  simpa using
    (OreLocalization.numerator_isUnit
      (⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ : R⁰))

/-- Every nonzero element of the full Ore localization is a unit. -/
theorem full_isUnit_of_ne_zero {x : R[R⁰⁻¹]} (hx : x ≠ 0) : IsUnit x :=
  isUnit_iff_ne_zero.mpr hx

end FullFractionRing


end OreStageLocalization
end AlgebraicAnalysis
