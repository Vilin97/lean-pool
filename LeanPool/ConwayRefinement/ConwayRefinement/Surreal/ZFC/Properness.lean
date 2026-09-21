/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.OmnificCodes
public import Mathlib.SetTheory.ZFC.Class
public import Mathlib.Logic.Small.Defs

import Mathlib.Logic.Small.Basic
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.Cardinal
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Ordinal

/-!
# Proper ZFC classes of numeric and omnific game codes

The intrinsic predicates on ZFC sets select numeric game codes and omnific-integer game codes.
Neither class is represented by a ZFC set. This is witnessed by the size of the distinct values:
evaluation covers every surreal number or omnific integer, and neither value type is small in
the universe of option sets. The quotient presentations of those values are likewise not small.
-/

universe u

public noncomputable section

namespace Surreal.OmnificInteger

/-- Omnific integers with option sets in universe `u` are not `u`-small. -/
theorem not_small : ¬Small.{u} OmnificInteger.{u} := by
  intro h
  letI : Small.{u} OmnificInteger.{u} := h
  let f : Ordinal.{u} → OmnificInteger.{u} := fun o ↦
    ⟨(NatOrdinal.of o).toSurreal, NatOrdinal.toSurreal_mem_omnificIntegers (NatOrdinal.of o)⟩
  apply not_injective_of_ordinal f
  intro a b hab
  exact NatOrdinal.of.injective (NatOrdinal.toSurreal.injective (congrArg Subtype.val hab))

end Surreal.OmnificInteger

namespace ZFSet

/-- The ZFC class of sets satisfying the game-code grammar and Conway's numeric condition. -/
def numericGameCodes : Class.{u} :=
  fun z ↦ ∃ h : IsGameCode z, (GameCode.mk z h).IsNumeric

/-- Membership in the numeric-code class is the intrinsic numeric predicate on a game code. -/
theorem numericGameCodes_iff (z : ZFSet.{u}) :
    numericGameCodes z ↔ ∃ h : IsGameCode z, (GameCode.mk z h).IsNumeric := (Iff.rfl)

/-- The ZFC class of game codes satisfying Conway's omnific-integer condition. -/
def omnificGameCodes : Class.{u} :=
  fun z ↦ ∃ h : IsGameCode z, (GameCode.mk z h).IsOmnificInteger

/-- Membership in the omnific-code class is Conway's omnific-integer predicate on a game code. -/
theorem omnificGameCodes_iff (z : ZFSet.{u}) :
    omnificGameCodes z ↔ ∃ h : IsGameCode z, (GameCode.mk z h).IsOmnificInteger := (Iff.rfl)

/-- Every omnific code is numeric. -/
theorem omnificGameCodes_subset_numericGameCodes :
    omnificGameCodes.{u} ⊆ numericGameCodes.{u} := by
  intro z hz
  obtain ⟨h, hm⟩ := (omnificGameCodes_iff z).1 hz
  exact (numericGameCodes_iff z).2 ⟨h, hm.isNumeric⟩

namespace GameCode

/-- A game code belongs to the numeric class exactly when it is numeric. -/
theorem mem_numericGameCodes (x : GameCode.{u}) : numericGameCodes (x : ZFSet.{u}) ↔
    x.IsNumeric := by
  rw [numericGameCodes_iff]
  constructor
  · rintro ⟨h, hx⟩
    simpa only [mk_coe] using hx
  · intro hx
    exact ⟨x.isGameCode, by simpa only [mk_coe] using hx⟩

/-- A game code belongs to the omnific class exactly when it is an omnific code. -/
theorem mem_omnificGameCodes (x : GameCode.{u}) : omnificGameCodes (x : ZFSet.{u}) ↔
    x.IsOmnificInteger := by
  rw [omnificGameCodes_iff]
  constructor
  · rintro ⟨h, hx⟩
    simpa only [mk_coe] using hx
  · intro hx
    exact ⟨x.isGameCode, by simpa only [mk_coe] using hx⟩

end GameCode

namespace NumericGameCode

/-- Numeric codes with the same underlying game code are equal. -/
@[ext]
theorem ext {x y : NumericGameCode.{u}} (h : x.code = y.code) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The underlying ZFC set distinguishes literal numeric codes. -/
theorem coe_code_injective :
    Function.Injective (fun x : NumericGameCode.{u} ↦ (x.code : ZFSet.{u})) :=
  fun _ _ h ↦ ext (GameCode.ext h)

/-- Every typed numeric code belongs to the intrinsic ZFC class. -/
theorem mem_numericGameCodes (x : NumericGameCode.{u}) :
    numericGameCodes (x.code : ZFSet.{u}) := (GameCode.mem_numericGameCodes _).2 x.numeric

/-- Numeric game codes are not small, because their values cover all surreal numbers. -/
theorem not_small : ¬Small.{u} NumericGameCode.{u} := by
  intro h
  letI : Small.{u} NumericGameCode.{u} := h
  exact _root_.Surreal.not_small (small_of_surjective toSurreal_surjective)

end NumericGameCode

/-- The intrinsic numeric-code class consists exactly of the underlying sets of numeric codes. -/
theorem numericGameCodes_iff_exists (z : ZFSet.{u}) :
    numericGameCodes z ↔ ∃ c : NumericGameCode.{u}, (c.code : ZFSet.{u}) = z := by
  constructor
  · intro hz
    obtain ⟨h, hn⟩ := (numericGameCodes_iff z).1 hz
    exact ⟨⟨GameCode.mk z h, hn⟩, GameCode.coe_mk z h⟩
  · rintro ⟨c, rfl⟩
    exact c.mem_numericGameCodes

namespace OmnificCode

/-- Omnific codes with the same underlying game code are equal. -/
@[ext]
theorem ext {x y : OmnificCode.{u}} (h : x.code = y.code) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The underlying ZFC set distinguishes literal omnific codes. -/
theorem coe_code_injective :
    Function.Injective (fun x : OmnificCode.{u} ↦ (x.code : ZFSet.{u})) :=
  fun _ _ h ↦ ext (GameCode.ext h)

/-- Every typed omnific code belongs to the intrinsic ZFC class. -/
theorem mem_omnificGameCodes (x : OmnificCode.{u}) :
    omnificGameCodes (x.code : ZFSet.{u}) := (GameCode.mem_omnificGameCodes _).2 x.omnific

/-- Omnific game codes are not small, because their values cover all omnific integers. -/
theorem not_small : ¬Small.{u} OmnificCode.{u} := by
  intro h
  letI : Small.{u} OmnificCode.{u} := h
  exact _root_.Surreal.OmnificInteger.not_small (small_of_surjective value_surjective)

end OmnificCode

/-- The intrinsic omnific-code class consists exactly of the underlying sets of omnific codes. -/
theorem omnificGameCodes_iff_exists (z : ZFSet.{u}) :
    omnificGameCodes z ↔ ∃ c : OmnificCode.{u}, (c.code : ZFSet.{u}) = z := by
  constructor
  · intro hz
    obtain ⟨h, hn⟩ := (omnificGameCodes_iff z).1 hz
    exact ⟨⟨GameCode.mk z h, hn⟩, GameCode.coe_mk z h⟩
  · rintro ⟨c, rfl⟩
    exact c.mem_omnificGameCodes

private theorem class_ne_ofSet_of_not_small {α : Type (u + 1)} (f : α → ZFSet.{u})
    (hf : Function.Injective f) (C : Class.{u}) (hC : ∀ x, C (f x))
    (hα : ¬Small.{u} α) (s : ZFSet.{u}) : C ≠ Class.ofSet s := by
  intro h
  let g : α → s := fun x ↦ ⟨f x, by
    apply Class.coe_apply.1
    rw [← h]
    exact hC x⟩
  exact hα (small_of_injective (f := g) (fun _ _ hab ↦ hf (congrArg Subtype.val hab)))

/-- No ZFC set has exactly the numeric game codes as its elements. -/
theorem numericGameCodes_ne_ofSet (s : ZFSet.{u}) : numericGameCodes ≠ Class.ofSet s :=
  class_ne_ofSet_of_not_small _ NumericGameCode.coe_code_injective _
    NumericGameCode.mem_numericGameCodes NumericGameCode.not_small s

/-- Numeric game codes form a proper ZFC class, with a proper class of distinct surreal values. -/
theorem numericGameCodes_notMem_univ : numericGameCodes ∉ Class.univ.{u} := by
  intro h
  obtain ⟨s, hs⟩ := Class.mem_univ.1 h
  exact numericGameCodes_ne_ofSet s hs.symm

/-- No ZFC set has exactly the omnific game codes as its elements. -/
theorem omnificGameCodes_ne_ofSet (s : ZFSet.{u}) : omnificGameCodes ≠ Class.ofSet s :=
  class_ne_ofSet_of_not_small _ OmnificCode.coe_code_injective _
    OmnificCode.mem_omnificGameCodes OmnificCode.not_small s

/-- Omnific codes form a proper ZFC class, with a proper class of distinct omnific values. -/
theorem omnificGameCodes_notMem_univ : omnificGameCodes ∉ Class.univ.{u} := by
  intro h
  obtain ⟨s, hs⟩ := Class.mem_univ.1 h
  exact omnificGameCodes_ne_ofSet s hs.symm

namespace Surreal

/-- Distinct Conway-equivalence classes of numeric ZFC game codes do not form a small type. -/
theorem not_small : ¬Small.{u} Surreal.{u} := by
  intro h
  letI : Small.{u} Surreal.{u} := h
  exact _root_.Surreal.not_small (small_of_surjective toSurreal_surjective)

namespace OmnificInteger

/-- Distinct omnific values in the class presentation do not form a small type. -/
theorem not_small : ¬Small.{u} OmnificInteger.{u} := by
  intro h
  letI : Small.{u} OmnificInteger.{u} := h
  exact _root_.Surreal.OmnificInteger.not_small (small_of_surjective ringEquiv.surjective)

end OmnificInteger
end Surreal
end ZFSet
