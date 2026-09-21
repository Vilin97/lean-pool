/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Basic
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Basic

/-!
# The omnific-integer class

An omnific code is numeric and Conway equivalent to the singleton cut `{x - 1 | x + 1}`.
The corresponding class values form a subring, identified exactly with the cut-defined omnific
integers. Equality here is equality of numeric values, not equality of their codes.
-/

universe u

public noncomputable section

namespace ZFSet
namespace GameCode

/-- Conway's omnific-integer condition on a numeric set-coded game. -/
def IsOmnificInteger (x : GameCode.{u}) : Prop :=
  x.IsNumeric ∧ AntisymmRel (· ≤ ·) x (ofSets {x - 1} {x + 1})

/-- An omnific game code is numeric. -/
theorem IsOmnificInteger.isNumeric {x : GameCode.{u}} (h : x.IsOmnificInteger) : x.IsNumeric :=
  h.1

/-- The code condition is precisely fixedness under Conway's defining singleton cut. -/
theorem isOmnificInteger_iff (x : GameCode.{u}) : x.IsOmnificInteger ↔
    x.IsNumeric ∧ AntisymmRel (· ≤ ·) x (ofSets {x - 1} {x + 1}) := (Iff.rfl)

/-- The set-code condition agrees with the actual omnific-integer predicate. -/
theorem isOmnificInteger_iff_toSurreal (x : GameCode.{u}) (hx : x.IsNumeric) :
    x.IsOmnificInteger ↔ _root_.Surreal.IsOmnificInteger (Surreal.toSurreal (Surreal.mk x hx)) := by
  letI : IGame.Numeric x.toIGame := (isNumeric_iff _).1 hx
  rw [isOmnificInteger_iff, and_iff_right hx, Surreal.toSurreal_mk,
    _root_.Surreal.isOmnificInteger_mk_iff]
  rw [← toIGame_equiv_toIGame]
  simp only [toIGame_ofSets, Set.image_singleton, toIGame_sub, toIGame_add, toIGame_one]

end GameCode

namespace Surreal

/-- A class value is omnific when a numeric code satisfies Conway's singleton-cut equation. -/
def IsOmnificInteger (x : Surreal.{u}) : Prop :=
  ∃ (c : GameCode.{u}) (hc : c.IsNumeric), mk c hc = x ∧ c.IsOmnificInteger

/-- The class and library predicates select exactly the same omnific integers. -/
theorem isOmnificInteger_iff (x : Surreal.{u}) :
    x.IsOmnificInteger ↔ _root_.Surreal.IsOmnificInteger x.toSurreal := by
  constructor
  · rintro ⟨c, hc, rfl, h⟩
    exact (GameCode.isOmnificInteger_iff_toSurreal c hc).1 h
  · intro h
    obtain ⟨c, hc, rfl⟩ := exists_mk x
    exact ⟨c, hc, rfl, (GameCode.isOmnificInteger_iff_toSurreal c hc).2 h⟩

/-- The subring of class values satisfying Conway's omnific-integer equation. -/
def omnificIntegers : Subring Surreal.{u} where
  carrier := {x | x.IsOmnificInteger}
  zero_mem' := (isOmnificInteger_iff _).2 (by
    rw [toSurreal_zero]
    exact _root_.Surreal.isOmnificInteger_zero)
  one_mem' := (isOmnificInteger_iff _).2 (by
    rw [toSurreal_one]
    exact _root_.Surreal.isOmnificInteger_one)
  add_mem' hx hy := (isOmnificInteger_iff _).2 (by
    rw [toSurreal_add]
    exact ((isOmnificInteger_iff _).1 hx).add ((isOmnificInteger_iff _).1 hy))
  neg_mem' hx := (isOmnificInteger_iff _).2 (by
    rw [toSurreal_neg]
    exact ((isOmnificInteger_iff _).1 hx).neg)
  mul_mem' hx hy := (isOmnificInteger_iff _).2 (by
    rw [toSurreal_mul]
    exact ((isOmnificInteger_iff _).1 hx).mul ((isOmnificInteger_iff _).1 hy))

@[simp]
theorem mem_omnificIntegers (x : Surreal.{u}) :
    x ∈ omnificIntegers ↔ x.IsOmnificInteger := (Iff.rfl)

/-- The class presentation of Conway's omnific-integer ring. -/
abbrev OmnificInteger := ↥(omnificIntegers : Subring Surreal.{u})

namespace OmnificInteger

/-- Evaluate an omnific class value in the library's omnific-integer ring. -/
def toOmnificInteger (x : OmnificInteger.{u}) : _root_.Surreal.OmnificInteger.{u} :=
  ⟨toSurreal x, _root_.Surreal.mem_omnificIntegers.2
    ((isOmnificInteger_iff _).1 ((mem_omnificIntegers _).1 x.2))⟩

@[simp]
theorem coe_toOmnificInteger (x : OmnificInteger.{u}) :
    (toOmnificInteger x : _root_.Surreal.{u}) = toSurreal (x : Surreal.{u}) := (rfl)

/-- An exact equivalence of omnific-integer rings, covering all elements and witnesses. -/
def ringEquiv : OmnificInteger.{u} ≃+* _root_.Surreal.OmnificInteger.{u} where
  toFun := toOmnificInteger
  invFun x := ⟨equiv.symm x, (mem_omnificIntegers _).2 ((isOmnificInteger_iff _).2 (by
    simpa only [← equiv_apply, equiv.apply_symm_apply] using
      (_root_.Surreal.mem_omnificIntegers.1 x.2)))⟩
  left_inv x := by
    apply Subtype.ext
    change equiv.symm (toSurreal (x : Surreal.{u})) = (x : Surreal.{u})
    rw [← equiv_apply, equiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    change toSurreal (equiv.symm (x : _root_.Surreal.{u})) = (x : _root_.Surreal.{u})
    rw [← equiv_apply, equiv.apply_symm_apply]
  map_add' x y := Subtype.ext (toSurreal_add x y)
  map_mul' x y := Subtype.ext (toSurreal_mul x y)

@[simp]
theorem ringEquiv_apply (x : OmnificInteger.{u}) : ringEquiv x = toOmnificInteger x := (rfl)

@[simp]
theorem toSurreal_coe_ringEquiv_symm (x : _root_.Surreal.OmnificInteger.{u}) :
    toSurreal (ringEquiv.symm x : Surreal.{u}) = (x : _root_.Surreal.{u}) := by
  simpa only [ringEquiv_apply, coe_toOmnificInteger] using
    congrArg (fun y : _root_.Surreal.OmnificInteger.{u} ↦ (y : _root_.Surreal.{u}))
      (ringEquiv.apply_symm_apply x)

/-- The omnific-ring comparison also preserves order. -/
def orderRingEquiv : OmnificInteger.{u} ≃+*o _root_.Surreal.OmnificInteger.{u} where
  __ := ringEquiv
  map_le_map_iff' := toSurreal_le_toSurreal _ _

@[simp]
theorem orderRingEquiv_apply (x : OmnificInteger.{u}) :
    orderRingEquiv x = toOmnificInteger x := (rfl)

end OmnificInteger
end Surreal
end ZFSet
