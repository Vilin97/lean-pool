/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.ZFC.GameOperations
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Division
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.Order.Lattice

import Mathlib.Algebra.Order.Ring.InjSurj

/-!
# Surreal values of ZFC game codes

Numeric ZFC game codes are quotiented by Conway equivalence. The resulting ordered field is
identified with the surreal numbers, preserving the value of each set-coded Conway cut.
-/

universe u

public noncomputable section

namespace ZFSet

/-- A set-coded game satisfying Conway's numeric condition. -/
structure NumericGameCode where
  /-- The underlying ZFC code for the numeric game. -/
  code : GameCode.{u}
  numeric : code.IsNumeric

namespace NumericGameCode

/-- The numeric game obtained by decoding a numeric ZFC game code. -/
def toIGame (x : NumericGameCode.{u}) : IGame.{u} := x.code.toIGame

instance (x : NumericGameCode.{u}) : IGame.Numeric x.toIGame := by
  exact (GameCode.isNumeric_iff x.code).1 x.numeric

/-- The surreal value of a numeric ZFC game code. -/
def toSurreal (x : NumericGameCode.{u}) : _root_.Surreal.{u} := _root_.Surreal.mk x.toIGame

/-- Numerical equality of codes is Conway equivalence, not literal equality of ZFC sets. -/
def setoid : Setoid NumericGameCode.{u} where
  r x y := AntisymmRel (· ≤ ·) x.code y.code
  iseqv := ⟨fun _ ↦ .rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Two numeric codes have the same surreal value exactly when they are Conway equivalent. -/
theorem toSurreal_eq_iff (x y : NumericGameCode.{u}) :
    x.toSurreal = y.toSurreal ↔ AntisymmRel (· ≤ ·) x.code y.code := by
  rw [toSurreal, toSurreal, _root_.Surreal.mk_eq_mk]
  rfl

/-- Every surreal value has a numeric ZFC game code. -/
theorem toSurreal_surjective : Function.Surjective (toSurreal.{u}) := by
  intro x
  let c : NumericGameCode.{u} := ⟨GameCode.ofIGame x.out, by
    rw [GameCode.isNumeric_iff, GameCode.toIGame_ofIGame]
    infer_instance⟩
  refine ⟨c, ?_⟩
  let : IGame.Numeric (GameCode.ofIGame x.out).toIGame :=
    (GameCode.isNumeric_iff _).1 c.numeric
  change _root_.Surreal.mk (GameCode.ofIGame x.out).toIGame = x
  simp only [GameCode.toIGame_ofIGame, _root_.Surreal.out_eq]

end NumericGameCode

/-- The class presentation of surreal values: numeric ZFC game codes modulo Conway equality. -/
def Surreal : Type (u + 1) := Quotient NumericGameCode.setoid.{u}

namespace Surreal

/-- The value represented by a numeric ZFC game code. -/
def mk (x : GameCode.{u}) (hx : x.IsNumeric) : Surreal.{u} :=
  Quotient.mk _ (NumericGameCode.mk x hx)

/-- Evaluate a Conway-equivalence class of numeric ZFC codes in the surreal field. -/
def toSurreal : Surreal.{u} → _root_.Surreal.{u} :=
  Quotient.lift NumericGameCode.toSurreal fun x y h ↦
    (NumericGameCode.toSurreal_eq_iff x y).2 h

@[simp]
theorem toSurreal_mk (x : GameCode.{u}) (hx : x.IsNumeric) :
    toSurreal (mk x hx) = @ _root_.Surreal.mk x.toIGame
      ((GameCode.isNumeric_iff x).1 hx) := (rfl)

/-- Equality of class values is precisely Conway equivalence of their numeric codes. -/
theorem mk_eq_mk (x y : GameCode.{u}) (hx : x.IsNumeric) (hy : y.IsNumeric) :
    mk x hx = mk y hy ↔ AntisymmRel (· ≤ ·) x y := Quotient.eq

/-- Every class value is represented by a numeric ZFC game code. -/
theorem exists_mk (x : Surreal.{u}) : ∃ (c : GameCode.{u}) (hc : c.IsNumeric), mk c hc = x := by
  induction x using Quotient.inductionOn with
  | h c => exact ⟨c.code, c.numeric, rfl⟩

/-- Evaluation distinguishes all surreal values represented by the code class. -/
theorem toSurreal_injective : Function.Injective (toSurreal.{u}) := by
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | h x y =>
    intro h
    exact Quotient.sound ((NumericGameCode.toSurreal_eq_iff x y).1 h)

/-- The class presentation includes every surreal number. -/
theorem toSurreal_surjective : Function.Surjective (toSurreal.{u}) := by
  intro x
  obtain ⟨c, hc⟩ := NumericGameCode.toSurreal_surjective x
  exact ⟨mk c.code c.numeric, hc⟩

/-- The exact correspondence between class-coded surreal values and the surreal field. -/
def equiv : Surreal.{u} ≃ _root_.Surreal.{u} :=
  Equiv.ofBijective toSurreal ⟨toSurreal_injective, toSurreal_surjective⟩

@[simp]
theorem equiv_apply (x : Surreal.{u}) : equiv x = toSurreal x := (rfl)

instance : Field Surreal.{u} := equiv.field

instance : LinearOrder Surreal.{u} := by
  classical
  exact equiv.linearOrder

/-- Evaluation preserves the field operations on class values. -/
def ringEquiv : Surreal.{u} ≃+* _root_.Surreal.{u} := equiv.ringEquiv

@[simp]
theorem ringEquiv_apply (x : Surreal.{u}) : ringEquiv x = toSurreal x := (rfl)

@[simp]
theorem toSurreal_zero : toSurreal (0 : Surreal.{u}) = 0 := map_zero ringEquiv

@[simp]
theorem toSurreal_one : toSurreal (1 : Surreal.{u}) = 1 := map_one ringEquiv

@[simp]
theorem toSurreal_add (x y : Surreal.{u}) :
    toSurreal (x + y) = toSurreal x + toSurreal y := map_add ringEquiv x y

@[simp]
theorem toSurreal_mul (x y : Surreal.{u}) :
    toSurreal (x * y) = toSurreal x * toSurreal y := map_mul ringEquiv x y

@[simp]
theorem toSurreal_le_toSurreal (x y : Surreal.{u}) :
    toSurreal x ≤ toSurreal y ↔ x ≤ y := (Iff.rfl)

@[simp]
theorem toSurreal_lt_toSurreal (x y : Surreal.{u}) :
    toSurreal x < toSurreal y ↔ x < y := (Iff.rfl)

instance : IsStrictOrderedRing Surreal.{u} :=
  Function.Injective.isStrictOrderedRing toSurreal toSurreal_zero toSurreal_one
    toSurreal_add toSurreal_mul (toSurreal_le_toSurreal _ _) (toSurreal_lt_toSurreal _ _)

/-- Evaluation is an ordered ring equivalence between the two presentations of surreals. -/
def orderRingEquiv : Surreal.{u} ≃+*o _root_.Surreal.{u} where
  __ := ringEquiv
  map_le_map_iff' := toSurreal_le_toSurreal _ _

@[simp]
theorem orderRingEquiv_apply (x : Surreal.{u}) : orderRingEquiv x = toSurreal x := (rfl)

@[simp]
theorem toSurreal_neg (x : Surreal.{u}) : toSurreal (-x) = -toSurreal x :=
  map_neg ringEquiv x

@[simp]
theorem toSurreal_sub (x y : Surreal.{u}) :
    toSurreal (x - y) = toSurreal x - toSurreal y := map_sub ringEquiv x y

@[simp]
theorem mk_zero : mk (0 : GameCode.{u}) GameCode.isNumeric_zero = 0 := by
  apply toSurreal_injective
  simp only [toSurreal_mk, GameCode.toIGame_zero, _root_.Surreal.mk_zero, toSurreal_zero]

@[simp]
theorem mk_one : mk (1 : GameCode.{u}) GameCode.isNumeric_one = 1 := by
  apply toSurreal_injective
  simp only [toSurreal_mk, GameCode.toIGame_one, _root_.Surreal.mk_one, toSurreal_one]

@[simp]
theorem mk_neg (x : GameCode.{u}) (hx : x.IsNumeric) :
    mk (-x) hx.neg = -mk x hx := by
  let : IGame.Numeric x.toIGame := (GameCode.isNumeric_iff _).1 hx
  apply toSurreal_injective
  simp only [toSurreal_mk, GameCode.toIGame_neg, _root_.Surreal.mk_neg, toSurreal_neg]

@[simp]
theorem mk_add (x y : GameCode.{u}) (hx : x.IsNumeric) (hy : y.IsNumeric) :
    mk (x + y) (hx.add hy) = mk x hx + mk y hy := by
  let : IGame.Numeric x.toIGame := (GameCode.isNumeric_iff _).1 hx
  let : IGame.Numeric y.toIGame := (GameCode.isNumeric_iff _).1 hy
  apply toSurreal_injective
  simp only [toSurreal_mk, GameCode.toIGame_add, _root_.Surreal.mk_add, toSurreal_add]

@[simp]
theorem mk_sub (x y : GameCode.{u}) (hx : x.IsNumeric) (hy : y.IsNumeric) :
    mk (x - y) (hx.sub hy) = mk x hx - mk y hy := by
  let : IGame.Numeric x.toIGame := (GameCode.isNumeric_iff _).1 hx
  let : IGame.Numeric y.toIGame := (GameCode.isNumeric_iff _).1 hy
  apply toSurreal_injective
  simp only [toSurreal_mk, GameCode.toIGame_sub, _root_.Surreal.mk_sub, toSurreal_sub]

@[simp]
theorem mk_mul (x y : GameCode.{u}) (hx : x.IsNumeric) (hy : y.IsNumeric) :
    mk (x * y) (hx.mul hy) = mk x hx * mk y hy := by
  let : IGame.Numeric x.toIGame := (GameCode.isNumeric_iff _).1 hx
  let : IGame.Numeric y.toIGame := (GameCode.isNumeric_iff _).1 hy
  apply toSurreal_injective
  simp only [toSurreal_mk, GameCode.toIGame_mul, _root_.Surreal.mk_mul, toSurreal_mul]

end Surreal
end ZFSet
