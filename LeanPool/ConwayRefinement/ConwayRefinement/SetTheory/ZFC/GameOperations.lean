/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.ZFC.Game
public import LeanPool.ConwayRefinement.CombinatorialGames.Game.Classes

import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Multiplication

/-!
# Comparison and arithmetic of ZFC game codes

The coding equivalence transports comparison and the raw game operations. These are operations on
pregames: game equivalence is `AntisymmRel (· ≤ ·)`, and no ring structure is asserted on raw codes.
-/

universe u

public noncomputable section

open Set

namespace ZFSet.GameCode

/-- Encode a literal game as a valid ZFC game code. -/
def ofIGame (x : IGame.{u}) : GameCode.{u} := IGame.zfSetEquiv x

/-- Decode a valid ZFC game code as a literal game. -/
def toIGame (x : GameCode.{u}) : IGame.{u} := IGame.zfSetEquiv.symm x

@[simp]
theorem toIGame_ofIGame (x : IGame.{u}) : toIGame (ofIGame x) = x :=
  IGame.zfSetEquiv.symm_apply_apply x

@[simp]
theorem ofIGame_toIGame (x : GameCode.{u}) : ofIGame (toIGame x) = x :=
  IGame.zfSetEquiv.apply_symm_apply x

@[simp]
theorem coe_ofIGame (x : IGame.{u}) : (ofIGame x : ZFSet.{u}) = IGame.toZFSet x :=
  IGame.coe_zfSetEquiv x

@[simp]
theorem toZFSet_toIGame (x : GameCode.{u}) : IGame.toZFSet x.toIGame = (x : ZFSet.{u}) :=
  IGame.toZFSet_zfSetEquiv_symm x

/-- Decoding game codes is injective. -/
theorem toIGame_injective : Function.Injective (toIGame.{u}) :=
  IGame.zfSetEquiv.symm.injective

@[simp]
theorem toIGame_inj {x y : GameCode.{u}} : x.toIGame = y.toIGame ↔ x = y :=
  toIGame_injective.eq_iff

@[simp]
theorem ofIGame_inj {x y : IGame.{u}} : ofIGame x = ofIGame y ↔ x = y :=
  IGame.zfSetEquiv.injective.eq_iff

instance : Preorder GameCode.{u} := Preorder.lift toIGame

@[simp]
theorem toIGame_le_toIGame (x y : GameCode.{u}) : x.toIGame ≤ y.toIGame ↔ x ≤ y := (Iff.rfl)

@[simp]
theorem toIGame_lt_toIGame (x y : GameCode.{u}) : x.toIGame < y.toIGame ↔ x < y := (Iff.rfl)

@[simp]
theorem ofIGame_le_ofIGame (x y : IGame.{u}) : ofIGame x ≤ ofIGame y ↔ x ≤ y := by
  change toIGame (ofIGame x) ≤ toIGame (ofIGame y) ↔ x ≤ y
  simp

@[simp]
theorem ofIGame_lt_ofIGame (x y : IGame.{u}) : ofIGame x < ofIGame y ↔ x < y := by
  change toIGame (ofIGame x) < toIGame (ofIGame y) ↔ x < y
  simp

@[simp]
theorem toIGame_equiv_toIGame (x y : GameCode.{u}) : x.toIGame ≈ y.toIGame ↔ x ≈ y := (Iff.rfl)

instance : Zero GameCode.{u} := ⟨ofIGame 0⟩
instance : One GameCode.{u} := ⟨ofIGame 1⟩
instance : Neg GameCode.{u} := ⟨fun x ↦ ofIGame (-x.toIGame)⟩
instance : Add GameCode.{u} := ⟨fun x y ↦ ofIGame (x.toIGame + y.toIGame)⟩
instance : Sub GameCode.{u} := ⟨fun x y ↦ ofIGame (x.toIGame - y.toIGame)⟩
instance : Mul GameCode.{u} := ⟨fun x y ↦ ofIGame (x.toIGame * y.toIGame)⟩

@[simp] theorem toIGame_zero : (0 : GameCode.{u}).toIGame = 0 := toIGame_ofIGame _
@[simp] theorem toIGame_one : (1 : GameCode.{u}).toIGame = 1 := toIGame_ofIGame _

@[simp]
theorem toIGame_neg (x : GameCode.{u}) : (-x).toIGame = -x.toIGame := toIGame_ofIGame _

@[simp]
theorem toIGame_add (x y : GameCode.{u}) : (x + y).toIGame = x.toIGame + y.toIGame :=
  toIGame_ofIGame _

@[simp]
theorem toIGame_sub (x y : GameCode.{u}) : (x - y).toIGame = x.toIGame - y.toIGame :=
  toIGame_ofIGame _

@[simp]
theorem toIGame_mul (x y : GameCode.{u}) : (x * y).toIGame = x.toIGame * y.toIGame :=
  toIGame_ofIGame _

@[simp]
theorem ofIGame_neg (x : IGame.{u}) : ofIGame (-x) = -ofIGame x := by
  apply toIGame_injective
  simp

@[simp]
theorem ofIGame_add (x y : IGame.{u}) : ofIGame (x + y) = ofIGame x + ofIGame y := by
  apply toIGame_injective
  simp

@[simp]
theorem ofIGame_sub (x y : IGame.{u}) : ofIGame (x - y) = ofIGame x - ofIGame y := by
  apply toIGame_injective
  simp

@[simp]
theorem ofIGame_mul (x y : IGame.{u}) : ofIGame (x * y) = ofIGame x * ofIGame y := by
  apply toIGame_injective
  simp

/-- A code is numeric when all its game positions are numbers in Conway's sense. -/
def IsNumeric (x : GameCode.{u}) : Prop := IGame.Numeric x.toIGame

theorem isNumeric_iff (x : GameCode.{u}) : IsNumeric x ↔ IGame.Numeric x.toIGame := (Iff.rfl)

@[simp]
theorem isNumeric_ofIGame (x : IGame.{u}) : IsNumeric (ofIGame x) ↔ IGame.Numeric x := by
  simp [IsNumeric]

@[simp]
theorem isNumeric_zero : IsNumeric (0 : GameCode.{u}) := by
  simp [IsNumeric]

@[simp]
theorem isNumeric_one : IsNumeric (1 : GameCode.{u}) := by
  simp [IsNumeric]

/-- Negation preserves numeric game codes. -/
theorem IsNumeric.neg {x : GameCode.{u}} (h : IsNumeric x) : IsNumeric (-x) := by
  letI : IGame.Numeric x.toIGame := (isNumeric_iff x).1 h
  simpa [IsNumeric] using (inferInstance : IGame.Numeric (-x.toIGame))

/-- Addition preserves numeric game codes. -/
theorem IsNumeric.add {x y : GameCode.{u}} (hx : IsNumeric x) (hy : IsNumeric y) :
    IsNumeric (x + y) := by
  letI : IGame.Numeric x.toIGame := (isNumeric_iff x).1 hx
  letI : IGame.Numeric y.toIGame := (isNumeric_iff y).1 hy
  simpa [IsNumeric] using (inferInstance : IGame.Numeric (x.toIGame + y.toIGame))

/-- Subtraction preserves numeric game codes. -/
theorem IsNumeric.sub {x y : GameCode.{u}} (hx : IsNumeric x) (hy : IsNumeric y) :
    IsNumeric (x - y) := by
  letI : IGame.Numeric x.toIGame := (isNumeric_iff x).1 hx
  letI : IGame.Numeric y.toIGame := (isNumeric_iff y).1 hy
  simpa [IsNumeric] using (inferInstance : IGame.Numeric (x.toIGame - y.toIGame))

/-- Multiplication preserves numeric game codes. -/
theorem IsNumeric.mul {x y : GameCode.{u}} (hx : IsNumeric x) (hy : IsNumeric y) :
    IsNumeric (x * y) := by
  letI : IGame.Numeric x.toIGame := (isNumeric_iff x).1 hx
  letI : IGame.Numeric y.toIGame := (isNumeric_iff y).1 hy
  simpa [IsNumeric] using (inferInstance : IGame.Numeric (x.toIGame * y.toIGame))

/-- The option codes for one player, with no identification of equivalent options. -/
def moves (p : Player) (x : GameCode.{u}) : Set GameCode.{u} :=
  ofIGame '' x.toIGame.moves p

instance (p : Player) (x : GameCode.{u}) : Small.{u} (x.moves p) :=
  inferInstanceAs (Small.{u} (ofIGame '' x.toIGame.moves p))

@[simp]
theorem mem_moves {p : Player} {x y : GameCode.{u}} :
    y ∈ x.moves p ↔ y.toIGame ∈ x.toIGame.moves p := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro h
    exact ⟨y.toIGame, h, ofIGame_toIGame y⟩

/-- Form a code from small left- and right-option sets. -/
def ofSets (s t : Set GameCode.{u}) [Small.{u} s] [Small.{u} t] : GameCode.{u} :=
  ofIGame !{toIGame '' s | toIGame '' t}

@[simp]
theorem toIGame_ofSets (s t : Set GameCode.{u}) [Small.{u} s] [Small.{u} t] :
    (ofSets s t).toIGame = !{toIGame '' s | toIGame '' t} := toIGame_ofIGame _

@[simp]
theorem moves_ofSets_left (s t : Set GameCode.{u}) [Small.{u} s] [Small.{u} t] :
    (ofSets s t).moves Player.left = s := by
  simp [moves, image_image]

@[simp]
theorem moves_ofSets_right (s t : Set GameCode.{u}) [Small.{u} s] [Small.{u} t] :
    (ofSets s t).moves Player.right = t := by
  simp [moves, image_image]

/-- The ZFC set of option codes for one player. -/
def optionCodes (p : Player) (x : GameCode.{u}) : ZFSet.{u} :=
  ZFSet.range fun y : x.moves p ↦ (y.1 : ZFSet.{u})

@[simp]
theorem mem_optionCodes {p : Player} {x : GameCode.{u}} {z : ZFSet.{u}} :
    z ∈ optionCodes p x ↔ ∃ y ∈ x.moves p, (y : ZFSet.{u}) = z := by
  simp [optionCodes]

/-- A code is an option exactly when its underlying set belongs to the corresponding option set. -/
theorem coe_mem_optionCodes {p : Player} {x y : GameCode.{u}} :
    (y : ZFSet.{u}) ∈ optionCodes p x ↔ y ∈ x.moves p := by
  rw [mem_optionCodes]
  constructor
  · rintro ⟨z, hz, h⟩
    exact (GameCode.ext h) ▸ hz
  · intro h
    exact ⟨y, h, rfl⟩

/-- The intrinsic option sets agree with the components of the pregame encoding. -/
theorem optionCodes_eq_optionsZFSet (p : Player) (x : GameCode.{u}) :
    optionCodes p x = IGame.optionsZFSet p x.toIGame := by
  apply ZFSet.ext
  intro z
  rw [mem_optionCodes, IGame.mem_optionsZFSet]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y.toIGame, mem_moves.1 hy, (toZFSet_toIGame y).trans h⟩
  · rintro ⟨y, hy, h⟩
    refine ⟨ofIGame y, ?_, ?_⟩
    · simpa using hy
    · simpa using h

/-- A code's Kuratowski-pair components are exactly its option sets. -/
theorem coe_eq_pair (x : GameCode.{u}) :
    (x : ZFSet.{u}) = ZFSet.pair (optionCodes Player.left x) (optionCodes Player.right x) := by
  rw [optionCodes_eq_optionsZFSet, optionCodes_eq_optionsZFSet, ← IGame.toZFSet_eq_pair]
  exact (toZFSet_toIGame x).symm

/-- Membership in an option set can be read directly from the code's ordered-pair components. -/
theorem mem_moves_of_coe_eq_pair {x y : GameCode.{u}} {L R : ZFSet.{u}}
    (h : (x : ZFSet.{u}) = ZFSet.pair L R) (p : Player) :
    y ∈ x.moves p ↔ (y : ZFSet.{u}) ∈ Player.cases L R p := by
  obtain ⟨hL, hR⟩ := ZFSet.pair_inj.1 ((coe_eq_pair x).symm.trans h)
  cases p
  · rw [← hL]
    exact coe_mem_optionCodes.symm
  · rw [← hR]
    exact coe_mem_optionCodes.symm

/-- Forming a game code from option sets produces their intrinsic Kuratowski ordered pair. -/
theorem coe_ofSets (s t : Set GameCode.{u}) [Small.{u} s] [Small.{u} t] :
    (ofSets s t : ZFSet.{u}) = ZFSet.pair
      (ZFSet.range fun y : s ↦ (y.1 : ZFSet.{u}))
      (ZFSet.range fun y : t ↦ (y.1 : ZFSet.{u})) := by
  rw [coe_eq_pair]
  apply congrArg₂ ZFSet.pair <;> apply ZFSet.ext <;> intro z <;> simp

/-- Conway comparison is the recursive comparison of the two option sets. -/
theorem le_iff_forall_not_le (x y : GameCode.{u}) :
    x ≤ y ↔ (∀ z ∈ x.moves Player.left, ¬ y ≤ z) ∧
      (∀ z ∈ y.moves Player.right, ¬ z ≤ x) := by
  rw [← toIGame_le_toIGame, IGame.le_iff_forall_lf]
  simp only [moves, Set.forall_mem_image, ← toIGame_le_toIGame, toIGame_ofIGame]

/-- Numeric codes have numeric options, with every left option below every right option. -/
theorem isNumeric_iff_options (x : GameCode.{u}) :
    IsNumeric x ↔
      (∀ y ∈ x.moves Player.left, ∀ z ∈ x.moves Player.right, y < z) ∧
      (∀ p, ∀ y ∈ x.moves p, IsNumeric y) := by
  rw [isNumeric_iff, IGame.numeric_def]
  simp only [moves, Set.forall_mem_image, ofIGame_lt_ofIGame, isNumeric_ofIGame]

@[simp]
theorem moves_neg (p : Player) (x : GameCode.{u}) :
    (-x).moves p = Neg.neg '' x.moves (-p) := by
  simp only [moves, toIGame_neg, IGame.moves_neg, ← Set.image_neg_eq_neg, image_image]
  exact Set.image_congr fun a _ ↦ ofIGame_neg a

@[simp]
theorem moves_add (p : Player) (x y : GameCode.{u}) :
    (x + y).moves p = (· + y) '' x.moves p ∪ (x + ·) '' y.moves p := by
  simp [moves, image_union, image_image]

/-- The usual option expression for the product of two game codes. -/
def mulOption (x y a b : GameCode.{u}) : GameCode.{u} := a * y + x * b - a * b

@[simp]
theorem toIGame_mulOption (x y a b : GameCode.{u}) :
    (mulOption x y a b).toIGame = IGame.mulOption x.toIGame y.toIGame a.toIGame b.toIGame := by
  simp [mulOption, IGame.mulOption]

@[simp]
theorem moves_mul (p : Player) (x y : GameCode.{u}) :
    (x * y).moves p = (fun a ↦ mulOption x y a.1 a.2) ''
      (x.moves Player.left ×ˢ y.moves p ∪ x.moves Player.right ×ˢ y.moves (-p)) := by
  simp [moves, mulOption, IGame.mulOption, image_union, prod_image_image_eq, image_image]

end ZFSet.GameCode
