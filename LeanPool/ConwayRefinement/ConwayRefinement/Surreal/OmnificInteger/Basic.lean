/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Division
public import Mathlib.Algebra.Ring.Subring.Defs
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.Round

import LeanPool.ConwayRefinement.CombinatorialGames.Tactic.GameCmp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Omnific integers

Conway defines a surreal number `x` to be an omnific integer when
`x = {x - 1 | x + 1}`. This file uses that fixed-point equation as the direct definition and
proves Conway's closure statements, so the resulting carrier is a subring of the surreal numbers.
The proofs use the exact option formulae for addition and multiplication of numeric pregames.

Conway's normal-form criterion, and the equivalent criterion recalled in LM24, Section 1.1, is a
theorem about this carrier rather than its definition. The pinned CombinatorialGames revision does
not yet construct the full surreal-to-Hahn normal-form map, so this file does not assume such a map
or use an unrelated Hahn-series presentation as the definition.

The source is *On Numbers and Games*, pages 45--46: the definition preceding Theorem 30, Theorem 30
for ring closure, and Theorem 31 for the later normal-form characterization.
-/

universe u

public noncomputable section

namespace Surreal

namespace OmnificInteger

private def cutGame (x : IGame.{u}) : IGame.{u} :=
  !{{x - 1} | {x + 1}}

private instance cutGameNumeric (x : IGame.{u}) [IGame.Numeric x] :
    IGame.Numeric (cutGame x) := by
  rw [IGame.numeric_def]
  constructor
  · simp only [cutGame, IGame.leftMoves_ofSets, IGame.rightMoves_ofSets,
      Set.mem_singleton_iff, forall_eq]
    rw [← Surreal.mk_lt_mk]
    simp only [Surreal.mk_sub, Surreal.mk_add, Surreal.mk_one]
    simp [sub_eq_add_neg, add_comm]
  · intro p y hy
    cases p with
    | left =>
        simp only [cutGame, IGame.leftMoves_ofSets, Set.mem_singleton_iff] at hy
        subst y
        infer_instance
    | right =>
        simp only [cutGame, IGame.rightMoves_ofSets, Set.mem_singleton_iff] at hy
        subst y
        infer_instance

private def IsOmnificGame (x : IGame.{u}) : Prop :=
  x ≈ cutGame x

private theorem isOmnificGame_zero : IsOmnificGame (0 : IGame.{u}) := by
  apply AntisymmRel.symm
  rw [← IGame.fits_zero_iff_equiv]
  simp [IGame.Fits, cutGame]

private theorem isOmnificGame_one : IsOmnificGame (1 : IGame.{u}) := by
  apply AntisymmRel.symm
  apply IGame.equiv_one_of_fits
  · rw [IGame.Fits]
    constructor
    · intro z hz
      simp only [cutGame, IGame.leftMoves_ofSets, Set.mem_singleton_iff] at hz
      subst z
      game_cmp
    · intro z hz
      simp only [cutGame, IGame.rightMoves_ofSets, Set.mem_singleton_iff] at hz
      subst z
      game_cmp
  · intro h
    have hz : ((1 : IGame.{u}) - 1) ⧏ cutGame 1 :=
      IGame.left_lf (by simp [cutGame])
    exact hz (h.1.trans (IGame.sub_self_equiv 1).2)

private theorem neg_cutGame (x : IGame.{u}) : -cutGame x = cutGame (-x) := by
  simp only [cutGame, IGame.neg_ofSets]
  congr! 2
  · simp [sub_eq_add_neg, add_comm]
  · simp [sub_eq_add_neg, add_comm]

private theorem IsOmnificGame.neg {x : IGame.{u}} (hx : IsOmnificGame x) :
    IsOmnificGame (-x) := by
  rw [IsOmnificGame, ← neg_cutGame]
  exact IGame.neg_congr hx

private theorem cutGame_add_cutGame_equiv {x y : IGame.{u}}
    [IGame.Numeric x] [IGame.Numeric y]
    (hx : IsOmnificGame x) (hy : IsOmnificGame y) :
    cutGame x + cutGame y ≈ cutGame (x + y) := by
  have hx' : Game.mk !{{x - 1} | {x + 1}} = Game.mk x := (Game.mk_eq hx).symm
  have hy' : Game.mk !{{y - 1} | {y + 1}} = Game.mk y := (Game.mk_eq hy).symm
  apply Game.mk_eq_mk.mp
  simp only [cutGame, IGame.ofSets_add_ofSets, Game.mk_ofSets, Set.image_union,
    Set.image_singleton]
  simp only [Game.mk_add, Game.mk_sub, Game.mk_one, hx', hy']
  abel_nf
  congr <;> simp

private theorem IsOmnificGame.add {x y : IGame.{u}} [IGame.Numeric x] [IGame.Numeric y]
    (hx : IsOmnificGame x) (hy : IsOmnificGame y) : IsOmnificGame (x + y) := by
  exact (IGame.add_congr hx hy).trans (cutGame_add_cutGame_equiv hx hy)

private theorem mulOption_cutGame_equiv {x y s t : IGame.{u}}
    [IGame.Numeric x] [IGame.Numeric y] [IGame.Numeric s] [IGame.Numeric t]
    (hx : IsOmnificGame x) (hy : IsOmnificGame y) :
    IGame.mulOption !{{x - 1} | {x + 1}} !{{y - 1} | {y + 1}}
      (x + s) (y + t) ≈ x * y - s * t := by
  letI : IGame.Numeric !{{x - 1} | {x + 1}} := cutGameNumeric x
  letI : IGame.Numeric !{{y - 1} | {y + 1}} := cutGameNumeric y
  have hx' : Surreal.mk !{{x - 1} | {x + 1}} = Surreal.mk x := (Surreal.mk_eq hx).symm
  have hy' : Surreal.mk !{{y - 1} | {y + 1}} = Surreal.mk y := (Surreal.mk_eq hy).symm
  apply Surreal.mk_eq_mk.mp
  simp only [IGame.mulOption, Surreal.mk_sub, Surreal.mk_add, Surreal.mk_mul]
  rw [hx', hy']
  ring

private theorem cutGame_mul_cutGame_equiv {x y : IGame.{u}}
    [IGame.Numeric x] [IGame.Numeric y]
    (hx : IsOmnificGame x) (hy : IsOmnificGame y) :
    cutGame x * cutGame y ≈ cutGame (x * y) := by
  rw [cutGame, cutGame, IGame.ofSets_mul_ofSets]
  apply IGame.equiv_of_exists
  · intro a ha
    simp only [IGame.leftMoves_ofSets, Set.mem_image, Set.mem_union, Set.mem_prod,
      Set.mem_singleton_iff, Prod.exists] at ha
    obtain ⟨a₁, b₁, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), rfl⟩ := ha
    · refine ⟨x * y - 1, by simp [cutGame], ?_⟩
      simpa [sub_eq_add_neg] using
        mulOption_cutGame_equiv (x := x) (y := y) (s := (-1)) (t := (-1)) hx hy
    · refine ⟨x * y - 1, by simp [cutGame], ?_⟩
      simpa using mulOption_cutGame_equiv (x := x) (y := y) (s := 1) (t := 1) hx hy
  · intro a ha
    simp only [IGame.rightMoves_ofSets, Set.mem_image, Set.mem_union, Set.mem_prod,
      Set.mem_singleton_iff, Prod.exists] at ha
    obtain ⟨a₁, b₁, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), rfl⟩ := ha
    · refine ⟨x * y + 1, by simp [cutGame], ?_⟩
      simpa [sub_eq_add_neg] using
        mulOption_cutGame_equiv (x := x) (y := y) (s := (-1)) (t := 1) hx hy
    · refine ⟨x * y + 1, by simp [cutGame], ?_⟩
      simpa [sub_eq_add_neg] using
        mulOption_cutGame_equiv (x := x) (y := y) (s := 1) (t := (-1)) hx hy
  · intro b hb
    simp only [cutGame, IGame.leftMoves_ofSets, Set.mem_singleton_iff] at hb
    subst b
    refine ⟨IGame.mulOption !{{x - 1} | {x + 1}} !{{y - 1} | {y + 1}}
      (x - 1) (y - 1), ?_, ?_⟩
    · simp
    · simpa [cutGame, sub_eq_add_neg] using
        mulOption_cutGame_equiv (x := x) (y := y) (s := (-1)) (t := (-1)) hx hy
  · intro b hb
    simp only [cutGame, IGame.rightMoves_ofSets, Set.mem_singleton_iff] at hb
    subst b
    refine ⟨IGame.mulOption !{{x - 1} | {x + 1}} !{{y - 1} | {y + 1}}
      (x - 1) (y + 1), ?_, ?_⟩
    · simp
    · simpa [cutGame, sub_eq_add_neg] using
        mulOption_cutGame_equiv (x := x) (y := y) (s := (-1)) (t := 1) hx hy

private theorem IsOmnificGame.mul {x y : IGame.{u}} [IGame.Numeric x] [IGame.Numeric y]
    (hx : IsOmnificGame x) (hy : IsOmnificGame y) : IsOmnificGame (x * y) := by
  exact (IGame.Numeric.mul_congr hx hy).trans (cutGame_mul_cutGame_equiv hx hy)

private theorem not_isOmnificGame_half : ¬IsOmnificGame (IGame.half : IGame.{u}) := by
  intro hhalf
  have hcut : cutGame (IGame.half : IGame.{u}) ≈ 0 :=
    IGame.fits_zero_iff_equiv.mp (by
      rw [IGame.Fits]
      constructor <;> intro z hz <;>
        simp only [cutGame, IGame.leftMoves_ofSets, IGame.rightMoves_ofSets,
          Set.mem_singleton_iff] at hz <;>
        subst z <;> game_cmp)
  exact IGame.zero_lt_half.not_ge (hhalf.trans hcut).1

end OmnificInteger

/-- The singleton cut `{x - 1 | x + 1}` associated with a surreal number `x`. -/
def omnificIntegerCut (x : Surreal.{u}) : Surreal.{u} :=
  !{{x - 1} | {x + 1}}' (by
    simp only [Set.mem_singleton_iff]
    intro a ha b hb
    subst a
    subst b
    simp [sub_eq_add_neg])

/-- Conway's omnific-integer cut is definitionally the singleton cut at distance one. -/
theorem omnificIntegerCut_eq (x : Surreal.{u}) :
    omnificIntegerCut x =
      !{{x - 1} | {x + 1}}' (by
        simp only [Set.mem_singleton_iff]
        rintro _ rfl _ rfl
        simp [sub_eq_add_neg]) :=
  (rfl)

/-- A surreal number is an omnific integer when it equals `{x - 1 | x + 1}`. -/
def IsOmnificInteger (x : Surreal.{u}) : Prop :=
  x = omnificIntegerCut x

/-- The defining fixed-point equation for an omnific integer. -/
theorem isOmnificInteger_iff {x : Surreal.{u}} :
    IsOmnificInteger x ↔ x = omnificIntegerCut x :=
  Iff.rfl

/-- Conway's singleton-cut definition of an omnific integer is equivalently fixedness under
rounding with radius one. -/
theorem isOmnificInteger_iff_round_one {x : Surreal.{u}} :
    IsOmnificInteger x ↔ x.round 1 = x := by
  rw [IsOmnificInteger, omnificIntegerCut, round_of_pos zero_lt_one]
  exact eq_comm

open OmnificInteger

private theorem omnificIntegerCut_mk (x : IGame.{u}) [IGame.Numeric x] :
    omnificIntegerCut (Surreal.mk x) = Surreal.mk (cutGame x) := by
  rw [omnificIntegerCut]
  symm
  letI : IGame.Numeric !{{x - 1} | {x + 1}} := cutGameNumeric x
  change Surreal.mk !{{x - 1} | {x + 1}} = _
  rw [Surreal.mk_ofSets]
  congr! 2 <;> simp

/-- The omnific-integer predicate expressed on a numeric pregame representative. -/
theorem isOmnificInteger_mk_iff (x : IGame.{u}) [IGame.Numeric x] :
    IsOmnificInteger (Surreal.mk x) ↔
      x ≈ !{{x - 1} | {x + 1}} := by
  rw [IsOmnificInteger, omnificIntegerCut_mk, Surreal.mk_eq_mk]
  rfl

/-- Zero is an omnific integer. -/
theorem isOmnificInteger_zero : IsOmnificInteger (0 : Surreal.{u}) := by
  rw [← Surreal.mk_zero, isOmnificInteger_mk_iff]
  exact OmnificInteger.isOmnificGame_zero

/-- One is an omnific integer. -/
theorem isOmnificInteger_one : IsOmnificInteger (1 : Surreal.{u}) := by
  rw [← Surreal.mk_one, isOmnificInteger_mk_iff]
  exact OmnificInteger.isOmnificGame_one

/-- The negative of an omnific integer is an omnific integer. -/
theorem IsOmnificInteger.neg {x : Surreal.{u}} (hx : IsOmnificInteger x) :
    IsOmnificInteger (-x) := by
  induction x using Surreal.ind with
  | mk x =>
      rw [← Surreal.mk_neg, isOmnificInteger_mk_iff]
      exact OmnificInteger.IsOmnificGame.neg ((isOmnificInteger_mk_iff x).mp hx)

/-- The sum of two omnific integers is an omnific integer. -/
theorem IsOmnificInteger.add {x y : Surreal.{u}}
    (hx : IsOmnificInteger x) (hy : IsOmnificInteger y) : IsOmnificInteger (x + y) := by
  induction x using Surreal.ind with
  | mk x =>
      induction y using Surreal.ind with
      | mk y =>
          rw [← Surreal.mk_add, isOmnificInteger_mk_iff]
          exact OmnificInteger.IsOmnificGame.add
            ((isOmnificInteger_mk_iff x).mp hx) ((isOmnificInteger_mk_iff y).mp hy)

/-- The product of two omnific integers is an omnific integer. -/
theorem IsOmnificInteger.mul {x y : Surreal.{u}}
    (hx : IsOmnificInteger x) (hy : IsOmnificInteger y) : IsOmnificInteger (x * y) := by
  induction x using Surreal.ind with
  | mk x =>
      induction y using Surreal.ind with
      | mk y =>
          rw [← Surreal.mk_mul, isOmnificInteger_mk_iff]
          exact OmnificInteger.IsOmnificGame.mul
            ((isOmnificInteger_mk_iff x).mp hx) ((isOmnificInteger_mk_iff y).mp hy)

/-- Omnific integers are closed under subtraction. -/
theorem IsOmnificInteger.sub {x y : Surreal.{u}}
    (hx : IsOmnificInteger x) (hy : IsOmnificInteger y) :
    IsOmnificInteger (x - y) :=
  hx.add hy.neg

/-- The subring of surreal numbers satisfying Conway's omnific-integer equation. -/
def omnificIntegers : Subring Surreal.{u} where
  carrier := {x | IsOmnificInteger x}
  zero_mem' := isOmnificInteger_zero
  one_mem' := isOmnificInteger_one
  add_mem' := IsOmnificInteger.add
  neg_mem' := IsOmnificInteger.neg
  mul_mem' := IsOmnificInteger.mul

/-- Membership in `omnificIntegers` is Conway's omnific-integer predicate. -/
@[simp]
theorem mem_omnificIntegers {x : Surreal.{u}} :
    x ∈ omnificIntegers ↔ IsOmnificInteger x :=
  Iff.rfl

/-- Omnific integers, with the ring structure inherited from the surreal numbers. -/
abbrev OmnificInteger := ↥(omnificIntegers : Subring Surreal.{u})

/-- Every natural number is an omnific integer. -/
@[simp]
theorem IsOmnificInteger.natCast (n : ℕ) :
    IsOmnificInteger (n : Surreal.{u}) :=
  mem_omnificIntegers.mp (n : OmnificInteger.{u}).2

/-- Every integer is an omnific integer. -/
@[simp]
theorem IsOmnificInteger.intCast (n : ℤ) :
    IsOmnificInteger (n : Surreal.{u}) :=
  mem_omnificIntegers.mp (n : OmnificInteger.{u}).2

/-- The surreal number `2⁻¹` is not an omnific integer. -/
theorem two_inv_not_mem_omnificIntegers :
    (2 : Surreal.{u})⁻¹ ∉ omnificIntegers := by
  rw [← IGame.mk_half, mem_omnificIntegers, isOmnificInteger_mk_iff]
  exact OmnificInteger.not_isOmnificGame_half

end Surreal
