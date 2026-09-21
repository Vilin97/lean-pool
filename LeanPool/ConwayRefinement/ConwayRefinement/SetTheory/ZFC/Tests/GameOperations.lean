/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.ZFC.GameOperations

/-!
# ZFC game-operation interface checks

These checks distinguish Conway comparison from a vacuous relation, numeric codes from arbitrary
game codes, and literal pregame equality from equality of game values.
-/

universe u

noncomputable section

open ZFSet.GameCode

example (x y : ZFSet.GameCode.{u}) :
    (x + y * x).toIGame = x.toIGame + y.toIGame * x.toIGame := by
  simp

example (x y : ZFSet.GameCode.{u}) (hx : IsNumeric x) (hy : IsNumeric y) :
    IsNumeric (-x + y * x) := hx.neg.add (hy.mul hx)

example : (0 : ZFSet.GameCode.{u}) < 1 := by
  rw [← toIGame_lt_toIGame]
  simp

example : ¬ IsNumeric (ofSets ({0} : Set ZFSet.GameCode.{u}) {0}) := by
  rw [isNumeric_iff_options]
  simp

example : (ofSets ({-1} : Set ZFSet.GameCode.{u}) {1}) ≈ 0 := by
  rw [← toIGame_equiv_toIGame]
  simp only [toIGame_ofSets, toIGame_zero, Set.image_singleton, toIGame_neg, toIGame_one]
  simp only [AntisymmRel]
  constructor <;> rw [IGame.le_iff_forall_lf] <;> simp

example : ofSets ({-1} : Set ZFSet.GameCode.{u}) {1} ≠ 0 := by
  intro h
  have hm : (-1 : ZFSet.GameCode.{u}) ∈ (0 : ZFSet.GameCode.{u}).moves Player.left := by
    rw [← h]
    simp
  simp at hm

example (x y : ZFSet.GameCode.{u}) (L R : ZFSet.{u})
    (h : (x : ZFSet.{u}) = ZFSet.pair L R) :
    y ∈ x.moves Player.left ↔ (y : ZFSet.{u}) ∈ L :=
  mem_moves_of_coe_eq_pair h Player.left

example (x y a b : ZFSet.GameCode.{u})
    (ha : a ∈ x.moves Player.left) (hb : b ∈ y.moves Player.right) :
    mulOption x y a b ∈ (x * y).moves Player.right := by
  rw [moves_mul]
  exact ⟨(a, b), Or.inl ⟨ha, hb⟩, rfl⟩
