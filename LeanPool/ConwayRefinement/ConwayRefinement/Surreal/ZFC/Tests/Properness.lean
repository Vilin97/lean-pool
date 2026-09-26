/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Properness
import LeanPool.ConwayRefinement.CombinatorialGames.Game.Special

/-!
# Public checks for the intrinsic proper classes

The empty ZFC set is not a game code, the star game is not numeric, and one half is numeric but
not omnific. These distinguish the intrinsic classes from all ZFC sets, all game codes, and the
incorrect identification of omnific and numeric codes. The remaining examples check coverage of
arbitrary values and properness through the exported interface.
-/

universe u

noncomputable section

open ZFSet

example : numericGameCodes ((0 : GameCode.{u}) : ZFSet.{u}) :=
  (GameCode.mem_numericGameCodes _).2 GameCode.isNumeric_zero

example : numericGameCodes ((1 : GameCode.{u}) : ZFSet.{u}) :=
  (GameCode.mem_numericGameCodes _).2 GameCode.isNumeric_one

example : omnificGameCodes ((0 : GameCode.{u}) : ZFSet.{u}) := by
  simpa only [OmnificCode.code_zero] using (0 : OmnificCode.{u}).mem_omnificGameCodes

example : omnificGameCodes ((1 : GameCode.{u}) : ZFSet.{u}) := by
  simpa only [OmnificCode.code_one] using (1 : OmnificCode.{u}).mem_omnificGameCodes

example : ¬numericGameCodes (∅ : ZFSet.{u}) := by
  intro h
  obtain ⟨hg, _⟩ := (numericGameCodes_iff _).1 h
  obtain ⟨L, R, heq, _, _⟩ := hg.exists_eq_pair
  have hm : ({L} : ZFSet.{u}) ∈ (∅ : ZFSet.{u}) := by rw [heq]; simp [ZFSet.pair]
  exact ZFSet.notMem_empty _ hm

example : ¬numericGameCodes
    ((GameCode.ofSets ({0} : Set GameCode.{u}) {0}) : ZFSet.{u}) := by
  rw [GameCode.mem_numericGameCodes, GameCode.isNumeric_iff_options]
  simp

example : numericGameCodes ((GameCode.ofIGame (IGame.half : IGame.{u})) : ZFSet.{u}) :=
  (GameCode.mem_numericGameCodes _).2 ((GameCode.isNumeric_ofIGame _).2 inferInstance)

example : ¬omnificGameCodes ((GameCode.ofIGame (IGame.half : IGame.{u})) : ZFSet.{u}) := by
  intro h
  have hn : (GameCode.ofIGame (IGame.half : IGame.{u})).IsNumeric :=
    (GameCode.isNumeric_ofIGame _).2 inferInstance
  have ho := (GameCode.isOmnificInteger_iff_toSurreal _ hn).1
    ((GameCode.mem_omnificGameCodes _).1 h)
  apply _root_.Surreal.two_inv_not_mem_omnificIntegers
  apply _root_.Surreal.mem_omnificIntegers.2
  simpa only [ZFSet.Surreal.toSurreal_mk, GameCode.toIGame_ofIGame, IGame.mk_half] using ho

example (x : _root_.Surreal.{u}) :
    ∃ c : NumericGameCode.{u}, numericGameCodes (c.code : ZFSet.{u}) ∧ c.toSurreal = x := by
  obtain ⟨c, hc⟩ := NumericGameCode.toSurreal_surjective x
  exact ⟨c, c.mem_numericGameCodes, hc⟩

example (x : _root_.Surreal.OmnificInteger.{u}) :
    ∃ c : OmnificCode.{u}, omnificGameCodes (c.code : ZFSet.{u}) ∧ c.value = x := by
  obtain ⟨c, hc⟩ := OmnificCode.value_surjective x
  exact ⟨c, c.mem_omnificGameCodes, hc⟩

example (z : ZFSet.{u}) (hz : numericGameCodes z) :
    ∃ c : NumericGameCode.{u}, (c.code : ZFSet.{u}) = z :=
  (numericGameCodes_iff_exists z).1 hz

example (z : ZFSet.{u}) (hz : omnificGameCodes z) :
    ∃ c : OmnificCode.{u}, (c.code : ZFSet.{u}) = z :=
  (omnificGameCodes_iff_exists z).1 hz

example (s : ZFSet.{u}) : numericGameCodes ≠ Class.ofSet s := numericGameCodes_ne_ofSet s

example (s : ZFSet.{u}) : omnificGameCodes ≠ Class.ofSet s := omnificGameCodes_ne_ofSet s

example : numericGameCodes ∉ Class.univ.{u} := numericGameCodes_notMem_univ

example : omnificGameCodes ∉ Class.univ.{u} := omnificGameCodes_notMem_univ

example : ¬Small.{u} ZFSet.Surreal.{u} := ZFSet.Surreal.not_small

example : ¬Small.{u} ZFSet.Surreal.OmnificInteger.{u} := ZFSet.Surreal.OmnificInteger.not_small
