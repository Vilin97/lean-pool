/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.ZFC.Game
import LeanPool.ConwayRefinement.CombinatorialGames.Game.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Public interface checks for ZFC game codes

The grammar excludes arbitrary ZFC sets. Its coding distinguishes complete pregame trees and
supports genuinely infinite option sets, not just finite trees or numeral examples.
-/

universe u

noncomputable section

example : ZFSet.IsGameCode (ZFSet.pair (∅ : ZFSet.{u}) ∅) := by simp

example : ¬ ZFSet.IsGameCode (∅ : ZFSet.{u}) := by
  intro h
  obtain ⟨L, R, heq, _, _⟩ := h.exists_eq_pair
  have hm : ({L} : ZFSet.{u}) ∈ (∅ : ZFSet.{u}) := by rw [heq]; simp [ZFSet.pair]
  exact ZFSet.notMem_empty _ hm

example (z : ZFSet.{u}) (hz : ZFSet.IsGameCode z) :
    IGame.toZFSet (IGame.zfSetEquiv.symm (ZFSet.GameCode.mk z hz)) = z := by
  simp

example (g : IGame.{u}) : IGame.zfSetEquiv.symm (IGame.zfSetEquiv g) = g := by
  simp

example {x y : ZFSet.GameCode.{u}} (h : (x : ZFSet.{u}) = (y : ZFSet.{u})) : x = y :=
  ZFSet.GameCode.ext h

example (n : ℕ) :
    IGame.toZFSet (n : IGame.{u}) ∈ IGame.optionsZFSet Player.left
      !{Set.range (fun k : ℕ ↦ (k : IGame.{u})) | ∅} := by
  simp

example :
    Set.Infinite (IGame.optionsZFSet Player.left
      !{Set.range (fun k : ℕ ↦ (k : IGame.{u})) | ∅} : Set ZFSet.{u}) := by
  have heq :
      (IGame.optionsZFSet Player.left
        !{Set.range (fun k : ℕ ↦ (k : IGame.{u})) | ∅} : Set ZFSet.{u}) =
      Set.range (fun k : ℕ ↦ IGame.toZFSet (k : IGame.{u})) := by
    ext z
    simp
  rw [heq]
  exact Set.infinite_range_of_injective
    (IGame.toZFSet_injective.comp (Nat.cast_injective (R := IGame.{u})))
