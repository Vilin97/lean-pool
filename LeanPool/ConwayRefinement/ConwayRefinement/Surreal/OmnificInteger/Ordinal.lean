/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Basic
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Ordinal

import LeanPool.ConwayRefinement.CombinatorialGames.Tactic.GameCmp

/-!
# Ordinals as omnific integers

This file proves the final assertion of Conway's Theorem 31: every ordinal, embedded in the
surreal numbers, is an omnific integer. The proof uses the canonical ordinal pregame and Conway's
fixed-point definition directly; it does not presuppose a surreal normal-form map.
-/

universe u

public noncomputable section

open IGame Order

namespace NatOrdinal

private theorem toIGame_le_sub_one_of_lt {a o : NatOrdinal.{u}} (hao : a < o) :
    a.toIGame ≤ o.toIGame - 1 := by
  rw [← ConwayGame.mk_le_mk]
  simp only [ConwayGame.mk_sub, ConwayGame.mk_one, ConwayGame.mk_natOrdinal_toIGame]
  rw [le_sub_iff_add_le, ← NatOrdinal.toGame_one, ← NatOrdinal.toGame_add]
  apply NatOrdinal.toGame.monotone
  simpa only [Order.succ_eq_add_one] using succ_le_of_lt hao

private theorem toIGame_equiv_omnificIntegerCut (o : NatOrdinal.{u}) :
    o.toIGame ≈ !{{o.toIGame - 1} | {o.toIGame + 1}} := by
  apply IGame.Fits.equiv_of_forall_moves
  · rw [IGame.Fits]
    constructor
    · intro z hz
      simp only [IGame.leftMoves_ofSets, Set.mem_singleton_iff] at hz
      subst z
      exact IGame.Numeric.not_le.mpr (by
        rw [← Surreal.mk_lt_mk]
        simp)
    · intro z hz
      simp only [IGame.rightMoves_ofSets, Set.mem_singleton_iff] at hz
      subst z
      exact IGame.Numeric.not_le.mpr (by
        rw [← Surreal.mk_lt_mk]
        simp)
  · intro z hz
    rw [NatOrdinal.leftMoves_toIGame] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨o.toIGame - 1, by simp, toIGame_le_sub_one_of_lt ha⟩
  · simp

/-- Every ordinal, under its canonical embedding in the surreal numbers, is an omnific integer. -/
theorem isOmnificInteger_toSurreal (o : NatOrdinal.{u}) :
    Surreal.IsOmnificInteger o.toSurreal := by
  rw [← Surreal.mk_natOrdinal_toIGame, Surreal.isOmnificInteger_mk_iff]
  exact toIGame_equiv_omnificIntegerCut o

/-- Every ordinal belongs to the omnific-integer subring of the surreal numbers. -/
theorem toSurreal_mem_omnificIntegers (o : NatOrdinal.{u}) :
    o.toSurreal ∈ Surreal.omnificIntegers :=
  Surreal.mem_omnificIntegers.mpr (isOmnificInteger_toSurreal o)

end NatOrdinal
