/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import LeanPool.MisereGames.Form.Birthday
public import LeanPool.MisereGames.GameForm
public import LeanPool.MisereGames.Mathlib.NatOrdinal
public import Mathlib.Data.Set.Defs

/-!
Misere combinatorial games.
-/

namespace MisereGames

open NatOrdinal Order Set

universe u

public section

namespace GameForm

open Form

@[simp]
theorem birthday_eq_zero {x : GameForm} : birthday x = 0 ↔ x = 0 := by
  rw [birthday, iSup_eq_zero_iff, GameForm.ext_iff]
  simp only [succ_eq_add_one, add_one_ne_zero, Subtype.forall, IsOption.iff_mem_union, mem_union,
             imp_false, not_or, forall_and, moves_zero (G := GameForm), eq_empty_iff_forall_notMem,
             Player.forall]

/-- The finite set of game forms born by day `n`. -/
noncomputable def birthdayFinset : ℕ → Finset GameForm.{u}
  | 0 => {0}
  | n + 1 => ((birthdayFinset n).powerset ×ˢ (birthdayFinset n).powerset).map
    ⟨fun a => !{a.1 | a.2}, fun a b hab => by aesop⟩

theorem mem_birthdayFinset_succ {x : GameForm} {n : ℕ} : x ∈ birthdayFinset (n + 1) ↔
    ∃ l r, (l ⊆ birthdayFinset n ∧ r ⊆ birthdayFinset n) ∧ !{l | r} = x := by
  simp [birthdayFinset]

@[simp]
theorem birthdayFinset_zero : birthdayFinset 0 = {0} := by rfl

@[simp]
theorem mem_birthdayFinset {x : GameForm} {n : ℕ} : x ∈ birthdayFinset n ↔ birthday x ≤ n := by
  induction n generalizing x with
  | zero =>
    simp [birthdayFinset_zero, birthday_eq_zero]
  | succ n IH =>
    simp_rw [mem_birthdayFinset_succ, birthday_le_iff, Finset.subset_iff, Nat.cast_add_one,
      ← succ_eq_add_one, lt_succ_iff, IH]
    constructor
    · aesop
    · rintro ⟨hl, hr⟩
      have hxl : xᴸ ⊆ birthdayFinset n := fun y hy => (IH (x := y)).2 (hl y hy)
      have hxr : xᴿ ⊆ birthdayFinset n := fun y hy => (IH (x := y)).2 (hr y hy)
      classical
      have := Set.fintypeSubset _ hxl
      have := Set.fintypeSubset _ hxr
      use xᴸ.toFinset, xᴿ.toFinset
      simp_all only [mem_toFinset, implies_true, and_self, coe_toFinset,
        ofSets_leftMoves_rightMoves]

end GameForm

end

end MisereGames
