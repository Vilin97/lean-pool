/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Game.Birthday
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Ordinal

import Mathlib.Algebra.Order.Group.OrderIso

/-!
# Birthday of a surreal number

TODO: write a better docstring
-/

universe u

public noncomputable section

namespace Surreal
open IGame NatOrdinal Order Set

/-- The birthday of a surreal number is defined as the least birthday
among all *numeric* pre-games that define it.

The numeric condition can be removed, see `Surreal.birthday_toGame`. -/
def birthday (x : Surreal.{u}) : NatOrdinal.{u} :=
  sInf (IGame.birthday '' {c | ∃ _ : Numeric c, mk c = x})

theorem birthday_eq_iGameBirthday (x : Surreal) :
    ∃ (y : IGame) (_ : Numeric y), mk y = x ∧ y.birthday = birthday x := by
  simp_rw [exists_and_right]
  refine csInf_mem (image_nonempty.2 ?_)
  exact ⟨_, _, x.out_eq⟩

theorem birthday_mk_le (x : IGame) [Numeric x] : birthday (mk x) ≤ x.birthday :=
  csInf_le' ⟨x, ⟨_, rfl⟩, rfl⟩

@[simp]
theorem birthday_zero : birthday 0 = 0 := by
  simpa using birthday_mk_le 0

@[simp]
theorem birthday_eq_zero {x : Surreal} : birthday x = 0 ↔ x = 0 := by
  obtain ⟨_, _, _, _⟩ := birthday_eq_iGameBirthday x
  refine ⟨fun _ ↦ ?_, ?_⟩ <;> simp_all

private theorem birthday_neg_le (x : Surreal) : (-x).birthday ≤ x.birthday := by
  obtain ⟨y, _, rfl, hy⟩ := birthday_eq_iGameBirthday x
  rw [← hy, ← IGame.birthday_neg]
  exact birthday_mk_le _

@[simp]
theorem birthday_neg (x : Surreal) : (-x).birthday = x.birthday := by
  apply (birthday_neg_le x).antisymm
  simpa using birthday_neg_le (-x)

theorem le_toSurreal_birthday (x : Surreal) : x ≤ x.birthday.toSurreal := by
  obtain ⟨y, _, rfl, hy⟩ := birthday_eq_iGameBirthday x
  rw [← hy]
  exact y.le_toIGame_birthday

theorem neg_toSurreal_birthday_le (x : Surreal) : -x.birthday.toSurreal ≤ x := by
  simpa [neg_le] using le_toSurreal_birthday (-x)

@[simp]
theorem birthday_toSurreal (o : NatOrdinal) : birthday o.toSurreal = o := by
  apply le_antisymm
  · simpa using birthday_mk_le o.toIGame
  · simpa using o.toSurreal.le_toSurreal_birthday

@[simp, norm_cast]
theorem birthday_natCast (n : ℕ) : birthday n = n := by
  simpa using birthday_toSurreal n

@[simp]
theorem birthday_ofNat (n : ℕ) [n.AtLeastTwo] : birthday ofNat(n) = n :=
  birthday_natCast n

@[simp]
theorem birthday_one : birthday 1 = 1 := by
  simpa using birthday_natCast 1

theorem birthday_ofSets_le {s t : Set Surreal.{u}}
    [Small.{u} s] [Small.{u} t] {H : ∀ x ∈ s, ∀ y ∈ t, x < y} :
    !{s | t}.birthday ≤ max (sSup (succ ∘ birthday '' s)) (sSup (succ ∘ birthday '' t)) := by
  choose f hf using birthday_eq_iGameBirthday
  have : Numeric !{f '' s | f '' t} := by
    rw [numeric_def]
    simp_rw [moves_ofSets]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨a, hx', _⟩ := hf x
      obtain ⟨b, hy', _⟩ := hf y
      rw [← mk_lt_mk, hx', hy']
      exact H x hx y hy
    rintro (_ | _) _ ⟨y, hy, rfl⟩
    all_goals
      obtain ⟨hy, _, _⟩ := hf y
      exact hy
  have : !{s | t} = mk !{f '' s | f '' t} := by
    rw [← toGame_inj, toGame_ofSets, toGame_mk, Game.mk_ofSets]
    simp_rw [image_image]
    congr! with a ha a ha
    all_goals
    · obtain ⟨_, ha', _⟩ := hf a
      rw [← toGame_mk, toGame_inj, ha']
  rw [this]
  apply (birthday_mk_le _).trans
  simp_rw [IGame.birthday_ofSets, image_comp]
  congr! <;> aesop

theorem birthday_add_le (x y : Surreal) : (x + y).birthday ≤ x.birthday + y.birthday := by
  obtain ⟨a, _, ha, ha'⟩ := birthday_eq_iGameBirthday x
  obtain ⟨b, _, hb, hb'⟩ := birthday_eq_iGameBirthday y
  rw [← ha', ← hb', ← ha, ← hb, ← IGame.birthday_add]
  exact birthday_mk_le _

theorem birthday_sub_le (x y : Surreal) : (x - y).birthday ≤ x.birthday + y.birthday := by
  simpa [sub_eq_add_neg] using birthday_add_le x (-y)

/- This is currently an open problem, see https://mathoverflow.net/a/476829/147705. -/
proof_wanted birthday_mul_le (x y : Surreal) : (x * y).birthday ≤ x.birthday * y.birthday

/-- The birthday of a surreal number is at least the birthday of the corresponding game. -/
theorem birthday_toGame_le (x : Surreal) : x.toGame.birthday ≤ x.birthday := by
  obtain ⟨c, _, rfl, h⟩ := birthday_eq_iGameBirthday x
  rw [← h, toGame_mk]
  exact Game.birthday_mk_le c

/-- Surreals with a bounded birthday form a small set. -/
instance small_setOf_birthday_le (o : NatOrdinal.{u}) : Small.{u} {x | birthday x ≤ o} := by
  have h₁ : {x | birthday x ≤ o} ⊆ toGame ⁻¹' {x | x.birthday ≤ o} := by
    intro x hx
    exact x.birthday_toGame_le.trans hx
  have h₂ := Set.restrictPreimage_injective {x | x.birthday ≤ o} toGame.injective
  have : Small.{u} (toGame ⁻¹' {x | x.birthday ≤ o}) := small_of_injective h₂
  exact small_subset h₁

/-- Surreals with a bounded birthday form a small set. -/
instance small_setOf_birthday_lt (o : NatOrdinal.{u}) : Small.{u} {x | birthday x < o} := by
  refine small_subset (?_ : {x : Surreal | x.birthday < o} ⊆ {x : Surreal | x.birthday ≤ o})
  simp +contextual [le_of_lt]

/-- A variant of `small_setOf_birthday_le` in simp-normal form -/
instance small_subtype_birthday_le (o : NatOrdinal.{u}) : Small.{u} {x // birthday x ≤ o} :=
  small_setOf_birthday_le o

/-- A variant of `small_setOf_birthday_lt` in simp-normal form -/
instance small_subtype_birthday_lt (o : NatOrdinal.{u}) : Small.{u} {x // birthday x < o} :=
  small_setOf_birthday_lt o

end Surreal
