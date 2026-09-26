/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Game.Ordinal
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Multiplication
public import Mathlib.Algebra.Order.Hom.Ring

/-!
# Ordinals as surreals

We define the canonical map `NatOrdinal → Surreal` in terms of the map `NatOrdinal.toIGame`.
-/

open IGame Set Surreal

@[expose] public noncomputable section

/-- Ordinal games are numeric. -/
instance IGame.Numeric.toIGame (o : NatOrdinal) : Numeric o.toIGame := by
  rw [numeric_def]
  simpa using fun a ha ↦ IGame.Numeric.toIGame a
termination_by o

namespace NatOrdinal

/-- Converts an ordinal into the corresponding surreal. -/
def toSurreal : NatOrdinal ↪o Surreal :=
  .ofStrictMono (fun o ↦ .mk o.toIGame) fun _ _ h ↦ toIGame.strictMono h

instance : Coe NatOrdinal Surreal where
  coe x := toSurreal x

@[simp]
theorem _root_.Surreal.mk_natOrdinal_toIGame (o : NatOrdinal) : .mk o.toIGame = o.toSurreal :=
  rfl

@[simp]
theorem _root_.Surreal.toGame_toSurreal (o : NatOrdinal) : o.toSurreal.toGame = o.toGame :=
  rfl

theorem toSurreal_def (o : NatOrdinal) : o.toSurreal = !{toSurreal '' Iio o | ∅} := by
  simp_rw [← Surreal.mk_natOrdinal_toIGame, toIGame_def o, Surreal.mk_ofSets]
  congr! <;> aesop

@[simp] theorem toSurreal_zero : toSurreal 0 = 0 := by simp [← Surreal.mk_natOrdinal_toIGame]
@[simp] theorem toSurreal_one : toSurreal 1 = 1 := by simp [← Surreal.mk_natOrdinal_toIGame]

theorem toSurreal_nonneg (a : NatOrdinal) : 0 ≤ a.toGame :=
  toIGame_nonneg a

@[simp]
theorem toSurreal_add (a b : NatOrdinal) : (a + b).toSurreal = a.toSurreal + b.toSurreal :=
  mk_eq (toIGame_add a b)

@[simp]
theorem toSurreal_mul (a b : NatOrdinal) : (a * b).toSurreal = a.toSurreal * b.toSurreal :=
  mk_eq (toIGame_mul a b)

/-- `NatOrdinal.toGame` as an `OrderRingHom`. -/
@[simps]
def toSurrealRingHom : NatOrdinal →+*o Surreal where
  toFun := toSurreal
  map_zero' := toSurreal_zero
  map_one' := toSurreal_one
  map_add' := toSurreal_add
  map_mul' := toSurreal_mul
  monotone' := toSurreal.monotone

@[simp]
theorem toSurreal_natCast : ∀ n : ℕ, toSurreal n = n :=
  map_natCast' toSurrealRingHom toSurreal_one

end NatOrdinal
end
