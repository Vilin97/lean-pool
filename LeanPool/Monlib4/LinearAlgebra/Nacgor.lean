/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
 # Normed additive commutative groups of rings

This file contains the `NormedAddCommGroupOfRing` class, which bundles the
ring structure together with the normed additive commutative group structure.
-/

open scoped BigOperators

/-- A ring whose additive group is a normed additive commutative group. -/
class NormedAddCommGroupOfRing (B : Type*) extends Ring B, NormedAddCommGroup B

attribute [instance] NormedAddCommGroupOfRing.toNormedAddCommGroup
attribute [instance] NormedAddCommGroupOfRing.toRing
attribute [instance] NormedAddCommGroupOfRing.toNorm

/-- The algebra structure coming from compatible scalar multiplication and multiplication. -/
@[reducible]
def Algebra.ofIsScalarTowerSmulCommClass {R A : Type*} [CommSemiring R] [Semiring A]
    [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] : Algebra R A :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass

/-- The pointwise ring with the `L^2` product norm is a normed additive group of rings. -/
@[reducible, instance]
noncomputable def PiNormedAddCommGroupOfRing {ι : Type*} [Fintype ι] {B : ι → Type*}
    [Π i, NormedAddCommGroupOfRing (B i)] : NormedAddCommGroupOfRing (Π i, B i) where
  toNorm := (PiLp.normedAddCommGroupToPi (2 : ENNReal) B).toNorm
  toRing := Pi.ring
  toMetricSpace := (PiLp.normedAddCommGroupToPi (2 : ENNReal) B).toMetricSpace
  dist_eq := (PiLp.normedAddCommGroupToPi (2 : ENNReal) B).dist_eq

/-- The `L^2` norm on a finite product is the square root of the sum of squared norms. -/
theorem Pi.normedAddCommGroupOfRing.norm_eq_sum {ι : Type*} [Fintype ι] {B : ι → Type*}
    [Π i, NormedAddCommGroupOfRing (B i)] (x : Π i, B i) :
    PiNormedAddCommGroupOfRing.norm x = Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
  have h2 : 0 < (2 : ENNReal).toReal := by norm_num
  change ‖WithLp.toLp (2 : ENNReal) x‖ = Real.sqrt (∑ i, ‖x i‖ ^ 2)
  rw [PiLp.norm_eq_sum h2]
  simp [Real.sqrt_eq_rpow]
