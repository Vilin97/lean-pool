/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Powers of two modulo powers of three

This file proves that `2` generates the unit group modulo every positive power
of three. At level `n`, its order modulo `3 ^ (n + 1)` is exactly
`2 * 3 ^ n`. Thus one complete period of exponents is equivalent to the full
unit group.
-/

namespace GKPCarry

/-- The unit represented by `2` modulo `3 ^ (level + 1)`. -/
def twoUnit (level : ℕ) : (ZMod (3 ^ (level + 1)))ˣ :=
  ZMod.unitOfCoprime 2
    ((by decide : Nat.Coprime 2 3).pow_right (level + 1))

lemma orderOf_twoUnit_sq (level : ℕ) :
    orderOf ((twoUnit level) ^ 2) = 3 ^ level := by
  rw [← orderOf_injective (Units.coeHom _) Units.val_injective]
  change orderOf ((2 : ZMod (3 ^ (level + 1))) ^ 2) = 3 ^ level
  convert ZMod.orderOf_one_add_prime Nat.prime_three (by decide) level using 1
  all_goals norm_num

lemma two_dvd_orderOf_twoUnit (level : ℕ) :
    2 ∣ orderOf (twoUnit level) := by
  have hdiv : 3 ∣ 3 ^ (level + 1) := dvd_pow_self 3 (by omega)
  let reduction := ZMod.unitsMap hdiv
  have hmap : reduction (twoUnit level) = ZMod.unitOfCoprime 2 (by decide) := by
    apply Units.ext
    rw [ZMod.unitsMap_val]
    change ((2 : ZMod (3 ^ (level + 1))).cast : ZMod 3) = 2
    exact ZMod.cast_natCast hdiv 2
  have himage : orderOf (reduction (twoUnit level)) = 2 := by
    rw [hmap]
    rw [← orderOf_injective (Units.coeHom _) Units.val_injective]
    change orderOf (2 : ZMod 3) = 2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime <;> decide
  rw [← himage]
  exact orderOf_map_dvd reduction (twoUnit level)

/-- The multiplicative order of `2` modulo `3 ^ (level + 1)` is the full
Euler period `2 * 3 ^ level`. -/
theorem orderOf_twoUnit (level : ℕ) :
    orderOf (twoUnit level) = 2 * 3 ^ level := by
  have hsquare := orderOf_twoUnit_sq level
  rw [orderOf_pow' (twoUnit level) (by decide),
    Nat.gcd_eq_right (two_dvd_orderOf_twoUnit level)] at hsquare
  calc
    orderOf (twoUnit level) = orderOf (twoUnit level) / 2 * 2 :=
      (Nat.div_mul_cancel (two_dvd_orderOf_twoUnit level)).symm
    _ = 2 * 3 ^ level := by rw [hsquare]; ring

/-- The unit group modulo `3 ^ (level + 1)` has `2 * 3 ^ level` elements. -/
theorem card_units_three_pow_succ (level : ℕ) :
    Fintype.card (ZMod (3 ^ (level + 1)))ˣ = 2 * 3 ^ level := by
  rw [ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ Nat.prime_three]
  ring

/-- Send an exponent in one complete period to the corresponding power of
`2` in the unit group. -/
def twoPowerUnitMap (level : ℕ) :
    Fin (2 * 3 ^ level) → (ZMod (3 ^ (level + 1)))ˣ :=
  fun exponent => twoUnit level ^ exponent.val

lemma twoPowerUnitMap_injective (level : ℕ) :
    Function.Injective (twoPowerUnitMap level) := by
  intro exponent₁ exponent₂ hequal
  have hmod := (pow_inj_mod (x := twoUnit level)).mp hequal
  rw [orderOf_twoUnit level] at hmod
  rw [Nat.mod_eq_of_lt exponent₁.isLt,
    Nat.mod_eq_of_lt exponent₂.isLt] at hmod
  exact Fin.ext hmod

/-- A complete period of exponents is equivalent to all units modulo the
corresponding power of three. -/
noncomputable def twoPowerUnitEquiv (level : ℕ) :
    Fin (2 * 3 ^ level) ≃ (ZMod (3 ^ (level + 1)))ˣ :=
  Equiv.ofBijective (twoPowerUnitMap level) <|
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨twoPowerUnitMap_injective level, by
        rw [Fintype.card_fin, card_units_three_pow_succ]⟩

@[simp]
theorem twoPowerUnitEquiv_apply (level : ℕ)
    (exponent : Fin (2 * 3 ^ level)) :
    twoPowerUnitEquiv level exponent = twoUnit level ^ exponent.val :=
  rfl

/-- The natural representative of the unit associated to an exponent is the
ordinary modular power. -/
theorem val_twoPowerUnitEquiv_apply (level : ℕ)
    (exponent : Fin (2 * 3 ^ level)) :
    ((twoPowerUnitEquiv level exponent :
        (ZMod (3 ^ (level + 1)))ˣ) : ZMod (3 ^ (level + 1))).val =
      2 ^ exponent.val % 3 ^ (level + 1) := by
  change ((2 : ZMod (3 ^ (level + 1))) ^ exponent.val).val = _
  have hcast :
      (2 : ZMod (3 ^ (level + 1))) ^ exponent.val =
        ((2 ^ exponent.val : ℕ) : ZMod (3 ^ (level + 1))) := by
    exact (Nat.cast_pow 2 exponent.val).symm
  rw [hcast, ZMod.val_natCast]

/-- Reduction of an arbitrary exponent to the exact period does not change
the residue modulo `3 ^ (level + 1)`. -/
theorem two_pow_mod_three_pow_succ_eq_reduced_exponent
    (level exponent : ℕ) :
    2 ^ exponent % 3 ^ (level + 1) =
      2 ^ (exponent % (2 * 3 ^ level)) % 3 ^ (level + 1) := by
  have hpow := pow_mod_orderOf (twoUnit level) exponent
  rw [orderOf_twoUnit level] at hpow
  have hvalues := congrArg
    (fun unit : (ZMod (3 ^ (level + 1)))ˣ =>
      ((unit : ZMod (3 ^ (level + 1))).val)) hpow
  change
    ((2 : ZMod (3 ^ (level + 1))) ^
        (exponent % (2 * 3 ^ level))).val =
      ((2 : ZMod (3 ^ (level + 1))) ^ exponent).val at hvalues
  have hcastReduced :
      (2 : ZMod (3 ^ (level + 1))) ^ (exponent % (2 * 3 ^ level)) =
        ((2 ^ (exponent % (2 * 3 ^ level)) : ℕ) :
          ZMod (3 ^ (level + 1))) := by
    exact (Nat.cast_pow 2 (exponent % (2 * 3 ^ level))).symm
  have hcastExponent :
      (2 : ZMod (3 ^ (level + 1))) ^ exponent =
        ((2 ^ exponent : ℕ) : ZMod (3 ^ (level + 1))) := by
    exact (Nat.cast_pow 2 exponent).symm
  rw [hcastReduced, hcastExponent,
    ZMod.val_natCast, ZMod.val_natCast] at hvalues
  exact hvalues.symm

end GKPCarry
