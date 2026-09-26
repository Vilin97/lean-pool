/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.FieldTheory.Perfect
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Algebraic.Integral
/-!
# Local fields

A local-field package here is a chosen complete discretely valued field with
finite residue field.  The topology-first mathlib class remains available
through imports; this file only adds the chosen-valuation API needed downstream.
-/

@[expose] public section

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

/-- A local field with a chosen complete discrete valuation and finite residue field. -/
structure LocalField (K : Type u) [Field K] extends CompleteDVF.{u, v} K where
  /-- The residue field of the chosen complete discrete valuation is finite. -/
  [residueFinite : Finite toCompleteDVF.residueField]

attribute [instance] LocalField.residueFinite

namespace LocalField

variable {K : Type u} [Field K]

/-- The residue field of a local field package. -/
abbrev residueField (F : LocalField.{u, v} K) : Type u :=
  F.toCompleteDVF.residueField

/-- The valuation subring of a local field package. -/
abbrev valuationSubring (F : LocalField.{u, v} K) : Type u :=
  F.toCompleteDVF.valuationSubring

/-- The maximal ideal of the valuation subring. -/
abbrev maximalIdeal (F : LocalField.{u, v} K) : Ideal F.valuationSubring :=
  F.toCompleteDVF.maximalIdeal

/-- The residue map of a local field package. -/
abbrev residueMap (F : LocalField.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  F.toCompleteDVF.residueMap

/-- The valuation subring of a local field package is a DVR. -/
theorem valuationSubring_isDiscreteValuationRing
    (F : LocalField.{u, v} K) :
    IsDiscreteValuationRing F.valuationSubring := by
  change IsDiscreteValuationRing F.toCompleteDVF.valuationSubring
  exact F.toCompleteDVF.valuationSubring_isDiscreteValuationRing

/-- The valuation subring of a local field package is Henselian. -/
theorem henselianRing (F : LocalField.{u, v} K) :
    HenselianRing F.valuationSubring F.maximalIdeal :=
  F.toCompleteDVF.henselianRing

/-- A local field package has a uniformizer. -/
theorem exists_uniformizer (F : LocalField.{u, v} K) :
    ∃ pi : F.valuationSubring, F.toCompleteDVF.valuation.IsUniformizer (pi : K) :=
  F.toCompleteDVF.exists_uniformizer

/-- The residue characteristic of a local field. -/
noncomputable abbrev residueCharacteristic (F : LocalField.{u, v} K) : ℕ :=
  ringChar F.residueField

/-- Establishes the inequality `F.residueCharacteristic ≠ 0`. -/
theorem residueCharacteristic_ne_zero (F : LocalField.{u, v} K) :
    F.residueCharacteristic ≠ 0 :=
  CharP.ringChar_ne_zero_of_finite F.residueField

/-- Proves the primality statement `Nat.Prime F.residueCharacteristic`. -/
theorem residueCharacteristic_prime (F : LocalField.{u, v} K) :
    Nat.Prime F.residueCharacteristic := by
  change Nat.Prime (ringChar F.toCompleteDVF.residueField)
  let : NoZeroDivisors F.toCompleteDVF.residueField :=
    GroupWithZero.noZeroDivisors
  exact CharP.prime_ringChar F.toCompleteDVF.residueField

/-- The target has the stated characteristic: `CharP F.residueField F.residueCharacteristic`. -/
instance residueField_charP_residueCharacteristic (F : LocalField.{u, v} K) :
    CharP F.residueField F.residueCharacteristic :=
  ringChar.charP (R := F.residueField)

/-- Registers the mathematical fact `Fact F.residueCharacteristic.Prime` for typeclass inference. -/
instance residueCharacteristic.fact_prime (F : LocalField.{u, v} K) :
    Fact F.residueCharacteristic.Prime :=
  ⟨F.residueCharacteristic_prime⟩

/-- The residue characteristic vanishes after reduction modulo the maximal
ideal.  This is the first characteristic input in the converse direction of
the local-field structure theory, the local-field structure classification. -/
theorem residueCharacteristic_natCast_residue_eq_zero
    (F : LocalField.{u, v} K) :
    F.residueMap (F.residueCharacteristic : F.valuationSubring) = 0 := by
  calc
    F.residueMap (F.residueCharacteristic : F.valuationSubring)
        = (F.residueCharacteristic : F.residueField) := by
          exact map_natCast F.residueMap F.residueCharacteristic
    _ = 0 := by
      exact ringChar.Nat.cast_ringChar (R := F.residueField)

/-- The residue characteristic belongs to the maximal ideal of the valuation
ring. -/
theorem residueCharacteristic_natCast_mem_maximalIdeal
    (F : LocalField.{u, v} K) :
    (F.residueCharacteristic : F.valuationSubring) ∈ F.maximalIdeal :=
  (F.toCompleteDVF.residue_eq_zero_iff
    (F.residueCharacteristic : F.valuationSubring)).1
    F.residueCharacteristic_natCast_residue_eq_zero

/-- Valuatively, the residue characteristic lies in the open unit ball. -/
theorem valuation_residueCharacteristic_natCast_lt_one
    (F : LocalField.{u, v} K) :
    F.toCompleteDVF.valuation
      ((F.residueCharacteristic : F.valuationSubring) : K) < 1 :=
  (F.toCompleteDVF.mem_maximalIdeal_iff
    (F.residueCharacteristic : F.valuationSubring)).1
    F.residueCharacteristic_natCast_mem_maximalIdeal

/-- Field-level form of the previous valuation estimate. -/
theorem valuation_natCast_residueCharacteristic_lt_one
    (F : LocalField.{u, v} K) :
    F.toCompleteDVF.valuation (F.residueCharacteristic : K) < 1 := by
  have hcast :
      ((F.residueCharacteristic : F.valuationSubring) : K) =
        (F.residueCharacteristic : K) := by
    exact map_natCast F.toCompleteDVF.valuation.valuationSubring.subtype
      F.residueCharacteristic
  rw [← hcast]
  exact F.valuation_residueCharacteristic_natCast_lt_one

/-- In mixed characteristic, the residue characteristic is a nonzero element of
the field even though it reduces to zero. -/
theorem natCast_residueCharacteristic_ne_zero_of_charZero
    (F : LocalField.{u, v} K) [CharZero K] :
    (F.residueCharacteristic : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr F.residueCharacteristic_ne_zero

/-- For an arbitrary integer, membership in the maximal ideal is exactly
divisibility by the residue characteristic. -/
theorem intCast_mem_maximalIdeal_iff_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (z : ℤ) :
    (z : F.valuationSubring) ∈ F.maximalIdeal ↔
      (F.residueCharacteristic : ℤ) ∣ z := by
  rw [← F.toCompleteDVF.residue_eq_zero_iff (z : F.valuationSubring)]
  rw [map_intCast]
  exact
    CharP.intCast_eq_zero_iff
      (R := F.residueField) F.residueCharacteristic z

/-- Natural-number version of
`intCast_mem_maximalIdeal_iff_residueCharacteristic_dvd`. -/
theorem natCast_mem_maximalIdeal_iff_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (n : ℕ) :
    (n : F.valuationSubring) ∈ F.maximalIdeal ↔
      F.residueCharacteristic ∣ n := by
  rw [← F.toCompleteDVF.residue_eq_zero_iff (n : F.valuationSubring)]
  rw [map_natCast]
  exact ringChar.spec (R := F.residueField) n

/-- Integer-valued maximal-ideal membership as a valuation inequality. -/
theorem valuationSubring_intCast_lt_one_iff_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (z : ℤ) :
    F.toCompleteDVF.valuation ((z : F.valuationSubring) : K) < 1 ↔
      (F.residueCharacteristic : ℤ) ∣ z :=
  (F.toCompleteDVF.mem_maximalIdeal_iff
    (z : F.valuationSubring)).symm.trans
    (F.intCast_mem_maximalIdeal_iff_residueCharacteristic_dvd z)

/-- Natural-number-valued maximal-ideal membership as a valuation inequality. -/
theorem valuationSubring_natCast_lt_one_iff_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.toCompleteDVF.valuation ((n : F.valuationSubring) : K) < 1 ↔
      F.residueCharacteristic ∣ n :=
  (F.toCompleteDVF.mem_maximalIdeal_iff
    (n : F.valuationSubring)).symm.trans
    (F.natCast_mem_maximalIdeal_iff_residueCharacteristic_dvd n)

/-- An integer prime to the residue characteristic is a unit in the valuation
ring. -/
theorem isUnit_intCast_iff_not_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (z : ℤ) :
    IsUnit (z : F.valuationSubring) ↔
      ¬ (F.residueCharacteristic : ℤ) ∣ z := by
  rw [← F.toCompleteDVF.residue_ne_zero_iff_isUnit (z : F.valuationSubring)]
  rw [map_intCast]
  exact
    not_congr
      (CharP.intCast_eq_zero_iff
        (R := F.residueField) F.residueCharacteristic z)

/-- A natural number prime to the residue characteristic is a unit in the
valuation ring. -/
theorem isUnit_natCast_iff_not_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUnit (n : F.valuationSubring) ↔
      ¬ F.residueCharacteristic ∣ n := by
  rw [← F.toCompleteDVF.residue_ne_zero_iff_isUnit (n : F.valuationSubring)]
  rw [map_natCast]
  exact not_congr (ringChar.spec (R := F.residueField) n)

/-- An integer prime to the residue characteristic has valuation one. -/
theorem valuationSubring_intCast_eq_one_of_not_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) {z : ℤ}
    (hz : ¬ (F.residueCharacteristic : ℤ) ∣ z) :
    F.toCompleteDVF.valuation ((z : F.valuationSubring) : K) = 1 := by
  have hle :
      F.toCompleteDVF.valuation ((z : F.valuationSubring) : K) ≤ 1 :=
    (F.toCompleteDVF.mem_valuationSubring_iff
      ((z : F.valuationSubring) : K)).1
      (z : F.valuationSubring).property
  have hnlt :
      ¬ F.toCompleteDVF.valuation ((z : F.valuationSubring) : K) < 1 := by
    intro hlt
    exact hz
      ((F.valuationSubring_intCast_lt_one_iff_residueCharacteristic_dvd z).1 hlt)
  exact le_antisymm hle (le_of_not_gt hnlt)

/-- A natural number prime to the residue characteristic has valuation one. -/
theorem valuationSubring_natCast_eq_one_of_not_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) {n : ℕ}
    (hn : ¬ F.residueCharacteristic ∣ n) :
    F.toCompleteDVF.valuation ((n : F.valuationSubring) : K) = 1 := by
  have hle :
      F.toCompleteDVF.valuation ((n : F.valuationSubring) : K) ≤ 1 :=
    (F.toCompleteDVF.mem_valuationSubring_iff
      ((n : F.valuationSubring) : K)).1
      (n : F.valuationSubring).property
  have hnlt :
      ¬ F.toCompleteDVF.valuation ((n : F.valuationSubring) : K) < 1 := by
    intro hlt
    exact hn
      ((F.valuationSubring_natCast_lt_one_iff_residueCharacteristic_dvd n).1 hlt)
  exact le_antisymm hle (le_of_not_gt hnlt)

/-- Field-level integer valuation criterion for the residue characteristic. -/
theorem valuation_intCast_lt_one_iff_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (z : ℤ) :
    F.toCompleteDVF.valuation (z : K) < 1 ↔
      (F.residueCharacteristic : ℤ) ∣ z := by
  have hcast :
      ((z : F.valuationSubring) : K) = (z : K) := by
    exact map_intCast F.toCompleteDVF.valuation.valuationSubring.subtype z
  rw [← hcast]
  exact F.valuationSubring_intCast_lt_one_iff_residueCharacteristic_dvd z

/-- Field-level natural-number valuation criterion for the residue
characteristic. -/
theorem valuation_natCast_lt_one_iff_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.toCompleteDVF.valuation (n : K) < 1 ↔
      F.residueCharacteristic ∣ n := by
  have hcast :
      ((n : F.valuationSubring) : K) = (n : K) := by
    exact map_natCast F.toCompleteDVF.valuation.valuationSubring.subtype n
  rw [← hcast]
  exact F.valuationSubring_natCast_lt_one_iff_residueCharacteristic_dvd n

/-- Field-level integer valuation-one criterion away from the residue
characteristic. -/
theorem valuation_intCast_eq_one_of_not_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) {z : ℤ}
    (hz : ¬ (F.residueCharacteristic : ℤ) ∣ z) :
    F.toCompleteDVF.valuation (z : K) = 1 := by
  have hcast :
      ((z : F.valuationSubring) : K) = (z : K) := by
    exact map_intCast F.toCompleteDVF.valuation.valuationSubring.subtype z
  rw [← hcast]
  exact F.valuationSubring_intCast_eq_one_of_not_residueCharacteristic_dvd hz

/-- Field-level natural-number valuation-one criterion away from the residue
characteristic. -/
theorem valuation_natCast_eq_one_of_not_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) {n : ℕ}
    (hn : ¬ F.residueCharacteristic ∣ n) :
    F.toCompleteDVF.valuation (n : K) = 1 := by
  have hcast :
      ((n : F.valuationSubring) : K) = (n : K) := by
    exact map_natCast F.toCompleteDVF.valuation.valuationSubring.subtype n
  rw [← hcast]
  exact F.valuationSubring_natCast_eq_one_of_not_residueCharacteristic_dvd hn

/-- Every integer lies in the valuation subring.  This is the denominator
control input for the mixed-characteristic branch of the local-field structure classification. -/
theorem valuation_intCast_le_one (F : LocalField.{u, v} K) (z : ℤ) :
    F.toCompleteDVF.valuation (z : K) ≤ 1 := by
  have hmem :
      ((z : F.valuationSubring) : K) ∈
        F.toCompleteDVF.valuation.valuationSubring :=
    (z : F.valuationSubring).property
  have hcast :
      ((z : F.valuationSubring) : K) = (z : K) := by
    exact map_intCast F.toCompleteDVF.valuation.valuationSubring.subtype z
  rw [← hcast]
  exact
    (F.toCompleteDVF.mem_valuationSubring_iff
      ((z : F.valuationSubring) : K)).1 hmem

/-- Every natural number lies in the valuation subring. -/
theorem valuation_natCast_le_one (F : LocalField.{u, v} K) (n : ℕ) :
    F.toCompleteDVF.valuation (n : K) ≤ 1 := by
  simpa using F.valuation_intCast_le_one (n : ℤ)

/-- If the denominator of a rational number is prime to the residue
characteristic, then its valuation is the valuation of its numerator. -/
theorem valuation_ratCast_eq_intCast_of_not_residueCharacteristic_dvd_den
    (F : LocalField.{u, v} K) (q : ℚ)
    (hden : ¬ F.residueCharacteristic ∣ q.den) :
    F.toCompleteDVF.valuation (q : K) =
      F.toCompleteDVF.valuation (q.num : K) := by
  calc
    F.toCompleteDVF.valuation (q : K)
        = F.toCompleteDVF.valuation ((q.num : K) / (q.den : K)) := by
          rw [Rat.cast_def]
    _ = F.toCompleteDVF.valuation (q.num : K) /
        F.toCompleteDVF.valuation (q.den : K) := by
          exact F.toCompleteDVF.valuation.map_div (q.num : K) (q.den : K)
    _ = F.toCompleteDVF.valuation (q.num : K) / 1 := by
          rw [F.valuation_natCast_eq_one_of_not_residueCharacteristic_dvd hden]
    _ = F.toCompleteDVF.valuation (q.num : K) := by
          simp

/-- A rational number with denominator prime to the residue characteristic lies
in the valuation subring.  This is the local `ℤ_(p)` input for the converse
classification in the local-field structure theory, the local-field structure classification. -/
theorem valuation_ratCast_le_one_of_not_residueCharacteristic_dvd_den
    (F : LocalField.{u, v} K) (q : ℚ)
    (hden : ¬ F.residueCharacteristic ∣ q.den) :
    F.toCompleteDVF.valuation (q : K) ≤ 1 := by
  rw [F.valuation_ratCast_eq_intCast_of_not_residueCharacteristic_dvd_den q hden]
  exact F.valuation_intCast_le_one q.num

/-- Valuation-subring membership form of
`valuation_ratCast_le_one_of_not_residueCharacteristic_dvd_den`. -/
theorem ratCast_mem_valuationSubring_of_not_residueCharacteristic_dvd_den
    (F : LocalField.{u, v} K) (q : ℚ)
    (hden : ¬ F.residueCharacteristic ∣ q.den) :
    (q : K) ∈ F.toCompleteDVF.valuation.valuationSubring :=
  (F.toCompleteDVF.mem_valuationSubring_iff (q : K)).2
    (F.valuation_ratCast_le_one_of_not_residueCharacteristic_dvd_den q hden)

/-- In a reduced rational number, if the denominator is divisible by the
residue characteristic then the numerator is not. -/
theorem not_residueCharacteristic_dvd_rat_num_of_dvd_den
    (F : LocalField.{u, v} K) (q : ℚ)
    (hden : F.residueCharacteristic ∣ q.den) :
    ¬ (F.residueCharacteristic : ℤ) ∣ q.num := by
  intro hnum
  have hnumNat : F.residueCharacteristic ∣ q.num.natAbs :=
    (Int.natCast_dvd.mp hnum)
  have hp_one : F.residueCharacteristic = 1 :=
    Nat.eq_one_of_dvd_coprimes q.reduced hnumNat hden
  exact F.residueCharacteristic_prime.ne_one hp_one

/-- For mixed-characteristic local fields, the rational numbers lying in the
valuation subring are exactly those whose denominator is prime to the residue
characteristic. -/
theorem valuation_ratCast_le_one_iff_not_residueCharacteristic_dvd_den
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    F.toCompleteDVF.valuation (q : K) ≤ 1 ↔
      ¬ F.residueCharacteristic ∣ q.den := by
  constructor
  · intro hle hden
    have hnumNot :
        ¬ (F.residueCharacteristic : ℤ) ∣ q.num :=
      F.not_residueCharacteristic_dvd_rat_num_of_dvd_den q hden
    have hnumVal :
        F.toCompleteDVF.valuation (q.num : K) = 1 :=
      F.valuation_intCast_eq_one_of_not_residueCharacteristic_dvd hnumNot
    have hdenValLt :
        F.toCompleteDVF.valuation (q.den : K) < 1 :=
      (F.valuation_natCast_lt_one_iff_residueCharacteristic_dvd q.den).2 hden
    have hdenNe : (q.den : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr q.den_ne_zero
    have hdenValPos :
        0 < F.toCompleteDVF.valuation (q.den : K) :=
      F.toCompleteDVF.valuation.pos_iff.2 hdenNe
    have hqVal :
        F.toCompleteDVF.valuation (q : K) =
          F.toCompleteDVF.valuation (q.num : K) /
            F.toCompleteDVF.valuation (q.den : K) := by
      calc
        F.toCompleteDVF.valuation (q : K)
            = F.toCompleteDVF.valuation ((q.num : K) / (q.den : K)) := by
              rw [Rat.cast_def]
        _ = F.toCompleteDVF.valuation (q.num : K) /
            F.toCompleteDVF.valuation (q.den : K) := by
              exact F.toCompleteDVF.valuation.map_div (q.num : K) (q.den : K)
    have hgt : 1 < F.toCompleteDVF.valuation (q : K) := by
      rw [hqVal, hnumVal]
      simpa [one_div] using (one_lt_inv₀ hdenValPos).2 hdenValLt
    exact (not_lt_of_ge hle) hgt
  · exact F.valuation_ratCast_le_one_of_not_residueCharacteristic_dvd_den q

/-- Valuation-subring membership version of
`valuation_ratCast_le_one_iff_not_residueCharacteristic_dvd_den`. -/
theorem ratCast_mem_valuationSubring_iff_not_residueCharacteristic_dvd_den
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    (q : K) ∈ F.toCompleteDVF.valuation.valuationSubring ↔
      ¬ F.residueCharacteristic ∣ q.den :=
  (F.toCompleteDVF.mem_valuationSubring_iff (q : K)).trans
    (F.valuation_ratCast_le_one_iff_not_residueCharacteristic_dvd_den q)

/-- The restriction of the local-field valuation to `ℚ` has the same valuation
subring as the `p`-adic valuation, where `p` is the residue characteristic. -/
theorem valuation_ratCast_le_one_iff_padicValuation_le_one
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    F.toCompleteDVF.valuation (q : K) ≤ 1 ↔
      Rat.padicValuation F.residueCharacteristic q ≤ 1 :=
  (F.valuation_ratCast_le_one_iff_not_residueCharacteristic_dvd_den q).trans
    (Rat.padicValuation_le_one_iff
      (p := F.residueCharacteristic) (x := q)).symm

/-- Valuation-subring membership version of
`valuation_ratCast_le_one_iff_padicValuation_le_one`. -/
theorem ratCast_mem_valuationSubring_iff_padicValuation_le_one
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    (q : K) ∈ F.toCompleteDVF.valuation.valuationSubring ↔
      Rat.padicValuation F.residueCharacteristic q ≤ 1 :=
  (F.toCompleteDVF.mem_valuationSubring_iff (q : K)).trans
    (F.valuation_ratCast_le_one_iff_padicValuation_le_one q)

/-- The valuation subring pulled back from `K` along the rational embedding is
the usual `p`-adic valuation subring of `ℚ`. -/
theorem ratCast_preimage_valuationSubring_eq_padicValuationSubring
    (F : LocalField.{u, v} K) [CharZero K] :
    F.toCompleteDVF.valuation.valuationSubring.comap (Rat.castHom K) =
      (Rat.padicValuation F.residueCharacteristic).valuationSubring := by
  ext q
  rw [ValuationSubring.mem_comap]
  simpa using F.ratCast_mem_valuationSubring_iff_padicValuation_le_one q

/-- The valuation on `K`, restricted along `ℚ → K`, is equivalent to the
`p`-adic valuation on `ℚ`. -/
theorem ratCast_valuation_isEquiv_padicValuation
    (F : LocalField.{u, v} K) [CharZero K] :
    (F.toCompleteDVF.valuation.comap (Rat.castHom K)).IsEquiv
      (Rat.padicValuation F.residueCharacteristic) := by
  refine (Valuation.isEquiv_iff_valuationSubring
    (v₁ := F.toCompleteDVF.valuation.comap (Rat.castHom K))
    (v₂ := Rat.padicValuation F.residueCharacteristic)).2 ?_
  ext q
  change F.toCompleteDVF.valuation ((Rat.castHom K) q) ≤ 1 ↔
    Rat.padicValuation F.residueCharacteristic q ≤ 1
  simpa using F.valuation_ratCast_le_one_iff_padicValuation_le_one q

/-- In positive equal characteristic, the residue field has the same
characteristic as the local field. -/
theorem residueField_charP_of_charP
    (F : LocalField.{u, v} K) (p : ℕ) [CharP K p] (hp : p ≠ 0) :
    CharP F.residueField p := by
  exact CharP.of_ringHom_of_ne_zero F.residueMap p hp

/-- In positive equal characteristic, the residue characteristic is the
characteristic of the local field. -/
theorem residueCharacteristic_eq_of_charP
    (F : LocalField.{u, v} K) (p : ℕ) [CharP K p] (hp : p ≠ 0) :
    F.residueCharacteristic = p := by
  have : CharP F.residueField p :=
    F.residueField_charP_of_charP p hp
  exact ringChar.eq F.residueField p

/-- Any finite residue-field algebra over a local field residue field is
algebraic. -/
theorem residueExtension_isAlgebraic_of_finite
    (F : LocalField.{u, v} K) {k : Type w} [Field k]
    [Algebra F.residueField k] [Finite k] :
    Algebra.IsAlgebraic F.residueField k := by
  let : Module.Finite F.residueField k :=
    Module.Finite.of_finite
  exact Algebra.IsAlgebraic.of_finite F.residueField k

/-- Any finite residue-field algebra over a local field residue field is
separable. -/
theorem residueExtension_isSeparable_of_finite
    (F : LocalField.{u, v} K) {k : Type w} [Field k]
    [Algebra F.residueField k] [Finite k] :
    Algebra.IsSeparable F.residueField k := by
  let : Module.Finite F.residueField k :=
    Module.Finite.of_finite
  let : Algebra.IsAlgebraic F.residueField k :=
    Algebra.IsAlgebraic.of_finite F.residueField k
  infer_instance

/-- The residue-field algebra between two local-field packages is separable. -/
theorem residueExtension_isSeparable
    (F : LocalField.{u, v} K) {L : Type w} [Field L]
    (E : LocalField.{w, x} L) [Algebra F.residueField E.residueField] :
    Algebra.IsSeparable F.residueField E.residueField :=
  F.residueExtension_isSeparable_of_finite (k := E.residueField)

end LocalField
end LocalFieldTheory.DiscreteValuationField
