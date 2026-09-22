/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.OmnificInteger
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Prime.Defs

import Mathlib.Algebra.Divisibility.Units

/-!
# Factorisation predicates quantified over omnific ZFC codes

All factors and divisibility witnesses below range over the full class of omnific game codes.
Products use Conway's recursive multiplication and equality is Conway equivalence. The
surjectivity of evaluation identifies these formulas with the usual ring predicates.
-/

universe u

public noncomputable section

namespace ZFSet

/-- A ZFC game code satisfying Conway's omnific-integer equation. -/
structure OmnificCode where
  /-- The underlying ZFC game code satisfying the omnific-integer condition. -/
  code : GameCode.{u}
  omnific : code.IsOmnificInteger

namespace OmnificCode

/-- The actual omnific integer represented by a set code. -/
def value (x : OmnificCode.{u}) : _root_.Surreal.OmnificInteger.{u} :=
  ⟨Surreal.toSurreal (Surreal.mk x.code x.omnific.isNumeric),
    _root_.Surreal.mem_omnificIntegers.2
      ((GameCode.isOmnificInteger_iff_toSurreal _ _).1 x.omnific)⟩

@[simp]
theorem coe_value (x : OmnificCode.{u}) : (x.value : _root_.Surreal.{u}) =
    Surreal.toSurreal (Surreal.mk x.code x.omnific.isNumeric) := (rfl)

/-- Every omnific integer, including every possible factor or divisor, has a set code. -/
theorem value_surjective : Function.Surjective (value.{u}) := by
  intro b
  let c := GameCode.ofIGame (b : _root_.Surreal.{u}).out
  have hc : c.IsNumeric := (GameCode.isNumeric_ofIGame _).2 inferInstance
  have hval : Surreal.toSurreal (Surreal.mk c hc) = (b : _root_.Surreal.{u}) := by
    rw [Surreal.toSurreal_mk]
    simp only [c, GameCode.toIGame_ofIGame, _root_.Surreal.out_eq]
  have hb : c.IsOmnificInteger := (GameCode.isOmnificInteger_iff_toSurreal c hc).2 (by
    rw [hval]
    exact _root_.Surreal.mem_omnificIntegers.1 b.2)
  exact ⟨⟨c, hb⟩, Subtype.ext hval⟩

/-- Equality of omnific codes means Conway equivalence, not literal code equality. -/
def Equivalent (x y : OmnificCode.{u}) : Prop := AntisymmRel (· ≤ ·) x.code y.code

/-- The equality relation on codes agrees exactly with equality of their values. -/
theorem equivalent_iff (x y : OmnificCode.{u}) : Equivalent x y ↔ x.value = y.value := by
  rw [Subtype.ext_iff, coe_value, coe_value]
  rw [Surreal.toSurreal_injective.eq_iff, Surreal.mk_eq_mk]
  rfl

instance : Zero OmnificCode.{u} := ⟨⟨0,
  (GameCode.isOmnificInteger_iff_toSurreal 0 GameCode.isNumeric_zero).2 (by
    rw [Surreal.mk_zero, Surreal.toSurreal_zero]
    exact _root_.Surreal.isOmnificInteger_zero)⟩⟩

instance : One OmnificCode.{u} := ⟨⟨1,
  (GameCode.isOmnificInteger_iff_toSurreal 1 GameCode.isNumeric_one).2 (by
    rw [Surreal.mk_one, Surreal.toSurreal_one]
    exact _root_.Surreal.isOmnificInteger_one)⟩⟩

instance : Mul OmnificCode.{u} := ⟨fun x y ↦ ⟨x.code * y.code,
  (GameCode.isOmnificInteger_iff_toSurreal _
    (x.omnific.isNumeric.mul y.omnific.isNumeric)).2 (by
    rw [Surreal.mk_mul _ _ x.omnific.isNumeric y.omnific.isNumeric, Surreal.toSurreal_mul]
    exact ((GameCode.isOmnificInteger_iff_toSurreal _ _).1 x.omnific).mul
      ((GameCode.isOmnificInteger_iff_toSurreal _ _).1 y.omnific))⟩⟩

@[simp]
theorem code_zero : (0 : OmnificCode.{u}).code = 0 := (rfl)

@[simp]
theorem code_one : (1 : OmnificCode.{u}).code = 1 := (rfl)

@[simp]
theorem code_mul (x y : OmnificCode.{u}) : (x * y).code = x.code * y.code := (rfl)

@[simp]
theorem value_zero : (0 : OmnificCode.{u}).value = 0 := by
  apply Subtype.ext
  simp only [coe_value, code_zero, Surreal.mk_zero, Surreal.toSurreal_zero]
  rfl

@[simp]
theorem value_one : (1 : OmnificCode.{u}).value = 1 := by
  apply Subtype.ext
  simp only [coe_value, code_one, Surreal.mk_one, Surreal.toSurreal_one]
  rfl

@[simp]
theorem value_mul (x y : OmnificCode.{u}) : (x * y).value = x.value * y.value := by
  apply Subtype.ext
  change Surreal.toSurreal (Surreal.mk (x.code * y.code)
    (x.omnific.isNumeric.mul y.omnific.isNumeric)) =
      Surreal.toSurreal (Surreal.mk x.code x.omnific.isNumeric) *
        Surreal.toSurreal (Surreal.mk y.code y.omnific.isNumeric)
  rw [Surreal.mk_mul _ _ x.omnific.isNumeric y.omnific.isNumeric, Surreal.toSurreal_mul]

/-- Divisibility with an omnific set-code witness and Conway equality. -/
def Divides (x y : OmnificCode.{u}) : Prop := ∃ z, Equivalent y (x * z)

/-- Units are codes with an omnific multiplicative inverse. -/
def IsUnit (x : OmnificCode.{u}) : Prop := Divides x 1

/-- Irreducibility tested against every pair of omnific codes. -/
def IsIrreducible (x : OmnificCode.{u}) : Prop :=
  ¬x.IsUnit ∧ ∀ a b, Equivalent x (a * b) → a.IsUnit ∨ b.IsUnit

/-- Primality tested against every pair of omnific codes and every divisibility witness. -/
def IsPrime (x : OmnificCode.{u}) : Prop :=
  ¬Equivalent x 0 ∧ ¬x.IsUnit ∧
    ∀ a b, Divides x (a * b) → Divides x a ∨ Divides x b

/-- Code divisibility is exactly divisibility in the omnific-integer ring. -/
theorem divides_iff (x y : OmnificCode.{u}) : Divides x y ↔ x.value ∣ y.value := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.value, by simpa only [value_mul] using (equivalent_iff _ _).1 hz⟩
  · rintro ⟨z, hz⟩
    obtain ⟨c, rfl⟩ := value_surjective z
    exact ⟨c, (equivalent_iff _ _).2 (by simpa only [value_mul] using hz)⟩

/-- Code units are exactly units in the omnific-integer ring. -/
theorem isUnit_iff (x : OmnificCode.{u}) : x.IsUnit ↔ _root_.IsUnit x.value := by
  rw [IsUnit, divides_iff, value_one, isUnit_iff_dvd_one]

/-- Code irreducibility is the unrestricted ring-theoretic predicate. -/
theorem isIrreducible_iff (x : OmnificCode.{u}) :
    x.IsIrreducible ↔ Irreducible x.value := by
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨fun hv ↦ hu ((isUnit_iff x).2 hv), ?_⟩
    intro a b hab
    obtain ⟨ca, rfl⟩ := value_surjective a
    obtain ⟨cb, rfl⟩ := value_surjective b
    have hc := h ca cb ((equivalent_iff _ _).2 (by simpa only [value_mul] using hab))
    exact hc.imp (isUnit_iff _).1 (isUnit_iff _).1
  · intro h
    refine ⟨fun hu ↦ h.not_isUnit ((isUnit_iff _).1 hu), ?_⟩
    intro a b hab
    have hv : x.value = a.value * b.value := by
      simpa only [value_mul] using (equivalent_iff _ _).1 hab
    exact (h.isUnit_or_isUnit hv).imp (isUnit_iff _).2 (isUnit_iff _).2

/-- Code primality is the unrestricted ring-theoretic predicate. -/
theorem isPrime_iff (x : OmnificCode.{u}) : x.IsPrime ↔ Prime x.value := by
  constructor
  · rintro ⟨hz, hu, h⟩
    refine ⟨fun hv ↦ hz ((equivalent_iff _ _).2 (by simpa only [value_zero] using hv)),
      fun hv ↦ hu ((isUnit_iff _).2 hv), ?_⟩
    intro a b hab
    obtain ⟨ca, rfl⟩ := value_surjective a
    obtain ⟨cb, rfl⟩ := value_surjective b
    have hc := h ca cb ((divides_iff _ _).2 (by simpa only [value_mul] using hab))
    exact hc.imp (divides_iff _ _).1 (divides_iff _ _).1
  · intro h
    refine ⟨fun hz ↦ h.ne_zero (by
      simpa only [value_zero] using (equivalent_iff _ _).1 hz),
      fun hu ↦ h.not_isUnit ((isUnit_iff _).1 hu), ?_⟩
    intro a b hab
    have hv : x.value ∣ a.value * b.value := by
      simpa only [value_mul] using (divides_iff _ _).1 hab
    exact (h.dvd_or_dvd hv).imp (divides_iff _ _).2 (divides_iff _ _).2

end OmnificCode
end ZFSet
