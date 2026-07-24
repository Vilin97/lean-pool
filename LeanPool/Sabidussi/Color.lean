/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# The four colours used in the Sabidussi proof

This file contains the elementary algebra over `F₂²` used by the proof. We use an explicit
product so that the three admissible local frames can be given by concrete formulas.
-/

namespace Sabidussi

open scoped BigOperators

/-- The field with two elements. -/
abbrev F₂ := ZMod 2

/-- The four-element colour space. -/
abbrev Color := F₂ × F₂

@[simp]
theorem F₂_add_self (x : F₂) : x + x = 0 := ZModModule.add_self x

@[simp]
theorem color_add_self (x : Color) : x + x = 0 := by
  ext <;> simp

theorem F₂_add_shuffle (a b : F₂) : a + (b + (a + b)) = 0 := by
  calc
    a + (b + (a + b)) = (a + a) + (b + b) := by abel
    _ = 0 := by simp

/-- The alternating form polarizing `quadratic`. -/
def bracket (x y : Color) : F₂ := x.1 * y.2 + x.2 * y.1

/-- The quadratic form detecting the colour `(1, 1)`. -/
def quadratic (x : Color) : F₂ := x.1 * x.2

@[simp]
theorem bracket_apply (x y : Color) : bracket x y = x.1 * y.2 + x.2 * y.1 := rfl

@[simp]
theorem quadratic_apply (x : Color) : quadratic x = x.1 * x.2 := rfl

theorem bracket_zero_left (x : Color) : bracket 0 x = 0 := by
  simp [bracket]

theorem bracket_zero_right (x : Color) : bracket x 0 = 0 := by
  simp [bracket]

theorem bracket_add_left (x y z : Color) :
    bracket (x + y) z = bracket x z + bracket y z := by
  simp only [bracket, Prod.fst_add, Prod.snd_add]
  ring

theorem bracket_add_right (x y z : Color) :
    bracket x (y + z) = bracket x y + bracket x z := by
  simp only [bracket, Prod.fst_add, Prod.snd_add]
  ring

/-- Bracketing with a fixed left argument, as an additive homomorphism. -/
def bracketRightHom (x : Color) : Color →+ F₂ where
  toFun := bracket x
  map_zero' := bracket_zero_right x
  map_add' := bracket_add_right x

@[simp]
theorem bracketRightHom_apply (x y : Color) : bracketRightHom x y = bracket x y := rfl

theorem sum_bracket_right {I : Type*} [Fintype I] (x : Color) (f : I → Color) :
    ∑ i, bracket x (f i) = bracket x (∑ i, f i) := by
  change ∑ i, bracketRightHom x (f i) = bracketRightHom x (∑ i, f i)
  exact (map_sum (bracketRightHom x) f Finset.univ).symm

theorem bracket_comm (x y : Color) : bracket x y = bracket y x := by
  simp [bracket, add_comm, mul_comm]

theorem bracket_self (x : Color) : bracket x x = 0 := by
  simp [bracket, mul_comm]

theorem quadratic_add (x y : Color) :
    quadratic (x + y) = quadratic x + quadratic y + bracket x y := by
  simp only [quadratic, bracket, Prod.fst_add, Prod.snd_add]
  ring

/-- The three locally admissible difference vectors at a 6-valent vertex. -/
def tripleDifference (t : Color) : Fin 3 → Color
  | ⟨0, _⟩ => t
  | ⟨1, _⟩ => (t.2, t.1 + t.2)
  | ⟨2, _⟩ => (t.1 + t.2, t.1)

@[simp]
theorem tripleDifference_zero (t : Color) : tripleDifference t 0 = t := rfl

@[simp]
theorem tripleDifference_one (t : Color) :
    tripleDifference t 1 = (t.2, t.1 + t.2) := rfl

@[simp]
theorem tripleDifference_two (t : Color) :
    tripleDifference t 2 = (t.1 + t.2, t.1) := rfl

theorem sum_tripleDifference (t : Color) : ∑ i, tripleDifference t i = 0 := by
  rw [Fin.sum_univ_three]
  change t + (t.2, t.1 + t.2) + (t.1 + t.2, t.1) = 0
  ext
  · change t.1 + t.2 + (t.1 + t.2) = 0
    exact F₂_add_self (t.1 + t.2)
  · change t.2 + (t.1 + t.2) + t.1 = 0
    calc
      t.2 + (t.1 + t.2) + t.1 = (t.1 + t.1) + (t.2 + t.2) := by abel
      _ = 0 := by simp

theorem tripleDifference_ne_zero (t : Color) (ht : t ≠ 0) (i : Fin 3) :
    tripleDifference t i ≠ 0 := by
  fin_cases i
  · simpa using ht
  · intro h
    apply ht
    rcases Prod.mk_eq_zero.mp h with ⟨h₂, hsum⟩
    ext
    · simpa [h₂] using hsum
    · exact h₂
  · intro h
    apply ht
    rcases Prod.mk_eq_zero.mp h with ⟨hsum, h₁⟩
    ext
    · exact h₁
    · simpa [h₁] using hsum

/-- At a 4-valent vertex the two local differences coincide. -/
def doubleDifference (t : Color) : Fin 2 → Color
  | ⟨0, _⟩ => t
  | ⟨1, _⟩ => t

theorem sum_doubleDifference (t : Color) : ∑ i, doubleDifference t i = 0 := by
  rw [Fin.sum_univ_two]
  exact color_add_self t

theorem doubleDifference_ne_zero (t : Color) (ht : t ≠ 0) (i : Fin 2) :
    doubleDifference t i ≠ 0 := by
  fin_cases i <;> exact ht

/-- The local quadratic contribution from two equal nonzero differences vanishes. -/
theorem double_local_quadratic (t : Color) :
    (∑ i, quadratic (doubleDifference t i)) +
      (∑ i, ∑ j,
        if j < i then bracket (doubleDifference t i) (doubleDifference t j) else 0) = 0 := by
  simp only [Fin.sum_univ_two, doubleDifference, quadratic, bracket]
  norm_num
  ring_nf
  rw [show (2 : F₂) = 0 from ZMod.natCast_self 2]
  simp

/-- The local quadratic contribution from the three `tripleDifference`s vanishes. -/
theorem triple_local_quadratic (t : Color) :
    (∑ i, quadratic (tripleDifference t i)) +
      (∑ i, ∑ j,
        if j < i then bracket (tripleDifference t i) (tripleDifference t j) else 0) = 0 := by
  simp only [Fin.sum_univ_three, tripleDifference, quadratic, bracket]
  split_ifs <;> try omega
  ring_nf
  rw [show (8 : F₂) = 0 from (show Even 8 by exact ⟨4, rfl⟩).natCast_zmod_two,
    show (4 : F₂) = 0 from (show Even 4 by exact ⟨2, rfl⟩).natCast_zmod_two]
  simp

end Sabidussi
