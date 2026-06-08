/-
Copyright (c) 2026 Matevz Miščič, Maša Žaucer, Job Petrovčič. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matevz Miščič, Maša Žaucer, Job Petrovčič
-/
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.RingTheory.NonUnitalSubring.Defs
import Mathlib.Tactic.NoncommRing

/-!
# Division subrings and division rings

Defines `IsDivisionSubring` and `IsDivisionRing`, supplies the conversion to
Mathlib's `DivisionRing`, and shows that an isomorphism of rings transports the
division-ring property.
-/

namespace LeanPool.ArtinWedderburn

variable {R : Type*} [Ring R]

/-- `S` is a division subring with identity `e` when it contains a nonzero element
and every nonzero member has a left inverse inside `S` equal to `e`. -/
def IsDivisionSubring (S : NonUnitalSubring R) (e : R) : Prop :=
  (∃ x : R, x ∈ S ∧ x ≠ 0) ∧
    (∀ x : R, x ∈ S → x ≠ 0 → ∃ y : R, y ∈ S ∧ y * x = e)

/-- A ring `R` is a division ring when it is nontrivial and every nonzero element has
a two-sided multiplicative inverse. -/
def IsDivisionRing (R : Type*) [Ring R] : Prop :=
  (∃ x : R, x ≠ 0) ∧ (∀ x : R, x ≠ 0 → ∃ y : R, y * x = 1 ∧ x * y = 1)

-- if every nonzero element has a left inverse then the ring is a division ring
theorem left_inv_implies_divring [Nontrivial R]
    (h : ∀ x : R, x ≠ 0 → ∃ y : R, y * x = 1) : IsDivisionRing R := by
  unfold IsDivisionRing
  refine ⟨exists_ne 0, ?_⟩
  intro x x_nz
  let ⟨y, hy⟩ := h x x_nz
  have y_nz : y ≠ 0 := left_ne_zero_of_mul_eq_one hy
  let ⟨z, hz⟩ := h y y_nz
  have x_eq_z : x = z := by
    calc x = (z * y) * x := by rw [hz]; noncomm_ring
        _ = z * (y * x) := by noncomm_ring
        _ = z := by rw [hy]; noncomm_ring
  refine ⟨y, hy, ?_⟩
  rw [x_eq_z]
  exact hz

/-- Promote a proof of `IsDivisionRing R` to a Mathlib `DivisionRing R` instance. -/
@[reducible]
noncomputable
def IsDivisionRingToDivisionRing (div : IsDivisionRing R) : DivisionRing R := by
  unfold IsDivisionRing at div
  have nontriv : Nontrivial R := by
    let ⟨⟨x, hx⟩, _⟩ := div
    exact ⟨x, 0, hx⟩
  apply DivisionRing.ofIsUnitOrEqZero
  intro a
  rw [isUnit_iff_exists]
  let ⟨_, h⟩ := div
  by_cases ha : a = 0
  · right
    exact ha
  · left
    specialize h a ha
    obtain ⟨y, ⟨hy1, hy2⟩⟩ := h
    exact ⟨y, hy2, hy1⟩

-- a ring isomorphic to a division ring is itself a division ring
theorem isomorphic_ring_div {R' : Type*} [Ring R'] (f : R ≃+* R') (h_div : IsDivisionRing R) :
    IsDivisionRing R' := by
  unfold IsDivisionRing at *
  let ⟨⟨x, hx⟩, h⟩ := h_div
  let ⟨y, hy⟩ := h x hx
  refine ⟨⟨f x, ?_⟩, ?_⟩
  · rw [RingEquiv.map_ne_zero_iff]
    exact hx
  · intro x' hx'
    let ⟨a, ha⟩ : ∃ (a : R), f a = x' := ⟨f.symm x', f.right_inv x'⟩
    let ⟨b, hb⟩ := h a (by rw [← ha] at hx'; exact (RingEquiv.map_ne_zero_iff f).mp hx')
    refine ⟨f b, ?_⟩
    rw [← ha]
    refine ⟨?_, ?_⟩
    · rw [map_mul_eq_one]
      exact hb.1
    · rw [map_mul_eq_one]
      exact hb.2

end LeanPool.ArtinWedderburn
