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
  refine ⟨exists_ne 0, fun x x_nz => ?_⟩
  obtain ⟨y, hy⟩ := h x x_nz
  obtain ⟨z, hz⟩ := h y (left_ne_zero_of_mul_eq_one hy)
  have x_eq_z : x = z := by
    calc x = (z * y) * x := by rw [hz]; noncomm_ring
      _ = z := by rw [mul_assoc, hy]
                  noncomm_ring
  exact ⟨y, hy, x_eq_z ▸ hz⟩

/-- Promote a proof of `IsDivisionRing R` to a Mathlib `DivisionRing R` instance. -/
@[reducible]
noncomputable
def IsDivisionRingToDivisionRing (div : IsDivisionRing R) : DivisionRing R := by
  unfold IsDivisionRing at div
  haveI : Nontrivial R := by
    obtain ⟨⟨x, hx⟩, _⟩ := div
    exact ⟨x, 0, hx⟩
  apply DivisionRing.ofIsUnitOrEqZero
  intro a
  rw [isUnit_iff_exists]
  by_cases ha : a = 0
  · exact Or.inr ha
  · obtain ⟨y, hy1, hy2⟩ := div.2 a ha
    exact Or.inl ⟨y, hy2, hy1⟩

-- a ring isomorphic to a division ring is itself a division ring
theorem isomorphic_ring_div {R' : Type*} [Ring R'] (f : R ≃+* R') (h_div : IsDivisionRing R) :
    IsDivisionRing R' := by
  unfold IsDivisionRing at *
  have hfnz : f h_div.1.choose ≠ 0 := (RingEquiv.map_ne_zero_iff f).mpr h_div.1.choose_spec
  refine ⟨⟨f h_div.1.choose, hfnz⟩, fun x' hx' => ?_⟩
  obtain ⟨a, rfl⟩ : ∃ a : R, f a = x' := ⟨f.symm x', f.right_inv x'⟩
  obtain ⟨b, hb1, hb2⟩ := h_div.2 a ((RingEquiv.map_ne_zero_iff f).mp hx')
  refine ⟨f b, ?_, ?_⟩
  · rw [map_mul_eq_one]
    exact hb1
  · rw [map_mul_eq_one]
    exact hb2

end LeanPool.ArtinWedderburn
