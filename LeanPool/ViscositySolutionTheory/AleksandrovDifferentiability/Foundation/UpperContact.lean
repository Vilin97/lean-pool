/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Upper quadratic contacts

This file contains the upper-contact predicate used in the Aleksandrov proof route.
-/

@[expose] public section

namespace AleksandrovDifferentiability

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `u` has an upper quadratic contact of opening `a` and slope `p` at `x`, relative to `s`. -/
def HasUpperContactWithSlopeOn (s : Set E) (u : E → ℝ) (x p : E) (a : ℝ) : Prop :=
  x ∈ s ∧ ∀ y ∈ s,
    u y ≤ u x + inner ℝ p (y - x) + (a / 2) * ‖y - x‖ ^ 2

/-- `u` has an upper quadratic contact of opening `a` at `x`, relative to `s`.

The vector `p` is the slope of the touching quadratic. The definition does not require
`0 ≤ a`; estimates that use the geometric opening should carry that hypothesis explicitly.
-/
def HasUpperContactOn (s : Set E) (u : E → ℝ) (x : E) (a : ℝ) : Prop :=
  ∃ p : E, HasUpperContactWithSlopeOn s u x p a

/-- The upper-contact opening is at most `A`, expressed through the approximation property used
in proofs: every larger opening `A + η`, `η > 0`, has an upper contact. -/
def HasUpperContactOpeningAtMostOn (s : Set E) (u : E → ℝ) (x : E) (A : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → HasUpperContactOn s u x (A + η)

/-- Fixed-slope version of `HasUpperContactOpeningAtMostOn`: every larger opening `A + η`,
`η > 0`, has an upper contact with the prescribed slope `p`. -/
def HasUpperContactWithSlopeOpeningAtMostOn
    (s : Set E) (u : E → ℝ) (x p : E) (A : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → HasUpperContactWithSlopeOn s u x p (A + η)

/-- Points of `s` where `u` has an upper quadratic contact of opening `a`. -/
def upperContactSet (s : Set E) (u : E → ℝ) (a : ℝ) : Set E :=
  {x | HasUpperContactOn s u x a}

/-- Points of `s` where `u` has an upper quadratic contact of opening `a` and slope `p`. -/
def upperContactWithSlopeSet (s : Set E) (u : E → ℝ) (p : E) (a : ℝ) : Set E :=
  {x | HasUpperContactWithSlopeOn s u x p a}

/-- Points of `s` where the upper-contact opening is at most `A`. -/
def upperContactOpeningAtMostSet (s : Set E) (u : E → ℝ) (A : ℝ) : Set E :=
  {x | HasUpperContactOpeningAtMostOn s u x A}

/-- Points of `s` where the upper-contact opening is at most `A` with prescribed slope `p`. -/
def upperContactWithSlopeOpeningAtMostSet
    (s : Set E) (u : E → ℝ) (p : E) (A : ℝ) : Set E :=
  {x | HasUpperContactWithSlopeOpeningAtMostOn s u x p A}

@[simp]
theorem mem_upperContactSet {s : Set E} {u : E → ℝ} {x : E} {a : ℝ} :
    x ∈ upperContactSet s u a ↔ HasUpperContactOn s u x a :=
  Iff.rfl

@[simp]
theorem mem_upperContactWithSlopeSet {s : Set E} {u : E → ℝ} {x p : E} {a : ℝ} :
    x ∈ upperContactWithSlopeSet s u p a ↔ HasUpperContactWithSlopeOn s u x p a :=
  Iff.rfl

@[simp]
theorem mem_upperContactOpeningAtMostSet {s : Set E} {u : E → ℝ} {x : E} {A : ℝ} :
    x ∈ upperContactOpeningAtMostSet s u A ↔ HasUpperContactOpeningAtMostOn s u x A :=
  Iff.rfl

@[simp]
theorem mem_upperContactWithSlopeOpeningAtMostSet
    {s : Set E} {u : E → ℝ} {x p : E} {A : ℝ} :
    x ∈ upperContactWithSlopeOpeningAtMostSet s u p A ↔
      HasUpperContactWithSlopeOpeningAtMostOn s u x p A :=
  Iff.rfl

theorem HasUpperContactWithSlopeOn.mem {s : Set E} {u : E → ℝ} {x p : E} {a : ℝ}
    (h : HasUpperContactWithSlopeOn s u x p a) :
    x ∈ s :=
  h.1

theorem HasUpperContactWithSlopeOn.upper_inequality
    {s : Set E} {u : E → ℝ} {x p y : E} {a : ℝ}
    (h : HasUpperContactWithSlopeOn s u x p a) (hy : y ∈ s) :
    u y ≤ u x + inner ℝ p (y - x) + (a / 2) * ‖y - x‖ ^ 2 :=
  h.2 y hy

theorem HasUpperContactWithSlopeOn.hasUpperContactOn
    {s : Set E} {u : E → ℝ} {x p : E} {a : ℝ}
    (h : HasUpperContactWithSlopeOn s u x p a) :
    HasUpperContactOn s u x a :=
  ⟨p, h⟩

theorem HasUpperContactWithSlopeOn.mono_opening
    {s : Set E} {u : E → ℝ} {x p : E} {a b : ℝ}
    (h : HasUpperContactWithSlopeOn s u x p a) (hab : a ≤ b) :
    HasUpperContactWithSlopeOn s u x p b := by
  refine ⟨h.mem, ?_⟩
  intro y hy
  have hupper := h.upper_inequality (y := y) hy
  have hhalf : a / 2 ≤ b / 2 := by linarith
  have hquad :
      (a / 2) * ‖y - x‖ ^ 2 ≤ (b / 2) * ‖y - x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)
  linarith

theorem HasUpperContactWithSlopeOn.mono_opening_add_nonneg
    {s : Set E} {u : E → ℝ} {x p : E} {a c : ℝ}
    (h : HasUpperContactWithSlopeOn s u x p a) (hc : 0 ≤ c) :
    HasUpperContactWithSlopeOn s u x p (a + c) :=
  h.mono_opening (by linarith)

theorem HasUpperContactOn.mem {s : Set E} {u : E → ℝ} {x : E} {a : ℝ}
    (h : HasUpperContactOn s u x a) :
    x ∈ s := by
  rcases h with ⟨p, hp⟩
  exact hp.mem

theorem HasUpperContactOn.exists_slope {s : Set E} {u : E → ℝ} {x : E} {a : ℝ}
    (h : HasUpperContactOn s u x a) :
    ∃ p : E, ∀ y ∈ s,
      u y ≤ u x + inner ℝ p (y - x) + (a / 2) * ‖y - x‖ ^ 2 := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, fun y hy ↦ hp.upper_inequality (y := y) hy⟩

theorem HasUpperContactOn.exists_slope_contact
    {s : Set E} {u : E → ℝ} {x : E} {a : ℝ}
    (h : HasUpperContactOn s u x a) :
    ∃ p : E, HasUpperContactWithSlopeOn s u x p a :=
  h

theorem HasUpperContactOn.mono_opening
    {s : Set E} {u : E → ℝ} {x : E} {a b : ℝ}
    (h : HasUpperContactOn s u x a) (hab : a ≤ b) :
    HasUpperContactOn s u x b := by
  rcases h.exists_slope_contact with ⟨p, hp⟩
  exact (hp.mono_opening hab).hasUpperContactOn

theorem HasUpperContactOn.mono_opening_add_nonneg
    {s : Set E} {u : E → ℝ} {x : E} {a c : ℝ}
    (h : HasUpperContactOn s u x a) (hc : 0 ≤ c) :
    HasUpperContactOn s u x (a + c) :=
  h.mono_opening (by linarith)

theorem HasUpperContactOpeningAtMostOn.hasUpperContactOn_add_pos
    {s : Set E} {u : E → ℝ} {x : E} {A η : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hη : 0 < η) :
    HasUpperContactOn s u x (A + η) :=
  h η hη

theorem HasUpperContactOpeningAtMostOn.exists_slope_contact_add_pos
    {s : Set E} {u : E → ℝ} {x : E} {A η : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hη : 0 < η) :
    ∃ p : E, HasUpperContactWithSlopeOn s u x p (A + η) :=
  (h.hasUpperContactOn_add_pos hη).exists_slope_contact

theorem HasUpperContactOpeningAtMostOn.mem
    {s : Set E} {u : E → ℝ} {x : E} {A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) :
    x ∈ s :=
  (h.hasUpperContactOn_add_pos zero_lt_one).mem

theorem HasUpperContactOpeningAtMostOn.mono_bound
    {s : Set E} {u : E → ℝ} {x : E} {A B : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hAB : A ≤ B) :
    HasUpperContactOpeningAtMostOn s u x B := by
  intro η hη
  exact (h.hasUpperContactOn_add_pos hη).mono_opening (by linarith)

theorem HasUpperContactOpeningAtMostOn.mono_bound_add_nonneg
    {s : Set E} {u : E → ℝ} {x : E} {A c : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hc : 0 ≤ c) :
    HasUpperContactOpeningAtMostOn s u x (A + c) :=
  h.mono_bound (by linarith)

theorem HasUpperContactOpeningAtMostOn.of_hasUpperContactOn
    {s : Set E} {u : E → ℝ} {x : E} {A : ℝ}
    (h : HasUpperContactOn s u x A) :
    HasUpperContactOpeningAtMostOn s u x A := by
  intro η hη
  exact h.mono_opening_add_nonneg (le_of_lt hη)

theorem HasUpperContactWithSlopeOpeningAtMostOn.hasUpperContactWithSlopeOn_add_pos
    {s : Set E} {u : E → ℝ} {x p : E} {A η : ℝ}
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A) (hη : 0 < η) :
    HasUpperContactWithSlopeOn s u x p (A + η) :=
  h η hη

theorem HasUpperContactWithSlopeOpeningAtMostOn.hasUpperContactOpeningAtMostOn
    {s : Set E} {u : E → ℝ} {x p : E} {A : ℝ}
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A) :
    HasUpperContactOpeningAtMostOn s u x A := by
  intro η hη
  exact (h.hasUpperContactWithSlopeOn_add_pos hη).hasUpperContactOn

theorem HasUpperContactWithSlopeOpeningAtMostOn.mem
    {s : Set E} {u : E → ℝ} {x p : E} {A : ℝ}
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A) :
    x ∈ s :=
  (h.hasUpperContactWithSlopeOn_add_pos zero_lt_one).mem

theorem HasUpperContactWithSlopeOpeningAtMostOn.mono_bound
    {s : Set E} {u : E → ℝ} {x p : E} {A B : ℝ}
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A) (hAB : A ≤ B) :
    HasUpperContactWithSlopeOpeningAtMostOn s u x p B := by
  intro η hη
  exact (h.hasUpperContactWithSlopeOn_add_pos hη).mono_opening (by linarith)

theorem HasUpperContactWithSlopeOpeningAtMostOn.mono_bound_add_nonneg
    {s : Set E} {u : E → ℝ} {x p : E} {A c : ℝ}
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A) (hc : 0 ≤ c) :
    HasUpperContactWithSlopeOpeningAtMostOn s u x p (A + c) :=
  h.mono_bound (by linarith)

theorem HasUpperContactWithSlopeOpeningAtMostOn.of_hasUpperContactWithSlopeOn
    {s : Set E} {u : E → ℝ} {x p : E} {A : ℝ}
    (h : HasUpperContactWithSlopeOn s u x p A) :
    HasUpperContactWithSlopeOpeningAtMostOn s u x p A := by
  intro η hη
  exact h.mono_opening_add_nonneg (le_of_lt hη)

theorem upperContactWithSlopeSet_subset_upperContactSet
    {s : Set E} {u : E → ℝ} {p : E} {a : ℝ} :
    upperContactWithSlopeSet s u p a ⊆ upperContactSet s u a := by
  intro x hx
  exact hx.hasUpperContactOn

theorem upperContactSet_subset_domain {s : Set E} {u : E → ℝ} {a : ℝ} :
    upperContactSet s u a ⊆ s := by
  intro x hx
  exact hx.mem

theorem upperContactWithSlopeSet_subset_domain
    {s : Set E} {u : E → ℝ} {p : E} {a : ℝ} :
    upperContactWithSlopeSet s u p a ⊆ s := by
  intro x hx
  exact hx.mem

theorem upperContactSet_mono_opening
    {s : Set E} {u : E → ℝ} {a b : ℝ} (hab : a ≤ b) :
    upperContactSet s u a ⊆ upperContactSet s u b := by
  intro x hx
  exact hx.mono_opening hab

theorem upperContactWithSlopeSet_mono_opening
    {s : Set E} {u : E → ℝ} {p : E} {a b : ℝ} (hab : a ≤ b) :
    upperContactWithSlopeSet s u p a ⊆ upperContactWithSlopeSet s u p b := by
  intro x hx
  exact hx.mono_opening hab

theorem upperContactSet_subset_upperContactOpeningAtMostSet
    {s : Set E} {u : E → ℝ} {A : ℝ} :
    upperContactSet s u A ⊆ upperContactOpeningAtMostSet s u A := by
  intro x hx
  exact HasUpperContactOpeningAtMostOn.of_hasUpperContactOn hx

theorem upperContactWithSlopeSet_subset_upperContactWithSlopeOpeningAtMostSet
    {s : Set E} {u : E → ℝ} {p : E} {A : ℝ} :
    upperContactWithSlopeSet s u p A ⊆ upperContactWithSlopeOpeningAtMostSet s u p A := by
  intro x hx
  exact HasUpperContactWithSlopeOpeningAtMostOn.of_hasUpperContactWithSlopeOn hx

theorem upperContactWithSlopeOpeningAtMostSet_subset_upperContactOpeningAtMostSet
    {s : Set E} {u : E → ℝ} {p : E} {A : ℝ} :
    upperContactWithSlopeOpeningAtMostSet s u p A ⊆ upperContactOpeningAtMostSet s u A := by
  intro x hx
  exact hx.hasUpperContactOpeningAtMostOn

theorem upperContactOpeningAtMostSet_subset_domain {s : Set E} {u : E → ℝ} {A : ℝ} :
    upperContactOpeningAtMostSet s u A ⊆ s := by
  intro x hx
  exact hx.mem

theorem upperContactWithSlopeOpeningAtMostSet_subset_domain
    {s : Set E} {u : E → ℝ} {p : E} {A : ℝ} :
    upperContactWithSlopeOpeningAtMostSet s u p A ⊆ s := by
  intro x hx
  exact hx.mem

theorem upperContactOpeningAtMostSet_mono_bound
    {s : Set E} {u : E → ℝ} {A B : ℝ} (hAB : A ≤ B) :
    upperContactOpeningAtMostSet s u A ⊆ upperContactOpeningAtMostSet s u B := by
  intro x hx
  exact hx.mono_bound hAB

theorem upperContactWithSlopeOpeningAtMostSet_mono_bound
    {s : Set E} {u : E → ℝ} {p : E} {A B : ℝ} (hAB : A ≤ B) :
    upperContactWithSlopeOpeningAtMostSet s u p A ⊆
      upperContactWithSlopeOpeningAtMostSet s u p B := by
  intro x hx
  exact hx.mono_bound hAB

end AleksandrovDifferentiability
