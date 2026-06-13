/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.Sensitivity.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic

/-!
# Multilinear Representation and Degree

Every Boolean function `f : (Fin n → Bool) → Bool` has a unique multilinear
polynomial representation over `ℤ`. This file defines the Möbius coefficients
of that representation and the multilinear degree of `f`.

## Main definitions

* `LeanPoolSensitivity.indicator` — the indicator assignment of a finite set
  of coordinates.
* `LeanPoolSensitivity.boolToInt` — the integer encoding of a Boolean value.
* `LeanPoolSensitivity.BoolFun.moebius` — the Möbius coefficient
  `c_S(f) = ∑_{T ⊆ S} (-1)^{|S|-|T|} f(1_T)`.
* `LeanPoolSensitivity.BoolFun.degree` — the multilinear degree of `f`.
-/

namespace LeanPoolSensitivity

variable {n : ℕ}

/-- The Boolean assignment that is `true` on coordinates in `S` and `false`
elsewhere. -/
def indicator (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

@[simp]
theorem indicator_mem {S : Finset (Fin n)} {i : Fin n} :
    indicator S i = true ↔ i ∈ S := by
  simp [indicator]

@[simp]
theorem indicator_not_mem {S : Finset (Fin n)} {i : Fin n} :
    indicator S i = false ↔ i ∉ S := by
  simp [indicator]

/-- Integer encoding of a Boolean value: `true ↦ 1` and `false ↦ 0`. -/
def boolToInt (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem boolToInt_true : boolToInt true = 1 := rfl
@[simp] theorem boolToInt_false : boolToInt false = 0 := rfl

namespace BoolFun

/-- The Möbius coefficient of `f` at `S`: the coefficient of the monomial
`∏_{i ∈ S} x_i` in the unique multilinear polynomial representing `f`,
computed by inclusion–exclusion as
`c_S(f) = ∑_{T ⊆ S} (-1)^{|S|-|T|} f(1_T)`. -/
def moebius (f : BoolFun n) (S : Finset (Fin n)) : ℤ :=
  ∑ T ∈ S.powerset,
    (-1) ^ (S.card - T.card) * boolToInt (f (indicator T))

/-- The multilinear degree of `f`: the maximum cardinality of `S` for which
the Möbius coefficient `c_S(f)` is nonzero. -/
noncomputable def degree (f : BoolFun n) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => f.moebius S ≠ 0)).sup
    Finset.card

/-- The multilinear degree of `f` is at most `n`. -/
theorem degree_le (f : BoolFun n) : f.degree ≤ n := by
  apply Finset.sup_le
  intro S hS
  simp only [Finset.mem_filter] at hS
  simpa using Finset.card_le_univ S

/-- If the multilinear degree is positive, there exists a "witness" set `S`
of cardinality equal to the degree at which the Möbius coefficient is
nonzero. -/
theorem exists_degree_witness (f : BoolFun n) (hd : 0 < f.degree) :
    ∃ S : Finset (Fin n), S.card = f.degree ∧ f.moebius S ≠ 0 := by
  unfold degree at hd ⊢
  set F := (Finset.univ : Finset (Finset (Fin n))).filter (fun S => f.moebius S ≠ 0)
  have hne : F.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [F, h] at hd
  obtain ⟨S, hS, heq⟩ := Finset.exists_mem_eq_sup F hne Finset.card
  exact ⟨S, heq.symm, (Finset.mem_filter.mp hS).2⟩

end BoolFun

end LeanPoolSensitivity
