/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Encoding.Pairing
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Paired relation predicates

This file adds the complexity-class predicates built on the neutral binary
pairing codec from `Complexitylib.Encoding.Pairing`.
-/


@[expose] public section

namespace Complexity

/-- A binary relation is **polynomially balanced** if witness length is bounded
by a polynomial in the input length. This is the standard short-witness
condition used in the definitions of NP, FNP, FNL, and related classes. -/
def PolyBalanced (R : List Bool → List Bool → Prop) : Prop :=
  ∃ p : Polynomial ℕ, ∀ x y, R x y → y.length ≤ p.eval x.length

/-- The pair language of `R` contains exactly the encodings `pair x y` for
which `R x y` holds. -/
def pairLang (R : List Bool → List Bool → Prop) : Language :=
  {z | ∃ x y, z = pair x y ∧ R x y}

/-- Membership of a canonically encoded pair reduces to the underlying
binary relation. -/
@[simp] theorem mem_pairLang_pair (R : List Bool → List Bool → Prop)
    (x y : List Bool) :
    pair x y ∈ pairLang R ↔ R x y := by
  constructor
  · rintro ⟨x', y', hpair, hR⟩
    obtain ⟨hx, hy⟩ := pair_inj hpair
    simpa [hx, hy] using hR
  · intro hR
    exact ⟨x, y, rfl, hR⟩

end Complexity
