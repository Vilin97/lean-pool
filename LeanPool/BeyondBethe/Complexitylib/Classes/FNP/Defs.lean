/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.Pairing
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Defs

/-!
# FNP and TFNP — Definitions

Core definitions for the function/search complexity classes **FNP** and **TFNP**,
and the `OrRelation` combinator used to construct TFNP problems from
NP ∩ coNP witness pairs.
-/


@[expose] public section

namespace Complexity

/-- **FNP** is the class of search problems defined by NP relations: binary
    relations that are polynomially balanced and decidable in polynomial time.
    A relation `R` is in FNP if witnesses have poly-bounded length and the
    pair language `{pair(x, y) | R x y}` is in P. -/
def FNP : Set (List Bool → List Bool → Prop) :=
  {R | PolyBalanced R ∧ pairLang R ∈ P}

/-- **TFNP** is the class of total FNP search problems: every instance has at
    least one witness. -/
def TFNP : Set (List Bool → List Bool → Prop) :=
  {R ∈ FNP | ∀ x, ∃ y, R x y}

/-- Combine two witness relations by disjunction. Used to construct TFNP
    problems from NP ∩ coNP witness pairs: the combined relation accepts any
    witness valid for either component. -/
def OrRelation (R₁ R₂ : List Bool → List Bool → Prop) :
    List Bool → List Bool → Prop :=
  fun x y => R₁ x y ∨ R₂ x y

end Complexity
