/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Multiplication

/-!
# Conway's refinement conjecture for cut-defined omnific integers

An omnific integer is a surreal number satisfying Conway's cut equation
`x = {x - 1 | x + 1}`. Conway's refinement conjecture says that every equation
`a * b = c * d` among
omnific integers admits the four-factor decomposition displayed below. Zero inputs are allowed;
there are no support, reducedness, or cardinality hypotheses.
-/

public noncomputable section

universe u

namespace ConwayRefinement.Standalone.Oz


/-- Conway's definition: `x` is an omnific integer when it is the cut with sole left option
`x - 1` and sole right option `x + 1`. -/
abbrev IsConwayOmnificInteger (x : Surreal.{u}) : Prop :=
  x = !{{x - 1} | {x + 1}}' (by
    simp only [Set.mem_singleton_iff]
    rintro _ rfl _ rfl
    simp [sub_eq_add_neg])

/-- Conway's refinement conjecture: every equality `a * b = c * d` of
cut-defined omnific integers has an omnific refinement
`a = e * f`, `b = g * h`, `c = e * g`, `d = f * h`.
All four inputs may be zero. -/
abbrev ConwayConjecture : Prop :=
  ∀ a b c d : Surreal.{u},
    IsConwayOmnificInteger a → IsConwayOmnificInteger b →
    IsConwayOmnificInteger c → IsConwayOmnificInteger d → a * b = c * d →
    ∃ e f g h : Surreal.{u},
      IsConwayOmnificInteger e ∧ IsConwayOmnificInteger f ∧
      IsConwayOmnificInteger g ∧ IsConwayOmnificInteger h ∧
      a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h


end ConwayRefinement.Standalone.Oz

/-!
## Formal proof

Proof module: `ConwayRefinementProof`.

* `ConwayConjecture` → `ConwayConjecture.proof`
-/
