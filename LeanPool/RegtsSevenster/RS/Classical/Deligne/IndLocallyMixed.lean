/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop29Close
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndSchurKilled

/-!
# Embedded objects are locally mixed

Proposition 2.9 applies to the embedded objects: an object of the
small category killed by some Schur functor stays killed after the
Ind-embedding, its dual embeds to a dual, and the trichotomy then
makes it a mixed sum of the unit and the odd line after base change
to some nonzero commutative algebra.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-- **Embedded Schur-killed objects are locally mixed.** -/
theorem locallyMixed_indOf
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C))
    (P : SchurPackage.{v}) (P₀ : SchurPackage.{0}) (Z : C)
    (lam : YoungDiagram)
    (hkill : letI := linearOfScalarUnit ψ; SchurKilled P Z lam) :
    letI := linearOfScalarUnit ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    letI := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
    ∀ (L : OddLine (Ind C)), ¬ IsZero (𝟙_ (Ind C)) →
      L.LocallyMixed ((indOf : C ⥤ Ind C).obj Z) := by
  let := linearOfScalarUnit ψ
  let := linearOfScalarUnit (indScalarUnit ψ)
  let := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
  intro L h1
  refine prop29 P P₀ L ((indOf : C ⥤ Ind C).obj Z)
    ((indOf : C ⥤ Ind C).obj (Zᘁ)) h1 ⟨lam, ?_⟩
  exact (schurKilled_indOf ψ P Z lam).mpr hkill

end RS
