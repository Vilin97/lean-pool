/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop21Core
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreOverSplitting
import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndSimple

/-!
# Deligne's Proposition 2.1, over a category with an odd line

If every object of a small abelian rigid symmetric monoidal
ℂ-linear category with scalar unit endomorphisms is killed by some
Schur functor, and its Ind-completion carries an odd line, then
there is a nonzero commutative algebra in the Ind-completion whose
fibre functor is strong monoidal, exact and faithful.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-- **Deligne's Proposition 2.1** for a category whose
Ind-completion carries an odd line. -/
theorem exists_fibre_functor
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C))
    (P : SchurPackage.{v}) (P₀ : SchurPackage.{0})
    (L : OddLine (Ind C))
    (hkill : letI := linearOfScalarUnit ψ
      ∀ Z : C, ∃ lam : YoungDiagram, SchurKilled P Z lam) :
    letI := linearOfScalarUnit ψ
    letI := monoidalLinearOfScalarUnitBraided ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    letI := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
    ∃ (𝔸 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      MonObj.one (X := 𝔸) ≠ 0 ∧
      Nonempty (((indOf : C ⥤ Ind C) ⋙ fibreOver L 𝔸).Monoidal) ∧
      Nonempty (Limits.PreservesFiniteLimits
        ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸)) ∧
      Nonempty (Limits.PreservesFiniteColimits
        ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸)) ∧
      ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸).Faithful := by
  let := linearOfScalarUnit ψ
  let := monoidalLinearOfScalarUnitBraided ψ
  let := linearOfScalarUnit (indScalarUnit ψ)
  let := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
  obtain ⟨𝔸, hmon, hcomm, hne, hsp, hsec⟩ :=
    exists_fibre_algebra ψ P P₀ L hkill
  let := hmon
  let := hcomm
  have hmono : Mono η[𝔸] :=
    mono_unit_ind (simple_unit_of_hasScalarUnit
      (hasScalarUnit_of_scalarUnit ψ)) 𝔸 hne
  have hpm : ∀ Z : Ind C, (tensorRight Z).PreservesMonomorphisms :=
    fun Z => inferInstance
  exact ⟨𝔸, hmon, hcomm, hne, ⟨indFibreMonoidal L 𝔸 hsp⟩,
    ⟨indFibre_preservesFiniteLimits L 𝔸 hsec⟩,
    ⟨indFibre_preservesFiniteColimits L 𝔸 hsec⟩,
    indFibre_faithful L 𝔸 hmono hsp⟩

end RS
