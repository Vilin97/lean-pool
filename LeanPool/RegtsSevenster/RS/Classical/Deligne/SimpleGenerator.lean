/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GeneratorAlgebra
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SimpleQuotient

/-!
# A simple algebra splitting the tensor generator

Composing the two halves: the splitting algebra of a single object
is countably presented, and every nonzero algebra object has a
simple quotient.  Base change carries the splitting down, so a
single simple algebra splits the chosen object.

Over a simple algebra the regular module is a simple object of the
module category, and so is its twist by the odd line, so a free
mixed module is semisimple of finite length.  That is what will
carry the splitting from the tensor generator to every subquotient,
and with it to the whole category.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-- **A simple algebra splitting a chosen object**, obtained from a
countably presented splitting algebra by passing to the quotient by
a maximal ideal.  The countably presented algebra above is kept,
together with the projection, because the dimension count for the
scalars of the quotient runs through it. -/
theorem exists_simple_generator_algebra
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C))
    (P : SchurPackage.{v}) (P₀ : SchurPackage.{0})
    (L : OddLine (Ind C)) (X₀ : C) (lam : YoungDiagram)
    (hkill : letI := linearOfScalarUnit ψ; SchurKilled P X₀ lam)
    (hlen : ∀ Z : C, ∃ N : ℕ, LengthLE Z N) :
    letI := linearOfScalarUnit ψ
    letI := monoidalLinearOfScalarUnitBraided ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    letI := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
    ∃ (p q : ℕ) (𝔸 𝔹 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸)
      (_ : MonObj 𝔹) (_ : IsCommMonObj 𝔹) (π : 𝔸 ⟶ 𝔹),
      η[𝔹] ≠ 0 ∧ CountablyPresented 𝔸 ∧ Epi π ∧ IsMonHom π ∧
      (∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤) ∧
      Nonempty (freeMod 𝔹 ((indOf : C ⥤ Ind C).obj X₀) ≅
        freeMod 𝔹 (L.mix p q)) := by
  let := linearOfScalarUnit ψ
  let := monoidalLinearOfScalarUnitBraided ψ
  let := linearOfScalarUnit (indScalarUnit ψ)
  let := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
  obtain ⟨p, q, 𝔸, hmon, hcomm, hne, hcp, ⟨e⟩⟩ :=
    exists_generator_algebra ψ P P₀ L X₀ lam hkill hlen
  let := hmon
  let := hcomm
  obtain ⟨𝔹, hmon', hcomm', π, hne', hepi, hhom, hsimple⟩ :=
    exists_simple_quotient 𝔸 hne
  let := hmon'
  let := hcomm'
  have := hhom
  exact ⟨p, q, 𝔸, 𝔹, hmon, hcomm, hmon', hcomm', π, hne', hcp, hepi,
    hhom, hsimple, ⟨freeModIsoBaseChange 𝔸 𝔹 π e⟩⟩

end RS
