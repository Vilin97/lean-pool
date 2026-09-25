/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SimpleGenerator
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SimplePoint
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SplitClosure
import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndOfLinear
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SimpleSplit
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SmallReduction

/-!
# One simple algebra splits the whole category

Splitting the single object `X ⊞ Xᘁ` and passing to a simple
quotient gives an algebra that splits the tensor generator and its
dual, a direct summand being a subquotient.  The split objects are
closed under sums and tensor products, so they contain every mixed
power, and over a simple algebra they are closed under subquotients
as well (`RS.exists_mix_of_isSubquotient`), so finite tensor
generation carries them to every object.  The scalars of that
algebra are the complex numbers, so its Γ-algebra has a complex
point.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-- **One simple algebra splits everything, and its Γ-algebra has a
complex point.** -/
theorem exists_splitting_simple_algebra
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] [HasFiniteBiproducts C]
    (ψ : ℂ ≃+* End (𝟙_ C))
    (P : SchurPackage.{v}) (P₀ : SchurPackage.{0})
    (L : OddLine (Ind C)) (X : C)
    (hgen : TensorGeneratedBy C X)
    (hgrow : letI := linearOfScalarUnit ψ; ModerateLengthGrowth C)
    (hlen : ∀ Z : C, ∃ N : ℕ, LengthLE Z N)
    :
    letI := linearOfScalarUnit ψ
    letI := monoidalLinearOfScalarUnitBraided ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    letI := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
    ∃ (𝔹 : Ind C) (_ : MonObj 𝔹) (_ : IsCommMonObj 𝔹),
      η[𝔹] ≠ 0 ∧
      (∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤) ∧
      SplitsOn L 𝔹 (indOf : C ⥤ Ind C) ∧
      Nonempty (SuperPoint (gammaAlgebra (Ind C) L 𝔹)) := by
  let := linearOfScalarUnit ψ
  let := monoidalLinearOfScalarUnitBraided ψ
  let := linearOfScalarUnit (indScalarUnit ψ)
  let := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
  have hu : HasScalarUnit C := hasScalarUnit_of_scalarUnit ψ
  obtain ⟨lam, hkill⟩ :=
    forall_exists_schurKilled P hu hgrow (X ⊞ (Xᘁ))
  obtain ⟨p, q, 𝔸, 𝔹, hmonA, hcommA, hmon, hcomm, π, hne, hcp, hepi,
      hhom, hsimple, ⟨e⟩⟩ :=
    exists_simple_generator_algebra ψ P P₀ L (X ⊞ (Xᘁ)) lam hkill hlen
  let := hmonA
  let := hcommA
  let := hmon
  let := hcomm
  have := hepi
  have hbig : IsSplit L 𝔹 ((indOf : C ⥤ Ind C).obj (X ⊞ (Xᘁ))) :=
    ⟨p, q, ⟨e⟩⟩
  have hsubB : ∀ Y Z : C, IsSubquotientOf Y Z →
      IsSplit L 𝔹 ((indOf : C ⥤ Ind C).obj Z) →
      IsSplit L 𝔹 ((indOf : C ⥤ Ind C).obj Y) := by
    intro Y Z hsq hZ
    obtain ⟨a, b, ⟨eZ⟩⟩ := hZ
    have : (indOf (C := C)).Additive := indOf_additive
    exact exists_mix_of_isSubquotient 𝔹 L hsimple hne
      (isSubquotientOf_map (indOf : C ⥤ Ind C) hsq) eZ
  have hX : IsSplit L 𝔹 ((indOf : C ⥤ Ind C).obj X) :=
    hsubB X (X ⊞ (Xᘁ))
      (isSubquotientOf_of_retract biprod.inl biprod.fst
        (by simp)) hbig
  have hXd : IsSplit L 𝔹 ((indOf : C ⥤ Ind C).obj (Xᘁ)) :=
    hsubB (Xᘁ) (X ⊞ (Xᘁ))
      (isSubquotientOf_of_retract biprod.inr biprod.snd
        (by simp)) hbig
  refine ⟨𝔹, hmon, hcomm, hne, hsimple,
    splitsOn_of_generator L 𝔹 X hX hXd hsubB hgen,
    ⟨superPointOfSimple hu ?_ hlen L π hcp hne hsimple⟩⟩
  exact indOfLinear_of_scalarUnit ψ

end RS
