/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaComplex

/-!
# The complex point of a simple algebra

The even part of the Γ-algebra of a simple countably presented
algebra is the complex numbers and its odd part vanishes, so the
Γ-algebra has a complex point on the nose: the inverse of the
structure map, with nothing to check on the odd side.

This is the last input of the fibre functor: with a point in hand
the base change of `RS/Classical/Deligne/PointFibre.lean` lands in
finite-dimensional super vector spaces.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-- **The structure map of the scalars is bijective** for a simple
countably presented algebra: injective because the scalars form a
field, surjective because every scalar is a complex multiple of the
unit. -/
theorem bijective_algebraMap_gammaEven
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] [CategoryTheory.Linear ℂ C]
    [MonoidalLinear ℂ C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)]
    (hu : HasScalarUnit C)
    (hsmul : IndOfLinear C) (hlen : ∀ Z : C, ∃ N : ℕ, LengthLE Z N)
    (L : OddLine (Ind C)) {𝔸 𝔹 : Ind C} [MonObj 𝔸] [MonObj 𝔹]
    [IsCommMonObj 𝔹] (π : 𝔸 ⟶ 𝔹) [Epi π]
    (hcp : CountablyPresented 𝔸) (hne : η[𝔹] ≠ 0)
    (hsimple : ∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤) :
    letI : Field ((gammaAlgebra (Ind C) L 𝔹).even) :=
      gammaEvenField 𝔹 L hsimple hne
    Function.Bijective
      (algebraMap ℂ ((gammaAlgebra (Ind C) L 𝔹).even)) := by
  let : Field ((gammaAlgebra (Ind C) L 𝔹).even) :=
    gammaEvenField 𝔹 L hsimple hne
  refine ⟨(algebraMap ℂ _).injective, fun g => ?_⟩
  obtain ⟨c, hc⟩ :=
    exists_smul_one_of_simple_of_epi hu hsmul hlen L π hcp hne hsimple g
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc.symm⟩

/-- **A simple countably presented algebra has a complex point.**
The even part is the complex numbers and the odd part vanishes, so
the point is the inverse of the structure map and the vanishing
condition is vacuous. -/
noncomputable def superPointOfSimple
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] [CategoryTheory.Linear ℂ C]
    [MonoidalLinear ℂ C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)]
    (hu : HasScalarUnit C)
    (hsmul : IndOfLinear C) (hlen : ∀ Z : C, ∃ N : ℕ, LengthLE Z N)
    (L : OddLine (Ind C)) {𝔸 𝔹 : Ind C} [MonObj 𝔸] [MonObj 𝔹]
    [IsCommMonObj 𝔹] (π : 𝔸 ⟶ 𝔹) [Epi π]
    (hcp : CountablyPresented 𝔸) (hne : η[𝔹] ≠ 0)
    (hsimple : ∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤) :
    SuperPoint (gammaAlgebra (Ind C) L 𝔹) where
  chi :=
    letI : Field ((gammaAlgebra (Ind C) L 𝔹).even) :=
      gammaEvenField 𝔹 L hsimple hne
    (AlgEquiv.ofBijective (Algebra.ofId ℂ _)
      (bijective_algebraMap_gammaEven hu hsmul hlen L π hcp hne
        hsimple)).symm.toAlgHom
  vanishing u v := by
    have hu0 : u = 0 := hom_oddLine_eq_zero_of_simple 𝔹 L hsimple u
    rw [hu0, map_zero]
    simp

end RS
