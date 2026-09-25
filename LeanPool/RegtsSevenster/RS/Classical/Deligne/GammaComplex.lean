/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SimpleScalars
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PresentedQuotient

/-!
# The scalars of a simple countably presented algebra are complex

The even part of the Γ-algebra of a simple algebra is a field, and a
quotient of a countably presented ind-object is countably presented,
so that field has countable dimension over the complex numbers.  A
field extension of the complex numbers of countable dimension is the
complex numbers, so every scalar is a complex multiple of the unit.

Together with the vanishing of the odd part this is exactly the pair
of hypotheses that `RS/Classical/Deligne/FreeSummand.lean` consumes:
the free-module functor is then full and faithful on the mixed
objects, and idempotents split with free image.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-- **The scalars of a simple countably presented algebra are the
complex numbers.**  The algebra is presented as a quotient of a
countably presented one, which is how the countable descent delivers
it. -/
theorem exists_smul_one_of_simple_of_epi
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] [CategoryTheory.Linear ℂ C]
    [MonoidalLinear ℂ C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)]
    (hu : HasScalarUnit C)
    (hsmul : IndOfLinear C) (hlen : ∀ Z : C, ∃ N : ℕ, LengthLE Z N)
    (L : OddLine (Ind C)) {𝔸 𝔹 : Ind C} [MonObj 𝔹]
    [IsCommMonObj 𝔹] (π : 𝔸 ⟶ 𝔹) [Epi π]
    (hcp : CountablyPresented 𝔸) (hne : η[𝔹] ≠ 0)
    (hsimple : ∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤)
    (g : 𝟙_ (Ind C) ⟶ 𝔹) : ∃ c : ℂ, g = c • η[𝔹] := by
  let : Field ((gammaAlgebra (Ind C) L 𝔹).even) :=
    gammaEvenField 𝔹 L hsimple hne
  have hrank :
      Module.rank ℂ ((gammaAlgebra (Ind C) L 𝔹).even) ≤ Cardinal.aleph0 :=
    rank_hom_unit_le_aleph0_of_epi hu hsmul hlen π hcp
  obtain ⟨c, hc⟩ :=
    exists_smul_one_of_countable_dimension
      ((gammaAlgebra (Ind C) L 𝔹).even) hrank g
  exact ⟨c, hc⟩

end RS
