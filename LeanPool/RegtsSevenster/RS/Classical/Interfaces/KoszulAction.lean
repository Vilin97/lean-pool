/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Interfaces.OmegaTensorPower

/-!
# The even-component restriction of the super permutation action

The even and odd components of a `SuperVect` endomorphism, and the
even-component representation of `SymGroupAlgebra n` they give:
`superPermAction` followed by the even-component extraction, which
is linear, so the composite is again linear.

Extraction is a linear map, so it carries zero to zero: whatever
the super permutation action kills, the even-component
representation kills too.  That containment is what the sector
trace needs.
-/

noncomputable section

namespace RS

open CategoryTheory MonoidalCategory Category
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)
  (P : DelignePackage (SkeinObj f))

/-! ### Even and odd components -/

/-- The even component of a SuperVect endomorphism, viewed as a
module endomorphism. -/
def evenComponent (W : SuperVect) (g : End W) :
    Module.End ℂ W.even :=
  (g : SuperVect.Hom W W).evenMap

/-- The odd component of a SuperVect endomorphism. -/
def oddComponent (W : SuperVect) (g : End W) :
    Module.End ℂ W.odd :=
  (g : SuperVect.Hom W W).oddMap

/-- The even component of zero is zero. -/
@[simp]
theorem evenComponent_zero (W : SuperVect) :
    evenComponent W 0 = 0 := rfl

/-- The odd component of zero is zero. -/
@[simp]
theorem oddComponent_zero (W : SuperVect) :
    oddComponent W 0 = 0 := rfl

/-- Even extraction is additive. -/
theorem evenComponent_add (W : SuperVect)
    (g₁ g₂ : End W) :
    evenComponent W (g₁ + g₂) =
      evenComponent W g₁ + evenComponent W g₂ := rfl

/-- Even extraction commutes with scaling. -/
theorem evenComponent_smul (W : SuperVect)
    (r : ℂ) (g : End W) :
    evenComponent W (r • g) = r • evenComponent W g := rfl

/-- The even-component extraction is a linear map from the
endomorphism algebra to the module endomorphism ring. -/
def evenComponentLinear (W : SuperVect) :
    End W →ₗ[ℂ] Module.End ℂ W.even where
  toFun := evenComponent W
  map_add' := evenComponent_add W
  map_smul' := evenComponent_smul W

/-! ### The even-component representation -/

/-- The even-component representation of `SymGroupAlgebra n`
on `(superPow V n).even`: the composite of `superPermAction`
with the even-component linear extraction. -/
noncomputable def evenPermRep (n : ℕ) :
    SymGroupAlgebra n →ₗ[ℂ]
      Module.End ℂ (superPow (strandImage f P) n).even := by
  letI := P.additive
  letI := P.linear
  exact (evenComponentLinear
    (superPow (strandImage f P) n)).comp
    (superPermAction f P n).toLinearMap

/-- **Even-restriction zero implication**: if the super-permutation
action kills an element, so does the even-component representation.
This is immediate because the even component of a zero SuperVect
morphism is zero. -/
theorem superPermAction_zero_imp_evenPermRep_zero (n : ℕ)
    (x : SymGroupAlgebra n) :
    letI := P.additive
    letI := P.linear
    superPermAction f P n x = 0 →
      evenPermRep f P n x = 0 := by
  let := P.additive
  let := P.linear
  intro h
  change (evenComponentLinear _).comp
    (superPermAction f P n).toLinearMap x = 0
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, h,
    map_zero]

end RS

end
