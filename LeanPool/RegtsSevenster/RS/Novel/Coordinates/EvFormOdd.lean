/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BasisSplit
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OddPair

/-!
# The evaluation functional on odd pairs

The odd counterpart of the standard-form identification: on
transported odd pairs the one-strand evaluation through the
structure map is the standard form's odd block — the symplectic
entries.
-/

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped TensorProduct

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}

/-- **The evaluation is the standard form on transported odd
pairs.** -/
theorem evFormOdd
    (e : SuperVect.Hom (stdSuperPair k ℓ) (P.ω.obj (SkeinObj.mk 1)))
    (hform :
      letI := P.braided
      SuperVect.Hom.comp
        (μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
          P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫ η P.ω)
        (SuperVect.tensorHom e e) = stdForm k ℓ)
    (x y : (stdSuperPair k ℓ).odd) :
    letI := P.braided
    omegaFun f P (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1))
        (((μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1)) :
          SuperVect.Hom _ _).evenMap
          (oddPair (e.oddMap x) (e.oddMap y))) =
      (stdForm k ℓ).evenMap (oddPair x y) := by
  letI := P.braided
  have h := congrArg (fun z : SuperVect.Hom
      (SuperVect.tensorObj (stdSuperPair k ℓ) (stdSuperPair k ℓ))
      SuperVect.tensorUnit => z.evenMap (oddPair x y)) hform
  refine Eq.trans ?_ h
  show omegaFun f P (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1))
      (((μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1)) :
        SuperVect.Hom _ _).evenMap
        (oddPair (e.oddMap x) (e.oddMap y))) =
    ((μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
        P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫ η P.ω :
      SuperVect.tensorObj (P.ω.obj (SkeinObj.mk 1))
        (P.ω.obj (SkeinObj.mk 1)) ⟶ SuperVect.tensorUnit) :
      SuperVect.Hom _ _).evenMap
      ((SuperVect.tensorHom e e).evenMap (oddPair x y))
  rw [show (SuperVect.tensorHom e e).evenMap (oddPair x y) =
      oddPair (e.oddMap x) (e.oddMap y) from
    tensorHom_oddPair e e x y]
  rfl

end RS
