/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapFun

/-!
# The evaluation functional in standard coordinates

Under a standard-model identification, the one-strand evaluation
functional composed with the structure map is the standard form:
the pointwise consequence of the model transport equation.
-/

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}

/-- **The evaluation is the standard form** on transported even
pairs. -/
theorem evForm
    (e : SuperVect.Hom (stdSuperPair k ℓ) (P.ω.obj (SkeinObj.mk 1)))
    (hform :
      letI := P.braided
      SuperVect.Hom.comp
        (μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
          P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫ η P.ω)
        (SuperVect.tensorHom e e) = stdForm k ℓ)
    (x y : (stdSuperPair k ℓ).even) :
    letI := P.braided
    omegaFun f P (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1))
        (((μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1)) :
          SuperVect.Hom _ _).evenMap
          (evenPair (e.evenMap x) (e.evenMap y))) =
      (stdForm k ℓ).evenMap (evenPair x y) := by
  letI := P.braided
  have h := congrArg (fun z : SuperVect.Hom
      (SuperVect.tensorObj (stdSuperPair k ℓ) (stdSuperPair k ℓ))
      SuperVect.tensorUnit => z.evenMap (evenPair x y)) hform
  refine Eq.trans ?_ h
  show omegaFun f P (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1))
      (((μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1)) :
        SuperVect.Hom _ _).evenMap
        (evenPair (e.evenMap x) (e.evenMap y))) =
    ((μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
        P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫ η P.ω :
      SuperVect.tensorObj (P.ω.obj (SkeinObj.mk 1))
        (P.ω.obj (SkeinObj.mk 1)) ⟶ SuperVect.tensorUnit) :
      SuperVect.Hom _ _).evenMap
      ((SuperVect.tensorHom e e).evenMap (evenPair x y))
  rw [show (SuperVect.tensorHom e e).evenMap (evenPair x y) =
      evenPair (e.evenMap x) (e.evenMap y) from
    tensorHom_evenPair e e x y]
  rfl

end RS
