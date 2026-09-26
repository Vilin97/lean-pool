/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ModelCoord

/-!
# The split cap on merged vectors

The multiplicative midpoint of the cap recursion: the split cap
(smaller cap tensored with one evaluation) evaluated on a
transported merge of model vectors is the product of the smaller
cap value and the strand evaluation.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))

-- Multiplicativity is checked by unfolding the
-- transport, the merge and the tensor of the two functionals.
/-- **The split cap is multiplicative over the merge.** -/
theorem omegaFun_capTensor_merge (m : ℕ)
    (x : (superPow (stdSuperPair k ℓ) (m + m)).even)
    (y : (superPow (stdSuperPair k ℓ) 2).even) :
    omegaFun f P (HomSpace.tensor f (m + m) 0 2 0
        (bundleCapClass f m) (evClass f))
      (((stdToOmega f P e ((m + m) + 2)) :
        SuperVect.Hom _ _).evenMap
        (((powMerge (stdSuperPair k ℓ) (m + m) 2) :
          SuperVect.Hom _ _).evenMap (evenPair x y))) =
      capVal f P e m x *
        omegaFun f P (evClass f)
          (((stdToOmega f P e 2) :
            SuperVect.Hom _ _).evenMap y) := by
  let := P.braided
  -- The transported merge is the structure-map image of the
  -- blockwise transports.
  have hmerge := congrArg (fun z :
      (superPow (stdSuperPair k ℓ) (m + m) ⊗
        superPow (stdSuperPair k ℓ) 2 ⟶
        P.ω.obj (SkeinObj.mk ((m + m) + 2))) =>
    (z : SuperVect.Hom _ _).evenMap (evenPair x y))
    (stdToOmega_merge f P e (m + m) 2)
  refine Eq.trans (congrArg (omegaFun f P
    (HomSpace.tensor f (m + m) 0 2 0
      (bundleCapClass f m) (evClass f))) hmerge.symm) ?_
  change omegaFun f P (HomSpace.tensor f (m + m) 0 2 0
      (bundleCapClass f m) (evClass f))
    (((μ P.ω (SkeinObj.mk (m + m)) (SkeinObj.mk 2)) :
      SuperVect.Hom _ _).evenMap
      (((stdToOmega f P e (m + m) ⊗ₘ stdToOmega f P e 2) :
        SuperVect.Hom _ _).evenMap (evenPair x y))) = _
  -- Evaluate the tensor pair blockwise.
  rw [show ((stdToOmega f P e (m + m) ⊗ₘ stdToOmega f P e 2) :
      SuperVect.Hom _ _).evenMap (evenPair x y) =
    evenPair
      ((stdToOmega f P e (m + m) :
        SuperVect.Hom _ _).evenMap x)
      ((stdToOmega f P e 2 :
        SuperVect.Hom _ _).evenMap y) from
    tensorHom_evenPair _ _ x y]
  -- The tensor functional splits as the product.
  exact omegaFun_tensor f P (bundleCapClass f m) (evClass f)
    ((stdToOmega f P e (m + m) : SuperVect.Hom _ _).evenMap x)
    ((stdToOmega f P e 2 : SuperVect.Hom _ _).evenMap y)

end RS
