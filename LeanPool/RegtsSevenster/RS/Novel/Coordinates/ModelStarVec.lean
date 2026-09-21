/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.PowMerge

/-!
# The assembled star vector in the model

The star vectors pull back along the model transport and
assemble by the block merge entirely inside the monoidal powers
of the standard space; transporting forward recovers the
fibre-side assembled vector.  This is the form on which the
colouring coordinates evaluate.
-/

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

/-- The assembled star vector, in the model. -/
noncomputable def modelStarVec :
    (ds : List ℕ) → (superPow (stdSuperPair k ℓ) ds.sum).even
  | [] => (1 : ℂ)
  | d :: ds =>
      ((eqToHom (congrArg (superPow (stdSuperPair k ℓ))
        (List.sum_cons.symm : d + ds.sum = (d :: ds).sum)) :
        superPow (stdSuperPair k ℓ) (d + ds.sum) ⟶
          superPow (stdSuperPair k ℓ) ((d :: ds).sum)) :
        SuperVect.Hom _ _).evenMap
      (((powMerge (stdSuperPair k ℓ) d ds.sum) :
        SuperVect.Hom _ _).evenMap
        (evenPair
          (((stdFromOmega f P e' d) :
            SuperVect.Hom _ _).evenMap (starVec f P d))
          (modelStarVec ds)))

-- Raised budget: the transport is compared with the assembled star
-- vector by recursion on the degree list, carrying the tensorator
-- at every step.
/-- **The model star vector transports to the assembled star
vector.** -/
theorem stdToOmega_modelStarVec
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _) :
    ∀ ds : List ℕ,
      ((stdToOmega f P e ds.sum) :
        SuperVect.Hom _ _).evenMap
          (modelStarVec f P e' ds) =
        omegaStarVec f P ds
  | [] => by
    letI := P.braided
    exact congrArg (fun z : (SuperVect.tensorUnit ⟶
        P.ω.obj (SkeinObj.mk 0)) =>
      (z : SuperVect.Hom _ _).evenMap (1 : ℂ))
      (((Category.comp_id (ε P.ω)).symm).trans
        (congrArg (fun w => ε P.ω ≫ w)
          (P.ω.map_id (SkeinObj.mk 0)).symm))
  | d :: ds => by
    letI := P.braided
    -- The cast migrates across the transport.
    have hcast := stdToOmega_bmc_cast f P e
      (List.sum_cons.symm : d + ds.sum = (d :: ds).sum)
    have hcast' := congrArg (fun z :
        (superPow (stdSuperPair k ℓ) (d + ds.sum) ⟶
          P.ω.obj (SkeinObj.mk ((d :: ds).sum))) =>
      (z : SuperVect.Hom _ _).evenMap
        (((powMerge (stdSuperPair k ℓ) d ds.sum) :
          SuperVect.Hom _ _).evenMap
          (evenPair
            (((stdFromOmega f P e' d) :
              SuperVect.Hom _ _).evenMap (starVec f P d))
            (modelStarVec f P e' ds)))) hcast
    refine Eq.trans (Eq.trans ?_ hcast'.symm) ?_
    · rfl
    · -- Now push the merge through the block transport.
      have hmerge := stdToOmega_merge f P e d ds.sum
      have hmerge' := congrArg (fun z :
          (superPow (stdSuperPair k ℓ) d ⊗
            superPow (stdSuperPair k ℓ) ds.sum ⟶
            P.ω.obj (SkeinObj.mk (d + ds.sum))) =>
        (P.ω.map (bundleMapClass f (finCongr
          (List.sum_cons.symm :
            d + ds.sum = (d :: ds).sum)))).evenMap
          ((z : SuperVect.Hom _ _).evenMap
            (evenPair
              (((stdFromOmega f P e' d) :
                SuperVect.Hom _ _).evenMap (starVec f P d))
              (modelStarVec f P e' ds)))) hmerge
      refine Eq.trans (Eq.trans ?_ hmerge'.symm) ?_
      · rfl
      · -- Evaluate the tensor on the even pair, cancel the
        -- strand inverse, and use the induction.
        show (P.ω.map (bundleMapClass f (finCongr
            (List.sum_cons.symm :
              d + ds.sum = (d :: ds).sum)))).evenMap
          (((μ P.ω (SkeinObj.mk d) (SkeinObj.mk ds.sum)) :
            SuperVect.Hom _ _).evenMap
            (((stdToOmega f P e d ⊗ₘ
              stdToOmega f P e ds.sum) :
              SuperVect.Hom _ _).evenMap
              (evenPair
                (((stdFromOmega f P e' d) :
                  SuperVect.Hom _ _).evenMap (starVec f P d))
                (modelStarVec f P e' ds)))) = _
        rw [show ((stdToOmega f P e d ⊗ₘ
            stdToOmega f P e ds.sum) :
            SuperVect.Hom _ _).evenMap
            (evenPair
              (((stdFromOmega f P e' d) :
                SuperVect.Hom _ _).evenMap (starVec f P d))
              (modelStarVec f P e' ds)) =
          evenPair
            ((stdToOmega f P e d : SuperVect.Hom _ _).evenMap
              (((stdFromOmega f P e' d) :
                SuperVect.Hom _ _).evenMap (starVec f P d)))
            ((stdToOmega f P e ds.sum :
              SuperVect.Hom _ _).evenMap
              (modelStarVec f P e' ds)) from
          tensorHom_evenPair _ _ _ _]
        rw [show (stdToOmega f P e d :
            SuperVect.Hom _ _).evenMap
            (((stdFromOmega f P e' d) :
              SuperVect.Hom _ _).evenMap (starVec f P d)) =
          starVec f P d from
          congrArg (fun z : (P.ω.obj (SkeinObj.mk d) ⟶
              P.ω.obj (SkeinObj.mk d)) =>
            (z : SuperVect.Hom _ _).evenMap (starVec f P d))
            (stdFromOmega_stdToOmega f P e e' hee' d)]
        rw [stdToOmega_modelStarVec hee' ds]
        rfl

end RS
