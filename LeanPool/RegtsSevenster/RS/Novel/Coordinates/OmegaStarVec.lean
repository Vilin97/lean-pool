/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OmegaTensor

/-!
# The assembled star vector

The image vector of the star-tensor class, assembled recursively
through the structure maps: each vertex contributes its star
vector, tensored on through `μ` and recast along the sum.  The
parameter value of a closed fragment is then the circle power
times the cap functional evaluated on the sorted assembled
vector — arc (b) of the extraction, complete.
-/

namespace RS

open CategoryTheory Functor.LaxMonoidal Functor.OplaxMonoidal
open MonoidalCategory

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))

/-- The assembled star vector of a degree list. -/
noncomputable def omegaStarVec :
    (ds : List ℕ) → (P.ω.obj (SkeinObj.mk ds.sum)).even
  | [] => omegaVec f P (𝟙 (SkeinObj.mk 0))
  | d :: ds =>
      letI := P.braided
      (P.ω.map (bundleMapClass f (finCongr
        (List.sum_cons.symm :
          d + ds.sum = (d :: ds).sum)))).evenMap
        (((μ P.ω (SkeinObj.mk d) (SkeinObj.mk ds.sum)) :
          SuperVect.Hom _ _).evenMap
          (evenPair (starVec f P d) (omegaStarVec ds)))

/-- **The star-tensor class assembles**: its image vector is the
recursively assembled star vector. -/
theorem omegaVec_starTensorClass : ∀ (ds : List ℕ),
    omegaVec f P (starTensorClass f ds) = omegaStarVec f P ds
  | [] => by
    rw [starTensorClass_nil, empty_class_eq_id]
    rfl
  | d :: ds => by
    letI := P.braided
    refine (congrArg (omegaVec f P)
      (starTensorClass_cons f d ds)).trans ?_
    refine (omegaVec_comp f P
      (HomSpace.tensor f 0 d 0 ds.sum
        (vertexStarClass f d) (starTensorClass f ds))
      (bundleMapClass f (finCongr
        (List.sum_cons.symm :
          d + ds.sum = (d :: ds).sum)))).trans ?_
    refine (congrArg (P.ω.map (bundleMapClass f (finCongr
      (List.sum_cons.symm :
        d + ds.sum = (d :: ds).sum)))).evenMap
      ((omegaVec_tensor f P (vertexStarClass f d)
        (starTensorClass f ds)).trans
        (congrArg (fun z =>
          ((μ P.ω (SkeinObj.mk d) (SkeinObj.mk ds.sum)) :
            SuperVect.Hom _ _).evenMap
            (evenPair (starVec f P d) z))
          (omegaVec_starTensorClass ds)))).trans ?_
    rfl

/-- **The parameter value, factored** (arc (b) complete): the
value of a closed fragment is the circle power times the cap
functional on the sorted assembled star vector. -/
theorem parameter_star_factor (W : ClosedFragment) :
    f.val W = circleVal f ^ W.circles *
      omegaFun f P (bundleCapClass f (edgeCount W))
        ((P.ω.map (bundleMapClass f
          (sortEquiv (starAssignEnum W)).symm)).evenMap
          (omegaStarVec f P (degList (starAssignEnum W)))) := by
  rw [← star_pairing f P W]
  rw [starClass_factor' f W]
  rw [show omegaVec f P (circleVal f ^ W.circles •
      HomSpace.comp f 0 ((degList (starAssignEnum W)).sum)
        (edgeCount W + edgeCount W)
        (starTensorClass f (degList (starAssignEnum W)))
        (bundleMapClass f
          (sortEquiv (starAssignEnum W)).symm)) =
    circleVal f ^ W.circles • omegaVec f P
      (HomSpace.comp f 0 ((degList (starAssignEnum W)).sum)
        (edgeCount W + edgeCount W)
        (starTensorClass f (degList (starAssignEnum W)))
        (bundleMapClass f
          (sortEquiv (starAssignEnum W)).symm)) from
    omegaVec_smul f P _ _]
  rw [show omegaVec f P
      (HomSpace.comp f 0 ((degList (starAssignEnum W)).sum)
        (edgeCount W + edgeCount W)
        (starTensorClass f (degList (starAssignEnum W)))
        (bundleMapClass f
          (sortEquiv (starAssignEnum W)).symm)) =
    (P.ω.map (bundleMapClass f
      (sortEquiv (starAssignEnum W)).symm)).evenMap
      (omegaVec f P
        (starTensorClass f (degList (starAssignEnum W)))) from
    omegaVec_comp f P _ _]
  rw [omegaVec_starTensorClass]
  rw [map_smul]
  rw [smul_eq_mul]

end RS
