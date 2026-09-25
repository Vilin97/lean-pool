/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapClosed

/-!
# The master colour sum

The parameter value as a pure colour-combinatorial sum: the cap
expansion through the closed form, the permutation and cast
transports, and the star-vector coordinates.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

-- Raised budget: the parameter is rewritten as a colour sum, which
-- unfolds the star vector, the transport and the diagonal cap
-- pairing in a single term.
/-- **The master colour sum**: the parameter value is the
circle factor times the colour sum of the transported star
coordinates against the diagonal cap pairing. -/
theorem parameter_colour_sum (W : ClosedFragment)
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _)
    (hform :
      letI := P.braided
      SuperVect.Hom.comp
        (μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
          P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫ η P.ω)
        (SuperVect.tensorHom e e) = stdForm k ℓ) :
    f.val W = circleVal f ^ W.circles *
      ∑ c : {c : MixedColouring k ℓ
          (edgeCount W + edgeCount W) // c.IsEven},
        ((-1 : ℂ) ^ oddInversions (sortSplitPerm W)
            (c.val ∘ finCongr
              (degList_sum (starAssignEnum W))) *
          ∏ v, starCoord f P e'
            ((degList (starAssignEnum W)).get v)
            (blockRestrict (degList (starAssignEnum W))
              ((c.val ∘ finCongr
                (degList_sum (starAssignEnum W))) ∘
                sortSplitPerm W) v)) *
        betaDiag (edgeCount W) c.val := by
  rw [parameter_capVal f P e e' W hee']
  congr 1
  refine Eq.trans (capVal_expansion f P e (edgeCount W) _) ?_
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [capVal_closed f P e hform (edgeCount W) c.val c.prop]
  congr 1
  refine Eq.trans (coordOf_cast
    (degList_sum (starAssignEnum W)) _ _) ?_
  refine Eq.trans (coordOf_modelPermMap'
    (sortSplitPerm W) _ _) ?_
  congr 1
  exact coordOf_modelStarVec f P e'
    (degList (starAssignEnum W)) _
    (((isEven_comp_finCongr
      (degList_sum (starAssignEnum W)) c.val).mpr
      c.prop).comp (sortSplitPerm W))

end RS
