/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ModelStarVec

/-!
# The sort as a permutation and a cast

The inverse sort of the star factorization splits as a same-arity
permutation followed by the degree-sum cast, feeding the
braiding-word transport and the cast transport respectively.
-/

@[expose] public section

namespace RS

/-- The inverse sort as a permutation of the degree-sum arity. -/
noncomputable def sortSplitPerm (W : ClosedFragment) :
    _root_.Equiv.Perm
      (Fin ((degList (starAssignEnum W)).sum)) :=
  (sortEquiv (starAssignEnum W)).symm.trans (finCongr
    (degList_sum (starAssignEnum W)).symm)

/-- The inverse sort is its permutation followed by the arity
cast. -/
theorem sortEquiv_symm_split (W : ClosedFragment) :
    (sortEquiv (starAssignEnum W)).symm =
      (sortSplitPerm W).trans (finCongr
        (degList_sum (starAssignEnum W))) :=
  _root_.Equiv.ext (fun _ => Fin.ext rfl)

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The sort bundle map splits as permutation then cast. -/
theorem bmc_sort_split (W : ClosedFragment) :
    bundleMapClass f (sortEquiv (starAssignEnum W)).symm =
      HomSpace.comp f ((degList (starAssignEnum W)).sum)
        ((degList (starAssignEnum W)).sum)
        (edgeCount W + edgeCount W)
        (bundleMapClass f ((sortSplitPerm W) :
          Fin ((degList (starAssignEnum W)).sum) ≃
            Fin ((degList (starAssignEnum W)).sum)))
        (bundleMapClass f (finCongr
          (degList_sum (starAssignEnum W)))) := by
  rw [bundleMapClass_comp]
  exact bundleMapClass_congr f (sortEquiv_symm_split W)

end RS
