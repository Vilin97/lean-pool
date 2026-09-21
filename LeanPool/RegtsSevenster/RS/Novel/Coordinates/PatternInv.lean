/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexBij

/-!
# The pattern inversion count

The master sum's global sign at a data colouring depends only on
the pattern: the sort-permutation's odd inversions count pairs of
participating slots, a pure `(W, F)` quantity.
-/

namespace RS

open Classical Finset

variable {k ℓ : ℕ}

open Classical in
/-- The pattern inversion count of an edge subset: inverted sort
pairs of participating slots. -/
noncomputable def patternOddInv (W : ClosedFragment)
    (F : EdgeSubset W) : ℕ :=
  (Finset.univ.filter
    (fun p : Fin (ds W).sum × Fin (ds W).sum =>
      p.1 < p.2 ∧ sortSplitPerm W p.1 > sortSplitPerm W p.2 ∧
      (starFlagEnum W).symm
        (finCongr (degList_sum (starAssignEnum W))
          (sortSplitPerm W p.1)) ∈ F.flags ∧
      (starFlagEnum W).symm
        (finCongr (degList_sum (starAssignEnum W))
          (sortSplitPerm W p.2)) ∈ F.flags)).card

open Classical in
/-- **The master sign at a data colouring is the pattern
inversion count.** -/
theorem oddInversions_colouringOf (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) :
    oddInversions (sortSplitPerm W)
      ((colouringOf W F ψ φ) ∘
        finCongr (degList_sum (starAssignEnum W))) =
    patternOddInv W F := by
  unfold oddInversions patternOddInv
  refine congrArg Finset.card (Finset.filter_congr
    (fun p _ => ?_))
  have hmem : ∀ t : Fin (edgeCount W + edgeCount W),
      ((colouringOf W F ψ φ) t).isRight = true ↔
      (starFlagEnum W).symm t ∈ F.flags := by
    intro t
    rw [← colourFlags_colouringOf W F ψ φ,
      mem_colourFlags_iff, _root_.Equiv.apply_symm_apply]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (hmem _).mp h3, (hmem _).mp h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (hmem _).mpr h3, (hmem _).mpr h4⟩

end RS
