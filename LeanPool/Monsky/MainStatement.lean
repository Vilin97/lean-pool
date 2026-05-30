/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha and contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import LeanPool.Monsky.SegmentCounting
import LeanPool.Monsky.TriangleCorollary
import LeanPool.Monsky.MonskyEven

namespace LeanPool.Monsky

local notation "Triangle" => Fin 3 → (EuclideanSpace ℝ (Fin 2))

open BigOperators


theorem monsky_theorem (n : ℕ) :
    (∃ (S : Finset Triangle),
      closed_hull unit_square = ⋃ (Δ ∈ S), closed_hull Δ ∧
      Set.PairwiseDisjoint (↑S : Set Triangle) open_hull ∧
      (∀ Δ₁ ∈ S, ∀ Δ₂ ∈ S,
        MeasureTheory.volume (open_hull Δ₁) = MeasureTheory.volume (open_hull Δ₂)) ∧
      S.card = n)
    ↔ (n ≠ 0 ∧ Even n) := by
  constructor
  · -- Hard direction
    intro ⟨S, hCover, hDisjoint, hArea, hCard⟩
    refine ⟨?_,?_⟩
    · rw [←hCard]
      exact (Nat.ne_of_lt (no_empty_cover hCover (closed_pol_nonempty (by norm_num) _))).symm
    · by_contra hOdd
      rw [Nat.not_even_iff_odd] at hOdd
      have ⟨_,Γ,v,hv⟩ := valuation_on_reals
      have ⟨T,hTS,hTrainbow⟩ := monsky_rainbow v S ⟨hCover,hDisjoint⟩ ?_
      · apply no_odd_rainbow_triangle v T hTrainbow hv ?_
        · use n, hOdd
          rw [←hCard]
          refine equal_area_cover_implies_triangle_area_n S ?_ T hTS
          -- Refactor is_equal_area_cover to mean actually the hypotheses here
          -- So that the rest of the proof one line.
          refine ⟨⟨hCover,hDisjoint⟩, ?_⟩
          use triangle_area T
          intro T' hT'S
          specialize hArea T hTS T' hT'S
          have this := congrArg (f := fun x ↦ x.toReal) hArea
          simp only at this
          rw [volume_open_triangle,volume_open_triangle ] at this
          exact this.symm
      · -- Similarly we should have a seperate lemma that says that for any "equal area cover"
        -- of the triangles all determinants are nonzero.
        intro T hTS hcontra
        have bla := equal_area_cover_implies_triangle_area_n S ?_ T hTS
        · rw [triangle_area, hcontra, hCard] at bla
          simp only [abs_zero, zero_div, one_div, zero_eq_inv] at bla
          apply Nat.not_odd_iff_even.2 (Even.zero (α := ℕ))
          convert hOdd
          rw [←Nat.cast_inj (R := ℝ)]
          convert bla
          exact AddMonoidWithOne.natCast_zero
        · -- This is exactly the same as above so should be abstracted
          -- when refactoring is_equal_area_cover.
          -- We put it in for now.
          refine ⟨⟨hCover,hDisjoint⟩, ?_⟩
          use triangle_area T
          intro T' hT'S
          specialize hArea T hTS T' hT'S
          have this := congrArg (f := fun x ↦ x.toReal) hArea
          simp only at this
          rw [volume_open_triangle,volume_open_triangle ] at this
          exact this.symm
  · -- Easy direction
    intro ⟨hnNonzero, hnEven⟩
    have ⟨S, hScover, hScard⟩  := monsky_easy_direction' hnEven hnNonzero
    use S
    -- monsky_easy_direction' should be changed so that the rest of this is one line
    -- To Do: Make area definitions combine better...
    refine ⟨hScover.1.1, hScover.1.2, ?_, hScard⟩
    intro T₁ hT₁ T₂ hT₂
    rw [volume_open_triangle', volume_open_triangle']
    have ⟨A,hA⟩ := hScover.2
    unfold triangle_area at hA
    rw [hA _ hT₁, hA _ hT₂]

end Monsky
end LeanPool
