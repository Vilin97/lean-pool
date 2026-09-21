/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.HalfSpace
/-!
# `NRR.Geometry.ConvexBody` — positive area implies nonempty interior

This module proves that a compact convex planar set with positive (Lebesgue) area has nonempty
interior.

The argument is the contrapositive: a convex set in the plane with empty interior has affine
span strictly smaller than the whole plane
(`Convex.interior_nonempty_iff_affineSpan_eq_top`), hence is contained in an affine line
`{x | ⟪u, x⟫ = c}` with `u ≠ 0`. Such a line is Lebesgue-null
(`NRR.Halfspace.hyperplane_null`, the project), so the set has zero area, contradicting
positivity.

The compactness hypothesis is retained on the public statements for a uniform public interface; it is not actually needed for the proof (only convexity and
finite-dimensionality of the plane are used).
-/

open scoped RealInnerProductSpace
open MeasureTheory

namespace NRR.Geometry.ConvexBody

/-- A compact convex planar set with empty interior is contained in an affine line
`{x | ⟪u, x⟫ = c}` with nonzero normal `u`.

The compactness hypothesis is not used; it is retained for a uniform interface. -/
theorem convex_emptyInterior_subset_affineLine
    {S : Set Plane}
    (hconv : Convex ℝ S)
    (hcomp : IsCompact S)
    (hint : interior S = ∅) :
    ∃ u : Plane, ∃ c : ℝ, u ≠ 0 ∧ S ⊆ {x : Plane | ⟪u, x⟫ = c} := by
  by_cases h_empty : S = ∅
  · exact ⟨EuclideanSpace.single 0 1, 0, ne_of_apply_ne (fun x => x 0) one_ne_zero,
      by simp +decide [h_empty]⟩
  · have h_affine_span : (affineSpan ℝ S) ≠ ⊤ := by
      have := hconv.interior_nonempty_iff_affineSpan_eq_top
      aesop
    -- The affine span is nonempty since `S` is nonempty.
    have h_affine_span_nonempty : (affineSpan ℝ S : Set Plane).Nonempty :=
      ⟨_, subset_affineSpan ℝ S (Classical.choose_spec (Set.nonempty_iff_ne_empty.mpr h_empty))⟩
    -- Hence the direction of the affine span is a proper submodule.
    have h_direction_ne_top : (affineSpan ℝ S).direction ≠ ⊤ := by
      contrapose! h_affine_span
      obtain ⟨x, hx⟩ := h_affine_span_nonempty
      ext y
      convert AffineSubspace.vadd_mem_of_mem_direction
        (h_affine_span.symm ▸ Submodule.mem_top : y - x ∈ (affineSpan ℝ S).direction) hx using 1
      simp
    -- A proper submodule has a nonzero vector in its orthogonal complement.
    obtain ⟨u, hu⟩ : ∃ u : Plane, u ≠ 0 ∧ ∀ w ∈ (affineSpan ℝ S).direction, ⟪w, u⟫ = 0 := by
      have h_orthogonal_complement : (affineSpan ℝ S).directionᗮ ≠ ⊥ :=
        fun h => h_direction_ne_top <| Submodule.orthogonal_eq_bot_iff.mp h
      obtain ⟨u, hu⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_orthogonal_complement
      exact ⟨u, hu.2, fun w hw => (Submodule.mem_orthogonal _ _).mp hu.1 w hw⟩
    refine ⟨u, ⟪u, Classical.choose h_affine_span_nonempty⟫, hu.1, fun x hx => ?_⟩
    have := hu.2 (x -ᵥ Classical.choose h_affine_span_nonempty) ?_
    · simp only [Set.mem_ofPred_eq]
      simp_all [inner_sub_left, sub_eq_zero, real_inner_comm]
    · exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hx)
        (Classical.choose_spec h_affine_span_nonempty)

/-- A compact convex planar set with positive area has nonempty interior.

The compactness hypothesis is not used; it is retained for a uniform interface. -/
theorem interior_nonempty_of_convex_compact_positive_area
    {S : Set Plane}
    (hconv : Convex ℝ S)
    (hcomp : IsCompact S)
    (harea : 0 < (volume S).toReal) :
    (interior S).Nonempty := by
  rcases (interior S).eq_empty_or_nonempty with h | h
  · exfalso
    obtain ⟨u, c, hu, hc⟩ := convex_emptyInterior_subset_affineLine hconv hcomp h
    have hnull := NRR.Halfspace.hyperplane_null hu c
    have hzero : volume S = 0 := nonpos_iff_eq_zero.mp (hnull ▸ measure_mono hc)
    rw [hzero] at harea
    simp at harea
  · exact h

end NRR.Geometry.ConvexBody
