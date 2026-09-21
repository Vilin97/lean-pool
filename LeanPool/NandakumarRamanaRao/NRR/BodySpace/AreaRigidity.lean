/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.Basic
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PositiveAreaInterior
/-!
# `NRR.BodySpace.AreaRigidity` — area rigidity for nested convex subbodies

This module proves the geometric rigidity statement used to identify a Hausdorff limit of canonical
cells: if one compact convex planar set is *strictly* contained in another with nonempty interior,
its Lebesgue area is strictly smaller. The consequence for the fixed-parent hyperspace is that a
nested pair of convex subbodies with equal positive area must coincide.

The set-level argument is elementary: a point of `interior D` lies outside the closed set `C` (else
`D = closure (interior D) ⊆ C`, contradicting strictness), and a small ball around that point sits
inside `D` and misses `C`, contributing strictly positive extra area.
-/

open MeasureTheory Metric

open NRR.Geometry

namespace NRR

/-- **Strict area monotonicity for nested compact convex bodies.** If `C ⊂ D` with `C`, `D` compact
and convex and `D` of nonempty interior, then `C` has strictly smaller Lebesgue area than `D`.

The convexity of `C` (`hCconv`) is part of the intended interface but is not needed for the proof:
only the compactness (hence closedness) of `C` and the convexity and nonempty interior of `D`
enter the argument. -/
theorem measure_lt_of_compact_convex_ssubset
    {C D : Set Plane}
    (hCcomp : IsCompact C) (hDcomp : IsCompact D)
    (hCconv : Convex ℝ C) (hDconv : Convex ℝ D)
    (hCD : C ⊂ D)
    (hDint : (interior D).Nonempty) :
    (volume C).toReal < (volume D).toReal := by
  have h_area_lt : (volume C) < (volume D) := by
    obtain ⟨x, hx⟩ : ∃ x : Plane, x ∈ interior D ∧ x ∉ C := by
      by_contra! h;
      have := hDconv.closure_interior_eq_closure_of_nonempty_interior hDint;
      exact hCD.2 ( by rw [ hDcomp.isClosed.closure_eq ] at this; exact this ▸ closure_minimal ( Set.subset_def.mpr h ) hCcomp.isClosed );
    obtain ⟨ε, hε⟩ : ∃ ε > 0, Metric.ball x ε ⊆ interior D := by
      exact Metric.isOpen_iff.mp ( isOpen_interior ) x hx.1
    obtain ⟨δ, hδ⟩ : ∃ δ > 0, Metric.ball x δ ⊆ Cᶜ := by
      exact Metric.mem_nhds_iff.mp ( hCcomp.isClosed.isOpen_compl.mem_nhds hx.2 )
    set r := min ε δ with hr_def
    have hr_pos : 0 < r := by
      exact lt_min hε.1 hδ.1
    have hr_ball : Metric.ball x r ⊆ D ∧ Disjoint (Metric.ball x r) C := by
      exact ⟨ Set.Subset.trans ( Metric.ball_subset_ball ( min_le_left _ _ ) ) ( Set.Subset.trans hε.2 ( interior_subset ) ), Set.disjoint_left.mpr fun y hy₁ hy₂ => hδ.2 ( Metric.ball_subset_ball ( min_le_right _ _ ) hy₁ ) hy₂ ⟩;
    have h_volume : volume C + volume (Metric.ball x r) ≤ volume D := by
      rw [ ← MeasureTheory.measure_union ];
      · exact MeasureTheory.measure_mono ( Set.union_subset hCD.1 hr_ball.1 );
      · exact hr_ball.2.symm;
      · exact measurableSet_ball;
    refine' lt_of_lt_of_le _ h_volume;
    refine' ENNReal.lt_add_right _ _;
    · exact hCcomp.measure_lt_top.ne;
    · exact ne_of_gt ( Metric.measure_ball_pos _ _ hr_pos );
  gcongr;
  exact hDcomp.measure_lt_top.ne

namespace ConvexSubbody

variable {K : Geometry.ConvexBody Plane}

/-- **Area rigidity for nested convex subbodies.** If the carrier of `C` is contained in that of
`D`, both have equal area, and `D` has positive area, then `C = D`. -/
theorem eq_of_subset_of_area_eq
    {C D : ConvexSubbody K}
    (hCD : (C.body : Set Plane) ⊆ (D.body : Set Plane))
    (harea : C.area = D.area)
    (hDpos : 0 < D.area) :
    C = D := by
  by_contra h_neq
  have h_strict : (C.body : Set Plane) ⊂ (D.body : Set Plane) :=
    hCD.ssubset_of_ne fun h => h_neq (ConvexSubbody.ext h)
  have hDint : (interior (D.body : Set Plane)).Nonempty :=
    Geometry.ConvexBody.interior_nonempty_of_convex_compact_positive_area
      D.convex D.isCompact hDpos
  have hlt := measure_lt_of_compact_convex_ssubset
    C.isCompact D.isCompact C.convex D.convex h_strict hDint
  exact absurd harea (ne_of_lt hlt)

/-- Ergonomic form of `eq_of_subset_of_area_eq` phrased with the subbody-to-set coercion. -/
theorem eq_of_subset_of_area_eq'
    {C D : ConvexSubbody K}
    (hCD : (C : Set Plane) ⊆ D)
    (harea : C.area = D.area)
    (hDpos : 0 < D.area) :
    C = D :=
  eq_of_subset_of_area_eq hCD harea hDpos

end ConvexSubbody

end NRR
