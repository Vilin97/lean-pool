/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.HalfspaceCut
import LeanPool.NandakumarRamanaRao.NRR.HalfSpace
import LeanPool.NandakumarRamanaRao.NRR.HalfSpaceCutArea

/-!
# `NRR.HalfSpaceCutAreaContinuity` — continuity of fixed-normal cut areas

For a fixed nonzero normal direction `u`, this module proves that the real-valued cut-area
functionals `cutAreaLower K u ·` and `cutAreaUpper K u ·` (defined in
`NRR.HalfSpaceCutArea`) are **continuous** functions of the threshold `c : ℝ`.

## The nondegeneracy hypothesis `u ≠ 0` is necessary

The hypothesis `u ≠ 0` is not a technical convenience — it is *mathematically required*. When
`u = 0` we have `⟪0, x⟫ = 0` for every `x`, so
`lowerClosedHalfspace 0 c = {x | 0 ≤ c}`, which equals `∅` for `c < 0` and the whole plane for
`c ≥ 0`. Hence `cutAreaLower K 0 c` is the step function that jumps from `0` to `K.area` at
`c = 0`; since a solid convex body has strictly positive area, this function is genuinely
**discontinuous** at `c = 0`. (Equivalently: the "boundary slice" `{x | ⟪0, x⟫ = c}` at `c = 0`
is the whole plane, which is *not* null, so the boundary-null argument below breaks down exactly
where the result fails.) Stating the theorems without `u ≠ 0` would therefore be stating a false
proposition, so the hypothesis is kept explicit. This is how the `u = 0` case is *handled*
rather than omitted.

## Proof route

The cut area is written as an integral of an indicator,
`cutAreaLower K u c = ∫ x, ((K : Set Plane) ∩ lowerClosedHalfspace u c).indicator (fun _ => 1) x`,
and continuity in `c` follows from `MeasureTheory.continuousAt_of_dominated`:

* the integrands are dominated by the integrable indicator `1_K` (finite because `K` is compact);
* for a.e. `x`, the map `c ↦ 1_{⟪u,x⟫ ≤ c}` is continuous at any point `c₀` — it fails only on the
 slice `{x ∈ K | ⟪u, x⟫ = c₀}`, which is null by `lowerCut_boundary_null` (needs `u ≠ 0`).
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace NRR.Geometry.ConvexBody

/-- The boundary slice `K ∩ {x | ⟪u, x⟫ = c}` of a fixed-normal cut has Lebesgue measure zero,
provided the normal `u` is nonzero. Derived from `NRR.Halfspace.hyperplane_null`. -/
theorem lowerCut_boundary_null
    (K : ConvexBody Plane) {u : Plane} (hu : u ≠ 0) (c : ℝ) :
    volume ((K : Set Plane) ∩ {x : Plane | ⟪u, x⟫ = c}) = 0 :=
  measure_mono_null Set.inter_subset_right (NRR.Halfspace.hyperplane_null hu c)

/-- **Continuity of the lower fixed-normal cut area** in the threshold, for a nonzero normal. -/
theorem continuous_cutAreaLower_fixedNormal
    (K : ConvexBody Plane) (u : Plane) (hu : u ≠ 0) :
    Continuous fun c : ℝ => cutAreaLower K u c := by
  -- Apply the dominated convergence theorem to show that the integral is continuous.
  have h_int_cont : Continuous (fun c : ℝ => ∫ x in K.carrier, (if ⟪u, x⟫ ≤ c then 1 else 0 : ℝ) ∂volume) := by
    refine' continuous_iff_continuousAt.mpr _;
    intro c₀; apply_rules [ MeasureTheory.continuousAt_of_dominated, continuousAt_const ] ;
    any_goals exact fun _ => 1;
    · exact Filter.Eventually.of_forall fun x => Measurable.aestronglyMeasurable ( by exact Measurable.ite ( measurableSet_le ( measurable_const.inner measurable_id' ) measurable_const ) measurable_const measurable_const );
    · exact Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun y => by split_ifs <;> norm_num;
    · exact ContinuousOn.integrableOn_compact K.isCompact ( continuousOn_const );
    · refine' MeasureTheory.ae_restrict_of_ae _;
      refine' MeasureTheory.measure_mono_null _ _;
      exact { x : Plane | ⟪u, x⟫ = c₀ };
      · intro x hx; contrapose! hx; simp_all +decide [ ContinuousAt ] ;
        cases lt_or_gt_of_ne hx <;> split_ifs <;> norm_num at *;
        · exact tendsto_const_nhds.congr' ( by filter_upwards [ lt_mem_nhds ‹_› ] with y hy; split_ifs <;> linarith );
        · linarith;
        · linarith;
        · exact tendsto_const_nhds.congr' ( by filter_upwards [ Iio_mem_nhds ‹_› ] with y hy; split_ifs <;> linarith [ hy.out ] );
      · exact NRR.Halfspace.hyperplane_null hu c₀;
  convert h_int_cont using 1;
  ext c; simp +decide [ ConvexBody.cutAreaLower ] ;
  erw [ MeasureTheory.integral_indicator ( show MeasurableSet ( lowerClosedHalfspace u c ) from lowerClosedHalfspace_isClosed u c |> IsClosed.measurableSet ) ] ; norm_num [ lowerClosedHalfspace ];
  rw [ MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply' ];
  · rw [ Set.inter_comm ];
  · exact K.isCompact.measurableSet

/-- **Continuity of the upper fixed-normal cut area** in the threshold, for a nonzero normal. -/
theorem continuous_cutAreaUpper_fixedNormal
    (K : ConvexBody Plane) (u : Plane) (hu : u ≠ 0) :
    Continuous fun c : ℝ => cutAreaUpper K u c := by
  -- This is the upper cut-area: apply the lower cut-area continuity result to the reflected body `K_(-(u))`.
  have h_reflect : Continuous (fun c : ℝ => cutAreaLower K (-u) (-c)) := by
    exact continuous_cutAreaLower_fixedNormal K ( -u ) ( neg_ne_zero.mpr hu ) |> Continuous.comp <| continuous_neg;
  convert h_reflect using 1;
  ext c
  simp [cutAreaUpper, cutAreaLower, upperClosedHalfspace, lowerClosedHalfspace]

end NRR.Geometry.ConvexBody
