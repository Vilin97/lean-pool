/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.HalfspaceCut
import LeanPool.NandakumarRamanaRao.NRR.HalfSpace
import LeanPool.NandakumarRamanaRao.NRR.HalfSpaceCutArea
import LeanPool.NandakumarRamanaRao.NRR.HalfSpaceCutAreaContinuity

/-!
# `NRR.Geometry.HalfspaceFiniteIntersectionAreaContinuity`

Area continuity for **finite intersections of fixed-normal moving halfspaces**.

For a finite index type `ι`, fixed normals `u : ι → Plane` and offsets `c : ι → ℝ`, the set
`finiteHalfspaceIntersection K u c` is the intersection of a planar convex body `K` with the
finitely many closed lower halfspaces `{x | ⟪u i, x⟫ ≤ c i}`, kept purely as a `Set Plane`
(never bundled as a `ConvexBody`). Its real-valued Lebesgue area is
`finiteHalfspaceIntersectionArea K u c`.

The main result `continuous_finiteHalfspaceIntersectionArea` states that this area depends
continuously on continuously-moving offsets.

## The nondegeneracy hypothesis `∀ i, u i ≠ 0` is necessary

Just as in the single-halfspace case (`continuous_cutAreaLower_fixedNormal`), the hypothesis
`u i ≠ 0` for each `i` is *mathematically required*, and its absence would make the theorem
**false**. Indeed, if some `u i = 0` then `lowerClosedHalfspace 0 (c i) = {x | 0 ≤ c i}`, which
is the whole plane for `c i ≥ 0` and empty for `c i < 0`. Taking a single index with `u 0 = 0`
and offset `c a 0 = a`, the intersection area jumps from `0` (for `a < 0`) to `K.area > 0`
(for `a ≥ 0`) at `a = 0`, hence is discontinuous. The corresponding "boundary slice"
`{x | ⟪0, x⟫ = 0}` is the whole plane, which is not null, so the boundary-null argument breaks
down exactly where the result fails. We therefore keep `∀ i, u i ≠ 0` explicit; this is how the
degenerate normal is *handled* rather than omitted.

## Proof route

The offset-to-area map factors as `A ∘ c` where
`A : (ι → ℝ) → ℝ, A f = finiteHalfspaceIntersectionArea K u f`. Since `ι` is finite, `ι → ℝ` is a
(first-countable, metrizable) product space, so `Continuous A` follows from
`MeasureTheory.continuous_of_dominated`:

* the area is the integral of the indicator of the (measurable, `K`-contained) intersection;
* the integrands are dominated by the integrable indicator `1_K` (finite, `K` compact);
* for a.e. `x`, the map `f ↦ 1_{∀ i, ⟪u i, x⟫ ≤ f i}` is continuous (in fact locally constant)
 at any `f₀` — it can fail only on the finite union of boundary hyperplanes
 `⋃ i {x | ⟪u i, x⟫ = f₀ i}`, which is null because each `u i ≠ 0`.

Continuity for an arbitrary topological domain `α` is then obtained by composing with the
continuous offset map `c : α → ι → ℝ`, so no first-countability hypothesis on `α` is needed.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace NRR.Geometry.ConvexBody

variable {ι : Type*}

/-- The intersection of a convex body `K` with the finitely many closed lower halfspaces with
normals `u i` and offsets `c i`. Kept purely as a `Set Plane`. -/
def finiteHalfspaceIntersection
    (K : ConvexBody Plane) (u : ι → Plane) (c : ι → ℝ) : Set Plane :=
  (K : Set Plane) ∩ ⋂ i, Geometry.lowerClosedHalfspace (u i) (c i)

/-- The real-valued Lebesgue area of a finite fixed-normal halfspace intersection. -/
noncomputable def finiteHalfspaceIntersectionArea
    (K : ConvexBody Plane) (u : ι → Plane) (c : ι → ℝ) : ℝ :=
  (volume (finiteHalfspaceIntersection K u c)).toReal

/-- A finite halfspace intersection is contained in the body. -/
theorem finiteHalfspaceIntersection_subset
    (K : ConvexBody Plane) (u : ι → Plane) (c : ι → ℝ) :
    finiteHalfspaceIntersection K u c ⊆ (K : Set Plane) :=
  Set.inter_subset_left

/-- Membership in a finite halfspace intersection. -/
theorem mem_finiteHalfspaceIntersection
    (K : ConvexBody Plane) (u : ι → Plane) (c : ι → ℝ) (x : Plane) :
    x ∈ finiteHalfspaceIntersection K u c ↔
      x ∈ (K : Set Plane) ∧ ∀ i, ⟪u i, x⟫ ≤ c i := by
  simp [finiteHalfspaceIntersection, Geometry.mem_lowerClosedHalfspace]

/-- A finite halfspace intersection is measurable. -/
theorem measurableSet_finiteHalfspaceIntersection [Countable ι]
    (K : ConvexBody Plane) (u : ι → Plane) (c : ι → ℝ) :
    MeasurableSet (finiteHalfspaceIntersection K u c) := by
  refine (K.isCompact.measurableSet).inter ?_
  exact MeasurableSet.iInter fun i =>
    (Geometry.lowerClosedHalfspace_isClosed (u i) (c i)).measurableSet

/-- The measure of a finite halfspace intersection is finite. -/
theorem volume_finiteHalfspaceIntersection_lt_top
    (K : ConvexBody Plane) (u : ι → Plane) (c : ι → ℝ) :
    volume (finiteHalfspaceIntersection K u c) < ⊤ :=
  lt_of_le_of_lt (measure_mono (finiteHalfspaceIntersection_subset K u c)) K.area_lt_top

/-
**Continuity of the finite fixed-normal intersection area in the offset vector.** For fixed
nonzero normals, the area is a continuous function of the offset vector `f : ι → ℝ`.
-/
theorem continuous_finiteHalfspaceIntersectionArea_pi [Fintype ι]
    (K : ConvexBody Plane) (u : ι → Plane) (hu : ∀ i, u i ≠ 0) :
    Continuous fun f : ι → ℝ => finiteHalfspaceIntersectionArea K u f := by
  refine' continuous_iff_continuousAt.mpr fun f₀ => _;
  have h_dominated : ∀ᵐ x ∂volume, ContinuousAt (fun f : ι → ℝ => (K.finiteHalfspaceIntersection u f).indicator (fun _ => (1 : ℝ)) x) f₀ := by
    refine' MeasureTheory.measure_mono_null _ _;
    exact ⋃ i, { x : Plane | ⟪u i, x⟫ = f₀ i };
    · intro x hx; contrapose! hx; simp_all +decide [ ContinuousAt ];
      by_cases hxK : x ∈ (K : Set Plane) <;> simp_all +decide [ NRR.Geometry.ConvexBody.finiteHalfspaceIntersection ];
      by_cases h : ∀ i, ⟪u i, x⟫ ≤ f₀ i <;> simp_all +decide;
      · exact fun i => Filter.eventually_of_mem ( IsOpen.mem_nhds ( isOpen_lt ( continuous_const ) ( continuous_apply i ) ) ( lt_of_le_of_ne ( h i ) ( hx i ) ) ) fun f hf => hf.le;
      · obtain ⟨ i, hi ⟩ := h;
        filter_upwards [ IsOpen.mem_nhds ( isOpen_lt ( continuous_apply i ) continuous_const ) hi ] with f hf using iff_of_false ( fun h => hf.not_ge <| h i ) ( fun h => hi.not_ge <| h i );
    · exact MeasureTheory.measure_iUnion_null fun i => NRR.Halfspace.hyperplane_null ( hu i ) ( f₀ i );
  have h_integrable : MeasureTheory.Integrable (fun x => (K : Set Plane).indicator (fun _ => (1 : ℝ)) x) volume := by
    rw [ MeasureTheory.integrable_indicator_iff ];
    · simp +decide [ K.isCompact.measure_lt_top ];
    · exact K.isCompact.measurableSet;
  have h_dominated : ∀ᵐ x ∂volume, ∀ f : ι → ℝ, |(K.finiteHalfspaceIntersection u f).indicator (fun _ => (1 : ℝ)) x| ≤ (K : Set Plane).indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [ ] with x f; by_cases hx : x ∈ K.carrier <;> simp +decide [ hx ];
    · by_cases h : x ∈ K.finiteHalfspaceIntersection u f <;> simp +decide [ h ];
    · exact fun h => hx h.1;
  have h_cont : ContinuousAt (fun f : ι → ℝ => ∫ x, (K.finiteHalfspaceIntersection u f).indicator (fun _ => (1 : ℝ)) x ∂volume) f₀ := by
    apply_rules [ MeasureTheory.continuousAt_of_dominated ];
    · exact Filter.Eventually.of_forall fun f => Measurable.aestronglyMeasurable ( by exact Measurable.indicator measurable_const ( by exact measurableSet_finiteHalfspaceIntersection K u f ) );
    · exact Filter.Eventually.of_forall fun f => h_dominated.mono fun x hx => hx f;
  convert h_cont using 1;
  ext f; rw [ MeasureTheory.integral_indicator ( measurableSet_finiteHalfspaceIntersection K u f ) ]; simp +decide [ finiteHalfspaceIntersectionArea ];
  rfl

/-- **Continuity of the finite fixed-normal moving-halfspace intersection area.** For fixed
nonzero normals `u` and continuously-moving offsets `c a`, the intersection area depends
continuously on `a`. The hypothesis `∀ i, u i ≠ 0` is necessary (see the module docstring). -/
theorem continuous_finiteHalfspaceIntersectionArea
    {α : Type*} [TopologicalSpace α] [Fintype ι]
    (K : ConvexBody Plane) (u : ι → Plane) (hu : ∀ i, u i ≠ 0)
    (c : α → ι → ℝ) (hc : Continuous c) :
    Continuous fun a : α => finiteHalfspaceIntersectionArea K u (c a) :=
  (continuous_finiteHalfspaceIntersectionArea_pi K u hu).comp hc

/-- **Fallback / power-cell specialization.** Weights `w : Fin n → ℝ` moving the offsets of `m`
fixed-normal halfspaces yield a continuous restricted-intersection area. -/
theorem continuous_finiteHalfspaceIntersectionArea_weights
    {m n : ℕ} (K : ConvexBody Plane) (u : Fin m → Plane) (hu : ∀ i, u i ≠ 0)
    (c : (Fin n → ℝ) → Fin m → ℝ) (hc : Continuous c) :
    Continuous fun w : Fin n → ℝ => finiteHalfspaceIntersectionArea K u (c w) :=
  continuous_finiteHalfspaceIntersectionArea K u hu c hc

end NRR.Geometry.ConvexBody
