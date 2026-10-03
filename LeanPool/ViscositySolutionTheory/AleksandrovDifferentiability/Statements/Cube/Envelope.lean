/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.GoodSet

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Cube-local Lipschitz-envelope squeeze lemmas

This file isolates the source proof's final envelope argument. Once the coordinate gradient
function is squeezed between two Lipschitz envelopes with the same derivative at a good point,
the coordinate gradient has the corresponding first-order expansion along the differentiability
set.
-/

@[expose] public noncomputable section

open MeasureTheory
open Asymptotics
open scoped MeasureTheory
open scoped NNReal
open scoped Topology

namespace AleksandrovDifferentiability

/-- If `U \ D` is null and `U` is open, then `U ∩ D` is dense in `U`.

This is the local form of the source proof's statement that a full-measure subset of an open cube
is dense in that cube. -/
theorem isOpen_subset_closure_inter_of_measure_diff_eq_zero
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X}
    [Measure.IsOpenPosMeasure μ] {U D : Set X}
    (hUopen : IsOpen U) (hnull : μ (U \ D) = 0) :
    U ⊆ closure (U ∩ D) := by
  intro x hxU
  rw [mem_closure_iff]
  intro O hOopen hxO
  by_contra hnonempty
  have hOU_subset : O ∩ U ⊆ U \ D := by
    intro y hy
    refine ⟨hy.2, ?_⟩
    intro hyD
    exact hnonempty ⟨y, hy.1, hy.2, hyD⟩
  have hOU_null : μ (O ∩ U) = 0 :=
    measure_mono_null hOU_subset hnull
  have hOU_open : IsOpen (O ∩ U) := hOopen.inter hUopen
  have hOU_nonempty : (O ∩ U).Nonempty := ⟨x, hxO, hxU⟩
  exact (hOU_open.measure_pos μ hOU_nonempty).ne' hOU_null

/-- Differentiability points of `u` inside the source cube `Q_r`. -/
def sourceCubeDifferentiabilitySet (n : ℕ) (r : ℝ) (u : SourceCubeSpace n → ℝ) :
    Set (SourceCubeSpace n) :=
  sourceOpenCube n r ∩ firstOrderDifferentiabilitySet u

/-- The differentiability points in `Q_1` are dense enough for the envelope argument on `Q_1`. -/
theorem sourceOpenCube_one_subset_closure_sourceCubeDifferentiabilitySet_one_of_convex
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    sourceOpenCube n 1 ⊆
      closure (sourceCubeDifferentiabilitySet n 1 u) :=
  isOpen_subset_closure_inter_of_measure_diff_eq_zero
    (μ := volume) (isOpen_sourceOpenCube (n := n) 1)
    (ConvexOn.volume_sourceOpenCube_diff_firstOrderDifferentiabilitySet_eq_zero hu)

/-- The differentiability points in `Q_{3/2}` are dense enough for the envelope argument on
`Q_1`. -/
theorem sourceOpenCube_one_subset_closure_sourceCubeDifferentiabilitySet_three_halves_of_convex
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    sourceOpenCube n 1 ⊆
      closure (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u) := by
  have hsubset :
      sourceCubeDifferentiabilitySet n 1 u ⊆
        sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u := by
    intro x hx
    exact
      ⟨sourceOpenCube_subset_of_le (n := n) (r := 1) (R := (3 / 2 : ℝ))
          (by norm_num) hx.1,
        hx.2⟩
  intro x hx
  exact
    closure_mono hsubset
      (sourceOpenCube_one_subset_closure_sourceCubeDifferentiabilitySet_one_of_convex hu hx)

/-- The density theorem gives a nontrivial differentiability-point sampling filter at each point
of `Q_1`, with sampling still inside `Q_1`. -/
theorem sourceOpenCube_one_nhdsWithin_sourceCubeDifferentiabilitySet_one_neBot_of_convex
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    {x : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) :
    (𝓝[sourceCubeDifferentiabilitySet n 1 u] x).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp
    (sourceOpenCube_one_subset_closure_sourceCubeDifferentiabilitySet_one_of_convex hu hx)

/-- The density theorem gives a nontrivial differentiability-point sampling filter at each point
of `Q_1`. -/
theorem sourceOpenCube_one_nhdsWithin_sourceCubeDifferentiabilitySet_three_halves_neBot_of_convex
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    {x : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) :
    (𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp
    (sourceOpenCube_one_subset_closure_sourceCubeDifferentiabilitySet_three_halves_of_convex hu hx)

/-- The good set `Omega_m` lies in the differentiability set `D_{3/2}` used for envelopes. -/
theorem cubeGoodSet_subset_sourceCubeDifferentiabilitySet_three_halves
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} :
    cubeGoodSet n u (m : ℝ) ⊆ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u := by
  intro x hx
  rcases (mem_cubeGoodSet.mp hx) with ⟨hxQ, hdiff, _hopening⟩
  exact
    ⟨sourceOpenCube_subset_of_le (n := n) (r := 1) (R := (3 / 2 : ℝ))
        (by norm_num) hxQ,
      hdiff⟩

/-- The good set `Omega_m` lies in the working cube `Q_1`. -/
theorem cubeGoodSet_subset_sourceOpenCube_one
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} :
    cubeGoodSet n u (m : ℝ) ⊆ sourceOpenCube n 1 := by
  intro x hx
  exact (mem_cubeGoodSet.mp hx).1

/-- Lower boundedness of a coordinate of the gradient on `D_{3/2}`. -/
theorem sourceCubeDifferentiabilitySet_three_halves_frechetGradient_coord_bddBelow
    {n : ℕ} {u : SourceCubeSpace n → ℝ} (i : Fin n)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u) :
    ∃ M : ℝ, ∀ y ∈ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u,
      -M ≤ frechetGradient u y i := by
  refine ⟨sourceCubeOscillation n u, ?_⟩
  intro y hy
  have hnorm :
      ‖frechetGradient u y‖ ≤ sourceCubeOscillation n u :=
    ConvexOn.norm_frechetGradient_le_sourceCubeOscillation_of_boundedOn_three_halves
      hu hbounded hy.1 hy.2
  have habs :
      |frechetGradient u y i| ≤ sourceCubeOscillation n u :=
    (abs_sourceCoordinate_le_norm (frechetGradient u y) i).trans hnorm
  exact (abs_le.mp habs).1

/-- Upper boundedness of a coordinate of the gradient on `D_{3/2}`. -/
theorem sourceCubeDifferentiabilitySet_three_halves_frechetGradient_coord_bddAbove
    {n : ℕ} {u : SourceCubeSpace n → ℝ} (i : Fin n)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u) :
    ∃ M : ℝ, ∀ y ∈ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u,
      frechetGradient u y i ≤ M := by
  refine ⟨sourceCubeOscillation n u, ?_⟩
  intro y hy
  have hnorm :
      ‖frechetGradient u y‖ ≤ sourceCubeOscillation n u :=
    ConvexOn.norm_frechetGradient_le_sourceCubeOscillation_of_boundedOn_three_halves
      hu hbounded hy.1 hy.2
  have habs :
      |frechetGradient u y i| ≤ sourceCubeOscillation n u :=
    (abs_sourceCoordinate_le_norm (frechetGradient u y) i).trans hnorm
  exact (abs_le.mp habs).2

/-- Cross-estimate input for the coordinate-gradient envelope argument. -/
theorem cubeGoodSet_nat_coordinateGradient_cross_bound_three_halves
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} (i : Fin n)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u) :
    ∀ x ∈ cubeGoodSet n u (m : ℝ),
      ∀ y ∈ sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u,
        |frechetGradient u y i - frechetGradient u x i| ≤
          (Real.toNNReal (2 * (((m : ℝ) + 1) + sourceCubeOscillation n u)) : ℝ) *
            dist y x := by
  intro x hx y hy
  have hosc_nonneg : 0 ≤ sourceCubeOscillation n u :=
    sourceCubeOscillation_nonneg_of_boundedOn hbounded
  have hcoeff_nonneg :
      0 ≤ 2 * (((m : ℝ) + 1) + sourceCubeOscillation n u) := by
    nlinarith
  have hmain :=
    cubeGoodSet_nat_abs_gradient_coord_sub_le_three_halves_global
      (n := n) (m := m) (u := u) (x0 := x) (x1 := y) i hu hbounded hx hy.1 hy.2
  simpa [dist_eq_norm, Real.toNNReal_of_nonneg hcoeff_nonneg] using hmain

/-- The lower McShane-type envelope used in the source proof:
`inf_y (g y + K * dist x y)` over `y ∈ E`. -/
noncomputable def lowerMcShaneEnvelope
    {n : ℕ} (K : ℝ≥0) (E : Set (SourceCubeSpace n)) (g : SourceCubeSpace n → ℝ) :
    SourceCubeSpace n → ℝ :=
  fun x => ⨅ y : E, g y + (K : ℝ) * dist x y

/-- The upper McShane-type envelope, defined by duality from the lower envelope. -/
noncomputable def upperMcShaneEnvelope
    {n : ℕ} (K : ℝ≥0) (E : Set (SourceCubeSpace n)) (g : SourceCubeSpace n → ℝ) :
    SourceCubeSpace n → ℝ :=
  fun x => -lowerMcShaneEnvelope K E (fun y => -g y) x

private theorem lowerMcShaneEnvelope_range_bddBelow
    {n : ℕ} {K : ℝ≥0} {E : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    (hbound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ g y) (x : SourceCubeSpace n) :
    BddBelow (Set.range fun y : E => g y + (K : ℝ) * dist x y) := by
  rcases hbound with ⟨M, hM⟩
  refine ⟨-M, ?_⟩
  rintro a ⟨y, rfl⟩
  exact (hM y y.2).trans (le_add_of_nonneg_right (mul_nonneg K.coe_nonneg dist_nonneg))

/-- A bounded-below lower McShane envelope is globally Lipschitz with the same constant.

The proof is the standard source-envelope estimate: compare every cone based at `y` using the
triangle inequality, then pass to the infimum. -/
theorem lowerMcShaneEnvelope_lipschitzWith
    {n : ℕ} {K : ℝ≥0} {E : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    [Nonempty E] (hbound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ g y) :
    LipschitzWith K (lowerMcShaneEnvelope K E g) := by
  refine LipschitzWith.of_le_add_mul K ?_
  intro x z
  have hxB := lowerMcShaneEnvelope_range_bddBelow (K := K) hbound x
  have hzB := lowerMcShaneEnvelope_range_bddBelow (K := K) hbound z
  have hsub :
      lowerMcShaneEnvelope K E g x - (K : ℝ) * dist x z ≤
        lowerMcShaneEnvelope K E g z := by
    refine le_ciInf ?_
    intro y
    have hx_le : lowerMcShaneEnvelope K E g x ≤ g y + (K : ℝ) * dist x y := by
      exact ciInf_le hxB y
    have htri : dist x y ≤ dist z y + dist x z := by
      calc
        dist x y ≤ dist x z + dist z y := dist_triangle x z y
        _ = dist z y + dist x z := by ring
    have hx_le' :
        lowerMcShaneEnvelope K E g x ≤
          g y + (K : ℝ) * (dist z y + dist x z) := by
      exact hx_le.trans (by gcongr)
    nlinarith
  nlinarith

/-- The lower envelope is bounded above by every defining cone. -/
theorem lowerMcShaneEnvelope_le_base
    {n : ℕ} {K : ℝ≥0} {E : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    (hbound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ g y) {x y : SourceCubeSpace n} (hy : y ∈ E) :
    lowerMcShaneEnvelope K E g x ≤ g y + (K : ℝ) * dist x y := by
  exact ciInf_le (lowerMcShaneEnvelope_range_bddBelow (K := K) hbound x) ⟨y, hy⟩

/-- A bounded-above upper McShane envelope is globally Lipschitz with the same constant. -/
theorem upperMcShaneEnvelope_lipschitzWith
    {n : ℕ} {K : ℝ≥0} {E : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    [Nonempty E] (hbound : ∃ M : ℝ, ∀ y ∈ E, g y ≤ M) :
    LipschitzWith K (upperMcShaneEnvelope K E g) := by
  rcases hbound with ⟨M, hM⟩
  have hnegBound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ -g y := by
    refine ⟨M, ?_⟩
    intro y hy
    linarith [hM y hy]
  have hlip : LipschitzWith K (lowerMcShaneEnvelope K E (fun y => -g y)) :=
    lowerMcShaneEnvelope_lipschitzWith (K := K) (E := E) (g := fun y => -g y) hnegBound
  refine LipschitzWith.of_dist_le_mul ?_
  intro x z
  simpa [upperMcShaneEnvelope, dist_neg_neg] using hlip.dist_le_mul x z

/-- Every defining cone lies below the upper envelope. -/
theorem base_le_upperMcShaneEnvelope
    {n : ℕ} {K : ℝ≥0} {E : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    (hbound : ∃ M : ℝ, ∀ y ∈ E, g y ≤ M) {x y : SourceCubeSpace n} (hy : y ∈ E) :
    g y - (K : ℝ) * dist x y ≤ upperMcShaneEnvelope K E g x := by
  rcases hbound with ⟨M, hM⟩
  have hnegBound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ -g y := by
    refine ⟨M, ?_⟩
    intro z hz
    linarith [hM z hz]
  have hle :
      lowerMcShaneEnvelope K E (fun z => -g z) x ≤
        -g y + (K : ℝ) * dist x y :=
    lowerMcShaneEnvelope_le_base (K := K) (E := E) (g := fun z => -g z) hnegBound hy
  dsimp [upperMcShaneEnvelope]
  linarith

/-- The lower envelope agrees with `g` at points where the source cross estimate is based. -/
theorem lowerMcShaneEnvelope_eq_on_of_cross_bound
    {n : ℕ} {K : ℝ≥0} {E F : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    (hbound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ g y)
    (hFE : F ⊆ E)
    (hcross : ∀ x ∈ F, ∀ y ∈ E, |g y - g x| ≤ (K : ℝ) * dist y x)
    {x : SourceCubeSpace n} (hx : x ∈ F) :
    lowerMcShaneEnvelope K E g x = g x := by
  have hxE : x ∈ E := hFE hx
  have : Nonempty E := ⟨⟨x, hxE⟩⟩
  apply le_antisymm
  · simpa using
      lowerMcShaneEnvelope_le_base (K := K) (E := E) (g := g) hbound (x := x) (y := x) hxE
  · refine le_ciInf ?_
    intro y
    have hy_le : g x ≤ g y + (K : ℝ) * dist x y := by
      have habs := hcross x hx y y.2
      have hleft : g x - g y ≤ (K : ℝ) * dist x y := by
        have hraw : g x - g y ≤ (K : ℝ) * dist (y : SourceCubeSpace n) x := by
          calc
            g x - g y = -(g y - g x) := by ring
            _ ≤ |g y - g x| := neg_le_abs _
            _ ≤ (K : ℝ) * dist (y : SourceCubeSpace n) x := habs
        simpa [dist_comm] using hraw
      linarith
    exact hy_le

/-- The upper envelope agrees with `g` at points where the source cross estimate is based. -/
theorem upperMcShaneEnvelope_eq_on_of_cross_bound
    {n : ℕ} {K : ℝ≥0} {E F : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    (hbound : ∃ M : ℝ, ∀ y ∈ E, g y ≤ M)
    (hFE : F ⊆ E)
    (hcross : ∀ x ∈ F, ∀ y ∈ E, |g y - g x| ≤ (K : ℝ) * dist y x)
    {x : SourceCubeSpace n} (hx : x ∈ F) :
    upperMcShaneEnvelope K E g x = g x := by
  have hxE : x ∈ E := hFE hx
  have : Nonempty E := ⟨⟨x, hxE⟩⟩
  apply le_antisymm
  · dsimp [upperMcShaneEnvelope]
    have hnegBound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ -g y := by
      rcases hbound with ⟨M, hM⟩
      refine ⟨M, ?_⟩
      intro y hy
      linarith [hM y hy]
    have hle :
        -g x ≤ lowerMcShaneEnvelope K E (fun y => -g y) x := by
      refine le_ciInf ?_
      intro y
      have hy_le : -g x ≤ -g y + (K : ℝ) * dist x y := by
        have habs := hcross x hx y y.2
        have hright : g y - g x ≤ (K : ℝ) * dist x y := by
          have hraw : g y - g x ≤ (K : ℝ) * dist (y : SourceCubeSpace n) x :=
            (le_abs_self (g y - g x)).trans habs
          simpa [dist_comm] using hraw
        linarith
      exact hy_le
    linarith
  · simpa using
      base_le_upperMcShaneEnvelope (K := K) (E := E) (g := g) hbound (x := x) (y := x) hxE

/-- Lower-envelope increments are below the original increments at cross-estimate base points. -/
theorem lowerMcShaneEnvelope_increment_le_of_cross_bound
    {n : ℕ} {K : ℝ≥0} {E F : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    (hbound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ g y)
    (hFE : F ⊆ E)
    (hcross : ∀ x ∈ F, ∀ y ∈ E, |g y - g x| ≤ (K : ℝ) * dist y x)
    {x : SourceCubeSpace n} (hx : x ∈ F) :
    ∀ᶠ y in 𝓝[E] x,
      lowerMcShaneEnvelope K E g y - lowerMcShaneEnvelope K E g x ≤ g y - g x := by
  have hxEq : lowerMcShaneEnvelope K E g x = g x :=
    lowerMcShaneEnvelope_eq_on_of_cross_bound hbound hFE hcross hx
  filter_upwards [self_mem_nhdsWithin] with y hyE
  have hy_le :
      lowerMcShaneEnvelope K E g y ≤ g y :=
    by
      simpa using
        lowerMcShaneEnvelope_le_base (K := K) (E := E) (g := g) hbound (x := y) (y := y) hyE
  linarith

/-- Original increments are below upper-envelope increments at cross-estimate base points. -/
theorem le_upperMcShaneEnvelope_increment_of_cross_bound
    {n : ℕ} {K : ℝ≥0} {E F : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    (hbound : ∃ M : ℝ, ∀ y ∈ E, g y ≤ M)
    (hFE : F ⊆ E)
    (hcross : ∀ x ∈ F, ∀ y ∈ E, |g y - g x| ≤ (K : ℝ) * dist y x)
    {x : SourceCubeSpace n} (hx : x ∈ F) :
    ∀ᶠ y in 𝓝[E] x,
      g y - g x ≤ upperMcShaneEnvelope K E g y - upperMcShaneEnvelope K E g x := by
  have hxEq : upperMcShaneEnvelope K E g x = g x :=
    upperMcShaneEnvelope_eq_on_of_cross_bound hbound hFE hcross hx
  filter_upwards [self_mem_nhdsWithin] with y hyE
  have hy_le :
      g y ≤ upperMcShaneEnvelope K E g y :=
    by
      simpa using
        base_le_upperMcShaneEnvelope (K := K) (E := E) (g := g) hbound (x := y) (y := y) hyE
  linarith

/-- The concrete envelopes are ordered on the defining set `E`. -/
theorem lowerMcShaneEnvelope_le_upperMcShaneEnvelope_of_mem
    {n : ℕ} {K : ℝ≥0} {E : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    (hLowerBound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ g y)
    (hUpperBound : ∃ M : ℝ, ∀ y ∈ E, g y ≤ M)
    {x : SourceCubeSpace n} (hx : x ∈ E) :
    lowerMcShaneEnvelope K E g x ≤ upperMcShaneEnvelope K E g x := by
  have hle_g : lowerMcShaneEnvelope K E g x ≤ g x := by
    simpa using
      lowerMcShaneEnvelope_le_base (K := K) (E := E) (g := g) hLowerBound
        (x := x) (y := x) hx
  have hg_le : g x ≤ upperMcShaneEnvelope K E g x := by
    simpa using
      base_le_upperMcShaneEnvelope (K := K) (E := E) (g := g) hUpperBound
        (x := x) (y := x) hx
  exact hle_g.trans hg_le

/-- By continuity, the concrete envelopes are ordered on `closure E`. -/
theorem lowerMcShaneEnvelope_le_upperMcShaneEnvelope_of_mem_closure
    {n : ℕ} {K : ℝ≥0} {E : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    [Nonempty E]
    (hLowerBound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ g y)
    (hUpperBound : ∃ M : ℝ, ∀ y ∈ E, g y ≤ M)
    {x : SourceCubeSpace n} (hx : x ∈ closure E) :
    lowerMcShaneEnvelope K E g x ≤ upperMcShaneEnvelope K E g x := by
  let orderedSet : Set (SourceCubeSpace n) :=
    {x | lowerMcShaneEnvelope K E g x ≤ upperMcShaneEnvelope K E g x}
  have hclosed : IsClosed orderedSet := by
    dsimp [orderedSet]
    exact
      isClosed_le
        (lowerMcShaneEnvelope_lipschitzWith (K := K) (E := E) (g := g)
          hLowerBound).continuous
        (upperMcShaneEnvelope_lipschitzWith (K := K) (E := E) (g := g)
          hUpperBound).continuous
  have hsubset : E ⊆ orderedSet := by
    intro y hy
    exact lowerMcShaneEnvelope_le_upperMcShaneEnvelope_of_mem hLowerBound hUpperBound hy
  exact closure_minimal hsubset hclosed hx

/-- Local order of the concrete envelopes near points in an open set contained in `closure E`. -/
theorem lowerMcShaneEnvelope_eventually_le_upperMcShaneEnvelope_of_mem_open_subset_closure
    {n : ℕ} {K : ℝ≥0} {E U : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    [Nonempty E]
    (hLowerBound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ g y)
    (hUpperBound : ∃ M : ℝ, ∀ y ∈ E, g y ≤ M)
    (hUopen : IsOpen U) (hUclosure : U ⊆ closure E)
    {x : SourceCubeSpace n} (hxU : x ∈ U) :
    ∀ᶠ y in 𝓝 x, lowerMcShaneEnvelope K E g y ≤ upperMcShaneEnvelope K E g y := by
  filter_upwards [hUopen.mem_nhds hxU] with y hyU
  exact lowerMcShaneEnvelope_le_upperMcShaneEnvelope_of_mem_closure
    (K := K) (E := E) (g := g) hLowerBound hUpperBound (hUclosure hyU)

/-- If two differentiable envelopes are ordered near a point and touch at that point, then their
derivatives agree there.

This is the Fermat-theorem step in the source proof, applied to `gplus - gminus`. -/
theorem lipschitzEnvelope_touching_hasFDerivAt_eq
    {n : ℕ} {gminus gplus : SourceCubeSpace n → ℝ} {x0 : SourceCubeSpace n}
    {Lminus Lplus : SourceCubeSpace n →L[ℝ] ℝ}
    (horder : ∀ᶠ x in 𝓝 x0, gminus x ≤ gplus x)
    (htouch : gminus x0 = gplus x0)
    (hdminus : HasFDerivAt gminus Lminus x0)
    (hdplus : HasFDerivAt gplus Lplus x0) :
    Lminus = Lplus := by
  let h : SourceCubeSpace n → ℝ := fun x => gplus x - gminus x
  have hmin : IsLocalMin h x0 := by
    filter_upwards [horder] with x hx
    dsimp [h]
    linarith
  have hd : HasFDerivAt h (Lplus - Lminus) x0 := by
    change HasFDerivAt (gplus - gminus) (Lplus - Lminus) x0
    exact hdplus.sub hdminus
  have hzero : Lplus - Lminus = 0 :=
    hmin.hasFDerivAt_eq_zero hd
  exact (sub_eq_zero.mp hzero).symm

/-- Abstract squeeze step for the source proof's Lipschitz envelopes.

In the source notation, `gminus` and `gplus` are the lower and upper McShane envelopes of a
coordinate derivative `g` on the dense differentiability set `E`. If the two envelopes are
differentiable at `x0` with the same derivative `ell`, and the increments of `g` are eventually
squeezed between the envelope increments along `E`, then `g` has the same first-order expansion
along `E`.
-/
theorem lipschitzEnvelope_squeeze_expansion
    {n : ℕ} {E : Set (SourceCubeSpace n)}
    {g gminus gplus : SourceCubeSpace n → ℝ} {x0 ell : SourceCubeSpace n}
    (hlower : ∀ᶠ x in 𝓝[E] x0, gminus x - gminus x0 ≤ g x - g x0)
    (hupper : ∀ᶠ x in 𝓝[E] x0, g x - g x0 ≤ gplus x - gplus x0)
    (hdminus : HasFDerivAt gminus (InnerProductSpace.toDual ℝ (SourceCubeSpace n) ell) x0)
    (hdplus : HasFDerivAt gplus (InnerProductSpace.toDual ℝ (SourceCubeSpace n) ell) x0) :
    (fun x : SourceCubeSpace n => g x - g x0 - inner ℝ ell (x - x0))
      =o[𝓝[E] x0] fun x => ‖x - x0‖ := by
  have hminus :
      (fun x : SourceCubeSpace n => gminus x - gminus x0 - inner ℝ ell (x - x0))
        =o[𝓝[E] x0] fun x => ‖x - x0‖ := by
    simpa [InnerProductSpace.toDual_apply_apply] using
      (hdminus.hasFDerivWithinAt.isLittleO.norm_right)
  have hplus :
      (fun x : SourceCubeSpace n => gplus x - gplus x0 - inner ℝ ell (x - x0))
        =o[𝓝[E] x0] fun x => ‖x - x0‖ := by
    simpa [InnerProductSpace.toDual_apply_apply] using
      (hdplus.hasFDerivWithinAt.isLittleO.norm_right)
  refine Asymptotics.isLittleO_iff.2 ?_
  intro c hc
  filter_upwards [hminus.bound hc, hplus.bound hc, hlower, hupper] with x
    hminus_bound hplus_bound hlower_x hupper_x
  set lin : ℝ := inner ℝ ell (x - x0)
  set rg : ℝ := g x - g x0 - lin
  set rminus : ℝ := gminus x - gminus x0 - lin
  set rplus : ℝ := gplus x - gplus x0 - lin
  have hrminus_le : rminus ≤ rg := by
    dsimp [rminus, rg, lin]
    linarith
  have hrg_le : rg ≤ rplus := by
    dsimp [rplus, rg, lin]
    linarith
  have hminus_abs : |rminus| ≤ c * ‖x - x0‖ := by
    simpa [Real.norm_eq_abs, rminus, lin] using hminus_bound
  have hplus_abs : |rplus| ≤ c * ‖x - x0‖ := by
    simpa [Real.norm_eq_abs, rplus, lin] using hplus_bound
  have hleft : -(c * ‖x - x0‖) ≤ rg :=
    ((abs_le.mp hminus_abs).1).trans hrminus_le
  have hright : rg ≤ c * ‖x - x0‖ :=
    hrg_le.trans (abs_le.mp hplus_abs).2
  have hrg_abs : |rg| ≤ c * ‖x - x0‖ :=
    abs_le.mpr ⟨hleft, hright⟩
  simpa [Real.norm_eq_abs, rg, lin] using hrg_abs

/-- Packaged touching-envelope squeeze step.

This combines the Fermat-theorem derivative-agreement step with
`lipschitzEnvelope_squeeze_expansion`. It returns the row vector representing the common
derivative of the two scalar envelopes.
-/
theorem lipschitzEnvelope_touching_squeeze_expansion
    {n : ℕ} {E : Set (SourceCubeSpace n)}
    {g gminus gplus : SourceCubeSpace n → ℝ} {x0 : SourceCubeSpace n}
    {Lminus Lplus : SourceCubeSpace n →L[ℝ] ℝ}
    (horder : ∀ᶠ x in 𝓝 x0, gminus x ≤ gplus x)
    (htouch : gminus x0 = gplus x0)
    (hlower : ∀ᶠ x in 𝓝[E] x0, gminus x - gminus x0 ≤ g x - g x0)
    (hupper : ∀ᶠ x in 𝓝[E] x0, g x - g x0 ≤ gplus x - gplus x0)
    (hdminus : HasFDerivAt gminus Lminus x0)
    (hdplus : HasFDerivAt gplus Lplus x0) :
    ∃ ell : SourceCubeSpace n,
      (fun x : SourceCubeSpace n => g x - g x0 - inner ℝ ell (x - x0))
        =o[𝓝[E] x0] fun x => ‖x - x0‖ := by
  let ell : SourceCubeSpace n :=
    (InnerProductSpace.toDual ℝ (SourceCubeSpace n)).symm Lminus
  refine ⟨ell, ?_⟩
  have hL : Lminus = Lplus :=
    lipschitzEnvelope_touching_hasFDerivAt_eq horder htouch hdminus hdplus
  have hdminus' :
      HasFDerivAt gminus (InnerProductSpace.toDual ℝ (SourceCubeSpace n) ell) x0 := by
    simpa [ell] using hdminus
  have hdplus' :
      HasFDerivAt gplus (InnerProductSpace.toDual ℝ (SourceCubeSpace n) ell) x0 := by
    simpa [ell, hL.symm] using hdplus
  exact lipschitzEnvelope_squeeze_expansion hlower hupper hdminus' hdplus'

/-- A.e. envelope bridge for a fixed coordinate-gradient function.

Once the lower and upper envelopes are globally Lipschitz, Rademacher gives differentiability of
both envelopes almost everywhere. At points of the touching set `F`, the touching/squeeze lemma
then gives the first-order expansion of the squeezed function along `E`.
-/
theorem lipschitzEnvelope_ae_touching_squeeze_expansion_of_mem
    {n : ℕ} {E F : Set (SourceCubeSpace n)}
    {g gminus gplus : SourceCubeSpace n → ℝ} {Kminus Kplus : ℝ≥0}
    (hminusLip : LipschitzWith Kminus gminus)
    (hplusLip : LipschitzWith Kplus gplus)
    (horder : ∀ x : SourceCubeSpace n, gminus x ≤ gplus x)
    (htouch : ∀ x ∈ F, gminus x = gplus x)
    (hlower :
      ∀ x ∈ F, ∀ᶠ y in 𝓝[E] x, gminus y - gminus x ≤ g y - g x)
    (hupper :
      ∀ x ∈ F, ∀ᶠ y in 𝓝[E] x, g y - g x ≤ gplus y - gplus x) :
    ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), x ∈ F →
      ∃ ell : SourceCubeSpace n,
        (fun y : SourceCubeSpace n => g y - g x - inner ℝ ell (y - x))
          =o[𝓝[E] x] fun y => ‖y - x‖ := by
  have hminusAE :
      ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), DifferentiableAt ℝ gminus x :=
    hminusLip.ae_differentiableAt
  have hplusAE :
      ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), DifferentiableAt ℝ gplus x :=
    hplusLip.ae_differentiableAt
  filter_upwards [hminusAE, hplusAE] with x hminusDiff hplusDiff hxF
  exact
    lipschitzEnvelope_touching_squeeze_expansion
      (Filter.Eventually.of_forall horder) (htouch x hxF) (hlower x hxF) (hupper x hxF)
      hminusDiff.hasFDerivAt hplusDiff.hasFDerivAt

/-- A.e. envelope bridge with only local order near points of `F`.

This is the form used by the source proof: the envelopes are ordered on the working open cube,
so they are ordered in a neighborhood of each point of `F`. -/
theorem lipschitzEnvelope_ae_touching_squeeze_expansion_of_mem_localOrder
    {n : ℕ} {E F : Set (SourceCubeSpace n)}
    {g gminus gplus : SourceCubeSpace n → ℝ} {Kminus Kplus : ℝ≥0}
    (hminusLip : LipschitzWith Kminus gminus)
    (hplusLip : LipschitzWith Kplus gplus)
    (horder : ∀ x ∈ F, ∀ᶠ y in 𝓝 x, gminus y ≤ gplus y)
    (htouch : ∀ x ∈ F, gminus x = gplus x)
    (hlower :
      ∀ x ∈ F, ∀ᶠ y in 𝓝[E] x, gminus y - gminus x ≤ g y - g x)
    (hupper :
      ∀ x ∈ F, ∀ᶠ y in 𝓝[E] x, g y - g x ≤ gplus y - gplus x) :
    ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), x ∈ F →
      ∃ ell : SourceCubeSpace n,
        (fun y : SourceCubeSpace n => g y - g x - inner ℝ ell (y - x))
          =o[𝓝[E] x] fun y => ‖y - x‖ := by
  have hminusAE :
      ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), DifferentiableAt ℝ gminus x :=
    hminusLip.ae_differentiableAt
  have hplusAE :
      ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), DifferentiableAt ℝ gplus x :=
    hplusLip.ae_differentiableAt
  filter_upwards [hminusAE, hplusAE] with x hminusDiff hplusDiff hxF
  exact
    lipschitzEnvelope_touching_squeeze_expansion
      (horder x hxF) (htouch x hxF) (hlower x hxF) (hupper x hxF)
      hminusDiff.hasFDerivAt hplusDiff.hasFDerivAt

/-- Restricted-measure form of `lipschitzEnvelope_ae_touching_squeeze_expansion_of_mem`. -/
theorem lipschitzEnvelope_ae_touching_squeeze_expansion
    {n : ℕ} {E F : Set (SourceCubeSpace n)}
    {g gminus gplus : SourceCubeSpace n → ℝ} {Kminus Kplus : ℝ≥0}
    (hminusLip : LipschitzWith Kminus gminus)
    (hplusLip : LipschitzWith Kplus gplus)
    (horder : ∀ x : SourceCubeSpace n, gminus x ≤ gplus x)
    (htouch : ∀ x ∈ F, gminus x = gplus x)
    (hlower :
      ∀ x ∈ F, ∀ᶠ y in 𝓝[E] x, gminus y - gminus x ≤ g y - g x)
    (hupper :
      ∀ x ∈ F, ∀ᶠ y in 𝓝[E] x, g y - g x ≤ gplus y - gplus x)
    (hF : MeasurableSet F) :
    ∀ᵐ x ∂(volume.restrict F : Measure (SourceCubeSpace n)),
      ∃ ell : SourceCubeSpace n,
        (fun y : SourceCubeSpace n => g y - g x - inner ℝ ell (y - x))
          =o[𝓝[E] x] fun y => ‖y - x‖ := by
  have hambient :
      ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), x ∈ F →
        ∃ ell : SourceCubeSpace n,
          (fun y : SourceCubeSpace n => g y - g x - inner ℝ ell (y - x))
            =o[𝓝[E] x] fun y => ‖y - x‖ :=
    lipschitzEnvelope_ae_touching_squeeze_expansion_of_mem
      hminusLip hplusLip horder htouch hlower hupper
  filter_upwards [ae_restrict_of_ae hambient, ae_restrict_mem (μ := volume) hF] with x hx hxF
  exact hx hxF

/-- Restricted-measure local-order form of
`lipschitzEnvelope_ae_touching_squeeze_expansion_of_mem_localOrder`. -/
theorem lipschitzEnvelope_ae_touching_squeeze_expansion_localOrder
    {n : ℕ} {E F : Set (SourceCubeSpace n)}
    {g gminus gplus : SourceCubeSpace n → ℝ} {Kminus Kplus : ℝ≥0}
    (hminusLip : LipschitzWith Kminus gminus)
    (hplusLip : LipschitzWith Kplus gplus)
    (horder : ∀ x ∈ F, ∀ᶠ y in 𝓝 x, gminus y ≤ gplus y)
    (htouch : ∀ x ∈ F, gminus x = gplus x)
    (hlower :
      ∀ x ∈ F, ∀ᶠ y in 𝓝[E] x, gminus y - gminus x ≤ g y - g x)
    (hupper :
      ∀ x ∈ F, ∀ᶠ y in 𝓝[E] x, g y - g x ≤ gplus y - gplus x)
    (hF : MeasurableSet F) :
    ∀ᵐ x ∂(volume.restrict F : Measure (SourceCubeSpace n)),
      ∃ ell : SourceCubeSpace n,
        (fun y : SourceCubeSpace n => g y - g x - inner ℝ ell (y - x))
          =o[𝓝[E] x] fun y => ‖y - x‖ := by
  have hambient :
      ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), x ∈ F →
        ∃ ell : SourceCubeSpace n,
          (fun y : SourceCubeSpace n => g y - g x - inner ℝ ell (y - x))
            =o[𝓝[E] x] fun y => ‖y - x‖ :=
    lipschitzEnvelope_ae_touching_squeeze_expansion_of_mem_localOrder
      hminusLip hplusLip horder htouch hlower hupper
  filter_upwards [ae_restrict_of_ae hambient, ae_restrict_mem (μ := volume) hF] with x hx hxF
  exact hx hxF

/-- Concrete McShane-envelope a.e. squeeze wrapper.

After the source proof establishes the remaining order fact `g^- <= g^+` for the concrete
envelopes, the boundedness and cross-estimate hypotheses give all other inputs needed by the
abstract a.e. envelope bridge.
-/
theorem lowerUpperMcShaneEnvelope_ae_squeeze_of_cross_bound
    {n : ℕ} {K : ℝ≥0} {E F : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    [Nonempty E]
    (hLowerBound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ g y)
    (hUpperBound : ∃ M : ℝ, ∀ y ∈ E, g y ≤ M)
    (hFE : F ⊆ E)
    (hcross : ∀ x ∈ F, ∀ y ∈ E, |g y - g x| ≤ (K : ℝ) * dist y x)
    (horder :
      ∀ x : SourceCubeSpace n,
        lowerMcShaneEnvelope K E g x ≤ upperMcShaneEnvelope K E g x)
    (hF : MeasurableSet F) :
    ∀ᵐ x ∂(volume.restrict F : Measure (SourceCubeSpace n)),
      ∃ ell : SourceCubeSpace n,
        (fun y : SourceCubeSpace n => g y - g x - inner ℝ ell (y - x))
          =o[𝓝[E] x] fun y => ‖y - x‖ := by
  refine
    lipschitzEnvelope_ae_touching_squeeze_expansion
      (E := E) (F := F) (g := g)
      (gminus := lowerMcShaneEnvelope K E g)
      (gplus := upperMcShaneEnvelope K E g)
      (Kminus := K) (Kplus := K)
      (lowerMcShaneEnvelope_lipschitzWith (K := K) (E := E) (g := g) hLowerBound)
      (upperMcShaneEnvelope_lipschitzWith (K := K) (E := E) (g := g) hUpperBound)
      horder ?_ ?_ ?_ hF
  · intro x hx
    rw [lowerMcShaneEnvelope_eq_on_of_cross_bound hLowerBound hFE hcross hx,
      upperMcShaneEnvelope_eq_on_of_cross_bound hUpperBound hFE hcross hx]
  · intro x hx
    exact lowerMcShaneEnvelope_increment_le_of_cross_bound hLowerBound hFE hcross hx
  · intro x hx
    exact le_upperMcShaneEnvelope_increment_of_cross_bound hUpperBound hFE hcross hx

/-- Concrete McShane-envelope a.e. squeeze wrapper on an open working set.

This is the source-faithful form: if the working open set `U` lies in `closure E`, then density
and continuity provide the local order `g^- <= g^+` near every point of `F ⊆ U`. -/
theorem lowerUpperMcShaneEnvelope_ae_squeeze_of_cross_bound_on_open
    {n : ℕ} {K : ℝ≥0} {E F U : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    [Nonempty E]
    (hLowerBound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ g y)
    (hUpperBound : ∃ M : ℝ, ∀ y ∈ E, g y ≤ M)
    (hFE : F ⊆ E)
    (hFU : F ⊆ U)
    (hUopen : IsOpen U)
    (hUclosure : U ⊆ closure E)
    (hcross : ∀ x ∈ F, ∀ y ∈ E, |g y - g x| ≤ (K : ℝ) * dist y x)
    (hF : MeasurableSet F) :
    ∀ᵐ x ∂(volume.restrict F : Measure (SourceCubeSpace n)),
      ∃ ell : SourceCubeSpace n,
        (fun y : SourceCubeSpace n => g y - g x - inner ℝ ell (y - x))
          =o[𝓝[E] x] fun y => ‖y - x‖ := by
  refine
    lipschitzEnvelope_ae_touching_squeeze_expansion_localOrder
      (E := E) (F := F) (g := g)
      (gminus := lowerMcShaneEnvelope K E g)
      (gplus := upperMcShaneEnvelope K E g)
      (Kminus := K) (Kplus := K)
      (lowerMcShaneEnvelope_lipschitzWith (K := K) (E := E) (g := g) hLowerBound)
      (upperMcShaneEnvelope_lipschitzWith (K := K) (E := E) (g := g) hUpperBound)
      ?_ ?_ ?_ ?_ hF
  · intro x hx
    exact
      lowerMcShaneEnvelope_eventually_le_upperMcShaneEnvelope_of_mem_open_subset_closure
        (K := K) (E := E) (U := U) (g := g)
        hLowerBound hUpperBound hUopen hUclosure (hFU hx)
  · intro x hx
    rw [lowerMcShaneEnvelope_eq_on_of_cross_bound hLowerBound hFE hcross hx,
      upperMcShaneEnvelope_eq_on_of_cross_bound hUpperBound hFE hcross hx]
  · intro x hx
    exact lowerMcShaneEnvelope_increment_le_of_cross_bound hLowerBound hFE hcross hx
  · intro x hx
    exact le_upperMcShaneEnvelope_increment_of_cross_bound hUpperBound hFE hcross hx

/-- Ambient-measure version of
`lowerUpperMcShaneEnvelope_ae_squeeze_of_cross_bound_on_open`, avoiding a measurability
assumption on the touching set `F`. -/
theorem lowerUpperMcShaneEnvelope_ae_squeeze_of_cross_bound_on_open_of_mem
    {n : ℕ} {K : ℝ≥0} {E F U : Set (SourceCubeSpace n)} {g : SourceCubeSpace n → ℝ}
    [Nonempty E]
    (hLowerBound : ∃ M : ℝ, ∀ y ∈ E, -M ≤ g y)
    (hUpperBound : ∃ M : ℝ, ∀ y ∈ E, g y ≤ M)
    (hFE : F ⊆ E)
    (hFU : F ⊆ U)
    (hUopen : IsOpen U)
    (hUclosure : U ⊆ closure E)
    (hcross : ∀ x ∈ F, ∀ y ∈ E, |g y - g x| ≤ (K : ℝ) * dist y x) :
    ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), x ∈ F →
      ∃ ell : SourceCubeSpace n,
        (fun y : SourceCubeSpace n => g y - g x - inner ℝ ell (y - x))
          =o[𝓝[E] x] fun y => ‖y - x‖ := by
  refine
    lipschitzEnvelope_ae_touching_squeeze_expansion_of_mem_localOrder
      (E := E) (F := F) (g := g)
      (gminus := lowerMcShaneEnvelope K E g)
      (gplus := upperMcShaneEnvelope K E g)
      (Kminus := K) (Kplus := K)
      (lowerMcShaneEnvelope_lipschitzWith (K := K) (E := E) (g := g) hLowerBound)
      (upperMcShaneEnvelope_lipschitzWith (K := K) (E := E) (g := g) hUpperBound)
      ?_ ?_ ?_ ?_
  · intro x hx
    exact
      lowerMcShaneEnvelope_eventually_le_upperMcShaneEnvelope_of_mem_open_subset_closure
        (K := K) (E := E) (U := U) (g := g)
        hLowerBound hUpperBound hUopen hUclosure (hFU hx)
  · intro x hx
    rw [lowerMcShaneEnvelope_eq_on_of_cross_bound hLowerBound hFE hcross hx,
      upperMcShaneEnvelope_eq_on_of_cross_bound hUpperBound hFE hcross hx]
  · intro x hx
    exact lowerMcShaneEnvelope_increment_le_of_cross_bound hLowerBound hFE hcross hx
  · intro x hx
    exact le_upperMcShaneEnvelope_increment_of_cross_bound hUpperBound hFE hcross hx

/-- Concrete source-envelope conclusion for one coordinate of the Fréchet gradient on an
integer good set.

For almost every ambient point, membership in `Omega_m` implies that the `i`-th coordinate of
`grad u` has a first-order expansion as the variable tends to the point through the
differentiability set `D_{3/2}`. -/
theorem cubeGoodSet_nat_ae_coordinateGradient_expansion_three_halves_of_mem
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} (i : Fin n)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u) :
    ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)),
      x ∈ cubeGoodSet n u (m : ℝ) →
        ∃ ell : SourceCubeSpace n,
          (fun y : SourceCubeSpace n =>
              frechetGradient u y i - frechetGradient u x i - inner ℝ ell (y - x))
            =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
              fun y => ‖y - x‖ := by
  let E : Set (SourceCubeSpace n) := sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u
  let F : Set (SourceCubeSpace n) := cubeGoodSet n u (m : ℝ)
  let U : Set (SourceCubeSpace n) := sourceOpenCube n 1
  let K : ℝ≥0 :=
    Real.toNNReal (2 * (((m : ℝ) + 1) + sourceCubeOscillation n u))
  have hUclosure : U ⊆ closure E := by
    simpa [U, E] using
      sourceOpenCube_one_subset_closure_sourceCubeDifferentiabilitySet_three_halves_of_convex
        (n := n) (u := u) hu
  have hEnonempty : E.Nonempty := by
    have hzeroU : (0 : SourceCubeSpace n) ∈ U := by
      exact zero_mem_sourceOpenCube (n := n) (r := 1) zero_lt_one
    have hzeroClosure : (0 : SourceCubeSpace n) ∈ closure E := hUclosure hzeroU
    rw [mem_closure_iff] at hzeroClosure
    rcases hzeroClosure Set.univ isOpen_univ trivial with ⟨y, _hy_univ, hyE⟩
    exact ⟨y, hyE⟩
  rcases hEnonempty with ⟨y0, hy0E⟩
  let : Nonempty E := ⟨⟨y0, hy0E⟩⟩
  have hLower :
      ∃ M : ℝ, ∀ y ∈ E, -M ≤ (fun z : SourceCubeSpace n => frechetGradient u z i) y := by
    simpa [E] using
      sourceCubeDifferentiabilitySet_three_halves_frechetGradient_coord_bddBelow
        (n := n) (u := u) i hu hbounded
  have hUpper :
      ∃ M : ℝ, ∀ y ∈ E, (fun z : SourceCubeSpace n => frechetGradient u z i) y ≤ M := by
    simpa [E] using
      sourceCubeDifferentiabilitySet_three_halves_frechetGradient_coord_bddAbove
        (n := n) (u := u) i hu hbounded
  have hFE : F ⊆ E := by
    simpa [F, E] using
      cubeGoodSet_subset_sourceCubeDifferentiabilitySet_three_halves
        (n := n) (m := m) (u := u)
  have hFU : F ⊆ U := by
    simpa [F, U] using cubeGoodSet_subset_sourceOpenCube_one (n := n) (m := m) (u := u)
  have hcross :
      ∀ x ∈ F, ∀ y ∈ E,
        |(fun z : SourceCubeSpace n => frechetGradient u z i) y -
            (fun z : SourceCubeSpace n => frechetGradient u z i) x| ≤
          (K : ℝ) * dist y x := by
    simpa [F, E, K] using
      cubeGoodSet_nat_coordinateGradient_cross_bound_three_halves
        (n := n) (m := m) (u := u) i hu hbounded
  have hAE :=
    lowerUpperMcShaneEnvelope_ae_squeeze_of_cross_bound_on_open_of_mem
      (K := K) (E := E) (F := F) (U := U)
      (g := fun z : SourceCubeSpace n => frechetGradient u z i)
      hLower hUpper hFE hFU (by simpa [U] using isOpen_sourceOpenCube (n := n) 1)
      hUclosure hcross
  simpa [E, F] using hAE

/-- Source-envelope output assembled over all coordinates: at almost every point of an integer
good set, the Fréchet gradient has a first-order expansion along `D_{3/2}`. -/
theorem cubeGoodSet_nat_ae_frechetGradient_expansion_three_halves_of_mem
    {n m : ℕ} {u : SourceCubeSpace n → ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u) :
    ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)),
      x ∈ cubeGoodSet n u (m : ℝ) →
        ∃ B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n,
          (fun y : SourceCubeSpace n =>
              frechetGradient u y - frechetGradient u x - B (y - x))
            =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
              fun y => ‖y - x‖ := by
  have hAE :
      ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), ∀ i : Fin n,
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∃ ell : SourceCubeSpace n,
            (fun y : SourceCubeSpace n =>
                frechetGradient u y i - frechetGradient u x i - inner ℝ ell (y - x))
              =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
                fun y => ‖y - x‖ := by
    rw [ae_all_iff]
    intro i
    exact cubeGoodSet_nat_ae_coordinateGradient_expansion_three_halves_of_mem i hu hbounded
  filter_upwards [hAE] with x hx hxgood
  have hcoordExists :
      ∀ i : Fin n, ∃ ell : SourceCubeSpace n,
        (fun y : SourceCubeSpace n =>
            frechetGradient u y i - frechetGradient u x i - inner ℝ ell (y - x))
          =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
            fun y => ‖y - x‖ :=
    fun i => hx i hxgood
  choose ell hell using hcoordExists
  rcases exists_frechetGradient_isLittleO_norm_of_coordinate_isLittleO
      (u := u) (x := x) (s := sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
      (ell := ell) hell with ⟨B, _hrows, hB⟩
  exact ⟨B, hB⟩

/-- Source-route a.e. gradient expansion after choosing an integer good set.

This is the countable-good-set assembly of
`cubeGoodSet_nat_ae_frechetGradient_expansion_three_halves_of_mem`: the source cover theorem
shows that `Q_1` is covered up to a null set by the integer good sets, and the fixed-good-set
envelope theorem supplies the linearization on whichever good set contains the point. -/
theorem ae_restrict_sourceOpenCube_exists_goodSet_frechetGradient_expansion_three_halves_of_convex
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      ∃ m : ℕ,
        x ∈ cubeGoodSet n u (m : ℝ) ∧
          ∃ B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n,
            (fun y : SourceCubeSpace n =>
                frechetGradient u y - frechetGradient u x - B (y - x))
              =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
                fun y => ‖y - x‖ := by
  let G : Set (SourceCubeSpace n) := ⋃ m : ℕ, cubeGoodSet n u (m : ℝ)
  have hGnull :
      volume (sourceOpenCube n 1 \ G) = 0 := by
    simpa [G] using
      volume_sourceOpenCube_diff_iUnion_cubeGoodSet_eq_zero_of_convex
        hfiniteStatement hn hbounded hconvex
  have hGae : ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)), x ∈ G := by
    rw [ae_iff]
    rw [Measure.restrict_apply_eq_zero' (isOpen_sourceOpenCube (n := n) 1).measurableSet]
    have hset :
        {x : SourceCubeSpace n | ¬ x ∈ G} ∩ sourceOpenCube n 1 =
          sourceOpenCube n 1 \ G := by
      ext x
      simp [Set.sdiff_eq, and_comm]
    rwa [hset]
  have hAE :
      ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), ∀ m : ℕ,
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∃ B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n,
            (fun y : SourceCubeSpace n =>
                frechetGradient u y - frechetGradient u x - B (y - x))
              =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
                fun y => ‖y - x‖ := by
    rw [ae_all_iff]
    intro m
    exact cubeGoodSet_nat_ae_frechetGradient_expansion_three_halves_of_mem
      (n := n) (m := m) (u := u) hconvex hbounded
  have hAERestrict :
      ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)), ∀ m : ℕ,
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∃ B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n,
            (fun y : SourceCubeSpace n =>
                frechetGradient u y - frechetGradient u x - B (y - x))
              =o[𝓝[sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u] x]
                fun y => ‖y - x‖ :=
    ae_restrict_of_ae hAE
  filter_upwards [hGae, hAERestrict] with x hxG hxAE
  rcases Set.mem_iUnion.mp hxG with ⟨m, hxgood⟩
  exact ⟨m, hxgood, hxAE m hxgood⟩

end AleksandrovDifferentiability
