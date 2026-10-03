/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Source-normalized coordinate cubes

This file records the cube notation used in the source proof. The normalized theorem is first
proved on `Q 3 = (-3, 3)^n` with conclusion on `Q 1 = (-1, 1)^n`.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Topology

/-- The source-proof coordinate space `R^n`, with its Euclidean inner-product structure. -/
abbrev SourceCubeSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The translated open coordinate cube `Q_r(c) = c + (-r, r)^n`. -/
def sourceOpenCubeAt {n : ℕ} (c : SourceCubeSpace n) (r : ℝ) : Set (SourceCubeSpace n) :=
  {x | ∀ i : Fin n, |x i - c i| < r}

/-- The centered open coordinate cube `Q_r = (-r, r)^n`. -/
def sourceOpenCube (n : ℕ) (r : ℝ) : Set (SourceCubeSpace n) :=
  sourceOpenCubeAt (0 : SourceCubeSpace n) r

/-- The centered closed coordinate cube `[-r, r]^n`. It is mainly used as the compact set
between `Q_1` and `Q_3` in the source-local differentiability-a.e. argument. -/
def sourceClosedCube (n : ℕ) (r : ℝ) : Set (SourceCubeSpace n) :=
  {x | ∀ i : Fin n, |x i| ≤ r}

/-- The oscillation of a real-valued function on a set, written in the source as
`osc_s u`. Later estimates carry boundedness and nonemptiness hypotheses when they need the
usual order properties of `sSup` and `sInf`. -/
def oscOn {E : Type*} (u : E → ℝ) (s : Set E) : ℝ :=
  sSup (u '' s) - sInf (u '' s)

/-- `u` is bounded on `s` in the bornological sense. -/
def BoundedOn {E : Type*} (s : Set E) (u : E → ℝ) : Prop :=
  Bornology.IsBounded (u '' s)

/-- Boundedness on a larger set restricts to boundedness on a subset. -/
theorem BoundedOn.mono {E : Type*} {s t : Set E} {u : E → ℝ}
    (h : BoundedOn t u) (hst : s ⊆ t) :
    BoundedOn s u :=
  h.subset (by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hst hx, rfl⟩)

/-- A continuous real-valued function on a compact set is bounded in the project `BoundedOn`
sense. -/
theorem BoundedOn.of_isCompact_of_continuousOn {E : Type*} [TopologicalSpace E]
     {s : Set E} {u : E → ℝ}
    (hs : IsCompact s) (hu : ContinuousOn u s) :
    BoundedOn s u :=
  (hs.image_of_continuousOn hu).isBounded

/-- The `i`-th Euclidean coordinate vector in the source cube model. -/
def sourceCoordinateVector {n : ℕ} (i : Fin n) : SourceCubeSpace n :=
  EuclideanSpace.basisFun (Fin n) ℝ i

/-- The base point of the coordinate line through `x` parallel to the `i`-th axis, obtained by
zeroing the `i`-th coordinate. -/
def coordinateLineBase {n : ℕ} (i : Fin n) (x : SourceCubeSpace n) : SourceCubeSpace n :=
  x - x i • sourceCoordinateVector i

/-- The point `y + s e_i` on the coordinate line through `y` parallel to the `i`-th axis. -/
def coordinateLinePoint {n : ℕ} (i : Fin n) (y : SourceCubeSpace n) (s : ℝ) :
    SourceCubeSpace n :=
  y + s • sourceCoordinateVector i

/-- The transverse coordinate space to the `i`-th source-coordinate direction. -/
abbrev SourceTransverseSpace {n : ℕ} (i : Fin n) :=
  EuclideanSpace ℝ {j : Fin n // j ≠ i}

/-- The open transverse cube in the coordinate hyperplane perpendicular to `e_i`. -/
def sourceTransverseOpenCube {n : ℕ} (i : Fin n) (r : ℝ) :
    Set (SourceTransverseSpace i) :=
  {a | ∀ j : {j : Fin n // j ≠ i}, |a j| < r}

/-- Embed transverse coordinates into the source cube by inserting zero in coordinate `i`. -/
def sourceTransverseEmbed {n : ℕ} (i : Fin n) (a : SourceTransverseSpace i) :
    SourceCubeSpace n :=
  WithLp.toLp 2 (fun j => if h : j = i then 0 else a ⟨j, h⟩)

/-- Product-coordinate chart for the `i`-th coordinate line: transverse base plus vertical
coordinate. -/
def sourceCoordinateChartPoint {n : ℕ} (i : Fin n) (a : SourceTransverseSpace i) (s : ℝ) :
    SourceCubeSpace n :=
  sourceTransverseEmbed i a + s • sourceCoordinateVector i

/-- Product-coordinate chart map for the `i`-th source-coordinate direction. -/
def sourceCoordinateChartMap {n : ℕ} (i : Fin n) :
    SourceTransverseSpace i × ℝ → SourceCubeSpace n :=
  fun p => sourceCoordinateChartPoint i p.1 p.2

@[simp]
theorem mem_sourceOpenCubeAt {n : ℕ} {c x : SourceCubeSpace n} {r : ℝ} :
    x ∈ sourceOpenCubeAt c r ↔ ∀ i : Fin n, |x i - c i| < r :=
  Iff.rfl

@[simp]
theorem mem_sourceOpenCube {n : ℕ} {x : SourceCubeSpace n} {r : ℝ} :
    x ∈ sourceOpenCube n r ↔ ∀ i : Fin n, |x i| < r := by
  simp [sourceOpenCube, sourceOpenCubeAt]

@[simp]
theorem mem_sourceClosedCube {n : ℕ} {x : SourceCubeSpace n} {r : ℝ} :
    x ∈ sourceClosedCube n r ↔ ∀ i : Fin n, |x i| ≤ r :=
  Iff.rfl

theorem sourceOpenCubeAt_subset_of_le {n : ℕ} {c : SourceCubeSpace n} {r R : ℝ}
    (hrR : r ≤ R) :
    sourceOpenCubeAt c r ⊆ sourceOpenCubeAt c R := by
  intro x hx i
  exact lt_of_lt_of_le (hx i) hrR

theorem sourceOpenCube_subset_of_le {n : ℕ} {r R : ℝ} (hrR : r ≤ R) :
    sourceOpenCube n r ⊆ sourceOpenCube n R :=
  sourceOpenCubeAt_subset_of_le hrR

theorem sourceOpenCube_one_subset_three {n : ℕ} :
    sourceOpenCube n 1 ⊆ sourceOpenCube n 3 :=
  sourceOpenCube_subset_of_le (by norm_num)

theorem sourceOpenCube_subset_sourceClosedCube_of_le {n : ℕ} {r R : ℝ} (hrR : r ≤ R) :
    sourceOpenCube n r ⊆ sourceClosedCube n R := by
  intro x hx i
  exact le_trans (le_of_lt (by simpa using hx i)) hrR

theorem sourceOpenCube_one_subset_sourceClosedCube_one {n : ℕ} :
    sourceOpenCube n 1 ⊆ sourceClosedCube n 1 :=
  sourceOpenCube_subset_sourceClosedCube_of_le le_rfl

theorem sourceClosedCube_subset_sourceOpenCube_of_lt {n : ℕ} {r R : ℝ} (hrR : r < R) :
    sourceClosedCube n r ⊆ sourceOpenCube n R := by
  intro x hx i
  simpa using lt_of_le_of_lt (hx i) hrR

theorem sourceClosedCube_one_subset_sourceOpenCube_three {n : ℕ} :
    sourceClosedCube n 1 ⊆ sourceOpenCube n 3 :=
  sourceClosedCube_subset_sourceOpenCube_of_lt (by norm_num)

theorem center_mem_sourceOpenCubeAt {n : ℕ} {c : SourceCubeSpace n} {r : ℝ} (hr : 0 < r) :
    c ∈ sourceOpenCubeAt c r := by
  intro i
  simpa using hr

theorem zero_mem_sourceOpenCube {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (0 : SourceCubeSpace n) ∈ sourceOpenCube n r :=
  center_mem_sourceOpenCubeAt hr

theorem sourceOpenCubeAt_eq_iInter {n : ℕ} (c : SourceCubeSpace n) (r : ℝ) :
    sourceOpenCubeAt c r = ⋂ i : Fin n, {x : SourceCubeSpace n | |x i - c i| < r} := by
  ext x
  simp [sourceOpenCubeAt]

theorem sourceClosedCube_eq_iInter {n : ℕ} (r : ℝ) :
    sourceClosedCube n r = ⋂ i : Fin n, {x : SourceCubeSpace n | |x i| ≤ r} := by
  ext x
  simp [sourceClosedCube]

theorem sourceTransverseOpenCube_eq_iInter {n : ℕ} (i : Fin n) (r : ℝ) :
    sourceTransverseOpenCube i r =
      ⋂ j : {j : Fin n // j ≠ i}, {a : SourceTransverseSpace i | |a j| < r} := by
  ext a
  simp [sourceTransverseOpenCube]

theorem isOpen_sourceOpenCubeAt {n : ℕ} (c : SourceCubeSpace n) (r : ℝ) :
    IsOpen (sourceOpenCubeAt c r) := by
  rw [sourceOpenCubeAt_eq_iInter]
  refine isOpen_iInter_of_finite fun i => ?_
  exact isOpen_lt
    (_root_.continuous_abs.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.sub continuous_const))
    continuous_const

theorem isOpen_sourceOpenCube {n : ℕ} (r : ℝ) :
    IsOpen (sourceOpenCube n r) :=
  isOpen_sourceOpenCubeAt (0 : SourceCubeSpace n) r

/-- Source open cubes are convex. -/
theorem convex_sourceOpenCubeAt {n : ℕ} (c : SourceCubeSpace n) (r : ℝ) :
    Convex ℝ (sourceOpenCubeAt c r) := by
  rw [sourceOpenCubeAt_eq_iInter]
  refine convex_iInter fun i => ?_
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hcoord :
      (a • x + b • y) i - c i =
        a * (x i - c i) + b * (y i - c i) := by
    have hc : c i = a * c i + b * c i := by
      calc
        c i = (a + b) * c i := by rw [hab]; ring
        _ = a * c i + b * c i := by ring
    calc
      (a • x + b • y) i - c i = a * x i + b * y i - c i := by simp
      _ = a * x i + b * y i - (a * c i + b * c i) := by
        nth_rewrite 1 [hc]
        rfl
      _ = a * (x i - c i) + b * (y i - c i) := by ring
  rw [hcoord]
  calc
    |a * (x i - c i) + b * (y i - c i)|
        ≤ |a * (x i - c i)| + |b * (y i - c i)| := abs_add_le _ _
    _ = a * |x i - c i| + b * |y i - c i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ < r := by
        by_cases ha_pos : 0 < a
        · have hx_lt : a * |x i - c i| < a * r :=
            mul_lt_mul_of_pos_left hx ha_pos
          have hy_le : b * |y i - c i| ≤ b * r :=
            mul_le_mul_of_nonneg_left (le_of_lt hy) hb
          have hsum_mul : a * r + b * r = r := by
            calc
              a * r + b * r = (a + b) * r := by ring
              _ = r := by rw [hab]; ring
          nlinarith
        · have ha_eq : a = 0 := le_antisymm (le_of_not_gt ha_pos) ha
          have hb_eq : b = 1 := by nlinarith
          simpa [ha_eq, hb_eq] using hy

/-- Centered source open cubes are convex. -/
theorem convex_sourceOpenCube {n : ℕ} (r : ℝ) :
    Convex ℝ (sourceOpenCube n r) :=
  convex_sourceOpenCubeAt (0 : SourceCubeSpace n) r

theorem isOpen_sourceTransverseOpenCube {n : ℕ} (i : Fin n) (r : ℝ) :
    IsOpen (sourceTransverseOpenCube i r) := by
  rw [sourceTransverseOpenCube_eq_iInter]
  refine isOpen_iInter_of_finite fun j => ?_
  exact isOpen_lt
    (_root_.continuous_abs.comp (EuclideanSpace.proj (𝕜 := ℝ) j).continuous)
    continuous_const

theorem continuous_sourceTransverseEmbed {n : ℕ} (i : Fin n) :
    Continuous (sourceTransverseEmbed i) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp ?_
  rw [continuous_pi_iff]
  intro j
  by_cases hji : j = i
  · subst hji
    simpa using continuous_const
  · let k : {j : Fin n // j ≠ i} := ⟨j, hji⟩
    simpa [hji, k] using (EuclideanSpace.proj (𝕜 := ℝ) k).continuous

theorem continuous_sourceCoordinateChartMap {n : ℕ} (i : Fin n) :
    Continuous (sourceCoordinateChartMap i) := by
  unfold sourceCoordinateChartMap sourceCoordinateChartPoint
  exact ((continuous_sourceTransverseEmbed i).comp continuous_fst).add
    (continuous_snd.smul continuous_const)

/-- The coordinate-line base projection `x ↦ x - x_i e_i` is continuous. -/
theorem continuous_coordinateLineBase {n : ℕ} (i : Fin n) :
    Continuous (coordinateLineBase i) := by
  unfold coordinateLineBase
  exact continuous_id.sub ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.smul continuous_const)

theorem isClosed_sourceClosedCube {n : ℕ} (r : ℝ) :
    IsClosed (sourceClosedCube n r) := by
  rw [sourceClosedCube_eq_iInter]
  refine isClosed_iInter fun i => ?_
  exact isClosed_le
    (_root_.continuous_abs.comp (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)
    continuous_const

theorem isBounded_sourceClosedCube {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    Bornology.IsBounded (sourceClosedCube n r) := by
  refine (Metric.isBounded_iff_subset_closedBall (0 : SourceCubeSpace n)).2
    ⟨Real.sqrt (n : ℝ) * r, ?_⟩
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm_sq_le : ‖x‖ ^ 2 ≤ (Real.sqrt (n : ℝ) * r) ^ 2 := by
    calc
      ‖x‖ ^ 2 = ∑ i : Fin n, x i ^ 2 := by
        exact EuclideanSpace.real_norm_sq_eq x
      _ ≤ ∑ _i : Fin n, r ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hr] using hx i)
      _ = (n : ℝ) * r ^ 2 := by simp
      _ = (Real.sqrt (n : ℝ) * r) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hright_nonneg : 0 ≤ Real.sqrt (n : ℝ) * r :=
    mul_nonneg (Real.sqrt_nonneg _) hr
  have habs := sq_le_sq.mp hnorm_sq_le
  simpa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg hright_nonneg] using habs

/-- Explicit Euclidean norm bound for points in the source open cube. -/
theorem norm_le_sqrt_card_mul_of_mem_sourceOpenCube {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r) {x : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n r) :
    ‖x‖ ≤ Real.sqrt (n : ℝ) * r := by
  have hnorm_sq_le : ‖x‖ ^ 2 ≤ (Real.sqrt (n : ℝ) * r) ^ 2 := by
    calc
      ‖x‖ ^ 2 = ∑ i : Fin n, x i ^ 2 := by
        exact EuclideanSpace.real_norm_sq_eq x
      _ ≤ ∑ _i : Fin n, r ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hr] using le_of_lt (hx i))
      _ = (n : ℝ) * r ^ 2 := by simp
      _ = (Real.sqrt (n : ℝ) * r) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hright_nonneg : 0 ≤ Real.sqrt (n : ℝ) * r :=
    mul_nonneg (Real.sqrt_nonneg _) hr
  have habs := sq_le_sq.mp hnorm_sq_le
  simpa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg hright_nonneg] using habs

/-- The transverse open coordinate cube is bounded. -/
theorem isBounded_sourceTransverseOpenCube {n : ℕ} (i : Fin n) {r : ℝ} (hr : 0 ≤ r) :
    Bornology.IsBounded (sourceTransverseOpenCube i r) := by
  refine (Metric.isBounded_iff_subset_closedBall (0 : SourceTransverseSpace i)).2
    ⟨Real.sqrt (Fintype.card {j : Fin n // j ≠ i} : ℝ) * r, ?_⟩
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm_sq_le :
      ‖a‖ ^ 2 ≤ (Real.sqrt (Fintype.card {j : Fin n // j ≠ i} : ℝ) * r) ^ 2 := by
    calc
      ‖a‖ ^ 2 = ∑ j : {j : Fin n // j ≠ i}, a j ^ 2 := by
        exact EuclideanSpace.real_norm_sq_eq a
      _ ≤ ∑ _j : {j : Fin n // j ≠ i}, r ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hr] using le_of_lt (ha j))
      _ = (Fintype.card {j : Fin n // j ≠ i} : ℝ) * r ^ 2 := by simp
      _ = (Real.sqrt (Fintype.card {j : Fin n // j ≠ i} : ℝ) * r) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hright_nonneg :
      0 ≤ Real.sqrt (Fintype.card {j : Fin n // j ≠ i} : ℝ) * r :=
    mul_nonneg (Real.sqrt_nonneg _) hr
  have habs := sq_le_sq.mp hnorm_sq_le
  simpa [abs_of_nonneg (norm_nonneg a), abs_of_nonneg hright_nonneg,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hr] using habs

theorem isCompact_sourceClosedCube {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    IsCompact (sourceClosedCube n r) :=
  Metric.isCompact_iff_isClosed_bounded.2
    ⟨isClosed_sourceClosedCube r, isBounded_sourceClosedCube hr⟩

/-- Continuity on the closed cube gives the boundedness hypothesis needed by the normalized
source-cube theorem on the corresponding open cube. -/
theorem BoundedOn.sourceOpenCube_of_continuousOn_sourceClosedCube {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hcont : ContinuousOn u (sourceClosedCube n r)) :
    BoundedOn (sourceOpenCube n r) u :=
  (BoundedOn.of_isCompact_of_continuousOn (isCompact_sourceClosedCube hr) hcont).mono
    (sourceOpenCube_subset_sourceClosedCube_of_le le_rfl)

/-- Since source cubes are open, inclusion in a larger source cube also gives inclusion in its
interior. -/
theorem sourceOpenCube_subset_interior_of_le {n : ℕ} {r R : ℝ} (hrR : r ≤ R) :
    sourceOpenCube n r ⊆ interior (sourceOpenCube n R) := by
  intro x hx
  simpa [(isOpen_sourceOpenCube (n := n) R).interior_eq] using
    sourceOpenCube_subset_of_le hrR hx

theorem sourceOpenCube_one_subset_interior_three {n : ℕ} :
    sourceOpenCube n 1 ⊆ interior (sourceOpenCube n 3) :=
  sourceOpenCube_subset_interior_of_le (by norm_num)

@[simp]
theorem sourceCoordinateVector_apply_self {n : ℕ} (i : Fin n) :
    sourceCoordinateVector i i = 1 := by
  simp [sourceCoordinateVector]

theorem sourceCoordinateVector_apply_ne {n : ℕ} {i j : Fin n} (hji : j ≠ i) :
    sourceCoordinateVector i j = 0 := by
  simp [sourceCoordinateVector, hji]

@[simp]
theorem norm_sourceCoordinateVector {n : ℕ} (i : Fin n) :
    ‖sourceCoordinateVector i‖ = 1 := by
  have hsq : ‖sourceCoordinateVector i‖ ^ 2 = (1 : ℝ) := by
    rw [← real_inner_self_eq_norm_sq]
    simp [sourceCoordinateVector]
  have hnonneg : 0 ≤ ‖sourceCoordinateVector i‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖sourceCoordinateVector i‖ + 1)]

/-- A positive-dimensional source cube space contains a unit vector. -/
theorem exists_unit_sourceCubeSpace_of_pos {n : ℕ} (hn : 0 < n) :
    ∃ v : SourceCubeSpace n, ‖v‖ = 1 := by
  exact ⟨sourceCoordinateVector ⟨0, hn⟩, norm_sourceCoordinateVector ⟨0, hn⟩⟩

@[simp]
theorem coordinateLineBase_apply_self {n : ℕ} (i : Fin n) (x : SourceCubeSpace n) :
    coordinateLineBase i x i = 0 := by
  simp [coordinateLineBase, sourceCoordinateVector]

theorem coordinateLineBase_apply_ne {n : ℕ} {i j : Fin n} (hji : j ≠ i)
    (x : SourceCubeSpace n) :
    coordinateLineBase i x j = x j := by
  simp [coordinateLineBase, sourceCoordinateVector, hji]

@[simp]
theorem coordinateLinePoint_apply_self {n : ℕ} (i : Fin n) (y : SourceCubeSpace n) (s : ℝ) :
    coordinateLinePoint i y s i = y i + s := by
  simp [coordinateLinePoint, sourceCoordinateVector]

theorem coordinateLinePoint_apply_ne {n : ℕ} {i j : Fin n} (hji : j ≠ i)
    (y : SourceCubeSpace n) (s : ℝ) :
    coordinateLinePoint i y s j = y j := by
  simp [coordinateLinePoint, sourceCoordinateVector, hji]

@[simp]
theorem mem_sourceTransverseOpenCube {n : ℕ} {i : Fin n} {a : SourceTransverseSpace i}
    {r : ℝ} :
    a ∈ sourceTransverseOpenCube i r ↔ ∀ j : {j : Fin n // j ≠ i}, |a j| < r :=
  Iff.rfl

@[simp]
theorem sourceTransverseEmbed_apply_self {n : ℕ} (i : Fin n) (a : SourceTransverseSpace i) :
    sourceTransverseEmbed i a i = 0 := by
  simp [sourceTransverseEmbed]

theorem sourceTransverseEmbed_apply_ne {n : ℕ} {i j : Fin n} (hji : j ≠ i)
    (a : SourceTransverseSpace i) :
    sourceTransverseEmbed i a j = a ⟨j, hji⟩ := by
  simp [sourceTransverseEmbed, hji]

@[simp]
theorem sourceCoordinateChartPoint_apply_self {n : ℕ} (i : Fin n)
    (a : SourceTransverseSpace i) (s : ℝ) :
    sourceCoordinateChartPoint i a s i = s := by
  simp [sourceCoordinateChartPoint]

theorem sourceCoordinateChartPoint_apply_ne {n : ℕ} {i j : Fin n} (hji : j ≠ i)
    (a : SourceTransverseSpace i) (s : ℝ) :
    sourceCoordinateChartPoint i a s j = a ⟨j, hji⟩ := by
  simp [sourceCoordinateChartPoint, sourceTransverseEmbed_apply_ne hji,
    sourceCoordinateVector_apply_ne hji]

/-- The coordinate chart as a linear map from the L2 product model. The ordinary product chart
`sourceCoordinateChartMap` is obtained by precomposing this map with `WithLp.toLp 2`. -/
def sourceCoordinateChartLinearMap {n : ℕ} (i : Fin n) :
    WithLp 2 (SourceTransverseSpace i × ℝ) →ₗ[ℝ] SourceCubeSpace n where
  toFun p := sourceCoordinateChartPoint i p.ofLp.1 p.ofLp.2
  map_add' p q := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp [sourceCoordinateChartPoint]
    · simp [sourceCoordinateChartPoint_apply_ne hji]
  map_smul' c p := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp [sourceCoordinateChartPoint]
    · simp [sourceCoordinateChartPoint_apply_ne hji]

/-- The inverse linear map to `sourceCoordinateChartLinearMap`, recording the transverse
coordinates and the distinguished coordinate. -/
def sourceCoordinateChartInverseLinearMap {n : ℕ} (i : Fin n) :
    SourceCubeSpace n →ₗ[ℝ] WithLp 2 (SourceTransverseSpace i × ℝ) where
  toFun x := WithLp.toLp 2 (WithLp.toLp 2 (fun j : {j : Fin n // j ≠ i} => x j), x i)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    ext j <;> simp
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    ext j <;> simp

theorem sourceCoordinateChartLinearMap_comp_inverse {n : ℕ} (i : Fin n) :
    (sourceCoordinateChartLinearMap i).comp (sourceCoordinateChartInverseLinearMap i) =
      LinearMap.id := by
  ext x j
  by_cases hji : j = i
  · subst hji
    simp [sourceCoordinateChartLinearMap, sourceCoordinateChartInverseLinearMap,
      sourceCoordinateChartPoint]
  · simp [sourceCoordinateChartLinearMap, sourceCoordinateChartInverseLinearMap,
      sourceCoordinateChartPoint_apply_ne hji]

theorem sourceCoordinateChartInverseLinearMap_comp {n : ℕ} (i : Fin n) :
    (sourceCoordinateChartInverseLinearMap i).comp (sourceCoordinateChartLinearMap i) =
      LinearMap.id := by
  ext p
  change WithLp.toLp 2
      (WithLp.toLp 2
        (fun j : {j : Fin n // j ≠ i} =>
          sourceCoordinateChartPoint i p.ofLp.1 p.ofLp.2 j),
        sourceCoordinateChartPoint i p.ofLp.1 p.ofLp.2 i) = p
  rw [← WithLp.toLp_ofLp (p := 2) p]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · ext j
    simp [sourceCoordinateChartPoint_apply_ne j.2]
  · simp

theorem sourceCoordinateChartLinearMap_norm {n : ℕ} (i : Fin n)
    (p : WithLp 2 (SourceTransverseSpace i × ℝ)) :
    ‖sourceCoordinateChartLinearMap i p‖ = ‖p‖ := by
  have : Subsingleton {j : Fin n // ¬ j ≠ i} := by
    refine ⟨fun a b => ?_⟩
    apply Subtype.ext
    exact (by_contra fun h => a.property h).trans (by_contra fun h => b.property h).symm
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.real_norm_sq_eq, WithLp.prod_norm_sq_eq_of_L2,
    EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ j : Fin n, (sourceCoordinateChartLinearMap i p).ofLp j ^ 2 =
        (∑ j : {j : Fin n // j ≠ i},
          (sourceCoordinateChartLinearMap i p).ofLp j ^ 2) +
          ∑ j : {j : Fin n // ¬ j ≠ i},
            (sourceCoordinateChartLinearMap i p).ofLp j ^ 2 := by
      rw [Fintype.sum_subtype_add_sum_subtype (fun j : Fin n => j ≠ i)
        (fun j : Fin n => (sourceCoordinateChartLinearMap i p).ofLp j ^ 2)]
    _ = (∑ j : {j : Fin n // j ≠ i}, p.ofLp.1.ofLp j ^ 2) + p.ofLp.2 ^ 2 := by
      congr 1
      · apply Finset.sum_congr rfl
        intro j _hj
        simp [sourceCoordinateChartLinearMap, sourceCoordinateChartPoint_apply_ne j.2]
      · rw [Fintype.sum_subsingleton
          (fun j : {j : Fin n // ¬ j ≠ i} =>
            (sourceCoordinateChartLinearMap i p).ofLp j ^ 2)
          ⟨i, by simp⟩]
        simp [sourceCoordinateChartLinearMap, sourceCoordinateChartPoint]
    _ = ∑ j : {j : Fin n // j ≠ i}, p.ofLp.1.ofLp j ^ 2 + ‖p.ofLp.2‖ ^ 2 := by
      simp [pow_two, Real.norm_eq_abs]

/-- The coordinate chart is a linear isometry equivalence from the L2 product model to the source
cube. -/
def sourceCoordinateChartLinearIsometryEquiv {n : ℕ} (i : Fin n) :
    WithLp 2 (SourceTransverseSpace i × ℝ) ≃ₗᵢ[ℝ] SourceCubeSpace n where
  toLinearEquiv := LinearEquiv.ofLinearMap
    (sourceCoordinateChartLinearMap i)
    (sourceCoordinateChartInverseLinearMap i)
    (sourceCoordinateChartLinearMap_comp_inverse i)
    (sourceCoordinateChartInverseLinearMap_comp i)
  norm_map' := sourceCoordinateChartLinearMap_norm i

@[simp]
theorem coordinateLineBase_sourceTransverseEmbed {n : ℕ} (i : Fin n)
    (a : SourceTransverseSpace i) :
    coordinateLineBase i (sourceTransverseEmbed i a) = sourceTransverseEmbed i a := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [coordinateLineBase_apply_ne hji]

@[simp]
theorem coordinateLineBase_sourceCoordinateChartPoint {n : ℕ} (i : Fin n)
    (a : SourceTransverseSpace i) (s : ℝ) :
    coordinateLineBase i (sourceCoordinateChartPoint i a s) = sourceTransverseEmbed i a := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [sourceCoordinateChartPoint_apply_ne hji, coordinateLineBase_apply_ne hji,
      sourceTransverseEmbed_apply_ne hji]

@[simp]
theorem sourceCoordinateChartPoint_base_self {n : ℕ} (i : Fin n)
    (a : SourceTransverseSpace i) (s : ℝ) :
    coordinateLinePoint i (sourceTransverseEmbed i a) s =
      sourceCoordinateChartPoint i a s := by
  rfl

theorem sourceTransverseEmbed_mem_sourceOpenCube {n : ℕ} {i : Fin n}
    {a : SourceTransverseSpace i} {r : ℝ}
    (hr : 0 < r) (ha : a ∈ sourceTransverseOpenCube i r) :
    sourceTransverseEmbed i a ∈ sourceOpenCube n r := by
  intro j
  by_cases hji : j = i
  · subst hji
    simpa using hr
  · simpa [sourceTransverseEmbed_apply_ne hji] using ha ⟨j, hji⟩

theorem sourceCoordinateChartPoint_mem_sourceOpenCube {n : ℕ} {i : Fin n}
    {a : SourceTransverseSpace i} {s r : ℝ}
    (ha : a ∈ sourceTransverseOpenCube i r) (hs : |s| < r) :
    sourceCoordinateChartPoint i a s ∈ sourceOpenCube n r := by
  intro j
  by_cases hji : j = i
  · subst hji
    simpa using hs
  · simpa [sourceCoordinateChartPoint_apply_ne hji] using ha ⟨j, hji⟩

theorem sourceCoordinateChartPoint_mem_sourceOpenCube_iff {n : ℕ} {i : Fin n}
    {a : SourceTransverseSpace i} {s r : ℝ} :
    sourceCoordinateChartPoint i a s ∈ sourceOpenCube n r ↔
      a ∈ sourceTransverseOpenCube i r ∧ |s| < r := by
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro j
      simpa [sourceCoordinateChartPoint_apply_ne j.2] using hx j
    · simpa using hx i
  · rintro ⟨ha, hs⟩
    exact sourceCoordinateChartPoint_mem_sourceOpenCube ha hs

@[simp]
theorem coordinateLinePoint_base_self {n : ℕ} (i : Fin n) (x : SourceCubeSpace n) :
    coordinateLinePoint i (coordinateLineBase i x) (x i) = x := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [coordinateLinePoint_apply_ne hji, coordinateLineBase_apply_ne hji]

@[simp]
theorem coordinateLinePoint_base_add {n : ℕ} (i : Fin n) (x : SourceCubeSpace n) (h : ℝ) :
    coordinateLinePoint i (coordinateLineBase i x) (x i + h) =
      x + h • sourceCoordinateVector i := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [coordinateLinePoint_apply_ne hji, coordinateLineBase_apply_ne hji,
      sourceCoordinateVector_apply_ne hji]

@[simp]
theorem coordinateLinePoint_base_sub {n : ℕ} (i : Fin n) (x : SourceCubeSpace n) (h : ℝ) :
    coordinateLinePoint i (coordinateLineBase i x) (x i - h) =
      x - h • sourceCoordinateVector i := by
  simp [sub_eq_add_neg]

theorem coordinateLineBase_mem_sourceOpenCube {n : ℕ} {i : Fin n} {x : SourceCubeSpace n}
    {r : ℝ} (hr : 0 < r) (hx : x ∈ sourceOpenCube n r) :
    coordinateLineBase i x ∈ sourceOpenCube n r := by
  intro j
  by_cases hji : j = i
  · subst hji
    simpa using hr
  · simpa [coordinateLineBase_apply_ne hji] using hx j

theorem coordinateLineBase_mem_sourceOpenCube_one {n : ℕ} {i : Fin n}
    {x : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) :
    coordinateLineBase i x ∈ sourceOpenCube n 1 :=
  coordinateLineBase_mem_sourceOpenCube (by norm_num) hx

@[simp]
theorem coordinateLineBase_idem {n : ℕ} (i : Fin n) (x : SourceCubeSpace n) :
    coordinateLineBase i (coordinateLineBase i x) = coordinateLineBase i x := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [coordinateLineBase_apply_ne hji]

/-- Each source-coordinate of a vector is bounded by its Euclidean norm. -/
theorem abs_sourceCoordinate_le_norm {n : ℕ} (z : SourceCubeSpace n) (i : Fin n) :
    |z i| ≤ ‖z‖ := by
  have hinner : |inner ℝ (sourceCoordinateVector i) z| ≤
      ‖sourceCoordinateVector i‖ * ‖z‖ := by
    simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (sourceCoordinateVector i) z
  have hcoord : inner ℝ (sourceCoordinateVector i) z = z i := by
    simpa [sourceCoordinateVector] using
      (EuclideanSpace.basisFun_inner (𝕜 := ℝ) (ι := Fin n) z i)
  rw [hcoord] at hinner
  simpa [sourceCoordinateVector] using hinner

/-- A displacement of Euclidean norm at most `1` from `Q_1` stays inside `Q_3`. -/
theorem sourceOpenCube_one_add_norm_le_one_mem_three {n : ℕ}
    {x z : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) (hz : ‖z‖ ≤ 1) :
    x + z ∈ sourceOpenCube n 3 := by
  intro i
  have htri : |x i + z i| ≤ |x i| + |z i| := abs_add_le (x i) (z i)
  have hx_i : |x i| < 1 := by simpa using hx i
  have hz_i : |z i| ≤ 1 := (abs_sourceCoordinate_le_norm z i).trans hz
  have hlt : |x i + z i| < 3 := by linarith
  simpa using hlt

/-- A displacement of Euclidean norm at most `1 / 2` from `Q_1` stays inside `Q_{3/2}`. -/
theorem sourceOpenCube_one_add_norm_le_half_mem_three_halves {n : ℕ}
    {x z : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    x + z ∈ sourceOpenCube n (3 / 2 : ℝ) := by
  intro i
  have htri : |x i + z i| ≤ |x i| + |z i| := abs_add_le (x i) (z i)
  have hx_i : |x i| < 1 := by simpa using hx i
  have hz_i : |z i| ≤ (1 / 2 : ℝ) := (abs_sourceCoordinate_le_norm z i).trans hz
  have hlt : |x i + z i| < (3 / 2 : ℝ) := by linarith
  simpa using hlt

/-- Small line segments from `Q_1` stay inside `Q_{3/2}`. -/
theorem sourceOpenCube_one_add_smul_norm_le_half_mem_three_halves {n : ℕ}
    {x z : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) (hz : ‖z‖ ≤ (1 / 2 : ℝ))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • z ∈ sourceOpenCube n (3 / 2 : ℝ) := by
  have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have htz : ‖t • z‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖t • z‖ = |t| * ‖z‖ := norm_smul t z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht_abs (norm_nonneg z)
      _ ≤ 1 * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hz (by norm_num)
      _ = (1 / 2 : ℝ) := by norm_num
  exact sourceOpenCube_one_add_norm_le_half_mem_three_halves hx htz

/-- Eventually, every short segment based at a point of `Q_1` lies inside `Q_{3/2}`. -/
theorem eventually_sourceOpenCube_one_add_smul_mem_three_halves {n : ℕ}
    {x : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) :
    ∀ᶠ z in 𝓝 (0 : SourceCubeSpace n),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        x + t • z ∈ sourceOpenCube n (3 / 2 : ℝ) := by
  filter_upwards [Metric.closedBall_mem_nhds (0 : SourceCubeSpace n) (by norm_num :
      (0 : ℝ) < 1 / 2)] with z hz t ht
  have hz_norm : ‖z‖ ≤ (1 / 2 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  exact sourceOpenCube_one_add_smul_norm_le_half_mem_three_halves hx hz_norm ht

/-- A displacement of Euclidean norm at most `2` from `Q_1` stays inside `Q_3`. -/
theorem sourceOpenCube_one_add_norm_le_two_mem_three {n : ℕ}
    {x z : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) (hz : ‖z‖ ≤ 2) :
    x + z ∈ sourceOpenCube n 3 := by
  intro i
  have htri : |x i + z i| ≤ |x i| + |z i| := abs_add_le (x i) (z i)
  have hx_i : |x i| < 1 := by simpa using hx i
  have hz_i : |z i| ≤ 2 := (abs_sourceCoordinate_le_norm z i).trans hz
  have hlt : |x i + z i| < 3 := by linarith
  simpa using hlt

/-- A displacement of Euclidean norm at most `3 / 2` from `Q_{3/2}` stays inside `Q_3`. -/
theorem sourceOpenCube_three_halves_add_norm_le_three_halves_mem_three {n : ℕ}
    {x z : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n (3 / 2 : ℝ))
    (hz : ‖z‖ ≤ (3 / 2 : ℝ)) :
    x + z ∈ sourceOpenCube n 3 := by
  intro i
  have htri : |x i + z i| ≤ |x i| + |z i| := abs_add_le (x i) (z i)
  have hx_i : |x i| < (3 / 2 : ℝ) := by simpa using hx i
  have hz_i : |z i| ≤ (3 / 2 : ℝ) := (abs_sourceCoordinate_le_norm z i).trans hz
  have hlt : |x i + z i| < 3 := by linarith
  simpa using hlt

/-- A displacement of Euclidean norm at most `1` from `Q_1` stays inside `Q_3`. -/
theorem sourceOpenCube_one_sub_norm_le_one_mem_three {n : ℕ}
    {x z : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) (hz : ‖z‖ ≤ 1) :
    x - z ∈ sourceOpenCube n 3 := by
  simpa [sub_eq_add_neg] using
    sourceOpenCube_one_add_norm_le_one_mem_three hx (z := -z) (by simpa using hz)

/-- A one-coordinate displacement of size less than `2` from `Q_1` stays inside `Q_3`.
This is the source-proof domain check for the endpoints `x + h e_i`. -/
theorem sourceOpenCube_one_add_coordinate_mem_three {n : ℕ} {i : Fin n}
    {x : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) {h : ℝ} (hh : |h| < 2) :
    x + h • sourceCoordinateVector i ∈ sourceOpenCube n 3 := by
  intro j
  by_cases hji : j = i
  · subst j
    have htri : |x i + h| ≤ |x i| + |h| := abs_add_le (x i) h
    have hx_i : |x i| < 1 := by simpa using hx i
    have hlt : |x i + h| < 3 := by linarith
    simpa [sourceCoordinateVector] using hlt
  · simpa [sourceCoordinateVector_apply_ne hji] using
      lt_trans (hx j) (by norm_num : (1 : ℝ) < 3)

/-- A one-coordinate displacement of size less than `2` from `Q_1` stays inside `Q_3`.
This is the source-proof domain check for the endpoints `x - h e_i`. -/
theorem sourceOpenCube_one_sub_coordinate_mem_three {n : ℕ} {i : Fin n}
    {x : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) {h : ℝ} (hh : |h| < 2) :
    x - h • sourceCoordinateVector i ∈ sourceOpenCube n 3 := by
  simpa [sub_eq_add_neg] using
    sourceOpenCube_one_add_coordinate_mem_three (i := i) hx (h := -h) (by simpa using hh)

end AleksandrovDifferentiability
