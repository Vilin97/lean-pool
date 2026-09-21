/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Faces
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Polytope
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Finite convex hulls in convex position

This file bridges the operational notion of convex position used in the
proof of Theorem 1.12 with mathlib's `ConvexIndependent`, and constructs the
rational polytope whose vertices are exactly a given rational family in
convex position.
-/

open scoped BigOperators

namespace EGZ

/-- The paper's finite-family notion of convex position, in the operational
form needed by Definition 3.7. -/
def IsInConvexPosition {d n : ℕ} (points : Fin n → RealCoord d) : Prop :=
  ∀ (i : Fin n) (weight : Fin n → ℝ),
    (∀ j, 0 ≤ weight j) →
    (∑ j, weight j) = 1 →
    points i = ∑ j, weight j • points j →
    ∃ j, weight j = 1

namespace IsInConvexPosition

/-- For an injective family, the operational definition of convex position
implies mathlib's set-theoretic convex independence. -/
theorem convexIndependent {d n : ℕ} {points : Fin n → RealCoord d}
    (hpos : IsInConvexPosition points) (hinjective : Function.Injective points) :
    ConvexIndependent ℝ points := by
  rw [convexIndependent_iff_finset]
  intro s i hi
  classical
  let : DecidableEq (RealCoord d) := Classical.decEq _
  rw [Finset.mem_convexHull'] at hi
  obtain ⟨w, hw0, hwsum, hwbar⟩ := hi
  let weight : Fin n → ℝ := fun j ↦ if j ∈ s then w (points j) else 0
  have hweight0 : ∀ j, 0 ≤ weight j := by
    intro j
    by_cases hj : j ∈ s
    · simp only [weight, hj, ite_eq_left]
      exact hw0 (points j) (Finset.mem_image_of_mem points hj)
    · simp [weight, hj]
  have hweightsum : (∑ j, weight j) = 1 := by
    rw [show (∑ j, weight j) = ∑ j ∈ s, w (points j) by
      simp [weight]]
    exact (Finset.sum_image (f := w) (g := points)
      (fun a _ b _ hab ↦ hinjective hab)).symm.trans hwsum
  have hwbar' : points i = ∑ j, weight j • points j := by
    rw [show (∑ j, weight j • points j) =
        ∑ j ∈ s, w (points j) • points j by simp [weight]]
    calc
      points i = ∑ y ∈ s.image points, w y • y := hwbar.symm
      _ = ∑ j ∈ s, w (points j) • points j :=
        Finset.sum_image (f := fun y ↦ w y • y) (g := points)
          (fun a _ b _ hab ↦ hinjective hab)
  obtain ⟨j, hj⟩ := hpos i weight hweight0 hweightsum hwbar'
  have hjs : j ∈ s := by
    by_contra hnot
    simp [weight, hnot] at hj
  have hsum_erase : ∑ k ∈ (Finset.univ.erase j), weight k = 0 := by
    have hdecomp := Finset.sum_erase_add (s := Finset.univ) (f := weight)
      (Finset.mem_univ j)
    rw [hweightsum, hj] at hdecomp
    linarith
  have hzero : ∀ k, k ≠ j → weight k = 0 := by
    intro k hkj
    have hk : k ∈ Finset.univ.erase j := by simp [hkj]
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ ↦ hweight0 x)).mp hsum_erase k hk
  have hbarj : (∑ k, weight k • points k) = points j := by
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro k _ hkj
      simp [hzero k hkj]
    · simp
  have hij : i = j := hinjective (hwbar'.trans hbarj)
  simpa [hij] using hjs

/-- An injective family in operational convex position is exactly the vertex
set of its convex hull. -/
theorem extremePoints_convexHull_range {d n : ℕ}
    {points : Fin n → RealCoord d} (hpos : IsInConvexPosition points)
    (hinjective : Function.Injective points) :
    (convexHull ℝ (Set.range points)).extremePoints ℝ = Set.range points := by
  classical
  apply Set.Subset.antisymm extremePoints_convexHull_subset
  rintro _ ⟨i, rfl⟩
  have hc : ConvexIndependent ℝ points := hpos.convexIndependent hinjective
  let T : Set (RealCoord d) := Set.range points \ {points i}
  have hnot : points i ∉ convexHull ℝ T := by
    intro hi
    let U : Set (Fin n) := {j | j ≠ i}
    have heq : points '' U = T := by
      ext y
      constructor
      · rintro ⟨j, hj, rfl⟩
        refine ⟨Set.mem_range_self j, ?_⟩
        simpa [U] using fun h ↦ hj (hinjective h)
      · rintro ⟨⟨j, rfl⟩, hj⟩
        refine ⟨j, ?_, rfl⟩
        simpa [U] using fun h ↦ hj (congrArg points h)
    have hii : i ∈ U := hc U i (by simpa [heq] using hi)
    exact hii rfl
  have hTfinite : T.Finite := (Set.finite_range points).sdiff
  obtain ⟨f, u, hfT, huf⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ T) (hTfinite.isClosed_convexHull ℝ) hnot
  let generators : Finset (RealCoord d) := Finset.univ.image points
  have hgenerators : (generators : Set (RealCoord d)) = Set.range points := by
    ext y
    simp [generators]
  let functional : RealCoord d →ᵃ[ℝ] ℝ := f.toLinearMap.toAffineMap
  have hle_gen : ∀ y ∈ generators,
      functional y ≤ functional (points i) := by
    intro y hy
    by_cases hyi : y = points i
    · simp [hyi]
    · have hyT : y ∈ T := by
        refine ⟨?_, by simpa using hyi⟩
        rw [← hgenerators]
        exact hy
      exact (hfT y (subset_convexHull ℝ T hyT)).le.trans huf.le
  have hlevel_gen :
      generators.filter (fun y ↦
        functional y = functional (points i)) = {points i} := by
    ext y
    constructor
    · intro hy
      obtain ⟨hygenerators, hyeq⟩ := Finset.mem_filter.mp hy
      by_contra hyi
      have hyT : y ∈ T := by
        refine ⟨?_, by simpa using hyi⟩
        rw [← hgenerators]
        exact hygenerators
      have hylt := (hfT y (subset_convexHull ℝ T hyT)).trans huf
      exact (ne_of_lt hylt) hyeq
    · intro hy
      have hyi : y = points i := Finset.mem_singleton.mp hy
      subst y
      apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      simp [generators]
  have hlevel :
      {y | y ∈ convexHull ℝ (generators : Set (RealCoord d)) ∧
          functional y = functional (points i)} = {points i} := by
    rw [RationalPolytope.convexHull_supportingLevel_eq generators functional
      (functional (points i)) hle_gen, hlevel_gen]
    simp
  apply exposedPoints_subset_extremePoints
  refine ⟨subset_convexHull ℝ _ (Set.mem_range_self i), f, ?_⟩
  intro y hy
  have hy' : y ∈ convexHull ℝ (generators : Set (RealCoord d)) := by
    simpa [hgenerators] using hy
  have hyle : f y ≤ f (points i) :=
    convexHull_min hle_gen
      (convex_halfSpace_le f.toLinearMap.isLinear (f (points i))) hy'
  refine ⟨hyle, fun hrev ↦ ?_⟩
  have hmem : y ∈
      {z | z ∈ convexHull ℝ (generators : Set (RealCoord d)) ∧
        functional z = functional (points i)} :=
    ⟨hy', le_antisymm hyle hrev⟩
  rw [hlevel] at hmem
  exact Set.mem_singleton_iff.mp hmem

end IsInConvexPosition

/-- A relative-interior point can be extended past any distinct point of the
set.  Equivalently, it is a strict convex combination of that point and a
second point of the set.  This elementary form is particularly convenient
when positive coefficients on a prescribed finite support must be retained. -/
theorem exists_openSegment_of_mem_intrinsicInterior {d : ℕ}
    {C : Set (RealCoord d)} {q x : RealCoord d}
    (hq : q ∈ intrinsicInterior ℝ C) (hx : x ∈ C) (hqx : q ≠ x) :
    ∃ z ∈ C, q ∈ openSegment ℝ x z := by
  rw [mem_intrinsicInterior] at hq
  obtain ⟨qA, hqAint, rfl⟩ := hq
  let : Nonempty (affineSpan ℝ C) := ⟨qA⟩
  let xA : affineSpan ℝ C := ⟨x, subset_affineSpan ℝ C hx⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hqAint
  obtain ⟨ε, hε, hball⟩ := hqAint
  let v : (affineSpan ℝ C).direction := qA -ᵥ xA
  let t : ℝ := ε / (2 * (‖v‖ + 1))
  have ht : 0 < t := by
    dsimp [t]
    positivity
  let zA : affineSpan ℝ C := t • v +ᵥ qA
  have hzball : zA ∈ Metric.ball qA ε := by
    rw [Metric.mem_ball, show dist zA qA = ‖t • v‖ by
      exact dist_vadd_left (V := (affineSpan ℝ C).direction) (t • v) qA]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    calc
      t * ‖v‖ < t * (‖v‖ + 1) :=
        mul_lt_mul_of_pos_left (lt_add_one _) ht
      _ = ε / 2 := by
        dsimp [t]
        field_simp
      _ < ε := by linarith
  have hzpre : zA ∈ ((↑) ⁻¹' C : Set (affineSpan ℝ C)) := hball hzball
  let z : RealCoord d := zA
  refine ⟨z, hzpre, ?_⟩
  refine ⟨t / (1 + t), 1 / (1 + t), ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · field_simp
    ring
  · funext j
    have hzj : z j = t * ((qA : RealCoord d) j - x j) +
        (qA : RealCoord d) j := by
      rfl
    change (t / (1 + t)) * x j + (1 / (1 + t)) * z j =
      (qA : RealCoord d) j
    rw [hzj]
    field_simp
    ring

/-- A finite convex hull together with the vertex identification needed in
the hollow-polytope branch. -/
structure FiniteHullModel {d n : ℕ} (points : Fin n → RealCoord d) where
  polytope : RationalPolytope d
  carrier_eq : polytope.carrier = convexHull ℝ (Set.range points)
  vertexSet_eq : polytope.vertexSet = Set.range points

/-- The finite hull of a nonempty rational family in convex position, with
its vertex set identified exactly. -/
noncomputable def finiteHullModel {d n : ℕ}
    (points : Fin n → RealCoord d) (hn : 0 < n)
    (hinjective : Function.Injective points)
    (hrational : ∀ i, IsRational (points i))
    (hpos : IsInConvexPosition points) : FiniteHullModel points := by
  let S : Set (RealCoord d) := Set.range points
  have hSfinite : S.Finite := Set.finite_range points
  have hSnonempty : S.Nonempty :=
    ⟨points ⟨0, hn⟩, Set.mem_range_self _⟩
  have hSrational : ∀ q ∈ S, IsRational q := by
    rintro _ ⟨i, rfl⟩
    exact hrational i
  let Q := RationalPolytope.ofFiniteConvexHull S hSfinite hSnonempty hSrational
  have hQcarrier : Q.carrier = convexHull ℝ S :=
    RationalPolytope.ofFiniteConvexHull_carrier S hSfinite hSnonempty hSrational
  refine { polytope := Q, carrier_eq := ?_, vertexSet_eq := ?_ }
  · simpa [S] using hQcarrier
  · rw [RationalPolytope.vertexSet, hQcarrier]
    simpa [S] using hpos.extremePoints_convexHull_range hinjective

end EGZ
