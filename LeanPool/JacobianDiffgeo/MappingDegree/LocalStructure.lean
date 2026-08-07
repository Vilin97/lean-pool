/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: mapping-degree. FiberStack: adapted charts stacked over a whole fiber.
-/
import LeanPool.JacobianDiffgeo.MappingDegree.Basics

/-!
# The stack of adapted charts over a fiber (heart, part 1)

* `RS.FiberStack F y₀` — the (finite) fiber over `y₀` enumerated as `pt : Fin n → X`,
  pairwise-disjoint adapted charts at each fiber point, and an open `V ∋ y₀` contained in every
  target-chart source, whose target-chart images lie in the normal-form balls and whose
  `F`-preimage is trapped in the chart sources. This is the multiplicity-aware local model of
  `F` over an arbitrary point of `Y` (branch value or not); Forster's 4.24-proof mechanism.
* `RS.exists_fiberStack` — existence over every `y₀ : Y` (compactness of `X` traps the fiber
  via the closed-map filter inequality `IsClosedMap.comap_nhds_le`; no sequences).
* Basic API: `mem_fiber_pt`, `maps_pt_eq`, `mem_source_pt`, `radius_pos`, `mult_ne_zero`,
  `fiber_eq_iUnion`.

`LocalConstancy.lean` combines this with the planar count (`RootCounting.lean`) to prove that
`fiberMultSum` is locally constant.
-/

open Filter Set Function
open scoped ContDiff Manifold Topology

namespace RS

section Structure

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- A stack of adapted charts over `y₀`: the (finite) fiber enumerated as `pt : Fin n → X`,
pairwise-disjoint adapted charts at each fiber point, and an open `V ∋ y₀` that is contained
in every target-chart source, whose target-chart images lie in the normal-form balls, and whose
`F`-preimage is trapped in the chart sources. -/
structure FiberStack (F : X → Y) (y₀ : Y) where
  /-- The number of points in the fiber. -/
  n : ℕ
  /-- An enumeration of the fiber. -/
  pt : Fin n → X
  pt_injective : Function.Injective pt
  range_pt : Set.range pt = F ⁻¹' {y₀}
  one_le_mult : ∀ i, 1 ≤ multiplicity F (pt i)
  /-- Adapted charts (local normal form `z ↦ z ^ k`) at each fiber point. -/
  A : ∀ i, AdaptedChartsAt F (pt i) (multiplicity F (pt i))
  disjoint_sources : Pairwise (Disjoint on fun i ↦ (A i).e.source)
  /-- The distinguished open neighborhood of `y₀`. -/
  V : Set Y
  isOpen_V : IsOpen V
  mem_V : y₀ ∈ V
  V_subset : ∀ i, V ⊆ (A i).e'.source
  map_V_mem_ball : ∀ i, ∀ y ∈ V,
    (A i).e' y ∈ Metric.ball 0 ((A i).radius ^ multiplicity F (pt i))
  preimage_V_subset : F ⁻¹' V ⊆ ⋃ i, (A i).e.source

namespace FiberStack

variable {F : X → Y} {y₀ : Y} (S : FiberStack F y₀)

theorem mem_fiber_pt (i : Fin S.n) : S.pt i ∈ F ⁻¹' {y₀} := by
  rw [← S.range_pt]; exact Set.mem_range_self i

theorem maps_pt_eq (i : Fin S.n) : F (S.pt i) = y₀ := S.mem_fiber_pt i

theorem mem_source_pt (i : Fin S.n) : S.pt i ∈ (S.A i).e.source := (S.A i).mem_source

theorem radius_pos (i : Fin S.n) : 0 < (S.A i).radius := (S.A i).radius_pos

theorem mult_ne_zero (i : Fin S.n) : multiplicity F (S.pt i) ≠ 0 :=
  Nat.one_le_iff_ne_zero.mp (S.one_le_mult i)

/-- The fiber over any `y ∈ V` decomposes along the chart sources (disjointly, by
`disjoint_sources`). -/
theorem fiber_eq_iUnion {y : Y} (hy : y ∈ S.V) :
    F ⁻¹' {y} = ⋃ i, (F ⁻¹' {y} ∩ (S.A i).e.source) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxV : x ∈ F ⁻¹' S.V := by
      have hxy : F x = y := hx
      rw [Set.mem_preimage, hxy]
      exact hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (S.preimage_V_subset hxV)
    exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
  · exact Set.iUnion_subset fun i ↦ Set.inter_subset_left

end FiberStack

end Structure

/-! ### Existence (standing surface hypotheses) -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {F : X → Y}

/-- Existence of a stack of adapted charts over every point (heart, part 1; Forster 4.24-proof
mechanism). Does NOT need `F` surjective, `Y` connected, nor the fiber nonempty (`n = 0` is
allowed). -/
theorem exists_fiberStack (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    (y₀ : Y) : Nonempty (FiberStack F y₀) := by
  have hnc : ∀ x : X, ¬ EventuallyConst F (𝓝 x) := not_eventuallyConst hF hne
  have hfin : (F ⁻¹' {y₀}).Finite := fiber_finite hF hne y₀
  -- 1. enumerate the fiber
  obtain ⟨n, pt, hrange⟩ := hfin.fin_embedding
  have hmem_fiber : ∀ i, (pt : Fin n → X) i ∈ F ⁻¹' {y₀} := fun i ↦ by
    rw [← hrange]; exact Set.mem_range_self i
  -- 2. pairwise-disjoint open neighborhoods of the fiber points
  obtain ⟨U, hU, hUdisj⟩ := hfin.t2_separation
  -- 3. adapted charts at each fiber point, shrunk into the disjoint opens
  have hex : ∀ i : Fin n, ∃ A : AdaptedChartsAt F (pt i) (multiplicity F (pt i)),
      A.e.source ⊆ U (pt i) := fun i ↦
    exists_adaptedChartsAt (hF (pt i)) (hnc (pt i))
      ((hU (pt i)).2.mem_nhds (hU (pt i)).1)
  choose A hA using hex
  have hdisj : Pairwise (Disjoint on fun i ↦ (A i).e.source) := fun i j hij ↦
    (hUdisj (hmem_fiber i) (hmem_fiber j) (pt.injective.ne hij)).mono (hA i) (hA j)
  -- 4. trap the fiber: `F` is a closed map, so a filter inequality yields `W ∋ y₀` with
  --    `F ⁻¹' W` inside the union of the chart sources
  have hW₀open : IsOpen (⋃ i, (A i).e.source) := isOpen_iUnion fun i ↦ (A i).e.open_source
  have hfiber_sub : F ⁻¹' {y₀} ⊆ ⋃ i, (A i).e.source := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Set.mem_iUnion.mpr ⟨i, (A i).mem_source⟩
  have hW₀mem : (⋃ i, (A i).e.source) ∈ 𝓝ˢ (F ⁻¹' {y₀}) :=
    hW₀open.mem_nhdsSet.mpr hfiber_sub
  obtain ⟨W, hWmem, hWsub⟩ := mem_comap.mp (hF.continuous.isClosedMap.comap_nhds_le hW₀mem)
  obtain ⟨W', hW'sub, hW'open, hyW'⟩ := mem_nhds_iff.mp hWmem
  -- 5. assemble `V`
  refine ⟨⟨n, pt, pt.injective, hrange,
    fun i ↦ one_le_multiplicity_of_not_const hF hne (pt i), A, hdisj,
    W' ∩ ⋂ i, ((A i).e'.source ∩
      (A i).e' ⁻¹' Metric.ball 0 ((A i).radius ^ multiplicity F (pt i))),
    ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- open
    apply hW'open.inter
    apply isOpen_iInter_of_finite
    intro i
    exact (A i).e'.continuousOn.isOpen_inter_preimage (A i).e'.open_source Metric.isOpen_ball
  · -- `y₀ ∈ V`
    refine ⟨hyW', Set.mem_iInter.mpr fun i ↦ ⟨?_, ?_⟩⟩
    · rw [show y₀ = F (pt i) from (hmem_fiber i : F (pt i) = y₀).symm]
      exact (A i).mem_source'
    · rw [Set.mem_preimage, show y₀ = F (pt i) from (hmem_fiber i : F (pt i) = y₀).symm,
        (A i).map_eq_zero']
      exact Metric.mem_ball_self (pow_pos (A i).radius_pos _)
  · -- `V ⊆ e'.source`
    exact fun i y hy ↦ (Set.mem_iInter.mp hy.2 i).1
  · -- images in the normal-form balls
    exact fun i y hy ↦ (Set.mem_iInter.mp hy.2 i).2
  · -- `F ⁻¹' V` trapped in the chart sources
    exact fun x hx ↦ hWsub (hW'sub hx.1)

end RS
