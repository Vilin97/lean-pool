/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact

/-!
# Gluing a vanishing approximation across an open frontier

Moise Chapter 8 replaces a chart-transition map on an open, locally finite subcomplex.  The
replacement is controlled by a tolerance which tends to zero at the frontier, so it fits
continuously with the unchanged map outside the open set.  This file isolates that analytic
argument from the later complex bookkeeping.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open Filter
open scoped Topology

/-- A positive control on `U` is strongly positive when it has a positive lower bound on every
compact subset of `U`.  This is Moise's notation `phi >> 0`, stated without continuity. -/
def StronglyPositiveOn {X : Type*} [TopologicalSpace X]
    (U : Set X) (phi : X → ℝ) : Prop :=
  ∀ C : Set X, IsCompact C → C ⊆ U →
    ∃ eps : ℝ, 0 < eps ∧ ∀ x ∈ C, eps ≤ phi x

/-- Distance to the complement, the canonical frontier-vanishing control on an open set. -/
noncomputable def frontierDistance {X : Type*} [PseudoMetricSpace X]
    (U : Set X) (x : X) : ℝ :=
  Metric.infDist x Uᶜ

theorem frontierDistance_pos {X : Type*} [PseudoMetricSpace X]
    {U : Set X} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) {x : X} (hx : x ∈ U) :
    0 < frontierDistance U x := by
  apply (hU.isClosed_compl.notMem_iff_infDist_pos hUc).mp
  simpa

/-- Distance to the complement is strongly positive on the open set. -/
theorem stronglyPositiveOn_frontierDistance {X : Type*} [PseudoMetricSpace X]
    {U : Set X} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    StronglyPositiveOn U (frontierDistance U) := by
  intro C hC hCU
  by_cases hCempty : C = ∅
  · exact ⟨1, by norm_num, by simp [hCempty]⟩
  · have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hCempty
    obtain ⟨x, hxC, hxMin⟩ := hC.exists_isMinOn hCne
      (Metric.continuous_infDist_pt Uᶜ).continuousOn
    refine ⟨frontierDistance U x, frontierDistance_pos hU hUc (hCU hxC), ?_⟩
    intro y hyC
    exact hxMin hyC

/-- The control tends to zero when points of `U` approach its frontier. -/
def VanishesAtFrontier {X : Type*} [TopologicalSpace X]
    (U : Set X) (phi : X → ℝ) : Prop :=
  ∀ x ∈ frontier U, Tendsto phi (nhdsWithin x U) (nhds 0)

/-- Distance to the complement tends to zero along the open set at every frontier point. -/
theorem vanishesAtFrontier_frontierDistance {X : Type*} [PseudoMetricSpace X]
    {U : Set X} (hU : IsOpen U) : VanishesAtFrontier U (frontierDistance U) := by
  intro x hx
  have hxnot : x ∉ U := by
    rw [frontier, hU.interior_eq] at hx
    exact hx.2
  have hxzero : frontierDistance U x = 0 :=
    Metric.infDist_zero_of_mem (Set.mem_compl hxnot)
  rw [← hxzero]
  exact ((Metric.continuous_infDist_pt Uᶜ).tendsto x).mono_left inf_le_left

/-! ## Compact exhaustion of a proper open set -/

/-- The `n`-th compact core of an open set, cut out by distance to its complement. -/
noncomputable def frontierCore {X : Type*} [PseudoMetricSpace X]
    (U : Set X) (n : ℕ) : Set X :=
  {x | 1 / (n + 1 : ℝ) ≤ frontierDistance U x}

theorem isCompact_frontierCore {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (U : Set X) (n : ℕ) : IsCompact (frontierCore U n) := by
  apply IsClosed.isCompact
  exact isClosed_Ici.preimage (Metric.continuous_infDist_pt Uᶜ)

theorem frontierCore_subset {X : Type*} [PseudoMetricSpace X]
    {U : Set X} (_ : Uᶜ.Nonempty) (n : ℕ) : frontierCore U n ⊆ U := by
  intro x hx
  by_contra hxU
  have hzero : frontierDistance U x = 0 :=
    Metric.infDist_zero_of_mem (Set.mem_compl hxU)
  rw [frontierCore, Set.mem_setOf_eq, hzero] at hx
  have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
  linarith

theorem iUnion_frontierCore {X : Type*} [PseudoMetricSpace X]
    {U : Set X} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    (⋃ n : ℕ, frontierCore U n) = U := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact frontierCore_subset hUc n hn
  · intro x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (frontierDistance_pos hU hUc hx)
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩

theorem frontierCore_subset_interior_succ {X : Type*} [PseudoMetricSpace X]
    (U : Set X) (n : ℕ) :
    frontierCore U n ⊆ interior (frontierCore U (n + 1)) := by
  let V : Set X := {x | 1 / (n + 2 : ℝ) < frontierDistance U x}
  have hVopen : IsOpen V :=
    isOpen_Ioi.preimage (Metric.continuous_infDist_pt Uᶜ)
  have hVsub : V ⊆ frontierCore U (n + 1) := by
    intro x hx
    change 1 / (n + 2 : ℝ) < frontierDistance U x at hx
    simp only [frontierCore, Set.mem_setOf_eq]
    have hden : (((n + 1 : ℕ) : ℝ) + 1) = n + 2 := by
      push_cast
      ring
    rw [hden]
    exact hx.le
  have hVint : V ⊆ interior (frontierCore U (n + 1)) :=
    interior_maximal hVsub hVopen
  intro x hx
  apply hVint
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hlt : 1 / (n + 2 : ℝ) < 1 / (n + 1 : ℝ) := by
    apply one_div_lt_one_div_of_lt hden
    norm_num
  exact hlt.trans_le hx

/-- Replace `h` by `g` on `U`. -/
noncomputable def frontierGlue {X Y : Type*} (U : Set X) (g h : X → Y) : X → Y := by
  classical
  exact U.piecewise g h

@[simp] theorem frontierGlue_of_mem {X Y : Type*} {U : Set X} {g h : X → Y}
    {x : X} (hx : x ∈ U) : frontierGlue U g h x = g x := by
  classical
  simp [frontierGlue, hx]

@[simp] theorem frontierGlue_of_notMem {X Y : Type*} {U : Set X} {g h : X → Y}
    {x : X} (hx : x ∉ U) : frontierGlue U g h x = h x := by
  classical
  simp [frontierGlue, hx]

/-- A replacement agrees asymptotically with the old map at the frontier of its open domain.
This is the topology-only form of Moise's condition `phi(P) → 0`. -/
def MatchesAtFrontier {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (U : Set X) (g h : X → Y) : Prop :=
  ∀ x ∈ frontier U, Tendsto g (nhdsWithin x U) (nhds (h x))

/-- A frontier-matching replacement on an open set glues continuously to the unchanged map.
Unlike `continuous_frontierGlue`, this form does not require a metric on the target. -/
theorem continuous_frontierGlue_of_matches {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} (hU : IsOpen U) {g h : X → Y}
    (hg : ContinuousOn g U) (hh : Continuous h)
    (hmatch : MatchesAtFrontier U g h) :
    Continuous (frontierGlue U g h) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxU : x ∈ U
  · have heq : frontierGlue U g h =ᶠ[nhds x] g := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact frontierGlue_of_mem hy
    exact (hg.continuousAt (hU.mem_nhds hxU)).congr_of_eventuallyEq heq
  · by_cases hxClosure : x ∈ closure U
    · have hxFrontier : x ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hxClosure, hxU⟩
      rw [ContinuousAt]
      intro V hV
      rw [frontierGlue_of_notMem hxU] at hV
      have hgV : g ⁻¹' V ∈ nhdsWithin x U := hmatch x hxFrontier hV
      obtain ⟨W, hW, hWsub⟩ :=
        mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hgV
      have hhV : h ⁻¹' V ∈ nhds x := hh.continuousAt hV
      apply Filter.mem_of_superset (inter_mem hW hhV)
      intro y hy
      by_cases hyU : y ∈ U
      · rw [Set.mem_preimage, frontierGlue_of_mem hyU]
        exact hWsub ⟨hy.1, hyU⟩
      · rw [Set.mem_preimage, frontierGlue_of_notMem hyU]
        exact hy.2
    · have houtside : Uᶜ ∈ nhds x := by
        exact Filter.mem_of_superset
          ((isOpen_compl_iff.mpr isClosed_closure).mem_nhds hxClosure)
          (Set.compl_subset_compl.mpr subset_closure)
      have heq : frontierGlue U g h =ᶠ[nhds x] h := by
        filter_upwards [houtside] with y hy
        exact frontierGlue_of_notMem hy
      exact hh.continuousAt.congr_of_eventuallyEq heq

/-- A replacement on an open set glues continuously to the old map when its error tends to zero
at the frontier.  No local finiteness or PL data enters this lemma. -/
theorem continuous_frontierGlue {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {U : Set X} (hU : IsOpen U) {g h : X → Y}
    (hg : ContinuousOn g U) (hh : Continuous h) {phi : X → ℝ}
    (hphi : VanishesAtFrontier U phi)
    (hclose : ∀ x ∈ U, dist (g x) (h x) ≤ |phi x|) :
    Continuous (frontierGlue U g h) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxU : x ∈ U
  · have heq : frontierGlue U g h =ᶠ[nhds x] g := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact frontierGlue_of_mem hy
    exact (hg.continuousAt (hU.mem_nhds hxU)).congr_of_eventuallyEq heq
  · by_cases hxClosure : x ∈ closure U
    · have hxFrontier : x ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hxClosure, hxU⟩
      rw [Metric.continuousAt_iff']
      intro eps heps
      have heps2 : 0 < eps / 2 := half_pos heps
      have hhsmall : ∀ᶠ y in nhds x, dist (h y) (h x) < eps / 2 :=
        (Metric.continuousAt_iff'.mp hh.continuousAt) (eps / 2) heps2
      have hphismallWithin : {y | dist (phi y) 0 < eps / 2} ∈ nhdsWithin x U :=
        (Metric.tendsto_nhds.mp (hphi x hxFrontier)) (eps / 2) heps2
      obtain ⟨V, hV, hVU⟩ :=
        mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hphismallWithin
      filter_upwards [hV, hhsmall] with y hyV hyh
      rw [frontierGlue_of_notMem hxU]
      by_cases hyU : y ∈ U
      · rw [frontierGlue_of_mem hyU]
        have hphiSmall : |phi y| < eps / 2 := by
          have := hVU ⟨hyV, hyU⟩
          simpa [Real.dist_eq] using this
        calc
          dist (g y) (h x) ≤ dist (g y) (h y) + dist (h y) (h x) :=
            dist_triangle _ _ _
          _ < eps / 2 + eps / 2 :=
            add_lt_add (lt_of_le_of_lt (hclose y hyU) hphiSmall) hyh
          _ = eps := by ring
      · rw [frontierGlue_of_notMem hyU]
        exact hyh.trans (half_lt_self heps)
    · have houtside : Uᶜ ∈ nhds x := by
        exact Filter.mem_of_superset
          ((isOpen_compl_iff.mpr isClosed_closure).mem_nhds hxClosure)
          (Set.compl_subset_compl.mpr subset_closure)
      have heq : frontierGlue U g h =ᶠ[nhds x] h := by
        filter_upwards [houtside] with y hy
        exact frontierGlue_of_notMem hy
      exact hh.continuousAt.congr_of_eventuallyEq heq

/-- Metric closeness controlled by a frontier-vanishing function supplies the topology-only
matching condition.  This is the bridge from the quantitative Chapter 6 approximation to the
metric-free paste in the ambient surface. -/
theorem matchesAtFrontier_of_vanishing_close {X Y : Type*}
    [TopologicalSpace X] [PseudoMetricSpace Y]
    {U : Set X} (hU : IsOpen U) {g h : X → Y}
    (hg : ContinuousOn g U) (hh : Continuous h) {phi : X → ℝ}
    (hphi : VanishesAtFrontier U phi)
    (hclose : ∀ x ∈ U, dist (g x) (h x) ≤ |phi x|) :
    MatchesAtFrontier U g h := by
  have hglue := continuous_frontierGlue hU hg hh hphi hclose
  intro x hx
  have hxU : x ∉ U := by
    rw [frontier, hU.interior_eq] at hx
    exact hx.2
  have ht : Tendsto (frontierGlue U g h) (nhdsWithin x U)
      (nhds (frontierGlue U g h x)) :=
    hglue.continuousAt.mono_left inf_le_left
  rw [frontierGlue_of_notMem hxU] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact frontierGlue_of_mem hy

/-- The range of a frontier glue is exactly the union of the replacement image and the
unchanged image.  This set-level formula is the one used in Moise Chapter 8 when the modified
old complex is united with the finite chart complex. -/
theorem range_frontierGlue {X Y : Type*} {U : Set X} {g h : X → Y} :
    Set.range (frontierGlue U g h) = g '' U ∪ h '' Uᶜ := by
  classical
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    by_cases hx : x ∈ U
    · exact Set.mem_union_left _ ⟨x, hx, (frontierGlue_of_mem hx).symm⟩
    · exact Set.mem_union_right _ ⟨x, hx, (frontierGlue_of_notMem hx).symm⟩
  · rintro y (hy | hy)
    · obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, frontierGlue_of_mem hx⟩
    · obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, frontierGlue_of_notMem hx⟩

/-- A replacement which is injective on the open set and misses the unchanged outside image
glues to a globally injective map.  No compactness or continuity is needed for this part. -/
theorem injective_frontierGlue {X Y : Type*} {U : Set X} {g h : X → Y}
    (hg : Set.InjOn g U) (hh : Function.Injective h)
    (hcross : Disjoint (g '' U) (h '' Uᶜ)) :
    Function.Injective (frontierGlue U g h) := by
  classical
  intro x y hxy
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ U
    · apply hg hx hy
      simpa only [frontierGlue_of_mem hx, frontierGlue_of_mem hy] using hxy
    · have hgx : g x ∈ g '' U := ⟨x, hx, rfl⟩
      have hhy : h y ∈ h '' Uᶜ := ⟨y, hy, rfl⟩
      have : g x = h y := by
        simpa only [frontierGlue_of_mem hx, frontierGlue_of_notMem hy] using hxy
      exact False.elim (Set.disjoint_left.mp hcross hgx (this ▸ hhy))
  · by_cases hy : y ∈ U
    · have hgy : g y ∈ g '' U := ⟨y, hy, rfl⟩
      have hhx : h x ∈ h '' Uᶜ := ⟨x, hx, rfl⟩
      have : h x = g y := by
        simpa only [frontierGlue_of_notMem hx, frontierGlue_of_mem hy] using hxy
      exact False.elim (Set.disjoint_left.mp hcross hgy (this.symm ▸ hhx))
    · apply hh
      simpa only [frontierGlue_of_notMem hx, frontierGlue_of_notMem hy] using hxy

/-- On a compact source, the continuous injective frontier glue is a topological embedding.
This packages the exact analytic conclusion used for Moise's modified map `f'_n`. -/
theorem isEmbedding_frontierGlue {X Y : Type*} [TopologicalSpace X]
    [CompactSpace X] [PseudoMetricSpace Y] [T2Space Y]
    {U : Set X} (hU : IsOpen U)
    {g h : X → Y} (hgcont : ContinuousOn g U) (hhcont : Continuous h)
    {phi : X → ℝ} (hphi : VanishesAtFrontier U phi)
    (hclose : ∀ x ∈ U, dist (g x) (h x) ≤ |phi x|)
    (hginj : Set.InjOn g U) (hhinj : Function.Injective h)
    (hcross : Disjoint (g '' U) (h '' Uᶜ)) :
    _root_.Topology.IsEmbedding (frontierGlue U g h) := by
  have hcontinuous := continuous_frontierGlue hU hgcont hhcont hphi hclose
  exact (hcontinuous.isClosedEmbedding
    (injective_frontierGlue hginj hhinj hcross)).isEmbedding

/-- Compact-to-Hausdorff embedding form of the topology-only frontier glue. -/
theorem isEmbedding_frontierGlue_of_matches {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    {U : Set X} (hU : IsOpen U) {g h : X → Y}
    (hgcont : ContinuousOn g U) (hhcont : Continuous h)
    (hmatch : MatchesAtFrontier U g h)
    (hginj : Set.InjOn g U) (hhinj : Function.Injective h)
    (hcross : Disjoint (g '' U) (h '' Uᶜ)) :
    _root_.Topology.IsEmbedding (frontierGlue U g h) := by
  have hcontinuous := continuous_frontierGlue_of_matches hU hgcont hhcont hmatch
  exact (hcontinuous.isClosedEmbedding
    (injective_frontierGlue hginj hhinj hcross)).isEmbedding

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
