/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Rectifiability.Continuum
public import LeanPool.Besicovitch.Statement
public import Mathlib.Analysis.Convex.Hull
import LeanPool.Besicovitch.Topology.ConnectedComponent
import LeanPool.Besicovitch.Rectifiability.HoleMerging
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Analysis.Convex.Caratheodory

/-!
# Surgery on continua

This file develops the continuum-surgery argument for countably many open convex holes.
-/

@[expose] public section

noncomputable section

open Bornology MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

namespace LeanPool.Besicovitch

/-- A nonempty compact set in a metric space contains two points realizing its extended diameter. -/
theorem _root_.IsCompact.exists_edist_eq_ediam {X : Type*} [MetricSpace X] {C : Set X}
    (hC : IsCompact C) (hCne : C.Nonempty) :
    ∃ x ∈ C, ∃ y ∈ C, edist x y = Metric.ediam C := by
  obtain ⟨p, hpC, hpmax⟩ := (hC.prod hC).exists_isMaxOn (hCne.prod hCne)
    continuous_dist.continuousOn
  have hdist : dist p.1 p.2 = Metric.diam C := by
    apply le_antisymm (Metric.dist_le_diam_of_mem hC.isBounded hpC.1 hpC.2)
    apply Metric.diam_le_of_forall_dist_le dist_nonneg
    intro x hx y hy
    exact @hpmax (x, y) ⟨hx, hy⟩
  exact ⟨p.1, hpC.1, p.2, hpC.2, by
    rw [edist_dist, hdist, Metric.diam,
      ENNReal.ofReal_toReal hC.isBounded.ediam_ne_top]⟩

/-- The two-segment bridge through an interior point of a convex hole. -/
def brokenSegment (a c b : (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) :=
  segment ℝ a c ∪ segment ℝ c b

/-- A one-hole surgery preserves a continuum's diameter and changes it only inside the hole. -/
def IsOneHoleSurgery (K U : Set (EuclideanSpace ℝ (Fin 2)))
    (x y : (EuclideanSpace ℝ (Fin 2))) (epsilon : ℝ)
    (D bridge : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  IsCompact D ∧ IsConnected D ∧ x ∈ D ∧ y ∈ D ∧
    Metric.ediam D = Metric.ediam K ∧ D ⊆ convexHull ℝ K ∧
    D \ U ⊆ K \ U ∧ D ∩ U ⊆ bridge ∧
    bridge ⊆ D ∧ IsCompact bridge ∧ IsPreconnected bridge ∧
    bridge ⊆ closure U ∧
    (bridge.Nonempty → (D ∩ (bridge \ U)).Nonempty) ∧
    μH[1] bridge < Metric.ediam U + ENNReal.ofReal epsilon

private theorem isCompact_brokenSegment (a c b : (EuclideanSpace ℝ (Fin 2))) :
    IsCompact (brokenSegment a c b) := by
  have hsegment (u v : (EuclideanSpace ℝ (Fin 2))) : IsCompact (segment ℝ u v) := by
    rw [← affineSegment_eq_segment]
    exact isCompact_Icc.image (by fun_prop)
  exact (hsegment a c).union (hsegment c b)

private theorem isConnected_brokenSegment (a c b : (EuclideanSpace ℝ (Fin 2))) :
    IsConnected (brokenSegment a c b) := by
  refine ⟨⟨c, Or.inl (right_mem_segment ℝ a c)⟩, ?_⟩
  exact IsPreconnected.union c (right_mem_segment ℝ a c) (left_mem_segment ℝ c b)
    (convex_segment a c).isPreconnected (convex_segment c b).isPreconnected

private theorem brokenSegment_subset_convexHull
    {K : Set (EuclideanSpace ℝ (Fin 2))}
    {a c b : (EuclideanSpace ℝ (Fin 2))}
    (ha : a ∈ K) (hc : c ∈ K) (hb : b ∈ K) :
    brokenSegment a c b ⊆ convexHull ℝ K := by
  exact union_subset (segment_subset_convexHull ha hc) (segment_subset_convexHull hc hb)

private theorem brokenSegment_sdiff_subset_endpoints
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hUopen : IsOpen U)
    (hUconvex : Convex ℝ U) {a c b : (EuclideanSpace ℝ (Fin 2))}
    (ha : a ∈ closure U) (hc : c ∈ U)
    (hb : b ∈ closure U) : brokenSegment a c b \ U ⊆ {a, b} := by
  have hcinterior : c ∈ interior U := by rwa [hUopen.interior_eq]
  have hac : openSegment ℝ a c ⊆ U := by
    simpa only [hUopen.interior_eq] using
      hUconvex.openSegment_closure_interior_subset_interior ha hcinterior
  have hcb : openSegment ℝ c b ⊆ U := by
    simpa only [hUopen.interior_eq] using
      hUconvex.openSegment_interior_closure_subset_interior hcinterior hb
  rintro z ⟨hz, hzU⟩
  rcases hz with hz | hz
  · rw [← insert_endpoints_openSegment] at hz
    rcases hz with rfl | rfl | hz
    · exact mem_insert _ _
    · exact (hzU hc).elim
    · exact (hzU (hac hz)).elim
  · rw [← insert_endpoints_openSegment] at hz
    rcases hz with rfl | rfl | hz
    · exact (hzU hc).elim
    · exact mem_insert_iff.mpr (Or.inr (mem_singleton _))
    · exact (hzU (hcb hz)).elim

private theorem hausdorffMeasure_brokenSegment_lt
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hUbounded : IsBounded U)
    {a c b : (EuclideanSpace ℝ (Fin 2))}
    (ha : a ∈ closure U) (hb : b ∈ closure U) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hac : dist a c < epsilon / 2) :
    μH[1] (brokenSegment a c b) < Metric.ediam U + ENNReal.ofReal epsilon := by
  have hab : dist a b ≤ Metric.diam U := by
    rw [← Metric.diam_closure]
    exact Metric.dist_le_diam_of_mem hUbounded.closure ha hb
  have hdist : dist a c + dist c b < Metric.diam U + epsilon := by
    calc
      dist a c + dist c b ≤ dist a c + (dist c a + dist a b) := by
        gcongr
        exact dist_triangle _ _ _
      _ = 2 * dist a c + dist a b := by rw [dist_comm c a]; ring
      _ < epsilon + dist a b := by linarith
      _ ≤ epsilon + Metric.diam U := by gcongr
      _ = Metric.diam U + epsilon := add_comm _ _
  calc
    μH[1] (brokenSegment a c b) ≤ μH[1] (segment ℝ a c) + μH[1] (segment ℝ c b) :=
      measure_union_le _ _
    _ = ENNReal.ofReal (dist a c + dist c b) := by
      rw [hausdorffMeasure_segment, hausdorffMeasure_segment, edist_dist, edist_dist,
        ENNReal.ofReal_add dist_nonneg dist_nonneg]
    _ < ENNReal.ofReal (Metric.diam U + epsilon) := by
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hdist
    _ = Metric.ediam U + ENNReal.ofReal epsilon := by
      rw [ENNReal.ofReal_add Metric.diam_nonneg hepsilon.le, Metric.diam,
        ENNReal.ofReal_toReal hUbounded.ediam_ne_top]

private theorem isCompact_connectedComponentIn_of_isCompact {F : Set (EuclideanSpace ℝ (Fin 2))}
    (hF : IsCompact F) {x : (EuclideanSpace ℝ (Fin 2))} (hx : x ∈ F) :
    IsCompact (connectedComponentIn F x) := by
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hF
  rw [connectedComponentIn_eq_image hx]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

private theorem connectedComponentIn_inter_closure_inter_of_not_mem
    {K U : Set (EuclideanSpace ℝ (Fin 2))} (hKcompact : IsCompact K) (hKconnected : IsConnected K)
    (hU : IsOpen U) {x y : (EuclideanSpace ℝ (Fin 2))}
    (hxK : x ∈ K) (hxU : x ∉ U) (hyK : y ∈ K)
    (hycomponent : y ∉ connectedComponentIn (K \ U) x) :
    (connectedComponentIn (K \ U) x ∩ closure (K ∩ U)).Nonempty := by
  classical
  by_contra hnonempty
  have hinter : connectedComponentIn (K \ U) x ∩ closure (K ∩ U) = ∅ :=
    not_nonempty_iff_eq_empty.mp hnonempty
  let S := K \ U
  have hScompact : IsCompact S := hKcompact.inter_right hU.isClosed_compl
  have hxS : x ∈ S := ⟨hxK, hxU⟩
  let xS : S := ⟨x, hxS⟩
  let O : Set (EuclideanSpace ℝ (Fin 2)) := (closure (K ∩ U))ᶜ ∩ {y}ᶜ
  have hOopen : IsOpen O := isOpen_compl_iff.mpr isClosed_closure |>.inter isOpen_compl_singleton
  have hcomponent_O : connectedComponent xS ⊆ ((↑) ⁻¹' O : Set S) := by
    intro z hz
    have hzcomponent : (z : (EuclideanSpace ℝ (Fin 2))) ∈ connectedComponentIn S x := by
      rw [connectedComponentIn_eq_image hxS]
      exact ⟨z, hz, rfl⟩
    have hzclosure : (z : (EuclideanSpace ℝ (Fin 2))) ∉ closure (K ∩ U) := by
      intro hz
      have : (z : (EuclideanSpace ℝ (Fin 2))) ∈
          connectedComponentIn (K \ U) x ∩ closure (K ∩ U) :=
        ⟨hzcomponent, hz⟩
      rw [hinter] at this
      exact this
    have hzy : (z : (EuclideanSpace ℝ (Fin 2))) ≠ y := by
      intro hzy
      apply hycomponent
      simpa [S, hzy] using hzcomponent
    exact ⟨hzclosure, hzy⟩
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hScompact
  obtain ⟨H, hHclopen, hcomponent_H, hH_O⟩ :=
    exists_isClopen_between_connectedComponent
      (hOopen.preimage continuous_subtype_val) hcomponent_O
  let Hplane : Set (EuclideanSpace ℝ (Fin 2)) := Subtype.val '' H
  have hHplane_compact : IsCompact Hplane :=
    hHclopen.isClosed.isCompact.image continuous_subtype_val
  have hHplane_O : Hplane ⊆ O := by
    rintro z ⟨w, hwH, rfl⟩
    exact hH_O hwH
  have hHplane_clopen_in_K : IsClopen ((↑) ⁻¹' Hplane : Set K) := by
    constructor
    · exact hHplane_compact.isClosed.preimage continuous_subtype_val
    · rcases isOpen_induced_iff.mp hHclopen.isOpen with ⟨V, hVopen, hpreimage⟩
      apply isOpen_induced_iff.mpr
      refine ⟨V ∩ O, hVopen.inter hOopen, ?_⟩
      ext z
      constructor
      · rintro ⟨hzV, hzO⟩
        have hzU : (z : (EuclideanSpace ℝ (Fin 2))) ∉ U := by
          intro hzU
          exact hzO.1 (subset_closure ⟨z.property, hzU⟩)
        let w : S := ⟨z, z.property, hzU⟩
        have hwH : w ∈ H := by
          rw [← hpreimage]
          exact hzV
        exact ⟨w, hwH, rfl⟩
      · rintro ⟨w, hwH, hwz⟩
        have hwV : (w : (EuclideanSpace ℝ (Fin 2))) ∈ V := by
          change w ∈ Subtype.val ⁻¹' V
          rw [hpreimage]
          exact hwH
        have hw : (w : (EuclideanSpace ℝ (Fin 2))) ∈ V ∩ O :=
          ⟨hwV, hHplane_O ⟨w, hwH, rfl⟩⟩
        change (z : (EuclideanSpace ℝ (Fin 2))) ∈ V ∩ O
        exact hwz ▸ hw
  let xK : K := ⟨x, hxK⟩
  have hxHplane : xK ∈ ((↑) ⁻¹' Hplane : Set K) := by
    refine ⟨xS, hcomponent_H ?_, rfl⟩
    exact mem_connectedComponent
  let yK : K := ⟨y, hyK⟩
  have hyHplane : yK ∉ ((↑) ⁻¹' Hplane : Set K) := by
    intro hyH
    exact (hHplane_O hyH).2 rfl
  letI : PreconnectedSpace K := Subtype.preconnectedSpace hKconnected.isPreconnected
  exact hyHplane (isPreconnected_univ.subset_isClopen hHplane_clopen_in_K
    ⟨xK, mem_univ _, hxHplane⟩ <| mem_univ yK)

private theorem isOneHoleSurgery_of_connected_subset
    {K U A : Set (EuclideanSpace ℝ (Fin 2))}
    {x y : (EuclideanSpace ℝ (Fin 2))}
    (hxy : edist x y = Metric.ediam K) (hAcompact : IsCompact A)
    (hAconnected : IsConnected A) (hxA : x ∈ A) (hyA : y ∈ A)
    (hAKU : A ⊆ K \ U) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    IsOneHoleSurgery K U x y epsilon A ∅ := by
  have hAconvexHull : A ⊆ convexHull ℝ K :=
    hAKU.trans <| (inter_subset_left.trans <| subset_convexHull ℝ K)
  have hediam : Metric.ediam A = Metric.ediam K := by
    apply le_antisymm (Metric.ediam_mono hAconvexHull |>.trans_eq (convexHull_ediam K))
    rw [← hxy]
    exact Metric.edist_le_ediam_of_mem hxA hyA
  refine ⟨hAcompact, hAconnected, hxA, hyA, hediam, hAconvexHull,
    ?_, ?_, empty_subset _, isCompact_empty, isPreconnected_empty, empty_subset _, ?_, ?_⟩
  · exact fun _ hz ↦ hAKU hz.1
  · rintro z ⟨hzA, hzU⟩
    exact ((hAKU hzA).2 hzU).elim
  · simp
  · rw [measure_empty]
    positivity

private theorem isOneHoleSurgery_of_component_union_bridge
    {K U A bridge : Set (EuclideanSpace ℝ (Fin 2))}
    {x y q : (EuclideanSpace ℝ (Fin 2))} {epsilon : ℝ}
    (hxy : edist x y = Metric.ediam K)
    (hAcompact : IsCompact A) (hAconnected : IsConnected A) (hyA : y ∈ A)
    (hqA : q ∈ A) (hAKU : A ⊆ K \ U) (hbridgeCompact : IsCompact bridge)
    (hbridgeConnected : IsConnected bridge) (hxbridge : x ∈ bridge) (hqbridge : q ∈ bridge)
    (hbridgeHull : bridge ⊆ convexHull ℝ K) (hbridgeClosure : bridge ⊆ closure U)
    (hbridgeSdiff : bridge \ U ⊆ K \ U)
    (hbridgeMeasure : μH[1] bridge < Metric.ediam U + ENNReal.ofReal epsilon) :
    IsOneHoleSurgery K U x y epsilon (A ∪ bridge) bridge := by
  have hconnected : IsConnected (A ∪ bridge) :=
    IsConnected.union ⟨q, hqA, hqbridge⟩ hAconnected hbridgeConnected
  have hsubset : A ∪ bridge ⊆ convexHull ℝ K :=
    union_subset (hAKU.trans <| inter_subset_left.trans <| subset_convexHull ℝ K) hbridgeHull
  have hediam : Metric.ediam (A ∪ bridge) = Metric.ediam K := by
    apply le_antisymm (Metric.ediam_mono hsubset |>.trans_eq (convexHull_ediam K))
    rw [← hxy]
    exact Metric.edist_le_ediam_of_mem (Or.inr hxbridge) (Or.inl hyA)
  refine ⟨hAcompact.union hbridgeCompact, hconnected, Or.inr hxbridge, Or.inl hyA,
    hediam, hsubset, ?_, ?_, ?_, hbridgeCompact, hbridgeConnected.2, hbridgeClosure,
    fun _ ↦ ⟨q, Or.inl hqA, hqbridge, (hAKU hqA).2⟩, hbridgeMeasure⟩
  · rintro z ⟨hzA | hzbridge, hzU⟩
    · exact hAKU hzA
    · exact hbridgeSdiff ⟨hzbridge, hzU⟩
  · rintro z ⟨hzA | hzbridge, hzU⟩
    · exact (hAKU hzA).2 hzU |>.elim
    · exact hzbridge
  · exact fun _ hz ↦ Or.inr hz

private theorem isOneHoleSurgery_of_two_components
    {K U A B bridge : Set (EuclideanSpace ℝ (Fin 2))}
    {x y a b : (EuclideanSpace ℝ (Fin 2))} {epsilon : ℝ}
    (hxy : edist x y = Metric.ediam K)
    (hAcompact : IsCompact A) (hAconnected : IsConnected A) (hxA : x ∈ A) (haA : a ∈ A)
    (hBcompact : IsCompact B) (hBconnected : IsConnected B) (hyB : y ∈ B) (hbB : b ∈ B)
    (hAKU : A ⊆ K \ U) (hBKU : B ⊆ K \ U) (hbridgeCompact : IsCompact bridge)
    (hbridgeConnected : IsConnected bridge) (habridge : a ∈ bridge) (hbbridge : b ∈ bridge)
    (hbridgeHull : bridge ⊆ convexHull ℝ K) (hbridgeClosure : bridge ⊆ closure U)
    (hbridgeSdiff : bridge \ U ⊆ K \ U)
    (hbridgeMeasure : μH[1] bridge < Metric.ediam U + ENNReal.ofReal epsilon) :
    IsOneHoleSurgery K U x y epsilon ((A ∪ bridge) ∪ B) bridge := by
  have hAbridge : IsConnected (A ∪ bridge) :=
    IsConnected.union ⟨a, haA, habridge⟩ hAconnected hbridgeConnected
  have hconnected : IsConnected ((A ∪ bridge) ∪ B) :=
    IsConnected.union ⟨b, Or.inr hbbridge, hbB⟩ hAbridge hBconnected
  have hsubset : (A ∪ bridge) ∪ B ⊆ convexHull ℝ K := by
    exact union_subset (union_subset
      (hAKU.trans <| inter_subset_left.trans <| subset_convexHull ℝ K) hbridgeHull)
      (hBKU.trans <| inter_subset_left.trans <| subset_convexHull ℝ K)
  have hediam : Metric.ediam ((A ∪ bridge) ∪ B) = Metric.ediam K := by
    apply le_antisymm (Metric.ediam_mono hsubset |>.trans_eq (convexHull_ediam K))
    rw [← hxy]
    exact Metric.edist_le_ediam_of_mem (Or.inl (Or.inl hxA)) (Or.inr hyB)
  refine ⟨(hAcompact.union hbridgeCompact).union hBcompact, hconnected,
    Or.inl (Or.inl hxA), Or.inr hyB, hediam, hsubset, ?_, ?_, ?_, hbridgeCompact,
    hbridgeConnected.2, hbridgeClosure,
    fun _ ↦ ⟨a, Or.inl (Or.inl haA), habridge, (hAKU haA).2⟩,
    hbridgeMeasure⟩
  · rintro z ⟨(hzA | hzbridge) | hzB, hzU⟩
    · exact hAKU hzA
    · exact hbridgeSdiff ⟨hzbridge, hzU⟩
    · exact hBKU hzB
  · rintro z ⟨(hzA | hzbridge) | hzB, hzU⟩
    · exact (hAKU hzA).2 hzU |>.elim
    · exact hzbridge
    · exact (hBKU hzB).2 hzU |>.elim
  · exact fun _ hz ↦ Or.inl (Or.inr hz)

private theorem IsOneHoleSurgery.swap
    {K U D bridge : Set (EuclideanSpace ℝ (Fin 2))}
    {x y : (EuclideanSpace ℝ (Fin 2))}
    {epsilon : ℝ} (h : IsOneHoleSurgery K U x y epsilon D bridge) :
    IsOneHoleSurgery K U y x epsilon D bridge := by
  rcases h with ⟨hDcompact, hDconnected, hxD, hyD, hdiam, hDhull,
    hDoutside, hDinside, hbridgeD, hbridgeCompact, hbridgeConnected, hbridgeClosure,
    hbridgeAnchor, hbridgeMeasure⟩
  exact ⟨hDcompact, hDconnected, hyD, hxD, hdiam, hDhull,
    hDoutside, hDinside, hbridgeD, hbridgeCompact, hbridgeConnected, hbridgeClosure,
    hbridgeAnchor, hbridgeMeasure⟩

private theorem exists_oneHoleSurgery_of_left_mem
    {K U : Set (EuclideanSpace ℝ (Fin 2))} (hKcompact : IsCompact K) (hKconnected : IsConnected K)
    {x y : (EuclideanSpace ℝ (Fin 2))} (hxK : x ∈ K) (hyK : y ∈ K)
    (hxy : edist x y = Metric.ediam K) (hUopen : IsOpen U)
    (hUconvex : Convex ℝ U) (hUbounded : IsBounded U) (hxU : x ∈ U)
    (hyU : y ∉ U) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ D bridge, IsOneHoleSurgery K U x y epsilon D bridge := by
  let B := connectedComponentIn (K \ U) y
  have hyKU : y ∈ K \ U := ⟨hyK, hyU⟩
  have hyB : y ∈ B := mem_connectedComponentIn hyKU
  have hxB : x ∉ B := by
    intro hxB
    exact (connectedComponentIn_subset (K \ U) y hxB).2 hxU
  obtain ⟨b, hbB, hbClosure⟩ :=
    connectedComponentIn_inter_closure_inter_of_not_mem hKcompact hKconnected
      hUopen hyK hyU hxK hxB
  have hBKU : B ⊆ K \ U := connectedComponentIn_subset _ _
  have hbKU : b ∈ K \ U := hBKU hbB
  have hbClosureU : b ∈ closure U := closure_mono inter_subset_right hbClosure
  let bridge := brokenSegment x x b
  have hxbridge : x ∈ bridge := Or.inl (left_mem_segment ℝ x x)
  have hbbridge : b ∈ bridge := Or.inr (right_mem_segment ℝ x b)
  have hbridgeSdiff : bridge \ U ⊆ K \ U := by
    intro z hz
    have hzxb : z ∈ ({x, b} : Set (EuclideanSpace ℝ (Fin 2))) :=
      brokenSegment_sdiff_subset_endpoints hUopen hUconvex
        (subset_closure hxU) hxU hbClosureU hz
    rcases hzxb with rfl | hzxb
    · exact (hz.2 hxU).elim
    · simpa only [mem_singleton_iff] using hzxb ▸ hbKU
  refine ⟨B ∪ bridge, bridge,
    isOneHoleSurgery_of_component_union_bridge hxy
      (isCompact_connectedComponentIn (hKcompact.inter_right hUopen.isClosed_compl) y)
      ((isConnected_connectedComponentIn_iff).2 hyKU) hyB hbB hBKU
      (isCompact_brokenSegment x x b) (isConnected_brokenSegment x x b)
      hxbridge hbbridge ?_ ?_ hbridgeSdiff ?_⟩
  · exact brokenSegment_subset_convexHull hxK hxK hbKU.1
  · exact union_subset (hUconvex.closure.segment_subset
      (subset_closure hxU) (subset_closure hxU))
      (hUconvex.closure.segment_subset (subset_closure hxU) hbClosureU)
  · exact hausdorffMeasure_brokenSegment_lt hUbounded
      (subset_closure hxU) hbClosureU hepsilon (by simp [hepsilon])

/-- A continuum can be surgically changed inside one open convex hole while preserving a
diameter-realizing pair. The bridge inserted in the hole has length at most the hole diameter,
up to an arbitrarily small error. -/
theorem exists_oneHoleSurgery
    {K U : Set (EuclideanSpace ℝ (Fin 2))} (hKcompact : IsCompact K) (hKconnected : IsConnected K)
    {x y : (EuclideanSpace ℝ (Fin 2))} (hxK : x ∈ K) (hyK : y ∈ K)
    (hxy : edist x y = Metric.ediam K) (hUopen : IsOpen U)
    (hUconvex : Convex ℝ U) (hUbounded : IsBounded U)
    (hUdiam : Metric.ediam U < Metric.ediam K) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ D bridge, IsOneHoleSurgery K U x y epsilon D bridge := by
  by_cases hxU : x ∈ U
  · have hyU : y ∉ U := by
      intro hyU
      have hxyU : edist x y ≤ Metric.ediam U :=
        Metric.edist_le_ediam_of_mem hxU hyU
      exact (not_lt_of_ge (hxy.symm ▸ hxyU)) hUdiam
    exact exists_oneHoleSurgery_of_left_mem hKcompact hKconnected hxK hyK hxy
      hUopen hUconvex hUbounded hxU hyU hepsilon
  · by_cases hyU : y ∈ U
    · obtain ⟨D, bridge, hD⟩ :=
        exists_oneHoleSurgery_of_left_mem hKcompact hKconnected hyK hxK
          (edist_comm x y ▸ hxy) hUopen hUconvex hUbounded hyU hxU hepsilon
      exact ⟨D, bridge, hD.swap⟩
    · let A := connectedComponentIn (K \ U) x
      let B := connectedComponentIn (K \ U) y
      have hxKU : x ∈ K \ U := ⟨hxK, hxU⟩
      have hyKU : y ∈ K \ U := ⟨hyK, hyU⟩
      have hxA : x ∈ A := mem_connectedComponentIn hxKU
      have hyB : y ∈ B := mem_connectedComponentIn hyKU
      by_cases hyA : y ∈ A
      · exact ⟨A, ∅, isOneHoleSurgery_of_connected_subset hxy
          (isCompact_connectedComponentIn (hKcompact.inter_right hUopen.isClosed_compl) x)
          ((isConnected_connectedComponentIn_iff).2 hxKU) hxA hyA
          (connectedComponentIn_subset _ _) hepsilon⟩
      · have hxB : x ∉ B := by
          intro hxB
          have hBA : B = A := connectedComponentIn_eq hxB
          exact hyA (hBA ▸ hyB)
        obtain ⟨a, haA, haClosure⟩ :=
          connectedComponentIn_inter_closure_inter_of_not_mem hKcompact hKconnected
            hUopen hxK hxU hyK hyA
        obtain ⟨b, hbB, hbClosure⟩ :=
          connectedComponentIn_inter_closure_inter_of_not_mem hKcompact hKconnected
            hUopen hyK hyU hxK hxB
        have hAKU : A ⊆ K \ U := connectedComponentIn_subset _ _
        have hBKU : B ⊆ K \ U := connectedComponentIn_subset _ _
        have haKU : a ∈ K \ U := hAKU haA
        have hbKU : b ∈ K \ U := hBKU hbB
        have haClosureU : a ∈ closure U := closure_mono inter_subset_right haClosure
        have hbClosureU : b ∈ closure U := closure_mono inter_subset_right hbClosure
        obtain ⟨c, hcKU, hac⟩ := Metric.mem_closure_iff.mp haClosure
          (epsilon / 2) (half_pos hepsilon)
        let bridge := brokenSegment a c b
        have habridge : a ∈ bridge := Or.inl (left_mem_segment ℝ a c)
        have hbbridge : b ∈ bridge := Or.inr (right_mem_segment ℝ c b)
        have hbridgeSdiff : bridge \ U ⊆ K \ U := by
          intro z hz
          have hzab : z ∈ ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) :=
            brokenSegment_sdiff_subset_endpoints hUopen hUconvex
              haClosureU hcKU.2 hbClosureU hz
          rcases hzab with rfl | hzab
          · exact haKU
          · simpa only [mem_singleton_iff] using hzab ▸ hbKU
        refine ⟨(A ∪ bridge) ∪ B, bridge,
          isOneHoleSurgery_of_two_components hxy
            (isCompact_connectedComponentIn
              (hKcompact.inter_right hUopen.isClosed_compl) x)
            ((isConnected_connectedComponentIn_iff).2 hxKU) hxA haA
            (isCompact_connectedComponentIn
              (hKcompact.inter_right hUopen.isClosed_compl) y)
            ((isConnected_connectedComponentIn_iff).2 hyKU) hyB hbB hAKU hBKU
            (isCompact_brokenSegment a c b) (isConnected_brokenSegment a c b)
            habridge hbbridge ?_ ?_ hbridgeSdiff ?_⟩
        · exact brokenSegment_subset_convexHull haKU.1 hcKU.1 hbKU.1
        · exact union_subset (hUconvex.closure.segment_subset
            haClosureU (subset_closure hcKU.2))
            (hUconvex.closure.segment_subset
              (subset_closure hcKU.2) hbClosureU)
        · exact hausdorffMeasure_brokenSegment_lt hUbounded
            haClosureU hbClosureU hepsilon hac

private def threePointBarycenters (C : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  (fun p : stdSimplex ℝ (Fin 3) × (Fin 3 → C) ↦
    ∑ i, p.1.1 i • (p.2 i : (EuclideanSpace ℝ (Fin 2)))) '' univ

private theorem exists_threePointBarycenter {C : Set (EuclideanSpace ℝ (Fin 2))} (hC : C.Nonempty)
    {t : Finset (EuclideanSpace ℝ (Fin 2))}
    (htC : (t : Set (EuclideanSpace ℝ (Fin 2))) ⊆ C)
    {w : (EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hw : ∀ y ∈ t, 0 ≤ w y) (hwsum : ∑ y ∈ t, w y = 1)
    (hcard : Fintype.card t ≤ 3) :
    ∃ p : stdSimplex ℝ (Fin 3) × (Fin 3 → C),
      ∑ i, p.1.1 i • (p.2 i : (EuclideanSpace ℝ (Fin 2))) = ∑ y ∈ t, w y • y := by
  let e : t ↪ Fin 3 := Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  let weight : Fin 3 → ℝ := Function.extend e (fun q : t ↦ w q) 0
  let point : Fin 3 → C :=
    Function.extend e (fun q : t ↦ ⟨q, htC q.property⟩) (fun _ ↦ ⟨hC.some, hC.some_mem⟩)
  have hweight_apply (q : t) : weight (e q) = w q := by simp [weight, Function.extend]
  have hpoint_apply (q : t) : (point (e q) : (EuclideanSpace ℝ (Fin 2))) = q := by
    simp [point, Function.extend]
  have hweight_zero {i : Fin 3} (hi : i ∉ Finset.univ.map e) : weight i = 0 := by
    apply Function.extend_apply'
    simpa only [Finset.mem_map, Finset.mem_univ, true_and, not_exists] using hi
  have hweightsum : ∑ i, weight i = 1 := by
    calc
      (∑ i, weight i) = (∑ i ∈ Finset.univ.map e, weight i) := by
        symm
        apply Finset.sum_subset (by simp)
        intro i _ hi
        exact hweight_zero hi
      _ = (∑ q : t, weight (e q)) := Finset.sum_map (Finset.univ : Finset t) e weight
      _ = (∑ q : t, w q) := by simp only [hweight_apply]
      _ = (∑ y ∈ t, w y) := Finset.sum_coe_sort t w
      _ = 1 := hwsum
  have hweight_nonneg (i : Fin 3) : 0 ≤ weight i := by
    by_cases hi : i ∈ Finset.univ.map e
    · obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hi
      exact hweight_apply q ▸ hw q q.property
    · rw [hweight_zero hi]
  let weights : stdSimplex ℝ (Fin 3) := ⟨weight, hweight_nonneg, hweightsum⟩
  refine ⟨(weights, point), ?_⟩
  calc
    (∑ i, weight i • (point i : (EuclideanSpace ℝ (Fin 2)))) =
        (∑ i ∈ Finset.univ.map e, weight i • (point i : (EuclideanSpace ℝ (Fin 2)))) := by
      symm
      apply Finset.sum_subset (by simp)
      intro i _ hi
      rw [hweight_zero hi, zero_smul]
    _ = (∑ q : t, weight (e q) • (point (e q) : (EuclideanSpace ℝ (Fin 2)))) :=
      Finset.sum_map (Finset.univ : Finset t) e _
    _ = (∑ q : t, w q • (q : (EuclideanSpace ℝ (Fin 2)))) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [hweight_apply, hpoint_apply]
    _ = (∑ y ∈ t, w y • y) := by
      simpa using Finset.sum_coe_sort t (fun y : (EuclideanSpace ℝ (Fin 2)) ↦ w y • y)

private theorem convexHull_eq_threePointBarycenters
    {C : Set (EuclideanSpace ℝ (Fin 2))} (hC : C.Nonempty) :
    convexHull ℝ C = threePointBarycenters C := by
  apply Subset.antisymm
  · intro z hz
    rw [convexHull_eq_union] at hz
    simp only [mem_iUnion, exists_prop] at hz
    obtain ⟨t, htC, htAffine, hzt⟩ := hz
    rw [Finset.mem_convexHull'] at hzt
    obtain ⟨w, hw, hwsum, hwz⟩ := hzt
    have hcard : Fintype.card t ≤ 3 := by
      calc
        Fintype.card t ≤
            Module.finrank ℝ
              (vectorSpan ℝ (range ((↑) : t → (EuclideanSpace ℝ (Fin 2))))) + 1 :=
          htAffine.card_le_finrank_succ
        _ ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + 1 :=
          Nat.add_le_add_right (Submodule.finrank_le _) 1
        _ = 3 := by simp [finrank_euclideanSpace]
    obtain ⟨p, hp⟩ := exists_threePointBarycenter hC htC hw hwsum hcard
    exact ⟨p, mem_univ _, by simpa [threePointBarycenters, hwz] using hp⟩
  · rintro z ⟨p, -, rfl⟩
    change (∑ i, p.1.1 i • (p.2 i : (EuclideanSpace ℝ (Fin 2)))) ∈ convexHull ℝ C
    rw [← Finset.centerMass_eq_of_sum_1 Finset.univ
      (fun i ↦ (p.2 i : (EuclideanSpace ℝ (Fin 2)))) p.1.2.2]
    exact Finset.univ.centerMass_mem_convexHull (fun i _ ↦ p.1.2.1 i)
      (by rw [p.1.2.2]; exact zero_lt_one) (fun i _ ↦ (p.2 i).property)

private theorem isCompact_convexHull_plane
    {C : Set (EuclideanSpace ℝ (Fin 2))} (hC : IsCompact C) :
    IsCompact (convexHull ℝ C) := by
  by_cases hCne : C.Nonempty
  · rw [convexHull_eq_threePointBarycenters hCne, threePointBarycenters]
    letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
    apply IsCompact.image isCompact_univ
    apply continuous_finsetSum Finset.univ
    intro i _
    exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
  · rw [not_nonempty_iff_eq_empty.mp hCne, convexHull_empty]
    exact isCompact_empty

private def holesBefore (U : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ i : Fin n, U i

@[simp]
private theorem holesBefore_zero (U : ℕ → Set (EuclideanSpace ℝ (Fin 2))) :
    holesBefore U 0 = ∅ := by
  simp [holesBefore]

private theorem holesBefore_succ (U : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (n : ℕ) :
    holesBefore U (n + 1) = holesBefore U n ∪ U n := by
  ext z
  simp only [holesBefore, mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hin : (i : ℕ) = n
    · exact Or.inr (hin ▸ hi)
    · exact Or.inl ⟨⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.2) hin⟩, hi⟩
  · rintro (⟨i, hi⟩ | hn)
    · exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last n, hn⟩

private structure SurgeryStage (C : Set (EuclideanSpace ℝ (Fin 2)))
    (U : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (eta : ℕ → ℝ) (x y : (EuclideanSpace ℝ (Fin 2))) (n : ℕ) where
  carrier : Set (EuclideanSpace ℝ (Fin 2))
  bridges : Fin n → Set (EuclideanSpace ℝ (Fin 2))
  isCompact_carrier : IsCompact carrier
  isConnected_carrier : IsConnected carrier
  left_mem : x ∈ carrier
  right_mem : y ∈ carrier
  ediam_eq : Metric.ediam carrier = Metric.ediam C
  subset_convexHull : carrier ⊆ convexHull ℝ C
  outside : carrier \ holesBefore U n ⊆ C \ holesBefore U n
  inside : ∀ i : Fin n, carrier ∩ U i ⊆ bridges i
  isCompact_bridge : ∀ i : Fin n, IsCompact (bridges i)
  isPreconnected_bridge : ∀ i : Fin n, IsPreconnected (bridges i)
  bridge_subset_closure : ∀ i : Fin n, bridges i ⊆ closure (U i)
  bridge_outside : ∀ i : Fin n, bridges i \ U i ⊆ C
  bridge_anchor : ∀ i : Fin n, (bridges i).Nonempty → (bridges i ∩ C).Nonempty
  bridge_measure : ∀ i : Fin n, μH[1] (bridges i) <
    Metric.ediam (U i) + ENNReal.ofReal (eta i)

private def initialSurgeryStage {C : Set (EuclideanSpace ℝ (Fin 2))}
    (U : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (eta : ℕ → ℝ) {x y : (EuclideanSpace ℝ (Fin 2))} (hCcompact : IsCompact C)
    (hCconnected : IsConnected C) (hxC : x ∈ C) (hyC : y ∈ C) :
    SurgeryStage C U eta x y 0 where
  carrier := C
  bridges := Fin.elim0
  isCompact_carrier := hCcompact
  isConnected_carrier := hCconnected
  left_mem := hxC
  right_mem := hyC
  ediam_eq := rfl
  subset_convexHull := subset_convexHull ℝ C
  outside := by simp
  inside := fun i ↦ Fin.elim0 i
  isCompact_bridge := fun i ↦ Fin.elim0 i
  isPreconnected_bridge := fun i ↦ Fin.elim0 i
  bridge_subset_closure := fun i ↦ Fin.elim0 i
  bridge_outside := fun i ↦ Fin.elim0 i
  bridge_anchor := fun i ↦ Fin.elim0 i
  bridge_measure := fun i ↦ Fin.elim0 i

private theorem SurgeryStage.exists_succ
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {eta : ℕ → ℝ}
    {x y : (EuclideanSpace ℝ (Fin 2))} {n : ℕ}
    (S : SurgeryStage C U eta x y n) (hxy : edist x y = Metric.ediam C)
    (hUopen : ∀ i, IsOpen (U i)) (hUconvex : ∀ i, Convex ℝ (U i))
    (hUbounded : ∀ i, IsBounded (U i))
    (hUdisjoint : Pairwise fun i j ↦ Disjoint (U i) (U j))
    (hsum : ∑' i, Metric.ediam (U i) < Metric.ediam C) (heta : ∀ i, 0 < eta i) :
    ∃ T : SurgeryStage C U eta x y (n + 1),
      T.carrier ⊆ S.carrier ∪ T.bridges (Fin.last n) ∧
      (∀ i : Fin n, T.bridges i.castSucc = S.bridges i) := by
  have hdiam : Metric.ediam (U n) < Metric.ediam S.carrier := by
    calc
      Metric.ediam (U n) ≤ ∑' i, Metric.ediam (U i) := ENNReal.le_tsum n
      _ < Metric.ediam C := hsum
      _ = Metric.ediam S.carrier := S.ediam_eq.symm
  obtain ⟨D, bridge, hD⟩ := exists_oneHoleSurgery S.isCompact_carrier
    S.isConnected_carrier S.left_mem S.right_mem (hxy.trans S.ediam_eq.symm)
    (hUopen n) (hUconvex n) (hUbounded n) hdiam (heta n)
  rcases hD with ⟨hDcompact, hDconnected, hxD, hyD, hDediam, hDhull,
    hDoutside, hDinside, hbridgeD, hbridgeCompact, hbridgePreconnected, hbridgeClosure,
    hbridgeAnchor, hbridgeMeasure⟩
  let bridges : Fin (n + 1) → Set (EuclideanSpace ℝ (Fin 2)) := Fin.lastCases bridge S.bridges
  have hDsubset : D ⊆ S.carrier ∪ bridge := by
    intro z hzD
    by_cases hzU : z ∈ U n
    · exact Or.inr (hDinside ⟨hzD, hzU⟩)
    · exact Or.inl (hDoutside ⟨hzD, hzU⟩).1
  have hDhullC : D ⊆ convexHull ℝ C := by
    calc
      D ⊆ convexHull ℝ S.carrier := hDhull
      _ ⊆ convexHull ℝ (convexHull ℝ C) := convexHull_mono S.subset_convexHull
      _ = convexHull ℝ C := (convex_convexHull ℝ C).convexHull_eq
  have hDoutsideBefore : D \ holesBefore U (n + 1) ⊆ C \ holesBefore U (n + 1) := by
    rw [holesBefore_succ]
    rintro z ⟨hzD, hzoutside⟩
    have hzold : z ∉ holesBefore U n := fun hz ↦ hzoutside (Or.inl hz)
    have hzn : z ∉ U n := fun hz ↦ hzoutside (Or.inr hz)
    have hzS : z ∈ S.carrier := (hDoutside ⟨hzD, hzn⟩).1
    exact ⟨(S.outside ⟨hzS, hzold⟩).1, hzoutside⟩
  have hbridgeAnchorC : bridge.Nonempty → (bridge ∩ C).Nonempty := by
    intro hbridge
    obtain ⟨q, hqD, hqbridge, hqn⟩ := hbridgeAnchor hbridge
    have hqold : q ∉ holesBefore U n := by
      rw [holesBefore]
      intro hq
      obtain ⟨i, hqi⟩ := mem_iUnion.mp hq
      have hne : n ≠ (i : ℕ) := by omega
      exact Set.disjoint_left.1 ((hUdisjoint hne).closure_left (hUopen i))
        (hbridgeClosure hqbridge) hqi
    have hqS : q ∈ S.carrier := (hDoutside ⟨hqD, hqn⟩).1
    exact ⟨q, hqbridge, (S.outside ⟨hqS, hqold⟩).1⟩
  have hbridgeOutsideC : bridge \ U n ⊆ C := by
    rintro q ⟨hqbridge, hqn⟩
    have hqold : q ∉ holesBefore U n := by
      rw [holesBefore]
      intro hq
      obtain ⟨i, hqi⟩ := mem_iUnion.mp hq
      have hne : n ≠ (i : ℕ) := by omega
      exact Set.disjoint_left.1 ((hUdisjoint hne).closure_left (hUopen i))
        (hbridgeClosure hqbridge) hqi
    have hqS : q ∈ S.carrier := (hDoutside ⟨hbridgeD hqbridge, hqn⟩).1
    exact (S.outside ⟨hqS, hqold⟩).1
  refine ⟨{
    carrier := D
    bridges := bridges
    isCompact_carrier := hDcompact
    isConnected_carrier := hDconnected
    left_mem := hxD
    right_mem := hyD
    ediam_eq := hDediam.trans S.ediam_eq
    subset_convexHull := hDhullC
    outside := hDoutsideBefore
    inside := ?_
    isCompact_bridge := ?_
    isPreconnected_bridge := ?_
    bridge_subset_closure := ?_
    bridge_outside := ?_
    bridge_anchor := ?_
    bridge_measure := ?_ }, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [bridges] using hDinside
    · intro j
      have hdisjoint : Disjoint (U j) (U n) := hUdisjoint (by omega)
      rintro z ⟨hzD, hzj⟩
      have hzn : z ∉ U n := Set.disjoint_left.1 hdisjoint hzj
      simpa [bridges] using S.inside j ⟨(hDoutside ⟨hzD, hzn⟩).1, hzj⟩
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [bridges] using hbridgeCompact
    · intro j
      simpa [bridges] using S.isCompact_bridge j
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [bridges] using hbridgePreconnected
    · intro j
      simpa [bridges] using S.isPreconnected_bridge j
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [bridges] using hbridgeClosure
    · intro j
      simpa [bridges] using S.bridge_subset_closure j
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [bridges] using hbridgeOutsideC
    · intro j
      simpa [bridges] using S.bridge_outside j
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [bridges] using hbridgeAnchorC
    · intro j
      simpa [bridges] using S.bridge_anchor j
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [bridges] using hbridgeMeasure
    · intro j
      simpa [bridges] using S.bridge_measure j
  · simpa [bridges] using hDsubset
  · intro i
    simp [bridges]

private structure SurgeryData (C : Set (EuclideanSpace ℝ (Fin 2)))
    (U : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (eta : ℕ → ℝ) (x y : (EuclideanSpace ℝ (Fin 2))) where
  isCompact_core : IsCompact C
  isConnected_core : IsConnected C
  left_mem_core : x ∈ C
  right_mem_core : y ∈ C
  realizes_ediam : edist x y = Metric.ediam C
  isOpen_hole : ∀ i, IsOpen (U i)
  convex_hole : ∀ i, Convex ℝ (U i)
  isBounded_hole : ∀ i, IsBounded (U i)
  disjoint_holes : Pairwise fun i j ↦ Disjoint (U i) (U j)
  sum_ediam_lt : ∑' i, Metric.ediam (U i) < Metric.ediam C
  error_pos : ∀ i, 0 < eta i

namespace SurgeryData

private noncomputable def next {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    {eta : ℕ → ℝ} {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) {n : ℕ}
    (S : SurgeryStage C U eta x y n) : SurgeryStage C U eta x y (n + 1) :=
  Classical.choose <| S.exists_succ P.realizes_ediam P.isOpen_hole P.convex_hole
    P.isBounded_hole P.disjoint_holes P.sum_ediam_lt P.error_pos

private theorem next_subset {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    {eta : ℕ → ℝ} {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) {n : ℕ}
    (S : SurgeryStage C U eta x y n) :
    (P.next S).carrier ⊆ S.carrier ∪ (P.next S).bridges (Fin.last n) :=
  (Classical.choose_spec <| S.exists_succ P.realizes_ediam P.isOpen_hole P.convex_hole
    P.isBounded_hole P.disjoint_holes P.sum_ediam_lt P.error_pos).1

private theorem next_bridge_castSucc {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    {eta : ℕ → ℝ} {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) {n : ℕ}
    (S : SurgeryStage C U eta x y n) (i : Fin n) :
    (P.next S).bridges i.castSucc = S.bridges i :=
  (Classical.choose_spec <| S.exists_succ P.realizes_ediam P.isOpen_hole P.convex_hole
    P.isBounded_hole P.disjoint_holes P.sum_ediam_lt P.error_pos).2 i

private noncomputable def stages {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    {eta : ℕ → ℝ} {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) :
    (n : ℕ) → SurgeryStage C U eta x y n
  | 0 => initialSurgeryStage U eta P.isCompact_core P.isConnected_core
      P.left_mem_core P.right_mem_core
  | n + 1 => P.next (P.stages n)

private def bridge {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {eta : ℕ → ℝ}
    {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) (i : ℕ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  (P.stages (i + 1)).bridges (Fin.last i)

private theorem stage_bridge_eq {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    {eta : ℕ → ℝ} {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) (n : ℕ)
    (i : Fin n) : (P.stages n).bridges i = P.bridge i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rfl
      · rw [stages, next_bridge_castSucc]
        exact ih j

private theorem stage_subset_core_union_bridges
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {eta : ℕ → ℝ}
    {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) (n : ℕ) :
    (P.stages n).carrier ⊆ C ∪ ⋃ i : Fin n, P.bridge i := by
  induction n with
  | zero =>
      intro z hz
      exact Or.inl hz
  | succ n ih =>
      intro z hz
      have hz' := next_subset P (P.stages n) hz
      rcases hz' with hzold | hznew
      · rcases ih hzold with hzC | hzi
        · exact Or.inl hzC
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hzi
          exact Or.inr (mem_iUnion.2 ⟨i.castSucc, hi⟩)
      · apply Or.inr
        apply mem_iUnion.2
        exact ⟨Fin.last n, hznew⟩

private theorem isCompact_bridge {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {eta : ℕ → ℝ}
    {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) (i : ℕ) :
    IsCompact (P.bridge i) :=
  (P.stages (i + 1)).isCompact_bridge (Fin.last i)

private theorem bridge_subset_closure {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {eta : ℕ → ℝ}
    {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) (i : ℕ) :
    P.bridge i ⊆ closure (U i) :=
  (P.stages (i + 1)).bridge_subset_closure (Fin.last i)

private theorem bridge_outside {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {eta : ℕ → ℝ}
    {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) (i : ℕ) :
    P.bridge i \ U i ⊆ C :=
  (P.stages (i + 1)).bridge_outside (Fin.last i)

private theorem bridge_anchor {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {eta : ℕ → ℝ}
    {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) (i : ℕ) :
    (P.bridge i).Nonempty → (P.bridge i ∩ C).Nonempty :=
  (P.stages (i + 1)).bridge_anchor (Fin.last i)

private theorem bridge_measure {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {eta : ℕ → ℝ}
    {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) (i : ℕ) :
    μH[1] (P.bridge i) < Metric.ediam (U i) + ENNReal.ofReal (eta i) :=
  (P.stages (i + 1)).bridge_measure (Fin.last i)

private theorem closure_core_union_bridges_sdiff
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {eta : ℕ → ℝ}
    {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) :
    closure (C ∪ ⋃ i, P.bridge i) \ ⋃ i, U i ⊆ C := by
  rintro z ⟨hzclosure, hzholes⟩
  by_contra hzC
  let delta := Metric.infDist z C
  have hCnonempty : C.Nonempty := ⟨x, P.left_mem_core⟩
  have hdelta : 0 < delta :=
    (P.isCompact_core.isClosed.notMem_iff_infDist_pos hCnonempty).1 hzC
  have hsum_ne : ∑' i, Metric.ediam (U i) ≠ ∞ :=
    ne_top_of_lt (P.sum_ediam_lt.trans_le le_top)
  have hdiam_tendsto : Filter.Tendsto (fun i ↦ Metric.diam (U i)) Filter.atTop (nhds 0) := by
    have hed := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum_ne
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hed
    change Filter.Tendsto (fun i ↦ (Metric.ediam (U i)).toReal)
      Filter.atTop (nhds 0) at hreal
    simpa only [Metric.diam] using hreal
  have heventually : ∀ᶠ i in Filter.atTop, Metric.diam (U i) < delta / 3 :=
    (tendsto_order.1 hdiam_tendsto).2 _ (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually
  let F := C ∪ ⋃ i : Fin N, P.bridge i
  have hFcompact : IsCompact F :=
    P.isCompact_core.union (isCompact_iUnion fun i ↦ P.isCompact_bridge i)
  have hFnonempty : F.Nonempty := hCnonempty.mono subset_union_left
  have hzF : z ∉ F := by
    rintro (hzC' | hzbridge)
    · exact hzC hzC'
    · obtain ⟨i, hzi⟩ := mem_iUnion.mp hzbridge
      have hzUi : z ∉ U i := fun h ↦ hzholes (mem_iUnion.2 ⟨(i : ℕ), h⟩)
      exact hzC (P.bridge_outside i ⟨hzi, hzUi⟩)
  have hdistF : 0 < Metric.infDist z F :=
    (hFcompact.isClosed.notMem_iff_infDist_pos hFnonempty).1 hzF
  let rho := min (delta / 3) (Metric.infDist z F / 2)
  have hrho : 0 < rho := lt_min (by linarith) (by linarith)
  obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.mp hzclosure rho hrho
  have hwF : w ∉ F := by
    apply Metric.notMem_of_dist_lt_infDist
    exact hzw.trans_le (min_le_right _ _ |>.trans (by linarith))
  rcases hw with hwC | hwbridge
  · exact (hwF (Or.inl hwC)).elim
  · obtain ⟨i, hwi⟩ := mem_iUnion.mp hwbridge
    have hiN : N ≤ i := by
      by_contra hiN
      apply hwF
      exact Or.inr (mem_iUnion.2 ⟨⟨i, Nat.lt_of_not_ge hiN⟩, hwi⟩)
    obtain ⟨a, haBridge, haC⟩ := P.bridge_anchor i ⟨w, hwi⟩
    have hwa : dist w a ≤ Metric.diam (U i) := by
      rw [← Metric.diam_closure]
      exact Metric.dist_le_diam_of_mem (P.isBounded_hole i).closure
        (P.bridge_subset_closure i hwi) (P.bridge_subset_closure i haBridge)
    have hdelta_le : delta ≤ dist z a := Metric.infDist_le_dist_of_mem haC
    have hcontradiction : delta < delta := calc
      delta ≤ dist z a := hdelta_le
      _ ≤ dist z w + dist w a := dist_triangle _ _ _
      _ < rho + delta / 3 := add_lt_add hzw (hwa.trans_lt (hN i hiN))
      _ ≤ delta / 3 + delta / 3 := add_le_add (min_le_left _ _) le_rfl
      _ < delta := by linarith
    exact (lt_irrefl _ hcontradiction).elim

private noncomputable def compactStage {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {eta : ℕ → ℝ}
    {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) (n : ℕ) :
    TopologicalSpace.NonemptyCompacts (convexHull ℝ C) := by
  letI : CompactSpace (convexHull ℝ C) :=
    isCompact_iff_compactSpace.mp (isCompact_convexHull_plane P.isCompact_core)
  exact {
    carrier := {q | (q : (EuclideanSpace ℝ (Fin 2))) ∈ (P.stages n).carrier}
    isCompact' :=
      ((P.stages n).isCompact_carrier.isClosed.preimage continuous_subtype_val).isCompact
    nonempty' :=
      ⟨⟨x, (P.stages n).subset_convexHull (P.stages n).left_mem⟩,
        (P.stages n).left_mem⟩ }

private theorem isConnected_compactStage {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {eta : ℕ → ℝ}
    {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) (n : ℕ) :
    IsConnected (P.compactStage n : Set (convexHull ℝ C)) := by
  refine ⟨⟨⟨x, (P.stages n).subset_convexHull (P.stages n).left_mem⟩,
    (P.stages n).left_mem⟩, ?_⟩
  exact LeanPool.Besicovitch.IsPreconnected.preimage_subtype_of_subset
    (P.stages n).isConnected_carrier.isPreconnected (P.stages n).subset_convexHull

end SurgeryData

private theorem isConnected_nonemptyCompacts_limit
    {Q : Type*} [MetricSpace Q] [CompactSpace Q]
    (K : ℕ → TopologicalSpace.NonemptyCompacts Q)
    (L : TopologicalSpace.NonemptyCompacts Q)
    (hK : ∀ n, IsConnected (K n : Set Q))
    (hlim : Filter.Tendsto K Filter.atTop (nhds L)) : IsConnected (L : Set Q) := by
  refine ⟨L.nonempty, ?_⟩
  rintro O P hO hP hcover hLO hLP
  by_contra hdisjoint
  obtain ⟨A, B, hAcompact, hBcompact, hAO, hBP, hLAB⟩ :=
    L.isCompact.binary_compact_cover hO hP hcover
  have hAB : Disjoint A B := by
    refine Set.disjoint_left.2 fun z hzA hzB ↦ hdisjoint ?_
    have hzL : z ∈ (L : Set Q) := by rw [hLAB]; exact Or.inl hzA
    exact ⟨z, hzL, hAO hzA, hBP hzB⟩
  have hAne : A.Nonempty := by
    obtain ⟨z, hzL, hzO⟩ := hLO
    rcases hLAB ▸ hzL with hzA | hzB
    · exact ⟨z, hzA⟩
    · exact (hdisjoint ⟨z, hzL, hzO, hBP hzB⟩).elim
  have hBne : B.Nonempty := by
    obtain ⟨z, hzL, hzP⟩ := hLP
    rcases hLAB ▸ hzL with hzA | hzB
    · exact (hdisjoint ⟨z, hzL, hAO hzA, hzP⟩).elim
    · exact ⟨z, hzB⟩
  obtain ⟨V, W, hV, hW, hAV, hBW, hVW⟩ :=
    SeparatedNhds.of_isCompact_isCompact_isClosed
      hAcompact hBcompact hBcompact.isClosed hAB
  have hLsub : (L : Set Q) ⊆ V ∪ W := by
    rw [hLAB]
    exact union_subset_union hAV hBW
  have hLmeetV : ((L : Set Q) ∩ V).Nonempty :=
    hAne.mono fun z hz ↦ ⟨by rw [hLAB]; exact Or.inl hz, hAV hz⟩
  have hLmeetW : ((L : Set Q) ∩ W).Nonempty :=
    hBne.mono fun z hz ↦ ⟨by rw [hLAB]; exact Or.inr hz, hBW hz⟩
  have heventuallySub : ∀ᶠ n in Filter.atTop, (K n : Set Q) ⊆ V ∪ W :=
    hlim.eventually <|
      (TopologicalSpace.NonemptyCompacts.isOpen_subsets_of_isOpen (hV.union hW)).mem_nhds hLsub
  have heventuallyV : ∀ᶠ n in Filter.atTop, ((K n : Set Q) ∩ V).Nonempty :=
    hlim.eventually <|
      (TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hV).mem_nhds hLmeetV
  have heventuallyW : ∀ᶠ n in Filter.atTop, ((K n : Set Q) ∩ W).Nonempty :=
    hlim.eventually <|
      (TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hW).mem_nhds hLmeetW
  obtain ⟨n, hnSub, hnV, hnW⟩ :=
    (heventuallySub.and (heventuallyV.and heventuallyW)).exists
  obtain ⟨z, -, hzV, hzW⟩ := (hK n).2 V W hV hW hnSub hnV hnW
  exact Set.disjoint_left.1 hVW hzV hzW

namespace SurgeryData

private theorem exists_limit {C : Set (EuclideanSpace ℝ (Fin 2))}
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {eta : ℕ → ℝ}
    {x y : (EuclideanSpace ℝ (Fin 2))} (P : SurgeryData C U eta x y) :
    ∃ D : Set (EuclideanSpace ℝ (Fin 2)),
      IsCompact D ∧ IsConnected D ∧ x ∈ D ∧ y ∈ D ∧ D ⊆ convexHull ℝ C ∧
        D ⊆ closure (C ∪ ⋃ i, P.bridge i) ∧ ∀ i, D ∩ U i ⊆ P.bridge i := by
  letI : CompactSpace (convexHull ℝ C) :=
    isCompact_iff_compactSpace.mp (isCompact_convexHull_plane P.isCompact_core)
  obtain ⟨L, phi, hphi, hlimit⟩ := CompactSpace.tendsto_subseq P.compactStage
  let D : Set (EuclideanSpace ℝ (Fin 2)) := Subtype.val '' (L : Set (convexHull ℝ C))
  have hLconnected : IsConnected (L : Set (convexHull ℝ C)) :=
    isConnected_nonemptyCompacts_limit (fun n ↦ P.compactStage (phi n)) L
      (fun n ↦ P.isConnected_compactStage (phi n)) hlimit
  have hDcompact : IsCompact D := L.isCompact.image continuous_subtype_val
  have hDconnected : IsConnected D :=
    hLconnected.image Subtype.val continuous_subtype_val.continuousOn
  let xHull : convexHull ℝ C := ⟨x, subset_convexHull ℝ C P.left_mem_core⟩
  let yHull : convexHull ℝ C := ⟨y, subset_convexHull ℝ C P.right_mem_core⟩
  have hxL : xHull ∈ L := by
    have hhit : ((L : Set (convexHull ℝ C)) ∩ {xHull}).Nonempty :=
      (TopologicalSpace.NonemptyCompacts.isClosed_inter_nonempty_of_isClosed
        isClosed_singleton).mem_of_tendsto hlimit <| Filter.Eventually.of_forall fun n ↦
          ⟨xHull, (P.stages (phi n)).left_mem, rfl⟩
    obtain ⟨q, hqL, hqx⟩ := hhit
    exact (mem_singleton_iff.mp hqx) ▸ hqL
  have hyL : yHull ∈ L := by
    have hhit : ((L : Set (convexHull ℝ C)) ∩ {yHull}).Nonempty :=
      (TopologicalSpace.NonemptyCompacts.isClosed_inter_nonempty_of_isClosed
        isClosed_singleton).mem_of_tendsto hlimit <| Filter.Eventually.of_forall fun n ↦
          ⟨yHull, (P.stages (phi n)).right_mem, rfl⟩
    obtain ⟨q, hqL, hqy⟩ := hhit
    exact (mem_singleton_iff.mp hqy) ▸ hqL
  have hDclosure : D ⊆ closure (C ∪ ⋃ i, P.bridge i) := by
    let F : Set (convexHull ℝ C) :=
      Subtype.val ⁻¹' closure (C ∪ ⋃ i, P.bridge i)
    have hFclosed : IsClosed F := isClosed_closure.preimage continuous_subtype_val
    have hLsubset : (L : Set (convexHull ℝ C)) ⊆ F :=
      (TopologicalSpace.NonemptyCompacts.isClosed_subsets_of_isClosed
        hFclosed).mem_of_tendsto hlimit <| Filter.Eventually.of_forall fun n q hq ↦ by
          apply subset_closure
          rcases P.stage_subset_core_union_bridges (phi n) hq with hqC | hqbridge
          · exact Or.inl hqC
          · obtain ⟨j, hj⟩ := mem_iUnion.mp hqbridge
            exact Or.inr (mem_iUnion.2 ⟨(j : ℕ), hj⟩)
    rintro z ⟨q, hqL, rfl⟩
    exact hLsubset hqL
  have hDinside : ∀ i, D ∩ U i ⊆ P.bridge i := by
    intro i z hz
    obtain ⟨q, hqL, rfl⟩ := hz.1
    by_contra hqbridge
    let V : Set (convexHull ℝ C) := Subtype.val ⁻¹' (U i \ P.bridge i)
    have hVopen : IsOpen V :=
      ((P.isOpen_hole i).sdiff (P.isCompact_bridge i).isClosed).preimage
        continuous_subtype_val
    have hLmeet : ((L : Set (convexHull ℝ C)) ∩ V).Nonempty :=
      ⟨q, hqL, hz.2, hqbridge⟩
    have hmeet : ∀ᶠ n in Filter.atTop,
        (((P.compactStage (phi n) : Set (convexHull ℝ C)) ∩ V).Nonempty) :=
      hlimit.eventually <|
        (TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hVopen).mem_nhds
          hLmeet
    have hindex : ∀ᶠ n in Filter.atTop, i + 1 ≤ phi n :=
      (Filter.tendsto_atTop.1 hphi.tendsto_atTop) (i + 1)
    obtain ⟨n, hnmeet, hni⟩ := (hmeet.and hindex).exists
    obtain ⟨r, hrstage, hrU, hrbridge⟩ := hnmeet
    let j : Fin (phi n) := ⟨i, Nat.lt_of_succ_le hni⟩
    have hrnew := (P.stages (phi n)).inside j ⟨hrstage, hrU⟩
    rw [P.stage_bridge_eq (phi n) j] at hrnew
    exact hrbridge hrnew
  exact ⟨D, hDcompact, hDconnected, ⟨xHull, hxL, rfl⟩, ⟨yHull, hyL, rfl⟩,
    fun _ ⟨q, _, hq⟩ ↦ hq ▸ q.property, hDclosure, hDinside⟩

end SurgeryData

/-- Countably many disjoint open convex holes can be bypassed without changing a
diameter-realizing pair, at a total length cost bounded by their diameters. -/
theorem exists_continuum_surgery {C : Set (EuclideanSpace ℝ (Fin 2))} (hCcompact : IsCompact C)
    (hCconnected : IsConnected C) {x y : (EuclideanSpace ℝ (Fin 2))}
    (hxC : x ∈ C) (hyC : y ∈ C)
    (hxy : edist x y = Metric.ediam C) (U : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (hUopen : ∀ i, IsOpen (U i)) (hUconvex : ∀ i, Convex ℝ (U i))
    (hUbounded : ∀ i, IsBounded (U i))
    (hUdisjoint : Pairwise fun i j ↦ Disjoint (U i) (U j))
    (hsum : (∑' i, Metric.ediam (U i)) < Metric.ediam C) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ D : Set (EuclideanSpace ℝ (Fin 2)),
      IsCompact D ∧ IsConnected D ∧ x ∈ D ∧ y ∈ D ∧
        Metric.ediam D = Metric.ediam C ∧ D ⊆ convexHull ℝ C ∧
        D \ ⋃ i, U i ⊆ C \ ⋃ i, U i ∧
        μH[1] (D ∩ ⋃ i, U i) ≤ (∑' i, Metric.ediam (U i)) + ENNReal.ofReal epsilon ∧
        μH[1] D ≤ μH[1] C + (∑' i, Metric.ediam (U i)) + ENNReal.ofReal epsilon := by
  let eta : ℕ → ℝ := fun i ↦ epsilon / 2 / 2 ^ i
  let P : SurgeryData C U eta x y := {
    isCompact_core := hCcompact
    isConnected_core := hCconnected
    left_mem_core := hxC
    right_mem_core := hyC
    realizes_ediam := hxy
    isOpen_hole := hUopen
    convex_hole := hUconvex
    isBounded_hole := hUbounded
    disjoint_holes := hUdisjoint
    sum_ediam_lt := hsum
    error_pos := fun _ ↦ by dsimp [eta]; positivity }
  obtain ⟨D, hDcompact, hDconnected, hxD, hyD, hDhull, hDclosure, hDinside⟩ :=
    P.exists_limit
  have hDediam : Metric.ediam D = Metric.ediam C := by
    apply le_antisymm (Metric.ediam_mono hDhull |>.trans_eq (convexHull_ediam C))
    rw [← hxy]
    exact Metric.edist_le_ediam_of_mem hxD hyD
  have hDoutside : D \ ⋃ i, U i ⊆ C \ ⋃ i, U i := by
    intro z hz
    exact ⟨P.closure_core_union_bridges_sdiff ⟨hDclosure hz.1, hz.2⟩, hz.2⟩
  have hDholes : D ∩ ⋃ i, U i ⊆ ⋃ i, P.bridge i := by
    rintro z ⟨hzD, hzU⟩
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hzU
    exact mem_iUnion.2 ⟨i, hDinside i ⟨hzD, hzi⟩⟩
  have hetaSum : ∑' i, ENNReal.ofReal (eta i) = ENNReal.ofReal epsilon := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ (P.error_pos i).le)
      (summable_geometric_two' epsilon), tsum_geometric_two']
  have hinsideMeasure :
      μH[1] (D ∩ ⋃ i, U i) ≤ (∑' i, Metric.ediam (U i)) + ENNReal.ofReal epsilon := by
    calc
      μH[1] (D ∩ ⋃ i, U i) ≤ μH[1] (⋃ i, P.bridge i) := measure_mono hDholes
      _ ≤ ∑' i, μH[1] (P.bridge i) := measure_iUnion_le _
      _ ≤ ∑' i, (Metric.ediam (U i) + ENNReal.ofReal (eta i)) :=
        ENNReal.tsum_le_tsum fun i ↦ (P.bridge_measure i).le
      _ = (∑' i, Metric.ediam (U i)) + ∑' i, ENNReal.ofReal (eta i) :=
        ENNReal.tsum_add
      _ = (∑' i, Metric.ediam (U i)) + ENNReal.ofReal epsilon := by rw [hetaSum]
  have hDdecomp : D ⊆ C ∪ (D ∩ ⋃ i, U i) := by
    intro z hzD
    by_cases hzU : z ∈ ⋃ i, U i
    · exact Or.inr ⟨hzD, hzU⟩
    · exact Or.inl (hDoutside ⟨hzD, hzU⟩).1
  have htotalMeasure :
      μH[1] D ≤ μH[1] C + (∑' i, Metric.ediam (U i)) + ENNReal.ofReal epsilon := by
    calc
      μH[1] D ≤ μH[1] (C ∪ (D ∩ ⋃ i, U i)) := measure_mono hDdecomp
      _ ≤ μH[1] C + μH[1] (D ∩ ⋃ i, U i) := measure_union_le _ _
      _ ≤ μH[1] C + ((∑' i, Metric.ediam (U i)) + ENNReal.ofReal epsilon) := by
        gcongr
      _ = μH[1] C + (∑' i, Metric.ediam (U i)) + ENNReal.ofReal epsilon :=
        (add_assoc _ _ _).symm
  exact ⟨D, hDcompact, hDconnected, hxD, hyD, hDediam, hDhull, hDoutside,
    hinsideMeasure, htotalMeasure⟩

/-- The continuum-surgery theorem for a countable index type. -/
theorem exists_continuum_surgery_countable {iota : Type*} [Countable iota]
    {C : Set (EuclideanSpace ℝ (Fin 2))} (hCcompact : IsCompact C) (hCconnected : IsConnected C)
    {x y : (EuclideanSpace ℝ (Fin 2))} (hxC : x ∈ C) (hyC : y ∈ C)
    (hxy : edist x y = Metric.ediam C) (U : iota → Set (EuclideanSpace ℝ (Fin 2)))
    (hUopen : ∀ i, IsOpen (U i)) (hUconvex : ∀ i, Convex ℝ (U i))
    (hUbounded : ∀ i, IsBounded (U i))
    (hUdisjoint : Pairwise fun i j ↦ Disjoint (U i) (U j))
    (hsum : (∑' i, Metric.ediam (U i)) < Metric.ediam C) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ D : Set (EuclideanSpace ℝ (Fin 2)),
      IsCompact D ∧ IsConnected D ∧ x ∈ D ∧ y ∈ D ∧
        Metric.ediam D = Metric.ediam C ∧ D ⊆ convexHull ℝ C ∧
        D \ ⋃ i, U i ⊆ C \ ⋃ i, U i ∧
        μH[1] (D ∩ ⋃ i, U i) ≤ (∑' i, Metric.ediam (U i)) + ENNReal.ofReal epsilon ∧
        μH[1] D ≤ μH[1] C + (∑' i, Metric.ediam (U i)) + ENNReal.ofReal epsilon := by
  letI : Encodable iota := Encodable.ofCountable iota
  let e : iota → ℕ := Encodable.encode
  let V : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := Function.extend e U ⊥
  have he : Function.Injective e := Encodable.encode_injective
  have hVencode (i : iota) : V (e i) = U i := by
    exact he.extend_apply U ⊥ i
  have hVoutside {n : ℕ} (hn : ¬ ∃ i, e i = n) : V n = ∅ := by
    dsimp only [V]
    rw [Function.extend_apply' U ⊥ n hn]
    rfl
  have hVopen : ∀ n, IsOpen (V n) := by
    intro n
    by_cases hn : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [hVencode]
      exact hUopen i
    · rw [hVoutside hn]
      exact isOpen_empty
  have hVconvex : ∀ n, Convex ℝ (V n) := by
    intro n
    by_cases hn : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [hVencode]
      exact hUconvex i
    · rw [hVoutside hn]
      exact convex_empty
  have hVbounded : ∀ n, IsBounded (V n) := by
    intro n
    by_cases hn : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [hVencode]
      exact hUbounded i
    · rw [hVoutside hn]
      exact Bornology.isBounded_empty
  have hVdisjoint : Pairwise fun m n ↦ Disjoint (V m) (V n) := by
    simpa only [V] using
      hUdisjoint.disjoint_extend_bot (he.factorsThrough U)
  have hUnion : (⋃ n, V n) = ⋃ i, U i := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hzn⟩ := mem_iUnion.mp hz
      by_cases hn : ∃ i, e i = n
      · obtain ⟨i, rfl⟩ := hn
        exact mem_iUnion.2 ⟨i, by simpa only [hVencode] using hzn⟩
      · rw [hVoutside hn] at hzn
        exact hzn.elim
    · intro hz
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
      exact mem_iUnion.2 ⟨e i, by simpa only [hVencode] using hzi⟩
  have hsupport :
      Function.support (fun n ↦ Metric.ediam (V n)) ⊆ Set.range e := by
    intro n hn
    by_contra hnrange
    apply hn
    change Metric.ediam (V n) = 0
    rw [hVoutside, Metric.ediam_empty]
    simpa only [Set.mem_range] using hnrange
  have hsumV : (∑' n, Metric.ediam (V n)) = ∑' i, Metric.ediam (U i) := by
    symm
    simpa only [hVencode] using he.tsum_eq hsupport
  simpa only [hUnion, hsumV] using
    exists_continuum_surgery hCcompact hCconnected hxC hyC hxy V hVopen hVconvex
      hVbounded hVdisjoint (by simpa only [hsumV] using hsum) hepsilon

/-- A countable family of open holes has a pairwise-disjoint open convex enlargement whose
total diameter is no larger. -/
theorem exists_pairwiseDisjoint_convex_hole_cover_countable
    {iota : Type*} [Countable iota] (U : iota → Set (EuclideanSpace ℝ (Fin 2)))
    (hUopen : ∀ i, IsOpen (U i))
    (hsum : (∑' i, Metric.ediam (U i)) ≠ ∞) :
    ∃ W : Set (Set (EuclideanSpace ℝ (Fin 2))),
      W.Countable ∧ W.PairwiseDisjoint id ∧
        (∀ V : W, IsOpen (V : Set (EuclideanSpace ℝ (Fin 2))) ∧
          Convex ℝ (V : Set (EuclideanSpace ℝ (Fin 2))) ∧
          IsBounded (V : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        (⋃ i, U i) ⊆ ⋃ V : W, (V : Set (EuclideanSpace ℝ (Fin 2))) ∧
        (∑' V : W, Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2)))) ≤
          ∑' i, Metric.ediam (U i) := by
  letI : Encodable iota := Encodable.ofCountable iota
  let e : iota → ℕ := Encodable.encode
  let V : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := Function.extend e U ⊥
  have he : Function.Injective e := Encodable.encode_injective
  have hVencode (i : iota) : V (e i) = U i := he.extend_apply U ⊥ i
  have hVoutside {n : ℕ} (hn : ¬ ∃ i, e i = n) : V n = ∅ := by
    dsimp only [V]
    rw [Function.extend_apply' U ⊥ n hn]
    rfl
  have hVopen : ∀ n, IsOpen (V n) := by
    intro n
    by_cases hn : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [hVencode]
      exact hUopen i
    · rw [hVoutside hn]
      exact isOpen_empty
  have hUnion : (⋃ n, V n) = ⋃ i, U i := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hzn⟩ := mem_iUnion.mp hz
      by_cases hn : ∃ i, e i = n
      · obtain ⟨i, rfl⟩ := hn
        exact mem_iUnion.2 ⟨i, by simpa only [hVencode] using hzn⟩
      · rw [hVoutside hn] at hzn
        exact hzn.elim
    · intro hz
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
      exact mem_iUnion.2 ⟨e i, by simpa only [hVencode] using hzi⟩
  have hsupport :
      Function.support (fun n ↦ Metric.ediam (V n)) ⊆ Set.range e := by
    intro n hn
    by_contra hnrange
    apply hn
    change Metric.ediam (V n) = 0
    rw [hVoutside, Metric.ediam_empty]
    simpa only [Set.mem_range] using hnrange
  have hsumV : (∑' n, Metric.ediam (V n)) = ∑' i, Metric.ediam (U i) := by
    symm
    simpa only [hVencode] using he.tsum_eq hsupport
  simpa only [hUnion, hsumV] using
    exists_pairwiseDisjoint_convex_hole_cover V hVopen (by simpa only [hsumV] using hsum)

/-- Surgery for arbitrary countably many open holes. The part not inherited from the old
continuum outside the holes has measure strictly smaller than the preserved diameter. -/
theorem exists_continuum_surgery_open_holes {iota : Type*} [Countable iota]
    {C : Set (EuclideanSpace ℝ (Fin 2))} (hCcompact : IsCompact C) (hCconnected : IsConnected C)
    {x y : (EuclideanSpace ℝ (Fin 2))} (hxC : x ∈ C) (hyC : y ∈ C)
    (hxy : edist x y = Metric.ediam C) (U : iota → Set (EuclideanSpace ℝ (Fin 2)))
    (hUopen : ∀ i, IsOpen (U i))
    (hsum : (∑' i, Metric.ediam (U i)) < Metric.ediam C) :
    ∃ D : Set (EuclideanSpace ℝ (Fin 2)),
      IsCompact D ∧ IsConnected D ∧ x ∈ D ∧ y ∈ D ∧
        Metric.ediam D = Metric.ediam C ∧ D ⊆ convexHull ℝ C ∧
        μH[1] (D \ (C \ ⋃ i, U i)) < Metric.ediam C ∧
        μH[1] (D ∩ ⋃ i, U i) < Metric.ediam C ∧
        μH[1] D ≤ μH[1] (C \ ⋃ i, U i) + Metric.ediam C := by
  obtain ⟨W, hWcountable, hWdisjoint, hWproperties, hcover, hWsum⟩ :=
    exists_pairwiseDisjoint_convex_hole_cover_countable U hUopen
      (ne_top_of_lt (hsum.trans_le le_top))
  letI : Countable W := hWcountable.to_subtype
  have hWpairwise : Pairwise fun V Z : W ↦
      Disjoint (V : Set (EuclideanSpace ℝ (Fin 2))) (Z : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro V Z hVZ
    simpa only [Function.onFun, id_eq] using
      hWdisjoint V.property Z.property (fun h ↦ hVZ (Subtype.ext h))
  obtain ⟨error, herror, hbudget⟩ :=
    ENNReal.lt_iff_exists_add_pos_lt.mp hsum
  obtain ⟨D, hDcompact, hDconnected, hxD, hyD, hDediam, hDhull,
      hDoutside, hDinside, -⟩ :=
    exists_continuum_surgery_countable hCcompact hCconnected hxC hyC hxy
      (fun V : W ↦ (V : Set (EuclideanSpace ℝ (Fin 2)))) (fun V ↦ (hWproperties V).1)
      (fun V ↦ (hWproperties V).2.1) (fun V ↦ (hWproperties V).2.2)
      hWpairwise (hWsum.trans_lt hsum) (NNReal.coe_pos.mpr herror)
  have hinsideStrict :
      μH[1] (D ∩ ⋃ V : W, (V : Set (EuclideanSpace ℝ (Fin 2)))) < Metric.ediam C := by
    calc
      μH[1] (D ∩ ⋃ V : W, (V : Set (EuclideanSpace ℝ (Fin 2)))) ≤
          (∑' V : W, Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2)))) +
            ENNReal.ofReal (error : ℝ) :=
        hDinside
      _ ≤ (∑' i, Metric.ediam (U i)) + (error : ℝ≥0∞) := by
        simpa only [ENNReal.ofReal_coe_nnreal, add_comm] using
          add_le_add_right hWsum (error : ℝ≥0∞)
      _ < Metric.ediam C := hbudget
  have hchargedSubset :
      D \ (C \ ⋃ i, U i) ⊆ D ∩ ⋃ V : W, (V : Set (EuclideanSpace ℝ (Fin 2))) := by
    rintro z ⟨hzD, hzcore⟩
    refine ⟨hzD, ?_⟩
    by_contra hzW
    have hzoutside := hDoutside ⟨hzD, hzW⟩
    apply hzcore
    exact ⟨hzoutside.1, fun hzU ↦ hzW (hcover hzU)⟩
  have hcharged : μH[1] (D \ (C \ ⋃ i, U i)) < Metric.ediam C :=
    (measure_mono hchargedSubset).trans_lt hinsideStrict
  have hinsideOriginal : μH[1] (D ∩ ⋃ i, U i) < Metric.ediam C := by
    apply (measure_mono ?_).trans_lt hcharged
    rintro z ⟨hzD, hzU⟩
    exact ⟨hzD, fun hzcore ↦ hzcore.2 hzU⟩
  have hdecomp : D ⊆ (C \ ⋃ i, U i) ∪ (D \ (C \ ⋃ i, U i)) := by
    intro z hzD
    by_cases hzcore : z ∈ C \ ⋃ i, U i
    · exact Or.inl hzcore
    · exact Or.inr ⟨hzD, hzcore⟩
  have htotal : μH[1] D ≤ μH[1] (C \ ⋃ i, U i) + Metric.ediam C := by
    calc
      μH[1] D ≤ μH[1] ((C \ ⋃ i, U i) ∪ (D \ (C \ ⋃ i, U i))) :=
        measure_mono hdecomp
      _ ≤ μH[1] (C \ ⋃ i, U i) + μH[1] (D \ (C \ ⋃ i, U i)) :=
        measure_union_le _ _
      _ ≤ μH[1] (C \ ⋃ i, U i) + Metric.ediam C := by
        gcongr
  exact ⟨D, hDcompact, hDconnected, hxD, hyD, hDediam, hDhull,
    hcharged, hinsideOriginal, htotal⟩

end LeanPool.Besicovitch
