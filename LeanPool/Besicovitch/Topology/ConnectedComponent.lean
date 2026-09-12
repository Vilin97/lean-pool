/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Connected components in compact spaces

A connected component in a compact Hausdorff space has arbitrarily small clopen
neighborhoods. This is the compact-space separation fact used in the BPC argument.
-/

@[expose] public section

open Set

namespace LeanPool.Besicovitch

/-- A preconnected subset remains preconnected when viewed inside a larger subtype. -/
theorem IsPreconnected.preimage_subtype_of_subset {X : Type*} [TopologicalSpace X]
    {A Q : Set X} (hA : IsPreconnected A) (hAQ : A ⊆ Q) :
    IsPreconnected ((↑) ⁻¹' A : Set Q) := by
  let inclusion : A → Q := fun x ↦ ⟨x, hAQ x.2⟩
  have hinclusion : Topology.IsInducing inclusion :=
    Topology.IsInducing.subtypeVal.codRestrict fun x : A ↦ hAQ x.2
  have himage : inclusion '' (univ : Set A) = (↑) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩
  rw [← himage, hinclusion.isPreconnected_image]
  letI : PreconnectedSpace A := Subtype.preconnectedSpace hA
  exact isPreconnected_univ

/-- A connected component cut out inside a compact set is compact. -/
theorem isCompact_connectedComponentIn {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (x : X) : IsCompact (connectedComponentIn K x) := by
  by_cases hx : x ∈ K
  · rw [connectedComponentIn_eq_image hx]
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  · rw [connectedComponentIn_eq_empty hx]
    exact isCompact_empty

/-- In a compact Hausdorff space, a connected component contained in an open set has a clopen
neighborhood contained in that open set. -/
theorem exists_isClopen_between_connectedComponent {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] {x : X} {U : Set X} (hU : IsOpen U)
    (hcomponent : connectedComponent x ⊆ U) :
    ∃ H : Set X, IsClopen H ∧ connectedComponent x ⊆ H ∧ H ⊆ U := by
  rw [connectedComponent_eq_iInter_isClopen] at hcomponent
  have hfinite := hU.isClosed_compl.isCompact.inter_iInter_nonempty
    (fun s : {s : Set X // IsClopen s ∧ x ∈ s} ↦ s) fun s ↦ s.2.1.1
  rw [← not_disjoint_iff_nonempty_inter, imp_not_comm, not_forall] at hfinite
  obtain ⟨sets, hsets⟩ :=
    hfinite (disjoint_compl_left_iff_subset.2 hcomponent)
  refine ⟨⋂ s ∈ sets, Subtype.val s, ?_, ?_, ?_⟩
  · exact isClopen_biInter_finset fun s _ ↦ s.2.1
  · rw [connectedComponent_eq_iInter_isClopen]
    intro y hy
    exact mem_iInter₂.2 fun s _ ↦ mem_iInter.1 hy s
  · rwa [← disjoint_compl_left_iff_subset, disjoint_iff_inter_eq_empty,
      ← not_nonempty_iff_eq_empty]

/-- A clopen neighborhood of a component in a closed ball remains clopen in the ambient compact
set when it lies in a strictly smaller ball. -/
theorem exists_isClopenWithin_between_connectedComponentIn_closedBall
    {X : Type*} [PseudoMetricSpace X] [T2Space X]
    {Q : Set X} (hQ : IsCompact Q)
    {z : X} (hzQ : z ∈ Q) {R rho : ℝ} (hR : 0 ≤ R) (hRrho : R < rho)
    (hcomponent : connectedComponentIn (Q ∩ Metric.closedBall z rho) z ⊆ Metric.ball z R) :
    ∃ H : Set X,
      connectedComponentIn (Q ∩ Metric.closedBall z rho) z ⊆ H ∧
        H ⊆ Q ∩ Metric.ball z R ∧ IsClopen ((↑) ⁻¹' H : Set Q) ∧ IsCompact H := by
  let K := Q ∩ Metric.closedBall z rho
  have hK : IsCompact K := hQ.inter_right Metric.isClosed_closedBall
  have hzK : z ∈ K :=
    ⟨hzQ, Metric.mem_closedBall_self (le_of_lt (hR.trans_lt hRrho))⟩
  let zK : K := ⟨z, hzK⟩
  let U : Set K := (↑) ⁻¹' Metric.ball z R
  have hU : IsOpen U := Metric.isOpen_ball.preimage continuous_subtype_val
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcomponent_subtype : connectedComponent zK ⊆ U := by
    intro x hx
    apply hcomponent
    rw [connectedComponentIn_eq_image hzK]
    exact ⟨x, hx, rfl⟩
  obtain ⟨H, hH_clopen, hcomponent_H, hH_U⟩ :=
    exists_isClopen_between_connectedComponent hU hcomponent_subtype
  let Hplane : Set X := Subtype.val '' H
  have hHplane_component : connectedComponentIn K z ⊆ Hplane := by
    rw [connectedComponentIn_eq_image hzK]
    exact image_mono hcomponent_H
  have hHplane_subset : Hplane ⊆ Q ∩ Metric.ball z R := by
    rintro x ⟨y, hyH, rfl⟩
    exact ⟨y.2.1, hH_U hyH⟩
  have hHplane_compact : IsCompact Hplane :=
    hH_clopen.isClosed.isCompact.image continuous_subtype_val
  refine ⟨Hplane, hHplane_component, hHplane_subset, ?_, hHplane_compact⟩
  constructor
  · exact hHplane_compact.isClosed.preimage continuous_subtype_val
  · rcases isOpen_induced_iff.mp hH_clopen.isOpen with ⟨O, hO, hpreimage⟩
    apply isOpen_induced_iff.mpr
    refine ⟨O ∩ Metric.ball z rho, hO.inter Metric.isOpen_ball, ?_⟩
    ext x
    constructor
    · rintro ⟨hxO, hxrho⟩
      let y : K := ⟨x, x.2, Metric.ball_subset_closedBall hxrho⟩
      have hyH : y ∈ H := by
        rw [← hpreimage]
        exact hxO
      exact ⟨y, hyH, rfl⟩
    · intro hx
      obtain ⟨y, hyH, hyx⟩ := hx
      have hyO : (y : X) ∈ O := by
        have : y ∈ Subtype.val ⁻¹' O := hpreimage.symm ▸ hyH
        exact this
      have hyR : (y : X) ∈ Metric.ball z R := hH_U hyH
      exact ⟨hyx ▸ hyO, Metric.ball_subset_ball hRrho.le (hyx ▸ hyR)⟩

end LeanPool.Besicovitch
