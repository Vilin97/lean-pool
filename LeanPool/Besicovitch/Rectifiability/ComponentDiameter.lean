/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.BPC.Basic
public import LeanPool.Besicovitch.Measure.UniformDensity
public import LeanPool.Besicovitch.Rectifiability.CompactAttachmentUnion
public import LeanPool.Besicovitch.Topology.ConnectedComponent
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Diameter of the local attachment component

The BPC witness prevents the component through the selected density point from remaining inside
the small inner ball.  Any hypothetical clopen separation would be crossed by one convex
attachment.
-/

@[expose] public section

noncomputable section

open Bornology MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

namespace LeanPool.Besicovitch

/-- The connected component through `z` in the attachment union localized to a closed ball. -/
def localAttachmentComponent (F : Set (EuclideanSpace ℝ (Fin 2)))
    (chosen : Set (Set (EuclideanSpace ℝ (Fin 2))))
    (z : (EuclideanSpace ℝ (Fin 2))) (rho : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  connectedComponentIn
    (compactAttachmentUnion F chosen ∩ Metric.closedBall z rho) z

/-- A BPC separation forces the local attachment component to have diameter at least
`sigma * rho / 2`. -/
theorem sigma_mul_radius_div_two_le_diam_localAttachmentComponent
    {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {F : Set (EuclideanSpace ℝ (Fin 2))} (hF : IsCompact F) {alpha tau sigma gamma : ℝ}
    (halpha : 0 < alpha) (halpha_tau : alpha ≤ tau) (hsigma : 0 ≤ sigma)
    (hsigma_one : sigma < 1) (hsigma_gamma : sigma < gamma) {m : ℕ}
    (huniform : F ⊆ uniformDensitySet mu F gamma m)
    {chosen : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hchosen : chosen ⊆ badConvexSets mu F alpha)
    (hselect : ∀ V ∈ badConvexSets mu F alpha, ∃ W ∈ chosen,
      (V ∩ W).Nonempty ∧ Metric.diam V < 2 * Metric.diam W)
    (hsum : ∑' V : chosen, Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2))) ≠ ∞)
    {z : (EuclideanSpace ℝ (Fin 2))} (hzF : z ∈ F) {rho delta : ℝ} (hrho : 0 < rho)
    (hrho_delta : rho < delta)
    (hannulus : ((Metric.ball z rho \ Metric.ball z (sigma * rho / 2)) ∩ F).Nonempty)
    (hpair : ∀ e₁ e₂ : Set (EuclideanSpace ℝ (Fin 2)),
      MeasurableSet e₁ → MeasurableSet e₂ →
      e₁.Nonempty → e₂.Nonempty → 0 < setEDist e₁ e₂ →
      setEDist e₁ e₂ < ENNReal.ofReal delta →
      (∀ x ∈ e₁ ∪ e₂, ∀ r : ℝ, 0 < r → r < 1 / (m + 1 : ℝ) →
        ENNReal.ofReal (2 * sigma * r) < mu (Metric.ball x r)) →
      ∃ v : Set (EuclideanSpace ℝ (Fin 2)),
        IsOpen v ∧ (v ∩ e₁).Nonempty ∧ (v ∩ e₂).Nonempty ∧
        ENNReal.ofReal tau * Metric.ediam v < mu (v \ (e₁ ∪ e₂))) :
    sigma * rho / 2 ≤ Metric.diam (localAttachmentComponent F chosen z rho) := by
  let Q := compactAttachmentUnion F chosen
  let C := localAttachmentComponent F chosen z rho
  have hQ : IsCompact Q := isCompact_compactAttachmentUnion hF halpha hchosen hsum
  have hzQ : z ∈ Q := Or.inl hzF
  have hR_nonneg : 0 ≤ sigma * rho / 2 := by positivity
  have hR_rho : sigma * rho / 2 < rho := by nlinarith
  by_contra hdiam
  have hdiam_lt : Metric.diam C < sigma * rho / 2 := lt_of_not_ge hdiam
  have hzK : z ∈ Q ∩ Metric.closedBall z rho :=
    ⟨hzQ, Metric.mem_closedBall_self hrho.le⟩
  have hzC : z ∈ C := mem_connectedComponentIn hzK
  have hC_bounded : IsBounded C :=
    (hQ.inter_right Metric.isClosed_closedBall).isBounded.subset
      (connectedComponentIn_subset _ _)
  have hC_inner : C ⊆ Metric.ball z (sigma * rho / 2) := by
    intro x hxC
    rw [Metric.mem_ball]
    exact (Metric.dist_le_diam_of_mem hC_bounded hxC hzC).trans_lt hdiam_lt
  obtain ⟨H, hCH, hHQ, hH_clopen, hH_compact⟩ :=
    exists_isClopenWithin_between_connectedComponentIn_closedBall hQ hzQ hR_nonneg
      hR_rho hC_inner
  let e₁ := F ∩ H
  let e₂ := F \ H
  have hzH : z ∈ H := hCH hzC
  have he₁_nonempty : e₁.Nonempty := ⟨z, hzF, hzH⟩
  obtain ⟨w, ⟨hw_outer, hw_inner⟩, hwF⟩ := hannulus
  have hwH : w ∉ H := fun hw ↦ hw_inner (hHQ hw).2
  have he₂_nonempty : e₂.Nonempty := ⟨w, hwF, hwH⟩
  have he₁_compact : IsCompact e₁ := hF.inter_right hH_compact.isClosed
  rcases isOpen_induced_iff.mp hH_clopen.isOpen with ⟨O, hO_open, hO_preimage⟩
  have he₂_eq : e₂ = F \ O := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxO
      apply hx.2
      have hxQ : x ∈ Q := Or.inl hx.1
      have : (⟨x, hxQ⟩ : Q) ∈ Subtype.val ⁻¹' O := hxO
      have hxHsub : (⟨x, hxQ⟩ : Q) ∈ Subtype.val ⁻¹' H := hO_preimage ▸ this
      exact hxHsub
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxH
      have hxQ : x ∈ Q := Or.inl hx.1
      have : (⟨x, hxQ⟩ : Q) ∈ Subtype.val ⁻¹' H := hxH
      have hxOsub : (⟨x, hxQ⟩ : Q) ∈ Subtype.val ⁻¹' O := hO_preimage.symm ▸ this
      have hxO : x ∈ O := hxOsub
      exact hx.2 hxO
  have he₂_compact : IsCompact e₂ := by
    rw [he₂_eq]
    exact hF.diff hO_open
  have he_disjoint : Disjoint e₁ e₂ := by
    rw [disjoint_left]
    intro x hx₁ hx₂
    exact hx₂.2 hx₁.2
  obtain ⟨separation, hseparation_pos, hseparation⟩ :=
    Metric.exists_pos_forall_lt_edist he₁_compact he₂_compact.isClosed he_disjoint
  have hsetEDist_lower : (separation : ℝ≥0∞) ≤ setEDist e₁ e₂ := by
    refine le_iInf fun x ↦ le_iInf fun hx ↦ le_iInf fun y ↦ le_iInf fun hy ↦ ?_
    exact (hseparation x hx y hy).le
  have hsetEDist_pos : 0 < setEDist e₁ e₂ :=
    (ENNReal.coe_pos.mpr hseparation_pos).trans_le hsetEDist_lower
  have hz_e₁ : z ∈ e₁ := ⟨hzF, hzH⟩
  have hw_e₂ : w ∈ e₂ := ⟨hwF, hwH⟩
  have hzw : dist z w < rho := by simpa [dist_comm] using hw_outer
  have hsetEDist_delta : setEDist e₁ e₂ < ENNReal.ofReal delta := by
    calc
      setEDist e₁ e₂ ≤ edist z w := setEDist_le_edist_of_mem hz_e₁ hw_e₂
      _ < ENNReal.ofReal rho := by
        rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hrho]
        exact hzw
      _ < ENNReal.ofReal delta := by
        exact (ENNReal.ofReal_lt_ofReal_iff (hrho.trans hrho_delta)).2 hrho_delta
  have he_partition : e₁ ∪ e₂ = F := by
    ext x
    simp only [e₁, e₂, mem_union, mem_inter_iff, mem_sdiff]
    tauto
  have he₁_measurable : MeasurableSet e₁ := he₁_compact.isClosed.measurableSet
  have he₂_measurable : MeasurableSet e₂ := he₂_compact.isClosed.measurableSet
  have hdensity : ∀ x ∈ e₁ ∪ e₂, ∀ r : ℝ, 0 < r → r < 1 / (m + 1 : ℝ) →
      ENNReal.ofReal (2 * sigma * r) < mu (Metric.ball x r) := by
    intro x hx r hr hrscale
    apply uniformDensitySet_ball_measure_gt hsigma hsigma_gamma
    · exact huniform (he_partition ▸ hx)
    · exact hr
    · exact hrscale
  obtain ⟨U, hU_open, hUe₁, hUe₂, hU_leak⟩ :=
    hpair e₁ e₂ he₁_measurable he₂_measurable he₁_nonempty he₂_nonempty
      hsetEDist_pos hsetEDist_delta hdensity
  have hU_leak_F : ENNReal.ofReal tau * Metric.ediam U < mu (U \ F) := by
    rwa [he_partition] at hU_leak
  have hUF : (U ∩ F).Nonempty := hUe₁.mono <| by
    intro x hx
    exact ⟨hx.1, hx.2.1⟩
  let V := openConvexHull U
  have hV_bad : V ∈ badConvexSets mu F alpha :=
    openConvexHull_mem_badConvexSets halpha_tau hU_open hUF hU_leak_F
  obtain ⟨W, hWchosen, hVW, hdiamVW⟩ := hselect V hV_bad
  have hV_bounded := isBounded_of_mem_badConvexSets halpha hV_bad
  have hV_subset : V ⊆ diameterThickening 2 W :=
    subset_diameterThickening_of_inter_nonempty hV_bounded hVW hdiamVW
  let A := convexAttachment F W
  have hA_subset_Q : A ⊆ Q := by
    intro x hx
    exact Or.inr (mem_iUnion_of_mem ⟨W, hWchosen⟩ hx)
  have hU_subset_V : U ⊆ V := subset_openConvexHull hU_open
  have hUF_subset_A : U ∩ F ⊆ A := by
    intro x hx
    apply subset_closure
    apply subset_convexHull ℝ
    exact ⟨hx.2, hV_subset (hU_subset_V hx.1)⟩
  obtain ⟨x₁, hx₁U, hx₁e₁⟩ := hUe₁
  have hx₁A : x₁ ∈ A := hUF_subset_A ⟨hx₁U, hx₁e₁.1⟩
  have hx₁H : x₁ ∈ H := hx₁e₁.2
  obtain ⟨x₂, hx₂U, hx₂e₂⟩ := hUe₂
  have hx₂A : x₂ ∈ A := hUF_subset_A ⟨hx₂U, hx₂e₂.1⟩
  have hx₂H : x₂ ∉ H := hx₂e₂.2
  have hA_preconnected : IsPreconnected A := (convex_convexAttachment F W).isPreconnected
  have hA_preconnected_Q : IsPreconnected ((↑) ⁻¹' A : Set Q) :=
    LeanPool.Besicovitch.IsPreconnected.preimage_subtype_of_subset hA_preconnected hA_subset_Q
  have hA_meets_H : (((↑) ⁻¹' A : Set Q) ∩ (↑) ⁻¹' H).Nonempty := by
    let xQ : Q := ⟨x₁, hA_subset_Q hx₁A⟩
    exact ⟨xQ, hx₁A, hx₁H⟩
  have hA_subset_H := hA_preconnected_Q.subset_isClopen hH_clopen hA_meets_H
  let x₂Q : Q := ⟨x₂, hA_subset_Q hx₂A⟩
  have hx₂A_Q : x₂Q ∈ ((↑) ⁻¹' A : Set Q) := hx₂A
  exact hx₂H (hA_subset_H hx₂A_Q)

end LeanPool.Besicovitch
