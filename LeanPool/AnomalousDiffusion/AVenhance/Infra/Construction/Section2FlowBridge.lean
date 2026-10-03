/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialFlowBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialFlowComposition
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialAuxiliaryInduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialJacobianFromP
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowBoundsAtScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2JointInduction

/-! Bridges from the global source-form flow package to the per-scale
hypotheses consumed by the Section 2 induction. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Construction

/-- The material-Jacobian display at one scale follows from the actual
all-order velocity material jets and the spatial displays at that scale. -/
theorem section2_flow_bounds_at_scale_from_induction
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ} {K : ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (hind : ∀ m : ℕ, Section2StreamInductionHypothesis (Φ := Φ) R M m)
    (hK : 1 ≤ K)
    (hlevels : MaterialAuxJetLevels I Φ (2 * Nstar β + 1) K (Nstar β))
    (m : ℕ) (hm : 1 ≤ m) :
    Section2FlowBoundsAtScale I Φ hseq (section2MaterialJacobianConstant β K) m := by
  have hspatial := section2_spatial_flow_data_from_previous hscales happB2 m hm
    (hind (m - 1))
  have hmaterial := section2_material_jacobian_of_material_levels hK hlevels hspatial
  exact section2_flow_bounds_at_scale_from_previous hscales happB2 m hm
    (hind (m - 1)) hmaterial

/-- Assemble `FlowBoundsData` from the same induction that proves the first
stream-regularity increment display. In particular, each positive-scale material field is
derived from the previous scale's stream induction hypothesis. -/
theorem section2_flow_bounds_of_stream_induction
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (hind : ∀ m : ℕ, Section2StreamInductionHypothesis (Φ := Φ) R M m)
    (hincrement : StreamIncrementBounds I Φ) :
    ∃ Cmat : ℝ, 1 ≤ Cmat ∧ FlowBoundsData I Φ hseq Cmat := by
  let Creg := 11 + 768 / (β - 1)
  have hreg : StreamRegularityBounds Creg I Φ :=
    stream_regularity_bounds_of_increment_bounds hseq hincrement
  obtain ⟨K, hK, hlevels⟩ :=
    material_aux_jet_levels_all_orders_of_A3 I hseq hreg
  let Cmat := section2MaterialJacobianConstant β K
  have hCmat : 1 ≤ Cmat := by
    dsimp [Cmat]
    exact section2MaterialJacobianConstant_ge_one hK
  have hflow : FlowBoundsData I Φ hseq Cmat := by
    refine ⟨hCmat, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro m hm s t ht n
      exact (section2_flow_bounds_at_scale_from_induction hscales happB2 hind
        hK hlevels m hm).inverse_regbounds s t ht n
    · intro m hm s t ht x
      exact (section2_flow_bounds_at_scale_from_induction hscales happB2 hind
        hK hlevels m hm).flow_close s t ht x
    · intro m hm s t ht n
      exact (section2_flow_bounds_at_scale_from_induction hscales happB2 hind
        hK hlevels m hm).flow_jacobian_composed s t ht n
    · intro m hm s t ht
      exact (section2_flow_bounds_at_scale_from_induction hscales happB2 hind
        hK hlevels m hm).composed_jacobian_smooth s t ht
    · intro m hm s t ht n hn
      exact (section2_flow_bounds_at_scale_from_induction hscales happB2 hind
        hK hlevels m hm).flow_jacobian s t ht n hn
    · intro m hm s t ht n hn x J
      exact (section2_flow_bounds_at_scale_from_induction hscales happB2 hind
        hK hlevels m hm).flow_higher_derivative s t ht n hn x J
    · intro m hm s t ht n ell hnell i j x J
      exact (section2_flow_bounds_at_scale_from_induction hscales happB2 hind
        hK hlevels m hm).material_jacobian s t ht n ell hnell i j x J
    · intro m hm s t ht i j x
      exact section2_material_jacobian_time_diff m s t i j x
    · intro m hm s t x
      exact section2_inverse_jacobian_time_diff m t s x
    · intro m hm t s x
      exact constructionFlowInv_hasDerivAt m t s x
  exact ⟨Cmat, hCmat, hflow⟩

/-- The joint induction now proves both `e.indyhyp` and the global source-form
flow/material package, with no full per-scale hypothesis assumed. -/
theorem section2_joint_induction_with_derived_flow
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M) :
    (∀ m : ℕ, Section2StreamInductionHypothesis (Φ := Φ) R M m) ∧
      StreamIncrementBounds I Φ ∧
      (∃ Cmat : ℝ, 1 ≤ Cmat ∧ FlowBoundsData I Φ hseq Cmat ∧
        (∀ m : ℕ, 1 ≤ m →
          CMaterialGoalSourceData I Φ hseq
            (materialFlowCompositionConstant β Cmat) m)) := by
  obtain ⟨hind, hincrement⟩ := section2_joint_induction hscales happB2
  obtain ⟨Cmat, hCmat, hflow⟩ :=
    section2_flow_bounds_of_stream_induction hscales happB2 hind hincrement
  exact ⟨hind, hincrement, Cmat, hCmat, hflow,
    fun m hm => c_material_goal_source_of_flow_bounds hflow hm⟩

end AVenhance.Infra.Construction

end
