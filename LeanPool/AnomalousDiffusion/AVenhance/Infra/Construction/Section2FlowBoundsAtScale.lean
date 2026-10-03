/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowRegularityCore
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowHigherDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowInverseBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialFlowBounds

/-! Per-scale assembly for the source-form §2 flow bounds. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Construction

/-- The spatial inputs to the material-Jacobian estimate follow directly
from the preceding Section 2 induction hypothesis. -/
theorem section2_spatial_flow_data_from_previous
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1)) :
    Section2SpatialFlowData I Φ hseq m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t ht x
    exact section2_flow_close_from_previous hscales happB2 m hm hprev s t ht x
  · intro s t ht n
    exact section2_flow_jacobian_composed_from_previous hscales happB2 m hm n
      hprev s t ht
  · intro s t ht
    exact section2_composed_jacobian_smooth m s t
  · intro s t ht n hn x J
    exact section2_flow_higher_derivative_from_previous hscales happB2 m hm n hn
      hprev s t ht x J

/-- Assemble the eight fields of `Section2FlowBoundsAtScale`
from the preceding scale. The final parameter is the disjoint
`material_jacobian` field. -/
theorem section2_flow_bounds_at_scale_from_previous
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ} {Cmat : ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1))
    (hmaterial : ∀ s t : ℝ,
      |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n ell : ℕ,
      n + ell ≤ Nstar β → ∀ i j : Fin 2, ∀ x : Vec 2,
        ∀ J : Fin n → Fin 2,
        ‖iteratedFDeriv ℝ n
          (fun y => constructionMaterialIterate
            (fun r z => streamVel (Φ m) (s + r) z) ell
            (fun r z => constructionComposedFlowJacobian hseq m s r z
              (basisVec j) i) t y)
          x (fun k => basisVec (J k))‖ ≤
            Cmat * (epsilon β I.Λ m)⁻¹ ^ n *
              (epsilon β I.Λ m ^ (β - 2)) ^ ell) :
    Section2FlowBoundsAtScale I Φ hseq Cmat m := by
  refine {
    inverse_regbounds := ?_
    flow_close := ?_
    flow_jacobian_composed := ?_
    composed_jacobian_smooth := ?_
    flow_jacobian := ?_
    flow_higher_derivative := ?_
    material_jacobian := hmaterial
    material_jacobian_time_diff := ?_
    inverse_jacobian_time_diff := ?_ }
  · intro s t ht n
    exact section2_flow_inverse_regbounds_from_previous hscales happB2 m hm hprev
      s t ht n
  · intro s t ht x
    exact section2_flow_close_from_previous hscales happB2 m hm hprev s t ht x
  · intro s t ht n
    exact section2_flow_jacobian_composed_from_previous hscales happB2 m hm n
      hprev s t ht
  · intro s t ht
    exact section2_composed_jacobian_smooth m s t
  · intro s t ht n hn
    exact section2_flow_jacobian_from_previous hscales happB2 m hm n hn
      hprev s t ht
  · intro s t ht n hn x J
    exact section2_flow_higher_derivative_from_previous hscales happB2 m hm n hn
      hprev s t ht x J
  · intro s t ht i j x
    exact section2_material_jacobian_time_diff m s t i j x
  · intro s t x
    exact section2_inverse_jacobian_time_diff m t s x

end AVenhance.Infra.Construction

end
