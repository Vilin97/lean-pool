/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Tactic

/-! # Uniform local ODE intervals inside a prescribed chart domain

The interval is uniform over a neighborhood of initial points. This uses
joint continuity of the Picard–Lindelöf flow, not pointwise existence alone.
-/

@[expose] public noncomputable section
open Set Metric
open scoped Topology

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A jointly continuous local flow stays inside any prescribed
neighborhood of the central initial point on a common time interval. -/
theorem exists_uniform_chart_flow {v : E → E} {x : E}
    (hv : ContDiffAt ℝ 1 v x) {U : Set E} (hU : U ∈ 𝓝 x) :
    ∃ V ∈ 𝓝 x, ∃ δ : ℝ, 0 < δ ∧
      ∃ α : E × ℝ → E, ContinuousOn α (V ×ˢ ball 0 δ) ∧
        ∀ y ∈ V, α (y, 0) = y ∧
          ∀ t ∈ ball 0 δ, α (y, t) ∈ U ∧
            HasDerivAt (fun s => α (y, s)) (v (α (y, t))) t := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hv
  obtain ⟨α, hα, hc⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hdom : closedBall x (r : ℝ) ×ˢ Icc (0 - ε) (0 + ε) ∈ 𝓝 (x, (0 : ℝ)) :=
    prod_mem_nhds (closedBall_mem_nhds x hr) (Icc_mem_nhds (by linarith) (by linarith))
  have hc' := hc.continuousAt hdom
  have hα0 : α (x, (0 : ℝ)) = x := (hα x (mem_closedBall_self r.2)).1
  have hu : α ⁻¹' U ∈ 𝓝 (x, (0 : ℝ)) := by
    apply hc'
    simpa only [hα0] using hU
  have hi : closedBall x (r : ℝ) ×ˢ Ioo (0 - ε) (0 + ε) ∈ 𝓝 (x, (0 : ℝ)) :=
    prod_mem_nhds (closedBall_mem_nhds x hr) (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨V, hV, T, hT, hsub⟩ := mem_nhds_prod_iff.mp (Filter.inter_mem hu hi)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hT
  refine ⟨V, hV, δ, hδ, α, hc.mono ?_, ?_⟩
  · intro z hz
    have hz' := hsub (show z ∈ V ×ˢ T from ⟨hz.1, hball hz.2⟩)
    exact ⟨hz'.2.1, Ioo_subset_Icc_self hz'.2.2⟩
  intro y hy
  have hy0 := hsub (show (y, (0 : ℝ)) ∈ V ×ˢ T from ⟨hy, mem_of_mem_nhds hT⟩)
  refine ⟨(hα y hy0.2.1).1, ?_⟩
  intro t ht
  have hyt := hsub (show (y, t) ∈ V ×ˢ T from ⟨hy, hball ht⟩)
  exact ⟨hyt.1, ((hα y hyt.2.1).2 t (Ioo_subset_Icc_self hyt.2.2)).hasDerivAt
    (Icc_mem_nhds hyt.2.2.1 hyt.2.2.2)⟩

/-- Nearby initial values have solutions on a common interval which stay
inside any prescribed neighborhood of the central initial point. -/
theorem exists_uniform_chart_ode {v : E → E} {x : E}
    (hv : ContDiffAt ℝ 1 v x) {U : Set E} (hU : U ∈ 𝓝 x) :
    ∃ V ∈ 𝓝 x, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ V, ∃ γ : ℝ → E, γ 0 = y ∧
        ∀ t ∈ ball 0 δ, γ t ∈ U ∧ HasDerivAt γ (v (γ t)) t := by
  obtain ⟨V, hV, δ, hδ, α, hc, hα⟩ := exists_uniform_chart_flow hv hU
  exact ⟨V, hV, δ, hδ, fun y hy => ⟨fun t => α (y, t), hα y hy⟩⟩

end LichnerowiczObata
