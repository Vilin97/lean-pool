/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.LocalVectorFieldExtension
public import LeanPool.PoincareGeometry.LichnerowiczObata.ScaledFlowPaths
public import LeanPool.PoincareGeometry.LichnerowiczObata.UniformChartODE

/-! # Jointly smooth local flows for locally smooth vector fields -/

@[expose] public noncomputable section
open Set Metric Filter
open scoped Topology ContDiff

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [HasContDiffBump E]

/-- A finite-order smooth vector field has a jointly smooth local flow on a
uniform product neighborhood, staying in any prescribed neighborhood. -/
theorem exists_smooth_local_flow (n : ℕ) (hn : n ≠ 0) {v : E → E} {x : E}
    (hv : ContDiffAt ℝ n v x) {U : Set E} (hU : U ∈ 𝓝 x) :
    ∃ V ∈ 𝓝 x, ∃ δ : ℝ, 0 < δ ∧
      ∃ α : E × ℝ → E, ContDiffOn ℝ n α (V ×ˢ ball 0 δ) ∧
        ∀ y ∈ V, α (y, 0) = y ∧
          ∀ t ∈ ball 0 δ, α (y, t) ∈ U ∧
            HasDerivAt (fun s => α (y, s)) (v (α (y, t))) t := by
  obtain ⟨w, hw, heq⟩ := exists_contDiff_extension n hv
  have h1 : (1 : ℕ∞ω) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  obtain ⟨V, hV, δ, hδ, α, hc, hα⟩ :=
    exists_uniform_chart_flow (hw.of_le h1).contDiffAt (inter_mem hU heq)
  have hs : ContDiffAt ℝ n α (x, 0) :=
    contDiffAt_flow_zero n hn ⟨w, hw.continuous⟩ hw hV hδ hc
      (fun y hy => (hα y hy).1) (fun y hy t ht => (hα y hy).2 t ht |>.2)
  obtain ⟨S, hS, hsS⟩ := hs.contDiffOn le_rfl (by simp)
  obtain ⟨W, hW, T, hT, hsub⟩ := mem_nhds_prod_iff.mp
    (inter_mem (prod_mem_nhds hV (ball_mem_nhds 0 hδ)) hS)
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
  have hdom : W ×ˢ ball (0 : ℝ) ε ⊆ (V ×ˢ ball 0 δ) ∩ S :=
    fun z hz => hsub ⟨hz.1, hεT hz.2⟩
  refine ⟨W, hW, ε, hε, α, hsS.mono (fun z hz => (hdom hz).2), ?_⟩
  intro y hy
  have hyV : y ∈ V := (hdom (show (y, (0 : ℝ)) ∈ W ×ˢ ball 0 ε from
    ⟨hy, mem_ball_self hε⟩)).1.1
  refine ⟨(hα y hyV).1, ?_⟩
  intro t ht
  have ha := (hα y hyV).2 t (hdom (show (y, t) ∈ W ×ˢ ball 0 ε from ⟨hy, ht⟩)).1.2
  exact ⟨ha.1.1, ha.1.2 ▸ ha.2⟩

end LichnerowiczObata
