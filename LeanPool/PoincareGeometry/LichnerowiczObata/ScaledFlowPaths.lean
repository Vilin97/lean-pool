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

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothPicardOperator

/-! # Continuous unit-interval paths from a local flow -/

@[expose] public noncomputable section
open Set Metric
open scoped Topology ContDiff

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Time scaling by a unit-interval parameter stays in the local time ball. -/
theorem mul_unitInterval_mem_ball {τ δ : ℝ} (hτ : τ ∈ ball 0 δ)
    (s : Icc (0 : ℝ) 1) : τ * (s : ℝ) ∈ ball 0 δ := by
  simp only [mem_ball, Real.dist_eq, sub_zero] at hτ ⊢
  rw [abs_mul, abs_of_nonneg s.property.1]
  exact (mul_le_of_le_one_right (abs_nonneg τ) s.property.2).trans_lt hτ

/-- A local flow as a unit-interval path, with zero used only outside the
region where continuity is available. -/
def scaledFlowPath (α : E × ℝ → E) (z : E × ℝ) : C(Icc (0 : ℝ) 1, E) :=
  ContinuousMap.mkD (fun s : Icc (0 : ℝ) 1 => α (z.1, z.2 * (s : ℝ))) 0

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuousOn_scaledFlow_uncurry {α : E × ℝ → E} {V : Set E} {δ : ℝ}
    (hc : ContinuousOn α (V ×ˢ ball 0 δ)) :
    ContinuousOn (fun z : (E × ℝ) × Icc (0 : ℝ) 1 => α (z.1.1, z.1.2 * (z.2 : ℝ)))
      ((V ×ˢ ball 0 δ) ×ˢ univ) := by
  have hm : Continuous (fun z : (E × ℝ) × Icc (0 : ℝ) 1 =>
      (z.1.1, z.1.2 * (z.2 : ℝ))) := by fun_prop
  exact hc.comp hm.continuousOn (fun z hz => ⟨hz.1.1, mul_unitInterval_mem_ball hz.1.2 z.2⟩)

/-- Joint continuity of the original flow gives continuity in the sup-norm
path space; no differentiability of the flow is used. -/
theorem continuousOn_scaledFlowPath {α : E × ℝ → E} {V : Set E} {δ : ℝ}
    (hc : ContinuousOn α (V ×ˢ ball 0 δ)) :
    ContinuousOn (scaledFlowPath α) (V ×ˢ ball 0 δ) :=
  ContinuousMap.continuousOn_mkD_of_uncurry _ 0 (continuousOn_scaledFlow_uncurry hc)

theorem scaledFlowPath_apply {α : E × ℝ → E} {V : Set E} {δ : ℝ}
    (hc : ContinuousOn α (V ×ˢ ball 0 δ)) {z : E × ℝ} (hz : z ∈ V ×ˢ ball 0 δ)
    (s : Icc (0 : ℝ) 1) : scaledFlowPath α z s = α (z.1, z.2 * (s : ℝ)) := by
  have hs : Continuous (fun s : Icc (0 : ℝ) 1 => α (z.1, z.2 * (s : ℝ))) :=
    (continuousOn_scaledFlow_uncurry hc).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hz, trivial⟩)
  simp only [scaledFlowPath, ContinuousMap.mkD_of_continuous hs, ContinuousMap.coe_mk]

/-- The differential equation implies the path-space Picard equation. -/
theorem scaledFlowPath_picard {α : E × ℝ → E} {V : Set E} {δ : ℝ}
    (v : C(E, E)) (hc : ContinuousOn α (V ×ˢ ball 0 δ))
    (hzero : ∀ y ∈ V, α (y, 0) = y)
    (hode : ∀ y ∈ V, ∀ t ∈ ball 0 δ,
      HasDerivAt (fun s => α (y, s)) (v (α (y, t))) t)
    {z : E × ℝ} (hz : z ∈ V ×ˢ ball 0 δ) :
    picardPathOperator v (z, scaledFlowPath α z) = scaledFlowPath α z := by
  let u := continuousMapSuperposition v (scaledFlowPath α z)
  have hu (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      unitPathExtend u t = v (α (z.1, z.2 * t)) := by
    have hp : projIcc 0 1 zero_le_one t = (⟨t, ht⟩ : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      simp [projIcc, ht.1, ht.2]
    simp only [unitPathExtend, hp]
    change v (scaledFlowPath α z ⟨t, ht⟩) = _
    rw [scaledFlowPath_apply hc hz]
  apply ContinuousMap.ext
  intro r
  have hr (t : ℝ) (ht : t ∈ uIcc 0 (r : ℝ)) : t ∈ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le r.property.1] at ht
    exact ⟨ht.1, ht.2.trans r.property.2⟩
  have hd : ∀ t ∈ uIcc 0 (r : ℝ),
      HasDerivAt (fun s => α (z.1, z.2 * s)) (z.2 • unitPathExtend u t) t := by
    intro t ht
    rw [hu t (hr t ht)]
    simpa [Function.comp_def] using (hode z.1 hz.1 (z.2 * t)
      (mul_unitInterval_mem_ball hz.2 ⟨t, hr t ht⟩)).scomp t
        ((hasDerivAt_id t).const_mul z.2)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_unitPathExtend u).const_smul z.2).intervalIntegrable 0 (r : ℝ))
  rw [intervalIntegral.integral_smul] at hi
  simp only [mul_zero, hzero z.1 hz.1] at hi
  change z.1 + z.2 • (∫ t in 0..(r : ℝ), unitPathExtend u t) = scaledFlowPath α z r
  rw [hi, add_sub_cancel, scaledFlowPath_apply hc hz]

/-- Smooth dependence of the scaled ODE paths, derived from continuity and
the differential equation rather than assumed as flow regularity. -/
theorem contDiffAt_scaledFlowPath_zero (n : ℕ) (hn : n ≠ 0)
    (v : C(E, E)) (hv : ContDiff ℝ n v)
    {α : E × ℝ → E} {V : Set E} {δ : ℝ} {x : E}
    (hV : V ∈ 𝓝 x) (hδ : 0 < δ)
    (hc : ContinuousOn α (V ×ˢ ball 0 δ))
    (hzero : ∀ y ∈ V, α (y, 0) = y)
    (hode : ∀ y ∈ V, ∀ t ∈ ball 0 δ,
      HasDerivAt (fun s => α (y, s)) (v (α (y, t))) t) :
    ContDiffAt ℝ n (scaledFlowPath α) (x, 0) := by
  have hN : V ×ˢ ball (0 : ℝ) δ ∈ 𝓝 (x, (0 : ℝ)) :=
    prod_mem_nhds hV (ball_mem_nhds 0 hδ)
  apply contDiffAt_picard_solution_zero n hn v hv
  · exact (continuousOn_scaledFlowPath hc _ (mem_of_mem_nhds hN)).continuousAt hN
  · exact Filter.eventually_of_mem hN (fun z hz => scaledFlowPath_picard v hc hzero hode hz)

/-- Evaluation at the endpoint recovers smoothness of the actual local flow. -/
theorem contDiffAt_flow_zero (n : ℕ) (hn : n ≠ 0)
    (v : C(E, E)) (hv : ContDiff ℝ n v)
    {α : E × ℝ → E} {V : Set E} {δ : ℝ} {x : E}
    (hV : V ∈ 𝓝 x) (hδ : 0 < δ)
    (hc : ContinuousOn α (V ×ˢ ball 0 δ))
    (hzero : ∀ y ∈ V, α (y, 0) = y)
    (hode : ∀ y ∈ V, ∀ t ∈ ball 0 δ,
      HasDerivAt (fun s => α (y, s)) (v (α (y, t))) t) :
    ContDiffAt ℝ n α (x, 0) := by
  let e : C(Icc (0 : ℝ) 1, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ ⟨1, by simp⟩
  have he := e.contDiff.contDiffAt.comp (x, (0 : ℝ))
    (contDiffAt_scaledFlowPath_zero n hn v hv hV hδ hc hzero hode)
  apply he.congr_of_eventuallyEq
  filter_upwards [prod_mem_nhds hV (ball_mem_nhds 0 hδ)] with z hz
  change α z = scaledFlowPath α z ⟨1, by simp⟩
  simp [scaledFlowPath_apply hc hz]

end LichnerowiczObata
