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

public import LeanPool.PoincareGeometry.LichnerowiczObata.UniformManifoldODE

/-! # Continuous dependence of complete manifold flows -/

@[expose] public noncomputable section
open Function Manifold Set
open scoped Topology ContDiff

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless] [T2Space M]
  {v : Π x : M, TangentSpace I x}
  (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y => (⟨y, v y⟩ : TangentBundle I M)))
  {F : M → ℝ → M} (hF0 : ∀ x, F x 0 = x) (hF : ∀ x, IsMIntegralCurve (F x) v)

include hv hF0 hF

/-- Any complete integral-curve family agrees with the jointly continuous
local flow supplied by Picard–Lindelöf. -/
theorem exists_continuousOn_integralCurve_family (x : M) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∃ δ : ℝ, 0 < δ ∧
      ContinuousOn (fun z : M × ℝ => F z.1 z.2) (V ×ˢ Metric.ball 0 δ) := by
  obtain ⟨V, hV, δ, hδ, α, hc, hα⟩ := exists_uniform_manifold_flow_contMDiff (hv x)
  have he : EqOn (fun z : M × ℝ => F z.1 z.2) α (V ×ˢ Metric.ball 0 δ) := by
    intro z hz
    have ht0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
    have ha : IsMIntegralCurveOn (fun t => α (z.1, t)) v (Ioo (-δ) δ) := by
      simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using (hα z.1 hz.1).2.1
    have he := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht0 hv
      ((hF z.1).isMIntegralCurveOn _) ha ((hF0 z.1).trans (hα z.1 hz.1).1.symm)
    exact he (by simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hz.2)
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.mpr hV, δ, hδ, ?_⟩
  exact (hc.congr he).mono (prod_mono interior_subset subset_rfl)

/-- Joint continuity at time zero follows from local flow uniqueness. -/
theorem continuousAt_integralCurve_family_zero (x : M) :
    ContinuousAt (fun z : M × ℝ => F z.1 z.2) (x, 0) := by
  obtain ⟨V, hVo, hx, δ, hδ, hc⟩ := exists_continuousOn_integralCurve_family hv hF0 hF x
  exact hc.continuousAt (prod_mem_nhds (hVo.mem_nhds hx) (Metric.ball_mem_nhds 0 hδ))

/-- Compactness makes the short-time continuous-dependence interval uniform
over all starting points. -/
theorem exists_uniform_continuity_interval_integralCurve_family [CompactSpace M] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Metric.ball 0 δ, Continuous (fun x => F x t) := by
  classical
  choose V hVo hx δ hδ hc using exists_continuousOn_integralCurve_family hv hF0 hF
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover V (fun x => (hVo x).mem_nhds (hx x))
  have hmin : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, ε ≤ δ x := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert x s hx ih =>
      obtain ⟨ε, hε, he⟩ := ih
      refine ⟨min ε (δ x), lt_min hε (hδ x), ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (he y hy)
  obtain ⟨ε, hε, he⟩ := hmin
  refine ⟨ε, hε, ?_⟩
  intro t ht
  apply continuous_iff_continuousAt.mpr
  intro y
  have hy : y ∈ ⋃ x ∈ s, V x := by rw [hs]; trivial
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp hy
  have ht' : t ∈ Metric.ball 0 (δ x) := Metric.ball_subset_ball (he x hxs) ht
  have hj : ContinuousAt (fun z : M × ℝ => F z.1 z.2) (y, t) := (hc x).continuousAt
    (prod_mem_nhds ((hVo x).mem_nhds hyx) (Metric.isOpen_ball.mem_nhds ht'))
  exact hj.comp' (f := fun z : M => (z, t)) (show ContinuousAt (fun z : M => (z, t)) y from
    (continuous_id.prodMk continuous_const).continuousAt)

omit [CompleteSpace E] in
/-- The group law is forced by uniqueness of global integral curves. -/
theorem integralCurve_family_add (x : M) (s t : ℝ) :
    F x (s + t) = F (F x t) s := by
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv
    ((hF x).comp_add t) (hF (F x t)) (by simp only [Function.comp_apply, zero_add, hF0])
  exact congrFun he s

/-- Every fixed-time map of a complete C1 flow on a compact manifold is
continuous, by iterating uniformly short continuous time steps. -/
theorem continuous_integralCurve_family_time [CompactSpace M] (t : ℝ) :
    Continuous (fun x => F x t) := by
  obtain ⟨ε, hε, hc⟩ := exists_uniform_continuity_interval_integralCurve_family hv hF0 hF
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / ε)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hε.le) hn
  have hsmall : t / (n : ℝ) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_div, abs_of_pos hnpos]
    apply (div_lt_iff₀ hnpos).mpr
    have hb := (div_lt_iff₀ hε).mp hn
    nlinarith
  have hu := hc (t / (n : ℝ)) hsmall
  have hi (m : ℕ) : Continuous (fun x => F x ((m : ℝ) * (t / (n : ℝ)))) := by
    induction m with
    | zero =>
      simp only [Nat.cast_zero, zero_mul]
      convert (continuous_id : Continuous (id : M → M)) using 1
      funext x
      exact hF0 x
    | succ m ih =>
      have he : (fun x => F x (((m + 1 : ℕ) : ℝ) * (t / (n : ℝ)))) =
          (fun x => F (F x ((m : ℝ) * (t / (n : ℝ)))) (t / (n : ℝ))) := by
        funext x
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
        exact integralCurve_family_add hv hF0 hF x _ _
      rw [he]
      exact hu.comp ih
  have ht : (n : ℝ) * (t / (n : ℝ)) = t := by field_simp [hnpos.ne']
  simpa only [ht] using hi n

/-- A complete integral-curve family of a C1 field on a compact manifold
depends jointly continuously on the initial point and time. -/
theorem continuous_integralCurve_family [CompactSpace M] :
    Continuous (fun z : M × ℝ => F z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hc := continuous_integralCurve_family_time hv hF0 hF z.2
  have hz := continuousAt_integralCurve_family_zero hv hF0 hF (F z.1 z.2)
  have harg : ContinuousAt (fun w : M × ℝ => (F w.1 z.2, w.2 - z.2)) z :=
    ((hc.comp continuous_fst).prodMk (continuous_snd.sub continuous_const)).continuousAt
  have hj : ContinuousAt (fun w : M × ℝ => F (F w.1 z.2) (w.2 - z.2)) z := by
    have hz' : ContinuousAt (fun w : M × ℝ => F w.1 w.2) (F z.1 z.2, z.2 - z.2) := by
      simpa only [sub_self] using hz
    exact hz'.comp' (f := fun w : M × ℝ => (F w.1 z.2, w.2 - z.2)) harg
  have he : (fun w : M × ℝ => F (F w.1 z.2) (w.2 - z.2)) =
      (fun w : M × ℝ => F w.1 w.2) := by
    funext w
    rw [← integralCurve_family_add hv hF0 hF, sub_add_cancel]
  rwa [he] at hj

omit hF0 hF in
/-- A C1 field on a compact boundaryless manifold has a jointly continuous
complete flow. Neither completeness nor continuous dependence is assumed. -/
theorem exists_continuous_global_manifold_flow [CompactSpace M] :
    ∃ G : M → ℝ → M, Continuous (fun z : M × ℝ => G z.1 z.2) ∧
      (∀ x, G x 0 = x) ∧ ∀ x, IsMIntegralCurve (G x) v := by
  classical
  choose G hG0 hG using exists_global_integralCurve_compact hv
  exact ⟨G, continuous_integralCurve_family hv hG0 hG, hG0, hG⟩

end LichnerowiczObata
