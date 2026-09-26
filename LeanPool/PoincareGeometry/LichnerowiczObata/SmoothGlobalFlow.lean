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

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothManifoldFlow
public import LeanPool.PoincareGeometry.LichnerowiczObata.ContinuousGlobalFlow

/-! # Smooth dependence of complete manifold flows -/

@[expose] public noncomputable section
open Function Manifold Set
open scoped Topology ContDiff

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [HasContDiffBump E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
  {v : Π x : M, TangentSpace I x} (n : ℕ) (hn : n ≠ 0)
  (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) n (fun y => (⟨y, v y⟩ : TangentBundle I M)))
  {F : M → ℝ → M} (hF0 : ∀ x, F x 0 = x) (hF : ∀ x, IsMIntegralCurve (F x) v)

include hn hv hF0 hF

/-- Uniqueness identifies any complete integral-curve family with the
constructed jointly smooth local solutions. -/
theorem exists_contMDiffOn_integralCurve_family (x : M) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∃ δ : ℝ, 0 < δ ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I n (fun z : M × ℝ => F z.1 z.2)
        (V ×ˢ Metric.ball 0 δ) := by
  obtain ⟨V, hV, δ, hδ, α, hc, hα⟩ := exists_smooth_local_manifold_flow n hn (hv x)
  have h1 : (1 : ℕ∞ω) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have he : EqOn (fun z : M × ℝ => F z.1 z.2) α (V ×ˢ Metric.ball 0 δ) := by
    intro z hz
    have ht0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
    have ha : IsMIntegralCurveOn (fun t => α (z.1, t)) v (Ioo (-δ) δ) := by
      simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using (hα z.1 hz.1).2
    have he := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht0 (hv.of_le h1)
      ((hF z.1).isMIntegralCurveOn _) ha ((hF0 z.1).trans (hα z.1 hz.1).1.symm)
    exact he (by simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hz.2)
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.mpr hV, δ, hδ, ?_⟩
  exact (hc.congr he).mono (prod_mono interior_subset subset_rfl)

theorem contMDiffAt_integralCurve_family_zero (x : M) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I n (fun z : M × ℝ => F z.1 z.2) (x, 0) := by
  obtain ⟨V, hVo, hx, δ, hδ, hc⟩ := exists_contMDiffOn_integralCurve_family n hn hv hF0 hF x
  exact hc.contMDiffAt (prod_mem_nhds (hVo.mem_nhds hx) (Metric.ball_mem_nhds 0 hδ))

/-- Compactness gives a common short interval for smooth fixed-time maps. -/
theorem exists_uniform_smoothness_interval_integralCurve_family [CompactSpace M] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Metric.ball 0 δ, ContMDiff I I n (fun x => F x t) := by
  classical
  choose V hVo hx δ hδ hc using exists_contMDiffOn_integralCurve_family n hn hv hF0 hF
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
  intro t ht y
  have hy : y ∈ ⋃ x ∈ s, V x := by rw [hs]; trivial
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp hy
  have ht' : t ∈ Metric.ball 0 (δ x) := Metric.ball_subset_ball (he x hxs) ht
  have hj : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I n (fun z : M × ℝ => F z.1 z.2) (y, t) :=
    (hc x).contMDiffAt
      (prod_mem_nhds ((hVo x).mem_nhds hyx) (Metric.isOpen_ball.mem_nhds ht'))
  exact hj.comp y (contMDiffAt_id.prodMk contMDiffAt_const)

/-- Every fixed-time map is smooth, by iterating uniformly short time steps. -/
theorem contMDiff_integralCurve_family_time [CompactSpace M] (t : ℝ) :
    ContMDiff I I n (fun x => F x t) := by
  have h1 : (1 : ℕ∞ω) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  obtain ⟨ε, hε, hc⟩ := exists_uniform_smoothness_interval_integralCurve_family n hn hv hF0 hF
  obtain ⟨k, hk⟩ := exists_nat_gt (|t| / ε)
  have hkpos : (0 : ℝ) < k := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hε.le) hk
  have hsmall : t / (k : ℝ) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_div, abs_of_pos hkpos]
    apply (div_lt_iff₀ hkpos).mpr
    have hb := (div_lt_iff₀ hε).mp hk
    nlinarith
  have hu := hc (t / (k : ℝ)) hsmall
  have hi (m : ℕ) : ContMDiff I I n (fun x => F x ((m : ℝ) * (t / (k : ℝ)))) := by
    induction m with
    | zero =>
      simp only [Nat.cast_zero, zero_mul]
      convert (contMDiff_id : ContMDiff I I n (id : M → M)) using 1
      funext x
      exact hF0 x
    | succ m ih =>
      have he : (fun x => F x (((m + 1 : ℕ) : ℝ) * (t / (k : ℝ)))) =
          (fun x => F (F x ((m : ℝ) * (t / (k : ℝ)))) (t / (k : ℝ))) := by
        funext x
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
        exact integralCurve_family_add (hv.of_le h1) hF0 hF x _ _
      rw [he]
      exact hu.comp ih
  have ht : (k : ℝ) * (t / (k : ℝ)) = t := by field_simp [hkpos.ne']
  simpa only [ht] using hi k

/-- The complete flow is jointly smooth in the initial point and time. -/
theorem contMDiff_integralCurve_family [CompactSpace M] :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) I n (fun z : M × ℝ => F z.1 z.2) := by
  have h1 : (1 : ℕ∞ω) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  intro z
  have hc := contMDiff_integralCurve_family_time n hn hv hF0 hF z.2
  have hz := contMDiffAt_integralCurve_family_zero n hn hv hF0 hF (F z.1 z.2)
  have hsub : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) n
      (fun w : M × ℝ => w.2 - z.2) :=
    (contDiff_id.sub contDiff_const).contMDiff.comp contMDiff_snd
  have harg : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) n
      (fun w : M × ℝ => (F w.1 z.2, w.2 - z.2)) z :=
    ((hc.comp contMDiff_fst).prodMk hsub) z
  have hj : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I n
      (fun w : M × ℝ => F (F w.1 z.2) (w.2 - z.2)) z := by
    have hz' : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I n
        (fun w : M × ℝ => F w.1 w.2) (F z.1 z.2, z.2 - z.2) := by
      simpa only [sub_self] using hz
    exact hz'.comp z harg
  have he : (fun w : M × ℝ => F (F w.1 z.2) (w.2 - z.2)) =
      (fun w : M × ℝ => F w.1 w.2) := by
    funext w
    rw [← integralCurve_family_add (hv.of_le h1) hF0 hF, sub_add_cancel]
  rwa [he] at hj

omit hn hv in
/-- Infinite smoothness follows from the separately proved finite orders. -/
theorem contMDiff_infty_integralCurve_family [CompactSpace M]
    (hvs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun y => (⟨y, v y⟩ : TangentBundle I M))) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun z : M × ℝ => F z.1 z.2) := by
  rw [contMDiff_infty]
  intro k
  have hk := contMDiff_integralCurve_family (k + 1) (Nat.succ_ne_zero k)
    (hvs.of_le (WithTop.coe_le_coe.2 (le_top : ((k + 1 : ℕ) : ℕ∞) ≤ ⊤))) hF0 hF
  exact hk.of_le (by exact_mod_cast Nat.le_succ k)

omit hn hv hF0 hF in
/-- A smooth vector field on a compact boundaryless manifold has a jointly
smooth complete flow. Existence and smooth dependence are both conclusions. -/
theorem exists_smooth_global_manifold_flow [CompactSpace M]
    (hvs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun y => (⟨y, v y⟩ : TangentBundle I M))) :
    ∃ G : M → ℝ → M, ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun z : M × ℝ => G z.1 z.2) ∧
      (∀ x, G x 0 = x) ∧ ∀ x, IsMIntegralCurve (G x) v := by
  classical
  choose G hG0 hG using exists_global_integralCurve_compact (hvs.of_le (by simp))
  exact ⟨G, contMDiff_infty_integralCurve_family hG0 hG hvs, hG0, hG⟩

end LichnerowiczObata
