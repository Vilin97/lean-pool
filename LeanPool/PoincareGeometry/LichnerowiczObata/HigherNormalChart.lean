/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalRayNormalization
public import LeanPool.PoincareGeometry.LichnerowiczObata.GeodesicNormalRadial

/-! # Arbitrary finite-order normal charts with metric identities -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [PreconnectedSpace M]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

omit [PreconnectedSpace M] in
/-- A fixed actual geodesic endpoint is smooth at zero velocity. Higher-order
flows may have different time domains; time rescaling and ODE uniqueness
identify their endpoint germs with the fixed endpoint. -/
theorem contDiffAt_coordinate_geodesic_endpoint_zero
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V)
    (hzV : (z, (0 : E)) ∈ V) {δ t : ℝ} (htpos : 0 < t)
    (htime : t ∈ Metric.ball 0 δ)
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun u => α (q, u)) (coordinateGeodesicSpray cov b c (α (q, s))) s) :
    ContDiffAt ℝ ∞ (fun v : E => (α ((z, v), t)).1) 0 := by
  apply contDiffAt_infty.mpr
  intro n
  obtain ⟨W, hW, hzW, ε, hε, β, hβ, hβsol, _⟩ :=
    exists_stationary_coordinate_geodesic_flow_of_order (n + 2) (by omega) cov hm ht b c hz
  let τ := ε / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτε : τ < ε := by dsimp [τ]; linarith
  let r := t / τ
  have hr : 0 < r := div_pos htpos hτ
  have hrt : r * τ = t := div_mul_cancel₀ t hτ.ne'
  have htδ : t < δ := by simpa [Real.dist_eq, abs_of_pos htpos] using htime
  let η := min ε (δ / r)
  have hτη : τ < η := lt_min hτε ((lt_div_iff₀ hr).mpr (by nlinarith [hrt]))
  have hη : 0 < η := hτ.trans hτη
  have hsub (s : ℝ) (hs : s ∈ Metric.ball (0 : ℝ) η) :
      s ∈ Metric.ball (0 : ℝ) ε ∧ r * s ∈ Metric.ball (0 : ℝ) δ := by
    have hsabs : |s| < η := by simpa [Real.dist_eq] using hs
    refine ⟨?_, ?_⟩
    · simpa [Real.dist_eq] using hsabs.trans_le (min_le_left ε (δ / r))
    · have hsd : |s| < δ / r := hsabs.trans_le (min_le_right ε (δ / r))
      have hm := (lt_div_iff₀ hr).mp hsd
      simpa [Real.dist_eq, abs_mul, abs_of_pos hr, mul_comm] using hm
  have hnearV : ∀ᶠ v : E in 𝓝 0, (z, v) ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hV.mem_nhds hzV)
  have hnearW : ∀ᶠ v : E in 𝓝 0, (z, r • v) ∈ W := by
    have hc : Continuous (fun v : E => (z, r • v)) :=
      continuous_const.prodMk (continuous_const.smul continuous_id)
    exact hc.continuousAt.preimage_mem_nhds (hW.mem_nhds (by simpa using hzW))
  have heq : (fun v : E => (α ((z, v), t)).1) =ᶠ[𝓝 0]
      (fun v : E => (β ((z, r • v), τ)).1) := by
    filter_upwards [hnearV, hnearW] with v hv hw
    have he := coordinate_geodesic_rescale_eqOn cov hm ht b c
      (α := fun s => α ((z, v), s)) (β := fun s => β ((z, r • v), s)) r
      Metric.isOpen_ball (convex_ball (0 : ℝ) η).isPreconnected (Metric.mem_ball_self hη)
      (fun s hs => ((hβsol _ hw).2 s (hsub s hs).1).1)
      (fun s hs => ((hsol _ hv).2 (r * s) (hsub s hs).2).2)
      (fun s hs => ((hβsol _ hw).2 s (hsub s hs).1).2)
      (by rw [(hβsol _ hw).1, (hsol _ hv).1])
      (by simpa [Real.dist_eq, abs_of_pos hτ] using hτη : τ ∈ Metric.ball 0 η)
    simpa only [hrt] using (congrArg Prod.fst he).symm
  have hτmem : τ ∈ Metric.ball (0 : ℝ) ε := by
    simpa [Real.dist_eq, abs_of_pos hτ] using hτε
  have hpt : ((z, r • (0 : E)), τ) ∈ W ×ˢ Metric.ball 0 ε := by
    simpa using And.intro hzW hτmem
  have hi : ContDiffAt ℝ (n + 2) (fun v : E => ((z, r • v), τ)) 0 :=
    (contDiffAt_const.prodMk (contDiffAt_const.smul contDiffAt_id)).prodMk contDiffAt_const
  have hh := ((hβ.contDiffAt ((hW.prod Metric.isOpen_ball).mem_nhds hpt)).comp 0 hi).fst
  exact (hh.of_le (by exact_mod_cast (show n ≤ n + 2 by omega))).congr_of_eventuallyEq heq

omit [PreconnectedSpace M] in
/-- The endpoint inverse retains the differentiability order of the flow. -/
theorem exists_geodesic_endpoint_local_inverse_of_order
    (n : ℕ) (hn : 2 ≤ n)
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {U : Set ((E × E) × ℝ)}
    (hU : IsOpen U) (hα : ContDiffOn ℝ n α U)
    (hode : ∀ q ∈ U, HasDerivAt (fun s => α (q.1, s))
      (coordinateGeodesicSpray cov b c (α q)) q.2)
    (hinit : (fun q => α (q, 0)) =ᶠ[𝓝 (z, (0 : E))] id)
    {T : Set ℝ} (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hmem : ∀ s ∈ T, ((z, 0), s) ∈ U)
    (hrest : ∀ s ∈ T, α ((z, 0), s) = (z, 0))
    {t : ℝ} (htime : t ∈ T) (htne : t ≠ 0) :
    ∃ e : OpenPartialHomeomorph E E,
      (e : E → E) = (fun v => (α ((z, v), t)).1) ∧
      0 ∈ e.source ∧ e 0 = z ∧ ContDiffAt ℝ n e.symm z := by
  have hn2 : (2 : ℕ∞ω) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℕ∞ω) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hn2)
  let f : E → E := fun v => (α ((z, v), t)).1
  let A : E ≃L[ℝ] E := (Units.mk0 t htne) • ContinuousLinearEquiv.refl ℝ E
  have hA : (A : E →L[ℝ] E) = t • ContinuousLinearMap.id ℝ E := by
    ext v
    rfl
  have hi : ContDiffAt ℝ n (fun v : E => ((z, v), t)) 0 :=
    (contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const
  have hf : ContDiffAt ℝ n f 0 :=
    ((hα.contDiffAt (hU.mem_nhds (hmem t htime))).comp 0 hi).fst
  have hd : HasFDerivAt f (A : E →L[ℝ] E) 0 := by
    rw [hA]
    exact hasFDerivAt_geodesic_endpoint_zero cov hm ht b c hz hU (hα.of_le hn2) hode hinit
      hT hconn hzero hmem hrest htime
  have hfzero : f 0 = z := congrArg Prod.fst (hrest t htime)
  refine ⟨hf.toOpenPartialHomeomorph f hd hn0, rfl,
    hf.mem_toOpenPartialHomeomorph_source hd hn0, hfzero, ?_⟩
  have hinv := hf.to_localInverse hd hn0
  rw [hfzero] at hinv
  exact hinv


/-- Normal charts retain the radial and metric identities and any prescribed
finite order on their source. The same chosen chart and its inverse are smooth
at the pole, by uniqueness of rescaled geodesics. -/
theorem exists_obata_normal_metric_chart_of_order
    (n : ℕ) (hn : 2 ≤ n)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a) :
    ∃ t : ℝ, 0 < t ∧ ∃ e : OpenPartialHomeomorph E E,
      0 ∈ e.source ∧ e 0 = z ∧
      HasFDerivAt e (t • ContinuousLinearMap.id ℝ E) 0 ∧
      ContDiffAt ℝ ∞ e 0 ∧ ContDiffAt ℝ ∞ e.symm z ∧
      (∀ u ∈ e.source, ContDiffAt ℝ n e u) ∧
      (∀ u ∈ e.source, e u ∈ (extChartAt I c).target) ∧
      (∀ u ∈ e.source, obataRadial K a f ((extChartAt I c).symm (e u)) =
        t * ‖(trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) u‖) ∧
      (∀ u ∈ e.source,
        Real.sqrt (K * coordinateMetricBilinear (I := I) c z u u) * t ∈ Ioo 0 Real.pi →
        (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (e u))
          (fderiv ℝ e u u) =
          (t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u)) •
            gradient (I := I) (obataRadial K a f) ((extChartAt I c).symm (e u))) ∧
      ∀ u ∈ e.source, u ≠ 0 → ∀ w v : E,
        let g := coordinateMetricBilinear (I := I) c z
        let angular := Real.sin (Real.sqrt K * (t * Real.sqrt (g u u))) ^ 2 / (K * g u u)
        coordinateMetricBilinear (I := I) c (e u)
          (fderiv ℝ e u w) (fderiv ℝ e u v) =
            angular * g w v + (t ^ 2 - angular) * (g u w * g u v / g u u) := by
  have hn2 : (2 : ℕ∞ω) ≤ n := by exact_mod_cast hn
  obtain ⟨V, hV, hzV, δ, hδ, α, hα, hsol, hrest⟩ :=
    exists_stationary_coordinate_geodesic_flow_of_order n (by omega) LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion b c hz
  have hα2 := hα.of_le hn2
  let t := δ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htime : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp [t]
    linarith
  have hinit : (fun q => α (q, 0)) =ᶠ[𝓝 (z, (0 : E))] id := by
    filter_upwards [hV.mem_nhds hzV] with q hq
    exact (hsol q hq).1
  obtain ⟨e, he, he0, hez, _hinv⟩ := exists_geodesic_endpoint_local_inverse_of_order n hn LC
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion b c hz
    (hV.prod Metric.isOpen_ball) hα (fun q hq => ((hsol _ hq.1).2 _ hq.2).2)
    hinit Metric.isOpen_ball (convex_ball (0 : ℝ) δ).isPreconnected
    (Metric.mem_ball_self hδ) (fun s hs => ⟨hzV, hs⟩) hrest htime ht.ne'
  obtain ⟨ε, hε, hmetric⟩ := exists_geodesic_normal_full_metric_ball b hf hK ha hb hH c hz
    hV hzV hδ hα2 hsol hrest hcrit hmax htime ht
  have hr := coordinate_normal_endpoint_radius_at_zero_eventually b hf hK ha hH c hV hsol
    hzV hcrit hmax htime ht.le
  obtain ⟨η, hη, hrad⟩ := Metric.eventually_nhds_iff.mp hr
  let S := Metric.ball (0 : E) (min ε η) ∩ {u | (z, u) ∈ V}
  have hS : IsOpen S := Metric.isOpen_ball.inter
    (hV.preimage (continuous_const.prodMk continuous_id))
  have hS0 : (0 : E) ∈ S := ⟨Metric.mem_ball_self (lt_min hε hη), hzV⟩
  let d := e.restrOpen S hS
  have hd : (d : E → E) = (fun u => (α ((z, u), t)).1) := he
  have hd0 : HasFDerivAt d (t • ContinuousLinearMap.id ℝ E) 0 := by
    rw [hd]
    exact hasFDerivAt_geodesic_endpoint_zero LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion b c hz (hV.prod Metric.isOpen_ball) hα2
      (fun q hq => ((hsol _ hq.1).2 _ hq.2).2) hinit Metric.isOpen_ball
      (convex_ball (0 : ℝ) δ).isPreconnected (Metric.mem_ball_self hδ)
      (fun s hs => ⟨hzV, hs⟩) hrest htime
  have hdSmooth : ContDiffAt ℝ ∞ d 0 := by
    rw [hd]
    exact contDiffAt_coordinate_geodesic_endpoint_zero LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion b c hz hV hzV ht htime hsol
  have hdzero : d 0 = z := hez
  have hdsource : (0 : E) ∈ d.source := ⟨he0, hS0⟩
  have hdinvzero : d.symm z = 0 := by rw [← hdzero]; exact d.left_inv hdsource
  have hdinvSmooth : ContDiffAt ℝ ∞ d.symm z := by
    let A : E ≃L[ℝ] E := (Units.mk0 t ht.ne') • ContinuousLinearEquiv.refl ℝ E
    apply d.contDiffAt_symm (f₀' := A)
    · rw [← hdzero]
      exact d.map_source hdsource
    · rw [hdinvzero]
      exact hd0
    · rw [hdinvzero]
      exact hdSmooth
  refine ⟨t, ht, d, hdsource, hez, hd0, hdSmooth, hdinvSmooth, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [hd]
    have hi : ContDiffAt ℝ n (fun y : E => ((z, y), t)) u :=
      (contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const
    have hpt : ((z, u), t) ∈ V ×ˢ Metric.ball 0 δ := ⟨hu.2.2, htime⟩
    exact (((hα.contDiffAt ((hV.prod Metric.isOpen_ball).mem_nhds
      hpt)).comp u hi).fst)
  · intro u hu
    rw [hd]
    exact ((hsol _ hu.2.2).2 t htime).1
  · intro u hu
    rw [hd]
    exact hrad (lt_of_lt_of_le hu.2.1 (min_le_right ε η))
  · intro u hu hphase
    rw [hd]
    exact coordinate_normal_endpoint_radial_gradient b hf hK ha hH c hV
      (hα2.of_le (by norm_num)) hsol hu.2.2 hcrit hmax htime hphase
  · intro u hu hune w v
    rw [hd]
    apply hmetric u _ hune w v
    have hnorm : ‖u‖ < min ε η := by
      simpa only [Metric.mem_ball, dist_zero_right] using hu.2.1
    exact lt_of_lt_of_le hnorm (min_le_left ε η)


end LichnerowiczObata
