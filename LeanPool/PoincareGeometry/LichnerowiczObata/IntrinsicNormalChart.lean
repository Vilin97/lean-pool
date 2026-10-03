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

public import LeanPool.PoincareGeometry.LichnerowiczObata.GeodesicNormalRadial
public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalLevelHomeomorph
public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialProduct

/-! # A genuine intrinsic radial normal chart -/

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

/-- The actual geodesic endpoint map gives a local homeomorphism from the
intrinsic tangent space, with the radial identity valid on its entire source. -/
theorem exists_intrinsic_radial_normal_chart
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (u w : TM y), hessian LC f y u w = -K * f y * inner ℝ u w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V)
    (hzV : (z, (0 : E)) ∈ V) {δ : ℝ} (hδ : 0 < δ)
    (hα : ContDiffOn ℝ 2 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, s))) s)
    (hrest : ∀ s ∈ Metric.ball 0 δ, α ((z, 0), s) = (z, 0))
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ) (ht : 0 < t) :
    let p := (extChartAt I c).symm z
    ∃ e : OpenPartialHomeomorph (TM p) M, 0 ∈ e.source ∧ e 0 = p ∧
      (∀ v, e v = (extChartAt I c).symm (α ((z,
        (trivializationAt E TM c).continuousLinearMapAt ℝ p v), t)).1) ∧
      ∀ v ∈ e.source, obataRadial K a f (e v) = t * ‖v‖ := by
  let p := (extChartAt I c).symm z
  have hp : p ∈ (chartAt H c).source := by simpa [p] using (extChartAt I c).map_target hz
  let L := (trivializationAt E TM c).continuousLinearEquivAt ℝ p hp
  let C : OpenPartialHomeomorph M E :=
    { toPartialEquiv := extChartAt I c
      open_source := isOpen_extChartAt_source c
      open_target := isOpen_extChartAt_target c
      continuousOn_toFun := continuousOn_extChartAt c
      continuousOn_invFun := continuousOn_extChartAt_symm c }
  have hinit : (fun q => α (q, 0)) =ᶠ[𝓝 (z, (0 : E))] id := by
    filter_upwards [hV.mem_nhds hzV] with q hq
    exact (hsol q hq).1
  obtain ⟨e, he, he0, hez, hinv⟩ := exists_geodesic_endpoint_local_inverse LC
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion b c hz
    (hV.prod Metric.isOpen_ball) hα (fun q hq => ((hsol _ hq.1).2 _ hq.2).2)
    hinit Metric.isOpen_ball (convex_ball (0 : ℝ) δ).isPreconnected
    (Metric.mem_ball_self hδ) (fun s hs => ⟨hzV, hs⟩) hrest htime ht.ne'
  let F := L.toHomeomorph.toOpenPartialHomeomorph.trans (e.trans C.symm)
  have hF0 : (0 : TM p) ∈ F.source := by
    change (0 : TM p) ∈ Set.univ ∧ L 0 ∈ e.source ∧ e (L 0) ∈ C.target
    simpa only [map_zero, hez] using And.intro (mem_univ (0 : TM p)) (And.intro he0 hz)
  have hFp : F 0 = p := by
    change C.symm (e (L 0)) = p
    rw [map_zero, hez]
    rfl
  have hF (v : TM p) : F v = (extChartAt I c).symm (α ((z,
      (trivializationAt E TM c).continuousLinearMapAt ℝ p v), t)).1 := by
    change C.symm (e (L v)) = _
    rw [he]
    have hLv : L v = (trivializationAt E TM c).continuousLinearMapAt ℝ p v :=
      congrFun ((trivializationAt E TM c).coe_continuousLinearEquivAt_eq hp) v
    rw [hLv]
    rfl
  have hr : ∀ᶠ v in 𝓝 (0 : TM p), obataRadial K a f (F v) = t * ‖v‖ := by
    simp_rw [hF]
    exact intrinsic_normal_endpoint_radius_at_zero_eventually b hf hK ha hH c hV hsol
      hz hzV hcrit hmax htime ht.le
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hr
  refine ⟨F.restrOpen (Metric.ball 0 ε) Metric.isOpen_ball,
    ⟨hF0, Metric.mem_ball_self hε⟩, hFp, hF, ?_⟩
  intro v hv
  exact hball hv.2

/-- A radial normal chart exists at an Obata maximum. Its geodesic family,
positive endpoint time, inverse, and radial identity are all constructed. -/
theorem exists_obata_radial_normal_chart
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (u w : TM y), hessian LC f y u w = -K * f y * inner ℝ u w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a) :
    let p := (extChartAt I c).symm z
    ∃ t : ℝ, 0 < t ∧ ∃ e : OpenPartialHomeomorph (TM p) M,
      0 ∈ e.source ∧ e 0 = p ∧ ∀ v ∈ e.source, obataRadial K a f (e v) = t * ‖v‖ := by
  obtain ⟨V, hV, hzV, δ, hδ, α, hα, hsol, hrest⟩ :=
    exists_stationary_coordinate_geodesic_flow LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion b c hz
  have ht : 0 < δ / 2 := by positivity
  have htime : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith
  obtain ⟨e, he0, hep, hemap, helevel⟩ := exists_intrinsic_radial_normal_chart b hf hK ha hH c hz
    hV hzV hδ hα hsol hrest hcrit hmax htime ht
  exact ⟨δ / 2, ht, e, he0, hep, helevel⟩

/-- Entire sufficiently small Obata radial levels are homeomorphic to
spheres in the intrinsic tangent space at the unique maximum. -/
theorem exists_small_obata_sphere_levels [CompactSpace M]
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ x, f x ≤ a)
    (hH : ∀ (y : M) (u w : TM y), hessian LC f y u w = -K * f y * inner ℝ u w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z) :
    let p := (extChartAt I c).symm z
    ∃ t : ℝ, 0 < t ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Ioo 0 ε,
      Nonempty (Metric.sphere (0 : TM p) (r / t) ≃ₜ {x : M // obataRadial K a f x = r}) := by
  let p := (extChartAt I c).symm z
  obtain ⟨t, ht, e, he0, hep, hlevel⟩ := exists_obata_radial_normal_chart b hf hK ha hH c hz
    hcrit ((hmax _).mpr rfl)
  have hc : Continuous (obataRadial K a f) := by
    have hfc := hf.continuous
    unfold obataRadial
    fun_prop
  have hn : ∀ x, 0 ≤ obataRadial K a f x :=
    fun x => div_nonneg (Real.arccos_nonneg _) (Real.sqrt_nonneg _)
  have hzero : ∀ x, obataRadial K a f x = 0 ↔ x = e 0 := by
    intro x
    rw [hep]
    constructor
    · intro hx
      have hsqrt : Real.sqrt K ≠ 0 := (Real.sqrt_pos.mpr hK).ne'
      have hz := (div_eq_zero_iff.mp hx).resolve_right hsqrt
      have hle := (le_div_iff₀ ha).mp (Real.arccos_eq_zero.mp hz)
      exact (hmax x).mp (le_antisymm (hb x) (by simpa using hle))
    · intro hx
      have he := (hmax x).mpr hx
      simp [obataRadial, he, ha.ne']
  obtain ⟨ε, hε, hlevels⟩ := exists_small_sphere_level_homeomorph e he0 hc hn hzero ht hlevel
  exact ⟨t, ht, ε, hε, hlevels⟩

/-- Normal coordinates at the unique maximum and complete radial transport
identify the entire regular region with an intrinsic tangent sphere times
the full radial interval. The sphere radius is constructed and positive. -/
theorem exists_obata_tangent_sphere_product [CompactSpace M] [T2Space M] [Nonempty M]
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (u w : TM y), hessian LC f y u w = -K * f y * inner ℝ u w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z) :
    let p := (extChartAt I c).symm z
    ∃ R : ℝ, 0 < R ∧ Nonempty ({x : M // -a < f x ∧ f x < a} ≃ₜ
      Metric.sphere (0 : TM p) R × Ioo 0 (Real.pi / Real.sqrt K)) := by
  obtain ⟨hb, hprod⟩ := obata_whole_level_product_at_positive_critical_value hK ha hf hnon hH
    ((extChartAt I c).symm z) ((hmax _).mpr rfl) hcrit
  have hf2 : ContMDiff I 𝓘(ℝ, ℝ) 2 f :=
    hf.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  obtain ⟨t, ht, ε, hε, hlevels⟩ := exists_small_obata_sphere_levels b hf2 hK ha
    (fun x => (hb x).2) hH c hz hcrit hmax
  have hL : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)
  let r := min ε (Real.pi / Real.sqrt K) / 2
  have hr : 0 < r := div_pos (lt_min hε hL) (by norm_num)
  have hre : r < ε := by
    have := min_le_left ε (Real.pi / Real.sqrt K)
    dsimp [r] at *
    linarith
  have hrL : r < Real.pi / Real.sqrt K := by
    have := min_le_right ε (Real.pi / Real.sqrt K)
    dsimp [r] at *
    linarith
  obtain ⟨e⟩ := hprod r ⟨hr, hrL⟩
  obtain ⟨s⟩ := hlevels r ⟨hr, hre⟩
  exact ⟨r / t, div_pos hr ht,
    ⟨e.trans (s.symm.prodCongr (Homeomorph.refl _))⟩⟩

end LichnerowiczObata
