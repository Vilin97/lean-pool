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

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothConnectionCoordinates
public import LeanPool.PoincareGeometry.LichnerowiczObata.FlowVariationEquation
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # The geodesic equation at zero velocity -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology BigOperators

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The geodesic acceleration is quadratic in velocity, so its first
derivative vanishes at zero velocity, including position perturbations. -/
theorem hasFDerivAt_coordinateGeodesicSpray_zero
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) :
    HasFDerivAt (coordinateGeodesicSpray cov b c)
      ((ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E)) (z, 0) := by
  classical
  let Γ := fun y => frameConnectionCoefficients cov (trivializationAt E TM c)
    b ((extChartAt I c).symm y)
  have hΓ (i j : ι) : DifferentiableAt ℝ (fun q : E × E => Γ q.1 (b i) (b j)) (z, 0) := by
    have hg : DifferentiableAt ℝ (fun y => Γ y (b i) (b j)) z :=
      ((contDiffOn_coordinateConnection_basis 1 cov hm ht b c i j).contDiffAt
        ((isOpen_extChartAt_target c).mem_nhds hz)).differentiableAt (by norm_num)
    exact DifferentiableAt.comp (𝕜 := ℝ) (f := fun q : E × E => q.1)
      (g := fun y : E => Γ y (b i) (b j)) (z, (0 : E)) hg differentiableAt_fst
  have hi (i : ι) : DifferentiableAt ℝ (fun q : E × E => b.repr q.2 i) (z, 0) :=
    (b.coord i).toContinuousLinearMap.differentiableAt.comp (z, (0 : E)) differentiableAt_snd
  have hterm (i j : ι) : HasFDerivAt (fun q : E × E =>
      (b.repr q.2 i * b.repr q.2 j) • Γ q.1 (b i) (b j)) (0 : E × E →L[ℝ] E) (z, 0) := by
    have hh := ((hi i).hasFDerivAt.mul (hi j).hasFDerivAt).smul (hΓ i j).hasFDerivAt
    convert hh using 1 <;> first | rfl | simp
  have hacc : HasFDerivAt (fun q : E × E => Γ q.1 q.2 q.2) (0 : E × E →L[ℝ] E) (z, 0) := by
    have he : (fun q : E × E => Γ q.1 q.2 q.2) =
        fun q => ∑ i, ∑ j, (b.repr q.2 i * b.repr q.2 j) • Γ q.1 (b i) (b j) := by
      funext q
      exact bilinear_diagonal_basis_expansion b (Γ q.1) q.2
    rw [he]
    have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm i j))
    simpa using hs
  convert (hasFDerivAt_snd (p := (z, (0 : E)))).prodMk hacc.neg using 1 <;>
    first | rfl | simp

/-- At rest, the geodesic linearization sends a perturbation to its velocity
component and has zero linear acceleration. -/
theorem fderiv_coordinateGeodesicSpray_zero_apply
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) (u v : E) :
    fderiv ℝ (coordinateGeodesicSpray cov b c) (z, 0) (u, v) = (v, 0) := by
  rw [(hasFDerivAt_coordinateGeodesicSpray_zero cov hm ht b c hz).fderiv]
  rfl

/-- Every actual geodesic solution starting at zero velocity is locally
stationary, by uniqueness of the constructed smooth ODE. -/
theorem coordinate_geodesic_at_rest_eventually
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) {α : ℝ → E × E}
    (hα : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt α (coordinateGeodesicSpray cov b c (α s)) s)
    (hzero : α 0 = (z, 0)) : α =ᶠ[𝓝 (0 : ℝ)] (fun _ => (z, 0)) := by
  have hD : IsOpen ((extChartAt I c).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target c).prod isOpen_univ
  have hp : (z, (0 : E)) ∈ (extChartAt I c).target ×ˢ (univ : Set E) := ⟨hz, mem_univ _⟩
  have hs := (contDiffOn_coordinateGeodesicSpray 1 cov hm ht b c).contDiffAt (hD.mem_nhds hp)
  obtain ⟨L, V, hV, hLip⟩ := hs.exists_lipschitzOnWith
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), α s ∈ V :=
    hα.self_of_nhds.continuousAt.preimage_mem_nhds (by rwa [hzero])
  have hconst : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun _ : ℝ => (z, (0 : E)))
        (coordinateGeodesicSpray cov b c (z, 0)) s ∧ (z, (0 : E)) ∈ V := by
    apply Filter.Eventually.of_forall
    intro s
    refine ⟨?_, mem_of_mem_nhds hV⟩
    convert hasDerivAt_const s (z, (0 : E)) using 1 <;>
      first | rfl | simp [coordinateGeodesicSpray]
  exact ODE_solution_unique_of_eventually (Filter.Eventually.of_forall (fun _ => hLip))
    (hα.and hmem) hconst hzero

/-- The spatial derivative of an actual smooth geodesic flow obeys the
flat linear system along its stationary zero-velocity solution. -/
theorem hasDerivAt_geodesic_flow_variation_at_rest
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {U : Set ((E × E) × ℝ)}
    (hU : IsOpen U) (hα : ContDiffOn ℝ 2 α U)
    (hode : ∀ q ∈ U, HasDerivAt (fun s => α (q.1, s))
      (coordinateGeodesicSpray cov b c (α q)) q.2)
    {t : ℝ} (hpt : ((z, 0), t) ∈ U) (hrest : α ((z, 0), t) = (z, 0)) (v : E × E) :
    HasDerivAt (fun s => fderiv ℝ α ((z, 0), s) (v, 0))
      ((fderiv ℝ α ((z, 0), t) (v, 0)).2, 0) t := by
  have hv : DifferentiableAt ℝ (coordinateGeodesicSpray cov b c) (α ((z, 0), t)) := by
    rw [hrest]
    exact (hasFDerivAt_coordinateGeodesicSpray_zero cov hm ht b c hz).differentiableAt
  have hd := hasDerivAt_flow_variation hU hα hode hpt hv v
  rw [hrest, fderiv_coordinateGeodesicSpray_zero_apply cov hm ht b c hz] at hd
  exact hd

omit [FiniteDimensional ℝ E] in
/-- Integration of the flat variational system on a connected open time domain.
The velocity variation is constant and the position variation is affine. -/
theorem flat_variation_eq_affine {J : ℝ → E × E} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hJ : ∀ t ∈ T, HasDerivAt J ((J t).2, 0) t) {t : ℝ} (ht : t ∈ T) :
    J t = ((J 0).1 + t • (J 0).2, (J 0).2) := by
  have hsnd : ∀ x ∈ T, HasDerivAt (fun s => (J s).2) 0 x := fun x hx =>
    (hasFDerivAt_snd (p := J x)).comp_hasDerivAt x (hJ x hx)
  have hfst : ∀ x ∈ T, HasDerivAt (fun s => (J s).1) (J x).2 x := fun x hx =>
    (hasFDerivAt_fst (p := J x)).comp_hasDerivAt x (hJ x hx)
  have hv : ∀ s ∈ T, (J s).2 = (J 0).2 := by
    intro s hs
    exact hT.is_const_of_deriv_eq_zero hconn
      (fun x hx => (hsnd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hsnd x hx).deriv) hs hzero
  have hp : ∀ s ∈ T,
      HasDerivAt (fun x => (J x).1 - x • (J 0).2) 0 s := by
    intro s hs
    convert (hfst s hs).sub ((hasDerivAt_id s).smul_const (J 0).2) using 1 <;>
      first | rfl | simp [hv s hs]
  have he := hT.is_const_of_deriv_eq_zero hconn
    (fun x hx => (hp x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hp x hx).deriv) ht hzero
  apply Prod.ext
  · simpa using (sub_eq_iff_eq_add.mp (by simpa using he))
  · exact hv t ht

/-- The actual geodesic flow has the Euclidean spatial linearization along
its stationary orbit, with initial derivative derived from the flow identity. -/
theorem fderiv_geodesic_flow_at_rest_apply
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {U : Set ((E × E) × ℝ)}
    (hU : IsOpen U) (hα : ContDiffOn ℝ 2 α U)
    (hode : ∀ q ∈ U, HasDerivAt (fun s => α (q.1, s))
      (coordinateGeodesicSpray cov b c (α q)) q.2)
    (hinit : (fun q => α (q, 0)) =ᶠ[𝓝 (z, (0 : E))] id)
    {T : Set ℝ} (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hmem : ∀ s ∈ T, ((z, 0), s) ∈ U)
    (hrest : ∀ s ∈ T, α ((z, 0), s) = (z, 0))
    {t : ℝ} (htime : t ∈ T) (u v : E) :
    fderiv ℝ α ((z, 0), t) ((u, v), 0) = (u + t • v, v) := by
  have hi := fderiv_flow_initial_apply
    ((hα.contDiffAt (hU.mem_nhds (hmem 0 hzero))).differentiableAt (by norm_num))
    hinit (u, v)
  have he := flat_variation_eq_affine hT hconn hzero
    (fun s hs => hasDerivAt_geodesic_flow_variation_at_rest cov hm ht b c hz
      hU hα hode (hmem s hs) (hrest s hs) (u, v)) htime
  simpa only [hi] using he

/-- The position endpoint of the geodesic flow has derivative `t • id` at
zero initial velocity. This is the differential used for normal coordinates. -/
theorem hasFDerivAt_geodesic_endpoint_zero
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {U : Set ((E × E) × ℝ)}
    (hU : IsOpen U) (hα : ContDiffOn ℝ 2 α U)
    (hode : ∀ q ∈ U, HasDerivAt (fun s => α (q.1, s))
      (coordinateGeodesicSpray cov b c (α q)) q.2)
    (hinit : (fun q => α (q, 0)) =ᶠ[𝓝 (z, (0 : E))] id)
    {T : Set ℝ} (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hmem : ∀ s ∈ T, ((z, 0), s) ∈ U)
    (hrest : ∀ s ∈ T, α ((z, 0), s) = (z, 0))
    {t : ℝ} (htime : t ∈ T) :
    HasFDerivAt (fun v => (α ((z, v), t)).1)
      (t • ContinuousLinearMap.id ℝ E) 0 := by
  apply hasFDerivAt_position_endpoint
    ((hα.contDiffAt (hU.mem_nhds (hmem t htime))).differentiableAt (by norm_num))
  intro v
  simpa using fderiv_geodesic_flow_at_rest_apply cov hm ht b c hz hU hα hode hinit
    hT hconn hzero hmem hrest htime 0 v

/-- At any nonzero time in its stationary time domain, the geodesic endpoint
map is a local homeomorphism with a twice continuously differentiable inverse
at the base point. The endpoint map itself is used as the forward function. -/
theorem exists_geodesic_endpoint_local_inverse
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {U : Set ((E × E) × ℝ)}
    (hU : IsOpen U) (hα : ContDiffOn ℝ 2 α U)
    (hode : ∀ q ∈ U, HasDerivAt (fun s => α (q.1, s))
      (coordinateGeodesicSpray cov b c (α q)) q.2)
    (hinit : (fun q => α (q, 0)) =ᶠ[𝓝 (z, (0 : E))] id)
    {T : Set ℝ} (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hmem : ∀ s ∈ T, ((z, 0), s) ∈ U)
    (hrest : ∀ s ∈ T, α ((z, 0), s) = (z, 0))
    {t : ℝ} (htime : t ∈ T) (htne : t ≠ 0) :
    ∃ e : OpenPartialHomeomorph E E,
      (e : E → E) = (fun v => (α ((z, v), t)).1) ∧
      0 ∈ e.source ∧ e 0 = z ∧ ContDiffAt ℝ 2 e.symm z := by
  let f : E → E := fun v => (α ((z, v), t)).1
  let A : E ≃L[ℝ] E := (Units.mk0 t htne) • ContinuousLinearEquiv.refl ℝ E
  have hA : (A : E →L[ℝ] E) = t • ContinuousLinearMap.id ℝ E := by
    ext v
    rfl
  have hi : ContDiffAt ℝ 2 (fun v : E => ((z, v), t)) 0 :=
    (contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const
  have hf : ContDiffAt ℝ 2 f 0 :=
    ((hα.contDiffAt (hU.mem_nhds (hmem t htime))).comp 0 hi).fst
  have hd : HasFDerivAt f (A : E →L[ℝ] E) 0 := by
    rw [hA]
    exact hasFDerivAt_geodesic_endpoint_zero cov hm ht b c hz hU hα hode hinit
      hT hconn hzero hmem hrest htime
  have hfzero : f 0 = z := congrArg Prod.fst (hrest t htime)
  refine ⟨hf.toOpenPartialHomeomorph f hd (by norm_num), rfl,
    hf.mem_toOpenPartialHomeomorph_source hd (by norm_num), hfzero, ?_⟩
  have hinv := hf.to_localInverse hd (by norm_num)
  rw [hfzero] at hinv
  exact hinv

/-- A constructed geodesic flow around zero velocity can be restricted to
an open product neighborhood on which its zero-velocity orbit is stationary. -/
theorem exists_stationary_coordinate_geodesic_flow_of_order
    (n : ℕ) (hn : n ≠ 0)
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) :
    ∃ V : Set (E × E), IsOpen V ∧ (z, (0 : E)) ∈ V ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ α : (E × E) × ℝ → E × E,
        ContDiffOn ℝ n α (V ×ˢ Metric.ball 0 δ) ∧
        (∀ q ∈ V, α (q, 0) = q ∧
          ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
            HasDerivAt (fun t => α (q, t))
              (coordinateGeodesicSpray cov b c (α (q, s))) s) ∧
        ∀ s ∈ Metric.ball 0 δ, α ((z, 0), s) = (z, 0) := by
  obtain ⟨W, hW, ε, hε, α, hα, hsol⟩ :=
    exists_smooth_coordinate_geodesic_flow n hn cov hm ht b c
      (u := (0 : E)) hz
  have hzW : (z, (0 : E)) ∈ W := mem_of_mem_nhds hW
  have hode : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun t => α ((z, 0), t))
        (coordinateGeodesicSpray cov b c (α ((z, 0), s))) s := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with s hs
    exact ((hsol (z, 0) hzW).2 s hs).2
  have hrest := coordinate_geodesic_at_rest_eventually cov hm ht b c hz hode
    (hsol (z, 0) hzW).1
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp
    (hrest.and (Metric.ball_mem_nhds (0 : ℝ) hε))
  have hball : Metric.ball (0 : ℝ) δ ⊆ Metric.ball 0 ε := fun s hs => (hsub hs).2
  refine ⟨interior W, isOpen_interior, mem_interior_iff_mem_nhds.mpr hW,
    δ, hδ, α, hα.mono (Set.prod_mono interior_subset hball), ?_, ?_⟩
  · intro q hq
    refine ⟨(hsol q (interior_subset hq)).1, ?_⟩
    intro s hs
    exact (hsol q (interior_subset hq)).2 s (hball hs)
  · intro s hs
    exact (hsub hs).1

/-- The second-order specialization used to construct normal coordinates. -/
theorem exists_stationary_coordinate_geodesic_flow
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) :
    ∃ V : Set (E × E), IsOpen V ∧ (z, (0 : E)) ∈ V ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ α : (E × E) × ℝ → E × E,
        ContDiffOn ℝ 2 α (V ×ˢ Metric.ball 0 δ) ∧
        (∀ q ∈ V, α (q, 0) = q ∧
          ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
            HasDerivAt (fun t => α (q, t))
              (coordinateGeodesicSpray cov b c (α (q, s))) s) ∧
        ∀ s ∈ Metric.ball 0 δ, α ((z, 0), s) = (z, 0) := by
  exact exists_stationary_coordinate_geodesic_flow_of_order 2 (by norm_num)
    cov hm ht b c hz

/-- Local normal coordinates are constructed from the actual geodesic flow.
Both the flow and its endpoint inverse are conclusions, not extra hypotheses. -/
theorem exists_coordinate_geodesic_normal_map
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) :
    ∃ V : Set (E × E), IsOpen V ∧ (z, (0 : E)) ∈ V ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ α : (E × E) × ℝ → E × E,
        ContDiffOn ℝ 2 α (V ×ˢ Metric.ball 0 δ) ∧
        (∀ q ∈ V, α (q, 0) = q ∧
          ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
            HasDerivAt (fun t => α (q, t))
              (coordinateGeodesicSpray cov b c (α (q, s))) s) ∧
        (∀ s ∈ Metric.ball 0 δ, α ((z, 0), s) = (z, 0)) ∧
        ∃ e : OpenPartialHomeomorph E E,
          (e : E → E) = (fun v => (α ((z, v), δ / 2)).1) ∧
          0 ∈ e.source ∧ e 0 = z ∧ ContDiffAt ℝ 2 e.symm z := by
  obtain ⟨V, hV, hzV, δ, hδ, α, hα, hsol, hrest⟩ :=
    exists_stationary_coordinate_geodesic_flow cov hm ht b c hz
  refine ⟨V, hV, hzV, δ, hδ, α, hα, hsol, hrest, ?_⟩
  have hinit : (fun q => α (q, 0)) =ᶠ[𝓝 (z, (0 : E))] id := by
    filter_upwards [hV.mem_nhds hzV] with q hq
    exact (hsol q hq).1
  have htime : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  exact exists_geodesic_endpoint_local_inverse cov hm ht b c hz
    (hV.prod Metric.isOpen_ball) hα
    (fun q hq => ((hsol q.1 hq.1).2 q.2 hq.2).2) hinit
    Metric.isOpen_ball (convex_ball (0 : ℝ) δ).isPreconnected
    (Metric.mem_ball_self hδ) (fun s hs => ⟨hzV, hs⟩) hrest htime (by positivity)

end LichnerowiczObata
