/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.GlobalNormalAngularMetric

/-! # Angular metric in intrinsic tangent-space parameters -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The actual normal-chart/radial-flow composite is differentiable at
every parameter whose starting point and destination radius are regular. -/
theorem mdifferentiableAt_normal_radial_composite
    {f : M → ℝ} (hf : Continuous f) {a ℓ : ℝ} {η : M × ℝ → M}
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 ℓ))
    (c : M) {e : E → E} {u : E} (he : DifferentiableAt ℝ e u)
    (hout : e u ∈ (extChartAt I c).target)
    (hreg : -a < f ((extChartAt I c).symm (e u)) ∧
      f ((extChartAt I c).symm (e u)) < a)
    {r : ℝ} (hr : r ∈ Ioo 0 ℓ) :
    MDifferentiableAt 𝓘(ℝ, E) I (fun y => η ((extChartAt I c).symm (e y), r)) u := by
  have hi : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I c).symm (e u) := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := c) hout)
  have hψ := hi.comp u (mdifferentiableAt_iff_differentiableAt.mpr he)
  have hU : IsOpen {x : M | -a < f x ∧ f x < a} :=
    (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)
  have hpt : ((extChartAt I c).symm (e u), r) ∈
      {x : M | -a < f x ∧ f x < a} ×ˢ Ioo 0 ℓ := ⟨hreg, hr⟩
  have hd := ((hη _ hpt).contMDiffAt ((hU.prod isOpen_Ioo).mem_nhds hpt)).mdifferentiableAt
    (by norm_num)
  exact hd.comp u (hψ.prodMk mdifferentiableAt_const)

omit [I.Boundaryless] in
/-- The forward tangent trivialization identifies the coordinate metric
with the intrinsic inner product at the chart base point. -/
theorem coordinate_metric_trivialization_forward (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) (u v : TM ((extChartAt I c).symm z)) :
    coordinateMetricBilinear (I := I) c z
      ((trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z) u)
      ((trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z) v) =
        inner ℝ u v := by
  have hp : (extChartAt I c).symm z ∈ (chartAt H c).source := by
    simpa using (extChartAt I c).map_target hz
  have hc (w : TM ((extChartAt I c).symm z)) :
      (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z)
        ((trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z) w) = w :=
    (trivializationAt E TM c).symmL_continuousLinearMapAt hp w
  change inner ℝ
    ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z)
      ((trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z) u))
    ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z)
      ((trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z) v)) = _
  rw [hc, hc]

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- Joint differentiability of the actual normal-chart flow map, including
the radial parameter and a continuous linear angular parameter change. -/
theorem mdifferentiableAt_normal_radial_joint
    {f : M → ℝ} (hf : Continuous f) {a ℓ : ℝ} {η : M × ℝ → M}
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 ℓ))
    (c : M) (L : P →L[ℝ] E) {e : E → E} {u : P}
    (he : DifferentiableAt ℝ e (L u))
    (hout : e (L u) ∈ (extChartAt I c).target)
    (hreg : -a < f ((extChartAt I c).symm (e (L u))) ∧
      f ((extChartAt I c).symm (e (L u))) < a)
    {r : ℝ} (hr : r ∈ Ioo 0 ℓ) :
    MDifferentiableAt 𝓘(ℝ, P × ℝ) I
      (fun q => η ((extChartAt I c).symm (e (L q.1)), q.2)) (u, r) := by
  have hi : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I c).symm (e (L u)) := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := c) hout)
  have hL : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, E) L u :=
    mdifferentiableAt_iff_differentiableAt.mpr L.differentiableAt
  have hψ : MDifferentiableAt 𝓘(ℝ, P) I
      (fun y => (extChartAt I c).symm (e (L y))) u :=
    (hi.comp (L u) (mdifferentiableAt_iff_differentiableAt.mpr he)).comp u hL
  have hU : IsOpen {x : M | -a < f x ∧ f x < a} :=
    (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)
  have hpt : ((extChartAt I c).symm (e (L u)), r) ∈
      {x : M | -a < f x ∧ f x < a} ×ˢ Ioo 0 ℓ := ⟨hreg, hr⟩
  have hd := ((hη _ hpt).contMDiffAt ((hU.prod isOpen_Ioo).mem_nhds hpt)).mdifferentiableAt
    (by norm_num)
  have hfirst : MDifferentiableAt 𝓘(ℝ, P × ℝ) I
      (fun q => (extChartAt I c).symm (e (L q.1))) (u, r) :=
    hψ.comp (f := Prod.fst) (g := fun y => (extChartAt I c).symm (e (L y)))
      (u, r) (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst)
  have hpair : MDifferentiableAt 𝓘(ℝ, P × ℝ) (I.prod 𝓘(ℝ, ℝ))
      (fun q => ((extChartAt I c).symm (e (L q.1)), q.2)) (u, r) :=
    hfirst.prodMk (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_snd)
  exact hd.comp (u, r) hpair

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The flow radius identity holds on a full neighborhood of each regular
normal-chart parameter, so it may be differentiated in both parameters. -/
theorem normal_radial_joint_level_eventually
    {f ρ : M → ℝ} (hf : Continuous f) {a ℓ : ℝ} {η : M × ℝ → M}
    (hlevel : ∀ x, -a < f x ∧ f x < a → ∀ r ∈ Ioo 0 ℓ, ρ (η (x, r)) = r)
    (c : M) (L : P →L[ℝ] E) {e : E → E} {u : P}
    (he : DifferentiableAt ℝ e (L u))
    (hout : e (L u) ∈ (extChartAt I c).target)
    (hreg : -a < f ((extChartAt I c).symm (e (L u))) ∧
      f ((extChartAt I c).symm (e (L u))) < a)
    {r : ℝ} (hr : r ∈ Ioo 0 ℓ) :
    (fun q : P × ℝ => ρ (η ((extChartAt I c).symm (e (L q.1)), q.2)))
      =ᶠ[𝓝 (u, r)] Prod.snd := by
  have hi : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I c).symm (e (L u)) := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := c) hout)
  have hL : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, E) L u :=
    mdifferentiableAt_iff_differentiableAt.mpr L.differentiableAt
  have hψ : MDifferentiableAt 𝓘(ℝ, P) I
      (fun y => (extChartAt I c).symm (e (L y))) u :=
    (hi.comp (L u) (mdifferentiableAt_iff_differentiableAt.mpr he)).comp u hL
  have hfirst : ContinuousAt
      (fun q : P × ℝ => (extChartAt I c).symm (e (L q.1))) (u, r) :=
    hψ.continuousAt.comp (f := Prod.fst)
      (g := fun y => (extChartAt I c).symm (e (L y))) continuousAt_fst
  have hU : IsOpen {x : M | -a < f x ∧ f x < a} :=
    (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)
  have hs := hfirst.preimage_mem_nhds (hU.mem_nhds hreg)
  have ht : ∀ᶠ q : P × ℝ in 𝓝 (u, r), q.2 ∈ Ioo 0 ℓ :=
    continuousAt_snd.preimage_mem_nhds (isOpen_Ioo.mem_nhds hr)
  filter_upwards [hs, ht] with q hq hqr
  exact hlevel _ hq _ hqr

omit [IsManifold I ∞ M] [I.Boundaryless] in
/-- A metric-compatible linear parameter change converts the coordinate
angular formula into an intrinsic one for the actual composite derivative. -/
theorem angular_metric_precompose_linear
    (L : P →L[ℝ] E) (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ x y, g (L x) (L y) = inner ℝ x y)
    {ψ : E → M} {u w v : P} {B : ℝ}
    (hψ : MDifferentiableAt 𝓘(ℝ, E) I ψ (L u))
    (hw : inner ℝ u w = 0) (hv : inner ℝ u v = 0)
    (hmetric : ∀ j k : E, g (L u) j = 0 → g (L u) k = 0 →
      inner ℝ (mfderiv 𝓘(ℝ, E) I ψ (L u) j) (mfderiv 𝓘(ℝ, E) I ψ (L u) k) =
        B * (g j k / g (L u) (L u))) :
    inner ℝ (mfderiv 𝓘(ℝ, P) I (ψ ∘ L) u w) (mfderiv 𝓘(ℝ, P) I (ψ ∘ L) u v) =
      B * (inner ℝ w v / ‖u‖ ^ 2) := by
  have hL : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, E) L u :=
    mdifferentiableAt_iff_differentiableAt.mpr L.differentiableAt
  have hwc := mfderiv_comp_apply u hψ hL w
  have hvc := mfderiv_comp_apply u hψ hL v
  rw [mfderiv_eq_fderiv, L.fderiv] at hwc hvc
  rw [hwc, hvc]
  convert hmetric (L w) (L v) ((hg u w).trans hw) ((hg u v).trans hv) using 1 <;>
    first | rfl | simp only [hg, real_inner_self_eq_norm_sq]

omit [IsManifold I ∞ M] [I.Boundaryless] in
/-- Passing from a positive-radius tangent sphere to unit directions cancels
the radius-squared factor in the angular metric of the actual map. -/
theorem angular_metric_rescale_unit {Φ : P → M} {u w v : P} {R B : ℝ}
    (hR : R ≠ 0) (hu : ‖u‖ = 1)
    (hΦ : MDifferentiableAt 𝓘(ℝ, P) I Φ (R • u))
    (hw : inner ℝ u w = 0) (hv : inner ℝ u v = 0)
    (hmetric : ∀ j k : P, inner ℝ (R • u) j = 0 → inner ℝ (R • u) k = 0 →
      inner ℝ (mfderiv 𝓘(ℝ, P) I Φ (R • u) j) (mfderiv 𝓘(ℝ, P) I Φ (R • u) k) =
        B * (inner ℝ j k / ‖R • u‖ ^ 2)) :
    inner ℝ (mfderiv 𝓘(ℝ, P) I (fun y => Φ (R • y)) u w)
      (mfderiv 𝓘(ℝ, P) I (fun y => Φ (R • y)) u v) = B * inner ℝ w v := by
  let L : P →L[ℝ] P := R • ContinuousLinearMap.id ℝ P
  have hL : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, P) L u :=
    mdifferentiableAt_iff_differentiableAt.mpr L.differentiableAt
  have hwc := mfderiv_comp_apply (f := (L : P → P)) u hΦ hL w
  have hvc := mfderiv_comp_apply (f := (L : P → P)) u hΦ hL v
  rw [mfderiv_eq_fderiv, L.fderiv] at hwc hvc
  change inner ℝ (mfderiv 𝓘(ℝ, P) I (Φ ∘ L) u w)
    (mfderiv 𝓘(ℝ, P) I (Φ ∘ L) u v) = _
  rw [hwc, hvc]
  have hw' : inner ℝ (R • u) (R • w) = 0 := by
    simp only [real_inner_smul_left, real_inner_smul_right, hw, mul_zero]
  have hv' : inner ℝ (R • u) (R • v) = 0 := by
    simp only [real_inner_smul_left, real_inner_smul_right, hv, mul_zero]
  have he := hmetric (R • w) (R • v) hw' hv'
  have hn : ‖R • u‖ ^ 2 = R ^ 2 := by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
  have hi : inner ℝ (R • w) (R • v) = R ^ 2 * inner ℝ w v := by
    simp only [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hn, hi] at he
  have hc : R ^ 2 * inner ℝ w v / R ^ 2 = inner ℝ w v := by field_simp
  rw [hc] at he
  exact he

/-- Intrinsic angular parameters for the actual normal-chart/radial-flow
composite. Differentiability and compatibility of the parameter change are
derived from the chart, flow, and tangent trivialization. -/
theorem normal_radial_composite_intrinsic_angular_metric
    {f : M → ℝ} (hf : Continuous f) {a ℓ B : ℝ} {η : M × ℝ → M}
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 ℓ))
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    {u w v : TM ((extChartAt I c).symm z)} {e : E → E}
    (he : DifferentiableAt ℝ e
      ((trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z) u))
    (hout : e ((trivializationAt E TM c).continuousLinearMapAt ℝ
      ((extChartAt I c).symm z) u) ∈ (extChartAt I c).target)
    (hreg : let x := (extChartAt I c).symm (e ((trivializationAt E TM c).continuousLinearMapAt ℝ
      ((extChartAt I c).symm z) u)); -a < f x ∧ f x < a)
    {r : ℝ} (hr : r ∈ Ioo 0 ℓ) (hw : inner ℝ u w = 0) (hv : inner ℝ u v = 0)
    (hmetric : let L := (trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z)
      let g := coordinateMetricBilinear (I := I) c z
      let ψ := fun y => η ((extChartAt I c).symm (e y), r)
      ∀ j k : E, g (L u) j = 0 → g (L u) k = 0 →
        inner ℝ (mfderiv 𝓘(ℝ, E) I ψ (L u) j) (mfderiv 𝓘(ℝ, E) I ψ (L u) k) =
          B * (g j k / g (L u) (L u))) :
    let L := (trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z)
    let Γ := fun y => η ((extChartAt I c).symm (e (L y)), r)
    inner ℝ (mfderiv 𝓘(ℝ, TM ((extChartAt I c).symm z)) I Γ u w)
      (mfderiv 𝓘(ℝ, TM ((extChartAt I c).symm z)) I Γ u v) =
        B * (inner ℝ w v / ‖u‖ ^ 2) := by
  let L := (trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z)
  have hψ := mdifferentiableAt_normal_radial_composite hf hη c he hout hreg hr
  exact angular_metric_precompose_linear L (coordinateMetricBilinear (I := I) c z)
    (coordinate_metric_trivialization_forward c hz) hψ hw hv hmetric

end LichnerowiczObata
