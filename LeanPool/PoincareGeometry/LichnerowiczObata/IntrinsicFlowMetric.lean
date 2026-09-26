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

public import LeanPool.PoincareGeometry.LichnerowiczObata.ConstructedRadialMetric
public import LeanPool.PoincareGeometry.LichnerowiczObata.AngularMetricEvolution

/-! # Intrinsic interpretation of coordinate flow variations -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Undoing the output trivialization recovers the actual tangent map from
the derivative of a map written in two fixed charts. -/
theorem symmL_fderiv_chart_map {ψ : M → M} (c₀ c₁ x : M)
    (hin : x ∈ (chartAt H c₀).source) (hout : ψ x ∈ (chartAt H c₁).source)
    (hψ : MDiffAt ψ x) (v : E) :
    (trivializationAt E TM c₁).symmL ℝ (ψ x)
      (fderiv ℝ (((extChartAt I c₁) ∘ ψ) ∘ (extChartAt I c₀).symm)
        (extChartAt I c₀ x) v) =
      mfderiv I I ψ x ((trivializationAt E TM c₀).symmL ℝ x v) := by
  have ho := mdifferentiableAt_extChartAt (I := I) hout
  have hd := fderiv_chart_comp ((extChartAt I c₁) ∘ ψ) c₀ x hin (ho.comp x hψ) v
  have hchain : mvfderiv I ((extChartAt I c₁) ∘ ψ) x
      ((trivializationAt E TM c₀).symmL ℝ x v) =
      mvfderiv I (extChartAt I c₁) (ψ x)
        (mfderiv I I ψ x ((trivializationAt E TM c₀).symmL ℝ x v)) := by
    exact mfderiv_comp_apply x ho hψ _
  have hd' := hd.trans hchain
  have hchart : mvfderiv I (extChartAt I c₁) (ψ x) =
      (trivializationAt E TM c₁).continuousLinearMapAt ℝ (ψ x) :=
    (TangentBundle.continuousLinearMapAt_trivializationAt hout).symm
  rw [hchart] at hd'
  have he := congrArg ((trivializationAt E TM c₁).symmL ℝ (ψ x)) hd'
  simpa only [(trivializationAt E TM c₁).symmL_continuousLinearMapAt hout] using he

omit [FiniteDimensional ℝ E] in
/-- A spatial direction of a jointly differentiable family is the derivative
of its fixed-time slice. -/
theorem fderiv_family_spatial {φ : E × ℝ → E} {p : E} {t : ℝ}
    (hφ : DifferentiableAt ℝ φ (p, t)) (v : E) :
    fderiv ℝ φ (p, t) (v, 0) = fderiv ℝ (fun y => φ (y, t)) p v := by
  have hi : HasFDerivAt (fun y : E => (y, t)) (ContinuousLinearMap.inl ℝ E ℝ) p := by
    convert (hasFDerivAt_id p).prodMk (hasFDerivAt_const t p) using 1 <;> rfl
  have hd := (hφ.hasFDerivAt.comp p hi).fderiv
  exact (congrArg (fun L : E →L[ℝ] E => L v) hd).symm

/-- Coordinate spatial variations of an actual manifold family represent its
intrinsic fixed-time tangent map on the natural open chart domain. -/
theorem symmL_fderiv_chartFlow {η : M × ℝ → M} {S : Set (M × ℝ)}
    (hS : IsOpen S) (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η S)
    (c₀ c₁ : M) {p : E} {t : ℝ}
    (hpt : (p, t) ∈ chartFlowDomain (I := I) η S c₀ c₁) (v : E) :
    let x := (extChartAt I c₀).symm p
    (trivializationAt E TM c₁).symmL ℝ (η (x, t))
      (fderiv ℝ (chartFlow (I := I) η c₀ c₁) (p, t) (v, 0)) =
      mfderiv I I (fun y => η (y, t)) x ((trivializationAt E TM c₀).symmL ℝ x v) := by
  let x := (extChartAt I c₀).symm p
  have hin : x ∈ (chartAt H c₀).source := by
    simpa only [extChartAt_source] using (extChartAt I c₀).map_target hpt.1.1
  have hp : extChartAt I c₀ x = p := (extChartAt I c₀).right_inv hpt.1.1
  have hD := isOpen_chartFlowDomain (I := I) hS hη.continuousOn c₀ c₁
  have hφ : DifferentiableAt ℝ (chartFlow (I := I) η c₀ c₁) (p, t) :=
    ((contDiffOn_chartFlow_domain (n := 1) hη c₀ c₁).contDiffAt
      (hD.mem_nhds hpt)).differentiableAt (by norm_num)
  have hηx : MDiffAt η (x, t) :=
    ((hη _ hpt.1.2).contMDiffAt (hS.mem_nhds hpt.1.2)).mdifferentiableAt (by norm_num)
  have hs : MDiffAt (fun y => η (y, t)) x :=
    hηx.comp x (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  dsimp only
  rw [fderiv_family_spatial hφ v]
  have he := symmL_fderiv_chart_map c₀ c₁ x hin hpt.2 hs v
  rw [hp] at he
  exact he

variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- The coordinate metric of spatial variations is their genuine intrinsic
inner product, so it does not depend on the chosen output chart. -/
theorem coordinate_flow_metric_eq_intrinsic {η : M × ℝ → M} {S : Set (M × ℝ)}
    (hS : IsOpen S) (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η S)
    (c₀ c₁ : M) {p : E} {t : ℝ}
    (hpt : (p, t) ∈ chartFlowDomain (I := I) η S c₀ c₁) (v w : E) :
    let x := (extChartAt I c₀).symm p
    let φ := chartFlow (I := I) η c₀ c₁
    coordinateMetricBilinear (I := I) c₁ (φ (p, t))
      (fderiv ℝ φ (p, t) (v, 0)) (fderiv ℝ φ (p, t) (w, 0)) =
      inner ℝ (mfderiv I I (fun y => η (y, t)) x ((trivializationAt E TM c₀).symmL ℝ x v))
        (mfderiv I I (fun y => η (y, t)) x ((trivializationAt E TM c₀).symmL ℝ x w)) := by
  dsimp only
  rw [coordinateMetricBilinear_apply]
  have he : (extChartAt I c₁).symm (chartFlow (I := I) η c₀ c₁ (p, t)) =
      η ((extChartAt I c₀).symm p, t) :=
    (extChartAt I c₁).left_inv (by simpa using hpt.2)
  rw [he, symmL_fderiv_chartFlow hS hη c₀ c₁ hpt v,
    symmL_fderiv_chartFlow hS hη c₀ c₁ hpt w]

/-- Intrinsic metric pairing of fixed-time spatial variations, with initial
vectors specified in one fixed source chart. No output chart occurs. -/
def intrinsicFlowMetric (η : M × ℝ → M) (c : M) (p v w : E) (t : ℝ) : ℝ :=
  let x := (extChartAt I c).symm p
  inner ℝ (mfderiv I I (fun y => η (y, t)) x ((trivializationAt E TM c).symmL ℝ x v))
    (mfderiv I I (fun y => η (y, t)) x ((trivializationAt E TM c).symmL ℝ x w))

/-- The chart metric equation transfers to the intrinsic pairing at every
interior radial time, choosing an output chart only locally for the proof. -/
theorem hasDerivAt_intrinsicFlowMetric {K a : ℝ} {f : M → ℝ} {η : M × ℝ → M}
    (hf : Continuous f)
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)))
    (hm : RadialChartMetricEvolution (I := I) K a f η)
    (c : M) {p : E} (hp : p ∈ (extChartAt I c).target)
    (hx : -a < f ((extChartAt I c).symm p) ∧ f ((extChartAt I c).symm p) < a)
    (v w : E) {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / Real.sqrt K)) :
    HasDerivAt (intrinsicFlowMetric (I := I) η c p v w)
      (2 * (Real.sqrt K * (Real.cos (Real.sqrt K * t) / Real.sin (Real.sqrt K * t))) *
        intrinsicFlowMetric (I := I) η c p v w t) t := by
  let c₁ := η ((extChartAt I c).symm p, t)
  let S := {x : M | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)
  have hS : IsOpen S :=
    ((isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)).prod isOpen_Ioo
  have hpt : (p, t) ∈ chartFlowDomain (I := I) η S c c₁ :=
    ⟨⟨hp, hx, ht⟩, mem_chart_source H c₁⟩
  have hD := isOpen_chartFlowDomain (I := I) hS hη.continuousOn c c₁
  let q := fun s => coordinateMetricBilinear (I := I) c₁
    (chartFlow (I := I) η c c₁ (p, s))
    (fderiv ℝ (chartFlow (I := I) η c c₁) (p, s) (v, 0))
    (fderiv ℝ (chartFlow (I := I) η c c₁) (p, s) (w, 0))
  have he : q =ᶠ[𝓝 t] intrinsicFlowMetric (I := I) η c p v w := by
    have hc : Continuous (fun s : ℝ => (p, s)) := continuous_const.prodMk continuous_id
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hD.mem_nhds hpt)] with s hs
    exact coordinate_flow_metric_eq_intrinsic hS hη c c₁ hs v w
  have hd := hm c c₁ p t hpt v w
  change HasDerivAt q (_ * q t) t at hd
  rw [he.eq_of_nhds] at hd
  exact hd.congr_of_eventuallyEq he.symm

/-- The intrinsic angular metric divided by the spherical sine-square factor
is constant on the entire open radial interval, without a single-chart assumption. -/
theorem intrinsicFlowMetric_sine_squared_normalized_eq {K a : ℝ} (hK : 0 < K)
    {f : M → ℝ} {η : M × ℝ → M} (hf : Continuous f)
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)))
    (hm : RadialChartMetricEvolution (I := I) K a f η)
    (c : M) {p : E} (hp : p ∈ (extChartAt I c).target)
    (hx : -a < f ((extChartAt I c).symm p) ∧ f ((extChartAt I c).symm p) < a)
    (v w : E) {r s : ℝ}
    (hr : r ∈ Ioo 0 (Real.pi / Real.sqrt K)) (hs : s ∈ Ioo 0 (Real.pi / Real.sqrt K)) :
    intrinsicFlowMetric (I := I) η c p v w r / Real.sin (Real.sqrt K * r) ^ 2 =
      intrinsicFlowMetric (I := I) η c p v w s / Real.sin (Real.sqrt K * s) ^ 2 := by
  exact sine_squared_normalized_eq (Real.sqrt_pos.mpr hK)
    (fun t ht => hasDerivAt_intrinsicFlowMetric hf hη hm c hp hx v w ht) hr hs

/-- The metric of actual spatial variations of a manifold family, with
arbitrary initial tangent vectors and no chart parameters. -/
def radialVariationMetric (η : M × ℝ → M) (x : M) (v w : TM x) (t : ℝ) : ℝ :=
  inner ℝ (mfderiv I I (fun y => η (y, t)) x v)
    (mfderiv I I (fun y => η (y, t)) x w)

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Specifying initial tangent vectors in a chart does not change their metric. -/
theorem intrinsicFlowMetric_eq_radialVariationMetric (η : M × ℝ → M) (c x : M)
    (hx : x ∈ (chartAt H c).source) (v w : TM x) (t : ℝ) :
    intrinsicFlowMetric (I := I) η c (extChartAt I c x)
      ((trivializationAt E TM c).continuousLinearMapAt ℝ x v)
      ((trivializationAt E TM c).continuousLinearMapAt ℝ x w) t =
      radialVariationMetric (I := I) η x v w t := by
  have he : (extChartAt I c).symm (extChartAt I c x) = x :=
    (extChartAt I c).left_inv (by simpa using hx)
  simp only [intrinsicFlowMetric]
  rw [he]
  simp only [(trivializationAt E TM c).symmL_continuousLinearMapAt hx]
  rfl

/-- Chart-free sine-square scaling of the actual tangent-map metric on the
full radial interval, for arbitrary initial tangent vectors. -/
theorem radialVariationMetric_sine_squared_normalized_eq {K a : ℝ} (hK : 0 < K)
    {f : M → ℝ} {η : M × ℝ → M} (hf : Continuous f)
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)))
    (hm : RadialChartMetricEvolution (I := I) K a f η)
    (x : M) (hx : -a < f x ∧ f x < a) (v w : TM x) {r s : ℝ}
    (hr : r ∈ Ioo 0 (Real.pi / Real.sqrt K)) (hs : s ∈ Ioo 0 (Real.pi / Real.sqrt K)) :
    radialVariationMetric (I := I) η x v w r / Real.sin (Real.sqrt K * r) ^ 2 =
      radialVariationMetric (I := I) η x v w s / Real.sin (Real.sqrt K * s) ^ 2 := by
  have hxc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hpx : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  have he : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source x)
  have hreg : -a < f ((extChartAt I x).symm (extChartAt I x x)) ∧
      f ((extChartAt I x).symm (extChartAt I x x)) < a := by rwa [he]
  have hh := intrinsicFlowMetric_sine_squared_normalized_eq hK hf hη hm x hpx hreg
    ((trivializationAt E TM x).continuousLinearMapAt ℝ x v)
    ((trivializationAt E TM x).continuousLinearMapAt ℝ x w) hr hs
  simpa only [intrinsicFlowMetric_eq_radialVariationMetric η x x hxc] using hh

end LichnerowiczObata
