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

public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalAngularTangency

/-! # The global angular metric of a constructed normal chart -/

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

/-- The actual normal chart, followed by radial transport, has the spherical
angular metric at every regular radius. Its initial metric and angularity
are both proved from the Obata equation and the constructed chart. -/
theorem exists_normal_chart_global_angular_metric
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    {η : M × ℝ → M}
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)))
    (hm : RadialChartMetricEvolution (I := I) K a f η)
    (hinit : ∀ x, -a < f x ∧ f x < a → η (x, obataRadial K a f x) = x)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a) :
    ∃ t : ℝ, 0 < t ∧ ∃ e : OpenPartialHomeomorph E E,
      0 ∈ e.source ∧ e 0 = z ∧
      HasFDerivAt e (t • ContinuousLinearMap.id ℝ E) 0 ∧
      ContDiffAt ℝ ∞ e 0 ∧
      (∀ u ∈ e.source, ContDiffAt ℝ 2 e u) ∧
      (∀ u ∈ e.source, e u ∈ (extChartAt I c).target) ∧
      (∀ u ∈ e.source, obataRadial K a f ((extChartAt I c).symm (e u)) =
        t * ‖(trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) u‖) ∧
      (∀ u ∈ e.source,
        Real.sqrt (K * coordinateMetricBilinear (I := I) c z u u) * t ∈ Ioo 0 Real.pi →
        mfderiv 𝓘(ℝ, E) I ((extChartAt I c).symm ∘ e) u u =
          (t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u)) •
            gradient (I := I) (obataRadial K a f) ((extChartAt I c).symm (e u))) ∧
      ∀ u ∈ e.source, u ≠ 0 →
        (-a < f ((extChartAt I c).symm (e u)) ∧ f ((extChartAt I c).symm (e u)) < a) →
        ∀ w v : E, coordinateMetricBilinear (I := I) c z u w = 0 →
          coordinateMetricBilinear (I := I) c z u v = 0 →
          ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
            let Ψ := fun y => η ((extChartAt I c).symm (e y), r)
            let g := coordinateMetricBilinear (I := I) c z
            inner ℝ (mfderiv 𝓘(ℝ, E) I Ψ u w) (mfderiv 𝓘(ℝ, E) I Ψ u v) =
              (Real.sin (Real.sqrt K * r) ^ 2 / K) * (g w v / g u u) := by
  obtain ⟨t, ht, e, he0, hez, hderiv0, hpoleSmooth, _, hsmooth, htarget, hrad, hgradient, hmetric⟩ :=
    exists_obata_intrinsic_angular_chart b hf hK ha hb hH c hz hcrit hmax
  refine ⟨t, ht, e, he0, hez, hderiv0, hpoleSmooth, hsmooth, htarget, hrad, hgradient, ?_⟩
  intro u hu hune hreg w v hw hv r hr
  let ψ := (extChartAt I c).symm ∘ e
  let L := (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z)
  let g := coordinateMetricBilinear (I := I) c z
  have hi : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I c).symm (e u) := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := c) (htarget u hu))
  have hψ : MDifferentiableAt 𝓘(ℝ, E) I ψ u :=
    hi.comp u (mdifferentiableAt_iff_differentiableAt.mpr
      ((hsmooth u hu).differentiableAt (by norm_num)))
  have hevent : (obataRadial K a f ∘ ψ) =ᶠ[𝓝 u] (fun y => t * ‖L y‖) := by
    filter_upwards [e.open_source.mem_nhds hu] with y hy
    exact hrad y hy
  have hn : Real.sqrt (g u u) = ‖L u‖ := by
    change Real.sqrt (inner ℝ (L u) (L u)) = _
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have harg : t * Real.sqrt (g u u) = obataRadial K a f (ψ u) := by
    rw [hn]
    exact (hrad u hu).symm
  have hbase : inner ℝ (mfderiv 𝓘(ℝ, E) I ψ u w) (mfderiv 𝓘(ℝ, E) I ψ u v) =
      (Real.sin (Real.sqrt K * obataRadial K a f (ψ u)) ^ 2 / K) * (g w v / g u u) := by
    have he := hmetric u hu hune w v hw hv
    change _ = (Real.sin (Real.sqrt K * (t * Real.sqrt (g u u))) ^ 2 / (K * g u u)) * g w v at he
    rw [he, harg]
    simp only [div_mul_eq_div_mul_one_div]
    ring
  exact normal_angular_composite_metric hK ha hf hη hm hinit L hψ hreg hevent hw hv hbase hr

variable [CompactSpace M] [T2Space M] [Nonempty M]

/-- Both the complete radial family and the normal chart are constructed
from the Obata equation. The same family retains its reset, level, and
unit-speed identities while its composite with the chart has the proved
spherical angular metric. -/
theorem exists_obata_global_angular_metric
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a) :
    (∀ x, -a ≤ f x ∧ f x ≤ a) ∧ ∃ η : M × ℝ → M,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ η
        ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)) ∧
      (∀ x, -a < f x ∧ f x < a →
        η (x, obataRadial K a f x) = x ∧
        (∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K), ∀ s : ℝ, η (η (x, r), s) = η (x, s)) ∧
        IsMIntegralCurveOn (fun r => η (x, r)) (gradient (I := I) (obataRadial K a f))
          (Ioo 0 (Real.pi / Real.sqrt K)) ∧
        (∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K), obataRadial K a f (η (x, r)) = r ∧
          ‖mfderiv 𝓘(ℝ, ℝ) I (fun s => η (x, s)) r 1‖ = 1) ∧
        ∃ p q : M,
          Filter.Tendsto (fun r => η (x, r)) (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) (𝓝 p) ∧
          Filter.Tendsto (fun r => η (x, r))
            (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) (𝓝 q) ∧
          f p = a ∧ f q = -a) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ e : OpenPartialHomeomorph E E,
        0 ∈ e.source ∧ e 0 = z ∧
        HasFDerivAt e (t • ContinuousLinearMap.id ℝ E) 0 ∧
      ContDiffAt ℝ ∞ e 0 ∧
        (∀ u ∈ e.source, ContDiffAt ℝ 2 e u) ∧
        (∀ u ∈ e.source, e u ∈ (extChartAt I c).target) ∧
        (∀ u ∈ e.source, obataRadial K a f ((extChartAt I c).symm (e u)) =
          t * ‖(trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) u‖) ∧
        (∀ u ∈ e.source,
          Real.sqrt (K * coordinateMetricBilinear (I := I) c z u u) * t ∈ Ioo 0 Real.pi →
          mfderiv 𝓘(ℝ, E) I ((extChartAt I c).symm ∘ e) u u =
            (t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u)) •
              gradient (I := I) (obataRadial K a f) ((extChartAt I c).symm (e u))) ∧
        ∀ u ∈ e.source, u ≠ 0 →
          (-a < f ((extChartAt I c).symm (e u)) ∧ f ((extChartAt I c).symm (e u)) < a) →
          ∀ w v : E, coordinateMetricBilinear (I := I) c z u w = 0 →
            coordinateMetricBilinear (I := I) c z u v = 0 →
            ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
              let Ψ := fun y => η ((extChartAt I c).symm (e y), r)
              let g := coordinateMetricBilinear (I := I) c z
              inner ℝ (mfderiv 𝓘(ℝ, E) I Ψ u w) (mfderiv 𝓘(ℝ, E) I Ψ u v) =
                (Real.sin (Real.sqrt K * r) ^ 2 / K) * (g w v / g u u) := by
  obtain ⟨a', ha', hb, hn, η, hη, hm, hcurves⟩ :=
    exists_smooth_obata_radial_family_metric hK hf hnon hH
  have he := hn ((extChartAt I c).symm z)
  rw [hcrit, hmax, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
  have heq : a' = a := by
    have hs : a' ^ 2 - a ^ 2 = 0 := (mul_eq_zero.mp he.symm).resolve_left hK.ne'
    nlinarith
  subst a'
  have htwo : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  have hone : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ ⊤)
  refine ⟨hb, η, hη, hcurves, ?_⟩
  exact exists_normal_chart_global_angular_metric (Module.finBasis ℝ E)
    (hf.of_le htwo) hK ha hb hH (hη.of_le hone) hm
    (fun x hx => (hcurves x hx).1) c hz hcrit hmax

end LichnerowiczObata
