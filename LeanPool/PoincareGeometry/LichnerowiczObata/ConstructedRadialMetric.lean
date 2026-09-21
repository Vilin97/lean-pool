/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.CoordinateAngularVariation
public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothRadialFlow

/-! # Metric evolution of the constructed radial family -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur Filter
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- Spherical metric evolution in every valid pair of charts, for the actual
spatial derivatives of a radial family. -/
def RadialChartMetricEvolution (K a : ℝ) (f : M → ℝ) (η : M × ℝ → M) : Prop :=
  ∀ (c₀ c₁ : M) (p : E) (t : ℝ),
    (p, t) ∈ chartFlowDomain (I := I) η
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)) c₀ c₁ →
    ∀ v w : E,
      let φ := chartFlow (I := I) η c₀ c₁
      HasDerivAt (fun s => coordinateMetricBilinear (I := I) c₁ (φ (p, s))
        (fderiv ℝ φ (p, s) (v, 0)) (fderiv ℝ φ (p, s) (w, 0)))
        (2 * (Real.sqrt K * (Real.cos (Real.sqrt K * t) / Real.sin (Real.sqrt K * t))) *
          coordinateMetricBilinear (I := I) c₁ (φ (p, t))
            (fderiv ℝ φ (p, t) (v, 0)) (fderiv ℝ φ (p, t) (w, 0))) t

/-- On the full open radial interval, the level identity guarantees that
the output is regular, so metric evolution needs no extra regularity premise. -/
theorem radialChartMetricEvolution_of_family {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TangentSpace I y),
      hessian LC f y v w = -K * f y * inner ℝ v w)
    {η : M × ℝ → M}
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 2 η
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)))
    (hode : ∀ y, -a < f y ∧ f y < a → IsMIntegralCurveOn (fun s => η (y, s))
      (gradient (I := I) (obataRadial K a f)) (Ioo 0 (Real.pi / Real.sqrt K)))
    (hlevel : ∀ y, -a < f y ∧ f y < a → ∀ s ∈ Ioo 0 (Real.pi / Real.sqrt K),
      obataRadial K a f (η (y, s)) = s) :
    RadialChartMetricEvolution (I := I) K a f η := by
  intro c₀ c₁ p t hpt v w
  let x := η ((extChartAt I c₀).symm p, t)
  have ht : obataRadial K a f x = t := hlevel _ hpt.1.2.1 _ hpt.1.2.2
  have hcos := obataRadial_cos hK ha x (hb x)
  rw [ht] at hcos
  have hreg : -a < f x ∧ f x < a := by
    rw [← hcos]
    exact obata_cos_level_mem hK ha hpt.1.2.2
  have hU : IsOpen {y : M | -a < f y ∧ f y < a} :=
    (isOpen_lt continuous_const hf.continuous).inter (isOpen_lt hf.continuous continuous_const)
  exact hasDerivAt_manifold_radial_chart_metric hK ha hf hb hH hU isOpen_Ioo hη
    hode hlevel (Module.finBasis ℝ E) c₀ c₁ hpt hreg v w

variable [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [CompactSpace M] [T2Space M] [Nonempty M] [PreconnectedSpace M]

/-- The same constructed smooth radial family has all its original flow and
endpoint guarantees together with the derived spherical chart-metric equation. -/
theorem exists_smooth_obata_radial_family_metric
    {K : ℝ} (hK : 0 < K) {f : M → ℝ} (hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian LC f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      (∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2)) ∧
      ∃ η : M × ℝ → M,
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ η
          ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)) ∧
        RadialChartMetricEvolution (I := I) K a f η ∧
        ∀ x : M, -a < f x ∧ f x < a →
          η (x, obataRadial K a f x) = x ∧
          (∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K), ∀ s : ℝ, η (η (x, r), s) = η (x, s)) ∧
          IsMIntegralCurveOn (fun r => η (x, r)) (gradient (I := I) (obataRadial K a f))
            (Ioo 0 (Real.pi / Real.sqrt K)) ∧
          (∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
            obataRadial K a f (η (x, r)) = r ∧
              ‖mfderiv 𝓘(ℝ, ℝ) I (fun t => η (x, t)) r 1‖ = 1) ∧
          ∃ p q : M,
            Tendsto (fun r => η (x, r)) (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) (𝓝 p) ∧
            Tendsto (fun r => η (x, r))
              (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) (𝓝 q) ∧
            f p = a ∧ f q = -a := by
  obtain ⟨a, ha, hb, hnorm, η, hη, hcurves⟩ :=
    exists_smooth_obata_radial_family hK hfs hnon hH
  refine ⟨a, ha, hb, hnorm, η, hη, ?_, hcurves⟩
  have htwo : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  exact radialChartMetricEvolution_of_family hK ha (hfs.of_le htwo) hb hH (hη.of_le htwo)
    (fun y hy => (hcurves y hy).2.2.1)
    (fun y hy s hs => ((hcurves y hy).2.2.2.1 s hs).1)

end LichnerowiczObata
