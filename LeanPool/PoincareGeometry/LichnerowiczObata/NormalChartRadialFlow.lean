/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataNormalRay
public import LeanPool.PoincareGeometry.LichnerowiczObata.IntrinsicNormalMetric

/-! # Actual normal-chart rays agree with the radial transport -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
/-- A polar parametrization is represented near its pole by a genuine
smooth map of Cartesian tangent vectors, with
an inner-product-preserving derivative at zero. -/
def HasRadialPoleModel {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (Φ : P × ℝ → M) (p : M) : Prop :=
  ∃ χ : P → M, χ 0 = p ∧ ContMDiffAt 𝓘(ℝ, P) I ∞ χ 0 ∧
    (∀ v w : P, inner ℝ (mfderiv 𝓘(ℝ, P) I χ 0 v)
      (mfderiv 𝓘(ℝ, P) I χ 0 w) = inner ℝ v w) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ Ioo 0 δ,
      Φ (u, r) = χ (r • (u : P))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- On a ball containing the seed sphere, the normal chart itself is the
radial transport of each seed point. The interval contains the seed time;
regularity and the initial equality are derived from the radial identity. -/
theorem normal_chart_eq_radial_transport
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (e : OpenPartialHomeomorph E E) {t R : ℝ} (ht : 0 < t) (hR : 0 < R)
    (htR : t * R ∈ Ioo 0 (Real.pi / Real.sqrt K))
    (hsmooth : ∀ u ∈ e.source, ContDiffAt ℝ 2 e u)
    (hout : ∀ u ∈ e.source, e u ∈ (extChartAt I c).target)
    (hball : ∀ v ∈ Metric.ball (0 : TM ((extChartAt I c).symm z)) (2 * R),
      (trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z) v ∈ e.source)
    (hrad : ∀ u ∈ e.source, obataRadial K a f ((extChartAt I c).symm (e u)) =
      t * ‖(trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) u‖)
    (hgradient : ∀ u ∈ e.source,
      Real.sqrt (K * coordinateMetricBilinear (I := I) c z u u) * t ∈ Ioo 0 Real.pi →
      mfderiv 𝓘(ℝ, E) I ((extChartAt I c).symm ∘ e) u u =
        (t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u)) •
          gradient (I := I) (obataRadial K a f) ((extChartAt I c).symm (e u)))
    (hregular : ∀ x, obataRadial K a f x ∈ Ioo 0 (Real.pi / Real.sqrt K) →
      -a < f x ∧ f x < a)
    (η : M × ℝ → M)
    (hcurves : ∀ x, -a < f x ∧ f x < a →
      IsMIntegralCurveOn (fun r => η (x, r)) (gradient (I := I) (obataRadial K a f))
        (Ioo 0 (Real.pi / Real.sqrt K)))
    (hinit : ∀ x, -a < f x ∧ f x < a → η (x, obataRadial K a f x) = x)
    (v : Metric.sphere (0 : TM ((extChartAt I c).symm z)) R) :
    let L := (trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z)
    ∀ r ∈ Ioo 0 (min (2 * (t * R)) (Real.pi / Real.sqrt K)),
      (extChartAt I c).symm (e (L ((r / (t * R)) • (v : TM ((extChartAt I c).symm z))))) =
        η ((extChartAt I c).symm (e (L v)), r) := by
  let p := (extChartAt I c).symm z
  let L := (trivializationAt E TM c).continuousLinearMapAt ℝ p
  let S := (trivializationAt E TM c).symmL ℝ p
  let ψ := (extChartAt I c).symm ∘ e
  let u := (t * R)⁻¹ • L v
  let b := min (2 * (t * R)) (Real.pi / Real.sqrt K)
  have hp : p ∈ (chartAt H c).source := by
    simpa [p] using (extChartAt I c).map_target hz
  have hcancel (w : TM p) : S (L w) = w :=
    (trivializationAt E TM c).symmL_continuousLinearMapAt hp w
  have hv : ‖(v : TM p)‖ = R := by
    simpa only [Metric.mem_sphere, dist_zero_right] using v.2
  have hscale (r : ℝ) : r • u = L ((r / (t * R)) • (v : TM p)) := by
    simp [u, map_smul, smul_smul, div_eq_mul_inv]
  have hnorm (r : ℝ) (hr : 0 ≤ r) : ‖S (r • u)‖ = r / t := by
    rw [hscale, map_smul, map_smul, hcancel, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hr htR.1.le), hv]
    field_simp
  have hsrc (r : ℝ) (hr : r ∈ Ioo 0 b) : r • u ∈ e.source := by
    rw [hscale]
    apply hball
    have hlt : r < 2 * (t * R) := lt_of_lt_of_le hr.2 (min_le_left _ _)
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr.1 htR.1), hv]
    have he : r / (t * R) * R = r / t := by field_simp
    rw [he]
    apply (div_lt_iff₀ ht).mpr
    nlinarith
  have hsmall (r : ℝ) (hr : r ∈ Ioo 0 b) : r ∈ Ioo 0 (Real.pi / Real.sqrt K) :=
    ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_right _ _)⟩
  have hρ (r : ℝ) (hr : r ∈ Ioo 0 b) : obataRadial K a f (ψ (r • u)) = r := by
    change obataRadial K a f ((extChartAt I c).symm (e (r • u))) = r
    rw [hrad _ (hsrc r hr)]
    change t * ‖S (r • u)‖ = r
    rw [hnorm r hr.1.le]
    field_simp
  have hseed : t * R ∈ Ioo 0 b :=
    ⟨htR.1, lt_min (by linarith [htR.1]) htR.2⟩
  have hseedarg : (t * R) • u = L v := by
    rw [hscale, div_self htR.1.ne', one_smul]
  have hseedρ : obataRadial K a f (ψ (L v)) = t * R := by
    simpa only [hseedarg] using hρ (t * R) hseed
  have hseedreg : -a < f (ψ (L v)) ∧ f (ψ (L v)) < a :=
    hregular _ (hseedρ ▸ htR)
  have heq := obata_normal_ray_eq_radial_curve ha hf ψ u (le_refl 0) hseed
    (hψ := by
      intro r hr
      have hi : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I c).symm (e (r • u)) := by
        simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
          (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := c) (hout _ (hsrc r hr)))
      exact hi.comp _ (mdifferentiableAt_iff_differentiableAt.mpr
        ((hsmooth _ (hsrc r hr)).differentiableAt (by norm_num))))
    (hreg := by
      intro r hr
      apply hregular
      rw [hρ r hr]
      exact hsmall r hr)
    (hrad := by
      intro r hr
      have hg : Real.sqrt (coordinateMetricBilinear (I := I) c z (r • u) (r • u)) =
          ‖S (r • u)‖ := by
        change Real.sqrt (inner ℝ (S (r • u)) (S (r • u))) = _
        rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      have hc : t * Real.sqrt (coordinateMetricBilinear (I := I) c z (r • u) (r • u)) = r := by
        rw [hg, hnorm r hr.1.le]
        field_simp
      have hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c z (r • u) (r • u)) * t =
          Real.sqrt K * r := by
        rw [Real.sqrt_mul hK.le]
        calc
          _ = Real.sqrt K * (t * Real.sqrt
            (coordinateMetricBilinear (I := I) c z (r • u) (r • u))) := by ring
          _ = Real.sqrt K * r := by rw [hc]
      have hphase_mem : Real.sqrt K * r ∈ Ioo 0 Real.pi := by
        refine ⟨mul_pos (Real.sqrt_pos.mpr hK) hr.1, ?_⟩
        have hh := (lt_div_iff₀ (Real.sqrt_pos.mpr hK)).mp (hsmall r hr).2
        nlinarith
      exact (hgradient _ (hsrc r hr) (hphase ▸ hphase_mem)).trans (by rw [hc]; rfl))
    (fun r => η (ψ (L v), r))
    ((hcurves _ hseedreg).mono (fun r hr => hsmall r hr))
    (by rw [hseedarg, ← hseedρ]; exact (hinit _ hseedreg).symm)
  change ∀ r ∈ Ioo 0 b, ψ (L ((r / (t * R)) • (v : TM p))) = η (ψ (L v), r)
  intro r hr
  simpa only [hscale, ψ, Function.comp_apply] using heq hr

end LichnerowiczObata
