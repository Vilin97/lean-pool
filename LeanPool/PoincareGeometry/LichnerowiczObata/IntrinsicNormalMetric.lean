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

public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalMetricChart
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Intrinsic tangent pairings of the normal chart -/

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

omit [FiniteDimensional ℝ E] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The derivative of a chart lift is the coordinate derivative transported
by the inverse tangent trivialization. -/
theorem coordinate_derivative_eq_intrinsic_chart_lift (c : M) {F : E → E} {u : E}
    (hF : DifferentiableAt ℝ F u) (hout : F u ∈ (extChartAt I c).target) (j : E) :
    (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (F u)) (fderiv ℝ F u j) =
      mfderiv 𝓘(ℝ, E) I ((extChartAt I c).symm ∘ F) u j := by
  let ψ := (extChartAt I c).symm ∘ F
  have hi : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I c).symm (F u) := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := c) hout)
  have hψ : MDifferentiableAt 𝓘(ℝ, E) I ψ u :=
    hi.comp u (mdifferentiableAt_iff_differentiableAt.mpr hF)
  have hx : ψ u ∈ (chartAt H c).source := by
    simpa [ψ] using (extChartAt I c).map_target hout
  have ho := mdifferentiableAt_extChartAt (I := I) hx
  have he : (extChartAt I c ∘ ψ) =ᶠ[𝓝 u] F := by
    filter_upwards [hF.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := I) c).mem_nhds hout)] with y hy
    exact (extChartAt I c).right_inv hy
  have hc := mfderiv_comp_apply u ho hψ j
  rw [mfderiv_eq_fderiv, he.fderiv_eq] at hc
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hx] at hc
  have hh := congrArg ((trivializationAt E TM c).symmL ℝ (ψ u)) hc
  exact hh.trans ((trivializationAt E TM c).symmL_continuousLinearMapAt hx
    (mfderiv 𝓘(ℝ, E) I ψ u j))

omit [FiniteDimensional ℝ E] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- Lifting a differentiable coordinate map through the inverse chart turns
its coordinate metric exactly into the pairing of its manifold derivatives. -/
theorem coordinate_metric_eq_intrinsic_chart_lift (c : M) {F : E → E} {u : E}
    (hF : DifferentiableAt ℝ F u) (hout : F u ∈ (extChartAt I c).target) (w v : E) :
    coordinateMetricBilinear (I := I) c (F u) (fderiv ℝ F u w) (fderiv ℝ F u v) =
      inner ℝ (mfderiv 𝓘(ℝ, E) I ((extChartAt I c).symm ∘ F) u w)
        (mfderiv 𝓘(ℝ, E) I ((extChartAt I c).symm ∘ F) u v) := by
  change inner ℝ ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (F u)) (fderiv ℝ F u w))
    ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (F u)) (fderiv ℝ F u v)) = _
  rw [coordinate_derivative_eq_intrinsic_chart_lift c hF hout w,
    coordinate_derivative_eq_intrinsic_chart_lift c hF hout v]

omit [FiniteDimensional ℝ E] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- Dividing out the endpoint time makes the normal chart's derivative
at the pole an intrinsic isometry. This uses its actual endpoint derivative,
not an additional metric assumption at the pole. -/
theorem normalized_normal_chart_derivative_inner (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) {e : E → E} {t : ℝ} (ht : t ≠ 0)
    (hez : e 0 = z) (hd : HasFDerivAt e (t • ContinuousLinearMap.id ℝ E) 0)
    (v w : TM ((extChartAt I c).symm z)) :
    let χ := fun u : TM ((extChartAt I c).symm z) => (extChartAt I c).symm
      (e ((1 / t) • (trivializationAt E TM c).continuousLinearMapAt ℝ
        ((extChartAt I c).symm z) u))
    inner ℝ (mfderiv 𝓘(ℝ, TM ((extChartAt I c).symm z)) I χ 0 v)
      (mfderiv 𝓘(ℝ, TM ((extChartAt I c).symm z)) I χ 0 w) = inner ℝ v w := by
  let p := (extChartAt I c).symm z
  let L := (trivializationAt E TM c).continuousLinearMapAt ℝ p
  let A : TM p →L[ℝ] E := (1 / t) • L
  let ψ := (extChartAt I c).symm ∘ e
  have hout : e 0 ∈ (extChartAt I c).target := hez ▸ hz
  have hi : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I c).symm (e 0) := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := c) hout)
  have hψ : MDifferentiableAt 𝓘(ℝ, E) I ψ (A 0) := by
    rw [map_zero]
    exact hi.comp 0 (mdifferentiableAt_iff_differentiableAt.mpr hd.differentiableAt)
  have hA : MDifferentiableAt 𝓘(ℝ, TM p) 𝓘(ℝ, E) A 0 :=
    mdifferentiableAt_iff_differentiableAt.mpr A.differentiableAt
  change inner ℝ (mfderiv 𝓘(ℝ, TM p) I (ψ ∘ A) 0 v)
    (mfderiv 𝓘(ℝ, TM p) I (ψ ∘ A) 0 w) = inner ℝ v w
  rw [mfderiv_comp_apply 0 hψ hA v, mfderiv_comp_apply 0 hψ hA w,
    mfderiv_eq_fderiv, A.fderiv]
  dsimp only [ψ]
  have hF : DifferentiableAt ℝ e (A 0) := by simpa only [map_zero] using hd.differentiableAt
  have houtA : e (A 0) ∈ (extChartAt I c).target := by simpa only [map_zero] using hout
  change inner ℝ (mfderiv 𝓘(ℝ, E) I ((extChartAt I c).symm ∘ e) (A 0) (A v))
    (mfderiv 𝓘(ℝ, E) I ((extChartAt I c).symm ∘ e) (A 0) (A w)) = inner ℝ v w
  rw [← coordinate_metric_eq_intrinsic_chart_lift c hF houtA (A v) (A w),
    map_zero, hd.fderiv, hez]
  have hscale (j : TM p) : (t • ContinuousLinearMap.id ℝ E) (A j) = L j := by
    simp [A, smul_smul, ht]
  rw [hscale v, hscale w]
  have hp : p ∈ (chartAt H c).source := by
    simpa [p] using (extChartAt I c).map_target hz
  change inner ℝ ((trivializationAt E TM c).symmL ℝ p (L v))
    ((trivializationAt E TM c).symmL ℝ p (L w)) = inner ℝ v w
  rw [(trivializationAt E TM c).symmL_continuousLinearMapAt hp v,
    (trivializationAt E TM c).symmL_continuousLinearMapAt hp w]

variable [PreconnectedSpace M]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

/-- The constructed normal chart carries the spherical angular metric as
an equality of actual manifold tangent inner products, not just coordinate
pairings. The chart and radial identity are retained with this conclusion. -/
theorem exists_obata_intrinsic_angular_chart
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a) :
    ∃ t : ℝ, 0 < t ∧ ∃ e : OpenPartialHomeomorph E E,
      0 ∈ e.source ∧ e 0 = z ∧
      HasFDerivAt e (t • ContinuousLinearMap.id ℝ E) 0 ∧
      ContDiffAt ℝ ∞ e 0 ∧ ContDiffAt ℝ 2 e.symm z ∧
      (∀ u ∈ e.source, ContDiffAt ℝ 2 e u) ∧
      (∀ u ∈ e.source, e u ∈ (extChartAt I c).target) ∧
      (∀ u ∈ e.source, obataRadial K a f ((extChartAt I c).symm (e u)) =
        t * ‖(trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) u‖) ∧
      (∀ u ∈ e.source,
        Real.sqrt (K * coordinateMetricBilinear (I := I) c z u u) * t ∈ Ioo 0 Real.pi →
        mfderiv 𝓘(ℝ, E) I ((extChartAt I c).symm ∘ e) u u =
          (t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u)) •
            gradient (I := I) (obataRadial K a f) ((extChartAt I c).symm (e u))) ∧
      ∀ u ∈ e.source, u ≠ 0 → ∀ w v : E,
        coordinateMetricBilinear (I := I) c z u w = 0 →
        coordinateMetricBilinear (I := I) c z u v = 0 →
        let g := coordinateMetricBilinear (I := I) c z
        inner ℝ (mfderiv 𝓘(ℝ, E) I ((extChartAt I c).symm ∘ e) u w)
          (mfderiv 𝓘(ℝ, E) I ((extChartAt I c).symm ∘ e) u v) =
            (Real.sin (Real.sqrt K * (t * Real.sqrt (g u u))) ^ 2 / (K * g u u)) * g w v := by
  obtain ⟨t, ht, e, he0, hez, hderiv0, hpoleSmooth, hinv, hsmooth, htarget, hrad, hgradient, hmetric⟩ :=
    exists_obata_normal_metric_chart b hf hK ha hb hH c hz hcrit hmax
  refine ⟨t, ht, e, he0, hez, hderiv0, hpoleSmooth, hinv, hsmooth, htarget, hrad, ?_, ?_⟩
  · intro u hu hphase
    rw [← coordinate_derivative_eq_intrinsic_chart_lift c
      ((hsmooth u hu).differentiableAt (by norm_num)) (htarget u hu) u]
    exact hgradient u hu hphase
  intro u hu hune w v hw hv
  rw [← coordinate_metric_eq_intrinsic_chart_lift c
    ((hsmooth u hu).differentiableAt (by norm_num)) (htarget u hu) w v]
  have he := hmetric u hu hune w v
  dsimp only at he ⊢
  rw [hw, hv] at he
  simpa only [zero_mul, zero_div, mul_zero, add_zero] using he

end LichnerowiczObata
