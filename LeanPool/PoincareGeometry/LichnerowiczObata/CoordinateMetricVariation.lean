/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.MetricConnectionCoordinates
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-! # Metric differentiation on arbitrary coordinate vectors -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The actual metric in a fixed tangent chart, bundled as a continuous
bilinear form so it can be evaluated on moving coordinate vectors. -/
def coordinateMetricBilinear (c : M) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let y := (extChartAt I c).symm z
  let L := (trivializationAt E TM c).symmL ℝ y
  (innerSL ℝ).bilinearComp L L

theorem coordinateMetricBilinear_apply (c : M) (z u w : E) :
    coordinateMetricBilinear (I := I) c z u w =
      inner ℝ ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) u)
        ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) w) := rfl

/-- A fixed coordinate vector gives a smooth local tangent section. -/
theorem contMDiffAt_coordinateConstant (c x : M) (hx : x ∈ (chartAt H c).source) (u : E) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, (trivializationAt E TM c).symmL ℝ y u⟩ : TangentBundle I M)) x := by
  let e := trivializationAt E TM c
  have hs : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, e.symmL ℝ y u⟩ : TangentBundle I M)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff]
    apply (contMDiffOn_const (c := u)).congr
    intro y hy
    simp only [e.symmL_apply hy, e.mk_symm hy]
    exact congrArg Prod.snd (e.apply_symm_apply' (x := u) hy)
  exact hs.contMDiffAt (e.open_baseSet.mem_nhds hx)

/-- Coordinate metric differentiation for arbitrary vectors is forced by
the genuine connection's metric compatibility. -/
theorem fderiv_coordinateMetric_pairing (cov : CovariantDerivative I E TM)
    (hcov : tangentMetricCompatible cov) (c x : M) (hx : x ∈ (chartAt H c).source)
    (d u w : E) :
    let e := trivializationAt E TM c
    fderiv ℝ ((fun y => inner ℝ (e.symmL ℝ y u) (e.symmL ℝ y w)) ∘
      (extChartAt I c).symm) (extChartAt I c x) d =
      inner ℝ (cov (fun y => e.symmL ℝ y u) x (e.symmL ℝ x d)) (e.symmL ℝ x w) +
        inner ℝ (e.symmL ℝ x u) (cov (fun y => e.symmL ℝ y w) x (e.symmL ℝ x d)) := by
  let e := trivializationAt E TM c
  have hu := (contMDiffAt_coordinateConstant (I := I) c x hx u).mdifferentiableAt (by norm_num)
  have hw := (contMDiffAt_coordinateConstant (I := I) c x hx w).mdifferentiableAt (by norm_num)
  have hd := fderiv_chart_comp
    (fun y => inner ℝ (e.symmL ℝ y u) (e.symmL ℝ y w)) c x hx
    (MDifferentiableAt.inner_bundle (F := E) (E := TM) hu hw) d
  exact hd.trans (CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq hcov
    (fun y => e.symmL ℝ y d) hu hw)

/-- For a constant coordinate section the ordinary coordinate derivative
vanishes, leaving precisely the actual frame connection coefficient. -/
theorem covariantDerivative_coordinateConstant (cov : CovariantDerivative I E TM)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (d u : E) :
    let e := trivializationAt E TM c
    cov (fun y => e.symmL ℝ y u) x (e.symmL ℝ x d) =
      e.symmL ℝ x (frameConnectionCoefficients cov e b x d u) := by
  let e := trivializationAt E TM c
  have hxe : x ∈ e.baseSet := hx
  have hs := (contMDiffAt_coordinateConstant (I := I) c x hx u).mdifferentiableAt (by norm_num)
  have hd := covariantDerivative_chart cov b (fun y => e.symmL ℝ y u) c x hx hs d
  have he : (fun z => e.continuousLinearMapAt ℝ ((extChartAt I c).symm z)
      (e.symmL ℝ ((extChartAt I c).symm z) u)) =ᶠ[𝓝 (extChartAt I c x)] (fun _ => u) := by
    have ht : (extChartAt I c).target ∈ 𝓝 (extChartAt I c x) :=
      (isOpen_extChartAt_target c).mem_nhds ((extChartAt I c).map_source (by simpa using hx))
    filter_upwards [ht] with z hz
    apply e.continuousLinearMapAt_symmL
    change (extChartAt I c).symm z ∈ (chartAt H c).source
    simpa only [extChartAt_source] using (extChartAt I c).map_target hz
  change e.continuousLinearMapAt ℝ x (cov (fun y => e.symmL ℝ y u) x (e.symmL ℝ x d)) = _ at hd
  rw [he.fderiv_eq] at hd
  simp only [fderiv_const_apply, zero_apply, add_zero] at hd
  have hi := congrArg (e.symmL ℝ x) hd
  simpa only [e, (trivializationAt E TM c).symmL_continuousLinearMapAt hx,
    (trivializationAt E TM c).continuousLinearMapAt_symmL hx] using hi

/-- The metric derivative on arbitrary coordinate vectors has the two
connection-coefficient terms, derived from the supplied metric connection. -/
theorem fderiv_coordinateMetric_pairing_coefficients (cov : CovariantDerivative I E TM)
    (hcov : tangentMetricCompatible cov) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (d u w : E) :
    let e := trivializationAt E TM c
    fderiv ℝ ((fun y => inner ℝ (e.symmL ℝ y u) (e.symmL ℝ y w)) ∘
      (extChartAt I c).symm) (extChartAt I c x) d =
      inner ℝ (e.symmL ℝ x (frameConnectionCoefficients cov e b x d u)) (e.symmL ℝ x w) +
        inner ℝ (e.symmL ℝ x u) (e.symmL ℝ x (frameConnectionCoefficients cov e b x d w)) := by
  dsimp only
  rw [fderiv_coordinateMetric_pairing cov hcov c x hx d u w,
    covariantDerivative_coordinateConstant cov b c x hx d u,
    covariantDerivative_coordinateConstant cov b c x hx d w]

end LichnerowiczObata
