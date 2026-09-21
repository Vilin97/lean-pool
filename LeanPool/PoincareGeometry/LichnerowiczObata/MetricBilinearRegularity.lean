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

public import LeanPool.PoincareGeometry.LichnerowiczObata.CoordinateMetricVariation
public import LeanPool.PoincareGeometry.LichnerowiczObata.MetricPairingCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Smoothness of the bilinear-valued coordinate metric -/

@[expose] public noncomputable section
open Set Bundle FiberBundle AlmostSchur
open scoped ContDiff Topology BigOperators Manifold

namespace LichnerowiczObata
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- In finite dimension, smoothness of all basis pairings gives smoothness
of the whole continuous bilinear form, in its operator norm. -/
theorem contDiffOn_bilinear_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {g : P → E →L[ℝ] E →L[ℝ] ℝ} {S : Set P} {n : ℕ∞ω}
    (hg : ∀ i j, ContDiffOn ℝ n (fun z => g z (b i) (b j)) S) : ContDiffOn ℝ n g S := by
  let q : ι → E →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  let R : ι → ι → E →L[ℝ] E →L[ℝ] ℝ := fun i j => (q i).smulRight (q j)
  have he (z : P) : g z = ∑ i, ∑ j, g z (b i) (b j) • R i j := by
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j
    simp [R, q, Module.Basis.coord_apply, Finsupp.single_apply]
  have hs : ContDiffOn ℝ n (fun z => ∑ i, ∑ j, g z (b i) (b j) • R i j) S := by
    apply ContDiffOn.sum
    intro i hi
    apply ContDiffOn.sum
    intro j hj
    let L : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toSpanSingleton ℝ (R i j)
    have hL : ContDiff ℝ n L := by
      exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ℝ)
        (F := E →L[ℝ] E →L[ℝ] ℝ) L
    exact hL.comp_contDiffOn (hg i j)
  exact hs.congr (fun z _ => he z)

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- The actual coordinate metric is C1 as an operator-norm-valued bilinear form. -/
theorem contDiffOn_coordinateMetricBilinear (c : M) :
    ContDiffOn ℝ 1 (coordinateMetricBilinear (I := I) c) (extChartAt I c).target := by
  let b := Module.finBasis ℝ E
  apply contDiffOn_bilinear_of_basis b
  intro i j
  have hm := contDiffOn_coordinateMetric (I := I) b c
  have hij := (contDiffOn_pi.mp (contDiffOn_pi.mp hm i)) j
  simpa only [coordinateMetric, tangentChartGram, tangentTrivializationGram,
    Matrix.gram_apply, coordinateMetricBilinear_apply] using hij

/-- At an interior chart point the bundled coordinate metric is differentiable. -/
theorem differentiableAt_coordinateMetricBilinear (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) :
    DifferentiableAt ℝ (coordinateMetricBilinear (I := I) c) z := by
  exact ((contDiffOn_coordinateMetricBilinear (I := I) c).contDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hz)).differentiableAt (by simp)

/-- Evaluating the bundled derivative agrees with differentiating a fixed pairing. -/
theorem fderiv_coordinateMetricBilinear_apply (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) (d u w : E) :
    fderiv ℝ (coordinateMetricBilinear (I := I) c) z d u w =
      fderiv ℝ (fun y => coordinateMetricBilinear (I := I) c y u w) z d := by
  have hg := differentiableAt_coordinateMetricBilinear (I := I) c hz
  rw [fderiv_clm_apply (hg.clm_apply (differentiableAt_const u))
    (differentiableAt_const w), fderiv_clm_apply hg (differentiableAt_const u)]
  simp

/-- Bundled metric compatibility, derived from the genuine metric connection. -/
theorem fderiv_coordinateMetricBilinear_coefficients
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : tangentMetricCompatible cov) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (c x : M) (hx : x ∈ (chartAt H c).source)
    (d u w : E) :
    let A := frameConnectionCoefficients cov
      (trivializationAt E (TangentSpace I : M → Type _) c) b x d
    fderiv ℝ (coordinateMetricBilinear (I := I) c) (extChartAt I c x) d u w =
      coordinateMetricBilinear (I := I) c (extChartAt I c x) (A u) w +
        coordinateMetricBilinear (I := I) c (extChartAt I c x) u (A w) := by
  dsimp only
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  rw [fderiv_coordinateMetricBilinear_apply c ((extChartAt I c).map_source hx')]
  have he : (extChartAt I c).symm (extChartAt I c x) = x :=
    (extChartAt I c).left_inv hx'
  simp only [coordinateMetricBilinear_apply]
  rw [he]
  simpa only [coordinateMetricBilinear_apply, he, Function.comp_def] using
    fderiv_coordinateMetric_pairing_coefficients cov hcov b c x hx d u w

/-- Along a differentiable coordinate curve, the actual metric pairing evolves
by the two covariant variation terms. -/
theorem hasDerivAt_coordinateMetric_pairing_connection
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : tangentMetricCompatible cov) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (c x : M) (hx : x ∈ (chartAt H c).source)
    {z u w : ℝ → E} {d u' w' : E} {t : ℝ}
    (hz : z t = extChartAt I c x) (hd : HasDerivAt z d t)
    (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t) :
    let g := coordinateMetricBilinear (I := I) c
    let A := frameConnectionCoefficients cov
      (trivializationAt E (TangentSpace I : M → Type _) c) b x d
    HasDerivAt (fun s => g (z s) (u s) (w s))
      (g (z t) (u' + A (u t)) (w t) + g (z t) (u t) (w' + A (w t))) t := by
  dsimp only
  have hzt : z t ∈ (extChartAt I c).target := by
    rw [hz]
    exact (extChartAt I c).map_source (by simpa using hx)
  have hg : HasDerivAt (fun s => coordinateMetricBilinear (I := I) c (z s))
      (fderiv ℝ (coordinateMetricBilinear (I := I) c) (z t) d) t := by
    exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E)
      (E := E →L[ℝ] E →L[ℝ] ℝ) t
      (differentiableAt_coordinateMetricBilinear (I := I) c hzt).hasFDerivAt hd
  apply hasDerivAt_metric_pairing_connection _ hg hu hw
  rw [hz]
  exact fderiv_coordinateMetricBilinear_coefficients cov hcov b c x hx d (u t) (w t)

end LichnerowiczObata
