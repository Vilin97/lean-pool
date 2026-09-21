/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.CoordinateCoefficientRegularity

/-! # Higher regularity of the actual coordinate coefficients

Every differentiability order possessed by the tangent metric and its bundle
trivializations passes to the Gram matrix, volume density and elliptic matrix.
In particular a smooth metric yields smooth local PDE coefficients.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped ContDiff Manifold Topology Matrix.Norms.Elementwise

namespace AlmostSchur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Higher regularity of the coordinate Gram matrix follows from the given metric. -/
theorem contDiffOn_coordinateMetric_of_order (n : WithTop ℕ∞)
    [IsManifold I n M]
    [ContMDiffVectorBundle n E TM I] [IsContMDiffRiemannianBundle I n E TM]
    (b : Module.Basis ι ℝ E) (c : M) :
    ContDiffOn ℝ n (coordinateMetric (I := I) b c) (extChartAt I c).target := by
  intro z hz
  let x := (extChartAt I c).symm z
  let e := trivializationAt E TM c
  have hx : x ∈ e.baseSet := by
    change (extChartAt I c).symm z ∈ (chartAt H c).source
    simpa only [extChartAt_source] using (extChartAt I c).map_target hz
  have hs (k : ι) : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (T% (e.localFrame b k)) x :=
    contMDiffAt_localFrame_of_mem n e b k hx
  have hi : ContMDiffAt 𝓘(ℝ, E) I n (extChartAt I c).symm z :=
    (contMDiffOn_extChartAt_symm c z hz).contMDiffAt ((isOpen_extChartAt_target c).mem_nhds hz)
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hm := ContMDiffAt.inner_bundle (F := E) (E := TM) (hs i) (hs j)
  have hc := (hm.comp z hi).contDiffAt
  simpa only [Function.comp_def, localFrame_eq_symmL, coordinateMetric,
    tangentChartGram, tangentTrivializationGram, Matrix.gram_apply, e] using hc

/-- The actual volume density inherits every available metric differentiability order. -/
theorem contDiffOn_coordinateDensity_of_order (n : WithTop ℕ∞)
    [IsManifold I n M]
    [ContMDiffVectorBundle n E TM I] [IsContMDiffRiemannianBundle I n E TM]
    (b : Module.Basis ι ℝ E) (c : M) :
    ContDiffOn ℝ n (fun z => matrixDensity (coordinateMetric (I := I) b c z))
      (extChartAt I c).target :=
  ((determinantMultilinear (ι := ι)).contDiff.comp_contDiffOn
    (contDiffOn_coordinateMetric_of_order n b c)).sqrt
      (fun z hz => (coordinateMetric_posDef b c z hz).det_pos.ne')

/-- The actual divergence-form elliptic matrix inherits the metric's regularity. -/
theorem contDiffOn_coordinateEllipticMatrix_of_order (n : WithTop ℕ∞)
    [IsManifold I n M]
    [ContMDiffVectorBundle n E TM I] [IsContMDiffRiemannianBundle I n E TM]
    (b : Module.Basis ι ℝ E) (c : M) :
    ContDiffOn ℝ n (coordinateEllipticMatrix (I := I) b c) (extChartAt I c).target :=
  contDiffOn_densityWeightedInverse _ (contDiffOn_coordinateMetric_of_order n b c)
    (fun z hz => (coordinateMetric_posDef b c z hz).det_pos)

end AlmostSchur
