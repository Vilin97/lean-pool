/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.HigherNormalChart

/-! # One invertible normal chart with its radial and metric identities -/

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
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- A single constructed local homeomorphism has the radial identity and
the full pole-normalized pullback metric on its source. Thus the metric and
topological constructions refer to the same map, including its derivative. -/
theorem exists_obata_normal_metric_chart
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
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
        (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (e u))
          (fderiv ℝ e u u) =
          (t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u)) •
            gradient (I := I) (obataRadial K a f) ((extChartAt I c).symm (e u))) ∧
      ∀ u ∈ e.source, u ≠ 0 → ∀ w v : E,
        let g := coordinateMetricBilinear (I := I) c z
        let angular := Real.sin (Real.sqrt K * (t * Real.sqrt (g u u))) ^ 2 / (K * g u u)
        coordinateMetricBilinear (I := I) c (e u)
          (fderiv ℝ e u w) (fderiv ℝ e u v) =
            angular * g w v + (t ^ 2 - angular) * (g u w * g u v / g u u) := by
  obtain ⟨t, ht, e, he0, hez, hd, hs, hinv, hsource, htarget, hrad, hgrad, hm⟩ :=
    exists_obata_normal_metric_chart_of_order 2 (by norm_num) b hf hK ha hb hH c hz hcrit hmax
  exact ⟨t, ht, e, he0, hez, hd, hs, hinv.of_le
    (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)),
    hsource, htarget, hrad, hgrad, hm⟩

end LichnerowiczObata
