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

public import LeanPool.PoincareGeometry.AlmostSchur.DensityComparison
public import LeanPool.PoincareGeometry.AlmostSchur.WeakKernelGluing

/-!
# The chartwise weak gradient kernel for actual Riemannian volume

We never assume that an entire chart target is connected. Nested interior balls
give Euclidean local AE constants; compact-set density comparison transfers them
to the actual normalized `riemannianVolume`. Abstract countable gluing then yields
the global constant. No Hausdorff-volume identification is used.

Source APIs: `chartPushforward_measure_comparison` in `DensityComparison`,
Mathlib `MeasureTheory/Measure/AbsolutelyContinuous.lean`
(`Measure.absolutelyContinuous_of_le_smul`), and `MeasureTheory/Measure/Map.lean`
(`ae_of_ae_map`). Only the upper density bound is needed for this direction of
null-set transport; the reverse bound is not assumed or used as an identity.
-/

@[expose] public noncomputable section

open Bundle Set MeasureTheory Metric Filter
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]

/-- A Euclidean AE constant on a compact coordinate set transfers to actual
Riemannian volume on the corresponding part of the chart source. The implication
form avoids requiring the chart map to be measurable outside its source. -/
theorem ae_eq_const_of_chart_comp_on_compact (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    {u : M → ℝ} {k : ℝ}
    (hu : (u ∘ (extChartAt I c).symm) =ᵐ[(volume : Measure E).restrict K]
      (fun _ => k)) :
    ∀ᵐ x ∂riemannianVolume (I := I),
      x ∈ (extChartAt I c).source → (extChartAt I c) x ∈ K → u x = k := by
  let φ := extChartAt I c
  let ν := riemannianVolume (I := I) (M := M)
  let η := Measure.map φ (ν.restrict φ.source)
  have hs : MeasurableSet φ.source := (isOpen_extChartAt_source (I := I) c).measurableSet
  have hφ : AEMeasurable φ (ν.restrict φ.source) :=
    aemeasurable_restrict_of_measurable_subtype hs
      (continuousOn_extChartAt (I := I) c).domRestrict.measurable
  obtain ⟨_, B, _, _, _, hdom⟩ := chartPushforward_measure_comparison (I := I) c hK hKt
  have huη : ∀ᵐ z ∂η.restrict K, u (φ.symm z) = k :=
    (Measure.absolutelyContinuous_of_le_smul hdom).ae_le hu
  have hp : ∀ᵐ z ∂η, z ∈ K → u (φ.symm z) = k :=
    (ae_restrict_iff' hK.measurableSet).1 huη
  have hpull := (ae_restrict_iff' hs).1 (ae_of_ae_map hφ hp)
  filter_upwards [hpull] with x hx hxs hxK
  simpa only [φ.left_inv hxs] using hx hxs hxK

/-- Weak zero derivatives in a single chart produce an open neighborhood of its
center on which the original function is AE constant for actual Riemannian volume.
Only interior balls are required to be connected. -/
theorem exists_open_ae_eq_const_of_chart_weakDeriv_eq_zero (c : M) {u : M → ℝ}
    (hu : LocallyIntegrableOn (u ∘ (extChartAt I c).symm)
      (extChartAt I c).target volume)
    (hweak : ∀ (ψ : E → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (extChartAt I c).target → ∀ v : E,
        ∫ z, (u ∘ (extChartAt I c).symm) z * fderiv ℝ ψ z v = 0) :
    ∃ V : Set M, IsOpen V ∧ c ∈ V ∧
      ∃ k : ℝ, u =ᵐ[(riemannianVolume (I := I)).restrict V] (fun _ => k) := by
  let φ := extChartAt I c
  have hc : c ∈ φ.source := mem_extChartAt_source c
  obtain ⟨d, hd, hdT⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) c)
    (φ c) (φ.map_source hc)
  have houter : closedBall (φ c) (d / 2) ⊆ φ.target :=
    (closedBall_subset_ball (by linarith : d / 2 < d)).trans hdT
  obtain ⟨k, hk⟩ := ae_eq_const_on_ball_of_weakDeriv_eq_zero hu hweak houter
    (show 0 < d / 4 by positivity) (show d / 4 < d / 2 by linarith)
  let K := closedBall (φ c) (d / 8)
  have hKball : K ⊆ ball (φ c) (d / 4) :=
    closedBall_subset_ball (by linarith : d / 8 < d / 4)
  have hKT : K ⊆ φ.target :=
    (closedBall_subset_ball (by linarith : d / 8 < d)).trans hdT
  have hkK : (u ∘ φ.symm) =ᵐ[(volume : Measure E).restrict K] (fun _ => k) :=
    ae_restrict_of_ae_restrict_of_subset hKball hk
  have htransfer := ae_eq_const_of_chart_comp_on_compact c (isCompact_closedBall _ _) hKT hkK
  let V := φ.source ∩ φ ⁻¹' ball (φ c) (d / 8)
  have hV : IsOpen V := (continuousOn_extChartAt (I := I) c).isOpen_inter_preimage
    (isOpen_extChartAt_source (I := I) c) isOpen_ball
  refine ⟨V, hV, ⟨hc, mem_ball_self (by positivity)⟩, k, ?_⟩
  apply (ae_restrict_iff' hV.measurableSet).2
  filter_upwards [htransfer] with x hx hxV
  exact hx hxV.1 (ball_subset_closedBall hxV.2)

/-- Chartwise distributional zero derivatives imply global AE constancy for the
actual Riemannian volume on a preconnected manifold. The Lindelöf assumption above
supplies the countable gluing; compact manifolds are included without an additional
compactness requirement here. No chart-target connectedness is assumed. -/
theorem ae_eq_const_of_chart_weakDeriv_eq_zero [PreconnectedSpace M] {u : M → ℝ}
    (hu : ∀ c : M, LocallyIntegrableOn (u ∘ (extChartAt I c).symm)
      (extChartAt I c).target volume)
    (hweak : ∀ (c : M) (ψ : E → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (extChartAt I c).target → ∀ v : E,
        ∫ z, (u ∘ (extChartAt I c).symm) z * fderiv ℝ ψ z v = 0) :
    ∃ k : ℝ, u =ᵐ[riemannianVolume (I := I)] (fun _ => k) := by
  let : (riemannianVolume (I := I) (M := M)).IsOpenPosMeasure :=
    ⟨fun V hV hne => ne_of_gt (riemannianVolume_open_pos (I := I) hV hne)⟩
  exact ae_eq_const_of_locally_ae_eq_const fun c =>
    exists_open_ae_eq_const_of_chart_weakDeriv_eq_zero c (hu c) (hweak c)

end AlmostSchur
