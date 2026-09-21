/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.LocalDistanceRealization
import LeanPool.PoincareGeometry.BonnetMyers.RiemannianMinimizer

/-!
# Local smooth connectors along an exact metric segment

An exact Hopf--Rinow metric segment is initially only continuous.  The local
distance-realization theorem supplies, around each of its parameter values,
smooth normal geodesics to all nearby segment points with exactly the same
length as the corresponding metric subsegment.  This is the local geometric
input for the remaining compatibility and smooth-upgrade argument.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T3Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
/-- Near each parameter of an exact Riemannian metric segment, every nearby
segment point is joined to the centre point by a smooth normal geodesic whose
length is exactly the corresponding parameter gap. -/
theorem riemannian_metric_segment_eventually_exists_distanceRealizing_geodesic
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    let cov := leviCivita (I := I) (M := M) g
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    ∀ {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M),
      Continuous γ →
      (∀ r s, riemannianEDist I (γ r) (γ s) =
        ENNReal.ofReal |(s : ℝ) - (r : ℝ)|) →
      ∀ t : MetricHopfRinow.SegmentParameter x z,
        ∃ ε > (0 : ℝ), ∀ s : MetricHopfRinow.SegmentParameter x z,
          |(s : ℝ) - (t : ℝ)| < ε →
          ∃ u : E, ∃ sol : LocalChartSecondOrderSolution I
          (LocalGeodesicData.coordinateAcceleration cov (γ t) b) (γ t) u,
          sol.radius = 2 ∧
          LocalChartSecondOrderSolution.curve sol 0 = γ t ∧
          LocalChartSecondOrderSolution.curve sol 1 = γ s ∧
          pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 =
            ENNReal.ofReal |(s : ℝ) - (t : ℝ)| ∧
          ∀ η : ℝ → M,
            η 0 = γ t → η 1 = γ s →
            ContMDiffOn (𝓘(ℝ, ℝ)) I 1 η (Icc (0 : ℝ) 1) →
            pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 ≤
              pathELength I η 0 1 := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  let cov := leviCivita (I := I) (M := M) g
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  dsimp only
  intro x z γ hγ hsegment t
  obtain ⟨N, hNopen, htN, hlocal⟩ :=
    exists_open_geodesically_distanceRealizing_neighborhood
      (I := I) (M := M) g (γ t)
  have hnear : γ ⁻¹' N ∈ 𝓝 t :=
    hγ.continuousAt.preimage_mem_nhds (hNopen.mem_nhds htN)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ε, hε, ?_⟩
  intro s hst
  have hs : s ∈ γ ⁻¹' N := hball (by
    change |(s : ℝ) - (t : ℝ)| < ε
    exact hst)
  obtain ⟨u, sol, hradius, hcurve0, hcurve1, hlength, hmin⟩ := hlocal (γ s) hs
  refine ⟨u, sol, hradius, hcurve0, hcurve1, ?_, hmin⟩
  rw [hlength, hsegment t s]

end BonnetMyersEntry
