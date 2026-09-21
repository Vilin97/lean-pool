/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentRegularity

/-!
# Coherent normal coordinates along metric segments

The local connector theorem is strengthened here by retaining one fixed
normal chart around each segment parameter.  Nearby points therefore have a
single continuous logarithm coordinate, its radial norm is the exact
parameter gap, and the corresponding radial geodesic is distance realizing.
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
/-- Around each parameter of an exact metric segment, one fixed normal chart
provides a continuous logarithm coordinate for nearby segment points.  Its
radial norm is exactly the parameter gap, and its radial geodesic realizes
the corresponding subsegment distance. -/
theorem riemannian_metric_segment_exists_continuous_local_log
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
        ∃ ε > (0 : ℝ), ∃ q : MetricHopfRinow.SegmentParameter x z → E,
          q t = 0 ∧ ContinuousAt q t ∧
          ∀ s : MetricHopfRinow.SegmentParameter x z,
            |(s : ℝ) - (t : ℝ)| < ε →
            ‖LocalGeodesicData.coordinateFrameCombination
              (I := I) (M := M) (x₀ := γ t) b (q s) (γ t)‖ =
                |(s : ℝ) - (t : ℝ)| ∧
            ∃ sol : LocalChartSecondOrderSolution I
              (LocalGeodesicData.coordinateAcceleration cov (γ t) b) (γ t) (q s),
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
  let c : M := γ t
  let zc : E := extChartAt I c c
  obtain ⟨F, ψ, U, V, W, r, hUopen, hzeroU, hVopen, hzcV, hF, hψ,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, hWopen, hzeroW,
    hWsubset, hFWopen, hzcFW, hr, hball, hgeodesic⟩ :=
      exists_normalCoordinate_unrestricted_lengthMinimizing_geodesic
        (I := I) (M := M) g c
  let N : Set M :=
    (extChartAt I c).source ∩ (extChartAt I c) ⁻¹' (F '' W)
  have hNopen : IsOpen N :=
    isOpen_extChartAt_preimage' (I := I) c hFWopen
  have hcN : c ∈ N := by
    refine ⟨mem_extChartAt_source (I := I) c, ?_⟩
    simpa [zc] using hzcFW
  have hnear : γ ⁻¹' N ∈ 𝓝 t :=
    hγ.continuousAt.preimage_mem_nhds (hNopen.mem_nhds hcN)
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.mp hnear
  let q : MetricHopfRinow.SegmentParameter x z → E :=
    fun s ↦ ψ (extChartAt I c (γ s))
  have hqt : q t = 0 := by
    change ψ (extChartAt I c c) = 0
    rw [← hFzero]
    exact hleft 0 hzeroU
  have hchartγ : ContinuousAt (fun s ↦ extChartAt I c (γ s)) t := by
    exact (continuousAt_extChartAt (I := I) c).comp hγ.continuousAt
  have hψat : ContinuousAt ψ (extChartAt I c c) :=
    hψ.continuousOn.continuousAt (hVopen.mem_nhds hzcV)
  have hqcont : ContinuousAt q t := by
    exact hψat.comp_of_eq hchartγ rfl
  refine ⟨ε, hε, q, hqt, hqcont, ?_⟩
  intro s hst
  have hsN : γ s ∈ N := hεN (by
    change |(s : ℝ) - (t : ℝ)| < ε
    exact hst)
  obtain ⟨u, huW, hFu⟩ := hsN.2
  have hqs : q s = u := by
    change ψ (extChartAt I c (γ s)) = u
    rw [← hFu]
    exact hleft u (hWsubset huW)
  have hqW : q s ∈ W := by rwa [hqs]
  obtain ⟨sol, hradius, hcoordinate, hlength, _hgauss, _hspeed,
    _hspeedAll, hdistRiem, hdistMetric, _hsubdist, hmin⟩ :=
    hgeodesic (q s) hqW
  have hendpoint : (extChartAt I c).symm (F (q s)) = γ s := by
    have hchartV : extChartAt I c (γ s) ∈ V := by
      exact hFmemV u (hWsubset huW) |> fun h ↦ hFu ▸ h
    rw [show F (q s) = extChartAt I c (γ s) by
      change F (ψ (extChartAt I c (γ s))) = extChartAt I c (γ s)
      exact hright _ hchartV]
    exact (extChartAt I c).left_inv hsN.1
  have hsegdist : dist c (γ s) = |(s : ℝ) - (t : ℝ)| := by
    rw [finiteRiemannianMetricSpace_dist_eq_riemannianEDist_toReal
      (I := I) (M := M) g, show c = γ t by rfl, hsegment t s,
      ENNReal.toReal_ofReal (abs_nonneg _)]
  have hnorm :
      ‖LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c) b (q s) c‖ =
        |(s : ℝ) - (t : ℝ)| := by
    rw [← hsegdist, ← hdistMetric, hendpoint]
  have hcurve1 : LocalChartSecondOrderSolution.curve sol 1 = γ s := by
    change (extChartAt I c).symm (sol.coordinate 1) = γ s
    rw [hcoordinate]
    exact hendpoint
  refine ⟨hnorm, sol, hradius, LocalChartSecondOrderSolution.curve_initial sol,
    hcurve1, ?_, ?_⟩
  · rw [hlength, hnorm]
  · intro η hη0 hη1 hη
    exact hmin η hη0 (hη1.trans hendpoint.symm) hη

end BonnetMyersEntry
