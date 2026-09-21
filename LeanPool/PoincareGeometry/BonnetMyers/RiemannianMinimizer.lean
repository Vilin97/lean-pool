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

import LeanPool.PoincareGeometry.BonnetMyers.RiemannianHopfRinow
import LeanPool.PoincareGeometry.BonnetMyers.MetricGeodesic

/-!
# Metric minimizers for complete Riemannian manifolds

This composes the Riemannian properness theorem with the independent metric
segment construction.  It establishes an actual continuous distance-realizing
segment for the finite Riemannian metric.  The later smooth upgrade must still
show that this metric minimizer is the locally constructed Riemannian
geodesic; that analytic bridge is intentionally not assumed here.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Completeness of the supplied Riemannian metric gives a continuous exact
minimizing segment between every pair of points in its finite intrinsic
metric.  No minimizing geodesic is taken as a hypothesis. -/
theorem finiteRiemannianMetricSpace_exists_metric_segment_of_complete
    [T3Space M] (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    CompleteSpace M →
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    ∀ x z : M,
      ∃ γ : MetricHopfRinow.SegmentParameter x z → M, Continuous γ ∧
        γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        γ ⟨dist x z, ⟨dist_nonneg, le_rfl⟩⟩ = z ∧
        ∀ r s, dist (γ r) (γ s) = |(s : ℝ) - (r : ℝ)| := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  intro hcomplete
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  letI : ProperSpace M :=
    finiteRiemannianMetricSpace_properSpace (I := I) (M := M) g hcomplete
  intro x z
  exact MetricHopfRinow.exists_metric_segment_of_properSpace
    (finiteRiemannianMetricSpace_hasApproximateIntermediate (I := I) (M := M) g) x z

/-- The metric segment obtained from completeness is also an exact segment
for the original Riemannian extended distance.  This is not a smoothness
claim: it records the precise intrinsic equality which the later regularity
argument must upgrade to a smooth minimizing geodesic. -/
theorem finiteRiemannianMetricSpace_exists_riemannian_metric_segment_of_complete
    [T3Space M] (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    CompleteSpace M →
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    ∀ x z : M,
      ∃ γ : MetricHopfRinow.SegmentParameter x z → M, Continuous γ ∧
        γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        γ ⟨dist x z, ⟨dist_nonneg, le_rfl⟩⟩ = z ∧
        ∀ r s, riemannianEDist I (γ r) (γ s) =
          ENNReal.ofReal |(s : ℝ) - (r : ℝ)| := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  intro hcomplete
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  intro x z
  obtain ⟨γ, hγ, hzero, hlast, hpair⟩ :=
    finiteRiemannianMetricSpace_exists_metric_segment_of_complete
      (I := I) (M := M) g hcomplete x z
  refine ⟨γ, hγ, hzero, hlast, ?_⟩
  intro r s
  rw [finiteRiemannianMetricSpace_riemannianEDist_eq_ofReal_dist
    (I := I) (M := M) g]
  rw [hpair r s]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M] in
/-- Every subsegment of an exact Riemannian metric segment is approached from
above by a smooth path with the prescribed endpoints.  The result is a
concrete consequence of the path-infimum definition of `riemannianEDist`; it
does not smuggle any differentiability into the metric segment itself. -/
theorem exists_smooth_path_lt_of_riemannian_metric_segment
    [PseudoMetricSpace M] [RiemannianBundle TM]
    {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M)
    (hsegment : ∀ r s, riemannianEDist I (γ r) (γ s) =
      ENNReal.ofReal |(s : ℝ) - (r : ℝ)|)
    (r s : MetricHopfRinow.SegmentParameter x z) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ → M, η 0 = γ r ∧ η 1 = γ s ∧
      CMDiff[Icc (0 : ℝ) 1] 1 η ∧
      pathELength I η 0 1 < ENNReal.ofReal (|(s : ℝ) - (r : ℝ)| + ε) := by
  apply exists_lt_of_riemannianEDist_lt
  rw [hsegment r s]
  apply (ENNReal.ofReal_lt_ofReal_iff (by linarith [abs_nonneg ((s : ℝ) - (r : ℝ))])).2
  linarith [abs_nonneg ((s : ℝ) - (r : ℝ))]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M] in
/-- The smooth approximants to a metric subsegment can be chosen locally
constant at their endpoints.  This is the form needed when adjacent
approximants are later spliced into a variation; it is still only an
approximation statement and does not assert smoothness of the metric segment
itself. -/
theorem exists_smooth_path_lt_locally_constant_of_riemannian_metric_segment
    [PseudoMetricSpace M] [RiemannianBundle TM]
    {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M)
    (hsegment : ∀ r s, riemannianEDist I (γ r) (γ s) =
      ENNReal.ofReal |(s : ℝ) - (r : ℝ)|)
    (r s : MetricHopfRinow.SegmentParameter x z) {a b ε : ℝ}
    (hab : a < b) (hε : 0 < ε) :
    ∃ η : ℝ → M, η a = γ r ∧ η b = γ s ∧ CMDiff 1 η ∧
      pathELength I η a b < ENNReal.ofReal (|(s : ℝ) - (r : ℝ)| + ε) ∧
      η =ᶠ[𝓝 a] (fun _ ↦ γ r) ∧ η =ᶠ[𝓝 b] (fun _ ↦ γ s) := by
  apply exists_lt_locally_constant_of_riemannianEDist_lt (x := γ r) (y := γ s) _ hab
  rw [hsegment r s]
  apply (ENNReal.ofReal_lt_ofReal_iff (by
    linarith [abs_nonneg ((s : ℝ) - (r : ℝ))])).2
  linarith [abs_nonneg ((s : ℝ) - (r : ℝ))]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M] in
/-- An exact metric segment already has the variational lower-bound property
of a minimizer: every smooth competitor with the same two subsegment endpoints
has at least its prescribed intrinsic length.  The statement intentionally
does not call the metric segment smooth; it is the endpoint-minimizing fact
that the later regularity and second-variation arguments must consume. -/
theorem riemannian_metric_segment_le_pathELength
    [PseudoMetricSpace M] [RiemannianBundle TM]
    {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M)
    (hsegment : ∀ r s, riemannianEDist I (γ r) (γ s) =
      ENNReal.ofReal |(s : ℝ) - (r : ℝ)|)
    (r s : MetricHopfRinow.SegmentParameter x z) {a b : ℝ}
    (hab : a ≤ b) {η : ℝ → M}
    (hη : ContMDiffOn (𝓘(ℝ, ℝ)) I 1 η (Icc a b))
    (hηa : η a = γ r) (hηb : η b = γ s) :
    ENNReal.ofReal |(s : ℝ) - (r : ℝ)| ≤ pathELength I η a b := by
  rw [← hsegment r s]
  exact riemannianEDist_le_pathELength hη hηa hηb hab

end BonnetMyersEntry
