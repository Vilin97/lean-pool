/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentTwoSided

/-!
# Dense local-geodesic loci of exact metric segments

The fixed local pieces obtained from corner rigidity occur densely from both
orientations.  Endpoint cases are included vacuously, while every other
parameter is approximated from the appropriate side inside the open normal
neighbourhood supplied at that parameter.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology RealInnerProductSpace

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

def IsLocallyGeodesicRightAt
    [PseudoMetricSpace M]
    [RiemannianBundle TM]
    (cov : CovariantDerivative I E TM)
    {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M)
    (t : MetricHopfRinow.SegmentParameter x z) : Prop :=
  ∃ c : M, ∃ v : TM c,
    ∃ β : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov c v,
      (‖v‖ = 1 ∨ (t : ℝ) = dist x z) ∧
      IntrinsicGeodesic.LocalGeodesic.curve β 0 = γ t ∧
      ∃ ρ > (0 : ℝ),
        ∀ s : MetricHopfRinow.SegmentParameter x z,
          (t : ℝ) < (s : ℝ) → (s : ℝ) - (t : ℝ) < ρ →
          IntrinsicGeodesic.LocalGeodesic.curve β
            ((s : ℝ) - (t : ℝ)) = γ s
theorem riemannian_metric_segment_dense_local_geodesic_right
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    let cov := leviCivita (I := I) (M := M) g
    ∀ {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M),
      Continuous γ →
      (∀ p q, riemannianEDist I (γ p) (γ q) =
        ENNReal.ofReal |(q : ℝ) - (p : ℝ)|) →
      Dense {t | IsLocallyGeodesicRightAt (I := I) (M := M) cov γ t} := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := by infer_instance
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  let cov := leviCivita (I := I) (M := M) g
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov 1 := by
    simpa [cov] using (leviCivitaSmooth (I := I) (M := M) g)
  dsimp only
  intro x z γ hγ hsegment
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro r
  rw [mem_closure_iff_nhds]
  intro U hU
  by_cases hrLast : (r : ℝ) = dist x z
  · have hlocalLast : IsLocallyGeodesicRightAt (I := I) (M := M) cov γ r := by
      let v : TM (γ r) := 0
      obtain ⟨β⟩ := IntrinsicGeodesic.exists_localGeodesic
        (I := I) (M := M) cov (γ r) v
      refine ⟨γ r, v, β, Or.inr hrLast,
        IntrinsicGeodesic.LocalGeodesic.curve_initial β,
        1, by norm_num, ?_⟩
      intro s hrs _
      have hsle : (s : ℝ) ≤ dist x z := s.2.2
      linarith
    exact ⟨r, mem_inter (mem_of_mem_nhds hU) hlocalLast⟩
  · have hrlt : (r : ℝ) < dist x z :=
      lt_of_le_of_ne r.2.2 hrLast
    obtain ⟨N, hNopen, hrN, hright⟩ :=
      riemannian_metric_segment_exists_local_geodesic_right
        (I := I) (M := M) g γ hγ hsegment r
    have hpreN : γ ⁻¹' N ∈ nhds r :=
      hγ.continuousAt.preimage_mem_nhds (hNopen.mem_nhds hrN)
    have hcommon : U ∩ γ ⁻¹' N ∈ nhds r := inter_mem hU hpreN
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hcommon
    let e : ℝ := min (δ / 2) ((dist x z - (r : ℝ)) / 2)
    have he : 0 < e := lt_min (by linarith) (by linarith)
    let q : MetricHopfRinow.SegmentParameter x z :=
      ⟨(r : ℝ) + e, by linarith [r.2.1], by
        have heGap : e ≤ (dist x z - (r : ℝ)) / 2 := min_le_right _ _
        linarith⟩
    have hrq : (r : ℝ) < (q : ℝ) := by
      dsimp [q]
      linarith
    have hqrBall : q ∈ Metric.ball r δ := by
      rw [Metric.mem_ball, dist_comm, Subtype.dist_eq, Real.dist_eq]
      dsimp [q]
      rw [show (r : ℝ) - ((r : ℝ) + e) = -e by ring,
        abs_neg, abs_of_pos he]
      have heδ : e ≤ δ / 2 := min_le_left _ _
      linarith
    have hqCommon := hball hqrBall
    obtain ⟨c, v, β, hv, hβzero, ρ, hρ, hβ⟩ :=
      hright q hqCommon.2 hrq
    have hqLocal : IsLocallyGeodesicRightAt (I := I) (M := M) cov γ q :=
      ⟨c, v, β, Or.inl hv, hβzero, ρ, hρ, hβ⟩
    exact ⟨q, hqCommon.1, hqLocal⟩

def IsLocallyGeodesicLeftAt
    [PseudoMetricSpace M]
    [RiemannianBundle TM]
    (cov : CovariantDerivative I E TM)
    {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M)
    (t : MetricHopfRinow.SegmentParameter x z) : Prop :=
  ∃ c : M, ∃ v : TM c,
    ∃ β : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov c v,
      (‖v‖ = 1 ∨ (t : ℝ) = 0) ∧
      IntrinsicGeodesic.LocalGeodesic.curve β 0 = γ t ∧
      ∃ ρ > (0 : ℝ),
        ∀ s : MetricHopfRinow.SegmentParameter x z,
          (s : ℝ) < (t : ℝ) → (t : ℝ) - (s : ℝ) < ρ →
          IntrinsicGeodesic.LocalGeodesic.curve β
            ((t : ℝ) - (s : ℝ)) = γ s
theorem riemannian_metric_segment_dense_local_geodesic_left
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    let cov := leviCivita (I := I) (M := M) g
    ∀ {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M),
      Continuous γ →
      (∀ p q, riemannianEDist I (γ p) (γ q) =
        ENNReal.ofReal |(q : ℝ) - (p : ℝ)|) →
      Dense {t | IsLocallyGeodesicLeftAt (I := I) (M := M) cov γ t} := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := by infer_instance
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  let cov := leviCivita (I := I) (M := M) g
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov 1 := by
    simpa [cov] using (leviCivitaSmooth (I := I) (M := M) g)
  dsimp only
  intro x z γ hγ hsegment
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro r
  rw [mem_closure_iff_nhds]
  intro U hU
  by_cases hrFirst : (r : ℝ) = 0
  · have hlocalFirst : IsLocallyGeodesicLeftAt (I := I) (M := M) cov γ r := by
      let v : TM (γ r) := 0
      obtain ⟨β⟩ := IntrinsicGeodesic.exists_localGeodesic
        (I := I) (M := M) cov (γ r) v
      refine ⟨γ r, v, β, Or.inr hrFirst,
        IntrinsicGeodesic.LocalGeodesic.curve_initial β,
        1, by norm_num, ?_⟩
      intro s hsr _
      have hsnonneg : 0 ≤ (s : ℝ) := s.2.1
      linarith
    exact ⟨r, mem_inter (mem_of_mem_nhds hU) hlocalFirst⟩
  · have hrpos : 0 < (r : ℝ) :=
      lt_of_le_of_ne r.2.1 (Ne.symm hrFirst)
    obtain ⟨N, hNopen, hrN, hleft⟩ :=
      riemannian_metric_segment_exists_local_geodesic_left
        (I := I) (M := M) g γ hγ hsegment r
    have hpreN : γ ⁻¹' N ∈ nhds r :=
      hγ.continuousAt.preimage_mem_nhds (hNopen.mem_nhds hrN)
    have hcommon : U ∩ γ ⁻¹' N ∈ nhds r := inter_mem hU hpreN
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hcommon
    let e : ℝ := min (δ / 2) ((r : ℝ) / 2)
    have he : 0 < e := lt_min (by linarith) (by linarith)
    let q : MetricHopfRinow.SegmentParameter x z :=
      ⟨(r : ℝ) - e, by
        have her : e ≤ (r : ℝ) / 2 := min_le_right _ _
        linarith, by linarith [r.2.2]⟩
    have hqr : (q : ℝ) < (r : ℝ) := by
      dsimp [q]
      linarith
    have hqrBall : q ∈ Metric.ball r δ := by
      rw [Metric.mem_ball, dist_comm, Subtype.dist_eq, Real.dist_eq]
      dsimp [q]
      rw [show (r : ℝ) - ((r : ℝ) - e) = e by ring, abs_of_pos he]
      have heδ : e ≤ δ / 2 := min_le_left _ _
      linarith
    have hqCommon := hball hqrBall
    obtain ⟨c, v, β, hv, hβzero, ρ, hρ, hβ⟩ :=
      hleft q hqCommon.2 hqr
    have hqLocal : IsLocallyGeodesicLeftAt (I := I) (M := M) cov γ q :=
      ⟨c, v, β, Or.inl hv, hβzero, ρ, hρ, hβ⟩
    exact ⟨q, hqCommon.1, hqLocal⟩

end BonnetMyersEntry
