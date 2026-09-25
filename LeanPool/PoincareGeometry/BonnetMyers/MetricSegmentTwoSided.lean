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

public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentGluing

/-!
# Two-sided local geodesic pieces along exact metric segments

Reversing the compact segment parameter turns the fixed right-hand local
geodesic supplied by `MetricSegmentGluing` into the corresponding left-hand
statement.  Keeping the reversal explicit avoids any hidden orientation or
endpoint convention in the later interval-gluing argument.
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

namespace MetricHopfRinow

/-- Reverse the orientation of the closed parameter interval of a metric
segment. -/
def reverseSegmentParameter {X : Type*} [PseudoMetricSpace X] {x z : X}
    (p : SegmentParameter x z) : SegmentParameter x z :=
  ⟨dist x z - (p : ℝ), sub_nonneg.mpr p.2.2,
    sub_le_self _ p.2.1⟩

@[simp] theorem coe_reverseSegmentParameter
    {X : Type*} [PseudoMetricSpace X] {x z : X}
    (p : SegmentParameter x z) :
    (reverseSegmentParameter p : ℝ) = dist x z - (p : ℝ) := rfl

@[simp] theorem reverseSegmentParameter_involutive
    {X : Type*} [PseudoMetricSpace X] {x z : X}
    (p : SegmentParameter x z) :
    reverseSegmentParameter (reverseSegmentParameter p) = p := by
  apply Subtype.ext
  simp only [coe_reverseSegmentParameter]
  ring

theorem continuous_reverseSegmentParameter
    {X : Type*} [PseudoMetricSpace X] {x z : X} :
    Continuous (reverseSegmentParameter : SegmentParameter x z →
      SegmentParameter x z) := by
  exact Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _

end MetricHopfRinow
/-- The fixed-local-geodesic realization also holds to the left of each
nearby segment point.  Its positive local time is the distance travelled in
the reversed segment orientation. -/
theorem riemannian_metric_segment_exists_local_geodesic_left
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
      ∀ r : MetricHopfRinow.SegmentParameter x z,
        ∃ N : Set M, IsOpen N ∧ γ r ∈ N ∧
          ∀ t : MetricHopfRinow.SegmentParameter x z, γ t ∈ N →
            (t : ℝ) < (r : ℝ) →
            ∃ c : M, ∃ v : TM c,
            ∃ β : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M)
                cov c v,
                ‖v‖ = 1 ∧
                IntrinsicGeodesic.LocalGeodesic.curve β 0 = γ t ∧
                ∃ ρ > (0 : ℝ),
                  ∀ s : MetricHopfRinow.SegmentParameter x z,
                    (s : ℝ) < (t : ℝ) →
                    (t : ℝ) - (s : ℝ) < ρ →
                    IntrinsicGeodesic.LocalGeodesic.curve β
                      ((t : ℝ) - (s : ℝ)) = γ s := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := by infer_instance
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  let cov := leviCivita (I := I) (M := M) g
  dsimp only
  intro x z γ hγ hsegment r
  let rev := MetricHopfRinow.reverseSegmentParameter
    (x := x) (z := z)
  let γrev : MetricHopfRinow.SegmentParameter x z → M := γ ∘ rev
  have hγrev : Continuous γrev :=
    hγ.comp MetricHopfRinow.continuous_reverseSegmentParameter
  have hsegmentRev : ∀ p q, riemannianEDist I (γrev p) (γrev q) =
      ENNReal.ofReal |(q : ℝ) - (p : ℝ)| := by
    intro p q
    rw [show γrev p = γ (rev p) by rfl, show γrev q = γ (rev q) by rfl,
      hsegment (rev p) (rev q)]
    congr 1
    simp only [rev, MetricHopfRinow.coe_reverseSegmentParameter]
    rw [show (dist x z - (q : ℝ)) - (dist x z - (p : ℝ)) =
      (p : ℝ) - (q : ℝ) by ring, abs_sub_comm]
  obtain ⟨N, hNopen, hrN, hlocal⟩ :=
    riemannian_metric_segment_exists_local_geodesic_right
      (I := I) (M := M) g γrev hγrev hsegmentRev (rev r)
  have hrN' : γ r ∈ N := by
    change γ (MetricHopfRinow.reverseSegmentParameter
      (MetricHopfRinow.reverseSegmentParameter r)) ∈ N at hrN
    rwa [MetricHopfRinow.reverseSegmentParameter_involutive] at hrN
  refine ⟨N, hNopen, hrN', ?_⟩
  intro t htN htr
  have hrevrt : (rev r : ℝ) < (rev t : ℝ) := by
    simp only [rev, MetricHopfRinow.coe_reverseSegmentParameter]
    linarith
  have htNrev : γrev (rev t) ∈ N := by
    change γ (MetricHopfRinow.reverseSegmentParameter
      (MetricHopfRinow.reverseSegmentParameter t)) ∈ N
    rwa [MetricHopfRinow.reverseSegmentParameter_involutive]
  obtain ⟨c, v, β, hvUnit, hβzero, ρ, hρ, hβ⟩ :=
    hlocal (rev t) htNrev hrevrt
  refine ⟨c, v, β, hvUnit, ?_, ρ, hρ, ?_⟩
  · change β.curve 0 = γ (MetricHopfRinow.reverseSegmentParameter
      (MetricHopfRinow.reverseSegmentParameter t)) at hβzero
    rwa [MetricHopfRinow.reverseSegmentParameter_involutive] at hβzero
  · intro s hst hgap
    have hrevts : (rev t : ℝ) < (rev s : ℝ) := by
      simp only [rev, MetricHopfRinow.coe_reverseSegmentParameter]
      linarith
    have hgapRev : (rev s : ℝ) - (rev t : ℝ) < ρ := by
      simp only [rev, MetricHopfRinow.coe_reverseSegmentParameter]
      convert hgap using 1 <;> ring
    have hs := hβ (rev s) hrevts hgapRev
    change β.curve ((rev s : ℝ) - (rev t : ℝ)) =
      γ (MetricHopfRinow.reverseSegmentParameter
        (MetricHopfRinow.reverseSegmentParameter s)) at hs
    rw [MetricHopfRinow.reverseSegmentParameter_involutive] at hs
    convert hs using 1 <;>
      simp only [rev, MetricHopfRinow.coe_reverseSegmentParameter] <;> ring

end BonnetMyersEntry
