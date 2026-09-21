/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.MetricHopfRinow
import LeanPool.PoincareGeometry.BonnetMyers.MetricBridge
import LeanPool.PoincareGeometry.BonnetMyers.LocalCompactness
import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-!
# Intrinsic intermediates for the Riemannian metric

This is the Riemannian input to the metric Hopf--Rinow argument.  It derives
an approximate intermediate point directly from an arbitrarily short smooth
path and the additivity of its length; no minimizing path or geodesic is used.
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

/-- The connected finite Riemannian metric has approximate intermediate
points.  The point is found by the intermediate value theorem on the distance
along a smooth path whose length is shorter than the prescribed sum of radii. -/
theorem finiteRiemannianMetricSpace_hasApproximateIntermediate
    [T3Space M] (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    MetricHopfRinow.HasApproximateIntermediate M := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  have hed (p q : M) : edist p q = riemannianEDist I p q :=
    finiteRiemannianMetricSpace_edist_eq_riemannianEDist (I := I) (M := M) g p q
  have hriem_ne_top (p q : M) : riemannianEDist I p q ≠ ⊤ := by
    rw [← hed p q]
    exact ne_of_lt (edist_lt_top_of_connected (I := I) p q)
  have hdist_eq (p q : M) : dist p q = (riemannianEDist I p q).toReal :=
    finiteRiemannianMetricSpace_dist_eq_riemannianEDist_toReal
      (I := I) (M := M) g p q
  intro x z a b ha hb hdist
  by_cases hsmall : dist x z ≤ a
  · refine ⟨z, hsmall, ?_⟩
    simpa using hb
  have halong : a < dist x z := lt_of_not_ge hsmall
  have hab : 0 < a + b := by linarith
  have hriem : riemannianEDist I x z < ENNReal.ofReal (a + b) := by
    apply (ENNReal.toReal_lt_toReal (hriem_ne_top x z) ENNReal.ofReal_ne_top).mp
    simpa [ENNReal.toReal_ofReal hab.le, hdist_eq x z] using hdist
  obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlength⟩ :=
    exists_lt_of_riemannianEDist_lt hriem
  have hγcont : ContinuousOn γ (Icc (0 : ℝ) 1) := hγsmooth.continuousOn
  have hdistcont : ContinuousOn (fun t ↦ dist x (γ t)) (Icc (0 : ℝ) 1) := by
    simpa [Function.comp_def] using
      continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγcont)
  have hainrange : a ∈ Icc (dist x (γ 0)) (dist x (γ 1)) := by
    constructor
    · simpa [hγ0] using ha.le
    · simpa [hγ1] using halong.le
  obtain ⟨t, ht, hta⟩ :=
    intermediate_value_Icc (f := fun s ↦ dist x (γ s)) zero_le_one hdistcont hainrange
  have hpref : riemannianEDist I x (γ t) ≤ pathELength I γ 0 t := by
    apply riemannianEDist_le_pathELength
    · apply hγsmooth.mono
      intro s hs
      exact ⟨hs.1, le_trans hs.2 ht.2⟩
    · exact hγ0
    · rfl
    · exact ht.1
  have htail : riemannianEDist I (γ t) z ≤ pathELength I γ t 1 := by
    apply riemannianEDist_le_pathELength
    · apply hγsmooth.mono
      intro s hs
      exact ⟨le_trans ht.1 hs.1, hs.2⟩
    · rfl
    · exact hγ1
    · exact ht.2
  have hpref' : ENNReal.ofReal a ≤ pathELength I γ 0 t := by
    calc
      ENNReal.ofReal a = riemannianEDist I x (γ t) := by
        rw [← show (riemannianEDist I x (γ t)).toReal = a by
          simpa [hdist_eq x (γ t)] using hta]
        exact ENNReal.ofReal_toReal (hriem_ne_top x (γ t))
      _ ≤ pathELength I γ 0 t := hpref
  have hsum : ENNReal.ofReal a + pathELength I γ t 1 <
      ENNReal.ofReal a + ENNReal.ofReal b := by
    calc
      ENNReal.ofReal a + pathELength I γ t 1 ≤
          pathELength I γ 0 t + pathELength I γ t 1 :=
        add_le_add_left hpref' _
      _ = pathELength I γ 0 1 := pathELength_add ht.1 ht.2
      _ < ENNReal.ofReal (a + b) := hγlength
      _ = ENNReal.ofReal a + ENNReal.ofReal b := ENNReal.ofReal_add ha.le hb.le
  have htail' : pathELength I γ t 1 < ENNReal.ofReal b :=
    (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).mp hsum
  have hriemtail : riemannianEDist I (γ t) z < ENNReal.ofReal b := by
    exact lt_of_le_of_lt htail htail'
  have hdisttail : dist (γ t) z < b := by
    rw [hdist_eq (γ t) z]
    have hreal : (riemannianEDist I (γ t) z).toReal < (ENNReal.ofReal b).toReal :=
      (ENNReal.toReal_lt_toReal hriemtail.ne_top ENNReal.ofReal_ne_top).mpr hriemtail
    simpa [ENNReal.toReal_ofReal hb.le] using hreal
  exact ⟨γ t, le_of_eq hta, hdisttail⟩

/-- Metric completeness of a connected finite-dimensional Riemannian manifold
implies properness of its finite intrinsic metric.  This is the compactness
half of Hopf--Rinow; it uses short smooth paths for intrinsicity and never
postulates a minimizing geodesic. -/
theorem finiteRiemannianMetricSpace_properSpace
    [T3Space M] (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    CompleteSpace M →
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    ProperSpace M := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  intro hcomplete
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  letI : CompleteSpace M :=
    completeSpace_finiteRiemannianMetricSpace (I := I) (M := M) g hcomplete
  apply MetricHopfRinow.properSpace_of_complete_of_localCompact_of_approximateIntermediate
  · intro x
    exact exists_compact_finiteRiemannian_closedBall (I := I) (M := M) g x
  · exact finiteRiemannianMetricSpace_hasApproximateIntermediate (I := I) (M := M) g

/-- On a complete connected Riemannian manifold, every fraction of the finite
intrinsic distance is attained.  This exposes the exact-intermediate part of
Hopf--Rinow for later coherent segment construction. -/
theorem finiteRiemannianMetricSpace_exists_intermediate_of_complete
    [T3Space M] (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    CompleteSpace M →
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    ∀ x z : M, ∀ r : ℝ, 0 ≤ r → r ≤ dist x z →
      ∃ y : M, dist x y = r ∧ dist y z = dist x z - r := by
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
  intro x z r hr0 hrd
  exact MetricHopfRinow.exists_intermediate_of_properSpace
    (finiteRiemannianMetricSpace_hasApproximateIntermediate (I := I) (M := M) g)
    x z hr0 hrd

end BonnetMyersEntry
