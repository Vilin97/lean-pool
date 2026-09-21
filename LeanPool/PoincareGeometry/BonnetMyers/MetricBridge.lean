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

import LeanPool.PoincareGeometry.BonnetMyers.GlobalDistance

/-!
# The finite metric behind the Riemannian edistance

`EMetricSpace.ofRiemannianMetric` is the right construction before connectedness
has been used, because Mathlib's path infimum is extended-valued.  On the
connected manifolds in the entry, `GlobalDistance` proves that all those
values are finite.  This file records the canonical finite metric obtained by
that proof and the exact completeness transfer needed by a Hopf--Rinow layer.
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

section

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
  [IsManifold I 1 M]

/-- The finite metric obtained from the Riemannian edistance on a connected
manifold.  The proof that the extended distance is finite is kept explicit,
so this definition cannot silently change the uniform structure. -/
noncomputable def finiteRiemannianMetricSpace
    [T3Space M] (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) : MetricSpace M := by
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : IsRiemannianManifold I M := by infer_instance
  have hfin : ∀ x y : M, edist x y ≠ (⊤ : ℝ≥0∞) := by
    intro x y htop
    exact (ne_of_lt (edist_lt_top_of_connected (I := I) x y)) htop
  exact EMetricSpace.toMetricSpace hfin

theorem finiteRiemannianMetricSpace_edist_eq_riemannianEDist
    [T3Space M] (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    ∀ x y : M, edist x y = riemannianEDist I x y := by
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : IsRiemannianManifold I M := by infer_instance
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  intro x y
  exact (IsRiemannianManifold.out (I := I) (M := M) x y)

/-- The finite metric is obtained by taking the real value of the intrinsic
extended distance.  This records the conversion explicitly because both the
original Riemannian `EMetricSpace` and the induced `MetricSpace` are present
in the Hopf--Rinow argument. -/
theorem finiteRiemannianMetricSpace_dist_eq_riemannianEDist_toReal
    [T3Space M] (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    ∀ x y : M, dist x y = (riemannianEDist I x y).toReal := by
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : IsRiemannianManifold I M := by infer_instance
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  intro x y
  change (edist x y).toReal = (riemannianEDist I x y).toReal
  rw [IsRiemannianManifold.out (I := I) (M := M) x y]

/-- In the finite metric installed from a connected Riemannian manifold, the
original extended Riemannian distance is exactly the extended-real image of
the finite distance.  This is stronger than the accompanying `toReal`
statement and is the conversion needed to turn a metric minimizing segment
back into an intrinsic Riemannian one. -/
theorem finiteRiemannianMetricSpace_riemannianEDist_eq_ofReal_dist
    [T3Space M] (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    ∀ x y : M, riemannianEDist I x y = ENNReal.ofReal (dist x y) := by
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : IsRiemannianManifold I M := by infer_instance
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  intro x y
  have hfinite : riemannianEDist I x y ≠ (⊤ : ℝ≥0∞) := by
    rw [← finiteRiemannianMetricSpace_edist_eq_riemannianEDist
      (I := I) (M := M) g x y]
    exact ne_of_lt (edist_lt_top_of_connected (I := I) x y)
  calc
    riemannianEDist I x y = ENNReal.ofReal (riemannianEDist I x y).toReal :=
      (ENNReal.ofReal_toReal hfinite).symm
    _ = ENNReal.ofReal (dist x y) := by
      rw [finiteRiemannianMetricSpace_dist_eq_riemannianEDist_toReal
        (I := I) (M := M) g x y]

theorem completeSpace_finiteRiemannianMetricSpace
    [T3Space M] (g : ContMDiffRiemannianMetric I ∞ E TM)
    (hcomplete : @CompleteSpace M
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace.toUniformSpace) :
    @CompleteSpace M
      (finiteRiemannianMetricSpace (I := I) (M := M) g).toUniformSpace := by
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : IsRiemannianManifold I M := by infer_instance
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  exact hcomplete

end

end BonnetMyersEntry
