/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.FiniteGeodesicCover
import LeanPool.PoincareGeometry.BonnetMyers.ParallelConnection

/-!
# Local parallel fields on a global-geodesic cover

A finite local-geodesic cover identifies every selected local curve with the
global curve through an equality of tangent-bundle states.  This module turns
that equality into an explicit dependent-fibre reindexing map.  It therefore
allows a canonical local parallel field to be read as a field along the
actual global curve on its certified cover neighbourhood.

This is still a local reindexing operation.  Equality of fields constructed
from different cover members is a later transport-gluing theorem, not an
assumption made here.
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
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace IntrinsicGeodesic
namespace GlobalGeodesic
namespace FiniteLocalGeodesicCover

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- Reindex a tangent vector from a selected local geodesic to the matching
point of the global curve.  The equality used for the cast is extracted from
the cover's certified total-state agreement, rather than from an unchecked
base-curve coincidence. -/
def reindexTangent
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {a b : ℝ}
    (C : FiniteLocalGeodesicCover (I := I) (M := M) γ a b)
    (t : {q : ℝ // q ∈ C.centers}) (s : ℝ)
    (hs : s - t.1 ∈ Metric.ball (0 : ℝ) (C.radius t)) :
    TM (LocalGeodesic.curve (C.localGeodesic t) (s - t.1)) → TM (curve γ s) :=
  cast (congrArg (TangentSpace I) (C.curve_eq_of_mem t s hs).symm)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] in
private theorem cast_tangent_inner {x y : M}
    (hxy : x = y) (u v : TM x) :
    inner ℝ (cast (congrArg (TangentSpace I) hxy) u)
        (cast (congrArg (TangentSpace I) hxy) v) = inner ℝ u v := by
  subst y
  rfl

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] in
/-- Fibre reindexing through a certified curve equality preserves the
Riemannian inner product exactly. -/
theorem reindexTangent_inner
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {a b : ℝ}
    (C : FiniteLocalGeodesicCover (I := I) (M := M) γ a b)
    (t : {q : ℝ // q ∈ C.centers}) (s : ℝ)
    (hs : s - t.1 ∈ Metric.ball (0 : ℝ) (C.radius t))
    (u v : TM (LocalGeodesic.curve (C.localGeodesic t) (s - t.1))) :
    inner ℝ (C.reindexTangent t s hs u) (C.reindexTangent t s hs v) =
      inner ℝ u v := by
  unfold reindexTangent
  exact cast_tangent_inner (C.curve_eq_of_mem t s hs).symm u v

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type u)] in
private theorem cast_tangent_roundtrip {x y : M}
    (hxy : x = y) (w : TM x) :
    cast (congrArg (TangentSpace I) hxy.symm)
      (cast (congrArg (TangentSpace I) hxy) w) = w := by
  subst y
  rfl

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)] in
/-- Reindexing is inverse to the explicit fibre cast induced by the same
certified curve equality.  This is the safe way to prescribe a global tangent
vector as initial data for a local field. -/
theorem reindexTangent_apply_cast
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {a b : ℝ}
    (C : FiniteLocalGeodesicCover (I := I) (M := M) γ a b)
    (t : {q : ℝ // q ∈ C.centers}) (s : ℝ)
    (hs : s - t.1 ∈ Metric.ball (0 : ℝ) (C.radius t))
    (w : TM (curve γ s)) :
    C.reindexTangent t s hs
      (cast (congrArg (TangentSpace I) (C.curve_eq_of_mem t s hs)) w) = w := by
  unfold reindexTangent
  exact cast_tangent_roundtrip (C.curve_eq_of_mem t s hs) w

/-- A canonical local parallel field, reindexed to the global curve on the
intersection of the cover neighbourhood and the field's ODE interval. -/
def canonicalFrameParallelOnGlobal
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {a b : ℝ}
    (C : FiniteLocalGeodesicCover (I := I) (M := M) γ a b)
    (t : {q : ℝ // q ∈ C.centers}) {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun s ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov (curve γ t.1) (IntrinsicGeodesic.canonicalBasis (E := E))
        ((C.localGeodesic t).solution.coordinate s)
        ((C.localGeodesic t).solution.velocity s)) 0 w₀) :
    ∀ s : {q : ℝ // q - t.1 ∈
      Metric.ball (0 : ℝ) (min (C.radius t) wsol.radius)}, TM (curve γ s.1) :=
  fun s ↦
    C.reindexTangent t s.1
      (by
        apply Metric.mem_ball.mpr
        exact lt_of_lt_of_le (Metric.mem_ball.mp s.2) (min_le_left _ _))
      (LocalGeodesic.canonicalFrameParallel (I := I) (M := M)
        (C.localGeodesic t) wsol (s.1 - t.1))

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] in
/-- The global-curve presentation retains exactly the local field's inner
product at every point in its certified domain. -/
theorem canonicalFrameParallelOnGlobal_inner
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {a b : ℝ}
    (C : FiniteLocalGeodesicCover (I := I) (M := M) γ a b)
    (t : {q : ℝ // q ∈ C.centers}) {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun s ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov (curve γ t.1) (IntrinsicGeodesic.canonicalBasis (E := E))
        ((C.localGeodesic t).solution.coordinate s)
        ((C.localGeodesic t).solution.velocity s)) 0 w₀)
    (s : {q : ℝ // q - t.1 ∈
      Metric.ball (0 : ℝ) (min (C.radius t) wsol.radius)}) :
    inner ℝ (C.canonicalFrameParallelOnGlobal t wsol s)
        (C.canonicalFrameParallelOnGlobal t wsol s) =
      inner ℝ
        (LocalGeodesic.canonicalFrameParallel (I := I) (M := M)
          (C.localGeodesic t) wsol (s.1 - t.1))
        (LocalGeodesic.canonicalFrameParallel (I := I) (M := M)
          (C.localGeodesic t) wsol (s.1 - t.1)) := by
  have hsC : s.1 - t.1 ∈ Metric.ball (0 : ℝ) (C.radius t) := by
    apply Metric.mem_ball.mpr
    exact lt_of_lt_of_le (Metric.mem_ball.mp s.2) (min_le_left _ _)
  unfold canonicalFrameParallelOnGlobal
  exact C.reindexTangent_inner t s.1 hsC _ _

/-- A canonical local parallel field has constant squared norm when read on
the global curve over a certified cover member.  The statement keeps the
global-time representative explicit: no unproved identification of fields
from different cover members is used. -/
theorem exists_canonicalFrameParallelOnGlobal_inner_self_constant
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {a b : ℝ}
    (C : FiniteLocalGeodesicCover (I := I) (M := M) γ a b)
    (t : {q : ℝ // q ∈ C.centers}) {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun s ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov (curve γ t.1) (IntrinsicGeodesic.canonicalBasis (E := E))
        ((C.localGeodesic t).solution.coordinate s)
        ((C.localGeodesic t).solution.velocity s)) 0 w₀)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ r > (0 : ℝ), r ≤ min (C.radius t) wsol.radius ∧
      ∀ u ∈ Ioo (-r) r,
        ∀ q : {s : ℝ // s - t.1 ∈
          Metric.ball (0 : ℝ) (min (C.radius t) wsol.radius)},
          q.1 = t.1 + u →
            inner ℝ (C.canonicalFrameParallelOnGlobal t wsol q)
                (C.canonicalFrameParallelOnGlobal t wsol q) =
              inner ℝ
                (LocalGeodesic.canonicalFrameParallel (I := I) (M := M)
                  (C.localGeodesic t) wsol 0)
                (LocalGeodesic.canonicalFrameParallel (I := I) (M := M)
                  (C.localGeodesic t) wsol 0) := by
  obtain ⟨r₀, hr₀, hr₀bound, hconstant⟩ :=
    LocalGeodesic.canonicalFrameParallel_inner_self_constant_near_zero
      (I := I) (M := M) (C.localGeodesic t) wsol hmetric
  let r : ℝ := min r₀ (C.radius t)
  have hr : 0 < r := lt_min hr₀ (C.radius_pos t)
  have hr₀le : r ≤ r₀ := min_le_left _ _
  have hrCle : r ≤ C.radius t := min_le_right _ _
  have hrwsol : r ≤ wsol.radius :=
    le_trans hr₀le (le_trans hr₀bound (min_le_right _ _))
  have hrbound : r ≤ min (C.radius t) wsol.radius :=
    le_min hrCle hrwsol
  refine ⟨r, hr, hrbound, ?_⟩
  intro u hu q hq
  have hu₀ : u ∈ Ioo (-r₀) r₀ := by
    exact ⟨lt_of_le_of_lt (neg_le_neg hr₀le) hu.1,
      lt_of_lt_of_le hu.2 hr₀le⟩
  have hqtime : q.1 - t.1 = u := by
    rw [hq]
    ring
  calc
    inner ℝ (C.canonicalFrameParallelOnGlobal t wsol q)
        (C.canonicalFrameParallelOnGlobal t wsol q) =
      inner ℝ
        (LocalGeodesic.canonicalFrameParallel (I := I) (M := M)
          (C.localGeodesic t) wsol (q.1 - t.1))
        (LocalGeodesic.canonicalFrameParallel (I := I) (M := M)
          (C.localGeodesic t) wsol (q.1 - t.1)) :=
      C.canonicalFrameParallelOnGlobal_inner t wsol q
    _ = inner ℝ
        (LocalGeodesic.canonicalFrameParallel (I := I) (M := M)
          (C.localGeodesic t) wsol u)
        (LocalGeodesic.canonicalFrameParallel (I := I) (M := M)
          (C.localGeodesic t) wsol u) := by rw [hqtime]
    _ = inner ℝ
        (LocalGeodesic.canonicalFrameParallel (I := I) (M := M)
          (C.localGeodesic t) wsol 0)
        (LocalGeodesic.canonicalFrameParallel (I := I) (M := M)
          (C.localGeodesic t) wsol 0) := hconstant u hu₀

end FiniteLocalGeodesicCover
end GlobalGeodesic
end IntrinsicGeodesic

end BonnetMyersEntry
