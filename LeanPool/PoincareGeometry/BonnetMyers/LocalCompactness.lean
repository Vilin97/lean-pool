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

import LeanPool.PoincareGeometry.BonnetMyers.MetricBridge
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# The local compactness base for the Hopf--Rinow bridge

Finite-dimensional manifold topology is locally compact independently of the
Riemannian metric.  After the connected finite-distance construction, this
gives compact intrinsic closed balls of sufficiently small radius.  It is only
the local statement: no properness or global compactness is asserted here.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

theorem exists_compact_finiteRiemannian_closedBall
    [T3Space M] (g : ContMDiffRiemannianMetric I ∞ E TM) (x : M) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro y a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    ∃ r : ℝ, 0 < r ∧ IsCompact (Metric.closedBall x r) := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞))
    (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  letI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro y a b; rfl⟩⟩
  let t₀ : TopologicalSpace M := inferInstance
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  let t₁ : TopologicalSpace M :=
    (inferInstance : MetricSpace M).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have htop : t₀ = t₁ := by
    rfl
  let hweak₀ : @WeaklyLocallyCompactSpace M t₀ := by
    letI : TopologicalSpace M := t₀
    letI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
    infer_instance
  have hball₁ : ∃ r : ℝ, 0 < r ∧
      @IsCompact M t₁ (Metric.closedBall x r) := by
    letI : TopologicalSpace M := t₁
    have htypes : @WeaklyLocallyCompactSpace M t₀ = @WeaklyLocallyCompactSpace M t₁ :=
      congrArg (fun t : TopologicalSpace M => @WeaklyLocallyCompactSpace M t) htop
    letI : @WeaklyLocallyCompactSpace M t₁ := htypes.mp hweak₀
    exact Metric.exists_isCompact_closedBall x
  rcases hball₁ with ⟨r, hr, hcompact⟩
  refine ⟨r, hr, ?_⟩
  have htypes : @IsCompact M t₀ (Metric.closedBall x r) =
      @IsCompact M t₁ (Metric.closedBall x r) :=
    congrArg (fun t : TopologicalSpace M => @IsCompact M t (Metric.closedBall x r)) htop
  exact htypes.mpr hcompact

end BonnetMyersEntry
