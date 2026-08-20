/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.NormalForm
import LeanPool.ClassificationOfSurfaces.GeometricTriangulationRealization

/-!
# Lean Eval target theorem

This file contains the public theorem matching the Lean Eval problem statement.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- Every compact connected Hausdorff topological 2-manifold with boundary is homeomorphic to the
sphere, an orientable normal-form quotient, or a non-orientable normal-form quotient. -/
theorem classification_of_surfaces (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    Nonempty (S ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (S ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧ Nonempty (S ≃ₜ Quot (NonOrientableRel p n))) := by
  let P := compactEvalSurfaceFiniteCyclicPresentation S
  let validP := compact_eval_surface_finiteCyclicPresentation_isSurfaceValid S
  have connectedP : P.IsConnected :=
    compact_eval_surface_finiteCyclicPresentation_isConnected S
  rcases compact_eval_surface_polygonalRealization_homeomorphic_surface S with
    ⟨hPS⟩
  rcases P.hasEvalRepresentative validP connectedP with hP | ⟨p, n, hP⟩
  · obtain ⟨hPR⟩ := hP
    exact Or.inl ⟨hPS.symm.trans hPR⟩
  · rcases hP with hP | hP
    · obtain ⟨hpn, ⟨hPR⟩⟩ := hP
      exact Or.inr ⟨p, n, Or.inl ⟨hpn, ⟨hPS.symm.trans hPR⟩⟩⟩
    · obtain ⟨hp, ⟨hPR⟩⟩ := hP
      exact Or.inr ⟨p, n, Or.inr ⟨hp, ⟨hPS.symm.trans hPR⟩⟩⟩

/-- Blueprint-facing spelling of `classification_of_surfaces`. -/
theorem topological_classification_of_surfaces (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    Nonempty (S ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (S ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧ Nonempty (S ≃ₜ Quot (NonOrientableRel p n))) :=
  classification_of_surfaces S

end ClassificationOfSurfaces
end Topology
end LeanEval
