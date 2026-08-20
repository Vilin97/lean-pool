/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicCanonicalRealization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicSphereRealization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicTerminalNormalization

/-!
# Faithful normal-form classification

This file composes the Gallier--Xu normalization of a valid connected finite-cyclic presentation
with the exact realization homeomorphisms for the three canonical endpoints.  Every type in this
chain is a faithful polygonal quotient.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- A valid connected finite-cyclic presentation has one of the exact Eval representatives.

The proof first normalizes to `NormalForm.canonicalPresentation`, preserving the polygonal
realization, and then uses the corresponding sphere, orientable, or nonorientable endpoint
homeomorphism. -/
theorem FiniteCyclicPresentation.hasEvalRepresentative
    (P : FiniteCyclicPresentation)
    (validP : P.IsSurfaceValid) (connectedP : P.IsConnected) :
    Nonempty (P.PolygonalRealization validP ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧
            Nonempty (P.PolygonalRealization validP ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧
            Nonempty (P.PolygonalRealization validP ≃ₜ Quot (NonOrientableRel p n))) := by
  obtain ⟨N, hN, hPN⟩ :=
    P.exists_admissible_normalForm_polygonallyEquivalent validP connectedP
  rcases hPN with ⟨hPN⟩
  cases N with
  | sphere =>
      exact Or.inl
        ⟨hPN.trans NormalForm.canonicalSphereRealizationHomeomorph⟩
  | orientable p n =>
      exact Or.inr
        ⟨p, n, Or.inl
          ⟨hN, ⟨hPN.trans
            (NormalForm.canonicalOrientableRealizationHomeomorph hN)⟩⟩⟩
  | nonOrientable p n =>
      exact Or.inr
        ⟨p, n, Or.inr
          ⟨hN, ⟨hPN.trans
            (NormalForm.canonicalNonOrientableRealizationHomeomorph hN)⟩⟩⟩

end ClassificationOfSurfaces
end Topology
end LeanEval
