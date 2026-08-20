/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicCanonical
import LeanPool.ClassificationOfSurfaces.FiniteCyclicFaceMerge

/-!
# Canonical output of finite-cyclic normalization

This file fixes the output type of the Gallier--Xu recursion before that recursion is assembled.
A result lands only at the existing `NormalForm.canonicalPresentation`; it cannot introduce a
second project-owned spelling of the Eval representatives.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

/-- The validity-bundled canonical presentation selected by an admissible normal form. -/
noncomputable def canonicalValidPresentation
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    ValidPresentation :=
  ⟨N.canonicalPresentation, N.canonicalPresentation_isSurfaceValid hN⟩

@[simp]
theorem canonicalValidPresentation_presentation
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    (canonicalValidPresentation N hN).presentation =
      N.canonicalPresentation :=
  rfl

/-- Certified output of the finite-cyclic Gallier--Xu normalization.

The dependent admissibility field supplies ordinary validity for the canonical endpoint, and the
equivalence field records the entire validity-safe move chain. -/
structure NormalizationResult (P : ValidPresentation) where
  /-- The `normalForm` declaration. -/
  normalForm : NormalForm
  admissible : normalForm.IsEvalAdmissible
  equivalent :
    NormalizationEquivalent P
      (canonicalValidPresentation normalForm admissible)

namespace NormalizationResult

/-- A canonical presentation is already normalized. -/
noncomputable def canonical
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    NormalizationResult (canonicalValidPresentation N hN) where
  normalForm := N
  admissible := hN
  equivalent := NormalizationEquivalent.refl _

/-- Transport a normalization result backward through a normalization equivalence. -/
noncomputable def ofEquivalent
    {P Q : ValidPresentation}
    (hPQ : NormalizationEquivalent P Q)
    (result : NormalizationResult Q) :
    NormalizationResult P where
  normalForm := result.normalForm
  admissible := result.admissible
  equivalent := hPQ.trans result.equivalent

/-- Transport a normalization result across a signed presentation isomorphism. -/
noncomputable def ofSignedIso
    {P Q : ValidPresentation}
    (e : SignedPresentationIso P.presentation Q.presentation)
    (result : NormalizationResult Q) :
    NormalizationResult P :=
  result.ofEquivalent (NormalizationEquivalent.ofSignedIso e)

/-- A normalization result gives the faithful polygonal realization equivalence to its exact
canonical finite-cyclic endpoint. -/
theorem polygonallyEquivalent
    {P : ValidPresentation}
    (result : NormalizationResult P) :
    P.presentation.PolygonallyEquivalent
      result.normalForm.canonicalPresentation
      P.valid
      (result.normalForm.canonicalPresentation_isSurfaceValid
        result.admissible) :=
  result.equivalent.polygonallyEquivalent

/-- Homeomorphism from a normalized input's faithful polygonal realization to the exact canonical
finite-cyclic realization. -/
noncomputable def realizationHomeomorph
    {P : ValidPresentation}
    (result : NormalizationResult P) :
    P.presentation.PolygonalRealization P.valid ≃ₜ
      result.normalForm.canonicalPresentation.PolygonalRealization
        (result.normalForm.canonicalPresentation_isSurfaceValid
          result.admissible) :=
  Classical.choice result.polygonallyEquivalent

end NormalizationResult

namespace Cancellation

/-- The terminal inverse-pair cancellation with no remaining darts yields the agreed canonical
sphere presentation. -/
noncomputable def sphereNormalizationResult
    (validSource :
      (source ([] : List (SignedDart (Fin 0)))).IsSurfaceValid) :
    NormalizationResult
      ⟨source ([] : List (SignedDart (Fin 0))), validSource⟩ := by
  let hcanonical :=
    sphereNormalizationEquivalent validSource
  let canonicalSphere :=
    canonicalValidPresentation NormalForm.sphere trivial
  have hnode :
      (⟨twoMonogonSphere, twoMonogonSphere_isSurfaceValid⟩ :
        ValidPresentation) = canonicalSphere := by
    apply ValidPresentation.ext
    rfl
  rw [hnode] at hcanonical
  exact
    { normalForm := .sphere
      admissible := trivial
      equivalent := hcanonical }

end Cancellation

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
