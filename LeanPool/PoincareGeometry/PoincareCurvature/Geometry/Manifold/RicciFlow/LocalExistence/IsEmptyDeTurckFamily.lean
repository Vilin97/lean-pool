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

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurck
/-!
# `IsEmpty M` family conversions for chosen-DeTurck and arbitrary-DeTurck packages

This thin extension module fills a small gap in `DeTurck.lean`. The
`_of_subsingleton_tangent` theorem-family conversions
(`Family.toIntrinsicDeTurck_of_subsingleton_tangent` etc.) cover the case where
every tangent fiber is a subsingleton, but they require that hypothesis as a
typeclass instance. For empty manifolds (`[IsEmpty M]`) the corresponding
hypothesis holds vacuously but is not registered as an instance, so the
existing conversions are not directly applicable.

This module supplies the explicit `_of_isEmpty` analogs by introducing the
needed `letI` locally and dispatching to the subsingleton-tangent version.
The mathematical content is unchanged; this is purely an API completion.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

section IsEmpty

variable [IsEmpty M]

/-- On an empty manifold, an intrinsic Ricci-flow local existence/uniqueness package converts
to an arbitrary-background Ricci-DeTurck package vacuously. -/
noncomputable def IntrinsicLocalExistenceUniqueness.toIntrinsicDeTurck_of_isEmpty
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  letI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  pkg.toIntrinsicDeTurck_of_subsingleton_tangent

/-- On an empty manifold, an arbitrary-background Ricci-DeTurck package converts back to the
intrinsic Ricci-flow package vacuously. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_of_isEmpty
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  letI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  pkg.toIntrinsic_of_subsingleton_tangent

/-- On an empty manifold, a chosen-background Ricci-DeTurck package can be widened to the
arbitrary-background Ricci-DeTurck package vacuously. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsicDeTurck_of_isEmpty
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  letI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  pkg.toIntrinsicDeTurck_of_subsingleton_tangent

/-- On an empty manifold, an arbitrary-background Ricci-DeTurck package restricts back to the
chosen-background package vacuously. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniqueness.toChosenIntrinsicDeTurck_of_isEmpty
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  letI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  pkg.toChosenIntrinsicDeTurck_of_subsingleton_tangent

/-- Family-level: `IntrinsicLocalExistenceUniquenessFamily.toIntrinsicDeTurck_of_isEmpty`. -/
noncomputable def IntrinsicLocalExistenceUniquenessFamily.toIntrinsicDeTurck_of_isEmpty
    (pkg : IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toIntrinsicDeTurck_of_isEmpty

/-- Family-level:
`ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicDeTurck_of_isEmpty`. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicDeTurck_of_isEmpty
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toIntrinsicDeTurck_of_isEmpty

/-- Family-level:
`IntrinsicDeTurckLocalExistenceUniquenessFamily.toChosenIntrinsicDeTurck_of_isEmpty`. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniquenessFamily.toChosenIntrinsicDeTurck_of_isEmpty
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toChosenIntrinsicDeTurck_of_isEmpty

/-- Family-level: `IntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsic_of_isEmpty`. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsic_of_isEmpty
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  fun ivp ↦ (pkg.package ivp).toIntrinsic_of_isEmpty

/-- Family-level: `IntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinary_of_isEmpty`. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinary_of_isEmpty
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  fun ivp ↦ (pkg.toIntrinsic_of_isEmpty ivp).toOrdinary

/-- Family-level: bundled
`IntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_of_isEmpty`. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_of_isEmpty
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := pkg.toIntrinsic_of_isEmpty

/-- Family-level: bundled
`IntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_of_isEmpty`. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_of_isEmpty
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  pkg.toIntrinsicFamily_of_isEmpty.toOrdinary

end IsEmpty

end RicciFlow
