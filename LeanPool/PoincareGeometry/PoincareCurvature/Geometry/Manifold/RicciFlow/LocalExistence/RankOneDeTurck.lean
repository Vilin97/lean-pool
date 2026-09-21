/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurck
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.RankOne
/-!
# Rank-one and model-space subsingleton chosen-background Ricci-DeTurck local existence/uniqueness

This thin extension module keeps the rank-one and model-space subsingleton chosen-background
Ricci-DeTurck consequences out of the core DeTurck file. The mathematical input is
`intrinsicLocalExistenceUniqueness_of_finrank_le_one` from `LocalExistence.lean` together with
the existing conversion `IntrinsicLocalExistenceUniqueness.toChosenIntrinsicDeTurck`. This
mirrors the patterns already in `DeTurck.lean` for the subsingleton-tangent and empty-manifold
cases (`chosenIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent` and
`_of_isEmpty`).

The arbitrary-background `IntrinsicDeTurckLocalExistenceUniqueness` package is **not** provided
in the rank-one case, because in finrank one the background connection on `TM` is not forced to
equal the chosen Levi-Civita connection of the evolving metric. The subsingleton-tangent case is
genuinely special — its arbitrary-background package follows from connection-uniqueness on
zero-dimensional fibers — and that lemma does not generalize to rank-one.

The model-space subsingleton variants (`[Subsingleton E]`) propagate via the registered instance
`instSubsingletonTangentSpaceOfSubsingletonModel` from `LocalExistence.lean`, so they are
straightforward synonyms of the existing `_of_subsingleton_tangent` constructors.
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

section Compact

variable [CompactSpace M]

/-- Chosen-background Ricci-DeTurck local existence/uniqueness on compact manifolds whose tangent
fibers all have real dimension at most one. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_finrank_le_one (I := I) (M := M) hfin ivp)
    |>.toChosenIntrinsicDeTurck

/-- The theorem-family version of
`chosenIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one`. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    chosenIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one
      (I := I) (M := M) hfin ivp

/-- Model-space version: when `Module.finrank ℝ E ≤ 1`, every tangent fiber has dimension at most
one, so chosen-background Ricci-DeTurck local existence/uniqueness holds. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  chosenIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one
    (I := I) (M := M) (fun x ↦ tangent_finrank_le_one_of_model (I := I) (M := M) x) ivp

/-- The theorem-family version of
`chosenIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_model_le_one`. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)] :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    chosenIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_model_le_one
      (I := I) (M := M) ivp

/-- Model-space subsingleton: when the model vector space `E` is a subsingleton, every tangent
fiber is automatically subsingleton, so chosen-background Ricci-DeTurck local existence/
uniqueness holds. Synonym of the existing `_of_subsingleton_tangent` constructor obtained
via the registered instance `instSubsingletonTangentSpaceOfSubsingletonModel`. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_model
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  chosenIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent
    (I := I) (M := M) ivp

/-- The theorem-family version of
`chosenIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_model`. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_subsingleton_model
    [Subsingleton E] :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    chosenIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_model
      (I := I) (M := M) ivp

end Compact

end RicciFlow
