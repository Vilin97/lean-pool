/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.FullTopologyMain

/-!
# The concrete Wallace counterexample

This file closes the construction.  All numerical parameters, subsequences, filters,
ultrafilters, finite character approximations, countable fusions, transfinite extensions, and
the final topology have been constructed in the imported modules.  The theorem below has no
mathematical hypothesis.
-/

namespace Wallace

open TriangularPreprocess

/-- A closed, witness-level form of the main construction.

There is a Hausdorff group topology on the canonical free Abelian group of rank continuum for
which the nonnegative cone, with its induced topology, is countably compact and is a Wallace
semigroup.  The explicit `CountablyCompactSpace` conjunct records the principal topological
conclusion separately, although it is also contained in `IsWallaceSemigroup`. -/
theorem continuumFreeGroup_positiveCone_isWallace :
    ∃ topology : TopologicalSpace ContinuumFreeGroup,
      @IsTopologicalAddGroup ContinuumFreeGroup topology _ ∧
      @T2Space ContinuumFreeGroup topology ∧
      @CountablyCompactSpace (positiveCone ContinuumIndex)
        (TopologicalSpace.induced
          (fun z : positiveCone ContinuumIndex ↦ (z : ContinuumFreeGroup)) topology) ∧
      @IsWallaceSemigroup (positiveCone ContinuumIndex)
        (TopologicalSpace.induced
          (fun z : positiveCone ContinuumIndex ↦ (z : ContinuumFreeGroup)) topology) _ := by
  let C : SeparationPackage ContinuumIndex := continuumFullSeparationPackage
  let topology : TopologicalSpace ContinuumFreeGroup := C.initialTopology
  letI : TopologicalSpace ContinuumFreeGroup := topology
  letI : IsTopologicalAddGroup ContinuumFreeGroup := C.initial_isTopologicalAddGroup
  letI : T2Space ContinuumFreeGroup := C.initial_t2Space
  letI : Infinite ContinuumIndex := continuumIndex_infinite
  let i : ContinuumIndex := Classical.choice inferInstance
  have hwallace : IsWallaceSemigroup (positiveCone ContinuumIndex) :=
    positiveCone_isWallace_of_limitProperty ContinuumIndex i
      C.positiveCone_hasWallaceLimitProperty
  refine ⟨topology, C.initial_isTopologicalAddGroup, C.initial_t2Space, ?_, hwallace⟩
  exact hwallace.2.2.2.1

/-- There exists a Hausdorff countably compact cancellative topological additive monoid which is
not a group.  The stronger public theorem in `TychonoffWallace.lean` also exposes commutativity
and Tychonoffness in its proposition. -/
theorem wallaceCounterexampleExists : WallaceCounterexampleExists :=
  by
    letI : Infinite ContinuumIndex := continuumIndex_infinite
    exact continuumFullSeparationPackage.wallaceCounterexampleExists

end Wallace
