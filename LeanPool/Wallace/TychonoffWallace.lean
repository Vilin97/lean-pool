/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.Main
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# The commutative Tychonoff Wallace semigroup

The original Wallace interface records Hausdorffness, countable compactness, cancellation and a
noninvertible element.  The paper's printed corollary also says that the witness is commutative
and Tychonoff.  This module makes both properties part of the public proposition.
-/

namespace Wallace

noncomputable section

open TriangularPreprocess

namespace FullCharacterPackage

variable {G : Type*} [AddCommGroup G]

/-- The initial topology is Tychonoff (`T₃.₅` in mathlib), since evaluation embeds the group into
a product of circles. -/
theorem initial_t35Space (C : FullCharacterPackage G) :
    @T35Space G C.initialTopology := by
  letI : TopologicalSpace G := C.initialTopology
  exact C.evaluation_injective.isEmbedding_induced.t35Space

end FullCharacterPackage

namespace SeparationPackage

variable {I : Type*}

theorem initial_t35Space (C : SeparationPackage I) :
    @T35Space (I →₀ ℤ) C.initialTopology :=
  C.toFullCharacterPackage.initial_t35Space

end SeparationPackage

/-- The exact existential content of the paper's Wallace corollary.  The algebraic structure is
explicitly commutative and the separation property is explicitly Tychonoff. -/
def CommutativeTychonoffWallaceCounterexampleExists : Prop :=
  ∃ (S : Type) (topology : TopologicalSpace S) (monoid : AddCommMonoid S),
    @T35Space S topology ∧
      @IsWallaceSemigroup S topology monoid.toAddMonoid

/-- The concrete nonnegative cone, with all properties in the printed corollary visible. -/
theorem continuumPositiveCone_isCommutativeTychonoffWallace :
    ∃ topology : TopologicalSpace (positiveCone ContinuumIndex),
      @T35Space (positiveCone ContinuumIndex) topology ∧
        @IsWallaceSemigroup (positiveCone ContinuumIndex) topology _ := by
  let C : SeparationPackage ContinuumIndex := continuumFullSeparationPackage
  let ambientTopology : TopologicalSpace ContinuumFreeGroup := C.initialTopology
  letI : TopologicalSpace ContinuumFreeGroup := ambientTopology
  letI : IsTopologicalAddGroup ContinuumFreeGroup := C.initial_isTopologicalAddGroup
  letI : T2Space ContinuumFreeGroup := C.initial_t2Space
  letI : T35Space ContinuumFreeGroup := C.initial_t35Space
  letI : Infinite ContinuumIndex := continuumIndex_infinite
  let coneTopology : TopologicalSpace (positiveCone ContinuumIndex) :=
    TopologicalSpace.induced
      (fun z : positiveCone ContinuumIndex ↦ (z : ContinuumFreeGroup)) ambientTopology
  letI : TopologicalSpace (positiveCone ContinuumIndex) := coneTopology
  let i : ContinuumIndex := Classical.choice inferInstance
  have hwallace : IsWallaceSemigroup (positiveCone ContinuumIndex) :=
    positiveCone_isWallace_of_limitProperty ContinuumIndex i
      C.positiveCone_hasWallaceLimitProperty
  exact ⟨coneTopology, inferInstance, hwallace⟩

/-- **Formal counterpart of the paper's Wallace corollary.**  There exists a commutative
Tychonoff countably compact topological semigroup with two-sided cancellation which is not a
group.  `Wallace.Audit` records the standard classical Lean foundations used by the proof. -/
theorem commutativeTychonoffWallaceCounterexampleExists :
    CommutativeTychonoffWallaceCounterexampleExists := by
  obtain ⟨topology, hT35, hwallace⟩ :=
    continuumPositiveCone_isCommutativeTychonoffWallace
  exact ⟨positiveCone ContinuumIndex, topology, inferInstance, hT35, hwallace⟩

end

end Wallace
