/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.ConcreteFusionRun
import LeanPool.Wallace.FullTopology

/-!
# The full free-Abelian group theorem

This module applies the unconditional fusion construction to the generic topological results in
`Wallace.FullTopology`.  The resulting theorem has no hypotheses.
-/

namespace Wallace

noncomputable section

open TriangularPreprocess
open Filter Topology

/-- The fully constructed character package on the canonical free Abelian group of rank
continuum. -/
def continuumFullSeparationPackage : SeparationPackage ContinuumIndex :=
  GlobalAssembly.separationPackage
    ConcreteFusionRun.blockSize ConcreteFusionRun.blockSize_pos
    ConcreteFusionRun.independenceBound
    ConcreteFusionRun.hasLocalSeparatingCharacters

/-- **Free-Abelian specialization of the main theorem.**  The free Abelian group of rank
continuum admits a Hausdorff
precompact countably compact group topology in which every convergent sequence is eventually
constant.  Precompactness is certified by a compatible totally bounded uniform group
structure. -/
theorem continuumFreeAbelianGroup_mainTheorem :
    FreeAbelianGroupConclusion ContinuumIndex :=
  continuumFullSeparationPackage.freeAbelianGroupConclusion

/-- The witness-level form of the free-Abelian specialization, kept as a convenient public API. -/
theorem continuumFreeAbelianGroup_mainTheorem_explicit :
    ∃ (topology : TopologicalSpace ContinuumFreeGroup)
      (uniformity : UniformSpace ContinuumFreeGroup),
      uniformity.toTopologicalSpace = topology ∧
      @IsUniformAddGroup ContinuumFreeGroup uniformity _ ∧
      @IsTopologicalAddGroup ContinuumFreeGroup topology _ ∧
      @T2Space ContinuumFreeGroup topology ∧
      @CountablyCompactSpace ContinuumFreeGroup topology ∧
      @TotallyBounded ContinuumFreeGroup uniformity Set.univ ∧
      (∀ (s : ℕ → ContinuumFreeGroup) (x : ContinuumFreeGroup),
        Tendsto s Filter.atTop (@nhds ContinuumFreeGroup topology x) →
          ∀ᶠ n in Filter.atTop, s n = x) :=
  continuumFreeAbelianGroup_mainTheorem

end

end Wallace
