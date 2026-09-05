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

end

end Wallace
