/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourCanonicalClassifier
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourPseudocoreCoverage
public import LeanPool.BrillNoetherGraphs.LowGenus.Infrastructure.CoreRelabelingClosed

/-!
# Closed coverage of the six cubic genus-four rows

The canonical classifier returns an occurrence-sensitive relabeling to one of
the six fixed cubic rows.  Closed-face relabeling therefore turns six named
row proofs into the classifier-facing coverage theorem consumed by the public
pseudocore reduction.
-/

@[expose] public section
namespace AtanasovRanganathan.GenusFourCubicCoverage

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ExplicitPotential
open Utilities.Certificate.ContractionForestCensusGeneral
open AtanasovRanganathan.Configurations
open AtanasovRanganathan.GenusFourCubicAtlas
open AtanasovRanganathan.GenusFourPseudocoreCoverage

/-- The six concrete closed-row obligations. -/
def RowClosedCoverage : Prop :=
  ∀ row ∈ atlas,
    ∀ (length : Fin 9 → ℕ)
      (hForest : IsForest row.core (zeroSlots length))
      (hNotLoopy : ¬ IsLoopy row.core (zeroSlots length)),
      BNExists (faceSpec row.core (by norm_num) length hForest hNotLoopy).graph 1 3

/-- Six closed row proofs and the public canonical classifier cover every
connected loopless cubic `6/9` core. -/
theorem cubicClosedCoverage_of_rows
    (rows : RowClosedCoverage) : CubicClosedCoverage := by
  intro candidate hConnected hLoopless hCubic
  obtain ⟨row, hRow, ⟨relabeling⟩⟩ :=
    GenusFourCanonicalClassifier.genusFourCubicRelabelingComplete
      candidate hConnected hLoopless hCubic
  exact ExplicitPotential.Core.Relabeling.closedPencil_of_target
    relabeling (by norm_num) (rows row hRow)

end AtanasovRanganathan.GenusFourCubicCoverage
