/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCanonicalClassifier
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConstructions
import LeanPool.BrillNoetherGraphs.LowGenus.Infrastructure.CoreRelabelingClosed

/-!
# Closed construction coverage of the cubic genus-five atlas

The canonical classifier returns occurrence-sensitive core relabelings.  The
first sixteen rows are exactly the Atanasov--Ranganathan construction atlas;
the remaining four rows are the bridge types and are deliberately left as a
separate structural branch.
-/
namespace AtanasovRanganathan.GenusFiveCubicCoverage

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ExplicitPotential
open AtanasovRanganathan.Configurations
open AtanasovRanganathan.GenusFiveConstructions
open AtanasovRanganathan.GenusFiveCubicAtlas

/-- The finite structural obligation left after the sixteen AR rows: every
closed face of each of the four cubic bridge cores carries a degree-four
rank-one pencil. -/
def BridgeAtlasClosedCoverage : Prop :=
  ∀ row ∈ bridgeAtlas,
    ClosedSubdivisionDharConstruction row.core (by norm_num)

/-- Read the aggregate of sixteen public AR constructions against the public
cubic-atlas row type. -/
theorem closedConstruction_of_mem_arAtlas
    (constructions : CubicAtlasConstructions)
    (row : Row) (hRow : row ∈ arAtlas) :
    ClosedSubdivisionDharConstruction row.core (by norm_num) := by
  simp [arAtlas] at hRow
  rcases hRow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact constructions.row01
  · exact constructions.row02
  · exact constructions.row03
  · exact constructions.row04
  · exact constructions.row05
  · exact constructions.row06
  · exact constructions.row07
  · exact constructions.row08
  · exact constructions.row09
  · exact constructions.row10
  · exact constructions.row11
  · exact constructions.row12
  · exact constructions.row13
  · exact constructions.row14
  · exact constructions.row15
  · exact constructions.row16

/-- A classified cubic core either inherits one of the sixteen closed AR
constructions or is one of the four explicit bridge rows. -/
theorem classified_closed_or_bridge
    (constructions : CubicAtlasConstructions)
    (candidate : ExplicitPotential.Core 8 12)
    (hConnected : candidate.Connected)
    (hLoopless : ∀ edge : Fin 12, candidate.tail edge ≠ candidate.head edge)
    (hCubic : candidate.Cubic) :
    ClosedSubdivisionDharConstruction candidate (by norm_num) ∨
      ∃ row ∈ bridgeAtlas, Nonempty (candidate.Relabeling row.core) := by
  obtain ⟨row, hRow, ⟨relabeling⟩⟩ :=
    GenusFiveCanonicalClassifier.genusFiveCubicRelabelingComplete
      candidate hConnected hLoopless hCubic
  rw [atlas, List.mem_append] at hRow
  rcases hRow with hAR | hBridge
  · exact Or.inl
      (ExplicitPotential.Core.Relabeling.closedConstruction_of_target
        relabeling (by norm_num)
        (closedConstruction_of_mem_arAtlas constructions row hAR))
  · exact Or.inr ⟨row, hBridge, ⟨relabeling⟩⟩

/-- Size-indexed wrapper used by trivalent expansion.  The expansion computes
its cubic size arithmetically, so keeping the equalities explicit avoids any
ad-hoc cast of ordered core occurrences. -/
theorem classified_closed_or_bridge_of_sizes
    {n p : ℕ} (candidate : ExplicitPotential.Core n p)
    (hVertices : n = 8) (hSlots : p = 12)
    (constructions : CubicAtlasConstructions)
    (hConnected : candidate.Connected)
    (hLoopless : ∀ edge : Fin p, candidate.tail edge ≠ candidate.head edge)
    (hCubic : candidate.Cubic) :
    ClosedSubdivisionDharConstruction candidate (by omega) ∨
      ∃ row ∈ bridgeAtlas, Nonempty (candidate.Relabeling row.core) := by
  subst n
  subst p
  exact classified_closed_or_bridge constructions candidate
    hConnected hLoopless hCubic

/-- Once the four bridge rows are closed structurally, the public classifier
returns a closed construction for every connected loopless cubic `8/12`
core. -/
theorem classified_closed_of_bridgeCoverage
    (constructions : CubicAtlasConstructions)
    (bridges : BridgeAtlasClosedCoverage)
    (candidate : ExplicitPotential.Core 8 12)
    (hConnected : candidate.Connected)
    (hLoopless : ∀ edge : Fin 12, candidate.tail edge ≠ candidate.head edge)
    (hCubic : candidate.Cubic) :
    ClosedSubdivisionDharConstruction candidate (by norm_num) := by
  rcases classified_closed_or_bridge constructions candidate hConnected
      hLoopless hCubic with hClosed | ⟨row, hRow, ⟨relabeling⟩⟩
  · exact hClosed
  · exact ExplicitPotential.Core.Relabeling.closedConstruction_of_target
      relabeling (by norm_num) (bridges row hRow)

/-- Size-indexed form of `classified_closed_of_bridgeCoverage`, for the
arithmetically sized output of trivalent expansion. -/
theorem classified_closed_of_sizes
    {n p : ℕ} (candidate : ExplicitPotential.Core n p)
    (hVertices : n = 8) (hSlots : p = 12)
    (constructions : CubicAtlasConstructions)
    (bridges : BridgeAtlasClosedCoverage)
    (hConnected : candidate.Connected)
    (hLoopless : ∀ edge : Fin p, candidate.tail edge ≠ candidate.head edge)
    (hCubic : candidate.Cubic) :
    ClosedSubdivisionDharConstruction candidate (by omega) := by
  subst n
  subst p
  exact classified_closed_of_bridgeCoverage constructions bridges candidate
    hConnected hLoopless hCubic

end AtanasovRanganathan.GenusFiveCubicCoverage
