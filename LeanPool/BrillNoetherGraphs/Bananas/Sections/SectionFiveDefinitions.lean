/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionBasics
import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphIso

/-!
# Shared definitions for Section 5

The structures and finite rank-drop sum used by the formal statements of the
marked-point symmetry section.
-/

namespace Bananas

open Utilities

/-- A graph automorphism which preserves the *set* of two marked vertices.
The definition permits either fixing the marks or interchanging them. -/
structure MarkedPointAutomorphism (M : TwiceMarked) where
  iso : CFGraphIso M.graph M.graph
  preserves_marked_set (x : M.graph.V) :
    (x = M.u ∨ x = M.v) ↔
      (iso.vertexEquiv x = M.u ∨ iso.vertexEquiv x = M.v)

/-- A marked-point automorphism which interchanges the ordered marks. -/
structure MarkedPointSwap (M : TwiceMarked) extends MarkedPointAutomorphism M where
  map_u : toMarkedPointAutomorphism.iso.vertexEquiv M.u = M.v
  map_v : toMarkedPointAutomorphism.iso.vertexEquiv M.v = M.u

/-- The finite rank-drop sum in the final, unlabelled proposition of Section
5.  This is the paper's sum over a fundamental domain `[k]`, encoded by
`Fin k`. -/
noncomputable def sectionFiveRankDropSum
    (M : TwiceMarked) (D : CFDiv M.graph) (k : ℕ) : ℤ :=
  ∑ m : Fin k,
    (rank M.graph
        (D + ((((m : ℕ) : ℤ) - 1) • oneChip M.u) -
          ((m : ℕ) : ℤ) • oneChip M.v) -
      rank M.graph
        (D + ((((m : ℕ) : ℤ) - 2) • oneChip M.u) -
          ((m : ℕ) : ℤ) • oneChip M.v))

end Bananas
