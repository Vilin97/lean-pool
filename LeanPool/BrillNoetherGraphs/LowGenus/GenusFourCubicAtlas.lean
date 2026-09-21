/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ConnectedCheckFast
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CubicCore
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
import Mathlib.Tactic

/-!
# The six loopless cubic genus-four core types

This module is the public, self-contained atlas of connected loopless cubic
cores on six vertices.  It contains only the six displayed cores and their
kernel-checked validity.  Exhaustiveness is proved separately by
`LowGenus.GenusFourCanonicalClassifier`.
-/
namespace AtanasovRanganathan.GenusFourCubicAtlas

open Utilities.Certificate
open Utilities.Certificate.ExplicitPotential

/-- One concrete loopless `6`-vertex, `9`-slot cubic core. -/
structure Row where
  core : Core 6 9
  loopless : ∀ edge : Fin 9, core.tail edge ≠ core.head edge
  connected : core.Connected
  cubic : core.Cubic

private theorem connected (core : Core 6 9) :
    core.connectedCheckFast = true → core.Connected :=
  fun h => ExplicitPotential.Core.connected_of_connectedCheckFast h

/-! The names retain the row numbers of the complete genus-four pseudocore
catalog from which these six terminal loopless cubic rows were extracted. -/

def row095Core : Core 6 9 where
  tail := ![0, 0, 0, 1, 1, 1, 2, 2, 2]
  head := ![4, 5, 5, 3, 4, 5, 3, 3, 4]

def row096Core : Core 6 9 where
  tail := ![0, 0, 0, 1, 1, 1, 2, 2, 2]
  head := ![4, 5, 5, 3, 4, 4, 3, 3, 5]

def row097Core : Core 6 9 where
  tail := ![0, 0, 0, 1, 1, 1, 2, 2, 3]
  head := ![4, 5, 5, 2, 3, 5, 3, 4, 4]

def row098Core : Core 6 9 where
  tail := ![0, 0, 0, 1, 1, 1, 2, 2, 4]
  head := ![4, 5, 5, 2, 3, 4, 3, 3, 5]

def row099Core : Core 6 9 where
  tail := ![0, 0, 0, 1, 1, 1, 2, 2, 2]
  head := ![3, 4, 5, 3, 4, 5, 3, 4, 5]

def row100Core : Core 6 9 where
  tail := ![0, 0, 0, 1, 1, 1, 2, 2, 3]
  head := ![3, 4, 5, 2, 4, 5, 3, 5, 4]

private theorem row095_loopless :
    ∀ edge : Fin 9, row095Core.tail edge ≠ row095Core.head edge := by
  intro edge; fin_cases edge <;> decide

private theorem row096_loopless :
    ∀ edge : Fin 9, row096Core.tail edge ≠ row096Core.head edge := by
  intro edge; fin_cases edge <;> decide

private theorem row097_loopless :
    ∀ edge : Fin 9, row097Core.tail edge ≠ row097Core.head edge := by
  intro edge; fin_cases edge <;> decide

private theorem row098_loopless :
    ∀ edge : Fin 9, row098Core.tail edge ≠ row098Core.head edge := by
  intro edge; fin_cases edge <;> decide

private theorem row099_loopless :
    ∀ edge : Fin 9, row099Core.tail edge ≠ row099Core.head edge := by
  intro edge; fin_cases edge <;> decide

private theorem row100_loopless :
    ∀ edge : Fin 9, row100Core.tail edge ≠ row100Core.head edge := by
  intro edge; fin_cases edge <;> decide

private theorem row095_cubic : row095Core.Cubic := by
  intro vertex; fin_cases vertex <;> decide

private theorem row096_cubic : row096Core.Cubic := by
  intro vertex; fin_cases vertex <;> decide

private theorem row097_cubic : row097Core.Cubic := by
  intro vertex; fin_cases vertex <;> decide

private theorem row098_cubic : row098Core.Cubic := by
  intro vertex; fin_cases vertex <;> decide

private theorem row099_cubic : row099Core.Cubic := by
  intro vertex; fin_cases vertex <;> decide

private theorem row100_cubic : row100Core.Cubic := by
  intro vertex; fin_cases vertex <;> decide

def row095 : Row := ⟨row095Core, row095_loopless,
  connected row095Core (by decide +kernel), row095_cubic⟩
def row096 : Row := ⟨row096Core, row096_loopless,
  connected row096Core (by decide +kernel), row096_cubic⟩
def row097 : Row := ⟨row097Core, row097_loopless,
  connected row097Core (by decide +kernel), row097_cubic⟩
def row098 : Row := ⟨row098Core, row098_loopless,
  connected row098Core (by decide +kernel), row098_cubic⟩
def row099 : Row := ⟨row099Core, row099_loopless,
  connected row099Core (by decide +kernel), row099_cubic⟩
def row100 : Row := ⟨row100Core, row100_loopless,
  connected row100Core (by decide +kernel), row100_cubic⟩

/-- The exact atlas order used by the emitted canonical-classifier payload. -/
def atlas : List Row := [row095, row096, row097, row098, row099, row100]

@[simp] theorem atlas_length : atlas.length = 6 := by
  rfl

end AtanasovRanganathan.GenusFourCubicAtlas
