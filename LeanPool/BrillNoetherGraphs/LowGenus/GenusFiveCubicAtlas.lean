/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CubicCore
public import Mathlib.Tactic

/-!
# The twenty loopless cubic genus-five core types

The first sixteen entries are the Atanasov--Ranganathan rows already owned by
`LowGenus`.  The final four are the elementary bridge-core types.  This module
is passive finite data plus kernel-checked validity; exhaustiveness is proved
separately by the public canonical classifier.
-/

@[expose] public section
namespace AtanasovRanganathan.GenusFiveCubicAtlas

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ExplicitPotential
open AtanasovRanganathan.GenusFiveCoreAtlas

/-- One concrete loopless `8`-vertex, `12`-slot cubic core. -/
structure Row where
  /-- The eight-vertex, twelve-slot core underlying this connected loopless cubic atlas row. -/
  core : ExplicitPotential.Core 8 12
  loopless : ∀ edge : Fin 12, core.tail edge ≠ core.head edge
  connected : core.Connected
  cubic : core.Cubic

/-- Connectivity for a core that is *not* an atlas row — the four bridge cores
below.  The sixteen AR rows all cite `GenusFiveCoreAtlas`'s own
`rowNN_connected` instead; six of them used to re-prove it here, which is where
six of the nine duplicated kernel connectivity reductions lived. -/
private theorem connected (core : ExplicitPotential.Core 8 12) :
    core.connectedCheckFast = true → core.Connected :=
  fun h => ExplicitPotential.Core.connected_of_connectedCheckFast h

/-! ## The sixteen AR rows -/

/-- Atlas row 01, bundling `row01Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row01 : Row := ⟨row01Core, row01_loopless, row01_connected, row01_trivalent⟩
/-- Atlas row 02, bundling `row02Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row02 : Row := ⟨row02Core, row02_loopless, row02_connected, row02_trivalent⟩
/-- Atlas row 03, bundling `row03Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row03 : Row := ⟨row03Core, row03_loopless, row03_connected, row03_trivalent⟩
/-- Atlas row 04, bundling `row04Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row04 : Row := ⟨row04Core, row04_loopless, row04_connected, row04_trivalent⟩
/-- Atlas row 05, bundling `row05Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row05 : Row := ⟨row05Core, row05_loopless, row05_connected, row05_trivalent⟩
/-- Atlas row 06, bundling `row06Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row06 : Row := ⟨row06Core, row06_loopless, row06_connected, row06_trivalent⟩
/-- Atlas row 07, bundling `row07Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row07 : Row := ⟨row07Core, row07_loopless, row07_connected, row07_trivalent⟩
/-- Atlas row 08, bundling `row08Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row08 : Row := ⟨row08Core, row08_loopless, row08_connected, row08_trivalent⟩
/-- Atlas row 09, bundling `row09Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row09 : Row := ⟨row09Core, row09_loopless, row09_connected, row09_trivalent⟩
/-- Atlas row 10, bundling `row10Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row10 : Row := ⟨row10Core, row10_loopless, row10_connected, row10_trivalent⟩
/-- Atlas row 11, bundling `row11Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row11 : Row := ⟨row11Core, row11_loopless, row11_connected, row11_trivalent⟩
/-- Atlas row 12, bundling `row12Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row12 : Row := ⟨row12Core, row12_loopless, row12_connected, row12_trivalent⟩
/-- Atlas row 13, bundling `row13Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row13 : Row := ⟨row13Core, row13_loopless, row13_connected, row13_trivalent⟩
/-- Atlas row 14, bundling `row14Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row14 : Row := ⟨row14Core, row14_loopless, row14_connected, row14_trivalent⟩
/-- Atlas row 15, bundling `row15Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row15 : Row := ⟨row15Core, row15_loopless, row15_connected, row15_trivalent⟩
/-- Atlas row 16, bundling `row16Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row16 : Row := ⟨row16Core, row16_loopless, row16_connected, row16_trivalent⟩

/-- The sixteen Atanasov–Ranganathan cubic rows, in their numbered order. -/
def arAtlas : List Row :=
  [row01, row02, row03, row04, row05, row06, row07, row08,
    row09, row10, row11, row12, row13, row14, row15, row16]

/-! ## The four bridge rows -/

/-- The eight-vertex root-double bridge core, given by its twelve ordered endpoint pairs. -/
def rootDoubleCore : ExplicitPotential.Core 8 12 where
  tail := ![0, 0, 1, 1, 0, 3, 3, 4, 5, 5, 6, 6]
  head := ![1, 2, 2, 2, 3, 4, 4, 5, 6, 7, 7, 7]

/-- The eight-vertex one-chord bridge core, given by its twelve ordered endpoint pairs. -/
def oneChordCore : ExplicitPotential.Core 8 12 where
  tail := ![0, 0, 1, 1, 0, 3, 3, 4, 4, 5, 6, 6]
  head := ![1, 2, 2, 2, 3, 4, 5, 5, 6, 7, 7, 7]

/-- The eight-vertex square bridge core, given by its twelve ordered endpoint pairs. -/
def squareCore : ExplicitPotential.Core 8 12 where
  tail := ![0, 0, 1, 1, 0, 3, 3, 4, 4, 5, 5, 6]
  head := ![1, 2, 2, 2, 3, 4, 5, 6, 7, 6, 7, 7]

/-- The eight-vertex double-matching bridge core, given by its twelve ordered endpoint pairs. -/
def doubleMatchingCore : ExplicitPotential.Core 8 12 where
  tail := ![0, 0, 1, 1, 0, 3, 3, 4, 4, 5, 5, 6]
  head := ![1, 2, 2, 2, 3, 4, 5, 6, 6, 7, 7, 7]

private theorem rootDouble_loopless :
    ∀ edge : Fin 12, rootDoubleCore.tail edge ≠ rootDoubleCore.head edge := by
  intro edge; fin_cases edge <;> decide

private theorem oneChord_loopless :
    ∀ edge : Fin 12, oneChordCore.tail edge ≠ oneChordCore.head edge := by
  intro edge; fin_cases edge <;> decide

private theorem square_loopless :
    ∀ edge : Fin 12, squareCore.tail edge ≠ squareCore.head edge := by
  intro edge; fin_cases edge <;> decide

private theorem doubleMatching_loopless :
    ∀ edge : Fin 12, doubleMatchingCore.tail edge ≠ doubleMatchingCore.head edge := by
  intro edge; fin_cases edge <;> decide

private theorem rootDouble_cubic : rootDoubleCore.Cubic := by
  intro vertex; fin_cases vertex <;> decide

private theorem oneChord_cubic : oneChordCore.Cubic := by
  intro vertex; fin_cases vertex <;> decide

private theorem square_cubic : squareCore.Cubic := by
  intro vertex; fin_cases vertex <;> decide

private theorem doubleMatching_cubic : doubleMatchingCore.Cubic := by
  intro vertex; fin_cases vertex <;> decide

/-- The root-double bridge core bundled with its looplessness, connectivity, and cubic-degree
proofs. -/
def rootDouble : Row := ⟨rootDoubleCore, by exact rootDouble_loopless,
  by exact connected rootDoubleCore (by decide +kernel), by exact rootDouble_cubic⟩
/-- The one-chord bridge core bundled with its looplessness, connectivity, and cubic-degree
proofs. -/
def oneChord : Row := ⟨oneChordCore, by exact oneChord_loopless,
  by exact connected oneChordCore (by decide +kernel), by exact oneChord_cubic⟩
/-- The square bridge core bundled with its looplessness, connectivity, and cubic-degree proofs. -/
def square : Row := ⟨squareCore, by exact square_loopless,
  by exact connected squareCore (by decide +kernel), by exact square_cubic⟩
/-- The double-matching bridge core bundled with its looplessness, connectivity, and
cubic-degree proofs. -/
def doubleMatching : Row := ⟨doubleMatchingCore, by exact doubleMatching_loopless,
  by exact connected doubleMatchingCore (by decide +kernel), by exact doubleMatching_cubic⟩

/-- The four bridge cores, ordered as root-double, one-chord, square, and double-matching. -/
def bridgeAtlas : List Row := [rootDouble, oneChord, square, doubleMatching]

/-- The exact atlas order used by the emitted classifier payload. -/
def atlas : List Row := arAtlas ++ bridgeAtlas

@[simp] theorem atlas_length : atlas.length = 20 := by
  rfl

end AtanasovRanganathan.GenusFiveCubicAtlas
