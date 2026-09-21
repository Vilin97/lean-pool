/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CubicCore
import Mathlib.Tactic

/-!
# The twenty loopless cubic genus-five core types

The first sixteen entries are the Atanasov--Ranganathan rows already owned by
`LowGenus`.  The final four are the elementary bridge-core types.  This module
is passive finite data plus kernel-checked validity; exhaustiveness is proved
separately by the public canonical classifier.
-/
namespace AtanasovRanganathan.GenusFiveCubicAtlas

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ExplicitPotential
open AtanasovRanganathan.GenusFiveCoreAtlas

/-- One concrete loopless `8`-vertex, `12`-slot cubic core. -/
structure Row where
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

def row01 : Row := ⟨row01Core, row01_loopless, row01_connected, row01_trivalent⟩
def row02 : Row := ⟨row02Core, row02_loopless, row02_connected, row02_trivalent⟩
def row03 : Row := ⟨row03Core, row03_loopless, row03_connected, row03_trivalent⟩
def row04 : Row := ⟨row04Core, row04_loopless, row04_connected, row04_trivalent⟩
def row05 : Row := ⟨row05Core, row05_loopless, row05_connected, row05_trivalent⟩
def row06 : Row := ⟨row06Core, row06_loopless, row06_connected, row06_trivalent⟩
def row07 : Row := ⟨row07Core, row07_loopless, row07_connected, row07_trivalent⟩
def row08 : Row := ⟨row08Core, row08_loopless, row08_connected, row08_trivalent⟩
def row09 : Row := ⟨row09Core, row09_loopless, row09_connected, row09_trivalent⟩
def row10 : Row := ⟨row10Core, row10_loopless, row10_connected, row10_trivalent⟩
def row11 : Row := ⟨row11Core, row11_loopless, row11_connected, row11_trivalent⟩
def row12 : Row := ⟨row12Core, row12_loopless, row12_connected, row12_trivalent⟩
def row13 : Row := ⟨row13Core, row13_loopless, row13_connected, row13_trivalent⟩
def row14 : Row := ⟨row14Core, row14_loopless, row14_connected, row14_trivalent⟩
def row15 : Row := ⟨row15Core, row15_loopless, row15_connected, row15_trivalent⟩
def row16 : Row := ⟨row16Core, row16_loopless, row16_connected, row16_trivalent⟩

def arAtlas : List Row :=
  [row01, row02, row03, row04, row05, row06, row07, row08,
    row09, row10, row11, row12, row13, row14, row15, row16]

/-! ## The four bridge rows -/

def rootDoubleCore : ExplicitPotential.Core 8 12 where
  tail := ![0, 0, 1, 1, 0, 3, 3, 4, 5, 5, 6, 6]
  head := ![1, 2, 2, 2, 3, 4, 4, 5, 6, 7, 7, 7]

def oneChordCore : ExplicitPotential.Core 8 12 where
  tail := ![0, 0, 1, 1, 0, 3, 3, 4, 4, 5, 6, 6]
  head := ![1, 2, 2, 2, 3, 4, 5, 5, 6, 7, 7, 7]

def squareCore : ExplicitPotential.Core 8 12 where
  tail := ![0, 0, 1, 1, 0, 3, 3, 4, 4, 5, 5, 6]
  head := ![1, 2, 2, 2, 3, 4, 5, 6, 7, 6, 7, 7]

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

def rootDouble : Row := ⟨rootDoubleCore, rootDouble_loopless,
  connected rootDoubleCore (by decide +kernel), rootDouble_cubic⟩
def oneChord : Row := ⟨oneChordCore, oneChord_loopless,
  connected oneChordCore (by decide +kernel), oneChord_cubic⟩
def square : Row := ⟨squareCore, square_loopless,
  connected squareCore (by decide +kernel), square_cubic⟩
def doubleMatching : Row := ⟨doubleMatchingCore, doubleMatching_loopless,
  connected doubleMatchingCore (by decide +kernel), doubleMatching_cubic⟩

def bridgeAtlas : List Row := [rootDouble, oneChord, square, doubleMatching]

/-- The exact atlas order used by the emitted classifier payload. -/
def atlas : List Row := arAtlas ++ bridgeAtlas

@[simp] theorem atlas_length : atlas.length = 20 := by
  rfl

end AtanasovRanganathan.GenusFiveCubicAtlas
