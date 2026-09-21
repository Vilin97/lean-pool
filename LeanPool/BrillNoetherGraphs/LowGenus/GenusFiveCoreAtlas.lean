/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ConnectedCheckFast
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ExplicitPotential
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity

/-!
# The Atanasov--Ranganathan genus-five cubic atlas

This is the public-layer transcription of the sixteen loopless, bridgeless,
topologically trivalent graphs displayed in Figure 8 of Atanasov--Ranganathan.
It contains only incidence data and kernel-checked elementary properties; it
does not assert the classification theorem or any divisor construction.

The vertices `0, ..., 7` follow the TikZ node order.  Parallel TikZ edges are
separate ordered slots.  The source contains stray self-loop draw commands in
the twelfth and sixteenth scopes; both scopes are already cubic with twelve
non-loop edges, so those commands are omitted, as the figure caption requires.
-/

namespace AtanasovRanganathan.GenusFiveCoreAtlas

open Utilities

open Certificate.ExplicitPotential

abbrev Core := Certificate.ExplicitPotential.Core 8 12

/-- Number of half-edge incidences at a vertex of a loopless ordered core. -/
def incidenceDegree (core : Core) (vertex : Fin 8) : Nat :=
  ∑ edge : Fin 12,
    ((if core.tail edge = vertex then 1 else 0) +
      (if core.head edge = vertex then 1 else 0))

def Trivalent (core : Core) : Prop :=
  ∀ vertex : Fin 8, incidenceDegree core vertex = 3

def Loopless (core : Core) : Prop :=
  ∀ edge : Fin 12, core.tail edge ≠ core.head edge

/-- Figure scope 1 (`a6,b6,c6,d6,x,y,e6,f6`). -/
def row01Core : Core :=
  { tail := ![0, 0, 2, 1, 2, 3, 5, 2, 4, 4, 6, 6]
    head := ![1, 1, 0, 3, 3, 5, 7, 4, 6, 5, 7, 7] }

/-- Figure scope 2 (`a9,b9,c9,b9a,c9a,d9,e9,f9`). -/
def row02Core : Core :=
  { tail := ![0, 1, 2, 5, 5, 6, 7, 7, 1, 2, 3, 3]
    head := ![1, 2, 5, 6, 6, 7, 0, 0, 3, 4, 4, 4] }

/-- Figure scope 3 (`41,42,43,45,A3,A5,B3,B5`). -/
def row03Core : Core :=
  { tail := ![0, 2, 0, 3, 0, 2, 6, 3, 7, 4, 4, 6]
    head := ![2, 1, 3, 1, 1, 6, 4, 7, 5, 5, 5, 7] }

/-- Figure scope 4 (`A1,A2,A8,A7,A3,A4,A5,A6`). -/
def row04Core : Core :=
  { tail := ![0, 0, 1, 4, 4, 5, 6, 6, 7, 3, 3, 2]
    head := ![1, 1, 4, 5, 5, 6, 7, 7, 3, 2, 2, 0] }

/-- Figure scope 5 (`a6,b6,c6,d6,x,y,e6,f6`). -/
def row05Core : Core :=
  { tail := ![0, 0, 2, 1, 2, 3, 5, 2, 4, 4, 6, 6]
    head := ![1, 1, 0, 3, 5, 5, 7, 4, 6, 3, 7, 7] }

/-- Figure scope 6 (`a6,b6,c6,d6,e6,f6,q6,p6`). -/
def row06Core : Core :=
  { tail := ![0, 0, 2, 1, 2, 7, 7, 6, 3, 2, 4, 4]
    head := ![1, 1, 0, 3, 7, 6, 6, 3, 5, 4, 5, 5] }

/-- Figure scope 7 (`41,42,43,45,B1,B2,B3,B4`). -/
def row07Core : Core :=
  { tail := ![0, 2, 0, 3, 2, 0, 1, 6, 4, 4, 5, 5]
    head := ![2, 1, 3, 1, 3, 4, 5, 7, 6, 6, 7, 7] }

/-- Figure scope 8 (`a6,b6,c6,j6,d6,h6,e6,f6`). -/
def row08Core : Core :=
  { tail := ![0, 0, 6, 3, 1, 2, 4, 5, 5, 2, 6, 6]
    head := ![1, 1, 3, 0, 4, 4, 5, 7, 2, 3, 7, 7] }

/-- Figure scope 9 (`31,32,33,34,35,36,311,312`). -/
def row09Core : Core :=
  { tail := ![0, 2, 1, 2, 1, 3, 4, 5, 0, 3, 6, 6]
    head := ![2, 1, 0, 5, 4, 4, 5, 3, 6, 7, 7, 7] }

/-- Figure scope 10 (`31,32,33,34,35,36,37,38`). -/
def row10Core : Core :=
  { tail := ![0, 2, 1, 2, 1, 3, 4, 6, 6, 5, 0, 5]
    head := ![2, 1, 0, 5, 4, 4, 6, 7, 7, 3, 3, 7] }

/-- Figure scope 11 (outer square and inner square). -/
def row11Core : Core :=
  { tail := ![0, 1, 3, 2, 4, 5, 7, 6, 4, 5, 7, 6]
    head := ![1, 3, 2, 0, 5, 7, 6, 4, 0, 1, 3, 2] }

/-- Figure scope 12, omitting the anomalous extra self-loop command. -/
def row12Core : Core :=
  { tail := ![0, 4, 2, 3, 0, 1, 5, 6, 7, 5, 6, 7]
    head := ![4, 2, 3, 1, 3, 4, 6, 7, 5, 0, 1, 2] }

/-- Figure scope 13 (two `K₄`-minus-edge blocks). -/
def row13Core : Core :=
  { tail := ![0, 2, 0, 3, 2, 4, 6, 4, 7, 6, 0, 1]
    head := ![2, 1, 3, 1, 3, 6, 5, 7, 5, 7, 4, 5] }

/-- Figure scope 14 (`a,b,c,d,e,f,g,h`). -/
def row14Core : Core :=
  { tail := ![0, 7, 7, 7, 0, 2, 3, 1, 5, 4, 2, 3]
    head := ![6, 1, 6, 6, 2, 3, 1, 5, 4, 0, 5, 4] }

/-- Figure scope 15, with cyclic vertex labels `O1, ..., O8`. -/
def row15Core : Core :=
  { tail := ![0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 7]
    head := ![1, 2, 3, 4, 5, 6, 7, 0, 4, 5, 6, 3] }

/-- Figure scope 16, omitting the anomalous extra self-loop command. -/
def row16Core : Core :=
  { tail := ![0, 4, 2, 3, 0, 3, 5, 6, 7, 5, 6, 7]
    head := ![4, 2, 3, 1, 1, 4, 6, 7, 5, 0, 1, 2] }

theorem row01_trivalent : Trivalent row01Core := by intro v; fin_cases v <;> decide
theorem row02_trivalent : Trivalent row02Core := by intro v; fin_cases v <;> decide
theorem row03_trivalent : Trivalent row03Core := by intro v; fin_cases v <;> decide
theorem row04_trivalent : Trivalent row04Core := by intro v; fin_cases v <;> decide
theorem row05_trivalent : Trivalent row05Core := by intro v; fin_cases v <;> decide
theorem row06_trivalent : Trivalent row06Core := by intro v; fin_cases v <;> decide
theorem row07_trivalent : Trivalent row07Core := by intro v; fin_cases v <;> decide
theorem row08_trivalent : Trivalent row08Core := by intro v; fin_cases v <;> decide
theorem row09_trivalent : Trivalent row09Core := by intro v; fin_cases v <;> decide
theorem row10_trivalent : Trivalent row10Core := by intro v; fin_cases v <;> decide
theorem row11_trivalent : Trivalent row11Core := by intro v; fin_cases v <;> decide
theorem row12_trivalent : Trivalent row12Core := by intro v; fin_cases v <;> decide
theorem row13_trivalent : Trivalent row13Core := by intro v; fin_cases v <;> decide
theorem row14_trivalent : Trivalent row14Core := by intro v; fin_cases v <;> decide
theorem row15_trivalent : Trivalent row15Core := by intro v; fin_cases v <;> decide
theorem row16_trivalent : Trivalent row16Core := by intro v; fin_cases v <;> decide

theorem row01_loopless : Loopless row01Core := by intro e; fin_cases e <;> decide
theorem row02_loopless : Loopless row02Core := by intro e; fin_cases e <;> decide
theorem row03_loopless : Loopless row03Core := by intro e; fin_cases e <;> decide
theorem row04_loopless : Loopless row04Core := by intro e; fin_cases e <;> decide
theorem row05_loopless : Loopless row05Core := by intro e; fin_cases e <;> decide
theorem row06_loopless : Loopless row06Core := by intro e; fin_cases e <;> decide
theorem row07_loopless : Loopless row07Core := by intro e; fin_cases e <;> decide
theorem row08_loopless : Loopless row08Core := by intro e; fin_cases e <;> decide
theorem row09_loopless : Loopless row09Core := by intro e; fin_cases e <;> decide
theorem row10_loopless : Loopless row10Core := by intro e; fin_cases e <;> decide
theorem row11_loopless : Loopless row11Core := by intro e; fin_cases e <;> decide
theorem row12_loopless : Loopless row12Core := by intro e; fin_cases e <;> decide
theorem row13_loopless : Loopless row13Core := by intro e; fin_cases e <;> decide
theorem row14_loopless : Loopless row14Core := by intro e; fin_cases e <;> decide
theorem row15_loopless : Loopless row15Core := by intro e; fin_cases e <;> decide
theorem row16_loopless : Loopless row16Core := by intro e; fin_cases e <;> decide

/-! ## Connectivity

All sixteen rows, in one place.  Six of them (`01`, `02`, `04`, `05`, `08`,
`10`) used to be proved locally in the row and chamber files instead — nine
copies in all, because rows `08` and `10` repeated the fact once per chamber —
and `GenusFiveCubicAtlas` re-proved the same six inline.  They were kept out of
here only because touching this file invalidates the forty-six modules that
import it, including every generated cover; the generated covers now build

/-! # Genus Five Core Atlas -/
only in the independent generated checks.

The checker is `connectedCheckFast`
(`Utilities/Subdivision/ConnectedCheckFast.lean`): a union--find fold rather
than an enumeration of all `2⁸` vertex subsets.  Measured on exactly these
sixteen cores, the old `connectedCheck` cost `0.52 s` each and this costs
`0.013 s`. -/

private theorem connectedOf {core : Certificate.ExplicitPotential.Core 8 12}
    (h : core.connectedCheckFast = true) : core.Connected :=
  Certificate.ExplicitPotential.Core.connected_of_connectedCheckFast h

/-- The first displayed row, AR's first family, is connected. -/
theorem row01_connected : row01Core.Connected := connectedOf (by decide +kernel)

/-- The second displayed row, AR's second family, is connected. -/
theorem row02_connected : row02Core.Connected := connectedOf (by decide +kernel)

theorem row03_connected : row03Core.Connected := connectedOf (by decide +kernel)

/-- The necklace row, AR's fourth family, is connected. -/
theorem row04_connected : row04Core.Connected := connectedOf (by decide +kernel)

/-- The sixth-family row is connected. -/
theorem row05_connected : row05Core.Connected := connectedOf (by decide +kernel)

theorem row06_connected : row06Core.Connected := connectedOf (by decide +kernel)

/-- The configuration-5 row is connected. -/
theorem row07_connected : row07Core.Connected := connectedOf (by decide +kernel)

/-- The seventh-family row is connected. -/
theorem row08_connected : row08Core.Connected := connectedOf (by decide +kernel)

theorem row09_connected : row09Core.Connected := connectedOf (by decide +kernel)

/-- The ninth-family row is connected. -/
theorem row10_connected : row10Core.Connected := connectedOf (by decide +kernel)

/-- The cube row is connected.  This small public fact lets its readable AR
construction use the closed-subdivision rank-determining-set theorem without
importing the private generated atlas. -/
theorem row11_connected : row11Core.Connected := connectedOf (by decide +kernel)

/-- The twelfth displayed row is connected. -/
theorem row12_connected : row12Core.Connected := connectedOf (by decide +kernel)

/-- The two-block row is connected. -/
theorem row13_connected : row13Core.Connected := connectedOf (by decide +kernel)

theorem row14_connected : row14Core.Connected := connectedOf (by decide +kernel)

/-- The Möbius-ladder row is connected. -/
theorem row15_connected : row15Core.Connected := connectedOf (by decide +kernel)

/-- The final displayed row is connected. -/
theorem row16_connected : row16Core.Connected := connectedOf (by decide +kernel)

end AtanasovRanganathan.GenusFiveCoreAtlas
