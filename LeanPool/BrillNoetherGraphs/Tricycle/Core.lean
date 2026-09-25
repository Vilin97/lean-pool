/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionSeparator
import Mathlib.Tactic

/-!
# The tricycle core

The counterexample of van Dobben de Bruyn, Smit and van der Wegen,
*Discrete and metric divisorial gonality can be different*, JCTA **189** (2022)
105619 (arXiv:2106.12568), in the vocabulary of this repository.

**Tricycle characterization.** The formalization uses the characterization
stated in the source text and depicted in Figures 1(b), 1(c), and 3:

> a multigraph is a tricycle if and only if it is a subdivision of the minimal
> tricycle `T_m` in which the transition edges are not subdivided.

That is the definition formalized here. The theorems in this library prove
`dgon(T_m) = 6` and `dgon(σ₂(T_m)) = 5`.

## The slot dictionary

`tricycleCore : Core 7 15` has vertices `v₀ = 0` and
`v₁⁻ = 1, v₁⁺ = 2, v₂⁻ = 3, v₂⁺ = 4, v₃⁻ = 5, v₃⁺ = 6`, and slots

| slots | role | source's name |
|---|---|---|
| 0–5 | `v₀ — vᵢ^±` | the six **spokes** |
| 6,7 / 8,9 / 10,11 | parallel pairs `vᵢ⁻ — vᵢ⁺` | the three **cycles** `C₁,C₂,C₃` |
| 12,13,14 | `v₁⁺—v₂⁻`, `v₂⁺—v₃⁻`, `v₃⁺—v₁⁻` | the three **transition** slots |

A subdivision `H` of `T_m` is `tricycleSpec length hpos` for an arbitrary
positive length vector; `σ_k(T_m)` is `length ≡ k`; and a *tricycle graph* is
one with `IsTricycle length`, i.e. the three transition slots have length one.
-/

namespace Utilities.Tricycle

open Finset

open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph

/-! ## The core -/

/-- The minimal tricycle `T_m` as an ordered core: six spokes, three bananas,
three transition slots. -/
def tricycleCore : ExplicitPotential.Core 7 15 where
  tail := ![0, 0, 0, 0, 0, 0, 1, 1, 3, 3, 5, 5, 2, 4, 6]
  head := ![1, 2, 3, 4, 5, 6, 2, 2, 4, 4, 6, 6, 3, 5, 1]

theorem tricycleCore_loopless :
    ∀ edge : Fin 15, tricycleCore.tail edge ≠ tricycleCore.head edge := by decide

theorem tricycleCore_connected : tricycleCore.Connected := by
  rw [← ExplicitPotential.Core.connectedCheck_eq_true_iff]
  decide

/-! ## Named vertices and slots -/

/-- The central vertex `v₀`. -/
def centre : Fin 7 := 0

/-- The transition vertices `vᵢ⁻`. -/
def vMinus : Fin 3 → Fin 7 := ![1, 3, 5]

/-- The transition vertices `vᵢ⁺`. -/
def vPlus : Fin 3 → Fin 7 := ![2, 4, 6]

/-- The spoke slot `v₀ — vᵢ⁻`. -/
def spokeMinus : Fin 3 → Fin 15 := ![0, 2, 4]

/-- The spoke slot `v₀ — vᵢ⁺`. -/
def spokePlus : Fin 3 → Fin 15 := ![1, 3, 5]

/-- The two parallel slots of the cycle `Cᵢ`. -/
def cycleSlot : Fin 3 → Fin 2 → Fin 15 := ![![6, 7], ![8, 9], ![10, 11]]

/-- The transition slot leaving `vᵢ⁺`. -/
def transitionSlot : Fin 3 → Fin 15 := ![12, 13, 14]

/-- The six spoke slots. -/
def spokeSlots : Finset (Fin 15) := {0, 1, 2, 3, 4, 5}

/-- The six transition vertices. -/
def transitionVertices : Finset (Fin 7) := {1, 2, 3, 4, 5, 6}

/-! ## The slot dictionary, verified -/

theorem spokeMinus_ends (i : Fin 3) :
    tricycleCore.tail (spokeMinus i) = centre ∧
      tricycleCore.head (spokeMinus i) = vMinus i := by decide +kernel +revert

theorem spokePlus_ends (i : Fin 3) :
    tricycleCore.tail (spokePlus i) = centre ∧
      tricycleCore.head (spokePlus i) = vPlus i := by decide +kernel +revert

theorem cycleSlot_ends (i : Fin 3) (j : Fin 2) :
    tricycleCore.tail (cycleSlot i j) = vMinus i ∧
      tricycleCore.head (cycleSlot i j) = vPlus i := by decide +kernel +revert

theorem transitionSlot_ends (i : Fin 3) :
    tricycleCore.tail (transitionSlot i) = vPlus i ∧
      tricycleCore.head (transitionSlot i) = vMinus (i + 1) := by decide +kernel +revert

theorem mem_spokeSlots_iff (e : Fin 15) :
    e ∈ spokeSlots ↔ ∃ i : Fin 3, e = spokeMinus i ∨ e = spokePlus i := by decide +kernel +revert

theorem mem_transitionVertices_iff (v : Fin 7) :
    v ∈ transitionVertices ↔ ∃ i : Fin 3, v = vMinus i ∨ v = vPlus i := by
  decide +kernel +revert

/-- The fifteen slots are exactly the six spokes, the six cycle slots and the
three transition slots. -/
theorem slot_classification (e : Fin 15) :
    (∃ i : Fin 3, e = spokeMinus i ∨ e = spokePlus i) ∨
      (∃ i : Fin 3, ∃ j : Fin 2, e = cycleSlot i j) ∨
      (∃ i : Fin 3, e = transitionSlot i) := by decide +kernel +revert

/-! ## Subdivisions of the tricycle core -/

/-- A subdivision `H` of the minimal tricycle, at an arbitrary positive length
vector. -/
def tricycleSpec (length : Fin 15 → ℕ) (hpos : ∀ e, 0 < length e) : Spec 7 15 :=
  Spec.ofCore tricycleCore (by omega) tricycleCore_loopless length hpos

@[simp] theorem tricycleSpec_core (length : Fin 15 → ℕ) (hpos : ∀ e, 0 < length e) :
    (tricycleSpec length hpos).core = tricycleCore := rfl

@[simp] theorem tricycleSpec_length (length : Fin 15 → ℕ) (hpos : ∀ e, 0 < length e)
    (e : Fin 15) : (tricycleSpec length hpos).length e = length e := rfl

theorem tricycleSpec_connected (length : Fin 15 → ℕ) (hpos : ∀ e, 0 < length e) :
    graphConnected (tricycleSpec length hpos).graph :=
  (tricycleSpec length hpos).graph_connected_of_coreConnected tricycleCore_connected

/-- Every subdivision of the minimal tricycle has genus nine; in particular the
tricycle attains the Brill--Noether bound `⌊(g+3)/2⌋ = 6` with equality. -/
theorem tricycleSpec_genus (length : Fin 15 → ℕ) (hpos : ∀ e, 0 < length e) :
    genus (tricycleSpec length hpos).graph = 9 := by
  rw [Spec.genus_graph]
  decide

/-- **A tricycle graph**: the transition slots are not subdivided.  This is the
characterisation at line 537 of the source's TeX, not Definition 3.1. -/
def IsTricycle (length : Fin 15 → ℕ) : Prop := ∀ i : Fin 3, length (transitionSlot i) = 1

end Utilities.Tricycle
