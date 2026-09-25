/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Tricycle.Core
import LeanPool.BrillNoetherGraphs.Utilities.Gonality.GonalityTransport
import LeanPool.BrillNoetherGraphs.Utilities.Gonality.BurnedSet
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankDeterminingSet
import Mathlib.Tactic

/-!
# The tricycle upper bounds

Two explicit divisors, both certified through the *core vertices are
rank-determining* theorem `Spec.rank_ge_one_of_forall_mem_coreVertices`
(`Utilities/Foundations/RankDeterminingSet.lean`), which is the repository's
metric-free form of Luo's Theorem 1.6 and is exactly the source's
Corollary 2.13.  Only seven obligations arise — one per core vertex — and each
is a single explicit firing set, checked by `decide`.

* **Proposition 3.3** of van Dobben de Bruyn–Smit–van der Wegen:
  `D₀ = 2·v₀ + Σᵢ (midpoint of transition slot i)` has positive rank on
  `σ₂(T_m)`, so `dgon(σ₂(T_m)) ≤ 5`.
  Firing `Sᵢᶜ` moves exactly four chips: two off `v₀` — *which is why the
  coefficient is `2`, and why `k = 2` and not `k = 1`* — and one off each of
  the two transition midpoints bounding the component `Sᵢ` of
  `σ₂(T_m) ∖ supp D₀` containing the cycle `Cᵢ`.  At `k = 2` a transition
  midpoint is adjacent to both of its transition vertices, so those two chips
  land exactly on `vᵢ⁻` and `vᵢ⁺`.
* **Theorem 3.9, upper half**: one chip on each of the six transition vertices
  has positive rank on `T_m`, so `dgon(T_m) ≤ 6`.

The firing sets and residual divisors are checked directly by the Lean kernel.
-/

namespace Utilities.Tricycle

open Finset

open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Gonality

/-! ## Winnability from an explicit script -/

/-- `effective` is a bounded quantifier over a `Fintype`; make that visible to
instance search so the concrete checks below are `decide`-shaped. -/
instance decidableEffective {G : CFGraph} (D : CFDiv G) : Decidable (effective D) := by
  unfold effective
  infer_instance

/-- An explicit firing script witnessing winnability. -/
theorem winnable_of_effective_add_prin {G : CFGraph} (D : CFDiv G)
    (x : firingScript G) (h : effective (D + prin G x)) : winnable G D := by
  refine ⟨D + prin G x, h, ?_⟩
  show (D + prin G x) - D ∈ principalDivisors G
  rw [principal_iff_eq_prin]
  exact ⟨x, by ring⟩

/-! ## The two concrete subdivisions -/

/-- The minimal tricycle `T_m` itself. -/
def Tm : Spec 7 15 := tricycleSpec (fun _ => 1) (fun _ => Nat.one_pos)

/-- Its `2`-subdivision `σ₂(T_m)`. -/
def Tm2 : Spec 7 15 := tricycleSpec (fun _ => 2) (fun _ => by omega)

theorem Tm_connected : graphConnected Tm.graph :=
  tricycleSpec_connected _ _

theorem Tm2_connected : graphConnected Tm2.graph :=
  tricycleSpec_connected _ _

/-! ## Theorem 3.9, upper half: `dgon(T_m) ≤ 6` -/

/-- One chip on each of the six transition vertices. -/
def sixChips : CFDiv Tm.graph :=
  fun v => if v = Tm.coreVertex 0 then 0 else 1

/-- The outer ring of `T_m`: everything but the centre.  Firing it once is legal
(each transition vertex has exactly one spoke edge and exactly one chip) and
delivers six chips to `v₀`. -/
def TmOuterRing : Finset Tm.graph.V :=
  Finset.univ.filter (fun v => v ≠ Tm.coreVertex 0)

theorem sixChips_effective : effective sixChips := by decide

theorem sixChips_deg : deg sixChips = 6 := by decide

theorem sixChips_rank : rank Tm.graph sixChips ≥ 1 := by
  refine Tm.rank_ge_one_of_forall_mem_coreVertices Tm_connected sixChips ?_
  intro x hx
  obtain ⟨v, rfl⟩ := (Tm.mem_coreVertices x).mp hx
  fin_cases v
  · exact winnable_of_effective_add_prin _ (indicatorScript Tm.graph TmOuterRing) (by decide)
  · exact winnable_of_effective_add_prin _ 0 (by decide)
  · exact winnable_of_effective_add_prin _ 0 (by decide)
  · exact winnable_of_effective_add_prin _ 0 (by decide)
  · exact winnable_of_effective_add_prin _ 0 (by decide)
  · exact winnable_of_effective_add_prin _ 0 (by decide)
  · exact winnable_of_effective_add_prin _ 0 (by decide)

/-- **Theorem 3.9, upper half.**  The minimal tricycle has divisorial gonality
at most six. -/
theorem divisorialGonality_Tm_le_six : divisorialGonality Tm.graph ≤ 6 :=
  divisorialGonality_le sixChips_effective sixChips_deg sixChips_rank

/-! ## Proposition 3.3: `dgon(σ₂(T_m)) ≤ 5` -/

/-- The midpoint of transition slot `i` in `σ₂`. -/
def transitionMidpoint (i : Fin 3) : Tm2.graph.V :=
  Tm2.interiorVertex (transitionSlot i) ⟨0, by decide +kernel +revert⟩

/-- **The special divisor** `D₀ = 2·v₀ + Σᵢ (midpoint of transition slot i)`. -/
def specialDivisor : CFDiv Tm2.graph :=
  fun v =>
    if v = Tm2.coreVertex 0 then 2
    else if v = transitionMidpoint 0 then 1
    else if v = transitionMidpoint 1 then 1
    else if v = transitionMidpoint 2 then 1
    else 0

/-- The component of `σ₂(T_m) ∖ supp D₀` containing the cycle `Cᵢ`: the cycle
itself together with the interiors of the two spokes at `vᵢ⁻` and `vᵢ⁺`. -/
def cycleComponent (i : Fin 3) : Finset Tm2.graph.V :=
  {Tm2.coreVertex (vMinus i), Tm2.coreVertex (vPlus i),
    Tm2.interiorVertex (cycleSlot i 0) ⟨0, by decide +kernel +revert⟩,
    Tm2.interiorVertex (cycleSlot i 1) ⟨0, by decide +kernel +revert⟩,
    Tm2.interiorVertex (spokeMinus i) ⟨0, by decide +kernel +revert⟩,
    Tm2.interiorVertex (spokePlus i) ⟨0, by decide +kernel +revert⟩}

/-- The set actually fired: the complement of `Sᵢ`. -/
def cycleComponentCompl (i : Fin 3) : Finset Tm2.graph.V :=
  Finset.univ.filter (fun v => v ∉ cycleComponent i)

theorem specialDivisor_effective : effective specialDivisor := by decide

theorem specialDivisor_deg : deg specialDivisor = 5 := by decide

theorem specialDivisor_rank : rank Tm2.graph specialDivisor ≥ 1 := by
  refine Tm2.rank_ge_one_of_forall_mem_coreVertices Tm2_connected specialDivisor ?_
  intro x hx
  obtain ⟨v, rfl⟩ := (Tm2.mem_coreVertices x).mp hx
  fin_cases v
  -- `v₀` carries two chips, so it is reached with the zero script.
  · exact winnable_of_effective_add_prin _ 0 (by decide)
  -- `v₁⁻`, `v₁⁺`: fire the complement of `S₁`.
  · exact winnable_of_effective_add_prin _
      (indicatorScript Tm2.graph (cycleComponentCompl 0)) (by decide)
  · exact winnable_of_effective_add_prin _
      (indicatorScript Tm2.graph (cycleComponentCompl 0)) (by decide)
  -- `v₂⁻`, `v₂⁺`: fire the complement of `S₂`.
  · exact winnable_of_effective_add_prin _
      (indicatorScript Tm2.graph (cycleComponentCompl 1)) (by decide)
  · exact winnable_of_effective_add_prin _
      (indicatorScript Tm2.graph (cycleComponentCompl 1)) (by decide)
  -- `v₃⁻`, `v₃⁺`: fire the complement of `S₃`.
  · exact winnable_of_effective_add_prin _
      (indicatorScript Tm2.graph (cycleComponentCompl 2)) (by decide)
  · exact winnable_of_effective_add_prin _
      (indicatorScript Tm2.graph (cycleComponentCompl 2)) (by decide)

/-- **Proposition 3.3.**  The `2`-subdivision of the minimal tricycle has
divisorial gonality at most five. -/
theorem divisorialGonality_Tm2_le_five : divisorialGonality Tm2.graph ≤ 5 :=
  divisorialGonality_le specialDivisor_effective specialDivisor_deg specialDivisor_rank

end Utilities.Tricycle
