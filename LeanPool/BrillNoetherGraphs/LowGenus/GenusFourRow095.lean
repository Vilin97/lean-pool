/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Segments.AtanasovRanganathanConfigurations
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ConnectedCheckFast
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.WindowProfileReachability
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourCubicAtlas

/-!
# The signed-window proof for genus-four Core 095

Core 095 is the loopless six-vertex, nine-slot core occurring as the first
family in Atanasov--Ranganathan.  This file translates the short firing
profiles recorded in the accompanying analysis
into the generic signed-window API.

The catalog orientation is

```
0: 0--4   1,2: 0--5   3: 1--3   4: 1--4
5: 1--5   6,7: 2--3   8: 2--4.
```

We first normalize `length 0 <= length 5`.  The opposite chamber is carried
to this one by the Core-095 involution and is treated separately below.
-/

namespace LowGenus.GenusFourRow095
open Utilities.Certificate

open Utilities

open Finset
open SubdivisionGraph
open WindowProfile

/-- The ordered nine-slot presentation of the catalog's loopless Core 095.
Keeping the concrete cardinalities visible makes subsequent `Fin` arithmetic
small and transparent. -/
def core : ExplicitPotential.Core 6 9 where
  tail := ![0, 0, 0, 1, 1, 1, 2, 2, 2]
  head := ![4, 5, 5, 3, 4, 5, 3, 3, 4]

/-- The proof core is definitionally the public cubic-atlas row. -/
theorem core_eq_atlas :
    core = AtanasovRanganathan.GenusFourCubicAtlas.row095Core := rfl

theorem core_loopless (edge : Fin 9) :
    core.tail edge ≠ core.head edge := by
  fin_cases edge <;> decide

theorem core_connected : core.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast (core := core) (by decide)

/-- Core 095 with arbitrary positive integral edge lengths. -/
abbrev Spec
    (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge) :
    SubdivisionGraph.Spec 6 9 where
  core := core
  length := length
  core_nonempty := by decide
  core_loopless := core_loopless
  length_pos := hLength

variable (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge)

theorem graphConnected : graphConnected (Spec length hLength).graph := by
  exact (Spec length hLength).graph_connected_of_coreConnected core_connected

/-- The comparison parameters used in the paper's first-family picture. -/
abbrev A : ℕ := length 0
abbrev X : ℕ := length 5 - length 0
abbrev B : ℕ := length 3
abbrev C : ℕ := length 8
abbrev Delta : ℕ := length 4

/-- Under the normalized inequality, the long central slot has length
`A + X`. -/
theorem length_five_eq_A_add_X (hNorm : length 0 ≤ length 5) :
    length 5 = A length + X length := by
  simp only [A, X]
  omega

/-- The moving chip `q`, at distance `X` from vertex 1 on slot 5. -/
def q (_hNorm : length 0 ≤ length 5) : (Spec length hLength).Vertex :=
  (Spec length hLength).pathVertex 5
    ⟨X length, by
      dsimp [Spec, X]
      have hSub := Nat.sub_le (length 5) (length 0)
      have hPos := hLength (5 : Fin 9)
      omega⟩
/-- The common profile reaching vertices `a=0` and `b=5` from every one of
the three displayed divisors.  Its endpoint divisor is
`a + b - c - q`.
-/
def abProfile (hNorm : length 0 ≤ length 5) :
    WindowProfile.Data (Spec length hLength) where
  coreValue := fun vertex =>
    if vertex = 0 ∨ vertex = 5 then 0 else (A length : ℤ)
  start := fun edge => if edge = 5 then X length else 0
  stop := fun edge =>
    if edge = 0 then A length else if edge = 5 then length 5 else 0
  slope := fun edge => if edge = 0 then 1 else if edge = 5 then -1 else 0
  start_le_stop := by
    intro edge
    by_cases hFive : edge = 5
    · subst edge
      simp [X]
    · simp [hFive]
  stop_le_length := by
    intro edge
    by_cases hZero : edge = 0
    · subst edge
      simp [A]
    · by_cases hFive : edge = 5
      · subst edge
        simp
      · simp [hZero, hFive]
  endpoint_compatible := by
    intro edge
    fin_cases edge
    all_goals simp [core, A, X]
    all_goals omega

@[simp] theorem abProfile_slope (hNorm : length 0 ≤ length 5)
    (edge : Fin 9) :
    (abProfile length hLength hNorm).slope edge =
      if edge = 0 then 1 else if edge = 5 then -1 else 0 := rfl

@[simp] theorem abProfile_start_zero (hNorm : length 0 ≤ length 5) :
    (Spec length hLength).pathVertex 0
        ((abProfile length hLength hNorm).startPosition 0) =
      (Spec length hLength).coreVertex 0 := by
  calc
    _ = (Spec length hLength).pathVertex 0
        ⟨0, by change 0 < length 0 + 1; omega⟩ := by
          apply (Spec length hLength).pathVertex_eq_of_val_eq
          rfl
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.tail 0) := by
          exact (Spec length hLength).pathVertex_zero 0
    _ = _ := rfl

@[simp] theorem abProfile_stop_zero (hNorm : length 0 ≤ length 5) :
    (Spec length hLength).pathVertex 0
        ((abProfile length hLength hNorm).stopPosition 0) =
      (Spec length hLength).coreVertex 4 := by
  calc
    _ = (Spec length hLength).pathVertex 0
        ⟨length 0, by change length 0 < length 0 + 1; omega⟩ := by
          apply (Spec length hLength).pathVertex_eq_of_val_eq
          rfl
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.head 0) := by
          exact (Spec length hLength).pathVertex_length 0
    _ = _ := rfl

@[simp] theorem abProfile_start_five (hNorm : length 0 ≤ length 5) :
    (Spec length hLength).pathVertex 5
        ((abProfile length hLength hNorm).startPosition 5) =
      q length hLength hNorm := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

@[simp] theorem abProfile_stop_five (hNorm : length 0 ≤ length 5) :
    (Spec length hLength).pathVertex 5
        ((abProfile length hLength hNorm).stopPosition 5) =
      (Spec length hLength).coreVertex 5 := by
  calc
    _ = (Spec length hLength).pathVertex 5
        ⟨length 5, by change length 5 < length 5 + 1; omega⟩ := by
          apply (Spec length hLength).pathVertex_eq_of_val_eq
          rfl
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.head 5) := by
          exact (Spec length hLength).pathVertex_length 5
    _ = _ := rfl

/-- Exact sparse principal divisor of the common `a/b` profile. -/
theorem abProfile_endpointDivisors (hNorm : length 0 ≤ length 5) :
    (abProfile length hLength hNorm).endpointDivisors =
      oneChip ((Spec length hLength).coreVertex 0) +
        oneChip ((Spec length hLength).coreVertex 5) -
        oneChip ((Spec length hLength).coreVertex 4) -
        oneChip (q length hLength hNorm) := by
  classical
  rw [WindowProfile.Data.endpointDivisors]
  simp [Fin.sum_univ_succ, abProfile_slope, abProfile_start_zero,
    abProfile_stop_zero, abProfile_start_five, abProfile_stop_five]
  abel

/-- The common profile reaches `a=0` for any effective third chip. -/
theorem reaches_zero
    (hNorm : length 0 ≤ length 5) (third : (Spec length hLength).Vertex) :
    StrongSeparator.Reaches (Spec length hLength).graph
      (AtanasovRanganathan.Configurations.threeChipDivisor
        ((Spec length hLength).coreVertex 4) (q length hLength hNorm) third)
      ((Spec length hLength).coreVertex 0) := by
  apply (abProfile length hLength hNorm).reaches_of_effective_endpointDivisors
  rw [abProfile_endpointDivisors]
  intro vertex
  simp [AtanasovRanganathan.Configurations.threeChipDivisor, oneChip]
  split_ifs <;> omega

/-- The same common profile reaches `b=5`. -/
theorem reaches_five
    (hNorm : length 0 ≤ length 5) (third : (Spec length hLength).Vertex) :
    StrongSeparator.Reaches (Spec length hLength).graph
      (AtanasovRanganathan.Configurations.threeChipDivisor
        ((Spec length hLength).coreVertex 4) (q length hLength hNorm) third)
      ((Spec length hLength).coreVertex 5) := by
  apply (abProfile length hLength hNorm).reaches_of_effective_endpointDivisors
  rw [abProfile_endpointDivisors]
  intro vertex
  simp [AtanasovRanganathan.Configurations.threeChipDivisor, oneChip]
  split_ifs <;> omega

end LowGenus.GenusFourRow095
