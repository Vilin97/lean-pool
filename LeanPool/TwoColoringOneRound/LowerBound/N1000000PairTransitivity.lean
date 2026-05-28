/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

import LeanPool.TwoColoringOneRound.LowerBound.Correlation
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Data
import LeanPool.TwoColoringOneRound.LowerBound.N1000000StructureConstants

namespace Distributed2Coloring.LowerBound

namespace N1000000PairTransitivity

open scoped BigOperators

open Distributed2Coloring.LowerBound.Correlation
open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000StructureConstants

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SymN := Distributed2Coloring.LowerBound.Sym n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev V := Vertex n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev G := Correlation.G n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Mask := Distributed2Coloring.LowerBound.Mask

noncomputable instance : Fintype G := by infer_instance

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev i0 : Fin 3 := 0
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev i1 : Fin 3 := 1
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev i2 : Fin 3 := 2

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def bit (k : Nat) : Nat := (1 : Nat) <<< k

/-- The directed overlap mask between two vertices, as a `3×3` partial permutation bitmask. -/
def dirMask (u v : V) : Mask :=
  -- We build a `9`-bit number by appending three `3`-bit rows.
  let row0 : Nat :=
    ((if u.1 i0 = v.1 i0 then bit 0 else 0) ||| (if u.1 i0 = v.1 i1 then bit 1 else 0)) |||
      (if u.1 i0 = v.1 i2 then bit 2 else 0)
  let row1 : Nat :=
    ((if u.1 i1 = v.1 i0 then bit 0 else 0) ||| (if u.1 i1 = v.1 i1 then bit 1 else 0)) |||
      (if u.1 i1 = v.1 i2 then bit 2 else 0)
  let row2 : Nat :=
    ((if u.1 i2 = v.1 i0 then bit 0 else 0) ||| (if u.1 i2 = v.1 i1 then bit 1 else 0)) |||
      (if u.1 i2 = v.1 i2 then bit 2 else 0)
  (row2 <<< 6) ||| ((row1 <<< 3) ||| row0)

@[simp] lemma testBit_bit (k t : Nat) : (bit k).testBit t = decide (k = t) := by
  -- `bit k = 2^k`.
  simp [bit, Nat.shiftLeft_eq, Nat.testBit_two_pow]

private lemma testBit_ite_bit {p : Prop} [Decidable p] (k t : Nat) :
    (Nat.testBit (if p then bit k else 0) t) = (decide p && decide (k = t)) := by
  by_cases hp : p <;> simp [hp, testBit_bit]

private lemma decide_mod_two_ite_bit {p : Prop} [Decidable p] (k : Nat) :
    decide (((if p then bit k else 0) % 2) = 1) = (decide p && decide (k = 0)) := by
  by_cases hp : p
  · cases k with
    | zero =>
        simp [hp, bit]
    | succ k =>
        have hdvd : 2 ∣ 2 ^ (Nat.succ k) := by
          refine ⟨2 ^ k, by simp [Nat.pow_succ, Nat.mul_comm]⟩
        have hmod : (2 ^ (Nat.succ k)) % 2 = 0 :=
          Nat.mod_eq_zero_of_dvd hdvd
        simp [hp, bit, Nat.shiftLeft_eq, hmod]
  · simp [hp]

lemma dirMask_testBit (u v : V) (i j : Fin 3) :
    (dirMask u v).testBit (i.1 * 3 + j.1) = decide (u.1 i = v.1 j) := by
  -- There are only `3×3` relevant bit positions; compute each case.
  fin_cases i <;> fin_cases j <;>
    simp [dirMask, i0, i1, i2, testBit_ite_bit, decide_mod_two_ite_bit, Nat.testBit_or,
      Nat.testBit_shiftLeft]

lemma dirMask_lt (u v : V) : dirMask u v < (1 <<< 9) := by
  -- Each row is a `3`-bit number, hence `< 2^3 = 8`.
  have hu01 : u.1 i0 ≠ u.1 i1 := by
    intro hEq
    exact (by decide : (i0 : Fin 3) ≠ i1) (u.2 hEq)
  have hu02 : u.1 i0 ≠ u.1 i2 := by
    intro hEq
    exact (by decide : (i0 : Fin 3) ≠ i2) (u.2 hEq)
  have hu12 : u.1 i1 ≠ u.1 i2 := by
    intro hEq
    exact (by decide : (i1 : Fin 3) ≠ i2) (u.2 hEq)
  have hv01 : v.1 i0 ≠ v.1 i1 := by
    intro hEq
    exact (by decide : (i0 : Fin 3) ≠ i1) (v.2 hEq)
  have hv02 : v.1 i0 ≠ v.1 i2 := by
    intro hEq
    exact (by decide : (i0 : Fin 3) ≠ i2) (v.2 hEq)
  have hv12 : v.1 i1 ≠ v.1 i2 := by
    intro hEq
    exact (by decide : (i1 : Fin 3) ≠ i2) (v.2 hEq)
  have hv10 : v.1 i1 ≠ v.1 i0 := by
    simpa [eq_comm] using hv01
  have hv20 : v.1 i2 ≠ v.1 i0 := by
    simpa [eq_comm] using hv02
  have hv21 : v.1 i2 ≠ v.1 i1 := by
    simpa [eq_comm] using hv12
  have hRow0 :
      (let row0 : Nat :=
        ((if u.1 i0 = v.1 i0 then bit 0 else 0) ||| (if u.1 i0 = v.1 i1 then bit 1 else 0)) |||
          (if u.1 i0 = v.1 i2 then bit 2 else 0); row0) < 2 ^ 3 := by
    -- There are only 8 Boolean possibilities.
    by_cases h00 : u.1 i0 = v.1 i0 <;>
    by_cases h01 : u.1 i0 = v.1 i1 <;>
    by_cases h02 : u.1 i0 = v.1 i2 <;>
    simp [h00, h01, h02, bit, hv01, hv02, hv12, hv10, hv20, hv21]
  have hRow1 :
      (let row1 : Nat :=
        ((if u.1 i1 = v.1 i0 then bit 0 else 0) ||| (if u.1 i1 = v.1 i1 then bit 1 else 0)) |||
          (if u.1 i1 = v.1 i2 then bit 2 else 0); row1) < 2 ^ 3 := by
    by_cases h10 : u.1 i1 = v.1 i0 <;>
    by_cases h11 : u.1 i1 = v.1 i1 <;>
    by_cases h12 : u.1 i1 = v.1 i2 <;>
    simp [h10, h11, h12, bit, hv01, hv02, hv12, hv10, hv20, hv21]
  have hRow2 :
      (let row2 : Nat :=
        ((if u.1 i2 = v.1 i0 then bit 0 else 0) ||| (if u.1 i2 = v.1 i1 then bit 1 else 0)) |||
          (if u.1 i2 = v.1 i2 then bit 2 else 0); row2) < 2 ^ 3 := by
    by_cases h20 : u.1 i2 = v.1 i0 <;>
    by_cases h21 : u.1 i2 = v.1 i1 <;>
    by_cases h22 : u.1 i2 = v.1 i2 <;>
    simp [h20, h21, h22, bit, hv01, hv02, hv12, hv10, hv20, hv21]
  -- Append the rows using `Nat.append_lt`.
  -- `row1 <<< 3 ||| row0 < 2^6`, then `row2 <<< 6 ||| ... < 2^9`.
  have h01 :
      (let row0 : Nat :=
        ((if u.1 i0 = v.1 i0 then bit 0 else 0) ||| (if u.1 i0 = v.1 i1 then bit 1 else 0)) |||
          (if u.1 i0 = v.1 i2 then bit 2 else 0)
      let row1 : Nat :=
        ((if u.1 i1 = v.1 i0 then bit 0 else 0) ||| (if u.1 i1 = v.1 i1 then bit 1 else 0)) |||
          (if u.1 i1 = v.1 i2 then bit 2 else 0); (row1 <<< 3) ||| row0) <
        2 ^ (3 + 3) := by
    simpa using Nat.append_lt (hx := hRow0) (hy := hRow1)
  have h012 :
      (let row0 : Nat :=
        ((if u.1 i0 = v.1 i0 then bit 0 else 0) ||| (if u.1 i0 = v.1 i1 then bit 1 else 0)) |||
          (if u.1 i0 = v.1 i2 then bit 2 else 0)
      let row1 : Nat :=
        ((if u.1 i1 = v.1 i0 then bit 0 else 0) ||| (if u.1 i1 = v.1 i1 then bit 1 else 0)) |||
          (if u.1 i1 = v.1 i2 then bit 2 else 0)
      let row2 : Nat :=
        ((if u.1 i2 = v.1 i0 then bit 0 else 0) ||| (if u.1 i2 = v.1 i1 then bit 1 else 0)) |||
          (if u.1 i2 = v.1 i2 then bit 2 else 0); (row2 <<< 6) |||
        ((row1 <<< 3) ||| row0)) < 2 ^ ((3 + 3) + 3) := by
    simpa [Nat.add_assoc] using Nat.append_lt (hx := h01) (hy := hRow2)
  -- Rewrite `dirMask` into the row form and finish.
  simpa [dirMask] using h012

/-!
This module intentionally contains only the low-level `dirMask` encoding lemmas.

The higher-level results that were once planned here are proved in
`N1000000Transitivity` as:
- `dirMask_isPartialPermMask`
- `exists_perm_of_dirMask_eq`
-/

end N1000000PairTransitivity

end Distributed2Coloring.LowerBound
