/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow095
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionIso

/-!
# The normalization involution of Core 095

The Atanasov--Ranganathan first-family proof normalizes `L₀ ≤ L₅`.
Core 095 has an involution

```
(0 5)(1 4)(2 3)
```

on core vertices.  It exchanges slots `0,5` and `3,8`, fixes the other
slots, and reverses every slot orientation.  This file packages that
involution as an occurrence-preserving subdivision relabeling, so a proof in
the normalized chamber transports to all positive length assignments.
-/

@[expose] public section

namespace LowGenus.GenusFourRow095
open Utilities.Certificate

open Utilities

open SubdivisionGraph

/-- Slot permutation induced by the Core-095 involution. -/
def slotSwapFun : Fin 9 → Fin 9 := ![5, 1, 2, 8, 4, 0, 6, 7, 3]

theorem slotSwapFun_bijective : Function.Bijective slotSwapFun := by decide

/-- The involutive permutation of the nine slots induced by the row-095 core symmetry, packaged
as an equivalence for transporting lengths. -/
def slotSwap : Fin 9 ≃ Fin 9 where
  toFun := slotSwapFun
  invFun := slotSwapFun
  left_inv := by
    intro edge
    fin_cases edge <;> rfl
  right_inv := by
    intro edge
    fin_cases edge <;> rfl

@[simp] theorem slotSwap_apply (edge : Fin 9) :
    slotSwap edge = slotSwapFun edge := rfl

/-- Pull a length assignment across the slot involution. -/
def swappedLength (length : Fin 9 → ℕ) (edge : Fin 9) : ℕ :=
  length (slotSwap.symm edge)

theorem swappedLength_pos (length : Fin 9 → ℕ)
    (hLength : ∀ edge, 0 < length edge) :
    ∀ edge, 0 < swappedLength length edge := by
  intro edge
  exact hLength (slotSwap.symm edge)

@[simp] theorem swappedLength_slotSwap (length : Fin 9 → ℕ)
    (edge : Fin 9) :
    swappedLength length (slotSwap edge) = length edge := by
  unfold swappedLength
  rw [Equiv.symm_apply_apply]

@[simp] theorem swappedLength_zero (length : Fin 9 → ℕ) :
    swappedLength length 0 = length 5 := by
  rfl

@[simp] theorem swappedLength_five (length : Fin 9 → ℕ) :
    swappedLength length 5 = length 0 := by
  rfl

@[simp] theorem swappedLength_three (length : Fin 9 → ℕ) :
    swappedLength length 3 = length 8 := by
  rfl

@[simp] theorem swappedLength_eight (length : Fin 9 → ℕ) :
    swappedLength length 8 = length 3 := by
  rfl

/-- The exact occurrence-sensitive relabeling from a Core-095 subdivision to
the subdivision with swapped lengths. -/
def swapRelabeling (length : Fin 9 → ℕ)
    (hLength : ∀ edge, 0 < length edge) :
    (Spec length hLength).Relabeling
      (Spec (swappedLength length) (swappedLength_pos length hLength)) where
  coreEquiv := Fin.revPerm
  slotEquiv := slotSwap
  reversed := fun _ => true
  length_eq := by
    intro edge
    exact (swappedLength_slotSwap length edge).symm
  tail_eq := by
    intro edge
    fin_cases edge <;> rfl
  head_eq := by
    intro edge
    fin_cases edge <;> rfl

/-- Graph isomorphism implementing the normalization involution. -/
def swapGraphIso (length : Fin 9 → ℕ)
    (hLength : ∀ edge, 0 < length edge) :
    CFGraphIso (Spec length hLength).graph
      (Spec (swappedLength length) (swappedLength_pos length hLength)).graph :=
  SubdivisionGraph.Spec.graphIso _ _ (swapRelabeling length hLength)

/-- `BNExists` on the swapped normalization is exactly the original
Core-095 existence problem. -/
theorem BNExists_swapped_iff (length : Fin 9 → ℕ)
    (hLength : ∀ edge, 0 < length edge) (r d : ℤ) :
    BNExists
        (Spec (swappedLength length) (swappedLength_pos length hLength)).graph
        r d ↔
      BNExists (Spec length hLength).graph r d := by
  exact (swapGraphIso length hLength).BNExists_iff r d

/-- If the normalized chamber has existence for every positive assignment,
then Core 095 has existence for every positive assignment.  The theorem is
stated for arbitrary rank and degree so the same normalization can be reused
at the transmission/essential-row level. -/
theorem BNExists_of_normalized
    (hNormalized : ∀ (length : Fin 9 → ℕ)
      (hLength : ∀ edge, 0 < length edge),
      length 0 ≤ length 5 → BNExists (Spec length hLength).graph 1 3)
    (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge) :
    BNExists (Spec length hLength).graph 1 3 := by
  by_cases hNorm : length 0 ≤ length 5
  · exact hNormalized length hLength hNorm
  · have hSwappedNorm :
        swappedLength length 0 ≤ swappedLength length 5 := by
      simp
      omega
    exact (BNExists_swapped_iff length hLength 1 3).mp
      (hNormalized (swappedLength length)
        (swappedLength_pos length hLength) hSwappedNorm)

end LowGenus.GenusFourRow095
