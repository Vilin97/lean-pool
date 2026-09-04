/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.Perm.Basic

/-!
# Maximal chains in the Boolean lattice

A permutation `σ : Equiv.Perm (Fin m)` records the order in which elements
are inserted into a maximal chain.  The state at level `j` consists of the
first `j` elements in that order.  The lemmas below expose both the ranked
chain structure and the exact one-element insertion step needed by the mass
transport argument.
-/

open Finset

namespace Feige

/-- The level-`j` state of the maximal Boolean-lattice chain encoded by
`σ`.  Here `σ k` is the element inserted at step `k`. -/
def chainState {m : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin (m + 1)) :
    Finset (Fin m) :=
  (Finset.univ.filter fun k : Fin m ↦ k.val < j.val).map σ.toEmbedding

@[simp]
theorem mem_chainState_iff {m : ℕ} (σ : Equiv.Perm (Fin m))
    (j : Fin (m + 1)) (i : Fin m) :
    i ∈ chainState σ j ↔ (σ.symm i).val < j.val := by
  simp [chainState]

@[simp]
theorem chainState_zero {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    chainState σ 0 = ∅ := by
  ext i
  simp

@[simp]
theorem chainState_last {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    chainState σ (Fin.last m) = Finset.univ := by
  ext i
  simp [Fin.is_lt]

@[simp]
theorem card_chainState {m : ℕ} (σ : Equiv.Perm (Fin m))
    (j : Fin (m + 1)) :
    (chainState σ j).card = j.val := by
  rw [chainState, Finset.card_map, Fin.card_filter_val_lt]
  exact Nat.min_eq_right (Nat.le_of_lt_succ j.isLt)

/-- States are monotone in their level. -/
theorem chainState_mono {m : ℕ} (σ : Equiv.Perm (Fin m))
    {j k : Fin (m + 1)} (hjk : j ≤ k) :
    chainState σ j ⊆ chainState σ k := by
  intro i hi
  rw [mem_chainState_iff] at hi ⊢
  exact lt_of_lt_of_le hi hjk

/-- The element inserted at step `j` was not present before that step. -/
theorem perm_not_mem_chainState_castSucc {m : ℕ} (σ : Equiv.Perm (Fin m))
    (j : Fin m) :
    σ j ∉ chainState σ j.castSucc := by
  simp

/-- Passing from level `j` to level `j+1` inserts exactly `σ j`. -/
theorem chainState_succ {m : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    chainState σ j.succ = insert (σ j) (chainState σ j.castSucc) := by
  ext i
  simp only [mem_chainState_iff, mem_insert]
  constructor
  · intro hi
    change (σ.symm i).val < j.val + 1 at hi
    by_cases hEq : (σ.symm i).val = j.val
    · left
      apply σ.symm.injective
      exact Fin.ext (by simpa using hEq)
    · right
      change (σ.symm i).val < j.val
      omega
  · rintro (rfl | hi)
    · simp
    · change (σ.symm i).val < j.val at hi
      change (σ.symm i).val < j.val + 1
      omega

/-- Consecutive states differ by precisely the singleton containing the next
permutation element. -/
theorem chainState_succ_sdiff {m : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    chainState σ j.succ \ chainState σ j.castSucc = {σ j} := by
  rw [chainState_succ]
  ext i
  simp [perm_not_mem_chainState_castSucc σ j]

/-- Distinct levels are strictly nested. -/
theorem chainState_ssubset {m : ℕ} (σ : Equiv.Perm (Fin m))
    {j k : Fin (m + 1)} (hjk : j < k) :
    chainState σ j ⊂ chainState σ k := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨chainState_mono σ hjk.le, ?_⟩
  intro hEq
  have hcard := congrArg Finset.card hEq
  have hval : j.val = k.val := by
    simpa only [card_chainState] using hcard
  exact (ne_of_lt hjk) (Fin.ext hval)

end Feige
