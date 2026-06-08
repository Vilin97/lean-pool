/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Maximum absolute value of a tuple of integers
-/


open Finset

variable {n : ℕ}

/-- The maximum absolute value of a tuple of integers (0 if empty). -/
def maxAbs (a : Fin n → ℤ) : ℕ :=
  univ.sup fun i ↦ (a i).natAbs

lemma maxAbs_zero {a : Fin 0 → ℤ} : maxAbs a = 0 := by simp [maxAbs]

lemma maxAbs_one {a : Fin 1 → ℤ} : maxAbs a = (a 0).natAbs := by simp [maxAbs]

variable {a : Fin n → ℤ}

lemma maxAbs_eq_foldr : maxAbs a = (List.ofFn fun i ↦ (a i).natAbs).foldr max 0 := by
  rw [← Nat.bot_eq_zero, List.foldr_sup_eq_sup_toFinset, maxAbs,
    ← (fun i ↦ (a i).natAbs).id_comp, ← sup_image]
  congr; ext; simp

lemma maxAbs_eq_of_forall_le {i : Fin n} (hi : ∀ j, (a j).natAbs ≤ (a i).natAbs) :
    maxAbs a = (a i).natAbs :=
  le_antisymm (Finset.sup_le (by simp_all)) (le_sup (f := fun i ↦ (a i).natAbs) (mem_univ _))
