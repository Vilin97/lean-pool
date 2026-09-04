/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.BooleanChain
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Inserting a new coordinate into a maximal chain

Let `σ` encode a maximal chain on `Fin n`, and let `J : Fin (n + 1)` be an
insertion rank.  We identify the old ground set with the first `n` elements
of `Fin (n + 1)` and use `Fin.last n` for the new element.  Before rank `J`
the new chain is the lifted old chain; after rank `J` it is the lifted old
chain with the new element adjoined.  These are the two cases of the
inserted-chain construction used in the proof of Theorem 2.1.
-/

open Finset

namespace Feige

/-- Lift a Boolean-lattice state to the enlarged ground set. -/
def liftChainState {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  S.map Fin.castSuccEmb

@[simp]
theorem mem_liftChainState {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    i.castSucc ∈ liftChainState S ↔ i ∈ S := by
  simp [liftChainState]

@[simp]
theorem last_not_mem_liftChainState {n : ℕ} (S : Finset (Fin n)) :
    Fin.last n ∉ liftChainState S := by
  simp [liftChainState]

@[simp]
theorem card_liftChainState {n : ℕ} (S : Finset (Fin n)) :
    (liftChainState S).card = S.card := by
  simp [liftChainState]

/-- The enlarged permutation obtained by inserting the new element
`Fin.last n` at rank `J` and retaining the relative order `σ` on old
elements. -/
def insertChainPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (J : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' J).trans
    ((Equiv.optionCongr σ).trans (finSuccEquiv' (Fin.last n)).symm)

@[simp]
theorem insertChainPerm_at {n : ℕ} (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1)) :
    insertChainPerm σ J J = Fin.last n := by
  simp [insertChainPerm]

@[simp]
theorem insertChainPerm_succAbove {n : ℕ} (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1)) (i : Fin n) :
    insertChainPerm σ J (J.succAbove i) = (σ i).castSucc := by
  simp [insertChainPerm]

@[simp]
theorem insertChainPerm_symm_last {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (J : Fin (n + 1)) :
    (insertChainPerm σ J).symm (Fin.last n) = J := by
  apply (insertChainPerm σ J).injective
  simp

@[simp]
theorem insertChainPerm_symm_castSucc {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (J : Fin (n + 1)) (i : Fin n) :
    (insertChainPerm σ J).symm i.castSucc =
      J.succAbove (σ.symm i) := by
  apply (insertChainPerm σ J).injective
  simp

private theorem succAbove_val_lt_of_le {n : ℕ}
    (J r : Fin (n + 1)) (hr : r ≤ J) (i : Fin n) :
    (J.succAbove i).val < r.val ↔ i.val < r.val := by
  change r.val ≤ J.val at hr
  by_cases hi : i.val < J.val
  · have hi' : i.castSucc < J := hi
    rw [Fin.succAbove_of_castSucc_lt _ _ hi']
    rfl
  · have hi' : J ≤ i.castSucc := not_lt.mp hi
    rw [Fin.succAbove_of_le_castSucc _ _ hi']
    simp only [Fin.val_succ]
    omega

private theorem succAbove_val_lt_succ_of_le {n : ℕ}
    (J r : Fin (n + 1)) (hr : J ≤ r) (i : Fin n) :
    (J.succAbove i).val < r.succ.val ↔ i.val < r.val := by
  change J.val ≤ r.val at hr
  by_cases hi : i.val < J.val
  · have hi' : i.castSucc < J := hi
    rw [Fin.succAbove_of_castSucc_lt _ _ hi']
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  · have hi' : J ≤ i.castSucc := not_lt.mp hi
    rw [Fin.succAbove_of_le_castSucc _ _ hi']
    simp only [Fin.val_succ]
    omega

/-- The states of the enlarged maximal chain, written directly in the two
cases before and after the insertion rank. -/
def insertedChainState {n : ℕ} (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1)) (j : Fin (n + 2)) : Finset (Fin (n + 1)) :=
  if h : j.val ≤ J.val then
    liftChainState (chainState σ
      ⟨j.val, lt_of_le_of_lt h J.isLt⟩)
  else
    insert (Fin.last n) <| liftChainState (chainState σ
      ⟨j.val - 1, by omega⟩)

/-- The enlarged chain state before the insertion rank. -/
theorem insertedChainState_before {n : ℕ} (σ : Equiv.Perm (Fin n))
    (J r : Fin (n + 1)) (hr : r ≤ J) :
    insertedChainState σ J r.castSucc =
      liftChainState (chainState σ r) := by
  rw [insertedChainState, dite_eq_left (show r.castSucc.val ≤ J.val by exact hr)]
  congr 2

/-- After the insertion rank, the new state consists of the corresponding
old state together with the inserted element. -/
theorem insertedChainState_after {n : ℕ} (σ : Equiv.Perm (Fin n))
    (J r : Fin (n + 1)) (hr : J ≤ r) :
    insertedChainState σ J r.succ =
      insert (Fin.last n) (liftChainState (chainState σ r)) := by
  rw [insertedChainState, dite_eq_right]
  · congr 3
  · intro h
    have : r.val + 1 ≤ r.val := le_trans h hr
    omega

@[simp]
theorem insertedChainState_zero {n : ℕ} (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1)) :
    insertedChainState σ J 0 = ∅ := by
  have h0 : (0 : Fin (n + 1)) ≤ J := Fin.zero_le J
  simpa [liftChainState] using insertedChainState_before σ J 0 h0

@[simp]
theorem insertedChainState_last {n : ℕ} (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1)) :
    insertedChainState σ J (Fin.last (n + 1)) = Finset.univ := by
  have hJ : J ≤ Fin.last n := Fin.le_last J
  rw [show Fin.last (n + 1) = (Fin.last n).succ by ext; simp]
  rw [insertedChainState_after σ J (Fin.last n) hJ, chainState_last]
  ext i
  by_cases hi : i = Fin.last n
  · simp [hi]
  · obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    simp

@[simp]
theorem card_insertedChainState {n : ℕ} (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1)) (j : Fin (n + 2)) :
    (insertedChainState σ J j).card = j.val := by
  simp only [insertedChainState]
  split_ifs with h
  · simp
  · rw [Finset.card_insert_of_notMem (last_not_mem_liftChainState _)]
    simp only [card_liftChainState, card_chainState]
    omega

/-- Before the insertion rank, `insertChainPerm` produces the lifted old
chain state. -/
theorem chainState_insertChainPerm_before {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (J r : Fin (n + 1)) (hr : r ≤ J) :
    chainState (insertChainPerm σ J) r.castSucc =
      liftChainState (chainState σ r) := by
  ext x
  by_cases hx : x = Fin.last n
  · subst x
    simp only [mem_chainState_iff, insertChainPerm_symm_last,
      last_not_mem_liftChainState]
    change r.val ≤ J.val at hr
    change (J.val < r.val ↔ False)
    exact iff_false_intro (Nat.not_lt.mpr hr)
  · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hx
    simp only [mem_chainState_iff, insertChainPerm_symm_castSucc,
      mem_liftChainState]
    exact succAbove_val_lt_of_le J r hr (σ.symm i)

/-- After the insertion rank, `insertChainPerm` produces the lifted old
chain state with the new coordinate adjoined. -/
theorem chainState_insertChainPerm_after {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (J r : Fin (n + 1)) (hr : J ≤ r) :
    chainState (insertChainPerm σ J) r.succ =
      insert (Fin.last n) (liftChainState (chainState σ r)) := by
  ext x
  by_cases hx : x = Fin.last n
  · subst x
    simp only [mem_chainState_iff, insertChainPerm_symm_last,
      mem_insert, true_or]
    change J.val ≤ r.val at hr
    change (J.val < r.val + 1 ↔ True)
    exact iff_true_intro (Nat.lt_succ_of_le hr)
  · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hx
    simp only [mem_chainState_iff, insertChainPerm_symm_castSucc,
      mem_insert, Fin.castSucc_ne_last, false_or, mem_liftChainState]
    exact succAbove_val_lt_succ_of_le J r hr (σ.symm i)

/-- The direct inserted-state formula agrees at every level with the
maximal chain encoded by the inserted permutation. -/
theorem chainState_insertChainPerm_eq_insertedChainState {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (J : Fin (n + 1)) (j : Fin (n + 2)) :
    chainState (insertChainPerm σ J) j =
      insertedChainState σ J j := by
  unfold insertedChainState
  split_ifs with h
  · let r : Fin (n + 1) :=
      ⟨j.val, lt_of_le_of_lt h J.isLt⟩
    have hr : r ≤ J := h
    ext x
    by_cases hx : x = Fin.last n
    · subst x
      simp only [mem_chainState_iff, insertChainPerm_symm_last,
        last_not_mem_liftChainState]
      change (J.val < j.val ↔ False)
      exact iff_false_intro (Nat.not_lt.mpr h)
    · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hx
      simp only [mem_chainState_iff, insertChainPerm_symm_castSucc,
        mem_liftChainState]
      exact succAbove_val_lt_of_le J r hr (σ.symm i)
  · have hJj : J.val < j.val := Nat.lt_of_not_ge h
    let r : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    have hr : J ≤ r := by
      change J.val ≤ r.val
      simp only [r]
      omega
    ext x
    by_cases hx : x = Fin.last n
    · subst x
      simp only [mem_chainState_iff, insertChainPerm_symm_last,
        mem_insert, true_or]
      exact iff_true_intro hJj
    · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hx
      simp only [mem_chainState_iff, insertChainPerm_symm_castSucc,
        mem_insert, Fin.castSucc_ne_last, false_or, mem_liftChainState]
      have heq := succAbove_val_lt_succ_of_le J r hr (σ.symm i)
      simpa only [r, Fin.val_succ, Nat.sub_add_cancel (by omega : 1 ≤ j.val)]
        using heq

end Feige
