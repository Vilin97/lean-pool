/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.AdjacentWord
public import LeanPool.RegtsSevenster.RS.Common.ListSign

/-!
# Sorting signs under a permutation of positions

Reordering a duplicate-free tuple multiplies the sorting sign of the
list it spells by the sign of the reordering.  The proof reduces to
adjacent transpositions, where the two lists differ by one swap and
the sorting signs by one factor of `−1`.
-/

@[expose] public section

namespace RS

open Equiv

/-! ### Splitting `List.ofFn v` at two adjacent positions -/

private theorem ofFn_split {α : Type} {m : ℕ} (v : Fin (m + 1) → α) (i : Fin m)
  :
    List.ofFn v =
      (List.ofFn v).take i.val ++ v i.castSucc :: v i.succ ::
        (List.ofFn v).drop (i.val + 2) := by
  have hi : i.val < (List.ofFn v).length := by simp [List.length_ofFn]
  have hi1 : i.val + 1 < (List.ofFn v).length := by simp [List.length_ofFn]
  have hg1 : (List.ofFn v)[i.val] = v i.castSucc :=
    by rw [List.getElem_ofFn]; congr 1
  have hg2 : (List.ofFn v)[i.val + 1] = v i.succ :=
    by rw [List.getElem_ofFn]; congr 1
  conv_lhs => rw [show List.ofFn v = (List.ofFn v).take i.val ++ (List.ofFn
    v).drop i.val from
    (List.take_append_drop i.val (List.ofFn v)).symm]
  congr 1
  rw [List.drop_eq_getElem_cons hi, hg1, List.drop_eq_getElem_cons hi1, hg2]

/-! ### `ofFn (v ∘ adjTrans i)` is the swapped split -/

private theorem ofFn_adjTrans_split {α : Type} {m : ℕ} (v : Fin (m + 1) → α) (i
  : Fin m) :
    List.ofFn (v ∘ ⇑(adjTrans i)) =
      (List.ofFn v).take i.val ++ v i.succ :: v i.castSucc ::
        (List.ofFn v).drop (i.val + 2) := by
  have htlen : ((List.ofFn v).take i.val).length = i.val := by
    simp [List.length_take, List.length_ofFn]; omega
  have fix {k : ℕ} (hk : k < m + 1) (hki : k ≠ i.val) (hki2 : k ≠ i.val + 1) :
      adjTrans i (⟨k, hk⟩ : Fin (m + 1)) = ⟨k, hk⟩ := by
    simp only [adjTrans, Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  have at_i (hk : i.val < m + 1) :
      adjTrans i (⟨i.val, hk⟩ : Fin (m + 1)) = i.succ := by
    have : (⟨i.val, hk⟩ : Fin (m + 1)) = i.castSucc := Fin.ext
      (by simp [Fin.val_castSucc])
    rw [this]; exact show adjTrans i i.castSucc = i.succ from by
      simp [adjTrans, Equiv.swap_apply_left]
  have at_i1 (hk : i.val + 1 < m + 1) :
      adjTrans i (⟨i.val + 1, hk⟩ : Fin (m + 1)) = i.castSucc := by
    have : (⟨i.val + 1, hk⟩ : Fin (m + 1)) = i.succ := Fin.ext
      (by simp [Fin.val_succ])
    rw [this]; exact show adjTrans i i.succ = i.castSucc from by
      simp [adjTrans, Equiv.swap_apply_right]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons,
               List.length_take, List.length_drop]; omega
  · intro k hk1 hk2
    simp only [List.length_ofFn] at hk1
    rw [List.getElem_ofFn]
    simp only [Function.comp]
    by_cases hk_lt : k < i.val
    · rw [fix hk1 (by omega) (by omega)]
      rw [List.getElem_append_left (by rw [htlen]; exact hk_lt)]
      rw [List.getElem_take, List.getElem_ofFn]
    · by_cases hk_eq : k = i.val
      · subst hk_eq
        rw [at_i hk1]
        rw [List.getElem_append_right (by rw [htlen])]
        simp only [htlen, Nat.sub_self]; rfl
      · by_cases hk_eq2 : k = i.val + 1
        · subst hk_eq2
          rw [at_i1 hk1]
          rw [List.getElem_append_right (by rw [htlen]; omega)]
          simp only [htlen, show i.val + 1 - i.val = 1 from by omega]; rfl
        · have hk_gt : k > i.val + 1 := by omega
          rw [fix hk1 (by omega) hk_eq2]
          rw [List.getElem_append_right (by rw [htlen]; omega)]
          simp only [htlen]
          have h1 : ¬(k - i.val = 0) := by omega
          have h2 : ¬(k - i.val - 1 = 0) := by omega
          rw [List.getElem_cons]
          simp only [h1, ↓reduceDIte]
          rw [List.getElem_cons]
          simp only [h2, ↓reduceDIte]
          rw [List.getElem_drop, List.getElem_ofFn]
          have heq : k = i.val + 2 + (k - i.val - 1 - 1) := by omega
          congr 1; exact Fin.ext heq

/-! ### The swap step -/

private theorem sortSign_ofFn_adjTrans {α : Type} [LinearOrder α] {m : ℕ}
    (i : Fin m) (v : Fin (m + 1) → α) (hinj : Function.Injective v) :
    sortSign (List.ofFn (v ∘ ⇑(adjTrans i))) = -sortSign (List.ofFn v) := by
  have hab : v i.castSucc ≠ v i.succ := by
    intro h; exact absurd (hinj h) (Fin.castSucc_lt_succ.ne)
  rw [ofFn_adjTrans_split v i]
  conv_rhs => rw [ofFn_split v i]
  exact sortSign_swap_adjacent _ _ hab

/-! ### The word lemma: induction on an adjacent-transposition word -/

private theorem word_sortSign {α : Type} [LinearOrder α] {m : ℕ}
    (w : List (Fin m)) (v : Fin (m + 1) → α) (hinj : Function.Injective v) :
    sortSign (List.ofFn (fun i => v ((w.map adjTrans).prod i))) =
      (-1 : ℤ) ^ w.length * sortSign (List.ofFn v) := by
  induction w generalizing v with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Perm.one_apply, List.length_nil,
      pow_zero, one_mul]
  | cons j w ih =>
    simp only [List.map_cons, List.prod_cons, Perm.mul_apply, List.length_cons]
    have hinj' : Function.Injective (v ∘ ⇑(adjTrans j)) := hinj.comp
      (adjTrans j).injective
    have hfun : (fun i => v ((adjTrans j) ((w.map adjTrans).prod i))) =
                (fun i => (v ∘ ⇑(adjTrans j)) ((w.map adjTrans).prod i)) := by
      ext; rfl
    rw [hfun, ih (v ∘ ⇑(adjTrans j)) hinj', sortSign_ofFn_adjTrans j v hinj,
      pow_succ]
    ring

/-! ### Sign of adjacent transposition words -/

private theorem sign_adjTrans {m : ℕ} (i : Fin m) :
    Perm.sign (adjTrans i) = -1 := by
  unfold adjTrans; exact Perm.sign_swap (Fin.castSucc_lt_succ.ne)

private theorem sign_adjWord_prod {m : ℕ} (w : List (Fin m)) :
    (Perm.sign ((w.map adjTrans).prod) : ℤ) = (-1 : ℤ) ^ w.length := by
  induction w with
  | nil => simp [Perm.sign_one, Units.val_one]
  | cons j w ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons,
               Perm.sign_mul, Units.val_mul, sign_adjTrans, pow_succ]
    rw [ih]; simp [Units.val_neg, Units.val_one]

/-! ### Main theorem -/

/-- Permuting a duplicate-free tuple multiplies its sorting sign by
the permutation's sign. -/
theorem sortSign_ofFn_comp_perm {α : Type} [LinearOrder α] {n : ℕ}
    (v : Fin n → α) (hinj : Function.Injective v)
    (τ : Perm (Fin n)) :
    sortSign (List.ofFn (fun i => v (τ i))) =
      (Perm.sign τ : ℤ) * sortSign (List.ofFn v) := by
  match n with
  | 0 =>
    have : τ = 1 := Subsingleton.elim τ 1
    simp [this, Perm.sign_one, Units.val_one, sortSign]
  | m + 1 =>
    have hw := adjWord_spec τ
    have heq : (fun i => v (τ i)) =
               (fun i => v (((adjWord τ).map adjTrans).prod i)) := by
      ext x; rw [hw]
    rw [heq, word_sortSign (adjWord τ) v hinj, ← sign_adjWord_prod (adjWord τ),
      hw]

end RS
