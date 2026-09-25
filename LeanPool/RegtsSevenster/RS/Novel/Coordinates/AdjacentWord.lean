/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Adjacent-transposition words for permutations of `Fin n`

Every permutation of `Fin n` is a product of adjacent transpositions.
We construct this factorisation explicitly as a list of positions
(an "adjacent-transposition word") and prove it correct.

## Strategy

We use mathlib's `Equiv.Perm.decomposeFin`, which decomposes
`σ : Perm (Fin (n+1))` into a pair `(p, σ')` with
`σ = swap 0 p * extPerm σ'` where `extPerm σ'` is the permutation
of `Fin (n+1)` that fixes `0` and acts as `σ'` on successors.

We then express `swap 0 p` as adjacent transpositions by the
conjugation identity
`swap 0 (k+2) = swap 0 (k+1) * swap (k+1) (k+2) * swap 0 (k+1)`,
and lift the recursive word for `σ'` by mapping positions through `Fin.succ`.
-/

@[expose] public section

namespace RS

open Equiv

/-- The adjacent transposition at position `i`: swaps `i` and `i + 1`. -/
def adjTrans {n : ℕ} (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap i.castSucc i.succ

/-- Permutations of `Fin 0` and `Fin 1` are trivial. -/
theorem perm_fin_one (σ : Equiv.Perm (Fin 1)) : σ = 1 :=
  Subsingleton.elim σ 1

/-! ### The 0-fixing extension -/

/-- The 0-fixing extension of a permutation: sends `0 ↦ 0` and
    `i.succ ↦ (σ i).succ`. -/
private def extPerm {n : ℕ} (σ : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  Perm.decomposeFin.symm (0, σ)

private theorem extPerm_apply_zero {n : ℕ} (σ : Perm (Fin n)) :
    extPerm σ 0 = 0 :=
  Perm.decomposeFin_symm_apply_zero 0 σ

private theorem extPerm_apply_succ {n : ℕ} (σ : Perm (Fin n)) (x : Fin n) :
    extPerm σ x.succ = (σ x).succ := by
  simp [extPerm, Perm.decomposeFin_symm_apply_succ]

private theorem extPerm_one {n : ℕ} : extPerm (1 : Perm (Fin n)) = 1 := by
  ext x; refine Fin.cases ?_ (fun i => ?_) x
  · simp [extPerm_apply_zero]
  · simp [extPerm_apply_succ]

private theorem extPerm_mul {n : ℕ} (σ τ : Perm (Fin n)) :
    extPerm (σ * τ) = extPerm σ * extPerm τ := by
  ext x; refine Fin.cases ?_ (fun i => ?_) x
  · simp [extPerm_apply_zero, Perm.mul_apply]
  · simp [extPerm_apply_succ, Perm.mul_apply]

private theorem extPerm_adjTrans {n : ℕ} (i : Fin n) :
    extPerm (adjTrans i) = adjTrans i.succ := by
  ext x; refine Fin.cases ?_ (fun j => ?_) x
  · -- x = 0: both sides map 0 to 0 since the swap is between i+1 and i+2
    simp only [extPerm_apply_zero, adjTrans, swap_apply_def,
               Fin.ext_iff, Fin.val_zero, Fin.val_castSucc, Fin.val_succ,
               apply_ite Fin.val]
    split_ifs <;> omega
  · -- x = j.succ: (adjTrans i j).succ = adjTrans i.succ j.succ
    simp only [extPerm_apply_succ, adjTrans, swap_apply_def,
               Fin.ext_iff, Fin.val_succ, Fin.val_castSucc,
               apply_ite Fin.val]
    split_ifs <;> omega

/-! ### Adjacent-transposition word for `swap 0 p` -/

/-- Auxiliary: adjacent-transposition word for `swap 0 ⟨k, _⟩` in
    `Perm (Fin (n+1))`.
    Recursion on `k`:
    - `k = 0`: identity, word = `[]`
    - `k+1`: `swap0WordAux k ++ [k] ++ swap0WordAux k`
      (conjugation: `swap 0 (k+1) = swap 0 k * swap k (k+1) * swap 0 k`) -/
private def swap0WordAux (n : ℕ) : (k : ℕ) → k ≤ n → List (Fin n)
  | 0, _ => []
  | k + 1, hk =>
    let w := swap0WordAux n k (by omega)
    w ++ [⟨k, by omega⟩] ++ w

private theorem swap0WordAux_spec (n : ℕ) :
    (k : ℕ) → (hk : k ≤ n) →
    ((swap0WordAux n k hk).map adjTrans).prod = swap (0 : Fin (n + 1)) ⟨k,
      by omega⟩
  | 0, _ => by
    simp only [swap0WordAux, List.map_nil, List.prod_nil]
    exact (swap_self _).symm
  | k + 1, hk => by
    unfold swap0WordAux
    rw [List.map_append, List.map_append, List.prod_append, List.prod_append,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        swap0WordAux_spec n k (by omega)]
    -- Goal: swap 0 ⟨k,_⟩ * adjTrans ⟨k,_⟩ * swap 0 ⟨k,_⟩ = swap 0 ⟨k+1,_⟩
    -- Convert adjTrans to swap
    have hadj : adjTrans (⟨k, by omega⟩ : Fin n) =
        swap (⟨k, by omega⟩ : Fin (n + 1)) ⟨k + 1, by omega⟩ := by
      ext ⟨_, _⟩
      simp only [adjTrans, swap_apply_def, Fin.ext_iff, Fin.val_castSucc,
                  Fin.val_succ, apply_ite Fin.val]
    rw [hadj]
    -- Now: swap 0 ⟨k,_⟩ * swap ⟨k,_⟩ ⟨k+1,_⟩ * swap 0 ⟨k,_⟩ = swap 0 ⟨k+1,_⟩
    -- Use the algebraic identity: swap y z * swap x y * swap y z = swap z x
    -- with y = ⟨k,_⟩, z = 0, x = ⟨k+1,_⟩
    rw [swap_comm (0 : Fin (n + 1)) ⟨k, by omega⟩,
        swap_comm (⟨k, by omega⟩ : Fin (n + 1)) ⟨k + 1, by omega⟩]
    rw [swap_mul_swap_mul_swap
          (show (⟨k + 1, by omega⟩ : Fin (n + 1)) ≠ ⟨k, by omega⟩ from by
            simp [Fin.ext_iff])
          (show (⟨k + 1, by omega⟩ : Fin (n + 1)) ≠ 0 from by
            simp [Fin.ext_iff]),
        swap_comm]

/-- Adjacent-transposition word for `swap 0 p`. -/
private def swap0Word {n : ℕ} (p : Fin (n + 1)) : List (Fin n) :=
  swap0WordAux n p.val (by omega)

private theorem swap0Word_spec {n : ℕ} (p : Fin (n + 1)) :
    ((swap0Word p).map adjTrans).prod = swap 0 p :=
  swap0WordAux_spec n p.val (by omega)

/-! ### The factorisation -/

/-- The factorisation `σ = swap 0 p * extPerm σ'` from `decomposeFin`. -/
private theorem decomposeFin_eq {n : ℕ} (σ : Perm (Fin (n + 1))) :
    σ = swap 0 (Perm.decomposeFin σ).1 * extPerm (Perm.decomposeFin σ).2 := by
  set p := (Perm.decomposeFin σ).1
  set σ' := (Perm.decomposeFin σ).2
  have hpair : Perm.decomposeFin σ = (p, σ') := rfl
  have h := Perm.decomposeFin.symm_apply_apply σ
  rw [hpair] at h
  rw [← h]
  ext x; refine Fin.cases ?_ (fun i => ?_) x
  · simp [Perm.decomposeFin_symm_apply_zero, Perm.mul_apply, extPerm_apply_zero,
    swap_apply_left]
  · simp only [Perm.decomposeFin_symm_apply_succ, Perm.mul_apply,
    extPerm_apply_succ]

/-- Lifting a word through `Fin.succ` corresponds to extending each
transposition. -/
private theorem map_succ_adjTrans_prod {n : ℕ} (w : List (Fin n)) :
    ((w.map Fin.succ).map adjTrans).prod = extPerm ((w.map adjTrans).prod) := by
  induction w with
  | nil => simp [extPerm_one]
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih, extPerm_mul, extPerm_adjTrans]

/-! ### The main construction -/

/-- An adjacent-transposition word for a permutation. -/
noncomputable def adjWord {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    List (Fin n) :=
  match n, σ with
  | 0, _ => []
  | _ + 1, σ =>
    let ⟨p, σ'⟩ := Perm.decomposeFin σ
    swap0Word p ++ (adjWord σ').map Fin.succ

/-- The word composes to the permutation. -/
theorem adjWord_spec {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    ((adjWord σ).map adjTrans).prod = σ := by
  match n, σ with
  | 0, σ =>
    simp only [adjWord, List.map_nil, List.prod_nil]
    exact (perm_fin_one σ).symm
  | _ + 1, σ =>
    simp only [adjWord]
    set p := (Perm.decomposeFin σ).1
    set σ' := (Perm.decomposeFin σ).2
    rw [List.map_append, List.prod_append, swap0Word_spec p,
        map_succ_adjTrans_prod, adjWord_spec σ']
    exact (decomposeFin_eq σ).symm

end RS
