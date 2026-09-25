/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ListSignPerm

/-!
# The index permutation between two orderings of the same list

Two duplicate-free lists with the same members are reorderings of
one another, and the reordering is a permutation of positions: the
*index permutation*.  Its sign is what a summand pays for being
written in one order rather than the other, so sorting signs along
any injective relabelling differ by exactly it, and the sign is
multiplicative along a chain of reorderings.
-/

@[expose] public section

namespace RS

open Equiv

/-! ### Length equality from Nodup + same membership -/

/-- Duplicate-free lists with the same members have the same
length. -/
theorem length_eq_of_nodup_mem {γ : Type*} (l₁ l₂ : List γ)
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁.length = l₂.length := by
  have hp : l₁.Perm l₂ := (List.perm_ext_iff_of_nodup h₁ h₂).mpr
    (fun x => hmem x)
  exact hp.length_eq

/-! ### The canonical index permutation -/

/-- **The index permutation** carrying one list to another with the
same members: the position in the second list of the entry at each
position of the first. -/
noncomputable def listIndexPerm {γ : Type*} [DecidableEq γ] (l₁ l₂ : List γ)
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
    (hlen : l₁.length = l₂.length) :
    Perm (Fin l₁.length) :=
  (h₁.getEquiv l₁).trans
    ((Equiv.subtypeEquivRight (fun x => hmem x)).trans
      ((h₂.getEquiv l₂).symm.trans (finCongr hlen.symm)))

/-! ### Defining property -/

/-- Its defining property: it matches the two lists entrywise. -/
theorem listIndexPerm_getElem {γ : Type*} [DecidableEq γ] (l₁ l₂ : List γ)
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
    (hlen : l₁.length = l₂.length) (i : Fin l₁.length) :
    l₂[((listIndexPerm l₁ l₂ h₁ h₂ hmem hlen) i).val]'(by
      have := ((listIndexPerm l₁ l₂ h₁ h₂ hmem hlen) i).isLt; omega) =
    l₁[i.val] := by
  simp only [listIndexPerm, Equiv.trans_apply, Equiv.subtypeEquivRight_apply]
  simp only [List.Nodup.getEquiv, finCongr]
  simp only [Equiv.coe_fn_mk]
  exact List.getElem_idxOf _

/-! ### Helper: inverse index property -/

private theorem listIndexPerm_inv_getElem {γ : Type*} [DecidableEq γ] (l₁ l₂ :
  List γ)
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
    (hlen : l₁.length = l₂.length) (j : Fin l₁.length) :
    l₁[((listIndexPerm l₁ l₂ h₁ h₂ hmem hlen).symm j).val] =
    l₂[j.val]'(by have := j.isLt; omega) := by
  have hfwd := listIndexPerm_getElem l₁ l₂ h₁ h₂ hmem hlen
      ((listIndexPerm l₁ l₂ h₁ h₂ hmem hlen).symm j)
  simp only [Equiv.apply_symm_apply] at hfwd
  exact hfwd.symm

/-! ### Main transport theorem -/

private theorem map_eq_ofFn_comp_inv {γ : Type*} [DecidableEq γ] {β : Type}
    (l₁ l₂ : List γ) (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) (hlen : l₁.length = l₂.length)
    (g : γ → β) :
    l₂.map g = List.ofFn (fun j : Fin l₁.length =>
      g (l₁[(listIndexPerm l₁ l₂ h₁ h₂ hmem hlen).symm j])) := by
  set τ := listIndexPerm l₁ l₂ h₁ h₂ hmem hlen
  have step1 : l₂.map g = List.ofFn (fun i : Fin l₂.length => g l₂[i]) :=
    (List.ofFn_getElem_eq_map l₂ g).symm
  rw [step1, List.ofFn_congr hlen.symm]
  congr 1; ext j
  have := listIndexPerm_inv_getElem l₁ l₂ h₁ h₂ hmem hlen j
  simp only [Fin.cast] at this ⊢
  exact congrArg g this.symm

/-- Sorting signs differ by the index permutation's sign, along any
injective relabelling of the entries. -/
theorem sortSign_map_listIndexPerm {γ : Type*} [DecidableEq γ] {β : Type}
  [LinearOrder β]
    (l₁ l₂ : List γ) (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) (hlen : l₁.length = l₂.length)
    (g : γ → β) (hg : (l₁.map g).Nodup) :
    sortSign (l₂.map g) =
      (Perm.sign (listIndexPerm l₁ l₂ h₁ h₂ hmem hlen) : ℤ) *
        sortSign (l₁.map g) := by
  set τ := listIndexPerm l₁ l₂ h₁ h₂ hmem hlen
  set v : Fin l₁.length → β := fun i => g l₁[i] with hv_def
  -- Injectivity of v from hg
  have hinj : Function.Injective v := by
    intro a b (hab : g l₁[a.val] = g l₁[b.val])
    have hinjon : Set.InjOn g {x | x ∈ l₁} := (List.nodup_map_iff_inj_on h₁).mp
      hg
    have heq : l₁[a.val] = l₁[b.val] :=
      hinjon (List.getElem_mem a.isLt) (List.getElem_mem b.isLt) hab
    exact Fin.ext (by exact h₁.getElem_inj_iff.mp heq)
  -- Rewrite l₁.map g as ofFn v
  have hmap₁ : l₁.map g = List.ofFn v := by
    exact (List.ofFn_getElem_eq_map l₁ g).symm
  -- Rewrite l₂.map g as ofFn (v ∘ τ.symm)
  have hmap₂ : l₂.map g = List.ofFn (fun j => v (τ.symm j)) :=
    map_eq_ofFn_comp_inv l₁ l₂ h₁ h₂ hmem hlen g
  -- Apply the main theorem
  rw [hmap₂, sortSign_ofFn_comp_perm v hinj τ.symm, Perm.sign_symm, hmap₁]

/-! ### Composition triangle (sign level) -/

/-- The index permutation composes across three lists, so its sign
is multiplicative along a chain. -/
theorem sign_listIndexPerm_trans {γ : Type*} [DecidableEq γ]
    (l₁ l₂ l₃ : List γ)
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h₃ : l₃.Nodup)
    (hmem₁₂ : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
    (hmem₂₃ : ∀ x, x ∈ l₂ ↔ x ∈ l₃)
    (hlen₁₂ : l₁.length = l₂.length)
    (hlen₂₃ : l₂.length = l₃.length) :
    Perm.sign (listIndexPerm l₁ l₃ h₁ h₃
      (fun x => (hmem₁₂ x).trans (hmem₂₃ x)) (hlen₁₂.trans hlen₂₃)) =
      Perm.sign (listIndexPerm l₁ l₂ h₁ h₂ hmem₁₂ hlen₁₂) *
        Perm.sign (listIndexPerm l₂ l₃ h₂ h₃ hmem₂₃ hlen₂₃) := by
  set τ₁₂ := listIndexPerm l₁ l₂ h₁ h₂ hmem₁₂ hlen₁₂
  set τ₂₃ := listIndexPerm l₂ l₃ h₂ h₃ hmem₂₃ hlen₂₃
  set τ₁₃ := listIndexPerm l₁ l₃ h₁ h₃ (fun x => (hmem₁₂ x).trans (hmem₂₃ x))
    (hlen₁₂.trans hlen₂₃)
  -- Conjugate τ₂₃ into Perm (Fin l₁.length)
  set τ₂₃' : Perm (Fin l₁.length) :=
    (finCongr hlen₁₂).symm.permCongr τ₂₃
  -- Show τ₁₃ = τ₂₃' * τ₁₂ by Equiv.ext
  suffices h : τ₁₃ = τ₂₃' * τ₁₂ by
    rw [h, Perm.sign_mul]
    have : Perm.sign τ₂₃' = Perm.sign τ₂₃ := Equiv.Perm.sign_permCongr _ _
    rw [this, mul_comm]
  ext i : 1
  -- Both sides, evaluated at i, give the unique index in l₁ of the
  -- element l₁[i] in l₃.
  simp only [Perm.mul_apply]
  -- Unfold τ₂₃' to finCongr ∘ τ₂₃ ∘ finCongr
  change τ₁₃ i = (finCongr hlen₁₂).symm (τ₂₃ ((finCongr hlen₁₂) (τ₁₂ i)))
  -- Both sides yield l₃[..] = l₁[i]; use nodup of l₃ to equate indices
  apply Fin.ext
  simp only [finCongr_symm]
  have hτ₁₃ := listIndexPerm_getElem l₁ l₃ h₁ h₃
    (fun x => (hmem₁₂ x).trans (hmem₂₃ x)) (hlen₁₂.trans hlen₂₃) i
  have hτ₁₂ := listIndexPerm_getElem l₁ l₂ h₁ h₂ hmem₁₂ hlen₁₂ i
  have hτ₂₃ := listIndexPerm_getElem l₂ l₃ h₂ h₃ hmem₂₃ hlen₂₃
    (finCongr hlen₁₂ (τ₁₂ i))
  -- l₃ at both positions = l₁[i]
  have h3bound₁ : (τ₁₃ i).val < l₃.length := by
    have := (τ₁₃ i).isLt; omega
  have h3bound₂ : (τ₂₃ (finCongr hlen₁₂ (τ₁₂ i))).val < l₃.length := by
    have := (τ₂₃ (finCongr hlen₁₂ (τ₁₂ i))).isLt; omega
  have hrhs : l₃[(τ₂₃ (finCongr hlen₁₂ (τ₁₂ i))).val]'h3bound₂ = l₁[i.val] := by
    rw [hτ₂₃]; exact hτ₁₂
  exact (h₃.getElem_inj_iff (hi := h3bound₁) (hj := h3bound₂)).mp
    (hτ₁₃.trans hrhs.symm)

end RS
