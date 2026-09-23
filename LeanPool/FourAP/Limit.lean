/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/
module

public import LeanPool.FourAP.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Logic.Equiv.Defs

/-!
# A computable permutation from safe stages

This file gives the effective version of the last proof and the computability
remark in the paper “A 4AP-free permutation of the positive integers”.
Given computable increasing safe words `P n` containing all integers below
`n`, both directions of the resulting permutation are computable:

* To find the value at position `i`, read position `i` in `P (i + 1)`.
* To find the position of a value `t`, find `t` in `P (t + 1)`.

These bounds are sufficient, but not necessarily efficient.  The theorem
`permutationOfSafeStages_eq_getElem` justifies the more efficient prescription
in the paper's remark: stop at *any* stage long enough to contain the position.
Neither direction of the equivalence uses a choice of preimage.
-/

@[expose] public section

namespace FourAP

/-- The conclusion of the paper for a sequence indexed by `ℕ`: no four entries
at increasing positions form a nonconstant arithmetic progression.  Because
`IsAP4` uses equations rather than natural subtraction, decreasing arithmetic
progressions are excluded as well. -/
def SequenceAPFree (f : ℕ → ℕ) : Prop :=
  ∀ ⦃i j k l : ℕ⦄, i < j → j < k → k < l →
    ¬ IsAP4 (f i) (f j) (f k) (f l)

/-- Once one stage is a prefix of its successor, it is a prefix of every
later stage. This is the “No entry, once placed, is ever moved” assertion in
the final proof of the paper. -/
theorem safeStages_prefix (P : ℕ → List ℕ)
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1))) {m n : ℕ} (hmn : m ≤ n) :
    (P m).IsPrefix (P n) := by
  induction hmn with
  | refl => exact List.prefix_refl _
  | @step n hmn ih => exact ih.trans (hstep n)

/-- Exhaustive targets give a concrete length bound: a word containing
`0, …, n-1` has at least `n` entries. Thus every requested position can be
reached after a bounded number of stages in the computability remark. -/
theorem safeStages_length (P : ℕ → List ℕ)
    (hcover : ∀ n t, t < n → t ∈ P n) (n : ℕ) : n ≤ (P n).length := by
  have hsub : List.range n ⊆ P n := by
    intro t ht
    exact hcover n t (List.mem_range.mp ht)
  simpa using (List.nodup_range (n := n)).length_le_of_subset hsub

/-- Reading a position at the bounded stage `i + 1` gives the same value as
reading it at any stage where it is already present. This is the finite-stage
stabilization argument underlying the computational procedure in the remark. -/
theorem safeStages_value_eq_getElem (P : ℕ → List ℕ)
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n)
    (n i : ℕ) (hi : i < (P n).length) : (P (i + 1)).getD i 0 = (P n)[i] := by
  have hi' : i < (P (i + 1)).length :=
    lt_of_lt_of_le (Nat.lt_succ_self i) (safeStages_length P hcover (i + 1))
  rw [List.getD_eq_getElem _ _ hi']
  let N := max n (i + 1)
  have h₁ : (P (i + 1)).IsPrefix (P N) :=
    safeStages_prefix P hstep (Nat.le_max_right _ _)
  have h₂ : (P n).IsPrefix (P N) :=
    safeStages_prefix P hstep (Nat.le_max_left _ _)
  exact (h₁.getElem hi').trans (h₂.getElem hi).symm

/-- A value has the same position in every stage in which it occurs.
This is the inverse form of the paper's assertion that placed entries never
move, and makes the inverse permutation computable without choosing preimages. -/
theorem safeStages_idxOf_eq (P : ℕ → List ℕ)
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n)
    (n t : ℕ) (ht : t ∈ P n) : (P (t + 1)).idxOf t = (P n).idxOf t := by
  let N := max n (t + 1)
  have h₁ : (P (t + 1)).IsPrefix (P N) :=
    safeStages_prefix P hstep (Nat.le_max_right _ _)
  have h₂ : (P n).IsPrefix (P N) :=
    safeStages_prefix P hstep (Nat.le_max_left _ _)
  exact (h₁.idxOf_eq_of_mem (hcover _ _ (Nat.lt_succ_self t))).trans
    (h₂.idxOf_eq_of_mem ht).symm

/-- The actual computable equivalence constructed by the final proof of the
paper from computable safe stages. Its forward map reads a bounded stage,
and its inverse searches a bounded finite word; the proofs below verify
that these explicitly given maps are mutually inverse. -/
def permutationOfSafeStages (R : ℕ → ℕ → Prop) (P : ℕ → List ℕ)
    (hsafe : ∀ n, Safe R (P n))
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n) : ℕ ≃ ℕ where
  toFun i := (P (i + 1)).getD i 0
  invFun t := (P (t + 1)).idxOf t
  left_inv i := by
    dsimp only
    have hi : i < (P (i + 1)).length :=
      lt_of_lt_of_le (Nat.lt_succ_self i) (safeStages_length P hcover (i + 1))
    have hvalue := safeStages_value_eq_getElem P hstep hcover (i + 1) i hi
    have hmem : (P (i + 1)).getD i 0 ∈ P (i + 1) := by
      rw [hvalue]
      exact List.getElem_mem hi
    rw [safeStages_idxOf_eq P hstep hcover (i + 1) _ hmem, hvalue]
    exact (hsafe (i + 1)).1.idxOf_getElem i hi
  right_inv t := by
    have ht : t ∈ P (t + 1) := hcover _ _ (Nat.lt_succ_self t)
    have hi := List.idxOf_lt_length_iff.mpr ht
    exact (safeStages_value_eq_getElem P hstep hcover (t + 1) _ hi).trans
      (List.getElem_idxOf hi)

/-- The bounded evaluation rule for the forward permutation in the paper's
computability remark. Coverage proves that the default value is never used. -/
@[simp] theorem permutationOfSafeStages_apply
    (R : ℕ → ℕ → Prop) (P : ℕ → List ℕ)
    (hsafe : ∀ n, Safe R (P n))
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n) (i : ℕ) :
    permutationOfSafeStages R P hsafe hstep hcover i = (P (i + 1)).getD i 0 := rfl

/-- The inverse permutation is a finite search in the stage that is
guaranteed to contain the value. This strengthens the computability remark
by supplying an explicit inverse as well as an explicit forward map. -/
@[simp] theorem permutationOfSafeStages_symm_apply
    (R : ℕ → ℕ → Prop) (P : ℕ → List ℕ)
    (hsafe : ∀ n, Safe R (P n))
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n) (t : ℕ) :
    (permutationOfSafeStages R P hsafe hstep hcover).symm t = (P (t + 1)).idxOf t := rfl

/-- The precise stopping rule from the paper's remark: the value at position
`i` can be read from any finite stage whose length is greater than `i`.
Later stages have exactly the same entry at that position. -/
theorem permutationOfSafeStages_eq_getElem
    (R : ℕ → ℕ → Prop) (P : ℕ → List ℕ)
    (hsafe : ∀ n, Safe R (P n))
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n)
    (n i : ℕ) (hi : i < (P n).length) :
    permutationOfSafeStages R P hsafe hstep hcover i = (P n)[i] :=
  safeStages_value_eq_getElem P hstep hcover n i hi

/-- The finite-stage contradiction in the last proof of the paper, applied
to the explicitly computable permutation. All four entries of a hypothetical
progression lie in a single safe stage, where their positions give the same
three comparisons in the completion. -/
theorem permutationOfSafeStages_apFree
    (R : ℕ → ℕ → Prop) (P : ℕ → List ℕ)
    (hsafe : ∀ n, Safe R (P n))
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n) :
    SequenceAPFree (permutationOfSafeStages R P hsafe hstep hcover) := by
  intro i j k l hij hjk hkl hap
  let f := permutationOfSafeStages R P hsafe hstep hcover
  let N := l + 1
  have hl : l < (P N).length :=
    lt_of_lt_of_le (Nat.lt_succ_self l) (safeStages_length P hcover N)
  have hk : k < (P N).length := Nat.lt_trans hkl hl
  have hj : j < (P N).length := Nat.lt_trans hjk hk
  have hi : i < (P N).length := Nat.lt_trans hij hj
  have hidx (x : ℕ) (hx : x < (P N).length) : (P N).idxOf (f x) = x := by
    rw [permutationOfSafeStages_eq_getElem R P hsafe hstep hcover N x hx]
    exact (hsafe N).1.idxOf_getElem x hx
  apply (hsafe N).2 hap
  · apply Or.inl
    change (P N).idxOf (f i) < (P N).idxOf (f j)
    simpa only [hidx i hi, hidx j hj] using hij
  · apply Or.inl
    change (P N).idxOf (f j) < (P N).idxOf (f k)
    simpa only [hidx j hj, hidx k hk] using hjk
  · apply Or.inl
    change (P N).idxOf (f k) < (P N).idxOf (f l)
    simpa only [hidx k hk, hidx l hl] using hkl

end FourAP
