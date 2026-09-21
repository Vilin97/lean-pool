/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.Canonization
public import LeanPool.DensityHalesJewett.DensityHalesJewett.FiniteUnions
public import LeanPool.DensityHalesJewett.DensityHalesJewett.Subspace
public import Mathlib.Order.Lattice.Nat
import Mathlib.Combinatorics.Pigeonhole

import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The Graham--Rothschild theorem for combinatorial lines

The finite-unions focusing argument, block canonization, and the line-coloring form of the
Graham--Rothschild theorem needed by the density proof.

Following `graham_rothschild_lines_from_mhj.tex`, the support canonization lemma
`Canonization.exists_canonical_of_le` reduces the colour of a line of a large subspace to the
support of its parameter word, and `FiniteUnions.exists_monochromaticUnions` produces pairwise
disjoint blocks of parameters all of whose nonempty unions are equally coloured.  Reading those
blocks as the variable directions of a subspace proves the theorem.

Mathlib's `Combinatorics.Subspace` indexes variable directions by an arbitrary function on
coordinates rather than by consecutive blocks of coordinates, so the block convention of the
write-up, and with it the finite Ramsey theorem used to arrange the blocks in increasing order,
is not needed here: pairwise disjoint blocks already describe a subspace.
-/

@[expose] public section

open Finset
open Combinatorics

namespace DensityHalesJewett

namespace GrahamRothschild

open Subspace

variable {α ι C : Type*} [DecidableEq ι] {m n : ℕ}

/-- The subspace whose variable directions are pairwise disjoint nonempty blocks of coordinates,
all remaining coordinates carrying a fixed letter. -/
noncomputable def ofBlocks (a₀ : α) (E : Fin m → Finset ι) (hE : ∀ j, (E j).Nonempty)
    (hEE : ∀ i j, i ≠ j → Disjoint (E i) (E j)) : Combinatorics.Subspace (Fin m) α ι where
  idxFun i := if h : ∃ j, i ∈ E j then Sum.inr h.choose else Sum.inl a₀
  proper e := by
    obtain ⟨i, hi⟩ := hE e
    refine ⟨i, ?_⟩
    rw [dite_eq_left ⟨e, hi⟩]
    apply congrArg Sum.inr
    by_contra hne
    exact Finset.disjoint_left.1 (hEE _ _ hne) (Exists.choose_spec (⟨e, hi⟩ : ∃ j, i ∈ E j)) hi

variable {a₀ : α} {E : Fin m → Finset ι} {hE : ∀ j, (E j).Nonempty}
  {hEE : ∀ i j, i ≠ j → Disjoint (E i) (E j)}

lemma ofBlocks_idxFun_of_mem {i : ι} {j : Fin m} (hij : i ∈ E j) :
    (ofBlocks a₀ E hE hEE).idxFun i = Sum.inr j := by
  simp only [ofBlocks]
  rw [dite_eq_left ⟨j, hij⟩]
  apply congrArg Sum.inr
  by_contra hne
  exact Finset.disjoint_left.1 (hEE _ _ hne) (Exists.choose_spec (⟨j, hij⟩ : ∃ j, i ∈ E j)) hij

lemma ofBlocks_idxFun_of_notMem {i : ι} (hi : ∀ j, i ∉ E j) :
    (ofBlocks a₀ E hE hEE).idxFun i = Sum.inl a₀ := by
  simp only [ofBlocks]
  rw [dite_eq_right (by simpa using hi)]

/-- The support of a word substituted into `ofBlocks` is the union of the blocks indexed by the
support of that word. -/
lemma sameSupport_wordMap_ofBlocks (x : Fin m → Option α) (J : Finset (Fin m))
    (hJ : ∀ j, j ∈ J ↔ x j = none) :
    SameSupport (wordMap (ofBlocks a₀ E hE hEE) x)
      fun i ↦ if i ∈ J.biUnion E then none else some a₀ := by
  have hite : ∀ i : ι, ((if i ∈ J.biUnion E then none else some a₀ : Option α) = none)
      ↔ i ∈ J.biUnion E := by
    intro i
    split <;> simp [*]
  intro i
  rw [wordMap]
  by_cases h : ∃ j, i ∈ E j
  · obtain ⟨j, hj⟩ := h
    rw [ofBlocks_idxFun_of_mem hj, Sum.elim_inr, ← hJ j, hite i, Finset.mem_biUnion]
    constructor
    · intro hjJ
      exact ⟨j, hjJ, hj⟩
    · rintro ⟨j', hj'J, hij'⟩
      by_contra hne
      refine Finset.disjoint_left.1 (hEE j j' ?_) hj hij'
      intro hjj'
      apply hne
      rw [hjj']
      exact hj'J
  · rw [not_exists] at h
    rw [ofBlocks_idxFun_of_notMem h, Sum.elim_inl, hite i]
    simp [Finset.mem_biUnion, h]

/-- Extend a colouring of the lines of a cube to a colouring of all words over `Option α`. -/
private noncomputable def extend [Nonempty C] (χ : Combinatorics.Line α (Fin n) → C)
    (w : Fin n → Option α) : C :=
  if h : ∃ i, w i = none then χ ⟨w, h⟩ else Classical.arbitrary C

private lemma extend_idxFun [Nonempty C] (χ : Combinatorics.Line α (Fin n) → C)
    (l : Combinatorics.Line α (Fin n)) : extend χ l.idxFun = χ l :=
  dite_eq_left l.proper

/-- **Graham--Rothschild for lines**: beyond a dimension depending only on the alphabet, the
number of colours and `m`, every colouring of the lines of a cube is constant on the lines of some
`m`-dimensional combinatorial subspace. -/
lemma exists_lines (α : Type*) [Finite α] [Nonempty α] (C : Type*) [Finite C] [Nonempty C]
    (m : ℕ) : ∃ N : ℕ, ∀ n, N ≤ n → ∀ χ : Combinatorics.Line α (Fin n) → C,
      ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
        ∃ c, ∀ l : Combinatorics.Line α (Fin m), χ (composeLine V l) = c := by
  classical
  obtain ⟨L, hL⟩ := FiniteUnions.exists_monochromaticUnions C m
  obtain ⟨N, hN⟩ := Canonization.exists_canonical_of_le α C L
  refine ⟨N, ?_⟩
  intro n hn χ
  obtain ⟨V, hV⟩ := hN n hn (extend χ)
  obtain ⟨E, hE, hEE, c, hc⟩ := hL fun I ↦
    extend χ (wordMap V fun i ↦ if i ∈ I then none else some (Classical.arbitrary α))
  refine ⟨compose V (ofBlocks (Classical.arbitrary α) E hE hEE), c, ?_⟩
  intro l
  rw [← extend_idxFun χ, composeLine_idxFun, wordMap_compose,
    hV _ _ (sameSupport_wordMap_ofBlocks l.idxFun {j | l.idxFun j = none} fun j ↦ by simp)]
  apply hc
  obtain ⟨j, hj⟩ := l.proper
  exact ⟨j, by simpa using hj⟩

/-- The Graham--Rothschild property for `k` letters, `r` colours and dimension `m`, in a cube of
dimension `N`. -/
def IsLineBound (k r m N : ℕ) : Prop :=
  ∀ χ : Combinatorics.Line (Fin k) (Fin N) → Fin r,
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin N),
      ∃ c, ∀ l : Combinatorics.Line (Fin k) (Fin m), χ (composeLine V l) = c

/-- A Graham--Rothschild dimension for colorings of combinatorial lines. -/
noncomputable def bound (alphabet colors dimension : ℕ) : ℕ :=
  sInf {N | ∀ n, N ≤ n → IsLineBound alphabet colors dimension n}

private lemma isLineBound_of_bound_le {k r m : ℕ} (hk : 1 ≤ k) (hr : 1 ≤ r) (n : ℕ)
    (hn : bound k r m ≤ n) : IsLineBound k r m n := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  exact Nat.sInf_mem (exists_lines (Fin k) (Fin r) m) n hn

/-- Transporting a subspace along an alphabet equivalence transports the lines it carries. -/
private lemma composeLine_reindex {β : Type*} (e : α ≃ β)
    (V : Combinatorics.Subspace (Fin m) β (Fin n)) (l : Combinatorics.Line α (Fin m)) :
    composeLine (V.reindex (Equiv.refl _) e.symm (Equiv.refl _)) l
      = Combinatorics.Line.map e.symm (composeLine V (l.map e)) := by
  apply Combinatorics.Line.ext
  funext i
  cases h : V.idxFun i <;>
    simp [composeLine, Combinatorics.Subspace.reindex, Combinatorics.Line.map, h]

/-- The line case of the Graham--Rothschild theorem. -/
lemma lines (α C : Type*) [Fintype α] [Nontrivial α] [Fintype C] [Nonempty C]
    [DecidableEq α] (m n : ℕ)
    (hn : bound (Fintype.card α) (Fintype.card C) m ≤ n)
    (χ : Combinatorics.Line α (Fin n) → C) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      ∃ c, ∀ l : Combinatorics.Line α (Fin m), χ (Subspace.mapLine V l) = c := by
  obtain ⟨V, c, hc⟩ :=
    isLineBound_of_bound_le (k := Fintype.card α) (r := Fintype.card C) (m := m)
      (le_trans one_le_two Fintype.one_lt_card) Fintype.card_pos n hn
      fun l ↦ Fintype.equivFin C (χ (l.map (Fintype.equivFin α).symm))
  refine ⟨V.reindex (Equiv.refl _) (Fintype.equivFin α).symm (Equiv.refl _),
    (Fintype.equivFin C).symm c, ?_⟩
  intro l
  rw [Subspace.mapLine_eq_composeLine, composeLine_reindex, ← hc (l.map (Fintype.equivFin α)),
    Equiv.symm_apply_apply]

/-- The two-color form of Graham--Rothschild used by the density argument. -/
lemma lines_twoColor (α : Type*) [Fintype α] [Nontrivial α] [DecidableEq α]
    (m n : ℕ)
    (hn : bound (Fintype.card α) 2 m ≤ n)
    (L : Finset (Combinatorics.Line α (Fin n))) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      (∀ l : Combinatorics.Line α (Fin m), Subspace.mapLine V l ∈ L) ∨
        (∀ l : Combinatorics.Line α (Fin m), Subspace.mapLine V l ∉ L) := by
  classical
  obtain ⟨V, c, hc⟩ :=
    lines α (Fin 2) m n hn fun l ↦ if l ∈ L then 0 else 1
  obtain rfl | ⟨c, rfl⟩ := c.eq_zero_or_eq_succ
  · refine ⟨V, ?_⟩
    left
    intro l
    by_contra h
    simpa [h] using hc l
  · refine ⟨V, ?_⟩
    right
    rw [Fin.eq_zero c] at hc
    intro l h
    simpa [h] using hc l

end GrahamRothschild
end DensityHalesJewett
