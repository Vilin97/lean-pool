/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — splitting a cluster into vertex blocks of a prescribed size

The deterministic route to the AX1 structural residual replaces each cluster of a good triple by
vertex *sub-blocks* of prescribed sizes (`RESIDUAL.md`, §3(b)); the sizes have to be proportional to
the densities of the opposite pairs, so what is needed is a splitting of a finset into blocks of a
*prescribed* size `a`, not into a prescribed number of equal parts.  This file provides it.

* `Nibble.AX1.blockOf S a i` — the `i`-th block of `S` at block size `a`: the elements whose index
  under `Finset.equivFin` lies in `[i·a, (i+1)·a)`.
* `Nibble.AX1.blockOf_subset`, `Nibble.AX1.blockOf_disjoint`, `Nibble.AX1.card_blockOf` — the blocks
  are subsets of `S`, pairwise disjoint, and of size exactly `a` as long as `(i+1)·a ≤ |S|`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star

/-! # BlockSplit -/

public section

open Finset

namespace Nibble.AX1

variable {V : Type} [DecidableEq V]

/-- The index of `x ∈ S` under the canonical enumeration of `S`. -/
noncomputable def enumIdx (S : Finset V) (x : {y // y ∈ S}) : ℕ := (S.equivFin x).val

omit [DecidableEq V] in
theorem enumIdx_lt (S : Finset V) (x : {y // y ∈ S}) : enumIdx S x < #S := (S.equivFin x).isLt

omit [DecidableEq V] in
theorem enumIdx_injective (S : Finset V) : Function.Injective (enumIdx S) := by
  intro x y h
  have : S.equivFin x = S.equivFin y := Fin.ext h
  exact S.equivFin.injective this

/-- **The `i`-th block of `S` at block size `a`.** -/
noncomputable def blockOf (S : Finset V) (a i : ℕ) : Finset V :=
  (S.attach.filter (fun x => enumIdx S x / a = i)).image Subtype.val

theorem mem_blockOf {S : Finset V} {a i : ℕ} {v : V} :
    v ∈ blockOf S a i ↔ ∃ h : v ∈ S, enumIdx S ⟨v, h⟩ / a = i := by
  classical
  constructor
  · intro hv
    rw [blockOf, Finset.mem_image] at hv
    obtain ⟨x, hx, hxv⟩ := hv
    rw [Finset.mem_filter] at hx
    subst hxv
    exact ⟨x.2, hx.2⟩
  · rintro ⟨h, hidx⟩
    rw [blockOf, Finset.mem_image]
    exact ⟨⟨v, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hidx⟩, rfl⟩

theorem blockOf_subset (S : Finset V) (a i : ℕ) : blockOf S a i ⊆ S := by
  intro v hv
  exact (mem_blockOf.mp hv).1

/-- Distinct blocks are disjoint. -/
theorem blockOf_disjoint (S : Finset V) (a : ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (blockOf S a i) (blockOf S a j) := by
  classical
  rw [Finset.disjoint_left]
  intro v hi hj
  obtain ⟨h1, h2⟩ := mem_blockOf.mp hi
  obtain ⟨h1', h2'⟩ := mem_blockOf.mp hj
  exact hij (by rw [← h2, ← h2'])

/-- The indices lying in the `i`-th block form the interval `[i·a, (i+1)·a)`. -/
theorem filter_div_eq_range {N a i : ℕ} (ha : 0 < a) :
    {j ∈ Finset.range N | j / a = i} = Finset.Ico (i * a) (min N ((i + 1) * a)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, lt_min_iff]
  constructor
  · rintro ⟨hj, rfl⟩
    refine ⟨Nat.div_mul_le_self j a, hj, ?_⟩
    · have h1 : j % a < a := Nat.mod_lt _ ha
      have h2 := Nat.div_add_mod j a
      nlinarith only [h1, h2]
  · rintro ⟨hlo, hj, hhi⟩
    refine ⟨hj, ?_⟩
    have h1 : i ≤ j / a := (Nat.le_div_iff_mul_le ha).mpr (by
      rw [Nat.mul_comm] at hlo ⊢; assumption)
    have h2 : j / a < i + 1 := (Nat.div_lt_iff_lt_mul ha).mpr (by
      rw [Nat.mul_comm] at hhi ⊢; assumption)
    omega

/-- **A block has exactly `a` elements**, provided the whole of the interval `[i·a, (i+1)·a)` fits
inside the index range of `S`. -/
theorem card_blockOf (S : Finset V) {a i : ℕ} (ha : 0 < a) (hfit : (i + 1) * a ≤ #S) :
    #(blockOf S a i) = a := by
  classical
  rw [blockOf, Finset.card_image_of_injective _ Subtype.coe_injective]
  -- the filtered attached set is in bijection with the filtered index range
  have hbij : #(S.attach.filter (fun x => enumIdx S x / a = i))
      = #{j ∈ Finset.range #S | j / a = i} := by
    refine Finset.card_bij (fun x _ => enumIdx S x) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_range.mpr (enumIdx_lt S x), hx.2⟩
    · intro x _ y _ h
      exact enumIdx_injective S h
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      refine ⟨S.equivFin.symm ⟨j, hj.1⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_attach _ _, ?_⟩
        have : enumIdx S (S.equivFin.symm ⟨j, hj.1⟩) = j := by
          simp [enumIdx]
        rw [this]; exact hj.2
      · simp [enumIdx]
  rw [hbij, filter_div_eq_range ha, Nat.card_Ico]
  have : min #S ((i + 1) * a) = (i + 1) * a := min_eq_right hfit
  rw [this]
  have : (i + 1) * a = i * a + a := by ring
  omega

end Nibble.AX1
