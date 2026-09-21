/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.PrimeSymmetry

/-!
# Barred permutations for the planar Fox--Neuwirth stratification

A barred permutation records a total vertical order of the labels and cuts that divide this order
into consecutive blocks.  A block represents labels with equal first coordinate; the block order
is their strict first-coordinate order and the permutation order inside a block is their strict
second-coordinate order.

The dual Fox--Neuwirth cell has dimension `p - blockCount`.  Thus one-block symbols index top
dual cells of dimension `p - 1`, while the all-singleton symbols index vertices.
-/

namespace NRR

open scoped BigOperators

variable {p : ℕ}

/-- Exact finite combinatorial symbol for a planar Fox--Neuwirth stratum.

`rank i` is the position of label `i` in the displayed permutation.  A member `k` of `bars`
places a bar after position `k`. -/
structure BarredPermutation (p : ℕ) where
  rank : Equiv.Perm (Fin p)
  bars : Finset (Fin (p - 1))
  deriving Fintype, DecidableEq

namespace BarredPermutation

@[ext] theorem ext
    {a b : BarredPermutation p}
    (hrank : a.rank = b.rank)
    (hbars : a.bars = b.bars) :
    a = b := by
  cases a
  cases b
  simp_all

/-- Number of bars strictly before the rank of a label.  This is the zero-based block number. -/
def blockIndex (c : BarredPermutation p) (i : Fin p) : ℕ :=
  (c.bars.filter fun k => k.1 < (c.rank i).1).card

/-- Two labels lie on the same vertical line in the represented stratum. -/
def SameBlock (c : BarredPermutation p) (i j : Fin p) : Prop :=
  c.blockIndex i = c.blockIndex j

instance (c : BarredPermutation p) : DecidableRel c.SameBlock :=
  fun i j => inferInstanceAs (Decidable (c.blockIndex i = c.blockIndex j))

/-- Number of nonempty consecutive blocks.  There are no blocks for `p = 0`. -/
def blockCount (c : BarredPermutation p) : ℕ :=
  if p = 0 then 0 else c.bars.card + 1

/-- Dimension in the dual Fox--Neuwirth complex. -/
def dualDimension (c : BarredPermutation p) : ℕ :=
  p - c.blockCount

/-- One-block symbols are the top-dimensional dual cells. -/
def IsTop (c : BarredPermutation p) : Prop :=
  c.bars = ∅

instance isTopDecidable (c : BarredPermutation p) : Decidable c.IsTop := by
  unfold IsTop
  infer_instance

/-- All-singleton symbols are vertices of the dual complex. -/
def IsVertex (c : BarredPermutation p) : Prop :=
  c.bars = Finset.univ

/-- Relabel a symbol by precomposition with `σ.symm`, matching `Config.relabel`. -/
def relabel (σ : Equiv.Perm (Fin p))
    (c : BarredPermutation p) : BarredPermutation p where
  rank := σ.symm.trans c.rank
  bars := c.bars

@[simp] theorem relabel_rank
    (σ : Equiv.Perm (Fin p)) (c : BarredPermutation p) (i : Fin p) :
    (c.relabel σ).rank i = c.rank (σ.symm i) :=
  rfl

@[simp] theorem relabel_bars
    (σ : Equiv.Perm (Fin p)) (c : BarredPermutation p) :
    (c.relabel σ).bars = c.bars :=
  rfl

@[simp] theorem relabel_one (c : BarredPermutation p) :
    c.relabel 1 = c := by
  apply BarredPermutation.ext
  · ext i
    have hi : (1 : Equiv.Perm (Fin p)).symm i = i :=
      (1 : Equiv.Perm (Fin p)).symm_apply_apply i
    exact congrArg (fun j => (c.rank j : ℕ)) hi
  · rfl

 theorem relabel_mul
    (σ τ : Equiv.Perm (Fin p)) (c : BarredPermutation p) :
    c.relabel (σ * τ) = (c.relabel τ).relabel σ := by
  apply BarredPermutation.ext
  · ext i
    rfl
  · rfl

@[simp] theorem blockIndex_relabel
    (σ : Equiv.Perm (Fin p)) (c : BarredPermutation p) (i : Fin p) :
    (c.relabel σ).blockIndex i = c.blockIndex (σ.symm i) := by
  rfl

@[simp] theorem sameBlock_relabel
    (σ : Equiv.Perm (Fin p)) (c : BarredPermutation p) (i j : Fin p) :
    (c.relabel σ).SameBlock i j ↔
      c.SameBlock (σ.symm i) (σ.symm j) := by
  rfl

@[simp] theorem blockCount_relabel
    (σ : Equiv.Perm (Fin p)) (c : BarredPermutation p) :
    (c.relabel σ).blockCount = c.blockCount := by
  simp [blockCount]

@[simp] theorem dualDimension_relabel
    (σ : Equiv.Perm (Fin p)) (c : BarredPermutation p) :
    (c.relabel σ).dualDimension = c.dualDimension := by
  simp [dualDimension]

@[simp] theorem isTop_relabel
    (σ : Equiv.Perm (Fin p)) (c : BarredPermutation p) :
    (c.relabel σ).IsTop ↔ c.IsTop := by
  simp [IsTop]

@[simp] theorem isVertex_relabel
    (σ : Equiv.Perm (Fin p)) (c : BarredPermutation p) :
    (c.relabel σ).IsVertex ↔ c.IsVertex := by
  simp [IsVertex]

/-- Face relation in the dual complex.

`a.IsFace b` means that the stratum symbol `a` is a refinement of `b`: ordered blocks of `a` may
be merged, but never reordered, and the vertical order inside every block of `a` is preserved.
The final conjunct records the corresponding dual-dimension inequality explicitly. -/
def IsFace (a b : BarredPermutation p) : Prop :=
  (∀ i j, a.blockIndex i ≤ a.blockIndex j →
      b.blockIndex i ≤ b.blockIndex j) ∧
  (∀ i j, a.SameBlock i j →
      ((a.rank i).1 < (a.rank j).1 ↔
        (b.rank i).1 < (b.rank j).1)) ∧
  a.dualDimension ≤ b.dualDimension

 theorem isFace_refl (a : BarredPermutation p) :
    a.IsFace a := by
  refine ⟨?_, ?_, le_rfl⟩
  · intro i j hij
    exact hij
  · intro i j hij
    exact Iff.rfl

 theorem isFace_trans
    {a b c : BarredPermutation p}
    (hab : a.IsFace b) (hbc : b.IsFace c) :
    a.IsFace c := by
  refine ⟨?_, ?_, hab.2.2.trans hbc.2.2⟩
  · intro i j hij
    exact hbc.1 i j (hab.1 i j hij)
  · intro i j hij
    have hbij : b.SameBlock i j := by
      apply Nat.le_antisymm
      · exact hab.1 i j (Nat.le_of_eq hij)
      · exact hab.1 j i (Nat.le_of_eq hij.symm)
    exact (hab.2.1 i j hij).trans (hbc.2.1 i j hbij)

 theorem isFace_relabel
    {a b : BarredPermutation p}
    (h : a.IsFace b) (σ : Equiv.Perm (Fin p)) :
    (a.relabel σ).IsFace (b.relabel σ) := by
  refine ⟨?_, ?_, by simpa using h.2.2⟩
  · intro i j hij
    exact h.1 (σ.symm i) (σ.symm j) hij
  · intro i j hij
    exact h.2.1 (σ.symm i) (σ.symm j) hij

/-- Codimension-one face relation. -/
def IsFacet (a b : BarredPermutation p) : Prop :=
  a.IsFace b ∧ a.dualDimension + 1 = b.dualDimension

noncomputable instance isFaceDecidable (a b : BarredPermutation p) :
    Decidable (a.IsFace b) := Classical.dec _

noncomputable instance isFacetDecidable (a b : BarredPermutation p) :
    Decidable (a.IsFacet b) := Classical.dec _

 theorem isFacet_relabel
    {a b : BarredPermutation p}
    (h : a.IsFacet b) (σ : Equiv.Perm (Fin p)) :
    (a.relabel σ).IsFacet (b.relabel σ) := by
  exact ⟨isFace_relabel h.1 σ, by simpa using h.2⟩

 theorem bars_card_le (c : BarredPermutation p) :
    c.bars.card ≤ p - 1 := by
  calc
    c.bars.card ≤ (Finset.univ : Finset (Fin (p - 1))).card :=
      Finset.card_le_card (Finset.subset_univ c.bars)
    _ = p - 1 := by simp

 theorem blockCount_eq
    (c : BarredPermutation p) (hp0 : 0 < p) :
    c.blockCount = c.bars.card + 1 := by
  simp [blockCount, Nat.ne_of_gt hp0]

 theorem dualDimension_eq
    (c : BarredPermutation p) (hp0 : 0 < p) :
    c.dualDimension = (p - 1) - c.bars.card := by
  rw [dualDimension, blockCount_eq c hp0]
  omega

 theorem dualDimension_top
    (c : BarredPermutation p) (hp0 : 0 < p)
    (hc : c.IsTop) :
    c.dualDimension = p - 1 := by
  rw [dualDimension_eq c hp0]
  simp [IsTop] at hc
  simp [hc]

 theorem dualDimension_vertex
    (c : BarredPermutation p) (hp0 : 0 < p)
    (hc : c.IsVertex) :
    c.dualDimension = 0 := by
  rw [dualDimension_eq c hp0]
  simp [IsVertex] at hc
  simp [hc]

/-- The prime symmetry action on barred permutations. -/
instance primeSymmetryAction (hp : Nat.Prime p) :
    MulAction (PrimeSymmetry hp) (BarredPermutation p) where
  smul g c := c.relabel (PrimeSymmetry.toPerm hp g)
  one_smul c := by
    change c.relabel (PrimeSymmetry.toPerm hp 1) = c
    rw [map_one, relabel_one]
  mul_smul g h c := by
    change c.relabel (PrimeSymmetry.toPerm hp (g * h)) =
      (c.relabel (PrimeSymmetry.toPerm hp h)).relabel (PrimeSymmetry.toPerm hp g)
    rw [map_mul]
    exact relabel_mul (PrimeSymmetry.toPerm hp g)
      (PrimeSymmetry.toPerm hp h) c

@[simp] theorem prime_smul_def
    (hp : Nat.Prime p) (g : PrimeSymmetry hp)
    (c : BarredPermutation p) :
    g • c = c.relabel (PrimeSymmetry.toPerm hp g) :=
  rfl

end BarredPermutation

end NRR
