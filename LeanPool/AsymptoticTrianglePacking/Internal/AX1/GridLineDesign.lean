/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **line design**: block sub-triples shared between several cluster triples

`Nibble.AX1.gridShift` (`Nibble.GridShiftUnique`) and `Nibble.AX1.gridUW_bijective`
(`Nibble.GridShiftBalance`) organise the sub-triples *inside one cluster triple*: the diagonal
labelling `(j, k) ↦ (j + k)` uses every block pair of every one of the three cluster pairs exactly
once, so one cluster triple alone already tiles its three pairs.

The assembly of `Nibble.AX1.BlockCoverResidual` (`Nibble.CoreGapBlockCover`) needs the *partial*
version of that statement, because a cluster pair `(U, W)` is in general shared by many cluster
triples `(U, W, X)`, and the rectangles used by different triples through the same pair have to be
disjoint.  The right unit of allocation is then not a single block pair but a whole **diagonal**:
writing the blocks of each cluster as `ZMod q`, the *line*

`L (a, b) = { (j, j + a, j + b) : j ∈ ZMod q }`

is a family of `q` block sub-triples whose three projections are the diagonal `a` of the pair
`(U, W)`, the diagonal `b` of `(U, X)` and the diagonal `b - a` of `(W, X)`.  The `q` diagonals
partition the `q²` block pairs of a cluster pair (`Nibble.AX1.diagIndex_bijective`), so allocating
*diagonals* to the triples through a pair is exactly the deterministic load-balancing problem that
`Nibble.AX1.balanced_bucket_le` (`Nibble.LoadBalance`) addresses, one dimension down.

* `Nibble.AX1.lineTriple` — the block sub-triple `(j, j + a, j + b)`;
* `Nibble.AX1.diagIndex_bijective` — the `q` diagonals of a cluster pair partition its `q²` block
  pairs (the partial-allocation form of `Nibble.AX1.gridUW_bijective`);
* `Nibble.AX1.lineTriple_UW_unique`, `Nibble.AX1.lineTriple_UX_unique`,
  `Nibble.AX1.lineTriple_WX_unique` — a family of lines whose labels `a`, `b` and `b - a` are
  pairwise distinct uses every block pair of every one of the three cluster pairs at most once;
* `Nibble.AX1.lineTriple_pair_disjoint` — two cluster triples through the same cluster pair that are
  given **disjoint** sets of diagonals never use a common block pair.

Everything here is at the level of block *indices*; no probability and no graph theory.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import Mathlib.Algebra.Lie.OfAssociative

/-! # GridLineDesign -/

public section

namespace Nibble.AX1

variable {q : ℕ}

/-- **One block sub-triple of the line `(a, b)`**: the blocks `j` of `U`, `j + a` of `W` and
`j + b` of `X`. -/
@[expose] def lineTriple (a b j : ZMod q) : ZMod q × ZMod q × ZMod q := (j, j + a, j + b)

@[simp] theorem lineTriple_fst (a b j : ZMod q) : (lineTriple a b j).1 = j := rfl

@[simp] theorem lineTriple_snd (a b j : ZMod q) : (lineTriple a b j).2.1 = j + a := rfl

@[simp] theorem lineTriple_thd (a b j : ZMod q) : (lineTriple a b j).2.2 = j + b := rfl

/-- **The `q` diagonals of a cluster pair partition its `q²` block pairs**: the map sending a
diagonal label `a` and a position `j` to the block pair `(j, j + a)` is a bijection.  This is the
allocation form of `Nibble.AX1.gridUW_bijective`: a cluster pair shared by several cluster triples
is exactly covered as soon as the diagonals are distributed among them. -/
theorem diagIndex_bijective :
    Function.Bijective (fun x : ZMod q × ZMod q => (x.2, x.2 + x.1)) := by
  constructor
  · rintro ⟨a, j⟩ ⟨a', j'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hj, hs⟩ := h
    subst hj
    exact Prod.ext (by simpa using add_left_cancel hs) rfl
  · rintro ⟨u, w⟩
    exact ⟨(w - u, u), by simp⟩

/-- Two block sub-triples of a family of lines with **distinct first labels** never use the same
block pair of the cluster pair `(U, W)`. -/
theorem lineTriple_UW_unique {a b a' b' j j' : ZMod q}
    (hfst : (lineTriple a b j).1 = (lineTriple a' b' j').1)
    (hsnd : (lineTriple a b j).2.1 = (lineTriple a' b' j').2.1) :
    a = a' ∧ j = j' := by
  simp only [lineTriple_fst, lineTriple_snd] at hfst hsnd
  subst hfst
  exact ⟨add_left_cancel hsnd, rfl⟩

/-- Two block sub-triples of a family of lines with **distinct second labels** never use the same
block pair of the cluster pair `(U, X)`. -/
theorem lineTriple_UX_unique {a b a' b' j j' : ZMod q}
    (hfst : (lineTriple a b j).1 = (lineTriple a' b' j').1)
    (hthd : (lineTriple a b j).2.2 = (lineTriple a' b' j').2.2) :
    b = b' ∧ j = j' := by
  simp only [lineTriple_fst, lineTriple_thd] at hfst hthd
  subst hfst
  exact ⟨add_left_cancel hthd, rfl⟩

/-- Two block sub-triples of a family of lines with **distinct differences** never use the same
block pair of the cluster pair `(W, X)`. -/
theorem lineTriple_WX_unique {a b a' b' j j' : ZMod q}
    (hsnd : (lineTriple a b j).2.1 = (lineTriple a' b' j').2.1)
    (hthd : (lineTriple a b j).2.2 = (lineTriple a' b' j').2.2) :
    b - a = b' - a' ∧ j + a = j' + a' := by
  simp only [lineTriple_snd, lineTriple_thd] at hsnd hthd
  refine ⟨?_, hsnd⟩
  have h : (j + b) - (j + a) = (j' + b') - (j' + a') := by rw [hsnd, hthd]
  rwa [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub] at h

/-- **The allocation criterion.**  Two cluster triples through the cluster pair `(U, W)` that are
allocated *disjoint* sets of diagonals never use a common block pair of that cluster pair: the
rectangles of the two triples inside `U × W` are disjoint. -/
theorem lineTriple_pair_disjoint {S T : Finset (ZMod q)} (hST : Disjoint S T)
    {a b a' b' : ZMod q} (ha : a ∈ S) (ha' : a' ∈ T) (j j' : ZMod q)
    (hfst : (lineTriple a b j).1 = (lineTriple a' b' j').1) :
    (lineTriple a b j).2.1 ≠ (lineTriple a' b' j').2.1 := by
  simp only [lineTriple_fst, lineTriple_snd] at hfst ⊢
  subst hfst
  intro hsnd
  exact (Finset.disjoint_left.mp hST ha) (add_left_cancel hsnd ▸ ha')

/-- **The diagonals of one cluster pair are exactly `q`, and each has exactly `q` block pairs.**
Together with `Nibble.AX1.diagIndex_bijective` this is the counting behind the allocation: the
diagonals allocated to the cluster triples through a pair tile that pair as soon as they partition
`ZMod q`. -/
theorem card_diag_fiber [NeZero q] (a : ZMod q) :
    (Finset.univ.image (fun j : ZMod q => ((j, j + a) : ZMod q × ZMod q))).card = q := by
  classical
  rw [Finset.card_image_of_injective _ (fun j j' h => by
    simpa using congrArg Prod.fst h)]
  simp [ZMod.card]

end Nibble.AX1
