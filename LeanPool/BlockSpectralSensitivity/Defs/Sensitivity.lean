/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Defs.Cube

/-!
# Sensitivity and block sensitivity

The measures of Section 1.1 of `bs_lambda.txt`:

* `sensCoords f x` is the set of coordinates sensitive at `x`, and `sensAt f x` is `s(f,x)`,
  its cardinality;
* `sens f` is `s(f)`;
* `bsAt f x` is `bs(f,x)`, the largest number of pairwise disjoint sensitive blocks at `x`;
* `bs f` is `bs(f)`.

`bsAt` is defined as a supremum over `ℕ` of the set of cardinalities of admissible
families; the set is bounded above, so `le_bsAt_of_family` gives the lower bounds we need.
`card_le_bs_of_blocks` packages the usual way to apply it: from an indexed family of
nonempty, pairwise disjoint sensitive blocks.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

/-! ## A missing `Set` lemma

Mathlib has the `iSupIndep` analogue (`iSupIndep.injOn`) but not the `PairwiseDisjoint` one;
it belongs next to `Set.injOn_iff_pairwise_ne` in `Mathlib/Data/Set/Pairwise/Basic.lean`. -/

/-- A pairwise disjoint family of nonzero elements is injective on its index set. -/
theorem Set.PairwiseDisjoint.injOn {ι α : Type*} [Lattice α] [OrderBot α] {f : ι → α}
    {s : Set ι} (h : s.PairwiseDisjoint f) (hne : ∀ i ∈ s, f i ≠ ⊥) : s.InjOn f := by
  intro i hi j hj hij
  by_contra hij'
  have hd : Disjoint (f i) (f j) := h hi hj hij'
  rw [← hij] at hd
  exact hne i hi (disjoint_self.1 hd)

namespace BSLambda

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A coordinate `v` is sensitive for `f` at `x` when flipping it changes the value. -/
def SensitiveCoord (f : Input V → Bool) (x : Input V) (v : V) : Prop :=
  f (flipSet x {v}) ≠ f x

instance (f : Input V → Bool) (x : Input V) (v : V) : Decidable (SensitiveCoord f x v) :=
  inferInstanceAs (Decidable (f (flipSet x {v}) ≠ f x))

/-- The sensitive coordinates of `f` at `x`. -/
def sensCoords (f : Input V → Bool) (x : Input V) : Finset V :=
  Finset.univ.filter fun v ↦ SensitiveCoord f x v

lemma mem_sensCoords {f : Input V → Bool} {x : Input V} {v : V} :
    v ∈ sensCoords f x ↔ SensitiveCoord f x v := Finset.mem_filter_univ v

/-- `s(f,x)`: the number of sensitive coordinates at `x`. -/
def sensAt (f : Input V → Bool) (x : Input V) : ℕ := (sensCoords f x).card

/-- Any `Finset` containing every sensitive coordinate at `x` bounds `s(f,x)`. -/
lemma sensAt_le_card {f : Input V → Bool} {x : Input V} {s : Finset V}
    (h : sensCoords f x ⊆ s) : sensAt f x ≤ s.card :=
  Finset.card_le_card h

/-- If every coordinate is sensitive at `x` then `s(f,x)` counts all coordinates. -/
lemma sensAt_eq_card_univ {f : Input V → Bool} {x : Input V} (h : ∀ v, SensitiveCoord f x v) :
    sensAt f x = Fintype.card V := by
  rw [sensAt, sensCoords, Finset.filter_true_of_mem fun v _ ↦ h v, Finset.card_univ]

/-- `s(f)`: the sensitivity of `f`. -/
def sens (f : Input V → Bool) : ℕ := Finset.univ.sup (sensAt f)

lemma sensAt_le_sens (f : Input V → Bool) (x : Input V) : sensAt f x ≤ sens f :=
  Finset.le_sup (Finset.mem_univ x)

lemma sens_le (f : Input V → Bool) {n : ℕ} (h : ∀ x, sensAt f x ≤ n) : sens f ≤ n :=
  Finset.sup_le fun x _ ↦ h x

/-- A nonempty set `A` of coordinates is a *sensitive block* at `x` when `f (x^A) ≠ f x`. -/
structure IsSensitiveBlock (f : Input V → Bool) (x : Input V) (A : Finset V) : Prop where
  nonempty : A.Nonempty
  flips : f (flipSet x A) ≠ f x

omit [Fintype V] in
/-- The usual way to exhibit a sensitive block: a nonempty `A` that turns `f` from `false`
to `true`. -/
lemma isSensitiveBlock_of_eq_true {f : Input V → Bool} {x : Input V} {A : Finset V}
    (hA : A.Nonempty) (hx : f x = false) (hflip : f (flipSet x A) = true) :
    IsSensitiveBlock f x A :=
  ⟨hA, by simp [hx, hflip]⟩

/-- A family of pairwise disjoint sensitive blocks at `x`. -/
structure IsBlockFamily (f : Input V → Bool) (x : Input V) (𝓑 : Finset (Finset V)) : Prop where
  sensitive : ∀ A ∈ 𝓑, IsSensitiveBlock f x A
  disjoint : (𝓑 : Set (Finset V)).PairwiseDisjoint id

/-- The set of cardinalities of admissible block families at `x`. -/
def blockFamilyCards (f : Input V → Bool) (x : Input V) : Set ℕ :=
  {n | ∃ 𝓑 : Finset (Finset V), IsBlockFamily f x 𝓑 ∧ 𝓑.card = n}

omit [Fintype V] in
lemma blockFamilyCards_bddAbove [Finite V] (f : Input V → Bool) (x : Input V) :
    BddAbove (blockFamilyCards f x) := by
  let := Fintype.ofFinite V
  refine ⟨Fintype.card (Finset V), ?_⟩
  rintro n ⟨𝓑, -, rfl⟩
  exact Finset.card_le_univ 𝓑

/-- `bs(f,x)`: the maximum number of pairwise disjoint sensitive blocks at `x`. -/
noncomputable def bsAt (f : Input V → Bool) (x : Input V) : ℕ := sSup (blockFamilyCards f x)

/-- `bs(f)`: the block sensitivity of `f`. -/
noncomputable def bs (f : Input V → Bool) : ℕ := Finset.univ.sup (bsAt f)

omit [Fintype V] in
/-- Exhibiting a family of pairwise disjoint sensitive blocks bounds `bsAt` from below. -/
lemma le_bsAt_of_family [Finite V] {f : Input V → Bool} {x : Input V} {𝓑 : Finset (Finset V)}
    (h : IsBlockFamily f x 𝓑) : 𝓑.card ≤ bsAt f x :=
  le_csSup (blockFamilyCards_bddAbove f x) ⟨𝓑, h, rfl⟩

lemma bsAt_le_bs (f : Input V → Bool) (x : Input V) : bsAt f x ≤ bs f :=
  Finset.le_sup (Finset.mem_univ x)

/-- The main lower-bound interface for block sensitivity. -/
lemma le_bs_of_family {f : Input V → Bool} {x : Input V} {𝓑 : Finset (Finset V)}
    (h : IsBlockFamily f x 𝓑) : 𝓑.card ≤ bs f :=
  (le_bsAt_of_family h).trans (bsAt_le_bs f x)

omit [Fintype V] in
/-- Sensitive blocks indexed by a `Finset ι` and pairwise disjoint on it form a block family. -/
lemma isBlockFamily_image {ι : Type*} {f : Input V → Bool} {x : Input V} {B : ι → Finset V}
    {s : Finset ι} (hsens : ∀ i ∈ s, IsSensitiveBlock f x (B i))
    (hdisj : (s : Set ι).PairwiseDisjoint B) :
    IsBlockFamily f x (s.image B) where
  sensitive A hA := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hA
    exact hsens i hi
  disjoint := by
    rw [Finset.coe_image]
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hne
    exact hdisj hi hj fun h ↦ hne (congrArg B h)

/-- An indexed family of pairwise disjoint sensitive blocks bounds `bs` from below.  The blocks
are automatically pairwise distinct, being nonempty and pairwise disjoint. -/
lemma card_le_bs_of_blocks {ι : Type*} {f : Input V → Bool} {x : Input V} {B : ι → Finset V}
    {s : Finset ι} (hsens : ∀ i ∈ s, IsSensitiveBlock f x (B i))
    (hdisj : (s : Set ι).PairwiseDisjoint B) : s.card ≤ bs f := by
  rw [← Finset.card_image_of_injOn
    (hdisj.injOn fun i hi ↦ Finset.nonempty_iff_ne_empty.1 (hsens i hi).nonempty)]
  exact le_bs_of_family (isBlockFamily_image hsens hdisj)

end BSLambda
