/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite colour classes and proper edge colourings

Colour classes partition a finite set. For graph edges, properness means
that two distinct edges of the same colour have disjoint endpoints.
-/

public section

namespace LeanPool.Vizing.ColourClasses

variable {α β : Type*} [DecidableEq β]

/-- The elements of `S` assigned the literal colour `b`. -/
@[expose]
def colourClass (S : Finset α) (colour : α → β) (b : β) : Finset α :=
  S.filter fun a => colour a = b

/-- The palette actually used by a finite coloured set. -/
def usedColours (S : Finset α) (colour : α → β) : Finset β := S.image colour

theorem mem_colourClass {S : Finset α} {colour : α → β} {b : β} {a : α} :
    a ∈ colourClass S colour b ↔ a ∈ S ∧ colour a = b := by
  simp [colourClass]

theorem colourClass_subset (S : Finset α) (colour : α → β) (b : β) :
    colourClass S colour b ⊆ S := by
  intro a ha
  exact (mem_colourClass.mp ha).1

theorem disjoint_colourClass {S : Finset α} {colour : α → β} {b d : β}
    (hbd : b ≠ d) :
    Disjoint (colourClass S colour b) (colourClass S colour d) := by
  rw [Finset.disjoint_left]
  intro a hab had
  have hb := (mem_colourClass.mp hab).2
  have hd := (mem_colourClass.mp had).2
  exact hbd (hb.symm.trans hd)

theorem biUnion_colourClass [DecidableEq α] (S : Finset α) (colour : α → β) :
    (usedColours S colour).biUnion (colourClass S colour) = S := by
  apply Finset.Subset.antisymm
  · intro a ha
    rcases Finset.mem_biUnion.mp ha with ⟨b, hb, hclass⟩
    exact (mem_colourClass.mp hclass).1
  · intro a ha
    refine Finset.mem_biUnion.mpr ⟨colour a, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · exact mem_colourClass.mpr ⟨ha, rfl⟩

/-- Exact cardinal ledger for the colour classes. -/
theorem card_eq_sum_card_colourClass (S : Finset α) (colour : α → β) :
    S.card = ∑ b ∈ usedColours S colour, (colourClass S colour b).card := by
  simpa only [usedColours, colourClass] using Finset.card_eq_sum_card_image colour S

/-! ### Proper edge colours -/

variable {V : Type*} [DecidableEq V]

/-- Two distinct edges assigned the same colour have no common endpoint. -/
@[expose]
def ProperOn (E : Finset (Sym2 V)) (colour : Sym2 V → β) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, e ≠ f → colour e = colour f →
    Disjoint e.toFinset f.toFinset

/-- Every colour class of a proper edge colouring is a matching. -/
theorem colourClass_pairwiseDisjoint_toFinset
    {E : Finset (Sym2 V)} {colour : Sym2 V → β}
    (hproper : ProperOn E colour) (b : β) :
    (↑(colourClass E colour b) : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
  intro e he f hf hef
  apply hproper e (colourClass_subset E colour b (by simpa using he))
    f (colourClass_subset E colour b (by simpa using hf)) hef
  have heq := (mem_colourClass.mp (by simpa using he)).2
  have hfq := (mem_colourClass.mp (by simpa using hf)).2
  exact heq.trans hfq.symm

end LeanPool.Vizing.ColourClasses
