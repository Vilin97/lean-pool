/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.YoungDiagrams

/-!
# Young diagrams of a fixed size

`Shape n` is the type of Young diagrams with exactly `n` cells.  It
carries decidable equality and a `Fintype` instance, obtained from the
correspondence with `Nat.Partition n` that reads off the row lengths.
This is the tree's standard idiom for "sum over the partitions of `n`".
-/

namespace RS

/-! ### Counting cells by rows -/

/-- Young diagrams are determined by their lists of row lengths. -/
theorem rowLens_injective : Function.Injective YoungDiagram.rowLens :=
  fun _ _ h => YoungDiagram.equivListRowLens.injective (Subtype.ext h)

/-! ### Shapes -/

/-- The Young diagrams with `n` cells. -/
def Shape (n : ℕ) : Type := {μ : YoungDiagram // μ.card = n}

namespace Shape

/-- A shape's diagram has exactly `n` cells. -/
@[simp]
theorem card_val {n : ℕ} (μ : Shape n) : μ.val.card = n := μ.property

/-- Shapes are equal as soon as their diagrams are. -/
@[ext]
theorem ext {n : ℕ} {μ ν : Shape n} (h : μ.val = ν.val) : μ = ν :=
  Subtype.ext h

end Shape

/-- Equality of shapes is decidable, cell set by cell set. -/
instance (n : ℕ) : DecidableEq (Shape n) := fun μ ν =>
  decidable_of_iff (μ.val.cells = ν.val.cells)
    ((Subtype.ext_iff.trans YoungDiagram.ext_iff).symm)

/-! ### The correspondence with partitions -/

/-- Young diagrams of size `n` correspond to partitions of `n`,
by reading off the row lengths. -/
noncomputable def shapeEquivPartition (n : ℕ) :
    Shape n ≃ Nat.Partition n where
  toFun μ :=
    { parts := ↑μ.val.rowLens
      parts_pos := fun hi =>
        μ.val.pos_of_mem_rowLens _ (Multiset.mem_coe.mp hi)
      parts_sum := by
        rw [Multiset.sum_coe, ← card_eq_sum_rowLens, μ.card_val] }
  invFun p :=
    ⟨YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·))
        (Multiset.pairwise_sort p.parts (· ≥ ·)).sortedGE,
      by
        rw [card_eq_sum_rowLens,
          YoungDiagram.rowLens_ofRowLens_eq_self
            (fun x hx => p.parts_pos ((Multiset.mem_sort _).mp hx)),
          ← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]⟩
  left_inv μ := by
    apply Shape.ext
    apply rowLens_injective
    rw [YoungDiagram.rowLens_ofRowLens_eq_self
        (fun x hx => μ.val.pos_of_mem_rowLens _
          (Multiset.mem_coe.mp ((Multiset.mem_sort _).mp hx))),
      Multiset.coe_sort,
      List.mergeSort_eq_self _ (μ.val.rowLens_sorted.pairwise)]
  right_inv p := by
    apply Nat.Partition.ext
    dsimp only
    rw [YoungDiagram.rowLens_ofRowLens_eq_self
        (fun x hx => p.parts_pos ((Multiset.mem_sort _).mp hx)),
      Multiset.sort_eq]

/-- The multiset of parts of the partition attached to a shape is the
multiset of its row lengths. -/
@[simp]
theorem shapeEquivPartition_apply_parts {n : ℕ} (μ : Shape n) :
    ((shapeEquivPartition n) μ).parts = ↑μ.val.rowLens :=
  rfl

/-- There are finitely many Young diagrams with `n` cells: as many as
there are partitions of `n`. -/
noncomputable instance (n : ℕ) : Fintype (Shape n) :=
  Fintype.ofEquiv _ (shapeEquivPartition n).symm

end RS
