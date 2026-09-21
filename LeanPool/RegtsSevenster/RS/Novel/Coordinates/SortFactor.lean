/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockSigma
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockSort

/-!
# The sorted factorization of a multi-star

Chaining the sort with the block enumeration and the block
factorization: any multi-star is, up to relabelling along the
sort, the iterated tensor of vertex stars over its degree list
with the free circles split off.  Specialised to the star union
this is the fragment-level star factorization.
-/

namespace RS

section SortEquiv

variable {n m : ℕ} (assign : Fin n → Fin m)

/-- The full sort: slots to the block-concatenated enumeration. -/
noncomputable def sortEquiv : Fin n ≃ Fin (degList assign).sum :=
  (sortSigma assign).trans (blockSigmaEquiv (degList assign))

/-- The sort intertwines the assignment with the block
assignment. -/
theorem blockAssign_sortEquiv (i : Fin n) :
    blockAssign (degList assign) (sortEquiv assign i) =
      finCongr (degList_length assign).symm (assign i) := by
  show blockAssign _
    (blockSigmaEquiv _ (sortSigma assign i)) = _
  rw [blockAssign_blockSigmaEquiv]
  exact sortSigma_fst assign i

/-- Sorting a multi-star into block-assigned form. -/
noncomputable def multiStarSorted (c : ℕ) :
    (multiStar assign c).Equiv
      ((multiStar (blockAssign (degList assign)) c).relabel
        (sortEquiv assign).symm) :=
  multiStarCompRelabel assign c (sortEquiv assign)
    (blockAssign (degList assign))
    (finCongr (degList_length assign).symm)
    (blockAssign_sortEquiv assign)

/-- **The sorted factorization**: a multi-star is the iterated
tensor of vertex stars over its degree list, with the circles
split off, relabelled along the sort. -/
noncomputable def multiStarFactor (c : ℕ) :
    (multiStar assign c).Equiv
      ((addCircles (starTensor (degList assign)) c).relabel
        (sortEquiv assign).symm) :=
  (multiStarSorted assign c).trans
    (Fragment.Equiv.relabelCongr
      (multiStarBlocks (degList assign) c) _)

end SortEquiv

section StarUnionFactor

/-- Reindexing the vertices of a multi-star. -/
noncomputable def multiStarVertexMap {V V' : Type}
    [Fintype V] [Fintype V'] {n : ℕ} (assign : Fin n → V)
    (c : ℕ) (e : V ≃ V') :
    (multiStar assign c).Equiv (multiStar (e ∘ assign) c) where
  flagEquiv := _root_.Equiv.refl _
  vertexEquiv := e
  attach_comm := fun g => by
    rcases g with i | i <;> rfl
  pairing_comm := fun g => by
    rcases g with i | i <;> rfl
  circles_eq := rfl

/-- The star union's assignment, with vertices enumerated. -/
noncomputable def starAssignEnum (W : ClosedFragment) :
    Fin (edgeCount W + edgeCount W) →
      Fin (Fintype.card W.Vertex) :=
  (Fintype.equivFin W.Vertex) ∘ starAssign W

/-- **The fragment-level star factorization**: the star union of
a closed fragment is the iterated tensor of its vertex stars over
the degree list, with its free circles split off, relabelled
along the sort. -/
noncomputable def starUnionFactor (W : ClosedFragment) :
    (starUnion W).Equiv
      ((addCircles (starTensor (degList (starAssignEnum W)))
        W.circles).relabel (sortEquiv (starAssignEnum W)).symm) :=
  (starUnionMultiStar W).trans
    ((multiStarVertexMap (starAssign W) W.circles
      (Fintype.equivFin W.Vertex)).trans
      (multiStarFactor (starAssignEnum W) W.circles))

end StarUnionFactor

end RS
