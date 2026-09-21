/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CoordInterface

/-!
# The multi-star form of the explosion

The star union of a closed fragment is a *multi-star*: a family
of pendant edges indexed by `Fin (2m)`, each attached to a vertex
by an assignment map.  This is the bridge between the explosion
machinery and the vertex-star factorization.
-/

namespace RS

/-- A multi-star: `n` pendant edges with a vertex assignment and
a free-circle count. -/
def multiStar {V : Type} [Fintype V] {n : ℕ}
    (assign : Fin n → V) (c : ℕ) : Fragment (Fin n) where
  Flag := Fin n ⊕ Fin n
  Vertex := V
  attach := fun g => match g with
    | Sum.inl i => Sum.inl (assign i)
    | Sum.inr i => Sum.inr i
  pairing := fun g => match g with
    | Sum.inl i => Sum.inr i
    | Sum.inr i => Sum.inl i
  pairing_invol := fun g => by rcases g with i | i <;> rfl
  pairing_ne := fun g => by rcases g with i | i <;> simp
  boundaryFlag := Sum.inr
  attach_boundaryFlag := fun _ => rfl
  eq_boundaryFlag := fun ℓ g h => by
    rcases g with i | i
    · exact absurd h (by simp)
    · exact congrArg Sum.inr (Sum.inr.inj h)
  circles := c

/-- The inner-flag enumeration of the star union: original flags
through the star enumeration. -/
noncomputable def starFlagEnum (W : ClosedFragment) :
    W.Flag ≃ Fin (edgeCount W + edgeCount W) :=
  (_root_.Equiv.subtypeUnivEquiv
    (fun f => Finset.mem_univ f)).symm.trans (starEnum W)

/-- The vertex assignment of the star union: each slot's original
flag sits at its vertex. -/
noncomputable def starAssign (W : ClosedFragment) :
    Fin (edgeCount W + edgeCount W) → W.Vertex :=
  fun i => ClosedFragment.vertexOf W ((starFlagEnum W).symm i)

/-- **The star union is a multi-star**: the explosion at the full
cut, enumerated, is the family of pendant edges over the original
flags with their vertex assignment. -/
noncomputable def starUnionMultiStar (W : ClosedFragment) :
    (starUnion W).Equiv
      (multiStar (starAssign W) W.circles) where
  flagEquiv :=
    _root_.Equiv.sumCongr (starFlagEnum W) (starEnum W)
  vertexEquiv := _root_.Equiv.refl W.Vertex
  attach_comm := fun g => by
    rcases g with fo | fc
    · show Sum.inl (starAssign W (starFlagEnum W fo)) =
        (Sum.inl (ClosedFragment.vertexOf W fo) :
          W.Vertex ⊕ Fin (edgeCount W + edgeCount W)).map
          (_root_.Equiv.refl W.Vertex) id
      refine congrArg Sum.inl ?_
      show ClosedFragment.vertexOf W
        ((starFlagEnum W).symm (starFlagEnum W fo)) = _
      rw [(starFlagEnum W).symm_apply_apply]
      rfl
    · show Sum.inr (starEnum W fc) =
        (Sum.inr (starEnum W fc) :
          W.Vertex ⊕ Fin (edgeCount W + edgeCount W)).map
          (_root_.Equiv.refl W.Vertex) id
      rfl
  pairing_comm := fun g => by
    rcases g with fo | fc
    · have hp : (starUnion W).pairing (Sum.inl fo) =
          Sum.inr ⟨fo, Finset.mem_univ fo⟩ :=
        dif_pos (Finset.mem_univ fo)
      rw [hp]
      show Sum.inr (starEnum W ⟨fo, Finset.mem_univ fo⟩) =
        Sum.inr (starFlagEnum W fo)
      rfl
    · show Sum.inl (starFlagEnum W fc.val) =
        Sum.inl ((starFlagEnum W).symm.symm fc.val)
      rfl
  circles_eq := rfl

end RS
