/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarClassFactor

/-!
# The star-tensor class and its recursion

The iterated vertex-star tensor as a Hom class, with its
defining recursion at class level: the cons case is the monoidal
tensor of the vertex-star class with the tail, composed with the
sum cast.
-/

@[expose] public section

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The vertex-star class: a `(0, d)`-morphism. -/
noncomputable def vertexStarClass (d : ℕ) :
    HomSpace f.val (0 + d) :=
  HomSpace.ofFragment f.val
    ((vertexStar d).relabel (finCongr (by omega : d = 0 + d)))

/-- The star-tensor class over a degree list. -/
noncomputable def starTensorClass (ds : List ℕ) :
    HomSpace f.val (0 + ds.sum) :=
  HomSpace.ofFragment f.val
    ((starTensor ds).relabel (finCongr
      (by omega : ds.sum = 0 + ds.sum)))

/-- The empty star tensor is the empty class. -/
theorem starTensorClass_nil :
    starTensorClass f [] =
      HomSpace.ofFragment f.val emptyClosedFragment :=
  HomSpace.ofFragment_congr f
    (relabelZeroEquiv (starTensor []) _)

/-- **The class recursion**: the star tensor over a cons is the
tensor of the head vertex-star class with the tail class,
composed with the sum cast. -/
theorem starTensorClass_cons (d : ℕ) (ds : List ℕ) :
    starTensorClass f (d :: ds) =
      HomSpace.comp f 0 (d + ds.sum) ((d :: ds).sum)
        (HomSpace.tensor f 0 d 0 ds.sum
          (vertexStarClass f d) (starTensorClass f ds))
        (bundleMapClass f (finCongr
          (List.sum_cons.symm : d + ds.sum = (d :: ds).sum))) := by
  simp only [vertexStarClass, starTensorClass]
  rw [HomSpace.tensor_ofFragment, comp_bundleMapClass,
    outTransport_finCongr]
  exact HomSpace.ofFragment_congr f
    ((Fragment.Equiv.relabelTrans _ _ _).trans
      (Fragment.Equiv.relabelEq _
        (_root_.Equiv.ext (fun x => Fin.ext rfl))))

/-- The class-level star factorization, in terms of the
star-tensor class. -/
theorem starClass_factor' (W : ClosedFragment) :
    starClass f W = circleVal f ^ W.circles •
      HomSpace.comp f 0 ((degList (starAssignEnum W)).sum)
        (edgeCount W + edgeCount W)
        (starTensorClass f (degList (starAssignEnum W)))
        (bundleMapClass f
          (sortEquiv (starAssignEnum W)).symm) :=
  starClass_factor f W

end RS
