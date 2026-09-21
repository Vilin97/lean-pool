/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.MultiStar
import LeanPool.RegtsSevenster.RS.DimensionDefinitions

/-!
# Free circles as scalars

A fragment with extra free circles is the tensor with a
circles-only closed fragment; on Hom classes the circles split
off as the power of the circle value.  This is the accompanying paper's
"free circles are carried by multiplicativity" discipline, at
class level.
-/

namespace RS

/-- The circle value of a parameter. -/
noncomputable def circleVal {R : ℕ} (f : EdgeRankParameter R) : ℂ :=
  f.val (circlesClosed 1)

/-- Adding free circles to a fragment. -/
def addCircles {α : Type} (X : Fragment α) (c : ℕ) :
    Fragment α :=
  { X with circles := X.circles + c }

/-- Adding circles is tensoring with a circles-only fragment. -/
noncomputable def addCirclesTensor {s t : ℕ}
    (X : Fragment (Fin (s + t))) (c : ℕ) :
    (tensorFragment X (circlesClosed c)).Equiv
      ((addCircles X c).relabel (finCongr
        (by omega : s + t = (s + 0) + (t + 0)))) where
  flagEquiv :=
    show (X.Flag ⊕ Empty) ≃ X.Flag from
      _root_.Equiv.sumEmpty X.Flag Empty
  vertexEquiv :=
    show (X.Vertex ⊕ Empty) ≃ X.Vertex from
      _root_.Equiv.sumEmpty X.Vertex Empty
  attach_comm := fun g => by
    rcases g with g | g
    · show (X.attach g).map id
        (finCongr (by omega : s + t = (s + 0) + (t + 0))) =
        Sum.map (show (X.Vertex ⊕ Empty) ≃ X.Vertex from
          _root_.Equiv.sumEmpty X.Vertex Empty) id
          (Sum.map id (interleaveEquiv s t 0 0)
            (Sum.map Sum.inl Sum.inl (X.attach g)))
      rcases ha : X.attach g with v | ℓ
      · rfl
      · exact congrArg Sum.inr (interleave_unit_right s t ℓ).symm
    · exact g.elim
  pairing_comm := fun g => by
    rcases g with g | g
    · rfl
    · exact g.elim
  circles_eq := rfl

/-- The union of circle fragments adds the counts. -/
noncomputable def circlesClosedUnion (a b : ℕ) :
    (ClosedFragment.union (circlesClosed a)
        (circlesClosed b)).Equiv (circlesClosed (a + b)) where
  flagEquiv :=
    haveI h1 : IsEmpty (circlesClosed a).Flag :=
      inferInstanceAs (IsEmpty Empty)
    haveI h2 : IsEmpty (circlesClosed b).Flag :=
      inferInstanceAs (IsEmpty Empty)
    haveI : IsEmpty (ClosedFragment.union (circlesClosed a)
        (circlesClosed b)).Flag :=
      ⟨fun g => g.elim h1.elim h2.elim⟩
    haveI : IsEmpty (circlesClosed (a + b)).Flag :=
      inferInstanceAs (IsEmpty Empty)
    _root_.Equiv.equivOfIsEmpty _ _
  vertexEquiv :=
    haveI h1 : IsEmpty (circlesClosed a).Vertex :=
      inferInstanceAs (IsEmpty Empty)
    haveI h2 : IsEmpty (circlesClosed b).Vertex :=
      inferInstanceAs (IsEmpty Empty)
    haveI : IsEmpty (ClosedFragment.union (circlesClosed a)
        (circlesClosed b)).Vertex :=
      ⟨fun g => g.elim h1.elim h2.elim⟩
    haveI : IsEmpty (circlesClosed (a + b)).Vertex :=
      inferInstanceAs (IsEmpty Empty)
    _root_.Equiv.equivOfIsEmpty _ _
  attach_comm := fun g => by
    haveI h1 : IsEmpty (circlesClosed a).Flag :=
      inferInstanceAs (IsEmpty Empty)
    haveI h2 : IsEmpty (circlesClosed b).Flag :=
      inferInstanceAs (IsEmpty Empty)
    exact g.elim h1.elim h2.elim
  pairing_comm := fun g => by
    haveI h1 : IsEmpty (circlesClosed a).Flag :=
      inferInstanceAs (IsEmpty Empty)
    haveI h2 : IsEmpty (circlesClosed b).Flag :=
      inferInstanceAs (IsEmpty Empty)
    exact g.elim h1.elim h2.elim
  circles_eq := rfl

/-- The circle value of `c` circles is the `c`-th power. -/
theorem circlesClosed_val {R : ℕ} (f : EdgeRankParameter R)
    (c : ℕ) :
    f.val (circlesClosed c) = circleVal f ^ c := by
  induction c with
  | zero =>
    rw [pow_zero]
    have h : (circlesClosed 0).Equiv emptyClosedFragment :=
      { flagEquiv :=
          haveI : IsEmpty (circlesClosed 0).Flag :=
            inferInstanceAs (IsEmpty Empty)
          haveI : IsEmpty emptyClosedFragment.Flag :=
            inferInstanceAs (IsEmpty Empty)
          _root_.Equiv.equivOfIsEmpty _ _
        vertexEquiv :=
          haveI : IsEmpty (circlesClosed 0).Vertex :=
            inferInstanceAs (IsEmpty Empty)
          haveI : IsEmpty emptyClosedFragment.Vertex :=
            inferInstanceAs (IsEmpty Empty)
          _root_.Equiv.equivOfIsEmpty _ _
        attach_comm := fun g => by
          haveI : IsEmpty (circlesClosed 0).Flag :=
            inferInstanceAs (IsEmpty Empty)
          exact isEmptyElim g
        pairing_comm := fun g => by
          haveI : IsEmpty (circlesClosed 0).Flag :=
            inferInstanceAs (IsEmpty Empty)
          exact isEmptyElim g
        circles_eq := rfl }
    rw [f.iso_invariant _ _ h]
    exact f.val_empty
  | succ n ih =>
    have h : (circlesClosed (n + 1)).Equiv
        (ClosedFragment.union (circlesClosed n)
          (circlesClosed 1)) :=
      (circlesClosedUnion n 1).symm
    rw [f.iso_invariant _ _ h, EdgeRankParameter.val_union,
      ih, pow_succ]
    rfl

variable {R : ℕ} (f : EdgeRankParameter R)

/-- Relabelling by the unit-padding cast fixes the class. -/
theorem ofFragment_relabel_unitcast {s t : ℕ}
    (Y : Fragment (Fin (s + t))) :
    HomSpace.ofFragment f.val (Y.relabel (finCongr
      (by omega : s + t = (s + 0) + (t + 0)))) =
      HomSpace.ofFragment f.val Y :=
  HomSpace.ofFragment_congr f
    ((Fragment.Equiv.relabelEq Y
      (_root_.Equiv.ext (fun _ => Fin.ext rfl))).trans
      (Fragment.Equiv.relabelRefl Y))

/-- **The class-level circle split**, at the padded arity: the
tensor with a circles-only fragment is the circle power times the
padded class. -/
theorem ofFragment_tensor_circles {s t : ℕ}
    (X : Fragment (Fin (s + t))) (c : ℕ) :
    HomSpace.ofFragment f.val
        (tensorFragment X (circlesClosed c)) =
      circleVal f ^ c •
        HomSpace.ofFragment f.val (X.relabel (finCongr
          (by omega : s + t = (s + 0) + (t + 0)))) := by
  rw [← HomSpace.tensor_ofFragment,
    show HomSpace.ofFragment f.val (circlesClosed c) =
      f.val (circlesClosed c) •
        HomSpace.ofFragment f.val emptyClosedFragment from
      ofFragment_eq_smul_empty f (circlesClosed c),
    map_smul, circlesClosed_val, HomSpace.tensor_ofFragment]
  exact congrArg (fun z => circleVal f ^ c • z)
    (HomSpace.ofFragment_congr f (tensorFragmentUnitRight X))

end RS
