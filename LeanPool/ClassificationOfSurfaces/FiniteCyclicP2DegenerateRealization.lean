/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP2Realization
import LeanPool.ClassificationOfSurfaces.P2DegenerateDisk

/-!
# Polygonal realization of one-sided-degenerate Gallier--Xu P2

This file lifts the local monogon--polygon disk theorem to finite cyclic presentations.  The
positive base case has an empty left cut word and a nonempty right cut word.  Reversal and child
swap transport that case to every ordinary-valid one-sided-degenerate cut.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P2

theorem leftLength_eq_zero
    {P : FiniteCyclicPresentation} {cut : P2Cut P}
    (hleft : cut.left = []) :
    cut.left.length = 0 := by
  simp [hleft]

/-- The rotated source side index, specialized to an empty-left cut. -/
noncomputable def rightDegenerateCutSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (_hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    Fin cut.right.length :=
  ⟨(i.val + positiveCutRotation P cut horientation) %
      cut.right.length,
    Nat.mod_lt _ hr⟩

@[simp]
theorem rightDegenerateCutSideIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    (rightDegenerateCutSideIndex
      P cut horientation hleft hr i).val =
      (i.val + positiveCutRotation P cut horientation) %
        cut.right.length :=
  rfl

theorem sourceBoundaryLength_eq_rightLength
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hleft : cut.left = []) :
    (P.boundary cut.face.face).length =
      cut.right.length := by
  rw [sourceBoundaryLength_eq_cutLength P cut,
    hleft]
  simp

theorem rightDegenerateCutSideIndex_injective
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    Function.Injective
      (rightDegenerateCutSideIndex
        P cut horientation hleft hr) := by
  intro i j hij
  have hmod :
      i.val + positiveCutRotation P cut horientation ≡
        j.val + positiveCutRotation P cut horientation
          [MOD cut.right.length] :=
    congrArg Fin.val hij
  have hcancel :
      i.val ≡ j.val [MOD cut.right.length] :=
    Nat.ModEq.add_right_cancel'
      (positiveCutRotation P cut horientation) hmod
  apply Fin.ext
  unfold Nat.ModEq at hcancel
  rw [← sourceBoundaryLength_eq_rightLength P cut hleft,
    Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt] at hcancel
  exact hcancel

theorem rightDegenerateCutSideIndex_surjective
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    Function.Surjective
      (rightDegenerateCutSideIndex
        P cut horientation hleft hr) := by
  exact ((Fintype.bijective_iff_injective_and_card
    (rightDegenerateCutSideIndex
      P cut horientation hleft hr)).2
      ⟨rightDegenerateCutSideIndex_injective
          P cut horientation hleft hr,
        by
          simp only [Fintype.card_fin]
          exact sourceBoundaryLength_eq_rightLength
            P cut hleft⟩).2

theorem right_get_rightDegenerateCutSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    cut.right[
        (rightDegenerateCutSideIndex
          P cut horientation hleft hr i).val] =
      (P.boundary cut.face.face)[i.val] := by
  -- Use the rotation lookup directly, with the empty append simplified.
  have hiCut :
      i.val < (cut.left ++ cut.right).length := by
    rw [hleft, List.nil_append,
      ← sourceBoundaryLength_eq_rightLength P cut hleft]
    exact i.isLt
  have hpoint :=
    congrArg (fun word => word[i.val]?)
      (rotate_cutBoundary_eq_sourceBoundary
        P cut horientation)
  rw [List.getElem?_rotate hiCut] at hpoint
  rw [hleft, List.nil_append] at hpoint
  rw [List.getElem?_eq_getElem
      (Nat.mod_lt _ hr),
    List.getElem?_eq_getElem i.isLt] at hpoint
  exact Option.some.inj (by
    simpa [rightDegenerateCutSideIndex] using hpoint)

/-- Phantom transport from the literal monogon to a selected child whose old-side count is
propositionally zero. -/
noncomputable def zeroLeftCellHomeomorph
    {l : ℕ} (hl : l = 0) :
    PolygonCell 1 ≃ₜ PolygonCell (l + 1) :=
  PolygonCell.rotateHomeomorph (by omega) 0

theorem zeroLeftCellHomeomorph_side
    {l : ℕ} (hl : l = 0) (t : unitInterval) :
    zeroLeftCellHomeomorph hl
        (PolygonCell.side (0 : Fin 1) t) =
      PolygonCell.side (Fin.last l) t := by
  rw [zeroLeftCellHomeomorph]
  have hpos : 0 < l + 1 := by omega
  rw [PolygonCell.rotateHomeomorph_side_of_eq
    (by omega) hpos 0 (0 : Fin 1) t]
  congr 2
  apply Fin.ext
  simp [hl]

/-- The `zeroLeftChildPairHomeomorph` declaration. -/
noncomputable def zeroLeftChildPairHomeomorph
    {l r : ℕ} (hl : l = 0) :
    DiskSquare.ChildPair 0 r ≃ₜ
      DiskSquare.ChildPair l r :=
  Homeomorph.sumCongr
    (zeroLeftCellHomeomorph hl)
    (Homeomorph.refl (PolygonCell (r + 1)))

theorem zeroLeftChildPair_generator_map
    {l r : ℕ} (hl : l = 0)
    {x y : DiskSquare.ChildPair 0 r}
    (hxy : DiskSquare.ParamChildSeamGenerator 0 r x y) :
    DiskSquare.ParamChildSeamGenerator l r
      (zeroLeftChildPairHomeomorph hl x)
      (zeroLeftChildPairHomeomorph hl y) := by
  cases hxy with
  | glue t =>
      change
        DiskSquare.ParamChildSeamGenerator l r
          (.inl
            (zeroLeftCellHomeomorph hl
              (PolygonCell.side (0 : Fin 1) t)))
          (.inr
            (PolygonCell.side (0 : Fin (r + 1))
              (unitInterval.symm t)))
      rw [zeroLeftCellHomeomorph_side]
      exact DiskSquare.ParamChildSeamGenerator.glue t

theorem zeroLeftCellHomeomorph_symm_side
    {l : ℕ} (hl : l = 0) (t : unitInterval) :
    (zeroLeftCellHomeomorph hl).symm
        (PolygonCell.side (Fin.last l) t) =
      PolygonCell.side (0 : Fin 1) t := by
  apply (zeroLeftCellHomeomorph hl).injective
  rw [Homeomorph.apply_symm_apply,
    zeroLeftCellHomeomorph_side]

theorem zeroLeftChildPair_generator_comap
    {l r : ℕ} (hl : l = 0)
    {x y : DiskSquare.ChildPair l r}
    (hxy : DiskSquare.ParamChildSeamGenerator l r x y) :
    DiskSquare.ParamChildSeamGenerator 0 r
      ((zeroLeftChildPairHomeomorph hl).symm x)
      ((zeroLeftChildPairHomeomorph hl).symm y) := by
  cases hxy with
  | glue t =>
      change
        DiskSquare.ParamChildSeamGenerator 0 r
          (.inl
            ((zeroLeftCellHomeomorph hl).symm
              (PolygonCell.side (Fin.last l) t)))
          (.inr
            (PolygonCell.side (0 : Fin (r + 1))
              (unitInterval.symm t)))
      rw [zeroLeftCellHomeomorph_symm_side]
      exact DiskSquare.ParamChildSeamGenerator.glue t

theorem zeroLeftChildPair_eqvGen_iff
    {l r : ℕ} (hl : l = 0)
    (x y : DiskSquare.ChildPair 0 r) :
    Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 r) x y ↔
      Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator l r)
        (zeroLeftChildPairHomeomorph hl x)
        (zeroLeftChildPairHomeomorph hl y) := by
  constructor
  · intro hxy
    induction hxy with
    | rel _ _ h =>
        exact Relation.EqvGen.rel _ _
          (zeroLeftChildPair_generator_map hl h)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro hxy
    let e :
        DiskSquare.ChildPair 0 r ≃ₜ
          DiskSquare.ChildPair l r :=
      zeroLeftChildPairHomeomorph hl
    have hcomap :
        ∀ {u v : DiskSquare.ChildPair l r},
          Relation.EqvGen
              (DiskSquare.ParamChildSeamGenerator l r) u v →
            Relation.EqvGen
              (DiskSquare.ParamChildSeamGenerator 0 r)
              (e.symm u) (e.symm v) := by
      intro u v huv
      induction huv with
      | rel _ _ h =>
          exact Relation.EqvGen.rel _ _
            (zeroLeftChildPair_generator_comap hl h)
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ih₁ ih₂ =>
          exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    simpa only [e, Homeomorph.symm_apply_apply] using
      hcomap hxy

/-- The `zeroLeftChildGluingHomeomorph` declaration. -/
noncomputable def zeroLeftChildGluingHomeomorph
    {l r : ℕ} (hl : l = 0) :
    DiskSquare.ParamChildGluing 0 r ≃ₜ
      DiskSquare.ParamChildGluing l r :=
  Homeomorph.Quotient.congr
    (zeroLeftChildPairHomeomorph hl)
    (zeroLeftChildPair_eqvGen_iff hl)

@[simp]
theorem zeroLeftChildGluingHomeomorph_mk_inr
    {l r : ℕ} (hl : l = 0)
    (z : PolygonCell (r + 1)) :
    zeroLeftChildGluingHomeomorph hl
        (@Quotient.mk''
          (DiskSquare.ChildPair 0 r)
          (DiskSquare.paramChildSeamSetoid 0 r)
          (.inr z)) =
      @Quotient.mk''
        (DiskSquare.ChildPair l r)
        (DiskSquare.paramChildSeamSetoid l r)
        (.inr z) :=
  rfl

/-- The selected source cell, cyclically aligned and then cut by the local degenerate disk
homeomorphism. -/
noncomputable def rightDegenerateSelectedCellHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    PolygonCell (P.boundary cut.face.face).length ≃ₜ
      DiskSquare.ParamChildGluing
        cut.left.length cut.right.length :=
  (PolygonCell.rotateHomeomorph
    (sourceBoundaryLength_eq_rightLength P cut hleft)
    (positiveCutRotation P cut horientation)).trans
    ((P2DegenerateDisk.sourceChildGluingHomeomorph
      cut.right.length hr).trans
      (zeroLeftChildGluingHomeomorph
        (leftLength_eq_zero hleft)))

theorem rightDegenerateSelectedCellHomeomorph_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (t : unitInterval) :
    rightDegenerateSelectedCellHomeomorph
        P cut horientation hleft hr
        (PolygonCell.side i t) =
      @Quotient.mk''
        (DiskSquare.ChildPair
          cut.left.length cut.right.length)
        (DiskSquare.paramChildSeamSetoid
          cut.left.length cut.right.length)
        (.inr
          (PolygonCell.side
            ((rightDegenerateCutSideIndex
              P cut horientation hleft hr i).addNat 1) t)) := by
  have hrotate :=
    PolygonCell.rotateHomeomorph_side_of_eq
      (sourceBoundaryLength_eq_rightLength P cut hleft)
      hr
      (positiveCutRotation P cut horientation) i t
  rw [rightDegenerateSelectedCellHomeomorph,
    Homeomorph.trans_apply, Homeomorph.trans_apply,
    hrotate,
    P2DegenerateDisk.sourceChildGluingHomeomorph_side,
    zeroLeftChildGluingHomeomorph_mk_inr]
  congr 3

/-- Cut the selected source face and include its local child quotient in the complete split
realization. -/
noncomputable def rightDegenerateSelectedFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    PolygonCell (P.boundary cut.face.face).length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  positiveChildGluingMap P cut horientation validP ∘
    rightDegenerateSelectedCellHomeomorph
      P cut horientation hleft hr

theorem continuous_rightDegenerateSelectedFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegenerateSelectedFaceMap
      P cut horientation hleft hr validP) :=
  (continuous_positiveChildGluingMap
      P cut horientation validP).comp
    (rightDegenerateSelectedCellHomeomorph
      P cut horientation hleft hr).continuous

theorem rightDegenerateSelectedFaceMap_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (i : Fin (P.boundary cut.face.face).length)
    (t : unitInterval) :
    rightDegenerateSelectedFaceMap
        P cut horientation hleft hr validP
        (PolygonCell.side i t) =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        ⟨rightFace P cut,
          PolygonCell.side
            (positiveRightChildSideIndex P cut horientation
              ((rightDegenerateCutSideIndex
                P cut horientation hleft hr i).addNat 1)) t⟩ := by
  rw [rightDegenerateSelectedFaceMap,
    Function.comp_apply,
    rightDegenerateSelectedCellHomeomorph_side,
    positiveChildGluingMap_mk]
  simp only [positiveChildPairMap, Function.comp_apply,
    positiveChildPairPreMap_inr,
    positiveRightChildCellHomeomorph_side]

/-- Facewise forward map for an empty-left positive cut. -/
noncomputable def rightDegenerateFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    PolygonCell (P.boundary f).length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    exact rightDegenerateSelectedFaceMap
      P cut horientation hleft hr validP
  · exact retainedFaceMap P cut hface validP

theorem continuous_rightDegenerateFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    Continuous (rightDegenerateFaceMap
      P cut horientation hleft hr validP f) := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    simpa [rightDegenerateFaceMap] using
      continuous_rightDegenerateSelectedFaceMap
        P cut horientation hleft hr validP
  · simpa [rightDegenerateFaceMap, hface] using
      continuous_retainedFaceMap P cut hface validP

/-- The `rightDegeneratePreMap` declaration. -/
noncomputable def rightDegeneratePreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonalPreRealization →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  fun x => rightDegenerateFaceMap
    P cut horientation hleft hr validP x.1 x.2

theorem continuous_rightDegeneratePreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegeneratePreMap
      P cut horientation hleft hr validP) := by
  apply continuous_sigma
  exact continuous_rightDegenerateFaceMap
    P cut horientation hleft hr validP

@[simp]
theorem rightDegeneratePreMap_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (P.boundary cut.face.face).length) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        ⟨cut.face.face, z⟩ =
      rightDegenerateSelectedFaceMap
        P cut horientation hleft hr validP z := by
  simp [rightDegeneratePreMap, rightDegenerateFaceMap]

@[simp]
theorem rightDegeneratePreMap_retained
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (z : PolygonCell (P.boundary f).length) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP ⟨f, z⟩ =
      retainedFaceMap P cut hface validP z := by
  simp [rightDegeneratePreMap,
    rightDegenerateFaceMap, hface]

theorem rightDegeneratePreMap_selected_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (i : Fin (P.boundary cut.face.face).length)
    (t : unitInterval) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        ⟨cut.face.face, PolygonCell.side i t⟩ =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        ⟨rightFace P cut,
          PolygonCell.side
            (positiveRightChildSideIndex P cut horientation
              ((rightDegenerateCutSideIndex
                P cut horientation hleft hr i).addNat 1)) t⟩ := by
  rw [rightDegeneratePreMap_selected,
    rightDegenerateSelectedFaceMap_side]

theorem rightDegeneratePreMap_retained_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (i : Fin (P.boundary f).length) (t : unitInterval) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        ⟨f, PolygonCell.side i t⟩ =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        ⟨oldFace P cut f,
          PolygonCell.side
            (retainedSideIndex P cut hface i) t⟩ := by
  rw [rightDegeneratePreMap_retained
      P cut horientation hleft hr validP hface,
    retainedFaceMap, retainedCellHomeomorph_side]

/-- Route every old source occurrence to the target occurrence carrying it after the split. -/
noncomputable def rightDegenerateMapOccurrence
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (o : P.BoundaryOccurrence) :
    (split P cut).BoundaryOccurrence := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    exact
      ⟨rightFace P cut,
        positiveRightChildSideIndex P cut horientation
          ((rightDegenerateCutSideIndex
            P cut horientation hleft hr i).addNat 1)⟩
  · exact
      ⟨oldFace P cut f,
        retainedSideIndex P cut hface i⟩

@[simp]
theorem rightDegenerateMapOccurrence_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    rightDegenerateMapOccurrence
        P cut horientation hleft hr
        ⟨cut.face.face, i⟩ =
      ⟨rightFace P cut,
        positiveRightChildSideIndex P cut horientation
          ((rightDegenerateCutSideIndex
            P cut horientation hleft hr i).addNat 1)⟩ := by
  simp [rightDegenerateMapOccurrence]

@[simp]
theorem rightDegenerateMapOccurrence_retained
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (i : Fin (P.boundary f).length) :
    rightDegenerateMapOccurrence
        P cut horientation hleft hr ⟨f, i⟩ =
      ⟨oldFace P cut f,
        retainedSideIndex P cut hface i⟩ := by
  simp [rightDegenerateMapOccurrence, hface]

theorem rightDegeneratePreMap_occurrenceSide
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (t : unitInterval) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        ((P.occurrenceSide o).point t) =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        (((split P cut).occurrenceSide
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr o)).point t) := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    rw [rightDegenerateMapOccurrence_selected]
    simp only [occurrenceSide,
      PolygonGluing.Side.point]
    convert rightDegeneratePreMap_selected_side
      P cut horientation hleft hr validP i t using 1 <;> rfl
  · rw [rightDegenerateMapOccurrence_retained
      P cut horientation hleft hr hface i]
    simp only [occurrenceSide,
      PolygonGluing.Side.point]
    convert rightDegeneratePreMap_retained_side
      P cut horientation hleft hr validP hface i t using 1 <;> rfl

theorem rightDegenerateMapOccurrence_dart
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (o : P.BoundaryOccurrence) :
    (rightDegenerateMapOccurrence
      P cut horientation hleft hr o).dart =
      P1.castSuccDart o.dart := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    rw [rightDegenerateMapOccurrence_selected,
      BoundaryOccurrence.dart_mk]
    rw [List.get_of_eq (split_boundary_right P cut)]
    change
      (rightBoundary P cut).get
          ⟨(rightDegenerateCutSideIndex
              P cut horientation hleft hr i).val + 1,
            by
              rw [rightBoundary_of_orientation_false
                P cut horientation]
              simp only [rightDegenerateCutSideIndex_val, retainWord, List.length_cons,
                List.length_map, Order.lt_add_one_iff, Order.add_one_le_iff]
              exact
                (rightDegenerateCutSideIndex
                  P cut horientation hleft hr i).isLt⟩ =
        P1.castSuccDart
          ((P.boundary cut.face.face)[i.val])
    rw [List.get_of_eq
      (rightBoundary_of_orientation_false
        P cut horientation)]
    change
      (.neg (freshEdge P) :: retainWord cut.right)[
          (rightDegenerateCutSideIndex
            P cut horientation hleft hr i).val + 1]'(by
              simp only [rightDegenerateCutSideIndex_val, retainWord, List.length_cons,
                List.length_map, Order.lt_add_one_iff, Order.add_one_le_iff]
              exact
                (rightDegenerateCutSideIndex
                  P cut horientation hleft hr i).isLt) =
        P1.castSuccDart
          ((P.boundary cut.face.face)[i.val])
    rw [List.getElem_cons_succ]
    change
      (List.map P1.castSuccDart cut.right)[
          (rightDegenerateCutSideIndex
            P cut horientation hleft hr i).val] =
        P1.castSuccDart
          ((P.boundary cut.face.face)[i.val])
    rw [List.getElem_map]
    exact congrArg P1.castSuccDart
      (right_get_rightDegenerateCutSideIndex
        P cut horientation hleft hr i)
  · rw [rightDegenerateMapOccurrence_retained
      P cut horientation hleft hr hface i,
      BoundaryOccurrence.dart_mk]
    rw [List.get_of_eq
      (split_boundary_old_of_ne P cut hface)]
    change
      (List.map P1.castSuccDart
        (P.boundary f))[i.val] =
          P1.castSuccDart
            ((P.boundary f)[i.val])
    rw [List.getElem_map]

@[simp]
theorem rightDegenerateMapOccurrence_edge
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (o : P.BoundaryOccurrence) :
    (rightDegenerateMapOccurrence
      P cut horientation hleft hr o).edge =
      o.edge.castSucc := by
  rw [BoundaryOccurrence.edge,
    rightDegenerateMapOccurrence_dart]
  exact P1.edgeOfDart_castSuccDart o.dart

theorem rightDegenerateMapOccurrence_injective
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    Function.Injective
      (rightDegenerateMapOccurrence
        P cut horientation hleft hr) := by
  classical
  rintro ⟨f, i⟩ ⟨g, j⟩ hmap
  by_cases hf : f = cut.face.face
  · subst f
    by_cases hg : g = cut.face.face
    · subst g
      rw [rightDegenerateMapOccurrence_selected,
        rightDegenerateMapOccurrence_selected] at hmap
      have hval := congrArg
        (fun o : (split P cut).BoundaryOccurrence =>
          o.2.val) hmap
      have hindex :
          rightDegenerateCutSideIndex
              P cut horientation hleft hr i =
            rightDegenerateCutSideIndex
              P cut horientation hleft hr j := by
        apply Fin.ext
        simpa [positiveRightChildSideIndex] using hval
      have hij :=
        rightDegenerateCutSideIndex_injective
          P cut horientation hleft hr hindex
      subst j
      rfl
    · rw [rightDegenerateMapOccurrence_selected,
        rightDegenerateMapOccurrence_retained
          P cut horientation hleft hr hg j] at hmap
      exact (oldFace_ne_rightFace P cut g
        (congrArg Sigma.fst hmap).symm).elim
  · by_cases hg : g = cut.face.face
    · subst g
      rw [rightDegenerateMapOccurrence_retained
          P cut horientation hleft hr hf i,
        rightDegenerateMapOccurrence_selected] at hmap
      exact (oldFace_ne_rightFace P cut f
        (congrArg Sigma.fst hmap)).elim
    · rw [rightDegenerateMapOccurrence_retained
          P cut horientation hleft hr hf i,
        rightDegenerateMapOccurrence_retained
          P cut horientation hleft hr hg j] at hmap
      have hface : f = g :=
        oldFace_injective P cut
          (congrArg Sigma.fst hmap)
      subst g
      have hval := congrArg
        (fun o : (split P cut).BoundaryOccurrence =>
          o.2.val) hmap
      have hij : i = j := by
        apply Fin.ext
        simpa [retainedSideIndex] using hval
      subst j
      rfl

/-- The `rightDegenerateMapPairing` declaration. -/
noncomputable def rightDegenerateMapPairing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (pairing : P.BoundaryPairing) :
    (split P cut).BoundaryPairing where
  source :=
    rightDegenerateMapOccurrence
      P cut horientation hleft hr pairing.source
  target :=
    rightDegenerateMapOccurrence
      P cut horientation hleft hr pairing.target
  source_ne_target := by
    intro h
    exact pairing.source_ne_target
      (rightDegenerateMapOccurrence_injective
        P cut horientation hleft hr h)
  source_not_boundary := by
    rw [rightDegenerateMapOccurrence_edge]
    intro hboundary
    apply pairing.source_not_boundary
    unfold IsBoundaryEdge at hboundary ⊢
    rw [edgeMultiplicity_split_castSucc P cut]
    exact hboundary
  target_not_boundary := by
    rw [rightDegenerateMapOccurrence_edge]
    intro hboundary
    apply pairing.target_not_boundary
    unfold IsBoundaryEdge at hboundary ⊢
    rw [edgeMultiplicity_split_castSucc P cut]
    exact hboundary
  direction := pairing.direction
  compatible := by
    cases hdirection : pairing.direction with
    | same =>
        have hcompatible := pairing.compatible
        rw [hdirection] at hcompatible
        change
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr pairing.target).dart =
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr pairing.source).dart
        rw [rightDegenerateMapOccurrence_dart,
          rightDegenerateMapOccurrence_dart]
        exact congrArg P1.castSuccDart hcompatible
    | opposite =>
        have hcompatible := pairing.compatible
        rw [hdirection] at hcompatible
        change
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr pairing.target).dart =
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr pairing.source).dart.flip
        rw [rightDegenerateMapOccurrence_dart,
          rightDegenerateMapOccurrence_dart]
        change
          P1.castSuccDart pairing.target.dart =
            (P1.castSuccDart pairing.source.dart).flip
        rw [← P2.castSuccDart_flip]
        exact congrArg P1.castSuccDart hcompatible

theorem rightDegeneratePreMap_pairing_eq
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        (pairing.identification.source.point t) =
      rightDegeneratePreMap
        P cut horientation hleft hr validP
        (pairing.identification.target.point
          (pairing.identification.parameter t)) := by
  rw [BoundaryPairing.identification_source,
    BoundaryPairing.identification_target,
    rightDegeneratePreMap_occurrenceSide,
    rightDegeneratePreMap_occurrenceSide]
  simpa [rightDegenerateMapPairing,
      PolygonGluing.Identification.parameter] using
    (split P cut).polygonalMk_pairing_eq
      (split_isSurfaceValid P cut validP)
      (rightDegenerateMapPairing
        P cut horientation hleft hr pairing) t

theorem rightDegeneratePreMap_respects
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {x y : P.PolygonalPreRealization}
    (hxy : P.PolygonalGluingRel validP x y) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP x =
      rightDegeneratePreMap
        P cut horientation hleft hr validP y := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      (P.polygonalIdentifications validP)) x y at hxy
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact rightDegeneratePreMap_pairing_eq
            P cut horientation hleft hr validP pairing t
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-! ### Inverse map -/

/-- Collapse the local child quotient back to the selected source face. -/
noncomputable def rightDegenerateChildGluingInvMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    DiskSquare.ParamChildGluing cut.left.length cut.right.length →
      P.PolygonalRealization validP :=
  fun q =>
    P.polygonalMk validP
      ⟨cut.face.face,
        (rightDegenerateSelectedCellHomeomorph
          P cut horientation hleft hr).symm q⟩

theorem continuous_rightDegenerateChildGluingInvMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegenerateChildGluingInvMap
      P cut horientation hleft hr validP) :=
  (P.continuous_polygonalMk validP).comp
    (continuous_sigmaMk.comp
      (rightDegenerateSelectedCellHomeomorph
        P cut horientation hleft hr).symm.continuous)

@[simp]
theorem rightDegenerateChildGluingInvMap_selectedCell
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (P.boundary cut.face.face).length) :
    rightDegenerateChildGluingInvMap
        P cut horientation hleft hr validP
        (rightDegenerateSelectedCellHomeomorph
          P cut horientation hleft hr z) =
      P.polygonalMk validP ⟨cut.face.face, z⟩ := by
  simp [rightDegenerateChildGluingInvMap]

/-- Inverse map on the selected target child. -/
noncomputable def rightDegenerateSelectedChildInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    PolygonCell
        ((split P cut).boundary
          (oldFace P cut cut.face.face)).length →
      P.PolygonalRealization validP :=
  rightDegenerateChildGluingInvMap
      P cut horientation hleft hr validP ∘
    positiveSelectedChildToGluing P cut horientation

theorem continuous_rightDegenerateSelectedChildInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegenerateSelectedChildInvFaceMap
      P cut horientation hleft hr validP) :=
  (continuous_rightDegenerateChildGluingInvMap
      P cut horientation hleft hr validP).comp
    (continuous_positiveSelectedChildToGluing
      P cut horientation)

/-- Inverse map on the right target child. -/
noncomputable def rightDegenerateRightChildInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    PolygonCell
        ((split P cut).boundary (rightFace P cut)).length →
      P.PolygonalRealization validP :=
  rightDegenerateChildGluingInvMap
      P cut horientation hleft hr validP ∘
    positiveRightChildToGluing P cut horientation

theorem continuous_rightDegenerateRightChildInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegenerateRightChildInvFaceMap
      P cut horientation hleft hr validP) :=
  (continuous_rightDegenerateChildGluingInvMap
      P cut horientation hleft hr validP).comp
    (continuous_positiveRightChildToGluing
      P cut horientation)

/-- Inverse map at an old target-face position. -/
noncomputable def rightDegenerateOldInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    PolygonCell
        ((split P cut).boundary (oldFace P cut f)).length →
      P.PolygonalRealization validP := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    exact rightDegenerateSelectedChildInvFaceMap
      P cut horientation hleft hr validP
  · exact retainedInvFaceMap P cut hface validP

theorem continuous_rightDegenerateOldInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    Continuous (rightDegenerateOldInvFaceMap
      P cut horientation hleft hr validP f) := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    simpa [rightDegenerateOldInvFaceMap] using
      continuous_rightDegenerateSelectedChildInvFaceMap
        P cut horientation hleft hr validP
  · simpa [rightDegenerateOldInvFaceMap, hface] using
      continuous_retainedInvFaceMap P cut hface validP

/-- Inverse face map indexed before applying the target `faceEquiv`. -/
noncomputable def rightDegenerateIndexedInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (j : Fin (P.faces.length + 1)) :
    PolygonCell
        ((split P cut).boundary (faceEquiv P cut j)).length →
      P.PolygonalRealization validP :=
  Fin.lastCases
    (rightDegenerateRightChildInvFaceMap
      P cut horientation hleft hr validP)
    (fun f =>
      rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP f)
    j

@[simp]
theorem rightDegenerateIndexedInvFaceMap_last
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    rightDegenerateIndexedInvFaceMap
        P cut horientation hleft hr validP (Fin.last P.faces.length) =
      rightDegenerateRightChildInvFaceMap
        P cut horientation hleft hr validP :=
  Fin.lastCases_last

@[simp]
theorem rightDegenerateIndexedInvFaceMap_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    rightDegenerateIndexedInvFaceMap
        P cut horientation hleft hr validP f.castSucc =
      rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP f :=
  Fin.lastCases_castSucc f

theorem continuous_rightDegenerateIndexedInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (j : Fin (P.faces.length + 1)) :
    Continuous (rightDegenerateIndexedInvFaceMap
      P cut horientation hleft hr validP j) := by
  induction j using Fin.lastCases with
  | last =>
      rw [rightDegenerateIndexedInvFaceMap_last]
      exact continuous_rightDegenerateRightChildInvFaceMap
        P cut horientation hleft hr validP
  | cast f =>
      rw [rightDegenerateIndexedInvFaceMap_castSucc]
      exact continuous_rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP f

/-- Inverse face map on the actual target face type. -/
noncomputable def rightDegenerateInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).Face) :
    PolygonCell ((split P cut).boundary q).length →
      P.PolygonalRealization validP := by
  let j := (faceEquiv P cut).symm q
  have hq : faceEquiv P cut j = q :=
    (faceEquiv P cut).apply_symm_apply q
  exact hq ▸ rightDegenerateIndexedInvFaceMap
    P cut horientation hleft hr validP j

theorem continuous_rightDegenerateInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).Face) :
    Continuous (rightDegenerateInvFaceMap
      P cut horientation hleft hr validP q) := by
  let j := (faceEquiv P cut).symm q
  have hq : faceEquiv P cut j = q :=
    (faceEquiv P cut).apply_symm_apply q
  change Continuous (hq ▸ rightDegenerateIndexedInvFaceMap
    P cut horientation hleft hr validP j)
  cases hq
  exact continuous_rightDegenerateIndexedInvFaceMap
    P cut horientation hleft hr validP j

@[simp]
theorem rightDegenerateInvFaceMap_oldFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    rightDegenerateInvFaceMap P cut horientation hleft hr validP
        (oldFace P cut f) =
      rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP f := by
  unfold rightDegenerateInvFaceMap
  dsimp only
  have hj :
      (faceEquiv P cut).symm (oldFace P cut f) = f.castSucc :=
    (faceEquiv P cut).symm_apply_eq.mpr rfl
  cases hj
  exact rightDegenerateIndexedInvFaceMap_castSucc
    P cut horientation hleft hr validP f

@[simp]
theorem rightDegenerateInvFaceMap_rightFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    rightDegenerateInvFaceMap P cut horientation hleft hr validP
        (rightFace P cut) =
      rightDegenerateRightChildInvFaceMap
        P cut horientation hleft hr validP := by
  unfold rightDegenerateInvFaceMap
  dsimp only
  have hj :
      (faceEquiv P cut).symm (rightFace P cut) =
        Fin.last P.faces.length :=
    (faceEquiv P cut).symm_apply_eq.mpr rfl
  cases hj
  exact rightDegenerateIndexedInvFaceMap_last
    P cut horientation hleft hr validP

/-- Continuous inverse map on the complete split polygonal pre-realization. -/
noncomputable def rightDegenerateInvPreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    (split P cut).PolygonalPreRealization →
      P.PolygonalRealization validP :=
  fun x => rightDegenerateInvFaceMap
    P cut horientation hleft hr validP x.1 x.2

theorem continuous_rightDegenerateInvPreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegenerateInvPreMap
      P cut horientation hleft hr validP) := by
  apply continuous_sigma
  exact continuous_rightDegenerateInvFaceMap
    P cut horientation hleft hr validP

@[simp]
theorem rightDegenerateInvPreMap_oldFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (z : PolygonCell
      ((split P cut).boundary (oldFace P cut f)).length) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨oldFace P cut f, z⟩ =
      rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP f z := by
  simp [rightDegenerateInvPreMap]

@[simp]
theorem rightDegenerateInvPreMap_rightFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell
      ((split P cut).boundary (rightFace P cut)).length) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨rightFace P cut, z⟩ =
      rightDegenerateRightChildInvFaceMap
        P cut horientation hleft hr validP z := by
  simp [rightDegenerateInvPreMap]

@[simp]
theorem rightDegenerateOldInvFaceMap_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP cut.face.face =
      rightDegenerateSelectedChildInvFaceMap
        P cut horientation hleft hr validP := by
  simp [rightDegenerateOldInvFaceMap]

@[simp]
theorem rightDegenerateOldInvFaceMap_retained
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face) :
    rightDegenerateOldInvFaceMap
        P cut horientation hleft hr validP f =
      retainedInvFaceMap P cut hface validP := by
  simp [rightDegenerateOldInvFaceMap, hface]

@[simp]
theorem rightDegenerateSelectedChildInvFaceMap_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (cut.left.length + 1)) :
    rightDegenerateSelectedChildInvFaceMap
        P cut horientation hleft hr validP
        (positiveSelectedChildCellHomeomorph
          P cut horientation z) =
      rightDegenerateChildGluingInvMap
        P cut horientation hleft hr validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length)
          (.inl z)) := by
  simp [rightDegenerateSelectedChildInvFaceMap, Function.comp_apply]

@[simp]
theorem rightDegenerateRightChildInvFaceMap_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (cut.right.length + 1)) :
    rightDegenerateRightChildInvFaceMap
        P cut horientation hleft hr validP
        (positiveRightChildCellHomeomorph
          P cut horientation z) =
      rightDegenerateChildGluingInvMap
        P cut horientation hleft hr validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length)
          (.inr z)) := by
  simp [rightDegenerateRightChildInvFaceMap, Function.comp_apply]

theorem rightDegenerateInvPreMap_retained_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (z : PolygonCell (P.boundary f).length) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨oldFace P cut f,
          retainedCellHomeomorph P cut hface z⟩ =
      P.polygonalMk validP ⟨f, z⟩ := by
  rw [rightDegenerateInvPreMap_oldFace,
    rightDegenerateOldInvFaceMap_retained
      P cut horientation hleft hr validP hface,
    retainedInvFaceMap_apply]

theorem rightDegenerateInvPreMap_selectedChild_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (cut.left.length + 1)) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨oldFace P cut cut.face.face,
          positiveSelectedChildCellHomeomorph
            P cut horientation z⟩ =
      rightDegenerateChildGluingInvMap
        P cut horientation hleft hr validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length)
          (.inl z)) := by
  rw [rightDegenerateInvPreMap_oldFace,
    rightDegenerateOldInvFaceMap_selected,
    rightDegenerateSelectedChildInvFaceMap_apply]

theorem rightDegenerateInvPreMap_rightChild_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (cut.right.length + 1)) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨rightFace P cut,
          positiveRightChildCellHomeomorph
            P cut horientation z⟩ =
      rightDegenerateChildGluingInvMap
        P cut horientation hleft hr validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length)
          (.inr z)) := by
  rw [rightDegenerateInvPreMap_rightFace,
    rightDegenerateRightChildInvFaceMap_apply]

/-- The inverse pre-map identifies the fresh target seam. -/
theorem rightDegenerateInvPreMap_fresh_seam
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (t : unitInterval) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨oldFace P cut cut.face.face,
          positiveSelectedChildCellHomeomorph P cut horientation
            (PolygonCell.side (Fin.last cut.left.length) t)⟩ =
      rightDegenerateInvPreMap P cut horientation hleft hr validP
        ⟨rightFace P cut,
          positiveRightChildCellHomeomorph P cut horientation
            (PolygonCell.side (0 : Fin (cut.right.length + 1))
              (unitInterval.symm t))⟩ := by
  rw [rightDegenerateInvPreMap_selectedChild_apply,
    rightDegenerateInvPreMap_rightChild_apply]
  apply congrArg
    (rightDegenerateChildGluingInvMap
      P cut horientation hleft hr validP)
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _
    (DiskSquare.ParamChildSeamGenerator.glue t)

/-- On every old boundary side, the inverse pre-map exactly undoes occurrence transport. -/
theorem rightDegenerateInvPreMap_mapOccurrence_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (t : unitInterval) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        (((split P cut).occurrenceSide
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr o)).point t) =
      P.polygonalMk validP ((P.occurrenceSide o).point t) := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    rw [rightDegenerateMapOccurrence_selected]
    change
      rightDegenerateInvPreMap P cut horientation hleft hr validP
          ⟨rightFace P cut,
            PolygonCell.side
              (positiveRightChildSideIndex P cut horientation
                ((rightDegenerateCutSideIndex
                  P cut horientation hleft hr i).addNat 1)) t⟩ =
        P.polygonalMk validP
          ⟨cut.face.face, PolygonCell.side i t⟩
    rw [← positiveRightChildCellHomeomorph_side
        P cut horientation
        ((rightDegenerateCutSideIndex
          P cut horientation hleft hr i).addNat 1) t,
      rightDegenerateInvPreMap_rightChild_apply,
      ← rightDegenerateSelectedCellHomeomorph_side
        P cut horientation hleft hr i t,
      rightDegenerateChildGluingInvMap_selectedCell]
  · rw [rightDegenerateMapOccurrence_retained
        P cut horientation hleft hr hface i]
    change
      rightDegenerateInvPreMap P cut horientation hleft hr validP
          ⟨oldFace P cut f,
            PolygonCell.side (retainedSideIndex P cut hface i) t⟩ =
        P.polygonalMk validP ⟨f, PolygonCell.side i t⟩
    rw [← retainedCellHomeomorph_side P cut hface i t,
      rightDegenerateInvPreMap_retained_apply]

/-- Every target occurrence on an old edge is the transported copy of a source occurrence.
The selected monogon and index zero of the right child are exactly the fresh seam. -/
theorem exists_rightDegenerateMapOccurrence_eq_of_edge_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (q : (split P cut).BoundaryOccurrence) (e : P.Edge)
    (hedge : q.edge = e.castSucc) :
    ∃ o : P.BoundaryOccurrence,
      rightDegenerateMapOccurrence
        P cut horientation hleft hr o = q := by
  classical
  rcases q with ⟨qf, j⟩
  rcases face_cases P cut qf with ⟨f, rfl⟩ | rfl
  · by_cases hface : f = cut.face.face
    · subst f
      have hjval : j.val = cut.left.length := by
        have hlen :=
          positive_split_boundary_selected_length
            P cut horientation
        have hjlt := j.isLt
        have hzero := leftLength_eq_zero hleft
        omega
      have hqfresh :
          (show (split P cut).BoundaryOccurrence from
            ⟨oldFace P cut cut.face.face, j⟩) =
            positiveSelectedFreshOccurrence
              P cut horientation := by
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          exact hjval
      have hqedge := congrArg BoundaryOccurrence.edge hqfresh
      rw [positiveSelectedFreshOccurrence_edge] at hqedge
      have hbad : e.castSucc = freshEdge P :=
        hedge.symm.trans hqedge
      exact (P1.firstSubedge_ne_freshEdge e hbad).elim
    · let i : Fin (P.boundary f).length :=
        ⟨j.val, by
          rw [← split_boundary_old_length_of_ne P cut hface]
          exact j.isLt⟩
      refine ⟨⟨f, i⟩, ?_⟩
      rw [rightDegenerateMapOccurrence_retained
        P cut horientation hleft hr hface i]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Fin.ext
        rfl
  · by_cases hj : j.val = 0
    · have hqfresh :
          (show (split P cut).BoundaryOccurrence from
            ⟨rightFace P cut, j⟩) =
            positiveRightFreshOccurrence P cut horientation := by
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          exact hj
      have hqedge := congrArg BoundaryOccurrence.edge hqfresh
      rw [positiveRightFreshOccurrence_edge] at hqedge
      have hbad : e.castSucc = freshEdge P :=
        hedge.symm.trans hqedge
      exact (P1.firstSubedge_ne_freshEdge e hbad).elim
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
      let rightIndex : Fin cut.right.length :=
        ⟨j.val - 1, by
          have hlen :=
            positive_split_boundary_right_length
              P cut horientation
          have hjlt := j.isLt
          omega⟩
      obtain ⟨i, hi⟩ :=
        rightDegenerateCutSideIndex_surjective
          P cut horientation hleft hr rightIndex
      refine ⟨⟨cut.face.face, i⟩, ?_⟩
      rw [rightDegenerateMapOccurrence_selected]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Fin.ext
        simp only [positiveRightChildSideIndex,
          Fin.val_addNat]
        rw [hi]
        simp only [rightIndex]
        omega

/-- A target pairing based at an old edge is exactly the transported source pairing. -/
theorem exists_rightDegenerateMapPairing_eq_of_source_edge_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).BoundaryPairing) (e : P.Edge)
    (hsourceEdge : q.source.edge = e.castSucc) :
    ∃ r : P.BoundaryPairing,
      rightDegenerateMapPairing
        P cut horientation hleft hr r = q := by
  have htargetEdge : q.target.edge = e.castSucc :=
    (targetPairing_edge_eq_source_edge q).trans hsourceEdge
  obtain ⟨source, hsource⟩ :=
    exists_rightDegenerateMapOccurrence_eq_of_edge_castSucc
      P cut horientation hleft hr q.source e hsourceEdge
  obtain ⟨target, htarget⟩ :=
    exists_rightDegenerateMapOccurrence_eq_of_edge_castSucc
      P cut horientation hleft hr q.target e htargetEdge
  have hsourceOldEdge : source.edge = e := by
    have hmapEdge :=
      congrArg BoundaryOccurrence.edge hsource
    rw [rightDegenerateMapOccurrence_edge, hsourceEdge] at hmapEdge
    exact Fin.castSucc_injective P.edgeCount hmapEdge
  have htargetOldEdge : target.edge = e := by
    have hmapEdge :=
      congrArg BoundaryOccurrence.edge htarget
    rw [rightDegenerateMapOccurrence_edge, htargetEdge] at hmapEdge
    exact Fin.castSucc_injective P.edgeCount hmapEdge
  have heInternal : ¬P.IsBoundaryEdge e := by
    intro heBoundary
    apply q.source_not_boundary
    unfold IsBoundaryEdge at heBoundary ⊢
    rw [hsourceEdge]
    exact
      (edgeMultiplicity_split_castSucc P cut e).symm.trans
        heBoundary
  have hsourceInternal : ¬P.IsBoundaryEdge source.edge := by
    rw [hsourceOldEdge]
    exact heInternal
  obtain ⟨r, hrsource⟩ :=
    validP.exists_pairing_source source hsourceInternal
  obtain ⟨_partner, _hpartner, hunique⟩ :=
    validP.exists_unique_partner source hsourceInternal
  have hsourceneTarget : source ≠ target := by
    intro heq
    apply q.source_ne_target
    calc
      q.source =
          rightDegenerateMapOccurrence
            P cut horientation hleft hr source :=
        hsource.symm
      _ = rightDegenerateMapOccurrence
            P cut horientation hleft hr target :=
        congrArg
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr) heq
      _ = q.target := htarget
  have hrcondition :
      source ≠ r.target ∧ r.target.edge = source.edge := by
    constructor
    · intro heq
      exact r.source_ne_target (hrsource.trans heq)
    · calc
        r.target.edge = r.source.edge :=
          targetPairing_edge_eq_source_edge r
        _ = source.edge :=
          congrArg BoundaryOccurrence.edge hrsource
  have htcondition :
      source ≠ target ∧ target.edge = source.edge :=
    ⟨hsourceneTarget,
      htargetOldEdge.trans hsourceOldEdge.symm⟩
  have hrtarget : r.target = target :=
    (hunique r.target hrcondition).trans
      (hunique target htcondition).symm
  have hmapSource :
      (rightDegenerateMapPairing
        P cut horientation hleft hr r).source = q.source := by
    change
      rightDegenerateMapOccurrence
          P cut horientation hleft hr r.source = q.source
    rw [hrsource, hsource]
  have hmapTarget :
      (rightDegenerateMapPairing
        P cut horientation hleft hr r).target = q.target := by
    change
      rightDegenerateMapOccurrence
          P cut horientation hleft hr r.target = q.target
    rw [hrtarget, htarget]
  have hmapDirection :
      (rightDegenerateMapPairing
        P cut horientation hleft hr r).direction = q.direction :=
    targetPairing_direction_eq_of_source_target_eq
      (rightDegenerateMapPairing
        P cut horientation hleft hr r) q
      hmapSource hmapTarget
  exact ⟨r,
    targetPairing_eq_of_source_target_direction_eq
      (rightDegenerateMapPairing
        P cut horientation hleft hr r) q
      hmapSource hmapTarget hmapDirection⟩

/-- Occurrence-side form of the exact fresh-seam equality. -/
theorem rightDegenerateInvPreMap_fresh_occurrence_seam
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (t : unitInterval) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        (((split P cut).occurrenceSide
          (positiveSelectedFreshOccurrence
            P cut horientation)).point t) =
      rightDegenerateInvPreMap P cut horientation hleft hr validP
        (((split P cut).occurrenceSide
          (positiveRightFreshOccurrence
            P cut horientation)).point
              (unitInterval.symm t)) := by
  rw [← positiveChildPairPreMap_fresh_inl
      P cut horientation t,
    ← positiveChildPairPreMap_fresh_inr
      P cut horientation (unitInterval.symm t)]
  exact rightDegenerateInvPreMap_fresh_seam
    P cut horientation hleft hr validP t

/-- The inverse pre-map identifies every target gluing generator. -/
theorem rightDegenerateInvPreMap_pairing_eq
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).BoundaryPairing) (t : unitInterval) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP
        (q.identification.source.point t) =
      rightDegenerateInvPreMap P cut horientation hleft hr validP
        (q.identification.target.point
          (q.identification.parameter t)) := by
  let edge : Fin (P.edgeCount + 1) := q.source.edge
  have hsourceEdge : q.source.edge = edge := rfl
  refine Fin.lastCases
    (motive := fun edge : Fin (P.edgeCount + 1) =>
      q.source.edge = edge →
        rightDegenerateInvPreMap
            P cut horientation hleft hr validP
            (q.identification.source.point t) =
          rightDegenerateInvPreMap
            P cut horientation hleft hr validP
            (q.identification.target.point
              (q.identification.parameter t)))
    ?_ (fun e hedge ↦ ?_) edge hsourceEdge
  · intro hedge
    have hfresh : q.source.edge = freshEdge P := by
      simpa only [freshEdge, P1.freshEdge] using hedge
    have htargetFresh : q.target.edge = freshEdge P :=
      (targetPairing_edge_eq_source_edge q).trans hfresh
    rcases positiveFreshOccurrence_cases
        P cut horientation validP q.source hfresh with
      hsourceSelected | hsourceRight
    · rcases positiveFreshOccurrence_cases
          P cut horientation validP q.target htargetFresh with
        htargetSelected | htargetRight
      · exact (q.source_ne_target
          (hsourceSelected.trans htargetSelected.symm)).elim
      · have hdirection : q.direction = .opposite := by
          cases hdirection : q.direction with
          | same =>
              have hcompatible := q.compatible
              rw [hdirection, hsourceSelected, htargetRight,
                positiveRightFreshOccurrence_dart,
                positiveSelectedFreshOccurrence_dart] at hcompatible
              cases hcompatible
          | opposite => rfl
        rw [BoundaryPairing.identification_source,
          BoundaryPairing.identification_target]
        simpa [hsourceSelected, htargetRight, hdirection,
            PolygonGluing.Identification.parameter,
            PolygonGluing.ParameterDirection.homeomorph_opposite_apply] using
          rightDegenerateInvPreMap_fresh_occurrence_seam
            P cut horientation hleft hr validP t
    · rcases positiveFreshOccurrence_cases
          P cut horientation validP q.target htargetFresh with
        htargetSelected | htargetRight
      · have hdirection : q.direction = .opposite := by
          cases hdirection : q.direction with
          | same =>
              have hcompatible := q.compatible
              rw [hdirection, hsourceRight, htargetSelected,
                positiveSelectedFreshOccurrence_dart,
                positiveRightFreshOccurrence_dart] at hcompatible
              cases hcompatible
          | opposite => rfl
        rw [BoundaryPairing.identification_source,
          BoundaryPairing.identification_target]
        simpa [hsourceRight, htargetSelected, hdirection,
            PolygonGluing.Identification.parameter,
            PolygonGluing.ParameterDirection.homeomorph_opposite_apply] using
          (rightDegenerateInvPreMap_fresh_occurrence_seam
            P cut horientation hleft hr validP
            (unitInterval.symm t)).symm
      · exact (q.source_ne_target
          (hsourceRight.trans htargetRight.symm)).elim
  · obtain ⟨r, hrPairing⟩ :=
      exists_rightDegenerateMapPairing_eq_of_source_edge_castSucc
        P cut horientation hleft hr validP q e hedge
    rw [← hrPairing, BoundaryPairing.identification_source,
      BoundaryPairing.identification_target]
    change
      rightDegenerateInvPreMap
          P cut horientation hleft hr validP
          (((split P cut).occurrenceSide
            (rightDegenerateMapOccurrence
              P cut horientation hleft hr r.source)).point t) =
        rightDegenerateInvPreMap
          P cut horientation hleft hr validP
          (((split P cut).occurrenceSide
            (rightDegenerateMapOccurrence
              P cut horientation hleft hr r.target)).point
            ((rightDegenerateMapPairing
              P cut horientation hleft hr r).identification.parameter t))
    rw [rightDegenerateInvPreMap_mapOccurrence_side,
      rightDegenerateInvPreMap_mapOccurrence_side]
    simpa [rightDegenerateMapPairing,
        PolygonGluing.Identification.parameter] using
      P.polygonalMk_pairing_eq validP r t

/-- The inverse pre-map is constant on the complete target gluing relation. -/
theorem rightDegenerateInvPreMap_respects
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {x y : (split P cut).PolygonalPreRealization}
    (hxy :
      (split P cut).PolygonalGluingRel
        (split_isSurfaceValid P cut validP) x y) :
    rightDegenerateInvPreMap P cut horientation hleft hr validP x =
      rightDegenerateInvPreMap
        P cut horientation hleft hr validP y := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      ((split P cut).polygonalIdentifications
        (split_isSurfaceValid P cut validP))) x y at hxy
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact rightDegenerateInvPreMap_pairing_eq
            P cut horientation hleft hr validP pairing t
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Descended equivalence -/

/-- Forward map after descent through the source polygonal quotient. -/
noncomputable def rightDegenerateRealizationMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonalRealization validP →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  Quotient.lift
    (rightDegeneratePreMap
      P cut horientation hleft hr validP)
    (fun _ _ hxy =>
      rightDegeneratePreMap_respects
        P cut horientation hleft hr validP hxy)

/-- Inverse map after descent through the target polygonal quotient. -/
noncomputable def rightDegenerateRealizationInvMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) →
      P.PolygonalRealization validP :=
  Quotient.lift
    (rightDegenerateInvPreMap
      P cut horientation hleft hr validP)
    (fun _ _ hxy =>
      rightDegenerateInvPreMap_respects
        P cut horientation hleft hr validP hxy)

@[simp]
theorem rightDegenerateRealizationMap_polygonalMk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (x : P.PolygonalPreRealization) :
    rightDegenerateRealizationMap
        P cut horientation hleft hr validP
        (P.polygonalMk validP x) =
      rightDegeneratePreMap
        P cut horientation hleft hr validP x :=
  rfl

@[simp]
theorem rightDegenerateRealizationInvMap_polygonalMk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (y : (split P cut).PolygonalPreRealization) :
    rightDegenerateRealizationInvMap
        P cut horientation hleft hr validP
        ((split P cut).polygonalMk
          (split_isSurfaceValid P cut validP) y) =
      rightDegenerateInvPreMap
        P cut horientation hleft hr validP y :=
  rfl

/-- On the locally glued child pair, the descended inverse is the explicit collapse map. -/
theorem rightDegenerateRealizationInvMap_childGluing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : DiskSquare.ParamChildGluing
      cut.left.length cut.right.length) :
    rightDegenerateRealizationInvMap
        P cut horientation hleft hr validP
        (positiveChildGluingMap
          P cut horientation validP q) =
      rightDegenerateChildGluingInvMap
        P cut horientation hleft hr validP q := by
  induction q using Quotient.inductionOn'
  case _ x =>
    cases x with
    | inl z =>
        rw [positiveChildGluingMap_mk]
        change
          rightDegenerateInvPreMap
              P cut horientation hleft hr validP
              ⟨oldFace P cut cut.face.face,
                positiveSelectedChildCellHomeomorph
                  P cut horientation z⟩ =
            rightDegenerateChildGluingInvMap
              P cut horientation hleft hr validP
              (@Quotient.mk''
                (DiskSquare.ChildPair
                  cut.left.length cut.right.length)
                (DiskSquare.paramChildSeamSetoid
                  cut.left.length cut.right.length)
                (.inl z))
        exact rightDegenerateInvPreMap_selectedChild_apply
          P cut horientation hleft hr validP z
    | inr z =>
        rw [positiveChildGluingMap_mk]
        change
          rightDegenerateInvPreMap
              P cut horientation hleft hr validP
              ⟨rightFace P cut,
                positiveRightChildCellHomeomorph
                  P cut horientation z⟩ =
            rightDegenerateChildGluingInvMap
              P cut horientation hleft hr validP
              (@Quotient.mk''
                (DiskSquare.ChildPair
                  cut.left.length cut.right.length)
                (DiskSquare.paramChildSeamSetoid
                  cut.left.length cut.right.length)
                (.inr z))
        exact rightDegenerateInvPreMap_rightChild_apply
          P cut horientation hleft hr validP z

/-- The descended forward map sends the child-collapse class back to the same local quotient. -/
theorem rightDegenerateRealizationMap_childGluingInv
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : DiskSquare.ParamChildGluing
      cut.left.length cut.right.length) :
    rightDegenerateRealizationMap
        P cut horientation hleft hr validP
        (rightDegenerateChildGluingInvMap
          P cut horientation hleft hr validP q) =
      positiveChildGluingMap P cut horientation validP q := by
  rw [rightDegenerateChildGluingInvMap,
    rightDegenerateRealizationMap_polygonalMk,
    rightDegeneratePreMap_selected]
  simp [rightDegenerateSelectedFaceMap, Function.comp_apply]

/-- The descended inverse is a left inverse on every source pre-realization point. -/
theorem rightDegenerateRealization_left_inverse_mk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (x : P.PolygonalPreRealization) :
    rightDegenerateRealizationInvMap
        P cut horientation hleft hr validP
        (rightDegeneratePreMap
          P cut horientation hleft hr validP x) =
      P.polygonalMk validP x := by
  rcases x with ⟨f, z⟩
  by_cases hface : f = cut.face.face
  · subst f
    rw [rightDegeneratePreMap_selected]
    change
      rightDegenerateRealizationInvMap
          P cut horientation hleft hr validP
          (positiveChildGluingMap P cut horientation validP
            (rightDegenerateSelectedCellHomeomorph
              P cut horientation hleft hr z)) =
        P.polygonalMk validP ⟨cut.face.face, z⟩
    rw [rightDegenerateRealizationInvMap_childGluing,
      rightDegenerateChildGluingInvMap_selectedCell]
  · rw [rightDegeneratePreMap_retained
        P cut horientation hleft hr validP hface,
      retainedFaceMap,
      rightDegenerateRealizationInvMap_polygonalMk,
      rightDegenerateInvPreMap_retained_apply]

/-- The descended forward map is a right inverse on every target pre-realization point. -/
theorem rightDegenerateRealization_right_inverse_mk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (y : (split P cut).PolygonalPreRealization) :
    rightDegenerateRealizationMap
        P cut horientation hleft hr validP
        (rightDegenerateInvPreMap
          P cut horientation hleft hr validP y) =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP) y := by
  rcases y with ⟨q, z⟩
  rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
  · by_cases hface : f = cut.face.face
    · subst f
      rw [rightDegenerateInvPreMap_oldFace,
        rightDegenerateOldInvFaceMap_selected]
      change
        rightDegenerateRealizationMap
            P cut horientation hleft hr validP
            (rightDegenerateChildGluingInvMap
              P cut horientation hleft hr validP
              (positiveSelectedChildToGluing
                P cut horientation z)) =
          (split P cut).polygonalMk
            (split_isSurfaceValid P cut validP)
            ⟨oldFace P cut cut.face.face, z⟩
      rw [rightDegenerateRealizationMap_childGluingInv,
        positiveChildGluingMap_selectedChildToGluing]
    · rw [rightDegenerateInvPreMap_oldFace,
        rightDegenerateOldInvFaceMap_retained
          P cut horientation hleft hr validP hface]
      change
        rightDegenerateRealizationMap
            P cut horientation hleft hr validP
            (P.polygonalMk validP
              ⟨f, (retainedCellHomeomorph
                P cut hface).symm z⟩) =
          (split P cut).polygonalMk
            (split_isSurfaceValid P cut validP)
            ⟨oldFace P cut f, z⟩
      rw [rightDegenerateRealizationMap_polygonalMk,
        rightDegeneratePreMap_retained
          P cut horientation hleft hr validP hface,
        retainedFaceMap]
      simp
  · rw [rightDegenerateInvPreMap_rightFace]
    change
      rightDegenerateRealizationMap
          P cut horientation hleft hr validP
          (rightDegenerateChildGluingInvMap
            P cut horientation hleft hr validP
            (positiveRightChildToGluing
              P cut horientation z)) =
        (split P cut).polygonalMk
          (split_isSurfaceValid P cut validP)
          ⟨rightFace P cut, z⟩
    rw [rightDegenerateRealizationMap_childGluingInv,
      positiveChildGluingMap_rightChildToGluing]

/-- Complete realization-equivalence data for an empty-left positive P2 split. -/
noncomputable def rightDegenerateRealizationEquivData
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    RealizationEquivData P (split P cut) validP
      (split_isSurfaceValid P cut validP) where
  toPre :=
    rightDegeneratePreMap
      P cut horientation hleft hr validP
  invPre :=
    rightDegenerateInvPreMap
      P cut horientation hleft hr validP
  continuous_toPre :=
    continuous_rightDegeneratePreMap
      P cut horientation hleft hr validP
  continuous_invPre :=
    continuous_rightDegenerateInvPreMap
      P cut horientation hleft hr validP
  to_respects := fun _ _ hxy =>
    rightDegeneratePreMap_respects
      P cut horientation hleft hr validP hxy
  inv_respects := fun _ _ hxy =>
    rightDegenerateInvPreMap_respects
      P cut horientation hleft hr validP hxy
  left_inverse_mk :=
    rightDegenerateRealization_left_inverse_mk
      P cut horientation hleft hr validP
  right_inverse_mk :=
    rightDegenerateRealization_right_inverse_mk
      P cut horientation hleft hr validP

/-- Explicit homeomorphism for an empty-left positive P2 split. -/
noncomputable def rightDegenerateRealizationHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonalRealization validP ≃ₜ
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  (rightDegenerateRealizationEquivData
    P cut horientation hleft hr validP).homeomorph

/-- Propositional realization invariance for an empty-left positive P2 split. -/
theorem rightDegeneratePolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) :=
  (rightDegenerateRealizationEquivData
    P cut horientation hleft hr validP).polygonallyEquivalent

/-! ### Transport to every one-sided-degenerate cut -/

/-- A positive cut with an empty right word reduces to the base theorem by swapping its two
displayed pieces. -/
theorem leftDegeneratePolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hright : cut.right = [])
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  have hswapOrientation :
      cut.swap.face.orientation = false := by
    simpa [P2Cut.swap] using horientation
  have hswapLeft : cut.swap.left = [] := by
    simpa [P2Cut.swap] using hright
  have hswapRight : 0 < cut.swap.right.length := by
    simpa [P2Cut.swap] using hl
  let validSwap :=
    split_isSurfaceValid P cut.swap validP
  exact
    (rightDegeneratePolygonallyEquivalent
      P cut.swap hswapOrientation hswapLeft hswapRight validP).trans
      ((swapSignedPresentationIso P cut).polygonallyEquivalent
        validSwap (split_isSurfaceValid P cut validP))

/-- Every positive one-sided-degenerate cut preserves polygonal realization. -/
theorem positiveOneSidedPolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  rcases honeSided with ⟨hleft, hr⟩ | ⟨hl, hright⟩
  · exact rightDegeneratePolygonallyEquivalent
      P cut horientation hleft hr validP
  · exact leftDegeneratePolygonallyEquivalent
      P cut horientation hl hright validP

/-- A negative one-sided cut reduces to the positive theorem after reversing the cut. -/
theorem negativeOneSidedPolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = true)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  have hflipOrientation :
      cut.flip.face.orientation = false := by
    simp [P2Cut.flip, OrientedFace.flip, horientation]
  have hflipOneSided :
      (cut.flip.left = [] ∧ 0 < cut.flip.right.length) ∨
        (0 < cut.flip.left.length ∧ cut.flip.right = []) := by
    rcases honeSided with ⟨hleft, hr⟩ | ⟨hl, hright⟩
    · right
      constructor
      · simpa [P2Cut.flip, inverseWord] using hr
      · simp [P2Cut.flip, inverseWord, hleft]
    · left
      constructor
      · simp [P2Cut.flip, inverseWord, hright]
      · simpa [P2Cut.flip, inverseWord] using hl
  let validFlip :=
    split_isSurfaceValid P cut.flip validP
  exact
    (positiveOneSidedPolygonallyEquivalent
      P cut.flip hflipOrientation hflipOneSided validP).trans
      ((flipSignedPresentationIso P cut).polygonallyEquivalent
        validFlip (split_isSurfaceValid P cut validP))

/-- Every one-sided-degenerate P2 split preserves the faithful polygonal realization,
independently of traversal orientation and of which displayed cut word is empty. -/
theorem oneSidedPolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  cases horientation : cut.face.orientation
  · exact positiveOneSidedPolygonallyEquivalent
      P cut horientation honeSided validP
  · exact negativeOneSidedPolygonallyEquivalent
      P cut horientation honeSided validP

end P2

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
