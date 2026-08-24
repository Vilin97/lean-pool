/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicDyck
import LeanPool.ClassificationOfSurfaces.FiniteCyclicUnorientedRealization

/-!
# The Gallier--Xu cross-cap rewrite

This file implements the common P2 refinement behind the pseudo-rewrite

`a X a Y  ~  b b Y⁻¹ X`.

The first source child is compared in its stored orientation and the second source child is read
backwards, exactly as in Gallier--Xu's derivation. The broader
`UnorientedPresentationIso` makes that face-orientation choice explicit; it is not hidden in the
ordinary signed edge relabeling.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Crosscap

/-- The source spelling with two equally oriented occurrences of `a`. -/
@[reducible]
def source {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (([.pos a] ++ X) ++ ([.pos a] ++ Y))

/-- A cyclic spelling of the target cross-cap word `a a Y⁻¹ X`. -/
@[reducible]
def target {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace ((X ++ [.pos a]) ++ ([.pos a] ++ inverseWord Y))

/-- Split the source between the two occurrences of `a`. -/
def sourceCut {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    P2Cut (source a X Y) where
  face := .pos 0
  left := [.pos a] ++ X
  right := [.pos a] ++ Y
  boundary_rotated := by
    change
      (([SignedDart.pos a] ++ X) ++
          ([SignedDart.pos a] ++ Y)).IsRotated
        (([SignedDart.pos a] ++ X) ++
          ([SignedDart.pos a] ++ Y))
    exact List.IsRotated.refl _

/-- Split the target along the edge used to merge the first source child with the reverse of the
second. -/
def targetCut {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    P2Cut (target a X Y) where
  face := .pos 0
  left := X ++ [.pos a]
  right := [.pos a] ++ inverseWord Y
  boundary_rotated := by
    change
      ((X ++ [SignedDart.pos a]) ++
          ([SignedDart.pos a] ++ inverseWord Y)).IsRotated
        ((X ++ [SignedDart.pos a]) ++
          ([SignedDart.pos a] ++ inverseWord Y))
    exact List.IsRotated.refl _

theorem sourceCut_isNondegenerate {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (sourceCut a X Y).IsNondegenerate := by
  constructor <;> simp [sourceCut]

theorem targetCut_isNondegenerate {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (targetCut a X Y).IsNondegenerate := by
  constructor <;> simp [targetCut]

/-- Exchange the target cross-cap edge with its fresh cutting edge. -/
def commonEdgeRelabeling {n : ℕ} (a : Fin n) :
    EdgeRelabeling (Fin (n + 1)) (Fin (n + 1)) where
  edgeEquiv := Equiv.swap a.castSucc (Fin.last n)
  reverse := fun _ ↦ false

theorem commonEdgeRelabeling_pos_old {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.pos a.castSucc) =
      .pos (Fin.last n) := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem commonEdgeRelabeling_neg_old {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.neg a.castSucc) =
      .neg (Fin.last n) := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem commonEdgeRelabeling_pos_fresh {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.pos (Fin.last n)) =
      .pos a.castSucc := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem commonEdgeRelabeling_neg_fresh {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.neg (Fin.last n)) =
      .neg a.castSucc := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart]

theorem commonEdgeRelabeling_retainWord {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n)))
    (ha : a ∉ word.map edgeOfDart) :
    (P2.retainWord word).map (commonEdgeRelabeling a).mapDart =
      P2.retainWord word := by
  induction word with
  | nil =>
      rfl
  | cons d word ih =>
      have hda : edgeOfDart d ≠ a := by
        intro h
        apply ha
        simp [h]
      have htail : a ∉ word.map edgeOfDart := by
        intro h
        exact ha (by simp [h])
      change
        (commonEdgeRelabeling a).mapDart (P1.castSuccDart d) ::
            (P2.retainWord word).map (commonEdgeRelabeling a).mapDart =
          P1.castSuccDart d :: P2.retainWord word
      rw [ih htail]
      congr 1
      cases d with
      | pos e =>
          have hcast : e.castSucc ≠ a.castSucc :=
            fun heq ↦ hda (Fin.castSucc_injective _ heq)
          simp [commonEdgeRelabeling, EdgeRelabeling.mapDart,
            Equiv.swap_apply_of_ne_of_ne hcast (Fin.castSucc_ne_last e)]
      | neg e =>
          have hcast : e.castSucc ≠ a.castSucc :=
            fun heq ↦ hda (Fin.castSucc_injective _ heq)
          simp [commonEdgeRelabeling, EdgeRelabeling.mapDart,
            Equiv.swap_apply_of_ne_of_ne hcast (Fin.castSucc_ne_last e)]

/-- Match the explicit face indices of the two canonical splits. -/
def commonFaceEquiv {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (P2.split (target a X Y) (targetCut a X Y)).Face ≃
      (P2.split (source a X Y) (sourceCut a X Y)).Face :=
  (P2.faceEquiv (target a X Y) (targetCut a X Y)).symm.trans
    (P2.faceEquiv (source a X Y) (sourceCut a X Y))

@[simp]
theorem commonFaceEquiv_selected {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    commonFaceEquiv a X Y
        (P2.oldFace (target a X Y) (targetCut a X Y) 0) =
      P2.oldFace (source a X Y) (sourceCut a X Y) 0 :=
  rfl

@[simp]
theorem commonFaceEquiv_right {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    commonFaceEquiv a X Y
        (P2.rightFace (target a X Y) (targetCut a X Y)) =
      P2.rightFace (source a X Y) (sourceCut a X Y) :=
  rfl

/-- Reverse exactly the right child of the target split. -/
def reverseCommonFace {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (q : (P2.split (target a X Y) (targetCut a X Y)).Face) : Bool :=
  decide (q = P2.rightFace (target a X Y) (targetCut a X Y))

@[simp]
theorem reverseCommonFace_selected {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    reverseCommonFace a X Y
        (P2.oldFace (target a X Y) (targetCut a X Y) 0) = false := by
  simp only [reverseCommonFace, decide_eq_false_iff_not]
  exact P2.oldFace_ne_rightFace (target a X Y) (targetCut a X Y) 0

theorem reverseCommonFace_right {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    reverseCommonFace a X Y
        (P2.rightFace (target a X Y) (targetCut a X Y)) = true := by
  simp [reverseCommonFace]

theorem split_target_boundary_selected {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (P2.split (target a X Y) (targetCut a X Y)).boundary
        (P2.oldFace (target a X Y) (targetCut a X Y) 0) =
      P2.selectedBoundary (target a X Y) (targetCut a X Y) := by
  change
    (P2.split (target a X Y) (targetCut a X Y)).boundary
        (P2.oldFace (target a X Y) (targetCut a X Y)
          (targetCut a X Y).face.face) =
      P2.selectedBoundary (target a X Y) (targetCut a X Y)
  exact P2.split_boundary_selected (target a X Y) (targetCut a X Y)

theorem split_source_boundary_selected {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (P2.split (source a X Y) (sourceCut a X Y)).boundary
        (P2.oldFace (source a X Y) (sourceCut a X Y) 0) =
      P2.selectedBoundary (source a X Y) (sourceCut a X Y) := by
  change
    (P2.split (source a X Y) (sourceCut a X Y)).boundary
        (P2.oldFace (source a X Y) (sourceCut a X Y)
          (sourceCut a X Y).face.face) =
      P2.selectedBoundary (source a X Y) (sourceCut a X Y)
  exact P2.split_boundary_selected (source a X Y) (sourceCut a X Y)

theorem split_target_boundary_right {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (P2.split (target a X Y) (targetCut a X Y)).boundary
        (P2.rightFace (target a X Y) (targetCut a X Y)) =
      P2.rightBoundary (target a X Y) (targetCut a X Y) :=
  P2.split_boundary_right (target a X Y) (targetCut a X Y)

theorem split_source_boundary_right {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (P2.split (source a X Y) (sourceCut a X Y)).boundary
        (P2.rightFace (source a X Y) (sourceCut a X Y)) =
      P2.rightBoundary (source a X Y) (sourceCut a X Y) :=
  P2.split_boundary_right (source a X Y) (sourceCut a X Y)

/-- The selected target child maps to a rotation of the selected source child. -/
theorem map_selectedBoundary_isRotated {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart) :
    ((P2.selectedBoundary (target a X Y) (targetCut a X Y)).map
      (commonEdgeRelabeling a).mapDart).IsRotated
        (P2.selectedBoundary (source a X Y) (sourceCut a X Y)) := by
  simp only [targetCut, sourceCut, OrientedFace.pos,
    P2.selectedBoundary, P2.storedWord_false,
    P2.selectedOrientedBoundary, P2.retainWord_append,
    P2.freshEdge, P1.freshEdge, List.map_append, List.map_singleton]
  rw [show P2.retainWord [SignedDart.pos a] =
      [SignedDart.pos a.castSucc] from rfl,
    List.map_singleton,
    commonEdgeRelabeling_retainWord a X haX,
    commonEdgeRelabeling_pos_old,
    commonEdgeRelabeling_pos_fresh]
  exact List.isRotated_append

/-- The right target child maps to a rotation of the reversed right source child. -/
theorem map_rightBoundary_isRotated_inverse {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haY : a ∉ Y.map edgeOfDart) :
    ((P2.rightBoundary (target a X Y) (targetCut a X Y)).map
      (commonEdgeRelabeling a).mapDart).IsRotated
        (inverseWord
          (P2.rightBoundary (source a X Y) (sourceCut a X Y))) := by
  simp only [targetCut, sourceCut, OrientedFace.pos,
    P2.rightBoundary, P2.storedWord_false,
    P2.rightOrientedBoundary, P2.retainWord_append,
    P2.freshEdge, P1.freshEdge, List.map_cons, List.map_append]
  rw [show P2.retainWord [SignedDart.pos a] =
      [SignedDart.pos a.castSucc] from rfl,
    List.map_singleton,
    commonEdgeRelabeling_neg_fresh,
    commonEdgeRelabeling_pos_old,
    commonEdgeRelabeling_retainWord a (inverseWord Y) (by
      simpa [map_edgeOfDart_inverseWord] using haY)]
  rw [show
    inverseWord
        (SignedDart.neg (Fin.last n) ::
          ([SignedDart.pos a.castSucc] ++ P2.retainWord Y)) =
      inverseWord (P2.retainWord Y) ++
        [SignedDart.neg a.castSucc, SignedDart.pos (Fin.last n)] by
    simp [inverseWord, SignedDart.flip]]
  rw [P2.retainWord_inverseWord]
  simpa only [List.cons_append, List.singleton_append, List.nil_append,
    List.append_assoc] using
    (List.isRotated_append
      (l := [SignedDart.neg a.castSucc, SignedDart.pos (Fin.last n)])
      (l' := inverseWord (P2.retainWord Y)))

/-- The two P2 refinements differ by edge relabeling and reversal of their right child face. -/
def splitUnorientedPresentationIso {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart) :
    UnorientedPresentationIso
      (P2.split (target a X Y) (targetCut a X Y))
      (P2.split (source a X Y) (sourceCut a X Y)) where
  edgeRelabeling := commonEdgeRelabeling a
  faceEquiv := commonFaceEquiv a X Y
  reverseFace := reverseCommonFace a X Y
  boundary_rotated := by
    intro q
    rcases P2.face_cases (target a X Y) (targetCut a X Y) q with
        ⟨f, rfl⟩ | rfl
    · have hf : f = 0 := by
        apply Fin.ext
        have hf' := f.isLt
        change f.val < 1 at hf'
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hf')
      subst f
      rw [commonFaceEquiv_selected, reverseCommonFace_selected,
        split_target_boundary_selected]
      change
        ((P2.selectedBoundary (target a X Y) (targetCut a X Y)).map
          (commonEdgeRelabeling a).mapDart).IsRotated
            ((P2.split (source a X Y) (sourceCut a X Y)).orientedBoundary
              (.pos (P2.oldFace (source a X Y) (sourceCut a X Y) 0)))
      rw [orientedBoundary_pos, split_source_boundary_selected]
      exact map_selectedBoundary_isRotated a X Y haX
    · rw [commonFaceEquiv_right, reverseCommonFace_right,
        split_target_boundary_right]
      change
        ((P2.rightBoundary (target a X Y) (targetCut a X Y)).map
          (commonEdgeRelabeling a).mapDart).IsRotated
            ((P2.split (source a X Y) (sourceCut a X Y)).orientedBoundary
              (.neg (P2.rightFace (source a X Y) (sourceCut a X Y))))
      rw [orientedBoundary_neg, split_source_boundary_right]
      exact map_rightBoundary_isRotated_inverse a X Y haY

/-- The Gallier--Xu cross-cap rewrite preserves faithful polygonal realizations. -/
theorem polygonallyEquivalent {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart)
    (validSource : (source a X Y).IsSurfaceValid)
    (validTarget : (target a X Y).IsSurfaceValid) :
    (source a X Y).PolygonallyEquivalent (target a X Y)
      validSource validTarget := by
  let validSourceSplit :=
    P2.split_isSurfaceValid (source a X Y) (sourceCut a X Y) validSource
  let validTargetSplit :=
    P2.split_isSurfaceValid (target a X Y) (targetCut a X Y) validTarget
  have hSource :
      (source a X Y).PolygonallyEquivalent
        (P2.split (source a X Y) (sourceCut a X Y))
        validSource validSourceSplit :=
    P2.nondegeneratePolygonallyEquivalent
      (source a X Y) (sourceCut a X Y)
      (by simp [sourceCut]) (by simp [sourceCut]) validSource
  have hTarget :
      (target a X Y).PolygonallyEquivalent
        (P2.split (target a X Y) (targetCut a X Y))
        validTarget validTargetSplit :=
    P2.nondegeneratePolygonallyEquivalent
      (target a X Y) (targetCut a X Y)
      (by simp [targetCut]) (by simp [targetCut]) validTarget
  have hCommon :
      (P2.split (target a X Y) (targetCut a X Y)).PolygonallyEquivalent
        (P2.split (source a X Y) (sourceCut a X Y))
        validTargetSplit validSourceSplit :=
    (splitUnorientedPresentationIso a X Y haX haY).polygonallyEquivalent
      validTargetSplit validSourceSplit
  exact hSource.trans (hCommon.symm.trans hTarget.symm)

end Crosscap

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
