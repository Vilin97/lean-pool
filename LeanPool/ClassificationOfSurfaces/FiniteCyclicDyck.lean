/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicMoveRealization

/-!
# The Gallier--Xu Dyck rewrite

This file implements the common-subdivision identity underlying Gallier--Xu's handle extraction
and boundary-loop grouping:

`a U V a⁻¹ X  ~  b V U b⁻¹ X`.

We retain the edge name `a` for `b`. Both one-face words split to signed-isomorphic two-face
presentations. The isomorphism exchanges the retained copy of `a` with the fresh cutting edge and
reverses the former. The side words `U`, `V`, and `X` must not use `a`; this is exactly the
side-condition available when the displayed two darts are the two occurrences of an inner edge.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Dyck

/-- A finite-cyclic presentation with one explicitly indexed face. -/
@[reducible]
def oneFace {n : ℕ} (word : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation where
  edgeCount := n
  faces := [word]

theorem oneFace_boundary_zero {n : ℕ} (word : List (SignedDart (Fin n))) :
    (oneFace word).boundary 0 = word :=
  rfl

/-- The source spelling of the Dyck rewrite. -/
@[reducible]
def source {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  oneFace (([.pos a] ++ U) ++ (V ++ [.neg a] ++ X))

/-- A cyclic spelling of the target word `a V U a⁻¹ X`, chosen so its common P2 subdivision is
definitionally transparent. -/
@[reducible]
def target {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  oneFace ((U ++ [.neg a]) ++ (X ++ [.pos a] ++ V))

/-- The P2 cut of the source word. -/
def sourceCut {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    P2Cut (source a U V X) where
  face := .pos 0
  left := [.pos a] ++ U
  right := V ++ [.neg a] ++ X
  boundary_rotated := by
    change
      (([SignedDart.pos a] ++ U) ++
          (V ++ [SignedDart.neg a] ++ X)).IsRotated
        (([SignedDart.pos a] ++ U) ++
          (V ++ [SignedDart.neg a] ++ X))
    exact List.IsRotated.refl _

/-- The P2 cut of the cyclic target spelling. -/
def targetCut {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    P2Cut (target a U V X) where
  face := .pos 0
  left := U ++ [.neg a]
  right := X ++ [.pos a] ++ V
  boundary_rotated := by
    change
      ((U ++ [SignedDart.neg a]) ++
          (X ++ [SignedDart.pos a] ++ V)).IsRotated
        ((U ++ [SignedDart.neg a]) ++
          (X ++ [SignedDart.pos a] ++ V))
    exact List.IsRotated.refl _

theorem sourceCut_isNondegenerate {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (sourceCut a U V X).IsNondegenerate := by
  constructor <;> simp [sourceCut]

theorem targetCut_isNondegenerate {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (targetCut a U V X).IsNondegenerate := by
  constructor <;> simp [targetCut]

/-- Exchange the old edge `a` with the fresh P2 edge, reversing the old edge. -/
def commonEdgeRelabeling {n : ℕ} (a : Fin n) :
    EdgeRelabeling (Fin (n + 1)) (Fin (n + 1)) where
  edgeEquiv := Equiv.swap a.castSucc (Fin.last n)
  reverse := fun e ↦ e = a.castSucc

@[simp]
theorem commonEdgeRelabeling_pos_old {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.pos a.castSucc) =
      .neg (Fin.last n) := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem commonEdgeRelabeling_neg_old {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.neg a.castSucc) =
      .pos (Fin.last n) := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem commonEdgeRelabeling_pos_fresh {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.pos (Fin.last n)) =
      .pos a.castSucc := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart,
    (Fin.castSucc_ne_last a).symm]

@[simp]
theorem commonEdgeRelabeling_neg_fresh {n : ℕ} (a : Fin n) :
    (commonEdgeRelabeling a).mapDart (.neg (Fin.last n)) =
      .neg a.castSucc := by
  simp [commonEdgeRelabeling, EdgeRelabeling.mapDart,
    (Fin.castSucc_ne_last a).symm]

theorem commonEdgeRelabeling_castSucc_of_ne {n : ℕ} (a e : Fin n)
    (h : e ≠ a) (orientation : Bool) :
    (commonEdgeRelabeling a).mapDart
        (if orientation then .neg e.castSucc else .pos e.castSucc) =
      if orientation then .neg e.castSucc else .pos e.castSucc := by
  have hcast : e.castSucc ≠ a.castSucc :=
    fun heq ↦ h (Fin.castSucc_injective _ heq)
  have hfresh : e.castSucc ≠ Fin.last n :=
    Fin.castSucc_ne_last e
  cases orientation <;>
    simp [commonEdgeRelabeling, EdgeRelabeling.mapDart, hcast,
      Equiv.swap_apply_of_ne_of_ne hcast hfresh]

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
          exact commonEdgeRelabeling_castSucc_of_ne a e hda false
      | neg e =>
          exact commonEdgeRelabeling_castSucc_of_ne a e hda true

/-- Match the explicit face indices of the two canonical splits. -/
def commonFaceEquiv {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (P2.split (target a U V X) (targetCut a U V X)).Face ≃
      (P2.split (source a U V X) (sourceCut a U V X)).Face :=
  (P2.faceEquiv (target a U V X) (targetCut a U V X)).symm.trans
    (P2.faceEquiv (source a U V X) (sourceCut a U V X))

@[simp]
theorem commonFaceEquiv_selected {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    commonFaceEquiv a U V X
        (P2.oldFace (target a U V X) (targetCut a U V X) 0) =
      P2.oldFace (source a U V X) (sourceCut a U V X) 0 :=
  rfl

theorem commonFaceEquiv_right {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    commonFaceEquiv a U V X
        (P2.rightFace (target a U V X) (targetCut a U V X)) =
      P2.rightFace (source a U V X) (sourceCut a U V X) :=
  rfl

theorem split_target_boundary_selected {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (P2.split (target a U V X) (targetCut a U V X)).boundary
        (P2.oldFace (target a U V X) (targetCut a U V X) 0) =
      P2.selectedBoundary (target a U V X) (targetCut a U V X) := by
  change
    (P2.split (target a U V X) (targetCut a U V X)).boundary
        (P2.oldFace (target a U V X) (targetCut a U V X)
          (targetCut a U V X).face.face) =
      P2.selectedBoundary (target a U V X) (targetCut a U V X)
  exact P2.split_boundary_selected (target a U V X) (targetCut a U V X)

theorem split_source_boundary_selected {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (P2.split (source a U V X) (sourceCut a U V X)).boundary
        (P2.oldFace (source a U V X) (sourceCut a U V X) 0) =
      P2.selectedBoundary (source a U V X) (sourceCut a U V X) := by
  change
    (P2.split (source a U V X) (sourceCut a U V X)).boundary
        (P2.oldFace (source a U V X) (sourceCut a U V X)
          (sourceCut a U V X).face.face) =
      P2.selectedBoundary (source a U V X) (sourceCut a U V X)
  exact P2.split_boundary_selected (source a U V X) (sourceCut a U V X)

theorem split_target_boundary_right {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (P2.split (target a U V X) (targetCut a U V X)).boundary
        (P2.rightFace (target a U V X) (targetCut a U V X)) =
      P2.rightBoundary (target a U V X) (targetCut a U V X) :=
  P2.split_boundary_right (target a U V X) (targetCut a U V X)

theorem split_source_boundary_right {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    (P2.split (source a U V X) (sourceCut a U V X)).boundary
        (P2.rightFace (source a U V X) (sourceCut a U V X)) =
      P2.rightBoundary (source a U V X) (sourceCut a U V X) :=
  P2.split_boundary_right (source a U V X) (sourceCut a U V X)

/-- The selected target child maps to a cyclic rotation of the selected source child. -/
theorem map_selectedBoundary_isRotated {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart) :
    ((P2.selectedBoundary (target a U V X) (targetCut a U V X)).map
      (commonEdgeRelabeling a).mapDart).IsRotated
        (P2.selectedBoundary (source a U V X) (sourceCut a U V X)) := by
  simp only [targetCut, sourceCut,
    OrientedFace.pos, P2.selectedBoundary, P2.storedWord_false,
    P2.selectedOrientedBoundary, P2.retainWord_append,
    P2.freshEdge, P1.freshEdge, List.map_append, List.map_singleton]
  rw [show P2.retainWord [SignedDart.neg a] =
      [SignedDart.neg a.castSucc] from rfl,
    show P2.retainWord [SignedDart.pos a] =
      [SignedDart.pos a.castSucc] from rfl,
    List.map_singleton,
    commonEdgeRelabeling_retainWord a U haU,
    commonEdgeRelabeling_neg_old,
    commonEdgeRelabeling_pos_fresh]
  exact List.isRotated_append

/-- The right target child maps to a cyclic rotation of the right source child. -/
theorem map_rightBoundary_isRotated {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart) :
    ((P2.rightBoundary (target a U V X) (targetCut a U V X)).map
      (commonEdgeRelabeling a).mapDart).IsRotated
        (P2.rightBoundary (source a U V X) (sourceCut a U V X)) := by
  simp only [targetCut, sourceCut,
    OrientedFace.pos, P2.rightBoundary, P2.storedWord_false,
    P2.rightOrientedBoundary, P2.retainWord_append,
    P2.freshEdge, P1.freshEdge, List.map_cons, List.map_append]
  rw [show P2.retainWord [SignedDart.pos a] =
      [SignedDart.pos a.castSucc] from rfl,
    show P2.retainWord [SignedDart.neg a] =
      [SignedDart.neg a.castSucc] from rfl,
    List.map_singleton,
    commonEdgeRelabeling_neg_fresh,
    commonEdgeRelabeling_retainWord a X haX,
    commonEdgeRelabeling_pos_old,
    commonEdgeRelabeling_retainWord a V haV]
  simpa only [List.cons_append, List.singleton_append, List.nil_append,
    List.append_assoc] using
    (List.isRotated_append
      (l := SignedDart.neg a.castSucc :: P2.retainWord X)
      (l' := SignedDart.neg (Fin.last n) :: P2.retainWord V))

/-- The two canonical P2 splits in the Dyck rewrite differ only by signed edge relabeling. -/
def splitSignedPresentationIso {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart) :
    SignedPresentationIso
      (P2.split (target a U V X) (targetCut a U V X))
      (P2.split (source a U V X) (sourceCut a U V X)) where
  edgeRelabeling := commonEdgeRelabeling a
  faceEquiv := commonFaceEquiv a U V X
  boundary_rotated := by
    intro q
    rcases P2.face_cases (target a U V X) (targetCut a U V X) q with
      ⟨f, rfl⟩ | rfl
    · have hf : f = 0 := by
        apply Fin.ext
        have hf' := f.isLt
        change f.val < 1 at hf'
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hf')
      subst f
      rw [commonFaceEquiv_selected,
        split_target_boundary_selected,
        split_source_boundary_selected]
      exact map_selectedBoundary_isRotated a U V X haU
    · rw [commonFaceEquiv_right,
        split_target_boundary_right,
        split_source_boundary_right]
      exact map_rightBoundary_isRotated a U V X haV haX

/-- The Gallier--Xu Dyck rewrite has a common directed subdivision. -/
theorem hasCommonSubdivision {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart) :
    HasCommonSubdivision (source a U V X) (target a U V X) := by
  let R := P2.split (source a U V X) (sourceCut a U V X)
  refine ⟨R, ?_, ?_⟩
  · exact Subdivides.p2
      (P2Subdivision.canonical _ _
        (sourceCut_isNondegenerate a U V X))
  · exact Subdivides.p2
      ⟨targetCut a U V X,
        Or.inl (targetCut_isNondegenerate a U V X),
        ⟨splitSignedPresentationIso a U V X haU haV haX⟩⟩

/-- The Dyck rewrite preserves faithful polygonal realizations whenever the two displayed
one-face presentations are ordinary-valid. -/
theorem polygonallyEquivalent {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (validSource : (source a U V X).IsSurfaceValid)
    (validTarget : (target a U V X).IsSurfaceValid) :
    (source a U V X).PolygonallyEquivalent (target a U V X)
      validSource validTarget :=
  (hasCommonSubdivision a U V X haU haV haX).toPolygonallyEquivalent
    validSource validTarget

end Dyck

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
