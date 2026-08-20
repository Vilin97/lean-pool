/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicCancellation

/-!
# Exact two-face merging for finite cyclic presentations

Two displayed faces separated by a last-index edge are the canonical P2 split of the
concatenation of their old boundary words, up to rotating the first child.  This supplies the
local merge used to reduce a connected presentation to one face.  It covers both ordinary
nondegenerate cuts and the one-sided monogon case.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace FaceMerge

/-- The one-face presentation obtained after merging the displayed pair. -/
@[reducible]
def target {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (U ++ V)

/-- Two displayed faces sharing only the last-index separator in the shown positions. -/
@[reducible]
def source {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation where
  edgeCount := n + 1
  faces :=
    [[.pos (P1.freshEdge n)] ++ P2.retainWord U,
      [.neg (P1.freshEdge n)] ++ P2.retainWord V]

/-- The canonical cut of the concatenated target word between `U` and `V`. -/
def targetCut {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    P2Cut (target U V) where
  face := ⟨0, false⟩
  left := U
  right := V
  boundary_rotated := List.IsRotated.refl _

@[simp]
theorem targetCut_left {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    (targetCut U V).left = U :=
  rfl

@[simp]
theorem targetCut_right {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    (targetCut U V).right = V :=
  rfl

/-- The displayed two-face source differs from the canonical target split only by rotating its
first child boundary. -/
def sourceSignedIsoSplitTarget {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    SignedPresentationIso
      (source U V) (P2.split (target U V) (targetCut U V)) where
  edgeRelabeling := by
    change EdgeRelabeling (Fin (n + 1)) (Fin (n + 1))
    exact EdgeRelabeling.refl _
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    change
      (((source U V).boundary f).map
        (EdgeRelabeling.refl (Fin (n + 1))).mapDart).IsRotated
        ((P2.split (target U V) (targetCut U V)).boundary f)
    rw [EdgeRelabeling.map_mapDart_refl]
    fin_cases f
    · change
        ([SignedDart.pos (P1.freshEdge n)] ++
            P2.retainWord U).IsRotated
          (P2.retainWord U ++
            [SignedDart.pos (P1.freshEdge n)])
      exact List.isRotated_append
    · change
        ([SignedDart.neg (P1.freshEdge n)] ++
            P2.retainWord V).IsRotated
          ([SignedDart.neg (P1.freshEdge n)] ++
            P2.retainWord V)
      exact List.IsRotated.refl _

/-- Merging preserves ordinary validity whenever the resulting face is nonempty. -/
theorem target_isSurfaceValid {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (hUV : U ++ V ≠ [])
    (validSource : (source U V).IsSurfaceValid) :
    (target U V).IsSurfaceValid := by
  classical
  refine ⟨⟨0⟩, ?_, ?_, ?_⟩
  · intro f
    simpa [target, Dyck.oneFace_boundary] using hUV
  · intro f g _h
    exact (Dyck.oneFace_face_eq_zero (U ++ V) f).trans
      (Dyck.oneFace_face_eq_zero (U ++ V) g).symm
  · intro e
    have hmultiplicity := validSource.2.2.2 e.castSucc
    change
      (∑ f : Fin 2,
        (source U V).faceEdgeMultiplicity f e.castSucc) = 1 ∨
      (∑ f : Fin 2,
        (source U V).faceEdgeMultiplicity f e.castSucc) = 2
        at hmultiplicity
    rw [Fin.sum_univ_two] at hmultiplicity
    change
      ((([SignedDart.pos (P1.freshEdge n)] ++
            P2.retainWord U).map edgeOfDart).count e.castSucc +
          (([SignedDart.neg (P1.freshEdge n)] ++
            P2.retainWord V).map edgeOfDart).count e.castSucc = 1) ∨
        ((([SignedDart.pos (P1.freshEdge n)] ++
            P2.retainWord U).map edgeOfDart).count e.castSucc +
          (([SignedDart.neg (P1.freshEdge n)] ++
            P2.retainWord V).map edgeOfDart).count e.castSucc = 2)
        at hmultiplicity
    have hne : P1.freshEdge n ≠ e.castSucc :=
      (P1.firstSubedge_ne_freshEdge e).symm
    simp only [List.map_append, List.map_cons, List.map_nil,
      edgeOfDart, List.count_append, List.count_cons,
      List.count_nil] at hmultiplicity
    simp only [beq_iff_eq, hne, ↓reduceIte, add_zero, zero_add] at hmultiplicity
    rw [P2.count_retainWord_castSucc,
      P2.count_retainWord_castSucc] at hmultiplicity
    rw [Dyck.oneFace_edgeMultiplicity]
    change
      ((U ++ V).map edgeOfDart).count e = 1 ∨
        ((U ++ V).map edgeOfDart).count e = 2
    simpa [List.map_append, List.count_append] using hmultiplicity

/-- The canonical cut is ordinary whenever the concatenated target is nonempty: it is either
nondegenerate or exactly one-sided-degenerate. -/
theorem targetCut_isOrdinary {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (hUV : U ++ V ≠ []) :
    (targetCut U V).IsNondegenerate ∨
      ((targetCut U V).left = [] ∧
          0 < (targetCut U V).right.length) ∨
        (0 < (targetCut U V).left.length ∧
          (targetCut U V).right = []) := by
  by_cases hU : U = []
  · right
    left
    subst U
    exact ⟨rfl, List.length_pos_iff_ne_nil.mpr (by simpa using hUV)⟩
  · by_cases hV : V = []
    · right
      right
      exact ⟨List.length_pos_iff_ne_nil.mpr hU, hV⟩
    · left
      exact ⟨hU, hV⟩

/-- Merge the displayed two faces into their concatenated one-face presentation. -/
theorem normalizationEquivalent {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (hUV : U ++ V ≠ [])
    (validSource : (source U V).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source U V, validSource⟩
      ⟨target U V,
        target_isSurfaceValid U V hUV validSource⟩ := by
  let splitTarget := P2.split (target U V) (targetCut U V)
  let sourceIso := sourceSignedIsoSplitTarget U V
  let validSplit : splitTarget.IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  let validTarget : (target U V).IsSurfaceValid :=
    target_isSurfaceValid U V hUV validSource
  have hsplit :
      NormalizationEquivalent
        ⟨source U V, validSource⟩
        ⟨splitTarget, validSplit⟩ :=
    NormalizationEquivalent.ofSignedIso sourceIso
  have hmerge :
      NormalizationEquivalent
        ⟨splitTarget, validSplit⟩
        ⟨target U V, validTarget⟩ := by
    have hcanonical :=
      P2.ordinaryMergeNormalizationEquivalent
        (target U V) (targetCut U V)
        (targetCut_isOrdinary U V hUV) validTarget
    exact hcanonical
  exact hsplit.trans hmerge

/-- Public realization-invariance form of exact two-face merging. -/
theorem polygonallyEquivalent {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (hUV : U ++ V ≠ [])
    (validSource : (source U V).IsSurfaceValid) :
    (source U V).PolygonallyEquivalent
      (target U V) validSource
      (target_isSurfaceValid U V hUV validSource) :=
  (normalizationEquivalent U V hUV validSource).polygonallyEquivalent

/-! ### Merging through an arbitrary signed-isomorphic split -/

/-- Any presentation signed-isomorphic to an ordinary canonical P2 split can be merged.
This is the stable interface used when the two child faces occur among additional untouched
faces: all face ordering and edge naming is confined to `sourceIso`. -/
theorem normalizationEquivalentOfSignedIso
    {P Q : FiniteCyclicPresentation}
    (cut : P2Cut Q)
    (hcut :
      cut.IsNondegenerate ∨
        (cut.left = [] ∧ 0 < cut.right.length) ∨
          (0 < cut.left.length ∧ cut.right = []))
    (sourceIso : SignedPresentationIso P (P2.split Q cut))
    (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨P, validP⟩
      ⟨Q, validQ⟩ := by
  let validSplitFromIso : (P2.split Q cut).IsSurfaceValid :=
    sourceIso.isSurfaceValid validP
  let validCanonicalSplit : (P2.split Q cut).IsSurfaceValid :=
    P2.split_isSurfaceValid Q cut validQ
  have hsplitNode :
      (⟨P2.split Q cut, validSplitFromIso⟩ : ValidPresentation) =
        ⟨P2.split Q cut, validCanonicalSplit⟩ := by
    apply ValidPresentation.ext
    rfl
  have hsource :
      NormalizationEquivalent
        ⟨P, validP⟩
        ⟨P2.split Q cut, validSplitFromIso⟩ :=
    NormalizationEquivalent.ofSignedIso sourceIso
  rw [hsplitNode] at hsource
  exact hsource.trans
    (P2.ordinaryMergeNormalizationEquivalent Q cut hcut validQ)

/-- Public realization-invariance form of merging through a signed-isomorphic split. -/
theorem polygonallyEquivalentOfSignedIso
    {P Q : FiniteCyclicPresentation}
    (cut : P2Cut Q)
    (hcut :
      cut.IsNondegenerate ∨
        (cut.left = [] ∧ 0 < cut.right.length) ∨
          (0 < cut.left.length ∧ cut.right = []))
    (sourceIso : SignedPresentationIso P (P2.split Q cut))
    (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  (normalizationEquivalentOfSignedIso
    cut hcut sourceIso validP validQ).polygonallyEquivalent

/-! ### A merge among untouched faces -/

namespace ContextMerge

/-- Merge `U` and `V` into the first face while retaining the remaining face words `W`. -/
@[reducible]
def target {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    FiniteCyclicPresentation where
  edgeCount := n
  faces := (U ++ V) :: W

/-! ### Marked merging

Deleting the separating edge immediately can make the merged word cyclically equal to an
untouched face.  The marked merge instead retains that edge as an adjacent inverse pair.  Its
two occurrences distinguish the merged face from every untouched face, so ordinary validity is
preserved.  A later contextual cancellation removes the marker after the face-merging recursion
has finished.
-/

/-- Merge the first and last displayed children while retaining their separator as an adjacent
inverse pair in the merged face. -/
@[reducible]
def markedTarget {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    FiniteCyclicPresentation where
  edgeCount := n + 1
  faces :=
    (P2.retainWord U ++
      [.pos (P1.freshEdge n), .neg (P1.freshEdge n)] ++
      P2.retainWord V) ::
      W.map P2.retainWord

/-- Cut the marked merged face immediately after the positive marker occurrence. -/
def markedTargetCut {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    P2Cut (markedTarget U V W) where
  face := ⟨⟨0, by simp [markedTarget]⟩, false⟩
  left := P2.retainWord U ++ [.pos (P1.freshEdge n)]
  right := [.neg (P1.freshEdge n)] ++ P2.retainWord V
  boundary_rotated := by
    change
      (P2.retainWord U ++
          [SignedDart.pos (P1.freshEdge n),
            SignedDart.neg (P1.freshEdge n)] ++
          P2.retainWord V).IsRotated
        ((P2.retainWord U ++
            [SignedDart.pos (P1.freshEdge n)]) ++
          ([SignedDart.neg (P1.freshEdge n)] ++ P2.retainWord V))
    simpa only [List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using
      (List.IsRotated.refl
        (P2.retainWord U ++
          [SignedDart.pos (P1.freshEdge n),
            SignedDart.neg (P1.freshEdge n)] ++
          P2.retainWord V))

theorem markedTargetCut_isNondegenerate {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (markedTargetCut U V W).IsNondegenerate := by
  constructor <;> simp [markedTargetCut]

/-- The canonical cut of the first face of a contextual merge. -/
def targetCut {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    P2Cut (target U V W) where
  face := ⟨⟨0, by simp [target]⟩, false⟩
  left := U
  right := V
  boundary_rotated := List.IsRotated.refl _

@[simp]
theorem targetCut_left {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (targetCut U V W).left = U :=
  rfl

@[simp]
theorem targetCut_right {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (targetCut U V W).right = V :=
  rfl

/-- The canonical source for merging in context is the exact P2 split of the target. -/
@[reducible]
def source {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    FiniteCyclicPresentation :=
  P2.split (target U V W) (targetCut U V W)

/-- Match the face positions of the expanded contextual source with the split marked target. -/
def markedMiddleFaceEquiv {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (P1.expand (source U V W) (P1.freshEdge n)).Face ≃
      (P2.split (markedTarget U V W) (markedTargetCut U V W)).Face :=
  finCongr (by
    rw [P1.expand_faces_length]
    change
      (P2.split (target U V W)
          (targetCut U V W)).faces.length =
        (P2.split (markedTarget U V W)
          (markedTargetCut U V W)).faces.length
    rw [P2.split_faces_length, P2.split_faces_length]
    simp [target, markedTarget])

@[simp]
theorem markedMiddleFaceEquiv_apply_val {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (f : (P1.expand (source U V W) (P1.freshEdge n)).Face) :
    (markedMiddleFaceEquiv U V W f).val = f.val :=
  rfl

@[simp]
theorem markedMiddleFaceEquiv_oldFace {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (f : (target U V W).Face) :
    markedMiddleFaceEquiv U V W
        (P1.faceEquiv (source U V W) (P1.freshEdge n)
          (P2.oldFace (target U V W) (targetCut U V W) f)) =
      P2.oldFace (markedTarget U V W) (markedTargetCut U V W)
        ⟨f.val, by
          change f.val < (W.map P2.retainWord).length + 1
          simpa [target] using f.isLt⟩ := by
  apply Fin.ext
  change f.val = f.val
  rfl

@[simp]
theorem markedMiddleFaceEquiv_rightFace {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    markedMiddleFaceEquiv U V W
        (P1.faceEquiv (source U V W) (P1.freshEdge n)
          (P2.rightFace (target U V W) (targetCut U V W))) =
      P2.rightFace (markedTarget U V W) (markedTargetCut U V W) := by
  apply Fin.ext
  change (target U V W).faces.length =
    (markedTarget U V W).faces.length
  simp [target, markedTarget]

/-- The child occupying the selected old-face position. -/
def selectedFace {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (source U V W).Face :=
  P2.oldFace (target U V W) (targetCut U V W)
    (targetCut U V W).face.face

/-- The child appended by the P2 split. -/
def rightFace {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (source U V W).Face :=
  P2.rightFace (target U V W) (targetCut U V W)

/-- The target face occupied by the `i`th untouched word. -/
def untouchedTargetFace {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (i : Fin W.length) :
    (target U V W).Face :=
  ⟨i.val + 1, by
    change i.val + 1 < ((U ++ V) :: W).length
    simp only [List.length_cons]
    omega⟩

/-- The source face occupied by the `i`th untouched word. -/
def untouchedSourceFace {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (i : Fin W.length) :
    (source U V W).Face :=
  P2.oldFace (target U V W) (targetCut U V W)
    (untouchedTargetFace U V W i)

@[simp]
theorem source_boundary_selected {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (source U V W).boundary (selectedFace U V W) =
      P2.retainWord U ++ [.pos (P1.freshEdge n)] := by
  simp [source, selectedFace, targetCut, P2.selectedBoundary,
    P2.selectedOrientedBoundary, P2.freshEdge, target]

@[simp]
theorem source_boundary_right {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (source U V W).boundary (rightFace U V W) =
      [.neg (P1.freshEdge n)] ++ P2.retainWord V := by
  simp [source, rightFace, targetCut, P2.rightBoundary,
    P2.rightOrientedBoundary, P2.freshEdge, target]

@[simp]
theorem target_boundary_untouched {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (i : Fin W.length) :
    (target U V W).boundary (untouchedTargetFace U V W i) =
      W.get i := by
  simp [target, untouchedTargetFace,
    FiniteCyclicPresentation.boundary]

@[simp]
theorem source_boundary_untouched {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (i : Fin W.length) :
    (source U V W).boundary (untouchedSourceFace U V W i) =
      P2.retainWord (W.get i) := by
  change
    (P2.split (target U V W) (targetCut U V W)).boundary
        (P2.oldFace (target U V W) (targetCut U V W)
          (untouchedTargetFace U V W i)) =
      P2.retainWord (W.get i)
  rw [P2.split_boundary_old_of_ne]
  · rw [target_boundary_untouched]
  · intro h
    have hval := congrArg Fin.val h
    change i.val + 1 = 0 at hval
    omega

/-- P1 expansion of the retained separator in the contextual source is signed-isomorphic to the
P2 split of the marked target. -/
def expandSourceSignedIsoSplitMarkedTarget {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    SignedPresentationIso
      (P1.expand (source U V W) (P1.freshEdge n))
      (P2.split (markedTarget U V W) (markedTargetCut U V W)) where
  edgeRelabeling := by
    change EdgeRelabeling (Fin (n + 2)) (Fin (n + 2))
    exact EdgeRelabeling.refl _
  faceEquiv := markedMiddleFaceEquiv U V W
  boundary_rotated := by
    intro f
    let p :=
      (P1.faceEquiv (source U V W) (P1.freshEdge n)).symm f
    have hf :
        P1.faceEquiv (source U V W) (P1.freshEdge n) p = f :=
      (P1.faceEquiv (source U V W)
        (P1.freshEdge n)).apply_symm_apply f
    rw [← hf, P1.expand_boundary]
    simp only [id_eq]
    have hmap :
        (P1.expandWord (P1.freshEdge n)
            ((source U V W).boundary p)).map
              (EdgeRelabeling.refl (Fin (n + 2))).mapDart =
          P1.expandWord (P1.freshEdge n)
            ((source U V W).boundary p) :=
      EdgeRelabeling.map_mapDart_refl _
    refine Eq.mpr
      (congrArg
        (fun word ↦ word.IsRotated
          ((P2.split (markedTarget U V W)
            (markedTargetCut U V W)).boundary
              (markedMiddleFaceEquiv U V W
                (P1.faceEquiv (source U V W)
                  (P1.freshEdge n) p))))
        hmap) ?_
    rcases P2.face_cases (target U V W) (targetCut U V W) p with
      ⟨q, hq⟩ | hq
    · rw [hq]
      rw [markedMiddleFaceEquiv_oldFace]
      induction q using Fin.cases with
      | zero =>
          have hsourceBoundary :
              (source U V W).boundary
                  (P2.oldFace (target U V W) (targetCut U V W) 0) =
                P2.selectedBoundary (target U V W)
                  (targetCut U V W) := by
            rw [P2.split_boundary_old]
            simp [targetCut]
          have htargetBoundary :
              (P2.split (markedTarget U V W)
                  (markedTargetCut U V W)).boundary
                    (P2.oldFace (markedTarget U V W)
                      (markedTargetCut U V W)
                      ⟨(0 : (target U V W).Face).val, by
                        change 0 <
                          (W.map P2.retainWord).length + 1
                        simp⟩) =
                P2.selectedBoundary (markedTarget U V W)
                  (markedTargetCut U V W) := by
            rw [P2.split_boundary_old]
            simp [markedTargetCut]
          rw [hsourceBoundary, htargetBoundary]
          simp only [targetCut, markedTargetCut,
            P2.selectedBoundary, P2.selectedOrientedBoundary,
            P2.storedWord, Bool.false_eq_true, if_false,
            P2.freshEdge]
          rw [P1.expandWord_append,
            Cancellation.expandWord_retainWord_fresh,
            P1.expandWord_singleton, P1.expandDart_pos_self]
          simp only [P2.retainWord, List.map_map, P1.firstSubedge, P1.freshEdge, List.map_append,
            List.map_cons, P1.castSuccDart_pos, List.map_nil, List.append_assoc, List.cons_append,
            List.nil_append]
          exact List.IsRotated.refl _
      | succ i =>
          let iW : Fin W.length :=
            ⟨i.val, by simp [target]⟩
          have hsource :
              (source U V W).boundary
                  (P2.oldFace (target U V W) (targetCut U V W)
                    i.succ) =
                P2.retainWord (W.get iW) := by
            rw [P2.split_boundary_old_of_ne]
            · simp [target, FiniteCyclicPresentation.boundary, iW]
            · intro h
              have hval := congrArg Fin.val h
              change i.val + 1 = 0 at hval
              omega
          rw [hsource]
          rw [show
            P1.expandWord (P1.freshEdge n)
                (P2.retainWord (W.get iW)) =
              P2.retainWord (P2.retainWord (W.get iW)) by
            exact Cancellation.expandWord_retainWord_fresh _]
          rw [P2.split_boundary_old_of_ne]
          · simp only [P2.retainWord, Fin.eta, List.get_eq_getElem, List.map_map,
              markedTarget, FiniteCyclicPresentation.boundary, List.length_cons,
              Fin.val_succ, List.append_assoc, List.cons_append, List.nil_append,
              List.getElem_cons_succ, List.getElem_map, iW]
            exact List.IsRotated.refl _
          · intro h
            have hval := congrArg Fin.val h
            change i.val + 1 = 0 at hval
            omega
    · rw [hq]
      rw [markedMiddleFaceEquiv_rightFace,
        P2.split_boundary_right, P2.split_boundary_right]
      simp only [targetCut, markedTargetCut, P2.rightBoundary,
        P2.rightOrientedBoundary, P2.storedWord, if_false,
        Bool.false_eq_true, P2.freshEdge]
      rw [P1.expandWord_cons, P1.expandDart_neg_self,
        Cancellation.expandWord_retainWord_fresh]
      simp only [P1.freshEdge, P1.firstSubedge, P2.retainWord, List.map_map, List.cons_append,
        List.nil_append, List.map_cons, P1.castSuccDart_neg]
      exact List.IsRotated.refl _

@[simp]
theorem markedTarget_boundary_zero {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n)))) :
    (markedTarget U V W).boundary 0 =
      P2.retainWord U ++
        [.pos (P1.freshEdge n), .neg (P1.freshEdge n)] ++
        P2.retainWord V :=
  rfl

@[simp]
theorem markedTarget_boundary_succ {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (i : Fin W.length) :
    (markedTarget U V W).boundary
        ⟨i.val + 1, by
          change i.val + 1 < (W.map P2.retainWord).length + 1
          simp⟩ =
      P2.retainWord (W.get i) := by
  simp [markedTarget, FiniteCyclicPresentation.boundary]

@[simp]
theorem markedTarget_boundary_succMap {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (i : Fin (W.map P2.retainWord).length) :
    (markedTarget U V W).boundary i.succ =
      P2.retainWord
        (W.get ⟨i.val, by simpa using i.isLt⟩) := by
  let iW : Fin W.length := ⟨i.val, by simpa using i.isLt⟩
  have hface :
      i.succ =
        (⟨iW.val + 1, by
          change iW.val + 1 < (W.map P2.retainWord).length + 1
          simp⟩ : (markedTarget U V W).Face) := by
    apply Fin.ext
    rfl
  rw [hface, markedTarget_boundary_succ]

/-- The adjacent inverse marker makes the merged face distinct from every untouched face, so a
marked merge preserves the project's strict ordinary validity predicate. -/
theorem markedTarget_isSurfaceValid {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (validSource : (source U V W).IsSurfaceValid) :
    (markedTarget U V W).IsSurfaceValid := by
  classical
  let marker := P1.freshEdge n
  let validExpanded :
      (P1.expand (source U V W) marker).IsSurfaceValid :=
    P1.expand_isSurfaceValid (source U V W) marker validSource
  let middleIso :=
    expandSourceSignedIsoSplitMarkedTarget U V W
  let validSplit :
      (P2.split (markedTarget U V W)
        (markedTargetCut U V W)).IsSurfaceValid :=
    middleIso.isSurfaceValid validExpanded
  refine ⟨⟨0, by simp [markedTarget]⟩, ?_, ?_, ?_⟩
  · intro f
    induction f using Fin.cases with
    | zero =>
        rw [markedTarget_boundary_zero]
        simp
    | succ i =>
        let iW : Fin W.length :=
          ⟨i.val, by simpa using i.isLt⟩
        have hsourceNonempty :=
          validSource.2.1
            (untouchedSourceFace U V W iW)
        rw [source_boundary_untouched] at hsourceNonempty
        rw [markedTarget_boundary_succMap]
        intro hnil
        apply hsourceNonempty
        exact (P2.retainWord_eq_nil_iff _).mpr
          (by simpa [iW] using hnil)
  · intro f g hfg
    induction f using Fin.cases with
    | zero =>
        induction g using Fin.cases with
        | zero => rfl
        | succ j =>
            let jW : Fin W.length :=
              ⟨j.val, by simpa using j.isLt⟩
            have hmarker :
                SignedDart.pos marker ∈
                  (markedTarget U V W).boundary 0 := by
              simp [marker]
            have htarget := hfg.mem_iff.mp hmarker
            rw [markedTarget_boundary_succMap] at htarget
            have hmarkerEq :
                P2.freshEdge (target U V W) = marker := by
              apply Fin.ext
              rfl
            have hnot :
                SignedDart.pos marker ∉
                  P2.retainWord (W.get jW) := by
              rw [← hmarkerEq]
              exact
                P2.pos_freshEdge_not_mem_retainWord
                  (target U V W) (W.get jW)
            exact (hnot (by simpa [jW] using htarget)).elim
    | succ i =>
        induction g using Fin.cases with
        | zero =>
            let iW : Fin W.length :=
              ⟨i.val, by simpa using i.isLt⟩
            have hmarker :
                SignedDart.pos marker ∈
                  (markedTarget U V W).boundary 0 := by
              simp [marker]
            have hsource := hfg.symm.mem_iff.mp hmarker
            rw [markedTarget_boundary_succMap] at hsource
            have hmarkerEq :
                P2.freshEdge (target U V W) = marker := by
              apply Fin.ext
              rfl
            have hnot :
                SignedDart.pos marker ∉
                  P2.retainWord (W.get iW) := by
              rw [← hmarkerEq]
              exact
                P2.pos_freshEdge_not_mem_retainWord
                  (target U V W) (W.get iW)
            exact (hnot (by simpa [iW] using hsource)).elim
        | succ j =>
            let iW : Fin W.length :=
              ⟨i.val, by simpa using i.isLt⟩
            let jW : Fin W.length :=
              ⟨j.val, by simpa using j.isLt⟩
            have hboundaries :
                (P2.retainWord (W.get iW)).IsRotated
                  (P2.retainWord (W.get jW)) := by
              rw [markedTarget_boundary_succMap,
                markedTarget_boundary_succMap] at hfg
              simpa [iW, jW] using hfg
            have hsourceBoundaries :
                ((source U V W).boundary
                    (untouchedSourceFace U V W iW)).IsRotated
                  ((source U V W).boundary
                    (untouchedSourceFace U V W jW)) := by
              rw [source_boundary_untouched,
                source_boundary_untouched]
              exact hboundaries
            have hsourceFaces :=
              validSource.2.2.1
                (untouchedSourceFace U V W iW)
                (untouchedSourceFace U V W jW)
                hsourceBoundaries
            apply Fin.ext
            have hval := congrArg Fin.val hsourceFaces
            have holdVal (k : Fin W.length) :
                (untouchedSourceFace U V W k).val =
                  k.val + 1 :=
              rfl
            rw [holdVal iW, holdVal jW] at hval
            have hij : iW.val = jW.val :=
              Nat.add_right_cancel hval
            simpa [iW, jW] using hij
  · intro e
    rw [P2.edgeMultiplicity_split_castSucc
      (markedTarget U V W) (markedTargetCut U V W) e]
    exact validSplit.2.2.2 e.castSucc

/-- The validity-safe marked merge preserves face-incidence connectivity. -/
theorem markedTarget_isConnected {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (connectedSource : (source U V W).IsConnected) :
    (markedTarget U V W).IsConnected := by
  have connectedExpanded :
      (P1.expand (source U V W) (P1.freshEdge n)).IsConnected :=
    P1.expand_isConnected
      (source U V W) (P1.freshEdge n) connectedSource
  have connectedSplit :
      (P2.split (markedTarget U V W)
        (markedTargetCut U V W)).IsConnected :=
    (expandSourceSignedIsoSplitMarkedTarget U V W).isConnected
      connectedExpanded
  exact P2.isConnected_of_split
    (markedTarget U V W) (markedTargetCut U V W) connectedSplit

/-- The validity-safe marked merge is a common P1/P2 subdivision: expand the old separator in
the source and cut the marked parent along the fresh second subedge. -/
theorem markedNormalizationEquivalent {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (validSource : (source U V W).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source U V W, validSource⟩
      ⟨markedTarget U V W,
        markedTarget_isSurfaceValid U V W validSource⟩ := by
  let expandedSource :=
    P1.expand (source U V W) (P1.freshEdge n)
  let splitMarked :=
    P2.split (markedTarget U V W) (markedTargetCut U V W)
  have hsourceExpanded :
      Subdivides (source U V W) expandedSource :=
    Subdivides.p1
      (P1Subdivision.canonical
        (source U V W) (P1.freshEdge n))
  have hexpandedSplit :
      Subdivides expandedSource splitMarked :=
    Subdivides.signedIso
      (expandSourceSignedIsoSplitMarkedTarget U V W)
  have htargetSplit :
      Subdivides (markedTarget U V W) splitMarked :=
    Subdivides.p2
      (P2Subdivision.canonical
        (markedTarget U V W) (markedTargetCut U V W)
        (markedTargetCut_isNondegenerate U V W))
  exact NormalizationEquivalent.ofCommonSubdivision
    ⟨splitMarked, hsourceExpanded.trans hexpandedSplit,
      htargetSplit⟩

/-- Faithful realization invariance of the validity-safe marked merge. -/
theorem markedPolygonallyEquivalent {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (validSource : (source U V W).IsSurfaceValid) :
    (source U V W).PolygonallyEquivalent
      (markedTarget U V W) validSource
      (markedTarget_isSurfaceValid U V W validSource) :=
  (markedNormalizationEquivalent U V W validSource).polygonallyEquivalent

/-- The contextual cut is ordinary exactly under the same nonempty condition as the two-face
special case. -/
theorem targetCut_isOrdinary {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (hUV : U ++ V ≠ []) :
    (targetCut U V W).IsNondegenerate ∨
      ((targetCut U V W).left = [] ∧
          0 < (targetCut U V W).right.length) ∨
        (0 < (targetCut U V W).left.length ∧
          (targetCut U V W).right = []) := by
  by_cases hU : U = []
  · right
    left
    subst U
    exact ⟨rfl, List.length_pos_iff_ne_nil.mpr (by simpa using hUV)⟩
  · by_cases hV : V = []
    · right
      right
      exact ⟨List.length_pos_iff_ne_nil.mpr hU, hV⟩
    · left
      exact ⟨hU, hV⟩

/-- A validity-safe contextual merge. The target-validity hypothesis is explicit because merging
can make two cyclic face words coincide, while `IsSurfaceValid` deliberately excludes duplicate
faces. -/
theorem normalizationEquivalent {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (hUV : U ++ V ≠ [])
    (validTarget : (target U V W).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source U V W,
        P2.split_isSurfaceValid
          (target U V W) (targetCut U V W) validTarget⟩
      ⟨target U V W, validTarget⟩ :=
  P2.ordinaryMergeNormalizationEquivalent
    (target U V W) (targetCut U V W)
    (targetCut_isOrdinary U V W hUV) validTarget

/-- Transport a contextual merge across the face ordering and edge naming of an arbitrary
source presentation. -/
theorem normalizationEquivalentOfSignedIso
    {P : FiniteCyclicPresentation} {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (W : List (List (SignedDart (Fin n))))
    (hUV : U ++ V ≠ [])
    (sourceIso : SignedPresentationIso P (source U V W))
    (validP : P.IsSurfaceValid)
    (validTarget : (target U V W).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨P, validP⟩
      ⟨target U V W, validTarget⟩ :=
  FaceMerge.normalizationEquivalentOfSignedIso
    (targetCut U V W) (targetCut_isOrdinary U V W hUV)
    sourceIso validP validTarget

end ContextMerge

/-! ### Arbitrary separator names -/

/-- Two displayed faces with an arbitrarily named, oppositely oriented separator. -/
@[reducible]
def namedSource {n : ℕ} (a : Fin (n + 1))
    (U V : List (SignedDart (Fin (n + 1)))) :
    FiniteCyclicPresentation where
  edgeCount := n + 1
  faces := [[.pos a] ++ U, [.neg a] ++ V]

/-- Rename the separator to last and delete that name from both remaining face words. -/
def namedSourceSignedIso {n : ℕ}
    (a : Fin (n + 1))
    (U V : List (SignedDart (Fin (n + 1))))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart) :
    SignedPresentationIso
      (namedSource a U V)
      (source
        (Cancellation.lowerTail a U)
        (Cancellation.lowerTail a V)) where
  edgeRelabeling :=
    EdgeRelabeling.ofEquiv (Cancellation.moveToLast a)
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [EdgeRelabeling.map_mapDart_ofEquiv]
    fin_cases f
    · change
        ([SignedDart.mapEquiv
            (Cancellation.moveToLast a) (.pos a)] ++
          Cancellation.renamedTail a U).IsRotated
          ([.pos (P1.freshEdge n)] ++
            P2.retainWord (Cancellation.lowerTail a U))
      rw [Cancellation.retainWord_lowerTail a U haU]
      have hmove :
          Cancellation.moveToLast a a = P1.freshEdge n := by
        simp [Cancellation.moveToLast, P1.freshEdge]
      rw [show SignedDart.mapEquiv
          (Cancellation.moveToLast a) (.pos a) =
            .pos (P1.freshEdge n) by simp [hmove]]
    · change
        ([SignedDart.mapEquiv
            (Cancellation.moveToLast a) (.neg a)] ++
          Cancellation.renamedTail a V).IsRotated
          ([.neg (P1.freshEdge n)] ++
            P2.retainWord (Cancellation.lowerTail a V))
      rw [Cancellation.retainWord_lowerTail a V haV]
      have hmove :
          Cancellation.moveToLast a a = P1.freshEdge n := by
        simp [Cancellation.moveToLast, P1.freshEdge]
      rw [show SignedDart.mapEquiv
          (Cancellation.moveToLast a) (.neg a) =
            .neg (P1.freshEdge n) by simp [hmove]]

/-- Merge two displayed faces with an arbitrary separator name. -/
theorem namedNormalizationEquivalent {n : ℕ}
    (a : Fin (n + 1))
    (U V : List (SignedDart (Fin (n + 1))))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (hUV :
      Cancellation.lowerTail a U ++
        Cancellation.lowerTail a V ≠ [])
    (validSource : (namedSource a U V).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨namedSource a U V, validSource⟩
      ⟨target
          (Cancellation.lowerTail a U)
          (Cancellation.lowerTail a V),
        target_isSurfaceValid
          (Cancellation.lowerTail a U)
          (Cancellation.lowerTail a V) hUV
          ((namedSourceSignedIso a U V haU haV).isSurfaceValid
            validSource)⟩ := by
  let sourceIso := namedSourceSignedIso a U V haU haV
  let validBase :
      (source
        (Cancellation.lowerTail a U)
        (Cancellation.lowerTail a V)).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      (normalizationEquivalent
        (Cancellation.lowerTail a U)
        (Cancellation.lowerTail a V) hUV validBase)

end FaceMerge

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
