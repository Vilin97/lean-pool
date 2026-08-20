/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicNormalizationResult

/-!
# Combinatorial selections for finite-cyclic reduction

This file supplies the finite graph and cyclic-list selections used by the recursive
Gallier--Xu normalization.  In particular, connected presentations with more than one face expose
a genuinely adjacent pair, and either occurrence of their common edge can be placed at the head
of a suitably oriented cyclic boundary.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Reduction

/-- Build an unoriented presentation isomorphism from equations stated using oriented source
faces and stored target faces. Reversing both sides converts this convenient input convention to
the target-oriented convention of `UnorientedPresentationIso`. -/
def unorientedIsoOfOrientedBoundaries
    {P Q : FiniteCyclicPresentation}
    (edgeRelabeling : EdgeRelabeling P.Edge Q.Edge)
    (faceEquiv : P.Face ≃ Q.Face)
    (reverseFace : P.Face → Bool)
    (boundary_rotated :
      ∀ f,
        ((P.orientedBoundary ⟨f, reverseFace f⟩).map
          edgeRelabeling.mapDart).IsRotated
            (Q.boundary (faceEquiv f))) :
    UnorientedPresentationIso P Q where
  edgeRelabeling := edgeRelabeling
  faceEquiv := faceEquiv
  reverseFace := reverseFace
  boundary_rotated := by
    intro f
    cases hreverse : reverseFace f with
    | false =>
        simpa [FiniteCyclicPresentation.orientedBoundary, hreverse] using
          boundary_rotated f
    | true =>
        have hinverse :=
          inverseWord_isRotated (boundary_rotated f)
        simpa only [FiniteCyclicPresentation.orientedBoundary,
          hreverse, if_true, inverseWord_inverseWord,
          EdgeRelabeling.inverseWord_map_mapDart] using hinverse

/-! ### Deleting a selected edge name -/

/-- The edge count after deleting one selected edge. -/
def edgeCountAfterDelete
    (P : FiniteCyclicPresentation) : ℕ :=
  P.edgeCount - 1

theorem edgeCountAfterDelete_add_one
    (P : FiniteCyclicPresentation) (e : P.Edge) :
    edgeCountAfterDelete P + 1 = P.edgeCount := by
  have hpositive : 0 < P.edgeCount := Nat.zero_lt_of_lt e.isLt
  exact Nat.sub_add_cancel hpositive

/-- Rename an arbitrary selected edge to the last position of the one-larger edge type. -/
def edgeToLast
    (P : FiniteCyclicPresentation) (e : P.Edge) :
    P.Edge ≃ Fin (edgeCountAfterDelete P + 1) := by
  let castCount :
      P.Edge ≃ Fin (edgeCountAfterDelete P + 1) :=
    finCongr (edgeCountAfterDelete_add_one P e).symm
  exact castCount.trans (Cancellation.moveToLast (castCount e))

theorem edgeToLast_selected
    (P : FiniteCyclicPresentation) (e : P.Edge) :
    edgeToLast P e e =
      P1.freshEdge (edgeCountAfterDelete P) := by
  simp [edgeToLast, Cancellation.moveToLast, P1.freshEdge]

/-- Rename a word after moving the selected edge to the fresh-last index. -/
def renamedTail
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (word : List P.Dart) :
    List (SignedDart (Fin (edgeCountAfterDelete P + 1))) :=
  word.map (SignedDart.mapEquiv (edgeToLast P e))

/-- Contract the now-unused last edge name from a renamed word. -/
def lowerTail
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (word : List P.Dart) :
    List (SignedDart (Fin (edgeCountAfterDelete P))) :=
  P1.contractWord (renamedTail P e word)

theorem freshEdge_not_mem_renamedTail
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (word : List P.Dart)
    (he : e ∉ word.map edgeOfDart) :
    P1.freshEdge (edgeCountAfterDelete P) ∉
      (renamedTail P e word).map edgeOfDart := by
  intro hfresh
  rcases List.mem_map.mp hfresh with ⟨d, hd, hedge⟩
  rcases List.mem_map.mp hd with ⟨old, hold, rfl⟩
  rw [edgeOfDart_mapEquiv] at hedge
  have holdEdge : edgeOfDart old = e := by
    apply (edgeToLast P e).injective
    rw [hedge, edgeToLast_selected]
  exact he (List.mem_map.mpr ⟨old, hold, holdEdge⟩)

/-- Lowering and re-embedding a renamed word which avoids the selected edge recovers that exact
renamed word. -/
theorem retainWord_lowerTail
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (word : List P.Dart)
    (he : e ∉ word.map edgeOfDart) :
    P2.retainWord (lowerTail P e word) =
      renamedTail P e word :=
  Cancellation.retainWord_contractWord_of_fresh_not_mem
    (renamedTail P e word)
    (freshEdge_not_mem_renamedTail P e word he)

/-! ### Moving a selected face pair to the endpoints -/

/-- The last face index, using an existing face to certify nonemptiness. -/
def lastFace
    (P : FiniteCyclicPresentation) (f : P.Face) :
    P.Face :=
  ⟨P.faces.length - 1, by
    have hf := f.isLt
    omega⟩

/-- Move `f` to index zero and a distinct `g` to the final index. -/
def faceToEndpoints
    (P : FiniteCyclicPresentation) (f g : P.Face) :
    P.Face ≃ P.Face :=
  let moveFirst :=
    Equiv.swap f ⟨0, Nat.zero_lt_of_lt f.isLt⟩
  moveFirst.trans (Equiv.swap (moveFirst g) (lastFace P f))

theorem faceToEndpoints_selected
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) :
    faceToEndpoints P f g f =
      ⟨0, Nat.zero_lt_of_lt f.isLt⟩ := by
  let zero : P.Face := ⟨0, Nat.zero_lt_of_lt f.isLt⟩
  let moveFirst := Equiv.swap f zero
  have hgf : moveFirst g ≠ moveFirst f := by
    intro h
    exact hfg (moveFirst.injective h.symm)
  have hgzero : moveFirst g ≠ zero := by
    simpa [moveFirst] using hgf
  have hvalues : f.val ≠ g.val := by
    exact fun h ↦ hfg (Fin.ext h)
  have hmany : 1 < P.faces.length := by
    omega
  have hlastZero : lastFace P f ≠ zero := by
    intro h
    have hval := congrArg Fin.val h
    change P.faces.length - 1 = 0 at hval
    omega
  change
    (Equiv.swap (moveFirst g) (lastFace P f)) (moveFirst f) =
      zero
  rw [show moveFirst f = zero by simp [moveFirst]]
  exact Equiv.swap_apply_of_ne_of_ne hgzero.symm hlastZero.symm

@[simp]
theorem faceToEndpoints_right
    (P : FiniteCyclicPresentation) (f g : P.Face) :
    faceToEndpoints P f g g = lastFace P f := by
  change
    (Equiv.swap
      ((Equiv.swap f ⟨0, Nat.zero_lt_of_lt f.isLt⟩) g)
      (lastFace P f))
      ((Equiv.swap f ⟨0, Nat.zero_lt_of_lt f.isLt⟩) g) =
        lastFace P f
  exact Equiv.swap_apply_left _ _

/-- Number of untouched faces after selecting two distinct endpoints. -/
def faceCountBetween
    (P : FiniteCyclicPresentation) : ℕ :=
  P.faces.length - 2

/-- The `i`th interior position between zero and the final face index. -/
def middleFacePosition
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) (i : Fin (faceCountBetween P)) :
    P.Face :=
  ⟨i.val + 1, by
    have hvalues : f.val ≠ g.val :=
      fun h ↦ hfg (Fin.ext h)
    have hmany : 1 < P.faces.length := by
      omega
    have hi := i.isLt
    change i.val < P.faces.length - 2 at hi
    change i.val + 1 < P.faces.length
    omega⟩

/-- The original face occupying an interior position after moving the selected pair to the
endpoints. -/
def middleOriginalFace
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) (i : Fin (faceCountBetween P)) :
    P.Face :=
  (faceToEndpoints P f g).symm
    (middleFacePosition P f g hfg i)

/-- Enumerate the original faces not selected as endpoints, in their transported order. -/
def middleOriginalFaces
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) :
    List P.Face :=
  List.ofFn (middleOriginalFace P f g hfg)

theorem middleOriginalFace_ne_selected
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) (i : Fin (faceCountBetween P)) :
    middleOriginalFace P f g hfg i ≠ f := by
  intro h
  have hpositions := congrArg (faceToEndpoints P f g) h
  have hmiddle :
      faceToEndpoints P f g
          (middleOriginalFace P f g hfg i) =
        middleFacePosition P f g hfg i := by
    simp [middleOriginalFace]
  rw [hmiddle, faceToEndpoints_selected P f g hfg] at hpositions
  have hval := congrArg Fin.val hpositions
  change i.val + 1 = 0 at hval
  omega

theorem middleOriginalFace_ne_right
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) (i : Fin (faceCountBetween P)) :
    middleOriginalFace P f g hfg i ≠ g := by
  intro h
  have hpositions := congrArg (faceToEndpoints P f g) h
  have hmiddle :
      faceToEndpoints P f g
          (middleOriginalFace P f g hfg i) =
        middleFacePosition P f g hfg i := by
    simp [middleOriginalFace]
  rw [hmiddle, faceToEndpoints_right] at hpositions
  have hval := congrArg Fin.val hpositions
  change i.val + 1 = P.faces.length - 1 at hval
  have hi := i.isLt
  change i.val < P.faces.length - 2 at hi
  omega

@[simp]
theorem middleOriginalFaces_length
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) :
    (middleOriginalFaces P f g hfg).length =
      faceCountBetween P := by
  simp [middleOriginalFaces]

/-- Every face is the selected face, the right face, or a uniquely positioned untouched face. -/
theorem face_eq_selected_or_right_or_middle
    (P : FiniteCyclicPresentation) (f g q : P.Face)
    (hfg : f ≠ g) :
    q = f ∨ q = g ∨
      ∃ i : Fin (faceCountBetween P),
        q = middleOriginalFace P f g hfg i := by
  let position := faceToEndpoints P f g q
  by_cases hzero : position.val = 0
  · left
    apply (faceToEndpoints P f g).injective
    apply Fin.ext
    rw [faceToEndpoints_selected P f g hfg]
    exact hzero
  · by_cases hlast :
      position.val = P.faces.length - 1
    · right
      left
      apply (faceToEndpoints P f g).injective
      apply Fin.ext
      rw [faceToEndpoints_right]
      exact hlast
    · right
      right
      have hvalues : f.val ≠ g.val :=
        fun h ↦ hfg (Fin.ext h)
      have hmany : 1 < P.faces.length := by
        omega
      have hpositionPositive : 0 < position.val := by
        omega
      have hpositionBelow : position.val < P.faces.length - 1 := by
        have hlt := position.isLt
        omega
      let i : Fin (faceCountBetween P) :=
        ⟨position.val - 1, by
          change position.val - 1 < P.faces.length - 2
          omega⟩
      refine ⟨i, ?_⟩
      apply (faceToEndpoints P f g).injective
      change
        faceToEndpoints P f g q =
          faceToEndpoints P f g
            ((faceToEndpoints P f g).symm
              (middleFacePosition P f g hfg i))
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      change position.val = i.val + 1
      simp only [i]
      omega

/-- A nontrivial reflexive-transitive path contains a genuinely non-reflexive step. -/
theorem exists_ne_step_of_reflTransGen
    {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) (hne : a ≠ b) :
    ∃ x y, r x y ∧ x ≠ y := by
  induction h with
  | refl =>
      exact (hne rfl).elim
  | @tail b c hab hbc ih =>
      by_cases hbcne : b ≠ c
      · exact ⟨b, c, hbc, hbcne⟩
      · have hbcEq : b = c := not_ne_iff.mp hbcne
        subst c
        exact ih hne

/-- Face adjacency is symmetric. -/
theorem faceAdjacent_comm
    (P : FiniteCyclicPresentation) (f g : P.Face) :
    P.FaceAdjacent f g ↔ P.FaceAdjacent g f := by
  constructor
  · rintro ⟨e, hef, heg⟩
    exact ⟨e, heg, hef⟩
  · rintro ⟨e, heg, hef⟩
    exact ⟨e, hef, heg⟩

/-- The contributions of two distinct faces are bounded by the total edge multiplicity. -/
theorem add_faceEdgeMultiplicity_le_edgeMultiplicity
    (P : FiniteCyclicPresentation)
    (f g : P.Face) (e : P.Edge) (hfg : f ≠ g) :
    P.faceEdgeMultiplicity f e + P.faceEdgeMultiplicity g e ≤
      P.edgeMultiplicity e := by
  classical
  unfold edgeMultiplicity
  have hsubset :
      ({f, g} : Finset P.Face) ⊆ Finset.univ := by
    intro x hx
    simp
  have hsum :=
    Finset.sum_le_sum_of_subset
      (f := fun q ↦ P.faceEdgeMultiplicity q e) hsubset
  simpa [hfg] using hsum

/-- Three distinct face contributions are bounded by total edge multiplicity. -/
theorem add_three_faceEdgeMultiplicity_le_edgeMultiplicity
    (P : FiniteCyclicPresentation)
    (f g q : P.Face) (e : P.Edge)
    (hfg : f ≠ g) (hfq : f ≠ q) (hgq : g ≠ q) :
    P.faceEdgeMultiplicity f e +
        P.faceEdgeMultiplicity g e +
        P.faceEdgeMultiplicity q e ≤
      P.edgeMultiplicity e := by
  classical
  unfold edgeMultiplicity
  have hsubset :
      ({f, g, q} : Finset P.Face) ⊆ Finset.univ := by
    intro x hx
    simp
  have hsum :=
    Finset.sum_le_sum_of_subset
      (f := fun r ↦ P.faceEdgeMultiplicity r e) hsubset
  simpa [hfg, hfq, hgq, Nat.add_assoc] using hsum

/-- Once two distinct faces contain an edge of surface multiplicity at most two, no third face
contains that edge. -/
theorem edge_not_mem_boundary_of_other
    (P : FiniteCyclicPresentation)
    (valid : P.IsSurfaceValid)
    (f g q : P.Face) (e : P.Edge)
    (hfg : f ≠ g) (hfq : f ≠ q) (hgq : g ≠ q)
    (hef : e ∈ (P.boundary f).map edgeOfDart)
    (heg : e ∈ (P.boundary g).map edgeOfDart) :
    e ∉ (P.boundary q).map edgeOfDart := by
  classical
  intro heq
  have hfpos : 0 < P.faceEdgeMultiplicity f e :=
    List.count_pos_iff.mpr hef
  have hgpos : 0 < P.faceEdgeMultiplicity g e :=
    List.count_pos_iff.mpr heg
  have hqpos : 0 < P.faceEdgeMultiplicity q e :=
    List.count_pos_iff.mpr heq
  have hthree :=
    add_three_faceEdgeMultiplicity_le_edgeMultiplicity
      P f g q e hfg hfq hgq
  rcases valid.2.2.2 e with htotal | htotal <;> omega

/-- A connected presentation with at least two faces contains two distinct adjacent faces. -/
theorem exists_distinct_faceAdjacent
    (P : FiniteCyclicPresentation)
    (connected : P.IsConnected)
    (hmany : 1 < P.faces.length) :
    ∃ f g : P.Face, f ≠ g ∧ P.FaceAdjacent f g := by
  let f : P.Face := ⟨0, by omega⟩
  let g : P.Face := ⟨1, hmany⟩
  have hfg : f ≠ g := by
    intro h
    have hval := congrArg Fin.val h
    change 0 = 1 at hval
    omega
  rcases exists_ne_step_of_reflTransGen
      (connected.2 f g) hfg with
    ⟨x, y, hxy, hxyne⟩
  exact ⟨x, y, hxyne, hxy⟩

/-- Any member of a linear list can be moved to its head by a cyclic rotation. -/
theorem exists_tail_isRotated_cons_of_mem
    {α : Type*} {a : α} {word : List α}
    (ha : a ∈ word) :
    ∃ tail, word.IsRotated (a :: tail) := by
  rw [List.mem_iff_append] at ha
  rcases ha with ⟨left, right, rfl⟩
  refine ⟨right ++ left, ?_⟩
  simpa only [List.cons_append, List.append_assoc] using
    (List.isRotated_append
      (l := left) (l' := a :: right))

/-- Recover a signed occurrence from membership in the projected unoriented edge word. -/
theorem exists_dart_of_mem_map_edgeOfDart
    {α : Type*} {e : α} {word : List (SignedDart α)}
    (he : e ∈ word.map edgeOfDart) :
    ∃ d ∈ word, edgeOfDart d = e := by
  rcases List.mem_map.mp he with ⟨d, hd, hde⟩
  exact ⟨d, hd, hde⟩

/-- A common edge displayed positively at the head of an oriented cyclic face boundary. -/
structure PositiveOccurrence
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge) where
  /-- The `orientedFace` declaration. -/
  orientedFace : P.OrientedFace
  face_eq : orientedFace.face = f
  /-- The `tail` declaration. -/
  tail : List P.Dart
  boundary_rotated :
    (P.orientedBoundary orientedFace).IsRotated (.pos e :: tail)

/-- A common edge displayed negatively at the head of an oriented cyclic face boundary. -/
structure NegativeOccurrence
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge) where
  /-- The `orientedFace` declaration. -/
  orientedFace : P.OrientedFace
  face_eq : orientedFace.face = f
  /-- The `tail` declaration. -/
  tail : List P.Dart
  boundary_rotated :
    (P.orientedBoundary orientedFace).IsRotated (.neg e :: tail)

/-- Choose the traversal orientation which displays a selected edge occurrence positively. -/
theorem exists_positiveOccurrence
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge)
    (he : e ∈ (P.boundary f).map edgeOfDart) :
    Nonempty (PositiveOccurrence P f e) := by
  rcases exists_dart_of_mem_map_edgeOfDart he with
    ⟨d, hd, hde⟩
  cases d with
  | pos a =>
      change a = e at hde
      subst e
      rcases exists_tail_isRotated_cons_of_mem hd with
        ⟨tail, hrotated⟩
      exact ⟨
        { orientedFace := ⟨f, false⟩
          face_eq := rfl
          tail := tail
          boundary_rotated := by
            simpa [FiniteCyclicPresentation.orientedBoundary] using
              hrotated }⟩
  | neg a =>
      change a = e at hde
      subst e
      have hpositive :
          SignedDart.pos a ∈ inverseWord (P.boundary f) := by
        rw [inverseWord]
        exact List.mem_map.mpr
          ⟨.neg a, by simpa using hd, rfl⟩
      rcases exists_tail_isRotated_cons_of_mem hpositive with
        ⟨tail, hrotated⟩
      exact ⟨
        { orientedFace := ⟨f, true⟩
          face_eq := rfl
          tail := tail
          boundary_rotated := by
            simpa [FiniteCyclicPresentation.orientedBoundary] using
              hrotated }⟩

/-- Reverse a positive displayed occurrence to obtain a negative displayed occurrence. -/
def PositiveOccurrence.flip
    {P : FiniteCyclicPresentation} {f : P.Face} {e : P.Edge}
    (occurrence : PositiveOccurrence P f e) :
    NegativeOccurrence P f e where
  orientedFace := occurrence.orientedFace.flip
  face_eq := occurrence.face_eq
  tail := inverseWord occurrence.tail
  boundary_rotated := by
    rw [P.orientedBoundary_flip]
    have hhead :
        (inverseWord (.pos e :: occurrence.tail)).IsRotated
          (.neg e :: inverseWord occurrence.tail) := by
      simpa [inverseWord, SignedDart.flip] using
        (List.isRotated_concat (.neg e) (inverseWord occurrence.tail))
    exact
      (inverseWord_isRotated occurrence.boundary_rotated).trans hhead

/-- The underlying stored face contains the positively displayed edge. -/
theorem PositiveOccurrence.edge_mem_boundary
    {P : FiniteCyclicPresentation} {f : P.Face} {e : P.Edge}
    (occurrence : PositiveOccurrence P f e) :
    e ∈ (P.boundary f).map edgeOfDart := by
  have hmapRotated :=
    occurrence.boundary_rotated.map edgeOfDart
  have horientedMem :
      e ∈ (P.orientedBoundary occurrence.orientedFace).map edgeOfDart :=
    hmapRotated.mem_iff.mpr (by simp [edgeOfDart])
  have horientedPositive :
      0 <
        ((P.orientedBoundary occurrence.orientedFace).map
          edgeOfDart).count e :=
    List.count_pos_iff.mpr horientedMem
  have hfacePositive :
      0 < P.faceEdgeMultiplicity occurrence.orientedFace.face e := by
    rw [← P.orientedBoundary_edgeMultiplicity
      occurrence.orientedFace e]
    exact horientedPositive
  rw [occurrence.face_eq] at hfacePositive
  exact List.count_pos_iff.mp hfacePositive

/-- The underlying stored face contains the negatively displayed edge. -/
theorem NegativeOccurrence.edge_mem_boundary
    {P : FiniteCyclicPresentation} {f : P.Face} {e : P.Edge}
    (occurrence : NegativeOccurrence P f e) :
    e ∈ (P.boundary f).map edgeOfDart := by
  have hmapRotated :=
    occurrence.boundary_rotated.map edgeOfDart
  have horientedMem :
      e ∈ (P.orientedBoundary occurrence.orientedFace).map edgeOfDart :=
    hmapRotated.mem_iff.mpr (by simp [edgeOfDart])
  have horientedPositive :
      0 <
        ((P.orientedBoundary occurrence.orientedFace).map
          edgeOfDart).count e :=
    List.count_pos_iff.mpr horientedMem
  have hfacePositive :
      0 < P.faceEdgeMultiplicity occurrence.orientedFace.face e := by
    rw [← P.orientedBoundary_edgeMultiplicity
      occurrence.orientedFace e]
    exact horientedPositive
  rw [occurrence.face_eq] at hfacePositive
  exact List.count_pos_iff.mp hfacePositive

/-- In two distinct incident faces, the displayed occurrence consumes the entire multiplicity
contributed by its face, so the same edge does not occur again in its tail. -/
theorem PositiveOccurrence.edge_not_mem_tail
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (occurrence : PositiveOccurrence P f e)
    (valid : P.IsSurfaceValid)
    (hfg : f ≠ g)
    (heg : e ∈ (P.boundary g).map edgeOfDart) :
    e ∉ occurrence.tail.map edgeOfDart := by
  classical
  have hmapRotated :=
    occurrence.boundary_rotated.map edgeOfDart
  have hpositive :
      e ∈ (P.orientedBoundary occurrence.orientedFace).map edgeOfDart := by
    exact hmapRotated.mem_iff.mpr (by simp [edgeOfDart])
  have hfpos : 0 < P.faceEdgeMultiplicity f e := by
    have horiented :=
      P.orientedBoundary_edgeMultiplicity occurrence.orientedFace e
    rw [← occurrence.face_eq, ← horiented]
    exact List.count_pos_iff.mpr hpositive
  have hgpos : 0 < P.faceEdgeMultiplicity g e := by
    exact List.count_pos_iff.mpr heg
  have htwo :
      P.faceEdgeMultiplicity f e + P.faceEdgeMultiplicity g e ≤
        P.edgeMultiplicity e :=
    add_faceEdgeMultiplicity_le_edgeMultiplicity P f g e hfg
  have htotal := valid.2.2.2 e
  have hfaceOne : P.faceEdgeMultiplicity f e = 1 := by
    rcases htotal with htotal | htotal <;> omega
  have horientedCount :
      ((P.orientedBoundary occurrence.orientedFace).map edgeOfDart).count e =
        P.faceEdgeMultiplicity f e := by
    simpa only [occurrence.face_eq] using
      P.orientedBoundary_edgeMultiplicity occurrence.orientedFace e
  have hrotatedCount := hmapRotated.perm.count_eq e
  have htailCount :
      (occurrence.tail.map edgeOfDart).count e = 0 := by
    rw [horientedCount, hfaceOne] at hrotatedCount
    simpa [edgeOfDart] using hrotatedCount.symm
  exact List.count_eq_zero.mp htailCount

/-- The corresponding no-second-occurrence statement for a negatively displayed face. -/
theorem NegativeOccurrence.edge_not_mem_tail
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (occurrence : NegativeOccurrence P f e)
    (valid : P.IsSurfaceValid)
    (hfg : f ≠ g)
    (heg : e ∈ (P.boundary g).map edgeOfDart) :
    e ∉ occurrence.tail.map edgeOfDart := by
  let positive : PositiveOccurrence P f e :=
    { orientedFace := occurrence.orientedFace.flip
      face_eq := occurrence.face_eq
      tail := inverseWord occurrence.tail
      boundary_rotated := by
        rw [P.orientedBoundary_flip]
        have hhead :
            (inverseWord (.neg e :: occurrence.tail)).IsRotated
              (.pos e :: inverseWord occurrence.tail) := by
          simpa [inverseWord, SignedDart.flip] using
            (List.isRotated_concat (.pos e) (inverseWord occurrence.tail))
        exact
          (inverseWord_isRotated occurrence.boundary_rotated).trans hhead }
  have hpositive :=
    positive.edge_not_mem_tail valid hfg heg
  simpa [positive, map_edgeOfDart_inverseWord] using hpositive

/-- The lowered left word used by the canonical contextual merge. -/
def mergeLeftWord
    {P : FiniteCyclicPresentation} {f : P.Face} {e : P.Edge}
    (occurrence : PositiveOccurrence P f e) :
    List (SignedDart (Fin (edgeCountAfterDelete P))) :=
  lowerTail P e occurrence.tail

/-- The lowered right word used by the canonical contextual merge. -/
def mergeRightWord
    {P : FiniteCyclicPresentation} {g : P.Face} {e : P.Edge}
    (occurrence : NegativeOccurrence P g e) :
    List (SignedDart (Fin (edgeCountAfterDelete P))) :=
  lowerTail P e occurrence.tail

/-- Lower and enumerate all faces not selected for a merge. -/
def mergeMiddleWords
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (f g : P.Face) (hfg : f ≠ g) :
    List (List (SignedDart (Fin (edgeCountAfterDelete P)))) :=
  (middleOriginalFaces P f g hfg).map
    (fun q ↦ lowerTail P e (P.boundary q))

theorem mergeMiddleWords_length
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (f g : P.Face) (hfg : f ≠ g) :
    (mergeMiddleWords P e f g hfg).length =
      faceCountBetween P := by
  simp [mergeMiddleWords]

theorem mergeMiddleWords_get
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (f g : P.Face) (hfg : f ≠ g)
    (i : Fin (faceCountBetween P)) :
    (mergeMiddleWords P e f g hfg).get
        ⟨i.val, by
          rw [mergeMiddleWords_length]
          exact i.isLt⟩ =
      lowerTail P e
        (P.boundary (middleOriginalFace P f g hfg i)) := by
  simp [mergeMiddleWords, middleOriginalFaces,
    middleOriginalFace]

theorem faceCountBetween_add_two
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) :
    faceCountBetween P + 2 = P.faces.length := by
  have hvalues : f.val ≠ g.val :=
    fun h ↦ hfg (Fin.ext h)
  have hmany : 1 < P.faces.length := by
    omega
  simp only [faceCountBetween]
  omega

/-- The canonical contextual P2 source associated to two oppositely displayed adjacent faces. -/
@[reducible]
def mergeSource
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    FiniteCyclicPresentation :=
  FaceMerge.ContextMerge.source
    (mergeLeftWord left) (mergeRightWord right)
    (mergeMiddleWords P e f g hfg)

/-- The presentation after merging the selected adjacent faces and deleting their separator. -/
@[reducible]
def mergeTarget
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    FiniteCyclicPresentation :=
  FaceMerge.ContextMerge.target
    (mergeLeftWord left) (mergeRightWord right)
    (mergeMiddleWords P e f g hfg)

@[simp]
theorem mergeSource_faces_length
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    (mergeSource left right hfg).faces.length =
      P.faces.length := by
  rw [show
    (mergeSource left right hfg).faces.length =
      (mergeMiddleWords P e f g hfg).length + 2 by
    rw [P2.split_faces_length]
    simp [FaceMerge.ContextMerge.target]]
  rw [mergeMiddleWords_length, faceCountBetween_add_two P f g hfg]

theorem mergeTarget_faces_length
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    (mergeTarget left right hfg).faces.length =
      P.faces.length - 1 := by
  change
    (mergeMiddleWords P e f g hfg).length + 1 =
      P.faces.length - 1
  rw [mergeMiddleWords_length]
  have hadd := faceCountBetween_add_two P f g hfg
  omega

/-- Reindex the input faces to the selected/interior/right ordering of its contextual merge
source. -/
def mergeFaceEquiv
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    P.Face ≃ (mergeSource left right hfg).Face :=
  (faceToEndpoints P f g).trans
    (finCongr (mergeSource_faces_length left right hfg).symm)

@[simp]
theorem mergeFaceEquiv_selected
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    mergeFaceEquiv left right hfg f =
      FaceMerge.ContextMerge.selectedFace
        (mergeLeftWord left) (mergeRightWord right)
        (mergeMiddleWords P e f g hfg) := by
  apply Fin.ext
  simp only [P2.split_edgeCount, mergeFaceEquiv, Equiv.trans_apply,
    faceToEndpoints_selected P f g hfg, FaceMerge.ContextMerge.selectedFace]
  change 0 = 0
  rfl

@[simp]
theorem mergeFaceEquiv_right
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    mergeFaceEquiv left right hfg g =
      FaceMerge.ContextMerge.rightFace
        (mergeLeftWord left) (mergeRightWord right)
        (mergeMiddleWords P e f g hfg) := by
  apply Fin.ext
  rw [show
    (mergeFaceEquiv left right hfg g).val =
      (lastFace P f).val by
    simp [mergeFaceEquiv]]
  change P.faces.length - 1 =
    (mergeMiddleWords P e f g hfg).length + 1
  rw [mergeMiddleWords_length]
  have hadd := faceCountBetween_add_two P f g hfg
  omega

@[simp]
theorem mergeFaceEquiv_middle
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (i : Fin (faceCountBetween P)) :
    mergeFaceEquiv left right hfg
        (middleOriginalFace P f g hfg i) =
      FaceMerge.ContextMerge.untouchedSourceFace
        (mergeLeftWord left) (mergeRightWord right)
        (mergeMiddleWords P e f g hfg)
        ⟨i.val, by
          rw [mergeMiddleWords_length]
          exact i.isLt⟩ := by
  apply Fin.ext
  simp only [P2.split_edgeCount, mergeFaceEquiv, middleOriginalFace,
    middleFacePosition, Equiv.trans_apply, Equiv.apply_symm_apply,
    FaceMerge.ContextMerge.untouchedSourceFace,
    FaceMerge.ContextMerge.untouchedTargetFace, List.length_cons]
  change i.val + 1 = i.val + 1
  rfl

/-- Reverse precisely the two selected source faces according to the traversals used to expose
their separator; untouched faces retain their stored orientation. -/
def mergeReverseFace
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (q : P.Face) :
    Bool :=
  if q = f then left.orientedFace.orientation
  else if q = g then right.orientedFace.orientation
  else false

/-- The arbitrary adjacent pair is the canonical contextual merge source after renaming the
separator, reordering faces, and choosing the two displayed traversal orientations. -/
def mergeUnorientedIso
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (valid : P.IsSurfaceValid) :
    UnorientedPresentationIso P (mergeSource left right hfg) := by
  apply unorientedIsoOfOrientedBoundaries
    (EdgeRelabeling.ofEquiv (edgeToLast P e))
    (mergeFaceEquiv left right hfg)
    (mergeReverseFace left right)
  intro q
  by_cases hqf : q = f
  · subst q
    rw [mergeFaceEquiv_selected,
      FaceMerge.ContextMerge.source_boundary_selected]
    have hreverse :
        mergeReverseFace left right f =
          left.orientedFace.orientation := by
      simp [mergeReverseFace]
    rw [hreverse]
    have horientedFace :
        (⟨f, left.orientedFace.orientation⟩ : P.OrientedFace) =
          left.orientedFace := by
      cases hleft : left.orientedFace with
      | mk face orientation =>
          have hface : face = f := by
            simpa [hleft] using left.face_eq
          subst face
          rfl
    rw [horientedFace]
    change
      ((P.orientedBoundary left.orientedFace).map
        (SignedDart.mapEquiv (edgeToLast P e))).IsRotated
          (P2.retainWord (lowerTail P e left.tail) ++
            [.pos (P1.freshEdge (edgeCountAfterDelete P))])
    rw [retainWord_lowerTail P e left.tail
      (left.edge_not_mem_tail valid hfg
        right.edge_mem_boundary)]
    have hmapped :=
      left.boundary_rotated.map
        (SignedDart.mapEquiv (edgeToLast P e))
    apply hmapped.trans
    change
      (SignedDart.pos (edgeToLast P e e) ::
          renamedTail P e left.tail).IsRotated
        (renamedTail P e left.tail ++
          [SignedDart.pos (P1.freshEdge
            (edgeCountAfterDelete P))])
    rw [edgeToLast_selected]
    exact List.IsRotated.cons_append_singleton
  · by_cases hqg : q = g
    · subst q
      rw [mergeFaceEquiv_right,
        FaceMerge.ContextMerge.source_boundary_right]
      have hreverse :
          mergeReverseFace left right g =
            right.orientedFace.orientation := by
        simp [mergeReverseFace, hfg.symm]
      rw [hreverse]
      have horientedFace :
          (⟨g, right.orientedFace.orientation⟩ : P.OrientedFace) =
            right.orientedFace := by
        cases hright : right.orientedFace with
        | mk face orientation =>
            have hface : face = g := by
              simpa [hright] using right.face_eq
            subst face
            rfl
      rw [horientedFace]
      change
        ((P.orientedBoundary right.orientedFace).map
          (SignedDart.mapEquiv (edgeToLast P e))).IsRotated
            ([.neg (P1.freshEdge (edgeCountAfterDelete P))] ++
              P2.retainWord (lowerTail P e right.tail))
      rw [retainWord_lowerTail P e right.tail
        (right.edge_not_mem_tail valid hfg.symm
          left.edge_mem_boundary)]
      have hmapped :=
        right.boundary_rotated.map
          (SignedDart.mapEquiv (edgeToLast P e))
      simpa [SignedDart.mapEquiv, edgeToLast_selected,
        renamedTail] using hmapped
    · rcases face_eq_selected_or_right_or_middle
        P f g q hfg with hselected | hright | ⟨i, hmiddle⟩
      · exact (hqf hselected).elim
      · exact (hqg hright).elim
      · subst q
        rw [mergeFaceEquiv_middle,
          FaceMerge.ContextMerge.source_boundary_untouched,
          mergeMiddleWords_get]
        have hmiddleF :
            middleOriginalFace P f g hfg i ≠ f := by
          intro h
          apply hqf
          exact h
        have hmiddleG :
            middleOriginalFace P f g hfg i ≠ g := by
          intro h
          apply hqg
          exact h
        rw [show
          mergeReverseFace left right
              (middleOriginalFace P f g hfg i) = false by
            simp [mergeReverseFace, hmiddleF, hmiddleG]]
        change
          ((P.boundary (middleOriginalFace P f g hfg i)).map
            (SignedDart.mapEquiv (edgeToLast P e))).IsRotated
              (P2.retainWord
                (lowerTail P e
                  (P.boundary
                    (middleOriginalFace P f g hfg i))))
        rw [retainWord_lowerTail P e
          (P.boundary (middleOriginalFace P f g hfg i))
          (edge_not_mem_boundary_of_other P valid f g
            (middleOriginalFace P f g hfg i) e hfg
            (Ne.symm hmiddleF) (Ne.symm hmiddleG)
            left.edge_mem_boundary right.edge_mem_boundary)]
        exact List.IsRotated.refl _

private theorem mergeSource_untouched_eq_of_boundary_rotated
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e) (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) (validP : P.IsSurfaceValid)
    (i j : Fin (mergeMiddleWords P e f g hfg).length)
    (h : ((mergeSource left right hfg).boundary
        (FaceMerge.ContextMerge.untouchedSourceFace (mergeLeftWord left)
          (mergeRightWord right) (mergeMiddleWords P e f g hfg) i)).IsRotated
      ((mergeSource left right hfg).boundary
        (FaceMerge.ContextMerge.untouchedSourceFace (mergeLeftWord left)
          (mergeRightWord right) (mergeMiddleWords P e f g hfg) j))) :
    FaceMerge.ContextMerge.untouchedSourceFace (mergeLeftWord left)
        (mergeRightWord right) (mergeMiddleWords P e f g hfg) i =
      FaceMerge.ContextMerge.untouchedSourceFace (mergeLeftWord left)
        (mergeRightWord right) (mergeMiddleWords P e f g hfg) j := by
  let U := mergeLeftWord left
  let V := mergeRightWord right
  let W := mergeMiddleWords P e f g hfg
  let iso := mergeUnorientedIso left right hfg validP
  let i' : Fin (faceCountBetween P) :=
    ⟨i.val, by simpa [W, mergeMiddleWords_length] using i.isLt⟩
  let j' : Fin (faceCountBetween P) :=
    ⟨j.val, by simpa [W, mergeMiddleWords_length] using j.isLt⟩
  let fi := middleOriginalFace P f g hfg i'
  let fj := middleOriginalFace P f g hfg j'
  have hfi : fi ≠ f := middleOriginalFace_ne_selected P f g hfg i'
  have hfig : fi ≠ g := middleOriginalFace_ne_right P f g hfg i'
  have hfj : fj ≠ f := middleOriginalFace_ne_selected P f g hfg j'
  have hfjg : fj ≠ g := middleOriginalFace_ne_right P f g hfg j'
  have hiFace : iso.faceEquiv fi =
      FaceMerge.ContextMerge.untouchedSourceFace U V W i := by
    apply Fin.ext
    change (mergeFaceEquiv left right hfg (middleOriginalFace P f g hfg i')).val = i.val + 1
    rw [mergeFaceEquiv_middle]
    rfl
  have hjFace : iso.faceEquiv fj =
      FaceMerge.ContextMerge.untouchedSourceFace U V W j := by
    apply Fin.ext
    change (mergeFaceEquiv left right hfg (middleOriginalFace P f g hfg j')).val = j.val + 1
    rw [mergeFaceEquiv_middle]
    rfl
  have hiReverse : mergeReverseFace left right fi = false := by
    simp [mergeReverseFace, hfi, hfig]
  have hjReverse : mergeReverseFace left right fj = false := by
    simp [mergeReverseFace, hfj, hfjg]
  have hiFace' : mergeFaceEquiv left right hfg fi =
      FaceMerge.ContextMerge.untouchedSourceFace U V W i := hiFace
  have hjFace' : mergeFaceEquiv left right hfg fj =
      FaceMerge.ContextMerge.untouchedSourceFace U V W j := hjFace
  have hi := iso.boundary_rotated fi
  have hj := iso.boundary_rotated fj
  change ((P.boundary fi).map iso.edgeRelabeling.mapDart).IsRotated
    ((mergeSource left right hfg).orientedBoundary
      ⟨mergeFaceEquiv left right hfg fi, mergeReverseFace left right fi⟩) at hi
  change ((P.boundary fj).map iso.edgeRelabeling.mapDart).IsRotated
    ((mergeSource left right hfg).orientedBoundary
      ⟨mergeFaceEquiv left right hfg fj, mergeReverseFace left right fj⟩) at hj
  have hi' : ((P.boundary fi).map iso.edgeRelabeling.mapDart).IsRotated
      ((mergeSource left right hfg).boundary
        (FaceMerge.ContextMerge.untouchedSourceFace U V W i)) := by
    rw [hiFace', hiReverse] at hi
    simpa [FiniteCyclicPresentation.orientedBoundary] using hi
  have hj' : ((P.boundary fj).map iso.edgeRelabeling.mapDart).IsRotated
      ((mergeSource left right hfg).boundary
        (FaceMerge.ContextMerge.untouchedSourceFace U V W j)) := by
    rw [hjFace', hjReverse] at hj
    simpa [FiniteCyclicPresentation.orientedBoundary] using hj
  have hmapped := hi'.trans (h.trans hj'.symm)
  have horiginal := hmapped.map iso.edgeRelabeling.symm.mapDart
  rw [EdgeRelabeling.map_mapDart_symm, EdgeRelabeling.map_mapDart_symm] at horiginal
  have hfij := validP.2.2.1 fi fj horiginal
  exact hiFace.symm.trans ((congrArg iso.faceEquiv hfij).trans hjFace)

/-- The specialized unoriented comparison used by an adjacent-face merge preserves ordinary
validity.  Reversing either selected face cannot create a duplicate: both selected faces contain
the fresh separator, untouched faces do not, and the two selected occurrences have opposite
signs. -/
theorem mergeSource_isSurfaceValid
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid) :
    (mergeSource left right hfg).IsSurfaceValid := by
  classical
  let U := mergeLeftWord left
  let V := mergeRightWord right
  let W := mergeMiddleWords P e f g hfg
  let base := FaceMerge.ContextMerge.target U V W
  let cut := FaceMerge.ContextMerge.targetCut U V W
  let iso := mergeUnorientedIso left right hfg validP
  have hfaces (q : (mergeSource left right hfg).Face) :
      q = FaceMerge.ContextMerge.selectedFace U V W ∨
        (∃ i : Fin W.length,
          q = FaceMerge.ContextMerge.untouchedSourceFace U V W i) ∨
        q = FaceMerge.ContextMerge.rightFace U V W := by
    rcases P2.face_cases base cut q with ⟨p, hp⟩ | hp
    · induction p using Fin.cases with
      | zero =>
          left
          rw [hp]
          apply Fin.ext
          rfl
      | succ i =>
          right
          left
          refine ⟨i, ?_⟩
          rw [hp]
          apply Fin.ext
          rfl
    · exact Or.inr (Or.inr hp)
  have hselectedRight
      (h :
        ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.selectedFace U V W)).IsRotated
          ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.rightFace U V W))) :
      False := by
    have hmem :
        P2.selectedFreshDart base cut ∈
          (mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.selectedFace U V W) := by
      change
        P2.selectedFreshDart base cut ∈
          (P2.split base cut).boundary
            (P2.oldFace base cut cut.face.face)
      rw [P2.split_boundary_selected]
      exact P2.selectedFreshDart_mem_selectedBoundary base cut
    have htarget := h.mem_iff.mp hmem
    change
      P2.selectedFreshDart base cut ∈
        (P2.split base cut).boundary (P2.rightFace base cut)
        at htarget
    rw [P2.split_boundary_right] at htarget
    exact P2.selectedFreshDart_not_mem_rightBoundary
      base cut htarget
  have hselectedUntouched
      (i : Fin W.length)
      (h :
        ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.selectedFace U V W)).IsRotated
          ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.untouchedSourceFace U V W i))) :
      False := by
    have hmem :
        P2.selectedFreshDart base cut ∈
          (mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.selectedFace U V W) := by
      change
        P2.selectedFreshDart base cut ∈
          (P2.split base cut).boundary
            (P2.oldFace base cut cut.face.face)
      rw [P2.split_boundary_selected]
      exact P2.selectedFreshDart_mem_selectedBoundary base cut
    have htarget := h.mem_iff.mp hmem
    rw [FaceMerge.ContextMerge.source_boundary_untouched] at htarget
    exact P2.selectedFreshDart_not_mem_retainWord
      base cut (W.get i) htarget
  have hrightUntouched
      (i : Fin W.length)
      (h :
        ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.rightFace U V W)).IsRotated
          ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.untouchedSourceFace U V W i))) :
      False := by
    have hmem :
        P2.rightFreshDart base cut ∈
          (mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.rightFace U V W) := by
      change
        P2.rightFreshDart base cut ∈
          (P2.split base cut).boundary (P2.rightFace base cut)
      rw [P2.split_boundary_right]
      exact P2.rightFreshDart_mem_rightBoundary base cut
    have htarget := h.mem_iff.mp hmem
    rw [FaceMerge.ContextMerge.source_boundary_untouched] at htarget
    exact P2.rightFreshDart_not_mem_retainWord
      base cut (W.get i) htarget
  have huntouched
      (i j : Fin W.length)
      (h :
        ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.untouchedSourceFace U V W i)).IsRotated
          ((mergeSource left right hfg).boundary
            (FaceMerge.ContextMerge.untouchedSourceFace U V W j))) :
      FaceMerge.ContextMerge.untouchedSourceFace U V W i =
        FaceMerge.ContextMerge.untouchedSourceFace U V W j :=
    mergeSource_untouched_eq_of_boundary_rotated left right hfg validP i j h
  refine ⟨iso.faceEquiv.nonempty_congr.mp validP.1, ?_, ?_, ?_⟩
  · intro q hq
    let p := iso.faceEquiv.symm q
    have hlength := iso.boundary_length_eq p
    rw [iso.faceEquiv.apply_symm_apply] at hlength
    have hp : (P.boundary p).length = 0 := by
      simpa only [hq, List.length_nil] using hlength
    exact validP.2.1 p (List.length_eq_zero_iff.mp hp)
  · intro q r hqr
    rcases hfaces q with hq | ⟨i, hq⟩ | hq <;>
      rcases hfaces r with hr | ⟨j, hr⟩ | hr
    · exact hq.trans hr.symm
    · subst q
      subst r
      exact (hselectedUntouched j hqr).elim
    · subst q
      subst r
      exact (hselectedRight hqr).elim
    · subst q
      subst r
      exact (hselectedUntouched i hqr.symm).elim
    · subst q
      subst r
      exact huntouched i j hqr
    · subst q
      subst r
      exact (hrightUntouched i hqr.symm).elim
    · subst q
      subst r
      exact (hselectedRight hqr.symm).elim
    · subst q
      subst r
      exact (hrightUntouched j hqr).elim
    · exact hq.trans hr.symm
  · intro b
    let a := iso.edgeEquiv.symm b
    have hmultiplicity := validP.2.2.2 a
    rw [iso.edgeMultiplicity_eq] at hmultiplicity
    dsimp [a] at hmultiplicity
    simpa only [iso.edgeEquiv.apply_symm_apply] using hmultiplicity

/-- The validity-safe result of merging an arbitrary adjacent pair while retaining its separator
as a cancellable adjacent inverse marker. -/
@[reducible]
def markedMergeTarget
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    FiniteCyclicPresentation :=
  FaceMerge.ContextMerge.markedTarget
    (mergeLeftWord left) (mergeRightWord right)
    (mergeMiddleWords P e f g hfg)

/-- An arbitrary marked merge preserves strict ordinary validity. -/
theorem markedMergeTarget_isSurfaceValid
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid) :
    (markedMergeTarget left right hfg).IsSurfaceValid :=
  FaceMerge.ContextMerge.markedTarget_isSurfaceValid
    (mergeLeftWord left) (mergeRightWord right)
    (mergeMiddleWords P e f g hfg)
    (mergeSource_isSurfaceValid left right hfg validP)

/-- An arbitrary marked merge preserves face-incidence connectivity. -/
theorem markedMergeTarget_isConnected
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid)
    (connectedP : P.IsConnected) :
    (markedMergeTarget left right hfg).IsConnected :=
  FaceMerge.ContextMerge.markedTarget_isConnected
    (mergeLeftWord left) (mergeRightWord right)
    (mergeMiddleWords P e f g hfg)
    ((mergeUnorientedIso left right hfg validP).isConnected connectedP)

/-- Merge any oppositely displayed adjacent pair without a target-validity side condition.  The
retained inverse marker is canceled only after the face recursion, preventing intermediate cyclic
duplicate faces. -/
theorem markedMergeNormalizationEquivalent
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨P, validP⟩
      ⟨markedMergeTarget left right hfg,
        markedMergeTarget_isSurfaceValid left right hfg validP⟩ := by
  let validSource :=
    mergeSource_isSurfaceValid left right hfg validP
  have hsource :
      NormalizationEquivalent
        ⟨P, validP⟩
        ⟨mergeSource left right hfg, validSource⟩ :=
    NormalizationEquivalent.ofUnorientedIso
      (mergeUnorientedIso left right hfg validP)
  exact hsource.trans
    (FaceMerge.ContextMerge.markedNormalizationEquivalent
      (mergeLeftWord left) (mergeRightWord right)
      (mergeMiddleWords P e f g hfg) validSource)

/-- A marked merge removes exactly one face. -/
theorem markedMergeTarget_faces_length
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g) :
    (markedMergeTarget left right hfg).faces.length =
      P.faces.length - 1 := by
  simp only [markedMergeTarget,
    FaceMerge.ContextMerge.markedTarget,
    List.length_cons, List.length_map]
  rw [mergeMiddleWords_length]
  have hadd := faceCountBetween_add_two P f g hfg
  omega

/-- Faithful polygonal-realization invariance of the arbitrary marked merge. -/
theorem markedMergePolygonallyEquivalent
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent
      (markedMergeTarget left right hfg) validP
      (markedMergeTarget_isSurfaceValid left right hfg validP) :=
  (markedMergeNormalizationEquivalent
    left right hfg validP).polygonallyEquivalent

/-- Merge an arbitrary oppositely displayed adjacent pair. Target validity remains explicit:
under the project's strict stored-word uniqueness clause, a merge can make its new word coincide
cyclically with an untouched face. -/
theorem mergeNormalizationEquivalent
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid)
    (validTarget : (mergeTarget left right hfg).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨P, validP⟩
      ⟨mergeTarget left right hfg, validTarget⟩ := by
  let U := mergeLeftWord left
  let V := mergeRightWord right
  let W := mergeMiddleWords P e f g hfg
  have hUV : U ++ V ≠ [] := by
    let first :
        (FaceMerge.ContextMerge.target U V W).Face :=
      ⟨0, by simp [FaceMerge.ContextMerge.target]⟩
    intro hempty
    apply validTarget.2.1 first
    change U ++ V = []
    exact hempty
  let validSource :
      (FaceMerge.ContextMerge.source U V W).IsSurfaceValid :=
    P2.split_isSurfaceValid
      (FaceMerge.ContextMerge.target U V W)
      (FaceMerge.ContextMerge.targetCut U V W)
      validTarget
  have hiso :
      NormalizationEquivalent
        ⟨P, validP⟩
        ⟨FaceMerge.ContextMerge.source U V W, validSource⟩ := by
    apply NormalizationEquivalent.ofUnorientedIso
    exact mergeUnorientedIso left right hfg validP
  exact hiso.trans
    (FaceMerge.ContextMerge.normalizationEquivalent
      U V W hUV validTarget)

/-- Faithful polygonal-realization invariance of the arbitrary adjacent-face merge. -/
theorem mergePolygonallyEquivalent
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (left : PositiveOccurrence P f e)
    (right : NegativeOccurrence P g e)
    (hfg : f ≠ g)
    (validP : P.IsSurfaceValid)
    (validTarget : (mergeTarget left right hfg).IsSurfaceValid) :
    P.PolygonallyEquivalent
      (mergeTarget left right hfg) validP validTarget :=
  (mergeNormalizationEquivalent
    left right hfg validP validTarget).polygonallyEquivalent

/-- Choose the traversal orientation which displays a selected edge occurrence negatively. -/
theorem exists_negativeOccurrence
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge)
    (he : e ∈ (P.boundary f).map edgeOfDart) :
    Nonempty (NegativeOccurrence P f e) := by
  rcases exists_positiveOccurrence P f e he with ⟨occurrence⟩
  exact ⟨occurrence.flip⟩

/-- A distinct adjacent pair can always be oriented with positive and negative occurrences of
the same separator displayed at the heads of its two cyclic boundaries. -/
theorem exists_oppositelyDisplayedAdjacentFaces
    (P : FiniteCyclicPresentation)
    (connected : P.IsConnected)
    (hmany : 1 < P.faces.length) :
    ∃ (f g : P.Face) (e : P.Edge),
      f ≠ g ∧
        Nonempty (PositiveOccurrence P f e) ∧
        Nonempty (NegativeOccurrence P g e) := by
  rcases exists_distinct_faceAdjacent P connected hmany with
    ⟨f, g, hfg, e, hef, heg⟩
  exact
    ⟨f, g, e, hfg,
      exists_positiveOccurrence P f e hef,
      exists_negativeOccurrence P g e heg⟩

/-- The validity-safe output of merging a connected presentation down to one face. -/
structure OneFaceReduction (P : ValidPresentation) where
  /-- The `target` declaration. -/
  target : ValidPresentation
  connected : target.presentation.IsConnected
  faces_length : target.presentation.faces.length = 1
  equivalent : NormalizationEquivalent P target

/-- Repeated marked merges reduce every connected ordinary-valid presentation to one face.

Each merge retains its separator as an adjacent inverse marker.  Consequently every recursive
target remains strictly valid even when deleting the separator immediately would duplicate an
untouched cyclic face word. -/
noncomputable def reduceToOneFace
    (P : ValidPresentation)
    (connectedP : P.presentation.IsConnected) :
    OneFaceReduction P := by
  classical
  by_cases hone : P.presentation.faces.length = 1
  · exact
      { target := P
        connected := connectedP
        faces_length := hone
        equivalent := NormalizationEquivalent.refl P }
  · have hpositive : 0 < P.presentation.faces.length := by
      rcases P.valid.1 with ⟨f⟩
      have hf := f.isLt
      omega
    have hmany : 1 < P.presentation.faces.length := by
      omega
    have hwitness :=
      exists_oppositelyDisplayedAdjacentFaces
        P.presentation connectedP hmany
    let f := Classical.choose hwitness
    have hwitnessF := Classical.choose_spec hwitness
    let g := Classical.choose hwitnessF
    have hwitnessG := Classical.choose_spec hwitnessF
    let e := Classical.choose hwitnessG
    have hdisplayed := Classical.choose_spec hwitnessG
    have hfg : f ≠ g := hdisplayed.1
    let left := Classical.choice hdisplayed.2.1
    let right := Classical.choice hdisplayed.2.2
    let validTarget :=
      markedMergeTarget_isSurfaceValid left right hfg P.valid
    let target : ValidPresentation :=
      ⟨markedMergeTarget left right hfg, validTarget⟩
    have connectedTarget : target.presentation.IsConnected :=
      markedMergeTarget_isConnected
        left right hfg P.valid connectedP
    have firstEquivalent : NormalizationEquivalent P target :=
      markedMergeNormalizationEquivalent left right hfg P.valid
    have result : OneFaceReduction target :=
      reduceToOneFace target connectedTarget
    exact
      { target := result.target
        connected := result.connected
        faces_length := result.faces_length
        equivalent := firstEquivalent.trans result.equivalent }
termination_by P.presentation.faces.length
decreasing_by
  rw [markedMergeTarget_faces_length]
  omega

end Reduction

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
