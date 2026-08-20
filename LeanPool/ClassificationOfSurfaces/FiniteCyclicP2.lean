/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP1

/-!
# Gallier--Xu P2 face subdivision

This file formalizes the second primitive subdivision from Gallier--Xu, Definition 6.3. A cyclic
boundary is cut, in a chosen traversal orientation, into two pieces `left` and `right`. The
presentation-level construction permits empty pieces so that it also expresses Gallier--Xu's
exceptional empty-word-sphere conversion. The public `P2Subdivision` relation requires both
pieces to be nonempty for an ordinary face subdivision. The selected face is replaced by two
faces whose boundaries in that same orientation
are

* `left d`, and
* `d⁻¹ right`,

where `d` is a fresh edge.

The orientation stored on the two target faces is the orientation chosen by the cut. In
particular, a negatively oriented cut deliberately stores the inverses of the displayed words;
it does not claim to preserve the old positive stored orientation. This convention makes
reversing a cut exchange the two children exactly.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace FiniteCyclicPresentation

open SurfaceCellComplex

/-- A cyclic, oriented place at which to apply Gallier--Xu P2.

The decomposition is cyclic rather than tied to the stored head of the list. Empty `left` or
`right` pieces are allowed. -/
structure P2Cut (P : FiniteCyclicPresentation) where
  /-- The `face` declaration. -/
  face : P.OrientedFace
  /-- The `left` declaration. -/
  left : List P.Dart
  /-- The `right` declaration. -/
  right : List P.Dart
  boundary_rotated : (P.orientedBoundary face).IsRotated (left ++ right)

namespace P2Cut

/-- A genuine face cut has an old boundary side on each side of the new cutting edge.

The raw `P2Cut` structure also represents the exceptional empty-word-sphere conversion, for which
both pieces are necessarily empty. -/
def IsNondegenerate {P : FiniteCyclicPresentation} (cut : P2Cut P) : Prop :=
  cut.left ≠ [] ∧ cut.right ≠ []

theorem isNondegenerate_iff_lengths_pos {P : FiniteCyclicPresentation}
    (cut : P2Cut P) :
    cut.IsNondegenerate ↔ 0 < cut.left.length ∧ 0 < cut.right.length := by
  simp only [IsNondegenerate, List.length_pos_iff_ne_nil]

/-- Cut a chosen oriented representative at a linear position. -/
def canonical {P : FiniteCyclicPresentation} (face : P.OrientedFace)
    (position : Fin ((P.orientedBoundary face).length + 1)) : P2Cut P where
  face := face
  left := (P.orientedBoundary face).take position
  right := (P.orientedBoundary face).drop position
  boundary_rotated := by
    simpa only [List.take_append_drop] using
      List.IsRotated.refl (P.orientedBoundary face)

@[simp]
theorem canonical_face {P : FiniteCyclicPresentation} (face : P.OrientedFace)
    (position : Fin ((P.orientedBoundary face).length + 1)) :
    (canonical face position).face = face :=
  rfl

@[simp]
theorem canonical_zero_left {P : FiniteCyclicPresentation} (face : P.OrientedFace) :
    (canonical face 0).left = [] :=
  rfl

@[simp]
theorem canonical_zero_right {P : FiniteCyclicPresentation} (face : P.OrientedFace) :
    (canonical face 0).right = P.orientedBoundary face :=
  rfl

@[simp]
theorem canonical_last_left {P : FiniteCyclicPresentation} (face : P.OrientedFace) :
    (canonical face (Fin.last (P.orientedBoundary face).length)).left =
      P.orientedBoundary face := by
  simp [canonical]

@[simp]
theorem canonical_last_right {P : FiniteCyclicPresentation} (face : P.OrientedFace) :
    (canonical face (Fin.last (P.orientedBoundary face).length)).right = [] := by
  simp [canonical]

/-- Move the cyclic cut point to the other end of the two pieces. -/
def swap {P : FiniteCyclicPresentation} (cut : P2Cut P) : P2Cut P where
  face := cut.face
  left := cut.right
  right := cut.left
  boundary_rotated :=
    cut.boundary_rotated.trans List.isRotated_append

/-- Reverse the traversal orientation of a cut. -/
def flip {P : FiniteCyclicPresentation} (cut : P2Cut P) : P2Cut P where
  face := cut.face.flip
  left := inverseWord cut.right
  right := inverseWord cut.left
  boundary_rotated := by
    rw [P.orientedBoundary_flip]
    simpa only [inverseWord_append] using
      inverseWord_isRotated cut.boundary_rotated

@[simp]
theorem swap_face {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.swap.face = cut.face :=
  rfl

@[simp]
theorem flip_face {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.flip.face = cut.face.flip :=
  rfl

@[simp]
theorem swap_swap {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.swap.swap = cut := by
  cases cut
  rfl

@[simp]
theorem flip_flip {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.flip.flip = cut := by
  cases cut
  simp [flip]

theorem swap_flip {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.swap.flip = cut.flip.swap := by
  cases cut
  rfl

@[simp]
theorem isNondegenerate_swap {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.swap.IsNondegenerate ↔ cut.IsNondegenerate := by
  rw [isNondegenerate_iff_lengths_pos, isNondegenerate_iff_lengths_pos]
  change
    (0 < cut.right.length ∧ 0 < cut.left.length) ↔
      0 < cut.left.length ∧ 0 < cut.right.length
  exact and_comm

@[simp]
theorem isNondegenerate_flip {P : FiniteCyclicPresentation} (cut : P2Cut P) :
    cut.flip.IsNondegenerate ↔ cut.IsNondegenerate := by
  rw [isNondegenerate_iff_lengths_pos, isNondegenerate_iff_lengths_pos]
  change
    (0 < (inverseWord cut.right).length ∧
      0 < (inverseWord cut.left).length) ↔
        0 < cut.left.length ∧ 0 < cut.right.length
  simp only [inverseWord_length]
  exact and_comm

end P2Cut

namespace P2

/-- The fresh cutting edge. -/
def freshEdge (P : FiniteCyclicPresentation) : Fin (P.edgeCount + 1) :=
  P1.freshEdge P.edgeCount

/-- Retain an old boundary word in the enlarged edge type. -/
def retainWord {n : ℕ} (word : List (SignedDart (Fin n))) :
    List (SignedDart (Fin (n + 1))) :=
  word.map P1.castSuccDart

/-- Store a displayed oriented boundary in the presentation's positive orientation. -/
def storedWord {α : Type*} (orientation : Bool)
    (word : List (SignedDart α)) : List (SignedDart α) :=
  if orientation then inverseWord word else word

@[simp]
theorem retainWord_nil {n : ℕ} :
    retainWord ([] : List (SignedDart (Fin n))) = [] :=
  rfl

@[simp]
theorem retainWord_append {n : ℕ}
    (left right : List (SignedDart (Fin n))) :
    retainWord (left ++ right) = retainWord left ++ retainWord right := by
  simp [retainWord]

@[simp]
theorem castSuccDart_flip {n : ℕ} (d : SignedDart (Fin n)) :
    P1.castSuccDart d.flip = (P1.castSuccDart d).flip := by
  cases d <;> rfl

@[simp]
theorem retainWord_inverseWord {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    retainWord (inverseWord word) = inverseWord (retainWord word) := by
  simp [retainWord, inverseWord, List.map_map, Function.comp_def]

@[simp]
theorem storedWord_false {α : Type*} (word : List (SignedDart α)) :
    storedWord false word = word :=
  rfl

@[simp]
theorem storedWord_true {α : Type*} (word : List (SignedDart α)) :
    storedWord true word = inverseWord word :=
  rfl

/-- Reading a stored word in its selected orientation returns the displayed word. -/
@[simp]
theorem oriented_storedWord {α : Type*} (orientation : Bool)
    (word : List (SignedDart α)) :
    (if orientation then inverseWord (storedWord orientation word)
      else storedWord orientation word) = word := by
  cases orientation <;> simp [storedWord]

@[simp]
theorem contractDart_castSuccDart {n : ℕ} (d : SignedDart (Fin n)) :
    P1.contractDart (P1.castSuccDart d) = some d := by
  cases d <;> simp [P1.contractDart, P1.castSuccDart]

@[simp]
theorem contractWord_retainWord {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    P1.contractWord (retainWord word) = word := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      rw [retainWord, List.map_cons]
      rw [P1.contractWord]
      simp only [List.filterMap_cons, contractDart_castSuccDart]
      exact congrArg (List.cons d) ih

/-- The first displayed child boundary. -/
def selectedOrientedBoundary (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    List (SignedDart (Fin (P.edgeCount + 1))) :=
  retainWord cut.left ++ [.pos (freshEdge P)]

/-- The second displayed child boundary. -/
def rightOrientedBoundary (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    List (SignedDart (Fin (P.edgeCount + 1))) :=
  .neg (freshEdge P) :: retainWord cut.right

/-- The first child boundary in its stored orientation. -/
def selectedBoundary (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    List (SignedDart (Fin (P.edgeCount + 1))) :=
  storedWord cut.face.orientation (selectedOrientedBoundary P cut)

/-- The second child boundary in its stored orientation. -/
def rightBoundary (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    List (SignedDart (Fin (P.edgeCount + 1))) :=
  storedWord cut.face.orientation (rightOrientedBoundary P cut)

/-- The word stored at a target face index. -/
def faceWord (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    Fin (P.faces.length + 1) → List (SignedDart (Fin (P.edgeCount + 1))) :=
  Fin.lastCases (rightBoundary P cut) fun f ↦
    if f = cut.face.face then
      selectedBoundary P cut
    else
      retainWord (P.boundary f)

/-- Canonical presentation-level P2 face split. -/
abbrev split (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    FiniteCyclicPresentation where
  edgeCount := P.edgeCount + 1
  faces := List.ofFn (faceWord P cut)

@[simp]
theorem split_edgeCount (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).edgeCount = P.edgeCount + 1 :=
  rfl

theorem split_faces_length (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).faces.length = P.faces.length + 1 := by
  simp [split]

/-- Identify the explicit target indexing type with the presentation's face type. -/
def faceEquiv (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    Fin (P.faces.length + 1) ≃ (split P cut).Face :=
  finCongr (split_faces_length P cut).symm

/-- The target face occupying an old source-face position. -/
def oldFace (P : FiniteCyclicPresentation) (cut : P2Cut P) (f : P.Face) :
    (split P cut).Face :=
  faceEquiv P cut f.castSucc

/-- The fresh second child face. -/
def rightFace (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).Face :=
  faceEquiv P cut (Fin.last P.faces.length)

@[simp]
theorem faceEquiv_apply_val (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (f : Fin (P.faces.length + 1)) :
    (faceEquiv P cut f).val = f.val :=
  rfl

theorem face_cases (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : (split P cut).Face) :
    (∃ f : P.Face, q = oldFace P cut f) ∨ q = rightFace P cut := by
  let i := (faceEquiv P cut).symm q
  have hi : faceEquiv P cut i = q :=
    (faceEquiv P cut).apply_symm_apply q
  refine Fin.lastCases
    (motive := fun j ↦ faceEquiv P cut j = q →
      (∃ f : P.Face, q = oldFace P cut f) ∨ q = rightFace P cut)
    ?_ (fun f h ↦ Or.inl ⟨f, h.symm⟩) i hi
  intro h
  exact Or.inr h.symm

@[simp]
theorem split_boundary_index (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : Fin (P.faces.length + 1)) :
    (split P cut).boundary (faceEquiv P cut q) = faceWord P cut q := by
  unfold boundary split
  rw [List.get_ofFn]
  apply congrArg (faceWord P cut)
  apply Fin.ext
  rfl

@[simp]
theorem split_boundary_old (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (f : P.Face) :
    (split P cut).boundary (oldFace P cut f) =
      if f = cut.face.face then
        selectedBoundary P cut
      else
        retainWord (P.boundary f) := by
  simp [oldFace, faceWord]

theorem split_boundary_selected (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).boundary (oldFace P cut cut.face.face) =
      selectedBoundary P cut := by
  simp

theorem split_boundary_old_of_ne (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (h : f ≠ cut.face.face) :
    (split P cut).boundary (oldFace P cut f) =
      retainWord (P.boundary f) := by
  simp [h]

@[simp]
theorem split_boundary_right (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).boundary (rightFace P cut) = rightBoundary P cut := by
  simp [rightFace, faceWord]

/-- The selected child has exactly the displayed oriented boundary `left d`. -/
theorem split_orientedBoundary_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).orientedBoundary
        ⟨oldFace P cut cut.face.face, cut.face.orientation⟩ =
      selectedOrientedBoundary P cut := by
  rw [orientedBoundary]
  simp only [split_boundary_selected]
  exact oriented_storedWord cut.face.orientation _

/-- The right child has exactly the displayed oriented boundary `d⁻¹ right`. -/
theorem split_orientedBoundary_right
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).orientedBoundary
        ⟨rightFace P cut, cut.face.orientation⟩ =
      rightOrientedBoundary P cut := by
  rw [orientedBoundary]
  simp only [split_boundary_right]
  exact oriented_storedWord cut.face.orientation _

/-- Retaining a word preserves whether it is empty. -/
@[simp]
theorem retainWord_eq_nil_iff {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    retainWord word = [] ↔ word = [] := by
  exact List.map_eq_nil_iff

/-- Retaining a word preserves the multiplicity of every old edge. -/
theorem count_retainWord_castSucc {n : ℕ} (e : Fin n)
    (word : List (SignedDart (Fin n))) :
    ((retainWord word).map edgeOfDart).count e.castSucc =
      (word.map edgeOfDart).count e := by
  have hcount :=
    List.count_map_of_injective (word.map edgeOfDart)
      Fin.castSucc (Fin.castSucc_injective n) e
  simpa [retainWord, List.map_map, Function.comp_def] using hcount

/-- Reversing the stored traversal does not change unoriented edge multiplicities. -/
theorem count_storedWord (orientation : Bool) {α : Type*} [DecidableEq α]
    (word : List (SignedDart α)) (e : α) :
    ((storedWord orientation word).map edgeOfDart).count e =
      (word.map edgeOfDart).count e := by
  cases orientation
  · rfl
  · rw [storedWord_true, map_edgeOfDart_inverseWord]
    exact (List.reverse_perm _).count_eq e

/-- The fresh edge does not occur in a retained old word. -/
theorem freshEdge_not_mem_retainWord
    (P : FiniteCyclicPresentation) (word : List P.Dart) :
    freshEdge P ∉ (retainWord word).map edgeOfDart := by
  intro h
  rcases List.mem_map.mp h with ⟨d, hd, hedge⟩
  rcases List.mem_map.mp hd with ⟨old, hold, rfl⟩
  have hlast : (edgeOfDart old).castSucc ≠ freshEdge P := by
    exact P1.firstSubedge_ne_freshEdge (edgeOfDart old)
  exact hlast (P1.edgeOfDart_castSuccDart old ▸ hedge)

@[simp]
theorem pos_freshEdge_not_mem_retainWord
    (P : FiniteCyclicPresentation) (word : List P.Dart) :
    SignedDart.pos (freshEdge P) ∉ retainWord word := by
  intro h
  exact freshEdge_not_mem_retainWord P word
    (List.mem_map.mpr ⟨.pos (freshEdge P), h, rfl⟩)

@[simp]
theorem neg_freshEdge_not_mem_retainWord
    (P : FiniteCyclicPresentation) (word : List P.Dart) :
    SignedDart.neg (freshEdge P) ∉ retainWord word := by
  intro h
  exact freshEdge_not_mem_retainWord P word
    (List.mem_map.mpr ⟨.neg (freshEdge P), h, rfl⟩)

@[simp]
theorem pos_freshEdge_not_mem_inverse_retainWord
    (P : FiniteCyclicPresentation) (word : List P.Dart) :
    SignedDart.pos (freshEdge P) ∉ inverseWord (retainWord word) := by
  intro h
  have hedge :
      freshEdge P ∈ (inverseWord (retainWord word)).map edgeOfDart :=
    List.mem_map.mpr ⟨.pos (freshEdge P), h, rfl⟩
  rw [map_edgeOfDart_inverseWord] at hedge
  exact freshEdge_not_mem_retainWord P word (List.mem_reverse.mp hedge)

@[simp]
theorem neg_freshEdge_not_mem_inverse_retainWord
    (P : FiniteCyclicPresentation) (word : List P.Dart) :
    SignedDart.neg (freshEdge P) ∉ inverseWord (retainWord word) := by
  intro h
  have hedge :
      freshEdge P ∈ (inverseWord (retainWord word)).map edgeOfDart :=
    List.mem_map.mpr ⟨.neg (freshEdge P), h, rfl⟩
  rw [map_edgeOfDart_inverseWord] at hedge
  exact freshEdge_not_mem_retainWord P word (List.mem_reverse.mp hedge)

/-- The signed fresh dart occurring in the selected child. -/
def selectedFreshDart (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    SignedDart (Fin (P.edgeCount + 1)) :=
  if cut.face.orientation then .neg (freshEdge P) else .pos (freshEdge P)

/-- The opposite signed fresh dart occurring in the right child. -/
def rightFreshDart (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    SignedDart (Fin (P.edgeCount + 1)) :=
  (selectedFreshDart P cut).flip

@[simp]
theorem edgeOfDart_selectedFreshDart
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    edgeOfDart (selectedFreshDart P cut) = freshEdge P := by
  cases h : cut.face.orientation <;>
    simp [selectedFreshDart, h, edgeOfDart]

@[simp]
theorem edgeOfDart_rightFreshDart
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    edgeOfDart (rightFreshDart P cut) = freshEdge P := by
  rw [rightFreshDart, edgeOfDart_flip, edgeOfDart_selectedFreshDart]

theorem selectedBoundary_of_orientation_false
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : cut.face.orientation = false) :
    selectedBoundary P cut =
      retainWord cut.left ++ [.pos (freshEdge P)] := by
  simp [selectedBoundary, selectedOrientedBoundary, storedWord, h]

theorem selectedBoundary_of_orientation_true
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : cut.face.orientation = true) :
    selectedBoundary P cut =
      .neg (freshEdge P) :: inverseWord (retainWord cut.left) := by
  simp [selectedBoundary, selectedOrientedBoundary, storedWord, h,
    inverseWord, SignedDart.flip]

theorem rightBoundary_of_orientation_false
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : cut.face.orientation = false) :
    rightBoundary P cut =
      .neg (freshEdge P) :: retainWord cut.right := by
  simp [rightBoundary, rightOrientedBoundary, storedWord, h]

theorem rightBoundary_of_orientation_true
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : cut.face.orientation = true) :
    rightBoundary P cut =
      inverseWord (retainWord cut.right) ++ [.pos (freshEdge P)] := by
  simp [rightBoundary, rightOrientedBoundary, storedWord, h,
    inverseWord, SignedDart.flip]

/-- Reversing the cut exchanges its selected child with the original right child. -/
@[simp]
theorem selectedBoundary_flip
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    selectedBoundary P cut.flip = rightBoundary P cut := by
  cases h : cut.face.orientation
  · have hflip : cut.flip.face.orientation = true := by
      simp [P2Cut.flip, OrientedFace.flip, h]
    rw [selectedBoundary_of_orientation_true P cut.flip hflip]
    rw [rightBoundary_of_orientation_false P cut h]
    simp [P2Cut.flip]
  · have hflip : cut.flip.face.orientation = false := by
      simp [P2Cut.flip, OrientedFace.flip, h]
    rw [selectedBoundary_of_orientation_false P cut.flip hflip]
    rw [rightBoundary_of_orientation_true P cut h]
    simp [P2Cut.flip]

/-- Reversing the cut exchanges its right child with the original selected child. -/
@[simp]
theorem rightBoundary_flip
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    rightBoundary P cut.flip = selectedBoundary P cut := by
  simpa only [P2Cut.flip_flip] using
    (selectedBoundary_flip P cut.flip).symm

theorem selectedFreshDart_mem_selectedBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    selectedFreshDart P cut ∈ selectedBoundary P cut := by
  cases h : cut.face.orientation
  · rw [selectedBoundary_of_orientation_false P cut h]
    simp [selectedFreshDart, h]
  · rw [selectedBoundary_of_orientation_true P cut h]
    simp [selectedFreshDart, h]

theorem selectedFreshDart_not_mem_rightBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    selectedFreshDart P cut ∉ rightBoundary P cut := by
  cases h : cut.face.orientation
  · rw [rightBoundary_of_orientation_false P cut h]
    simp [selectedFreshDart, h]
  · rw [rightBoundary_of_orientation_true P cut h]
    simp [selectedFreshDart, h]

theorem rightFreshDart_mem_rightBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    rightFreshDart P cut ∈ rightBoundary P cut := by
  cases h : cut.face.orientation
  · rw [rightBoundary_of_orientation_false P cut h]
    simp [rightFreshDart, selectedFreshDart, h, SignedDart.flip]
  · rw [rightBoundary_of_orientation_true P cut h]
    simp [rightFreshDart, selectedFreshDart, h, SignedDart.flip]

theorem rightFreshDart_not_mem_selectedBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    rightFreshDart P cut ∉ selectedBoundary P cut := by
  cases h : cut.face.orientation
  · rw [selectedBoundary_of_orientation_false P cut h]
    simp [rightFreshDart, selectedFreshDart, h, SignedDart.flip]
  · rw [selectedBoundary_of_orientation_true P cut h]
    simp [rightFreshDart, selectedFreshDart, h, SignedDart.flip]

theorem selectedFreshDart_not_mem_retainWord
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (word : List P.Dart) :
    selectedFreshDart P cut ∉ retainWord word := by
  cases h : cut.face.orientation <;>
    simp [selectedFreshDart, h]

theorem rightFreshDart_not_mem_retainWord
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (word : List P.Dart) :
    rightFreshDart P cut ∉ retainWord word := by
  cases h : cut.face.orientation <;>
    simp [rightFreshDart, selectedFreshDart, h, SignedDart.flip]

/-- The selected child receives the old-edge occurrences in the left cut piece. -/
theorem faceEdgeMultiplicity_split_selected_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (e : P.Edge) :
    (split P cut).faceEdgeMultiplicity (oldFace P cut cut.face.face) e.castSucc =
      (cut.left.map edgeOfDart).count e := by
  unfold faceEdgeMultiplicity
  rw [split_boundary_selected]
  calc
    ((selectedBoundary P cut).map edgeOfDart).count e.castSucc =
        ((selectedOrientedBoundary P cut).map edgeOfDart).count e.castSucc :=
      count_storedWord cut.face.orientation _ _
    _ = (cut.left.map edgeOfDart).count e := by
      have hne : e.castSucc ≠ freshEdge P :=
        P1.firstSubedge_ne_freshEdge e
      have hne' : freshEdge P ≠ e.castSucc :=
        Ne.symm hne
      simp [selectedOrientedBoundary, edgeOfDart,
        count_retainWord_castSucc, hne']

/-- The right child receives the old-edge occurrences in the right cut piece. -/
theorem faceEdgeMultiplicity_split_right_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (e : P.Edge) :
    (split P cut).faceEdgeMultiplicity (rightFace P cut) e.castSucc =
      (cut.right.map edgeOfDart).count e := by
  unfold faceEdgeMultiplicity
  rw [split_boundary_right]
  calc
    ((rightBoundary P cut).map edgeOfDart).count e.castSucc =
        ((rightOrientedBoundary P cut).map edgeOfDart).count e.castSucc :=
      count_storedWord cut.face.orientation _ _
    _ = (cut.right.map edgeOfDart).count e := by
      have hne : e.castSucc ≠ freshEdge P :=
        P1.firstSubedge_ne_freshEdge e
      have hne' : freshEdge P ≠ e.castSucc :=
        Ne.symm hne
      simp [rightOrientedBoundary, edgeOfDart,
        count_retainWord_castSucc, hne']

/-- Every unselected face retains its old-edge multiplicities. -/
theorem faceEdgeMultiplicity_split_old_of_ne
    (P : FiniteCyclicPresentation) (cut : P2Cut P) {f : P.Face}
    (h : f ≠ cut.face.face) (e : P.Edge) :
    (split P cut).faceEdgeMultiplicity (oldFace P cut f) e.castSucc =
      P.faceEdgeMultiplicity f e := by
  unfold faceEdgeMultiplicity
  rw [split_boundary_old_of_ne P cut h]
  exact count_retainWord_castSucc e (P.boundary f)

/-- The selected child contains the fresh edge exactly once. -/
@[simp]
theorem faceEdgeMultiplicity_split_selected_freshEdge
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).faceEdgeMultiplicity (oldFace P cut cut.face.face)
      (freshEdge P) = 1 := by
  unfold faceEdgeMultiplicity
  rw [split_boundary_selected]
  calc
    ((selectedBoundary P cut).map edgeOfDart).count (freshEdge P) =
        ((selectedOrientedBoundary P cut).map edgeOfDart).count (freshEdge P) :=
      count_storedWord cut.face.orientation _ _
    _ = 1 := by
      have hzero :
          ((retainWord cut.left).map edgeOfDart).count (freshEdge P) = 0 :=
        List.count_eq_zero.mpr (freshEdge_not_mem_retainWord P cut.left)
      simp [selectedOrientedBoundary, edgeOfDart, hzero]

/-- The right child contains the fresh edge exactly once. -/
@[simp]
theorem faceEdgeMultiplicity_split_right_freshEdge
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).faceEdgeMultiplicity (rightFace P cut) (freshEdge P) = 1 := by
  unfold faceEdgeMultiplicity
  rw [split_boundary_right]
  calc
    ((rightBoundary P cut).map edgeOfDart).count (freshEdge P) =
        ((rightOrientedBoundary P cut).map edgeOfDart).count (freshEdge P) :=
      count_storedWord cut.face.orientation _ _
    _ = 1 := by
      have hzero :
          ((retainWord cut.right).map edgeOfDart).count (freshEdge P) = 0 :=
        List.count_eq_zero.mpr (freshEdge_not_mem_retainWord P cut.right)
      simp [rightOrientedBoundary, edgeOfDart, hzero]

/-- An unselected face contains no occurrence of the fresh edge. -/
theorem faceEdgeMultiplicity_split_old_freshEdge_of_ne
    (P : FiniteCyclicPresentation) (cut : P2Cut P) {f : P.Face}
    (h : f ≠ cut.face.face) :
    (split P cut).faceEdgeMultiplicity (oldFace P cut f) (freshEdge P) = 0 := by
  unfold faceEdgeMultiplicity
  rw [split_boundary_old_of_ne P cut h]
  exact List.count_eq_zero.mpr (freshEdge_not_mem_retainWord P (P.boundary f))

/-- The selected source face's multiplicity is the sum of the two cut-piece counts. -/
theorem faceEdgeMultiplicity_cut_eq_add
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (e : P.Edge) :
    P.faceEdgeMultiplicity cut.face.face e =
      (cut.left.map edgeOfDart).count e +
        (cut.right.map edgeOfDart).count e := by
  have hrotation :=
    (cut.boundary_rotated.map edgeOfDart).perm.count_eq e
  calc
    P.faceEdgeMultiplicity cut.face.face e =
        ((P.orientedBoundary cut.face).map edgeOfDart).count e :=
      (P.orientedBoundary_edgeMultiplicity cut.face e).symm
    _ = (((cut.left ++ cut.right).map edgeOfDart).count e) :=
      hrotation
    _ = (cut.left.map edgeOfDart).count e +
        (cut.right.map edgeOfDart).count e := by
      simp

private theorem sum_replace_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (values : ι → ℕ) (selected : ι) (left right : ℕ)
    (hselected : values selected = left + right) :
    (∑ x, if x = selected then left else values x) + right =
      ∑ x, values x := by
  have hsum :
      (∑ x, if x = selected then left else values x) =
        left + ∑ x ∈ Finset.univ.erase selected, values x := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun x ↦ if x = selected then left else values x)
      (Finset.mem_univ selected)]
    simp only [ite_eq_left]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ selected :=
      Finset.ne_of_mem_erase hx
    simp [hne]
  rw [hsum]
  calc
    (left + ∑ x ∈ Finset.univ.erase selected, values x) + right =
        (left + right) + ∑ x ∈ Finset.univ.erase selected, values x := by
      omega
    _ = values selected + ∑ x ∈ Finset.univ.erase selected, values x := by
      rw [hselected]
    _ = ∑ x, values x :=
      Finset.add_sum_erase Finset.univ values (Finset.mem_univ selected)

/-- P2 preserves the total multiplicity of every retained old edge. -/
theorem edgeMultiplicity_split_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (e : P.Edge) :
    P.edgeMultiplicity e =
      (split P cut).edgeMultiplicity e.castSucc := by
  unfold edgeMultiplicity
  have hreindex :
      (∑ q : (split P cut).Face,
          (split P cut).faceEdgeMultiplicity q e.castSucc) =
        ∑ q : Fin (P.faces.length + 1),
          (split P cut).faceEdgeMultiplicity (faceEquiv P cut q) e.castSucc :=
    (Fintype.sum_equiv (faceEquiv P cut)
      (fun q ↦ (split P cut).faceEdgeMultiplicity
        (faceEquiv P cut q) e.castSucc)
      (fun q ↦ (split P cut).faceEdgeMultiplicity q e.castSucc)
      (fun _ ↦ rfl)).symm
  rw [hreindex, Fin.sum_univ_castSucc]
  symm
  change
    (∑ f : P.Face,
      (split P cut).faceEdgeMultiplicity (oldFace P cut f) e.castSucc) +
        (split P cut).faceEdgeMultiplicity (rightFace P cut) e.castSucc =
      ∑ f : P.Face, P.faceEdgeMultiplicity f e
  rw [faceEdgeMultiplicity_split_right_castSucc]
  have hold :
      (∑ f : P.Face,
          (split P cut).faceEdgeMultiplicity (oldFace P cut f) e.castSucc) =
        ∑ f : P.Face,
          if f = cut.face.face then
            (cut.left.map edgeOfDart).count e
          else
            P.faceEdgeMultiplicity f e := by
    apply Finset.sum_congr rfl
    intro f hf
    by_cases hface : f = cut.face.face
    · subst f
      simp [faceEdgeMultiplicity_split_selected_castSucc]
    · simp [hface, faceEdgeMultiplicity_split_old_of_ne P cut hface]
  rw [hold]
  exact sum_replace_add
    (fun f ↦ P.faceEdgeMultiplicity f e) cut.face.face
    ((cut.left.map edgeOfDart).count e)
    ((cut.right.map edgeOfDart).count e)
    (faceEdgeMultiplicity_cut_eq_add P cut e)

/-- The fresh cutting edge occurs exactly once in each child and nowhere else. -/
@[simp]
theorem edgeMultiplicity_split_freshEdge
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).edgeMultiplicity (freshEdge P) = 2 := by
  unfold edgeMultiplicity
  have hreindex :
      (∑ q : (split P cut).Face,
          (split P cut).faceEdgeMultiplicity q (freshEdge P)) =
        ∑ q : Fin (P.faces.length + 1),
          (split P cut).faceEdgeMultiplicity
            (faceEquiv P cut q) (freshEdge P) :=
    (Fintype.sum_equiv (faceEquiv P cut)
      (fun q ↦ (split P cut).faceEdgeMultiplicity
        (faceEquiv P cut q) (freshEdge P))
      (fun q ↦ (split P cut).faceEdgeMultiplicity q (freshEdge P))
      (fun _ ↦ rfl)).symm
  rw [hreindex, Fin.sum_univ_castSucc]
  change
    (∑ f : P.Face,
      (split P cut).faceEdgeMultiplicity (oldFace P cut f) (freshEdge P)) +
        (split P cut).faceEdgeMultiplicity (rightFace P cut) (freshEdge P) = 2
  rw [faceEdgeMultiplicity_split_right_freshEdge]
  have hold :
      (∑ f : P.Face,
          (split P cut).faceEdgeMultiplicity
            (oldFace P cut f) (freshEdge P)) =
        ∑ f : P.Face, if f = cut.face.face then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro f hf
    by_cases hface : f = cut.face.face
    · subst f
      simp
    · simp [hface, faceEdgeMultiplicity_split_old_freshEdge_of_ne P cut hface]
  rw [hold]
  simp

/-- Retaining old edge names preserves and reflects cyclic rotation. -/
@[simp]
theorem retainWord_isRotated_iff {n : ℕ}
    (left right : List (SignedDart (Fin n))) :
    (retainWord left).IsRotated (retainWord right) ↔
      left.IsRotated right := by
  constructor
  · intro h
    simpa only [contractWord_retainWord] using
      P1.contractWord_isRotated h
  · intro h
    simpa only [retainWord] using h.map P1.castSuccDart

/-- P2 preserves ordinary finite-presentation incidence validity. -/
theorem split_isSurfaceValid
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : P.IsSurfaceValid) :
    (split P cut).IsSurfaceValid := by
  refine ⟨⟨rightFace P cut⟩, ?_, ?_, ?_⟩
  · intro q
    rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
    · by_cases hface : f = cut.face.face
      · subst f
        rw [split_boundary_selected]
        exact List.ne_nil_of_mem
          (selectedFreshDart_mem_selectedBoundary P cut)
      · rw [split_boundary_old_of_ne P cut hface]
        intro hnil
        exact h.2.1 f ((retainWord_eq_nil_iff (P.boundary f)).mp hnil)
    · rw [split_boundary_right]
      exact List.ne_nil_of_mem (rightFreshDart_mem_rightBoundary P cut)
  · intro q r hqr
    rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
    · rcases face_cases P cut r with ⟨g, rfl⟩ | rfl
      · by_cases hf : f = cut.face.face
        · subst f
          by_cases hg : g = cut.face.face
          · subst g
            rfl
          · have hselected :
                selectedFreshDart P cut ∈
                  (split P cut).boundary
                    (oldFace P cut cut.face.face) := by
              rw [split_boundary_selected]
              exact selectedFreshDart_mem_selectedBoundary P cut
            have htarget := hqr.mem_iff.mp hselected
            rw [split_boundary_old_of_ne P cut hg] at htarget
            exact (selectedFreshDart_not_mem_retainWord
              P cut (P.boundary g) htarget).elim
        · by_cases hg : g = cut.face.face
          · subst g
            have hselected :
                selectedFreshDart P cut ∈
                  (split P cut).boundary
                    (oldFace P cut cut.face.face) := by
              rw [split_boundary_selected]
              exact selectedFreshDart_mem_selectedBoundary P cut
            have htarget := hqr.symm.mem_iff.mp hselected
            rw [split_boundary_old_of_ne P cut hf] at htarget
            exact (selectedFreshDart_not_mem_retainWord
              P cut (P.boundary f) htarget).elim
          · have hretained :
                (retainWord (P.boundary f)).IsRotated
                  (retainWord (P.boundary g)) := by
              rw [← split_boundary_old_of_ne P cut hf,
                ← split_boundary_old_of_ne P cut hg]
              exact hqr
            have hsource :=
              (retainWord_isRotated_iff (P.boundary f) (P.boundary g)).mp
                hretained
            have hfg := h.2.2.1 f g hsource
            subst g
            rfl
      · by_cases hf : f = cut.face.face
        · subst f
          have hselected :
              selectedFreshDart P cut ∈
                (split P cut).boundary
                  (oldFace P cut cut.face.face) := by
            rw [split_boundary_selected]
            exact selectedFreshDart_mem_selectedBoundary P cut
          have htarget := hqr.mem_iff.mp hselected
          rw [split_boundary_right] at htarget
          exact (selectedFreshDart_not_mem_rightBoundary P cut htarget).elim
        · have hright :
              rightFreshDart P cut ∈
                (split P cut).boundary (rightFace P cut) := by
            rw [split_boundary_right]
            exact rightFreshDart_mem_rightBoundary P cut
          have htarget := hqr.symm.mem_iff.mp hright
          rw [split_boundary_old_of_ne P cut hf] at htarget
          exact (rightFreshDart_not_mem_retainWord
            P cut (P.boundary f) htarget).elim
    · rcases face_cases P cut r with ⟨g, rfl⟩ | rfl
      · by_cases hg : g = cut.face.face
        · subst g
          have hselected :
              selectedFreshDart P cut ∈
                (split P cut).boundary
                  (oldFace P cut cut.face.face) := by
            rw [split_boundary_selected]
            exact selectedFreshDart_mem_selectedBoundary P cut
          have htarget := hqr.symm.mem_iff.mp hselected
          rw [split_boundary_right] at htarget
          exact (selectedFreshDart_not_mem_rightBoundary P cut htarget).elim
        · have hright :
              rightFreshDart P cut ∈
                (split P cut).boundary (rightFace P cut) := by
            rw [split_boundary_right]
            exact rightFreshDart_mem_rightBoundary P cut
          have htarget := hqr.mem_iff.mp hright
          rw [split_boundary_old_of_ne P cut hg] at htarget
          exact (rightFreshDart_not_mem_retainWord
            P cut (P.boundary g) htarget).elim
      · rfl
  · intro e
    change Fin (P.edgeCount + 1) at e
    refine Fin.lastCases ?_ (fun old ↦ ?_) e
    · exact Or.inr (by
        simpa only [freshEdge, P1.freshEdge] using
          edgeMultiplicity_split_freshEdge P cut)
    · have hmultiplicity := h.2.2.2 old
      rw [edgeMultiplicity_split_castSucc P cut old] at hmultiplicity
      exact hmultiplicity

/-- Edge membership is independent of the chosen traversal orientation of a face. -/
theorem edge_mem_orientedBoundary_iff
    (P : FiniteCyclicPresentation) (face : P.OrientedFace) (e : P.Edge) :
    e ∈ (P.orientedBoundary face).map edgeOfDart ↔
      e ∈ (P.boundary face.face).map edgeOfDart := by
  cases face with
  | mk face orientation =>
      cases orientation
      · rfl
      · rw [orientedBoundary, ite_eq_left rfl, map_edgeOfDart_inverseWord]
        exact List.mem_reverse

/-- An edge of the selected face occurs in one of the two cut pieces. -/
theorem edge_mem_cut_pieces_iff
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (e : P.Edge) :
    e ∈ cut.left.map edgeOfDart ∨ e ∈ cut.right.map edgeOfDart ↔
      e ∈ (P.boundary cut.face.face).map edgeOfDart := by
  calc
    e ∈ cut.left.map edgeOfDart ∨ e ∈ cut.right.map edgeOfDart ↔
        e ∈ (cut.left ++ cut.right).map edgeOfDart := by
      simp
    _ ↔ e ∈ (P.orientedBoundary cut.face).map edgeOfDart :=
      (cut.boundary_rotated.map edgeOfDart).mem_iff.symm
    _ ↔ e ∈ (P.boundary cut.face.face).map edgeOfDart :=
      edge_mem_orientedBoundary_iff P cut.face e

/-- Membership of an old edge is retained after enlarging the edge type. -/
theorem castSucc_edge_mem_retainWord
    {n : ℕ} {e : Fin n} {word : List (SignedDart (Fin n))}
    (h : e ∈ word.map edgeOfDart) :
    e.castSucc ∈ (retainWord word).map edgeOfDart := by
  rcases List.mem_map.mp h with ⟨d, hd, rfl⟩
  exact List.mem_map.mpr
    ⟨P1.castSuccDart d, List.mem_map.mpr ⟨d, hd, rfl⟩,
      P1.edgeOfDart_castSuccDart d⟩

/-- Storing a word in the opposite traversal preserves unoriented edge membership. -/
theorem edge_mem_storedWord_iff
    {α : Type*} (orientation : Bool)
    (word : List (SignedDart α)) (e : α) :
    e ∈ (storedWord orientation word).map edgeOfDart ↔
      e ∈ word.map edgeOfDart := by
  cases orientation
  · rfl
  · rw [storedWord_true, map_edgeOfDart_inverseWord]
    exact List.mem_reverse

theorem castSucc_edge_mem_selectedBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) {e : P.Edge}
    (h : e ∈ cut.left.map edgeOfDart) :
    e.castSucc ∈ (selectedBoundary P cut).map edgeOfDart := by
  apply (edge_mem_storedWord_iff cut.face.orientation _ _).mpr
  simp only [selectedOrientedBoundary, List.map_append, List.map_singleton,
    List.mem_append, List.mem_singleton]
  exact Or.inl (castSucc_edge_mem_retainWord h)

theorem castSucc_edge_mem_rightBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) {e : P.Edge}
    (h : e ∈ cut.right.map edgeOfDart) :
    e.castSucc ∈ (rightBoundary P cut).map edgeOfDart := by
  apply (edge_mem_storedWord_iff cut.face.orientation _ _).mpr
  simp only [rightOrientedBoundary, List.map_cons, List.mem_cons]
  exact Or.inr (castSucc_edge_mem_retainWord h)

/-- The two child faces are adjacent through the fresh cutting edge. -/
theorem split_children_faceAdjacent
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut).FaceAdjacent
      (oldFace P cut cut.face.face) (rightFace P cut) := by
  refine ⟨freshEdge P, ?_, ?_⟩
  · rw [split_boundary_selected]
    exact List.mem_map.mpr
      ⟨selectedFreshDart P cut,
        selectedFreshDart_mem_selectedBoundary P cut,
        edgeOfDart_selectedFreshDart P cut⟩
  · rw [split_boundary_right]
    exact List.mem_map.mpr
      ⟨rightFreshDart P cut,
        rightFreshDart_mem_rightBoundary P cut,
        edgeOfDart_rightFreshDart P cut⟩

private theorem faceAdjacent_symm
    {P : FiniteCyclicPresentation} {f g : P.Face}
    (h : P.FaceAdjacent f g) :
    P.FaceAdjacent g f := by
  rcases h with ⟨e, hf, hg⟩
  exact ⟨e, hg, hf⟩

private theorem faceChain_symm
    {P : FiniteCyclicPresentation} {f g : P.Face}
    (h : Relation.ReflTransGen P.FaceAdjacent f g) :
    Relation.ReflTransGen P.FaceAdjacent g f := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl f => exact Relation.ReflTransGen.refl
  | single h => exact Relation.ReflTransGen.single (faceAdjacent_symm h)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₂.trans ih₁

/-- A source-face edge occurs in a child reachable from the retained face position. -/
theorem exists_child_edge
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (f : P.Face) (e : P.Edge)
    (h : e ∈ (P.boundary f).map edgeOfDart) :
    ∃ q : (split P cut).Face,
      Relation.ReflTransGen (split P cut).FaceAdjacent
        (oldFace P cut f) q ∧
      e.castSucc ∈ ((split P cut).boundary q).map edgeOfDart := by
  by_cases hface : f = cut.face.face
  · subst f
    rcases (edge_mem_cut_pieces_iff P cut e).mpr h with hleft | hright
    · refine ⟨oldFace P cut cut.face.face,
        Relation.ReflTransGen.refl, ?_⟩
      rw [split_boundary_selected]
      exact castSucc_edge_mem_selectedBoundary P cut hleft
    · refine ⟨rightFace P cut,
        Relation.ReflTransGen.single (split_children_faceAdjacent P cut), ?_⟩
      rw [split_boundary_right]
      exact castSucc_edge_mem_rightBoundary P cut hright
  · refine ⟨oldFace P cut f, Relation.ReflTransGen.refl, ?_⟩
    rw [split_boundary_old_of_ne P cut hface]
    exact castSucc_edge_mem_retainWord h

/-- A source adjacency lifts to a target path between the retained face positions. -/
theorem map_faceAdjacent_chain
    (P : FiniteCyclicPresentation) (cut : P2Cut P) {f g : P.Face}
    (h : P.FaceAdjacent f g) :
    Relation.ReflTransGen (split P cut).FaceAdjacent
      (oldFace P cut f) (oldFace P cut g) := by
  rcases h with ⟨e, hf, hg⟩
  rcases exists_child_edge P cut f e hf with ⟨q, hfq, hq⟩
  rcases exists_child_edge P cut g e hg with ⟨r, hgr, hr⟩
  exact hfq.trans
    ((Relation.ReflTransGen.single ⟨e.castSucc, hq, hr⟩).trans
      (faceChain_symm hgr))

/-- A source face-adjacency path lifts to a target path. -/
theorem map_faceChain
    (P : FiniteCyclicPresentation) (cut : P2Cut P) {f g : P.Face}
    (h : Relation.ReflTransGen P.FaceAdjacent f g) :
    Relation.ReflTransGen (split P cut).FaceAdjacent
      (oldFace P cut f) (oldFace P cut g) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl f => exact Relation.ReflTransGen.refl
  | single h => exact map_faceAdjacent_chain P cut h
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem target_to_oldFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : (split P cut).Face) :
    ∃ f : P.Face,
      Relation.ReflTransGen (split P cut).FaceAdjacent
        q (oldFace P cut f) := by
  rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
  · exact ⟨f, Relation.ReflTransGen.refl⟩
  · exact ⟨cut.face.face,
      Relation.ReflTransGen.single
        (faceAdjacent_symm (split_children_faceAdjacent P cut))⟩

private theorem oldFace_to_target
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : (split P cut).Face) :
    ∃ f : P.Face,
      Relation.ReflTransGen (split P cut).FaceAdjacent
        (oldFace P cut f) q := by
  rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
  · exact ⟨f, Relation.ReflTransGen.refl⟩
  · exact ⟨cut.face.face,
      Relation.ReflTransGen.single (split_children_faceAdjacent P cut)⟩

/-- P2 preserves connectivity of the face-edge incidence graph. -/
theorem split_isConnected
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : P.IsConnected) :
    (split P cut).IsConnected := by
  refine ⟨⟨rightFace P cut⟩, ?_⟩
  intro q r
  rcases target_to_oldFace P cut q with ⟨f, hq⟩
  rcases oldFace_to_target P cut r with ⟨g, hr⟩
  exact hq.trans ((map_faceChain P cut (h.2 f g)).trans hr)

/-- Collapse both child faces of a P2 split back to their source face. -/
def collapseFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : (split P cut).Face) : P.Face :=
  if h : q.val < P.faces.length then
    ⟨q.val, h⟩
  else
    cut.face.face

@[simp]
theorem collapseFace_oldFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P) (f : P.Face) :
    collapseFace P cut (oldFace P cut f) = f := by
  apply Fin.ext
  simp [collapseFace, oldFace]

@[simp]
theorem collapseFace_rightFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    collapseFace P cut (rightFace P cut) = cut.face.face := by
  apply Fin.ext
  simp [collapseFace, rightFace]

/-- A retained old edge in a child face comes from the corresponding collapsed source face. -/
private theorem oldEdge_mem_collapseFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : (split P cut).Face) (e : P.Edge)
    (h : e.castSucc ∈ ((split P cut).boundary q).map edgeOfDart) :
    e ∈ (P.boundary (collapseFace P cut q)).map edgeOfDart := by
  rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
  · rw [collapseFace_oldFace]
    by_cases hface : f = cut.face.face
    · subst f
      apply List.count_pos_iff.mp
      have hpositive :
          0 < (split P cut).faceEdgeMultiplicity
            (oldFace P cut cut.face.face) e.castSucc :=
        List.count_pos_iff.mpr h
      rw [faceEdgeMultiplicity_split_selected_castSucc] at hpositive
      change 0 < P.faceEdgeMultiplicity cut.face.face e
      rw [faceEdgeMultiplicity_cut_eq_add]
      omega
    · apply List.count_pos_iff.mp
      have hpositive :
          0 < (split P cut).faceEdgeMultiplicity
            (oldFace P cut f) e.castSucc :=
        List.count_pos_iff.mpr h
      rw [faceEdgeMultiplicity_split_old_of_ne P cut hface] at hpositive
      exact hpositive
  · rw [collapseFace_rightFace]
    apply List.count_pos_iff.mp
    have hpositive :
        0 < (split P cut).faceEdgeMultiplicity
          (rightFace P cut) e.castSucc :=
      List.count_pos_iff.mpr h
    rw [faceEdgeMultiplicity_split_right_castSucc] at hpositive
    change 0 < P.faceEdgeMultiplicity cut.face.face e
    rw [faceEdgeMultiplicity_cut_eq_add]
    omega

/-- Any child containing the fresh cutting edge collapses to the selected source face. -/
private theorem collapseFace_eq_of_freshEdge_mem
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (q : (split P cut).Face)
    (h : freshEdge P ∈ ((split P cut).boundary q).map edgeOfDart) :
    collapseFace P cut q = cut.face.face := by
  rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
  · rw [collapseFace_oldFace]
    by_contra hface
    have hpositive :
        0 < (split P cut).faceEdgeMultiplicity
          (oldFace P cut f) (freshEdge P) :=
      List.count_pos_iff.mpr h
    rw [faceEdgeMultiplicity_split_old_freshEdge_of_ne P cut hface] at hpositive
    omega
  · exact collapseFace_rightFace P cut

/-- Collapsing the child faces sends target adjacency to a source adjacency path. -/
theorem collapse_faceAdjacent_chain
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {q r : (split P cut).Face}
    (h : (split P cut).FaceAdjacent q r) :
    Relation.ReflTransGen P.FaceAdjacent
      (collapseFace P cut q) (collapseFace P cut r) := by
  rcases h with ⟨b, hqb, hrb⟩
  change Fin (P.edgeCount + 1) at b
  revert hqb hrb
  refine Fin.lastCases ?_ (fun e hqb hrb ↦ ?_) b
  · intro hqb hrb
    rw [collapseFace_eq_of_freshEdge_mem P cut q hqb,
      collapseFace_eq_of_freshEdge_mem P cut r hrb]
  · exact Relation.ReflTransGen.single
      ⟨e, oldEdge_mem_collapseFace P cut q e hqb,
        oldEdge_mem_collapseFace P cut r e hrb⟩

/-- Collapsing the child faces sends target adjacency paths to source adjacency paths. -/
theorem collapse_faceChain
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {q r : (split P cut).Face}
    (h : Relation.ReflTransGen (split P cut).FaceAdjacent q r) :
    Relation.ReflTransGen P.FaceAdjacent
      (collapseFace P cut q) (collapseFace P cut r) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | single hadj => exact collapse_faceAdjacent_chain P cut hadj
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A P2 split is connected only if its source presentation is connected. -/
theorem isConnected_of_split
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : (split P cut).IsConnected) :
    P.IsConnected := by
  refine ⟨?_, ?_⟩
  · exact (Nonempty.map (collapseFace P cut) h.1)
  · intro f g
    have hchain := h.2 (oldFace P cut f) (oldFace P cut g)
    have hmapped := collapse_faceChain P cut hchain
    simpa only [collapseFace_oldFace] using hmapped

/-- Every P2 split of an exceptional empty-word presentation is ordinarily valid. -/
theorem split_isSurfaceValid_of_isEmptyWordSphere
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : P.IsEmptyWordSphere) :
    (split P cut).IsSurfaceValid := by
  have hallFaces (f : P.Face) : f = cut.face.face := by
    apply Fin.ext
    have hlength := h.faces_length_eq_one
    have hf := f.isLt
    have hcut := cut.face.face.isLt
    omega
  refine ⟨⟨rightFace P cut⟩, ?_, ?_, ?_⟩
  · intro q
    rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
    · rw [hallFaces f, split_boundary_selected]
      exact List.ne_nil_of_mem
        (selectedFreshDart_mem_selectedBoundary P cut)
    · rw [split_boundary_right]
      exact List.ne_nil_of_mem (rightFreshDart_mem_rightBoundary P cut)
  · intro q r hqr
    rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
    · rcases face_cases P cut r with ⟨g, rfl⟩ | rfl
      · rw [hallFaces f, hallFaces g]
      · rw [hallFaces f] at hqr
        have hselected :
            selectedFreshDart P cut ∈
              (split P cut).boundary
                (oldFace P cut cut.face.face) := by
          rw [split_boundary_selected]
          exact selectedFreshDart_mem_selectedBoundary P cut
        have htarget := hqr.mem_iff.mp hselected
        rw [split_boundary_right] at htarget
        exact (selectedFreshDart_not_mem_rightBoundary P cut htarget).elim
    · rcases face_cases P cut r with ⟨g, rfl⟩ | rfl
      · rw [hallFaces g] at hqr
        have hselected :
            selectedFreshDart P cut ∈
              (split P cut).boundary
                (oldFace P cut cut.face.face) := by
          rw [split_boundary_selected]
          exact selectedFreshDart_mem_selectedBoundary P cut
        have htarget := hqr.symm.mem_iff.mp hselected
        rw [split_boundary_right] at htarget
        exact (selectedFreshDart_not_mem_rightBoundary P cut htarget).elim
      · rfl
  · intro e
    change Fin (P.edgeCount + 1) at e
    have hedgeCount := h.edgeCount_eq_zero
    have he : e = freshEdge P := by
      apply Fin.ext
      have heLt := e.isLt
      simp only [freshEdge, P1.freshEdge, Fin.last]
      omega
    subst e
    exact Or.inr (edgeMultiplicity_split_freshEdge P cut)

/-- P2 preserves Gallier validity, including the exceptional empty-word branch. -/
theorem split_isGallierValid
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (h : P.IsGallierValid) :
    (split P cut).IsGallierValid := by
  rcases h with hregular | hempty
  · exact Or.inl
      ⟨split_isSurfaceValid P cut hregular.1,
        split_isConnected P cut hregular.2⟩
  · exact Or.inl
      ⟨split_isSurfaceValid_of_isEmptyWordSphere P cut hempty,
        split_isConnected P cut hempty.isConnected⟩

/-- The zero-position P2 cut of Gallier--Xu's exceptional sphere presentation. -/
def emptyWordSphereCut : P2Cut emptyWordSphere :=
  P2Cut.canonical (.pos 0) 0

/-- The last-position spelling of the same empty boundary cut. -/
def emptyWordSphereLastCut : P2Cut emptyWordSphere :=
  P2Cut.canonical (.pos 0) (Fin.last 0)

@[simp]
theorem emptyWordSphereLastCut_eq :
    emptyWordSphereLastCut = emptyWordSphereCut :=
  rfl

/-- P2 turns the exceptional empty-word sphere presentation into the two-monogon presentation. -/
@[simp]
theorem split_emptyWordSphere :
    split emptyWordSphere emptyWordSphereCut = twoMonogonSphere :=
  rfl

/-- The endpoint-at-the-right spelling gives the same exact regression. -/
@[simp]
theorem split_emptyWordSphere_last :
    split emptyWordSphere emptyWordSphereLastCut = twoMonogonSphere :=
  rfl

end P2

/-- A Gallier--Xu P2 face subdivision, up to signed presentation isomorphism of the target.

An ordinary P2 move cuts between two distinct places of a nonempty cyclic boundary, so both old
boundary pieces are nonempty. The sole degenerate case admitted here is Gallier--Xu's exceptional
empty-word sphere, whose conversion to the ordinary-valid two-monogon presentation is also
represented by the raw `P2.split` construction. This is a syntactic move relation and
deliberately does not bundle source validity. -/
def P2Subdivision (P Q : FiniteCyclicPresentation) : Prop :=
  ∃ cut : P2Cut P,
    (cut.IsNondegenerate ∨ P.IsEmptyWordSphere) ∧
      Nonempty (SignedPresentationIso (P2.split P cut) Q)

namespace P2Subdivision

/-- A canonical nondegenerate split is a P2 subdivision. -/
theorem canonical (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hcut : cut.IsNondegenerate) :
    P2Subdivision P (P2.split P cut) :=
  ⟨cut, Or.inl hcut, ⟨SignedPresentationIso.refl _⟩⟩

/-- The raw split of an exceptional empty-word sphere is an allowed exceptional P2 step. -/
theorem canonicalEmptyWordSphere (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hP : P.IsEmptyWordSphere) :
    P2Subdivision P (P2.split P cut) :=
  ⟨cut, Or.inr hP, ⟨SignedPresentationIso.refl _⟩⟩

/-- P2 subdivisions preserve ordinary incidence validity. -/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : P2Subdivision P Q) (h : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  rcases hPQ with ⟨cut, _hcut, ⟨e⟩⟩
  exact e.isSurfaceValid (P2.split_isSurfaceValid P cut h)

/-- P2 subdivisions preserve face-incidence connectivity. -/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : P2Subdivision P Q) (h : P.IsConnected) :
    Q.IsConnected := by
  rcases hPQ with ⟨cut, _hcut, ⟨e⟩⟩
  exact e.isConnected (P2.split_isConnected P cut h)

/-- P2 subdivisions preserve Gallier validity. -/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : P2Subdivision P Q) (h : P.IsGallierValid) :
    Q.IsGallierValid := by
  rcases hPQ with ⟨cut, _hcut, ⟨e⟩⟩
  exact e.isGallierValid (P2.split_isGallierValid P cut h)

/-- The exceptional sphere presentation subdivides to the two-monogon sphere presentation. -/
theorem emptyWordSphere_twoMonogonSphere :
    P2Subdivision emptyWordSphere twoMonogonSphere := by
  simpa only [P2.split_emptyWordSphere] using
    canonicalEmptyWordSphere emptyWordSphere P2.emptyWordSphereCut
      emptyWordSphere_isEmptyWordSphere

end P2Subdivision

end FiniteCyclicPresentation
end ClassificationOfSurfaces
end Topology
end LeanEval
