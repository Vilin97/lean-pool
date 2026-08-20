/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.CanonicalWords
import LeanPool.ClassificationOfSurfaces.FiniteCyclicPresentation

/-!
# Canonical finite cyclic presentations

This file fixes the finite-cyclic endpoint of the Gallier--Xu normalization lane. A typed
one-face boundary word is enumerated by `Fin` exactly once, and the named normal forms use that
adapter. The sphere branch uses the ordinary-valid two-monogon presentation obtained from the
exceptional empty-word sphere by P2.

The orientable and nonorientable words remain the existing `NormalForm.orientableBoundaryWord`
and `NormalForm.nonOrientableBoundaryWord`; this file does not introduce another formulation of
the Lean-Eval representatives.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

open SurfaceCellComplex

namespace FiniteCyclicPresentation

/-- The two existing projections from a signed dart to its unoriented edge agree. -/
theorem map_edgeOfDart_eq_map_edgeName {Edge : Type}
    (word : List (SignedDart Edge)) :
    word.map edgeOfDart = word.map SignedDart.edgeName := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      cases d <;> simp [edgeOfDart, SignedDart.edgeName, ih]

/-- Enumerate the edge names of a typed one-face signed boundary word. -/
@[reducible]
noncomputable def ofOneFaceWord {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) : FiniteCyclicPresentation where
  edgeCount := Fintype.card Edge
  faces := [word.map (SignedDart.mapEquiv (Fintype.equivFin Edge))]

theorem ofOneFaceWord_faces_length {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).faces.length = 1 := by
  simp [ofOneFaceWord]

theorem ofOneFaceWord_boundary_zero {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).boundary 0 =
      word.map (SignedDart.mapEquiv (Fintype.equivFin Edge)) := by
  rfl

theorem ofOneFaceWord_face_eq_zero {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) (f : (ofOneFaceWord word).Face) :
    f = 0 := by
  apply Fin.ext
  have hf := f.isLt
  change f.val <
    [word.map (SignedDart.mapEquiv (Fintype.equivFin Edge))].length at hf
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at hf
  change f.val = 0
  omega

theorem ofOneFaceWord_boundary {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) (f : (ofOneFaceWord word).Face) :
    (ofOneFaceWord word).boundary f =
      word.map (SignedDart.mapEquiv (Fintype.equivFin Edge)) := by
  rw [ofOneFaceWord_face_eq_zero word f]
  exact ofOneFaceWord_boundary_zero word

/-- The original edge names are equivalent to the enumerated one-face presentation edges. -/
noncomputable def ofOneFaceWordEdgeEquiv {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) :
    Edge ≃ (ofOneFaceWord word).Edge := by
  change Edge ≃ Fin (Fintype.card Edge)
  exact Fintype.equivFin Edge

theorem ofOneFaceWord_edgeMultiplicity {Edge : Type} [Fintype Edge]
    [DecidableEq Edge] (word : List (SignedDart Edge)) (e : Edge) :
    (ofOneFaceWord word).edgeMultiplicity
        (ofOneFaceWordEdgeEquiv word e) =
      (word.map edgeOfDart).count e := by
  classical
  simp only [edgeMultiplicity, ofOneFaceWord, faceEdgeMultiplicity,
    ofOneFaceWordEdgeEquiv, id_eq, boundary, List.get_eq_getElem, List.length_cons,
    List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.getElem_cons_zero,
    List.map_map, Function.comp_def, edgeOfDart_mapEquiv, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, zero_add, smul_eq_mul, one_mul]
  have hmap :
      word.map (fun x => Fintype.equivFin Edge (edgeOfDart x)) =
        (word.map edgeOfDart).map (Fintype.equivFin Edge) := by
    simp only [List.map_map, Function.comp_def]
  rw [hmap]
  exact List.count_map_of_injective (word.map edgeOfDart)
    (Fintype.equivFin Edge) (Fintype.equivFin Edge).injective e

/-- A nonempty typed one-face word with surface edge multiplicities gives an ordinary-valid finite
cyclic presentation. -/
theorem ofOneFaceWord_isSurfaceValid {Edge : Type} [Fintype Edge]
    [DecidableEq Edge] (word : List (SignedDart Edge))
    (hne : word ≠ [])
    (hmultiplicity :
      ∀ e : Edge,
        (word.map edgeOfDart).count e = 1 ∨
          (word.map edgeOfDart).count e = 2) :
    (ofOneFaceWord word).IsSurfaceValid := by
  classical
  refine ⟨⟨0, by simp [ofOneFaceWord]⟩, ?_, ?_, ?_⟩
  · intro f
    rw [ofOneFaceWord_boundary]
    intro hmapped
    apply hne
    have hlength := congrArg List.length hmapped
    simpa using hlength
  · intro f g _h
    rw [ofOneFaceWord_face_eq_zero word f,
      ofOneFaceWord_face_eq_zero word g]
  · intro a
    let e := (ofOneFaceWordEdgeEquiv word).symm a
    have ha : a = ofOneFaceWordEdgeEquiv word e := by
      exact ((ofOneFaceWordEdgeEquiv word).apply_symm_apply a).symm
    rw [ha, ofOneFaceWord_edgeMultiplicity]
    exact hmultiplicity e

/-- Every enumerated one-face presentation is connected at the face-incidence level. -/
theorem ofOneFaceWord_isConnected {Edge : Type} [Fintype Edge]
    (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).IsConnected := by
  refine ⟨⟨0, by simp [ofOneFaceWord]⟩, ?_⟩
  intro f g
  rw [ofOneFaceWord_face_eq_zero word f,
    ofOneFaceWord_face_eq_zero word g]

end FiniteCyclicPresentation

namespace NormalForm

/-- The single finite-cyclic target selected for each named normal form.

The admissibility predicate excludes the empty orientable word and the zero-crosscap
nonorientable word when ordinary surface validity is required. -/
noncomputable def canonicalPresentation : NormalForm → FiniteCyclicPresentation
  | .sphere => FiniteCyclicPresentation.twoMonogonSphere
  | .orientable p n =>
      FiniteCyclicPresentation.ofOneFaceWord (orientableBoundaryWord p n)
  | .nonOrientable p n =>
      FiniteCyclicPresentation.ofOneFaceWord (nonOrientableBoundaryWord p n)

@[simp]
theorem canonicalPresentation_sphere :
    canonicalPresentation .sphere =
      FiniteCyclicPresentation.twoMonogonSphere :=
  rfl

@[simp]
theorem canonicalPresentation_orientable (p n : ℕ) :
    canonicalPresentation (.orientable p n) =
      FiniteCyclicPresentation.ofOneFaceWord (orientableBoundaryWord p n) :=
  rfl

@[simp]
theorem canonicalPresentation_nonOrientable (p n : ℕ) :
    canonicalPresentation (.nonOrientable p n) =
      FiniteCyclicPresentation.ofOneFaceWord (nonOrientableBoundaryWord p n) :=
  rfl

/-- Every Eval-admissible canonical presentation has ordinary surface incidence validity. -/
theorem canonicalPresentation_isSurfaceValid
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    N.canonicalPresentation.IsSurfaceValid := by
  cases N with
  | sphere =>
      exact FiniteCyclicPresentation.twoMonogonSphere_isSurfaceValid
  | orientable p n =>
      apply FiniteCyclicPresentation.ofOneFaceWord_isSurfaceValid
      · exact orientableBoundaryWord_ne_nil hN
      · intro e
        have hocc := orientableBoundaryWord_edge_occurrences p n e
        rw [SurfaceCellComplex.wordEdgeOccurrences_card_eq_count_edgeName] at hocc
        rw [FiniteCyclicPresentation.map_edgeOfDart_eq_map_edgeName]
        cases e <;> simp_all
  | nonOrientable p n =>
      apply FiniteCyclicPresentation.ofOneFaceWord_isSurfaceValid
      · exact nonOrientableBoundaryWord_ne_nil hN
      · intro e
        have hocc := nonOrientableBoundaryWord_edge_occurrences p n e
        rw [SurfaceCellComplex.wordEdgeOccurrences_card_eq_count_edgeName] at hocc
        rw [FiniteCyclicPresentation.map_edgeOfDart_eq_map_edgeName]
        cases e <;> simp_all

/-- Canonical finite-cyclic presentations are face-incidence connected. -/
theorem canonicalPresentation_isConnected (N : NormalForm) :
    N.canonicalPresentation.IsConnected := by
  cases N with
  | sphere =>
      exact FiniteCyclicPresentation.twoMonogonSphere_isConnected
  | orientable p n =>
      exact FiniteCyclicPresentation.ofOneFaceWord_isConnected
        (orientableBoundaryWord p n)
  | nonOrientable p n =>
      exact FiniteCyclicPresentation.ofOneFaceWord_isConnected
        (nonOrientableBoundaryWord p n)

/-- Eval-admissible canonical presentations satisfy the packed Gallier--Xu input predicate. -/
theorem canonicalPresentation_isGallierValid
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    N.canonicalPresentation.IsGallierValid :=
  FiniteCyclicPresentation.isGallierValid_of_isSurfaceValid_of_isConnected
    (N.canonicalPresentation_isSurfaceValid hN)
    N.canonicalPresentation_isConnected

end NormalForm

end LeanEval.Topology.ClassificationOfSurfaces
