/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicNormalization

/-!
# Derived Gallier--Xu word rewrites

This file builds the repeated word transformations used after the primitive P1/P2 phase of the
normalization proof.  It starts with proof-producing infrastructure for one-face cyclic words:

* cyclic rotation is a signed presentation isomorphism;
* validity transports across any permutation of the underlying unoriented edge occurrences;
* the Dyck rewrite is available with either orientation of its distinguished edge.

These lemmas keep intermediate validity witnesses out of the public derived-chain APIs.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Dyck

@[simp]
theorem inverseWord_singleton {α : Type*} (d : SignedDart α) :
    inverseWord [d] = [d.flip] :=
  rfl

/-- The unique face of an explicitly indexed one-face presentation. -/
theorem oneFace_face_eq_zero {n : ℕ}
    (word : List (SignedDart (Fin n))) (f : (oneFace word).Face) :
    f = 0 := by
  change (show Fin 1 from f) = (0 : Fin 1)
  exact Fin.eq_zero _

@[simp]
theorem oneFace_boundary {n : ℕ}
    (word : List (SignedDart (Fin n))) (f : (oneFace word).Face) :
    (oneFace word).boundary f = word := by
  rw [oneFace_face_eq_zero word f]
  rfl

/-- The edge multiplicity of a one-face presentation is the count in its displayed word. -/
@[simp]
theorem oneFace_edgeMultiplicity {n : ℕ}
    (word : List (SignedDart (Fin n))) (e : Fin n) :
    (oneFace word).edgeMultiplicity e =
      (word.map edgeOfDart).count e := by
  classical
  simp [edgeMultiplicity, faceEdgeMultiplicity, oneFace]

/-- A permutation of the unoriented edge occurrences preserves one-face surface validity.
Orientation signs and cyclic positions are intentionally irrelevant here. -/
theorem oneFace_isSurfaceValid_of_edgePerm {n : ℕ}
    {sourceWord targetWord : List (SignedDart (Fin n))}
    (hperm :
      (sourceWord.map edgeOfDart).Perm
        (targetWord.map edgeOfDart))
    (validSource : (oneFace sourceWord).IsSurfaceValid) :
    (oneFace targetWord).IsSurfaceValid := by
  classical
  have hsourceNonempty : sourceWord ≠ [] := by
    simpa using validSource.2.1 (0 : (oneFace sourceWord).Face)
  have htargetNonempty : targetWord ≠ [] := by
    intro htarget
    have hlength := hperm.length_eq
    simp only [List.length_map, htarget, List.length_nil] at hlength
    exact hsourceNonempty (List.length_eq_zero_iff.mp hlength)
  refine ⟨⟨0⟩, ?_, ?_, ?_⟩
  · intro f
    simpa using htargetNonempty
  · intro f g _h
    rw [oneFace_face_eq_zero targetWord f,
      oneFace_face_eq_zero targetWord g]
  · intro e
    rw [oneFace_edgeMultiplicity]
    rw [← hperm.count_eq e]
    simpa only [oneFace_edgeMultiplicity] using validSource.2.2.2 e

/-- A cyclic rotation of one displayed face word is a signed presentation isomorphism. -/
def oneFaceSignedIsoOfIsRotated {n : ℕ}
    {sourceWord targetWord : List (SignedDart (Fin n))}
    (hrotated : sourceWord.IsRotated targetWord) :
    SignedPresentationIso (oneFace sourceWord) (oneFace targetWord) where
  edgeRelabeling := EdgeRelabeling.refl _
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [EdgeRelabeling.map_mapDart_refl,
      oneFace_boundary, oneFace_boundary]
    exact hrotated

/-- A cyclic rotation of ordinary-valid one-face words is a normalization equivalence. -/
theorem normalizationEquivalentOfIsRotated {n : ℕ}
    {sourceWord targetWord : List (SignedDart (Fin n))}
    (hrotated : sourceWord.IsRotated targetWord)
    (validSource : (oneFace sourceWord).IsSurfaceValid)
    (validTarget : (oneFace targetWord).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨oneFace sourceWord, validSource⟩
      ⟨oneFace targetWord, validTarget⟩ :=
  NormalizationEquivalent.ofSignedIso
    (oneFaceSignedIsoOfIsRotated hrotated)

/-- The Dyck rewrite preserves the unoriented edge-occurrence multiset, hence ordinary validity. -/
theorem target_isSurfaceValid {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (validSource : (source a U V X).IsSurfaceValid) :
    (target a U V X).IsSurfaceValid := by
  apply oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_singleton, edgeOfDart,
    List.count_append, List.count_cons, List.count_nil]
  omega

/-- Reverse exactly one named edge orientation. -/
def reverseEdgeRelabeling {n : ℕ} (a : Fin n) :
    EdgeRelabeling (Fin n) (Fin n) where
  edgeEquiv := Equiv.refl _
  reverse := fun e ↦ decide (e = a)

@[simp]
theorem reverseEdgeRelabeling_pos {n : ℕ} (a : Fin n) :
    (reverseEdgeRelabeling a).mapDart (.pos a) = .neg a := by
  simp [reverseEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem reverseEdgeRelabeling_neg {n : ℕ} (a : Fin n) :
    (reverseEdgeRelabeling a).mapDart (.neg a) = .pos a := by
  simp [reverseEdgeRelabeling, EdgeRelabeling.mapDart]

theorem reverseEdgeRelabeling_of_ne {n : ℕ} (a e : Fin n)
    (h : e ≠ a) (orientation : Bool) :
    (reverseEdgeRelabeling a).mapDart
        (if orientation then .neg e else .pos e) =
      if orientation then .neg e else .pos e := by
  cases orientation <;>
    simp [reverseEdgeRelabeling, EdgeRelabeling.mapDart, h]

theorem reverseEdgeRelabeling_word {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n)))
    (ha : a ∉ word.map edgeOfDart) :
    word.map (reverseEdgeRelabeling a).mapDart = word := by
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
      rw [List.map_cons, ih htail]
      congr 1
      cases d with
      | pos e =>
          exact reverseEdgeRelabeling_of_ne a e hda false
      | neg e =>
          exact reverseEdgeRelabeling_of_ne a e hda true

/-- The negatively oriented spelling of the Dyck source. -/
@[reducible]
def negativeSource {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  oneFace (([.neg a] ++ U) ++ (V ++ [.pos a] ++ X))

/-- The corresponding negatively oriented target spelling. -/
@[reducible]
def negativeTarget {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  oneFace ((U ++ [.pos a]) ++ (X ++ [.neg a] ++ V))

/-- Reversing `a` identifies the negative source spelling with the positive source spelling. -/
def negativeSourceSignedIso {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart) :
    SignedPresentationIso
      (negativeSource a U V X) (source a U V X) where
  edgeRelabeling := reverseEdgeRelabeling a
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [oneFace_boundary, oneFace_boundary]
    simp only [List.map_append, List.map_singleton,
      reverseEdgeRelabeling_neg, reverseEdgeRelabeling_pos]
    rw [reverseEdgeRelabeling_word a U haU,
      reverseEdgeRelabeling_word a V haV,
      reverseEdgeRelabeling_word a X haX]

/-- Reversing `a` identifies the negative target spelling with the positive target spelling. -/
def negativeTargetSignedIso {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart) :
    SignedPresentationIso
      (negativeTarget a U V X) (target a U V X) where
  edgeRelabeling := reverseEdgeRelabeling a
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [oneFace_boundary, oneFace_boundary]
    simp only [List.map_append, List.map_singleton,
      reverseEdgeRelabeling_pos, reverseEdgeRelabeling_neg]
    rw [reverseEdgeRelabeling_word a U haU,
      reverseEdgeRelabeling_word a X haX,
      reverseEdgeRelabeling_word a V haV]

/-- The negatively spelled Dyck rewrite also preserves ordinary validity. -/
theorem negativeTarget_isSurfaceValid {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (validSource : (negativeSource a U V X).IsSurfaceValid) :
    (negativeTarget a U V X).IsSurfaceValid := by
  apply oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_singleton, edgeOfDart,
    List.count_append, List.count_cons, List.count_nil]
  omega

/-- The generic Dyck rewrite with the distinguished edge displayed negative first. -/
theorem negativeNormalizationEquivalent {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (validSource : (negativeSource a U V X).IsSurfaceValid)
    (validTarget : (negativeTarget a U V X).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨negativeSource a U V X, validSource⟩
      ⟨negativeTarget a U V X, validTarget⟩ := by
  let sourceIso := negativeSourceSignedIso a U V X haU haV haX
  let targetIso := negativeTargetSignedIso a U V X haU haV haX
  let validPositiveSource : (source a U V X).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  let validPositiveTarget : (target a U V X).IsSurfaceValid :=
    targetIso.isSurfaceValid validTarget
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      ((normalizationEquivalent a U V X haU haV haX
          validPositiveSource validPositiveTarget).trans
        (NormalizationEquivalent.ofSignedIso targetIso).symm)

end Dyck

namespace Crosscap

/-- The cross-cap rewrite preserves the unoriented edge-occurrence multiset, hence validity. -/
theorem target_isSurfaceValid {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (validSource : (source a X Y).IsSurfaceValid) :
    (target a X Y).IsSurfaceValid := by
  apply Dyck.oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_singleton, edgeOfDart,
    map_edgeOfDart_inverseWord, List.count_append, List.count_cons,
    List.count_nil, List.count_reverse]
  omega

/-- The cross-cap source with the distinguished edge displayed negative. -/
@[reducible]
def negativeSource {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (([.neg a] ++ X) ++ ([.neg a] ++ Y))

/-- The corresponding negatively oriented target. -/
@[reducible]
def negativeTarget {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace ((X ++ [.neg a]) ++ ([.neg a] ++ inverseWord Y))

/-- The negatively oriented cross-cap rewrite preserves ordinary validity. -/
theorem negativeTarget_isSurfaceValid {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (validSource : (negativeSource a X Y).IsSurfaceValid) :
    (negativeTarget a X Y).IsSurfaceValid := by
  apply Dyck.oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_singleton, edgeOfDart,
    map_edgeOfDart_inverseWord, List.count_append, List.count_cons,
    List.count_nil, List.count_reverse]
  omega

/-- The `negativeSourceSignedIso` declaration. -/
def negativeSourceSignedIso {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart) :
    SignedPresentationIso
      (negativeSource a X Y) (source a X Y) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling a
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [List.map_append, List.map_singleton,
      Dyck.reverseEdgeRelabeling_neg]
    rw [Dyck.reverseEdgeRelabeling_word a X haX,
      Dyck.reverseEdgeRelabeling_word a Y haY]

/-- The `negativeTargetSignedIso` declaration. -/
def negativeTargetSignedIso {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart) :
    SignedPresentationIso
      (negativeTarget a X Y) (target a X Y) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling a
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [List.map_append, List.map_singleton,
      Dyck.reverseEdgeRelabeling_neg]
    rw [Dyck.reverseEdgeRelabeling_word a X haX,
      Dyck.reverseEdgeRelabeling_word a (inverseWord Y) (by
        simpa [map_edgeOfDart_inverseWord] using haY)]

/-- The cross-cap rewrite with both distinguished occurrences displayed negative. -/
theorem negativeNormalizationEquivalent {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart)
    (validSource : (negativeSource a X Y).IsSurfaceValid)
    (validTarget : (negativeTarget a X Y).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨negativeSource a X Y, validSource⟩
      ⟨negativeTarget a X Y, validTarget⟩ := by
  let sourceIso := negativeSourceSignedIso a X Y haX haY
  let targetIso := negativeTargetSignedIso a X Y haX haY
  let validPositiveSource : (source a X Y).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  let validPositiveTarget : (target a X Y).IsSurfaceValid :=
    targetIso.isSurfaceValid validTarget
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      ((normalizationEquivalent a X Y haX haY
          validPositiveSource validPositiveTarget).trans
        (NormalizationEquivalent.ofSignedIso targetIso).symm)

/-- The adjacent-crosscap source `a a X Y`. -/
@[reducible]
def adjacentSource {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace ([.pos a, .pos a] ++ X ++ Y)

/-- The alternate cross-cap target `a Y a X⁻¹`. -/
@[reducible]
def adjacentTarget {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  source a Y (inverseWord X)

/-- The alternate adjacent-crosscap rewrite preserves ordinary validity. -/
theorem adjacentTarget_isSurfaceValid {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (validSource : (adjacentSource a X Y).IsSurfaceValid) :
    (adjacentTarget a X Y).IsSurfaceValid := by
  apply Dyck.oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_cons, List.map_nil, edgeOfDart,
    map_edgeOfDart_inverseWord, List.count_append, List.count_cons,
    List.count_nil, List.count_reverse]
  omega

/-- `a a X Y` is a rotation of the ordinary cross-cap target obtained from
`a Y a X⁻¹`. -/
theorem adjacentSource_isRotated_target {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (adjacentSource a X Y).boundary 0 |>.IsRotated
      ((target a Y (inverseWord X)).boundary 0) := by
  simp only [adjacentSource, target, Dyck.oneFace_boundary_zero,
    inverseWord_inverseWord]
  convert
    (List.isRotated_append
      (l := [SignedDart.pos a, SignedDart.pos a] ++ X)
      (l' := Y)) using 1
  all_goals simp only [List.nil_append, List.cons_append,
    List.append_assoc]

/-- Gallier--Xu's alternate rule `a a X Y ~ a Y a X⁻¹`. -/
theorem adjacentNormalizationEquivalent {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart)
    (validSource : (adjacentSource a X Y).IsSurfaceValid)
    (validTarget : (adjacentTarget a X Y).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨adjacentSource a X Y, validSource⟩
      ⟨adjacentTarget a X Y, validTarget⟩ := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (adjacentSource_isRotated_target a X Y)
  let validGenericTarget :
      (target a Y (inverseWord X)).IsSurfaceValid :=
    rotation.isSurfaceValid validSource
  have hRotate :
      NormalizationEquivalent
        ⟨adjacentSource a X Y, validSource⟩
        ⟨target a Y (inverseWord X), validGenericTarget⟩ :=
    NormalizationEquivalent.ofSignedIso rotation
  have haInverseX : a ∉ (inverseWord X).map edgeOfDart := by
    simpa [map_edgeOfDart_inverseWord] using haX
  have hCrosscap :
      NormalizationEquivalent
        ⟨source a Y (inverseWord X), validTarget⟩
        ⟨target a Y (inverseWord X), validGenericTarget⟩ :=
    normalizationEquivalent a Y (inverseWord X)
      haY haInverseX validTarget validGenericTarget
  exact hRotate.trans hCrosscap.symm

end Crosscap

namespace Handle

/-- The source spelling for Gallier--Xu handle extraction. -/
@[reducible]
def source {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.source a U ([.pos b] ++ V) (X ++ [.neg b] ++ Y)

/-- The result of the first Dyck rewrite. -/
@[reducible]
def afterFirst {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.target a U ([.pos b] ++ V) (X ++ [.neg b] ++ Y)

/-- A cyclic spelling of `afterFirst` exposing the two occurrences of `b`. -/
@[reducible]
def secondSource {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.source b (V ++ U) ([.neg a] ++ X) (Y ++ [.pos a])

/-- The result of the second Dyck rewrite. -/
@[reducible]
def afterSecond {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.target b (V ++ U) ([.neg a] ++ X) (Y ++ [.pos a])

/-- A cyclic spelling of `afterSecond` exposing `a⁻¹` before `a`. -/
@[reducible]
def thirdSource {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.negativeSource a (X ++ V ++ U) ([.neg b] ++ Y) [.pos b]

/-- The target spelling contains the handle `a b a⁻¹ b⁻¹`, followed cyclically by
`Y X V U`. -/
@[reducible]
def target {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.negativeTarget a (X ++ V ++ U) ([.neg b] ++ Y) [.pos b]

/-- Handle extraction preserves the unoriented edge-occurrence multiset, hence ordinary
validity. -/
theorem target_isSurfaceValid {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n)))
    (validSource : (source a b U V X Y).IsSurfaceValid) :
    (target a b U V X Y).IsSurfaceValid := by
  apply Dyck.oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_cons, List.map_nil, edgeOfDart,
    List.count_append, List.count_cons, List.count_nil]
  omega

/-- The chosen target spelling is cyclically the handle
`a b a⁻¹ b⁻¹`, followed by `Y X V U`. -/
theorem target_boundary_isRotated_handle {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    (target a b U V X Y).boundary 0 |>.IsRotated
      ([.pos a, .pos b, .neg a, .neg b] ++ Y ++ X ++ V ++ U) := by
  simp only [target, Dyck.negativeTarget, Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := X ++ V ++ U)
      (l' := [SignedDart.pos a, SignedDart.pos b,
        SignedDart.neg a, SignedDart.neg b] ++ Y)) using 1 <;>
    simp only [List.nil_append, List.cons_append, List.append_assoc]

/-- Rotate the first Dyck target to expose the second distinguished edge. -/
theorem afterFirst_isRotated_secondSource {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    (afterFirst a b U V X Y).boundary 0 |>.IsRotated
      ((secondSource a b U V X Y).boundary 0) := by
  simp only [afterFirst, secondSource, Dyck.target, Dyck.source,
    Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := U ++ [SignedDart.neg a] ++ X ++
        [SignedDart.neg b] ++ Y ++ [SignedDart.pos a])
      (l' := [SignedDart.pos b] ++ V)) using 1 <;>
    simp only [List.cons_append, List.append_assoc]

/-- Rotate the second Dyck target to expose `a` in the opposite orientation. -/
theorem afterSecond_isRotated_thirdSource {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    (afterSecond a b U V X Y).boundary 0 |>.IsRotated
      ((thirdSource a b U V X Y).boundary 0) := by
  simp only [afterSecond, thirdSource, Dyck.target, Dyck.negativeSource,
    Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := V ++ U ++ [SignedDart.neg b] ++ Y ++
        [SignedDart.pos a] ++ [SignedDart.pos b])
      (l' := [SignedDart.neg a] ++ X)) using 1 <;>
    simp only [List.cons_append, List.append_assoc]

/-- Gallier--Xu's three-Dyck chain extracts the interleaved opposite pairs as a handle. -/
theorem normalizationEquivalent {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n)))
    (hab : a ≠ b)
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart)
    (hbU : b ∉ U.map edgeOfDart)
    (hbV : b ∉ V.map edgeOfDart)
    (hbX : b ∉ X.map edgeOfDart)
    (hbY : b ∉ Y.map edgeOfDart)
    (validSource : (source a b U V X Y).IsSurfaceValid)
    (validTarget : (target a b U V X Y).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source a b U V X Y, validSource⟩
      ⟨target a b U V X Y, validTarget⟩ := by
  have haBV :
      a ∉ ([SignedDart.pos b] ++ V).map edgeOfDart := by
    simp [edgeOfDart, hab, haV]
  have haXbY :
      a ∉ (X ++ [SignedDart.neg b] ++ Y).map edgeOfDart := by
    simp [edgeOfDart, haX, hab, haY]
  let validAfterFirst : (afterFirst a b U V X Y).IsSurfaceValid :=
    Dyck.target_isSurfaceValid a U ([SignedDart.pos b] ++ V)
      (X ++ [SignedDart.neg b] ++ Y) validSource
  have hFirst :
      NormalizationEquivalent
        ⟨source a b U V X Y, validSource⟩
        ⟨afterFirst a b U V X Y, validAfterFirst⟩ :=
    Dyck.normalizationEquivalent a U ([SignedDart.pos b] ++ V)
      (X ++ [SignedDart.neg b] ++ Y) haU haBV haXbY
      validSource validAfterFirst
  let firstRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (afterFirst_isRotated_secondSource a b U V X Y)
  let validSecondSource : (secondSource a b U V X Y).IsSurfaceValid :=
    firstRotation.isSurfaceValid validAfterFirst
  have hRotateFirst :
      NormalizationEquivalent
        ⟨afterFirst a b U V X Y, validAfterFirst⟩
        ⟨secondSource a b U V X Y, validSecondSource⟩ :=
    NormalizationEquivalent.ofSignedIso firstRotation
  have hbVU : b ∉ (V ++ U).map edgeOfDart := by
    simp [hbV, hbU]
  have hbNegAX :
      b ∉ ([SignedDart.neg a] ++ X).map edgeOfDart := by
    simp [edgeOfDart, hab.symm, hbX]
  have hbYPosA :
      b ∉ (Y ++ [SignedDart.pos a]).map edgeOfDart := by
    simp [edgeOfDart, hbY, hab.symm]
  let validAfterSecond : (afterSecond a b U V X Y).IsSurfaceValid :=
    Dyck.target_isSurfaceValid b (V ++ U) ([SignedDart.neg a] ++ X)
      (Y ++ [SignedDart.pos a]) validSecondSource
  have hSecond :
      NormalizationEquivalent
        ⟨secondSource a b U V X Y, validSecondSource⟩
        ⟨afterSecond a b U V X Y, validAfterSecond⟩ :=
    Dyck.normalizationEquivalent b (V ++ U) ([SignedDart.neg a] ++ X)
      (Y ++ [SignedDart.pos a]) hbVU hbNegAX hbYPosA
      validSecondSource validAfterSecond
  let secondRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (afterSecond_isRotated_thirdSource a b U V X Y)
  let validThirdSource : (thirdSource a b U V X Y).IsSurfaceValid :=
    secondRotation.isSurfaceValid validAfterSecond
  have hRotateSecond :
      NormalizationEquivalent
        ⟨afterSecond a b U V X Y, validAfterSecond⟩
        ⟨thirdSource a b U V X Y, validThirdSource⟩ :=
    NormalizationEquivalent.ofSignedIso secondRotation
  have haXVU : a ∉ (X ++ V ++ U).map edgeOfDart := by
    simp [haX, haV, haU]
  have haNegBY :
      a ∉ ([SignedDart.neg b] ++ Y).map edgeOfDart := by
    simp [edgeOfDart, hab, haY]
  have haPosB :
      a ∉ ([SignedDart.pos b] : List (SignedDart (Fin n))).map edgeOfDart := by
    simp [edgeOfDart, hab]
  have hThird :
      NormalizationEquivalent
        ⟨thirdSource a b U V X Y, validThirdSource⟩
        ⟨target a b U V X Y, validTarget⟩ :=
    Dyck.negativeNormalizationEquivalent a
      (X ++ V ++ U) ([SignedDart.neg b] ++ Y) [SignedDart.pos b]
      haXVU haNegBY haPosB validThirdSource validTarget
  exact hFirst.trans
    (hRotateFirst.trans
      (hSecond.trans (hRotateSecond.trans hThird)))

end Handle

namespace HandleToCrosscaps

-- A compact interface for one validity-preserving normalization rewrite.  Keeping validity
-- transport inside the certificate prevents long chains from exposing every dependent witness.
private structure RewriteCertificate (P Q : FiniteCyclicPresentation) : Prop where
  target_isSurfaceValid : P.IsSurfaceValid → Q.IsSurfaceValid
  normalizationEquivalent :
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      NormalizationEquivalent ⟨P, validP⟩ ⟨Q, validQ⟩

-- Composition chooses the intermediate validity witness once, behind the compact interface.
private theorem RewriteCertificate.trans {P Q R : FiniteCyclicPresentation}
    (hPQ : RewriteCertificate P Q) (hQR : RewriteCertificate Q R) :
    RewriteCertificate P R where
  target_isSurfaceValid validP := hQR.target_isSurfaceValid (hPQ.target_isSurfaceValid validP)
  normalizationEquivalent validP validR := by
    let validQ := hPQ.target_isSurfaceValid validP
    exact (hPQ.normalizationEquivalent validP validQ).trans
      (hQR.normalizationEquivalent validQ validR)

-- Package the generic negative cross-cap rule without specializing its presentation expressions.
private theorem negativeCrosscap_rewriteCertificate {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart) (haY : a ∉ Y.map edgeOfDart) :
    RewriteCertificate (Crosscap.negativeSource a X Y) (Crosscap.negativeTarget a X Y) := by
  constructor
  · exact Crosscap.negativeTarget_isSurfaceValid a X Y
  · exact Crosscap.negativeNormalizationEquivalent a X Y haX haY

-- Package the generic positive cross-cap rule at the same compact interface.
private theorem crosscap_rewriteCertificate {n : ℕ} (a : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart) (haY : a ∉ Y.map edgeOfDart) :
    RewriteCertificate (Crosscap.source a X Y) (Crosscap.target a X Y) := by
  constructor
  · exact Crosscap.target_isSurfaceValid a X Y
  · exact Crosscap.normalizationEquivalent a X Y haX haY

/-- A crosscap followed by a handle, with arbitrary intervening words `X` and `Y`. -/
@[reducible]
def source {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.adjacentSource a
    (X ++ [.pos b, .pos c]) ([.neg b, .neg c] ++ Y)

/-- The first alternate cross-cap rewrite. -/
@[reducible]
def afterFirst {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.adjacentTarget a
    (X ++ [.pos b, .pos c]) ([.neg b, .neg c] ++ Y)

/-- Rotate the first target to expose the two negative occurrences of `b`. -/
@[reducible]
def secondSource {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.negativeSource b
    ([.neg c] ++ Y ++ [.pos a] ++ [.neg c])
    (inverseWord X ++ [.pos a])

/-- The result of rewriting the two negative occurrences of `b`. -/
@[reducible]
def afterSecond {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.negativeTarget b
    ([.neg c] ++ Y ++ [.pos a] ++ [.neg c])
    (inverseWord X ++ [.pos a])

/-- Expose the two negative occurrences of `c`. -/
@[reducible]
def thirdSource {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.negativeSource c
    (Y ++ [.pos a])
    ([.neg b, .neg b, .neg a] ++ X)

/-- The result of rewriting the two negative occurrences of `c`. -/
@[reducible]
def afterThird {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.negativeTarget c
    (Y ++ [.pos a])
    ([.neg b, .neg b, .neg a] ++ X)

/-- Expose the remaining two occurrences of `a`. -/
@[reducible]
def fourthSource {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.source a
    ([.pos b, .pos b] ++ Y)
    ([.neg c, .neg c] ++ inverseWord X)

/-- The final spelling is cyclically `a a X c c b b Y`: three crosscaps. -/
@[reducible]
def target {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.target a
    ([.pos b, .pos b] ++ Y)
    ([.neg c, .neg c] ++ inverseWord X)

theorem afterFirst_isRotated_secondSource {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (afterFirst a b c X Y).boundary 0 |>.IsRotated
      ((secondSource a b c X Y).boundary 0) := by
  simp only [afterFirst, secondSource, Crosscap.adjacentTarget,
    Crosscap.source, Crosscap.negativeSource,
    Dyck.oneFace_boundary_zero, inverseWord_append]
  convert
    (List.isRotated_append
      (l := [SignedDart.pos a])
      (l' := [SignedDart.neg b, SignedDart.neg c] ++ Y ++
        [SignedDart.pos a, SignedDart.neg c, SignedDart.neg b] ++
        inverseWord X)) using 1
  all_goals simp only [inverseWord, SignedDart.flip, List.reverse_cons,
    List.reverse_nil, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.append_assoc]

theorem afterSecond_isRotated_thirdSource {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (afterSecond a b c X Y).boundary 0 |>.IsRotated
      ((thirdSource a b c X Y).boundary 0) := by
  simpa only [afterSecond, thirdSource, Crosscap.negativeTarget,
    Crosscap.negativeSource, Dyck.oneFace_boundary_zero,
    inverseWord_append, inverseWord_inverseWord,
    Dyck.inverseWord_singleton, SignedDart.flip,
    List.cons_append, List.nil_append, List.append_assoc] using
      (List.IsRotated.refl ((thirdSource a b c X Y).boundary 0))

theorem afterThird_isRotated_fourthSource {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (afterThird a b c X Y).boundary 0 |>.IsRotated
      ((fourthSource a b c X Y).boundary 0) := by
  simp only [afterThird, fourthSource, Crosscap.negativeTarget,
    Crosscap.source, Dyck.oneFace_boundary_zero, inverseWord_append]
  convert
    (List.isRotated_append
      (l := Y ++ [SignedDart.pos a, SignedDart.neg c,
        SignedDart.neg c] ++ inverseWord X)
      (l' := [SignedDart.pos a, SignedDart.pos b,
        SignedDart.pos b])) using 1
  all_goals simp only [inverseWord, SignedDart.flip, List.reverse_cons,
    List.reverse_nil, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.append_assoc]

/-- Check the exact final cyclic order of the three crosscaps. -/
theorem target_boundary_isRotated_crosscaps {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    (target a b c X Y).boundary 0 |>.IsRotated
      ([.pos a, .pos a] ++ X ++
        [.pos c, .pos c, .pos b, .pos b] ++ Y) := by
  simp only [target, Crosscap.target, Dyck.oneFace_boundary_zero,
    inverseWord_append, inverseWord_inverseWord]
  convert
    (List.isRotated_append
      (l := [SignedDart.pos b, SignedDart.pos b] ++ Y)
      (l' := [SignedDart.pos a, SignedDart.pos a] ++ X ++
        [SignedDart.pos c, SignedDart.pos c])) using 1
  all_goals simp only [inverseWord, SignedDart.flip, List.reverse_cons,
    List.reverse_nil, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.append_assoc]

-- The first alternate cross-cap rewrite, with its validity transport hidden in a certificate.
private theorem first_rewriteCertificate {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (hab : a ≠ b) (hac : a ≠ c)
    (haX : a ∉ X.map edgeOfDart) (haY : a ∉ Y.map edgeOfDart) :
    RewriteCertificate (source a b c X Y) (afterFirst a b c X Y) := by
  have haFirstX :
      a ∉ (X ++ [SignedDart.pos b, SignedDart.pos c]).map edgeOfDart := by
    simp [edgeOfDart, haX, hab, hac]
  have haFirstY :
      a ∉ ([SignedDart.neg b, SignedDart.neg c] ++ Y).map edgeOfDart := by
    simp [edgeOfDart, hab, hac, haY]
  constructor
  · exact Crosscap.adjacentTarget_isSurfaceValid a
      (X ++ [.pos b, .pos c]) ([.neg b, .neg c] ++ Y)
  · intro validP validQ
    exact Crosscap.adjacentNormalizationEquivalent a
      (X ++ [.pos b, .pos c]) ([.neg b, .neg c] ++ Y)
      haFirstX haFirstY validP validQ

-- Rotation after the first rewrite is independent of the chosen validity witnesses.
private theorem first_rotationCertificate {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    RewriteCertificate (afterFirst a b c X Y) (secondSource a b c X Y) := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (afterFirst_isRotated_secondSource a b c X Y)
  constructor
  · exact rotation.isSurfaceValid
  · intro _ _
    exact NormalizationEquivalent.ofSignedIso rotation

-- Rotation after rewriting `b` exposes the two negative occurrences of `c`.
private theorem second_rotationCertificate {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    RewriteCertificate (afterSecond a b c X Y) (thirdSource a b c X Y) := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (afterSecond_isRotated_thirdSource a b c X Y)
  constructor
  · exact rotation.isSurfaceValid
  · intro _ _
    exact NormalizationEquivalent.ofSignedIso rotation

-- The final rotation exposes the two remaining occurrences of `a`.
private theorem third_rotationCertificate {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    RewriteCertificate (afterThird a b c X Y) (fourthSource a b c X Y) := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (afterThird_isRotated_fourthSource a b c X Y)
  constructor
  · exact rotation.isSurfaceValid
  · intro _ _
    exact NormalizationEquivalent.ofSignedIso rotation

/-- Gallier--Xu Step 5: a crosscap and a handle are equivalent to three crosscaps. -/
theorem normalizationEquivalent {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n)))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haX : a ∉ X.map edgeOfDart) (haY : a ∉ Y.map edgeOfDart)
    (hbX : b ∉ X.map edgeOfDart) (hbY : b ∉ Y.map edgeOfDart)
    (hcX : c ∉ X.map edgeOfDart) (hcY : c ∉ Y.map edgeOfDart)
    (validSource : (source a b c X Y).IsSurfaceValid)
    (validTarget : (target a b c X Y).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source a b c X Y, validSource⟩
      ⟨target a b c X Y, validTarget⟩ := by
  have hbSecondX :
      b ∉ ([SignedDart.neg c] ++ Y ++
        [SignedDart.pos a] ++ [SignedDart.neg c]).map edgeOfDart := by
    simp [edgeOfDart, hbc, hbY, hab.symm]
  have hbSecondY :
      b ∉ (inverseWord X ++ [SignedDart.pos a]).map edgeOfDart := by
    simp [map_edgeOfDart_inverseWord, hbX, edgeOfDart, hab.symm]
  have hcThirdX :
      c ∉ (Y ++ [SignedDart.pos a]).map edgeOfDart := by
    simp [hcY, edgeOfDart, hac.symm]
  have hcThirdY :
      c ∉ ([SignedDart.neg b, SignedDart.neg b,
        SignedDart.neg a] ++ X).map edgeOfDart := by
    simp [edgeOfDart, hbc.symm, hac.symm, hcX]
  have haFourthX :
      a ∉ ([SignedDart.pos b, SignedDart.pos b] ++ Y).map edgeOfDart := by
    simp [edgeOfDart, hab, haY]
  have haFourthY :
      a ∉ ([SignedDart.neg c, SignedDart.neg c] ++
        inverseWord X).map edgeOfDart := by
    simp [edgeOfDart, hac, map_edgeOfDart_inverseWord, haX]
  let chain₁ :=
    (first_rewriteCertificate a b c X Y hab hac haX haY).trans
      (first_rotationCertificate a b c X Y)
  let chain₂ := chain₁.trans
    (negativeCrosscap_rewriteCertificate b
      ([.neg c] ++ Y ++ [.pos a] ++ [.neg c])
      (inverseWord X ++ [.pos a]) hbSecondX hbSecondY)
  let chain₃ := chain₂.trans (second_rotationCertificate a b c X Y)
  let chain₄ := chain₃.trans
    (negativeCrosscap_rewriteCertificate c
      (Y ++ [.pos a]) ([.neg b, .neg b, .neg a] ++ X)
      hcThirdX hcThirdY)
  let chain₅ := chain₄.trans (third_rotationCertificate a b c X Y)
  let chain := chain₅.trans
    (crosscap_rewriteCertificate a
      ([.pos b, .pos b] ++ Y) ([.neg c, .neg c] ++ inverseWord X)
      haFourthX haFourthY)
  exact chain.normalizationEquivalent validSource validTarget

end HandleToCrosscaps

namespace LoopGrouping

/-- A cyclic word with the loop block `a H a⁻¹`, a separating word `X`, and a block `V` to
move next to the loop. -/
@[reducible]
def source {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (([.pos a] ++ H) ++ ([.neg a] ++ X ++ V))

/-- Rotate the source to expose the negative occurrence of `a` first. -/
@[reducible]
def rotatedSource {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.negativeSource a X V H

/-- The target is cyclically `a H a⁻¹ V X`, so `V` has crossed the separating word `X`. -/
@[reducible]
def target {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.negativeTarget a X V H

theorem source_isRotated_rotatedSource {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    (source a H X V).boundary 0 |>.IsRotated
      ((rotatedSource a H X V).boundary 0) := by
  simp only [source, rotatedSource, Dyck.negativeSource,
    Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := [SignedDart.pos a] ++ H)
      (l' := [SignedDart.neg a] ++ X ++ V)) using 1
  all_goals simp only [List.cons_append, List.append_assoc]

/-- The target spelling displays the moved block immediately after the loop. -/
theorem target_boundary_isRotated_grouped {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    (target a H X V).boundary 0 |>.IsRotated
      ([.pos a] ++ H ++ [.neg a] ++ V ++ X) := by
  simp only [target, Dyck.negativeTarget, Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := X)
      (l' := [SignedDart.pos a] ++ H ++
        [SignedDart.neg a] ++ V)) using 1
  all_goals simp only [List.cons_append, List.append_assoc]

/-- Gallier--Xu loop grouping is one negative Dyck rewrite after a cyclic rotation. -/
theorem normalizationEquivalent {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n)))
    (haH : a ∉ H.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (validSource : (source a H X V).IsSurfaceValid)
    (validTarget : (target a H X V).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source a H X V, validSource⟩
      ⟨target a H X V, validTarget⟩ := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (source_isRotated_rotatedSource a H X V)
  let validRotatedSource : (rotatedSource a H X V).IsSurfaceValid :=
    rotation.isSurfaceValid validSource
  have hRotate :
      NormalizationEquivalent
        ⟨source a H X V, validSource⟩
        ⟨rotatedSource a H X V, validRotatedSource⟩ :=
    NormalizationEquivalent.ofSignedIso rotation
  have hDyck :
      NormalizationEquivalent
        ⟨rotatedSource a H X V, validRotatedSource⟩
        ⟨target a H X V, validTarget⟩ :=
    Dyck.negativeNormalizationEquivalent a X V H
      haX haV haH validRotatedSource validTarget
  exact hRotate.trans hDyck

end LoopGrouping

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
