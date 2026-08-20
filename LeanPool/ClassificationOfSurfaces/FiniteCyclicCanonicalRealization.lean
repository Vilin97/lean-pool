/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.CanonicalGeneratorMaps
import LeanPool.ClassificationOfSurfaces.FiniteCyclicCanonical
import LeanPool.ClassificationOfSurfaces.FiniteCyclicSignedRealization
import LeanPool.ClassificationOfSurfaces.SphereQuotientHomeomorph

/-!
# Realization of canonical finite-cyclic presentations

`FiniteCyclicPresentation.ofOneFaceWord` enumerates the edge names of an existing typed
one-face word.  This file proves that the enumeration does not change the faithful polygonal
quotient.  The result is the only adapter between the finite-cyclic normalization target and the
already-certified canonical polygonal quotients; in particular, it does not restate either
Lean-Eval relation.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

open SurfaceCellComplex

namespace FiniteCyclicPresentation

variable {Edge : Type} [Fintype Edge]

theorem ofOneFaceWord_boundary_length
    (word : List (SignedDart Edge)) (f : (ofOneFaceWord word).Face) :
    ((ofOneFaceWord word).boundary f).length = word.length := by
  rw [ofOneFaceWord_boundary]
  simp

/-- The unique enumerated face is equivalent to the unique typed one-face face. -/
noncomputable def ofOneFaceWordFaceEquiv (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).Face ≃ PUnit where
  toFun := fun _ ↦ PUnit.unit
  invFun := fun _ ↦ 0
  left_inv := fun f ↦ (ofOneFaceWord_face_eq_zero word f).symm
  right_inv := by
    intro f
    cases f
    rfl

/-- The face disk of the enumerated word, with its phantom side count cast back to the original
word length. -/
noncomputable def ofOneFaceWordFaceHomeomorph
    (word : List (SignedDart Edge)) (f : (ofOneFaceWord word).Face) :
    PolygonCell ((ofOneFaceWord word).boundary f).length ≃ₜ
      PolygonCell word.length :=
  PolygonCell.rotateHomeomorph (ofOneFaceWord_boundary_length word f) 0

/-- Enumerating the edge names and the unique face leaves the polygonal pre-realization
homeomorphic to the original typed one-face pre-realization. -/
noncomputable def ofOneFaceWordPreHomeomorph
    (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).PolygonalPreRealization ≃ₜ
      (oneFacePresentation Edge word).PolygonalPreRealization :=
  (IsHomeomorph.sigmaMap (ofOneFaceWordFaceEquiv word).bijective
      (fun f => (ofOneFaceWordFaceHomeomorph word f).isHomeomorph)).homeomorph
    (Sigma.map (ofOneFaceWordFaceEquiv word)
      fun f => ofOneFaceWordFaceHomeomorph word f)

@[simp]
theorem ofOneFaceWordPreHomeomorph_apply_fst
    (word : List (SignedDart Edge))
    (x : (ofOneFaceWord word).PolygonalPreRealization) :
    (ofOneFaceWordPreHomeomorph word x).1 = PUnit.unit :=
  rfl

@[simp]
theorem ofOneFaceWordPreHomeomorph_apply_snd
    (word : List (SignedDart Edge))
    (x : (ofOneFaceWord word).PolygonalPreRealization) :
    (ofOneFaceWordPreHomeomorph word x).2 =
      ofOneFaceWordFaceHomeomorph word x.1 x.2 :=
  rfl

/-- A boundary position of the enumerated word, read as the same position of the original typed
word. -/
noncomputable def ofOneFaceWordMapOccurrence
    (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).BoundaryOccurrence →
      (oneFacePresentation Edge word).BoundaryOccurrence
  | ⟨f, i⟩ =>
      ⟨PUnit.unit, Fin.cast (ofOneFaceWord_boundary_length word f) i⟩

@[simp]
theorem ofOneFaceWordMapOccurrence_fst
    (word : List (SignedDart Edge))
    (o : (ofOneFaceWord word).BoundaryOccurrence) :
    (ofOneFaceWordMapOccurrence word o).1 = PUnit.unit :=
  rfl

@[simp]
theorem ofOneFaceWordMapOccurrence_snd_val
    (word : List (SignedDart Edge))
    (o : (ofOneFaceWord word).BoundaryOccurrence) :
    (ofOneFaceWordMapOccurrence word o).2.val = o.2.val :=
  rfl

/-- The pre-realization homeomorphism is parameter-exact on every labelled side. -/
theorem ofOneFaceWordPreHomeomorph_occurrenceSide_point
    (word : List (SignedDart Edge))
    (o : (ofOneFaceWord word).BoundaryOccurrence) (t : unitInterval) :
    ofOneFaceWordPreHomeomorph word
        (((ofOneFaceWord word).occurrenceSide o).point t) =
      ((oneFacePresentation Edge word).occurrenceSide
        (ofOneFaceWordMapOccurrence word o)).point t := by
  rcases o with ⟨f, i⟩
  change
    ofOneFaceWordPreHomeomorph word
        ⟨f, PolygonCell.side i t⟩ =
      ⟨PUnit.unit,
        PolygonCell.side
          (Fin.cast (ofOneFaceWord_boundary_length word f) i) t⟩
  apply Sigma.ext
  · rfl
  · simp only [ofOneFaceWordPreHomeomorph_apply_snd,
      ofOneFaceWordFaceHomeomorph]
    apply heq_of_eq
    rw [PolygonCell.rotateHomeomorph_side_of_eq
      (ofOneFaceWord_boundary_length word f)
      (by
        rw [← ofOneFaceWord_boundary_length word f]
        exact Nat.zero_lt_of_lt i.isLt)
      0 i t]
    congr 2
    apply Fin.ext
    simp only [Nat.add_zero, Fin.cast]
    exact Nat.mod_eq_of_lt (by
      simpa only [ofOneFaceWord_boundary_length] using i.isLt)

/-- Relabeling the original dart at a mapped position recovers the enumerated dart exactly. -/
theorem ofOneFaceWordMapOccurrence_dart
    (word : List (SignedDart Edge))
    (o : (ofOneFaceWord word).BoundaryOccurrence) :
    SignedDart.mapEquiv (Fintype.equivFin Edge)
        ((oneFacePresentation Edge word).occurrenceDart
          (ofOneFaceWordMapOccurrence word o)) =
      o.dart := by
  rcases o with ⟨f, i⟩
  have hf : f = 0 := ofOneFaceWord_face_eq_zero word f
  subst f
  simp only [BoundaryOccurrence.dart_mk, List.get_eq_getElem,
    ofOneFaceWord_boundary, List.getElem_map,
    EmbeddingLike.apply_eq_iff_eq]
  change word.get _ = word.get _
  congr 1

/-- The inverse occurrence transport, from the typed one-face word to its enumeration. -/
noncomputable def ofOneFaceWordComapOccurrence
    (word : List (SignedDart Edge)) :
    (oneFacePresentation Edge word).BoundaryOccurrence →
      (ofOneFaceWord word).BoundaryOccurrence
  | ⟨f, i⟩ =>
      ⟨0, Fin.cast
        (ofOneFaceWord_boundary_length word 0).symm
        (by
          cases f
          exact i)⟩

/-- Boundary positions are unchanged by enumeration. -/
noncomputable def ofOneFaceWordOccurrenceEquiv
    (word : List (SignedDart Edge)) :
    (ofOneFaceWord word).BoundaryOccurrence ≃
      (oneFacePresentation Edge word).BoundaryOccurrence where
  toFun := ofOneFaceWordMapOccurrence word
  invFun := ofOneFaceWordComapOccurrence word
  left_inv := by
    rintro ⟨f, i⟩
    have hf : f = 0 := ofOneFaceWord_face_eq_zero word f
    subst f
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      rfl
  right_inv := by
    rintro ⟨f, i⟩
    cases f
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      rfl

@[simp]
theorem ofOneFaceWordOccurrenceEquiv_apply
    (word : List (SignedDart Edge))
    (o : (ofOneFaceWord word).BoundaryOccurrence) :
    ofOneFaceWordOccurrenceEquiv word o =
      ofOneFaceWordMapOccurrence word o :=
  rfl

@[simp]
theorem ofOneFaceWordMapOccurrence_comap
    (word : List (SignedDart Edge))
    (o : (oneFacePresentation Edge word).BoundaryOccurrence) :
    ofOneFaceWordMapOccurrence word
        ((ofOneFaceWordOccurrenceEquiv word).symm o) = o :=
  (ofOneFaceWordOccurrenceEquiv word).apply_symm_apply o

theorem ofOneFaceWordComapOccurrence_dart
    (word : List (SignedDart Edge))
    (o : (oneFacePresentation Edge word).BoundaryOccurrence) :
    SignedDart.mapEquiv (Fintype.equivFin Edge)
        ((oneFacePresentation Edge word).occurrenceDart o) =
      (FiniteCyclicPresentation.BoundaryOccurrence.dart
        ((ofOneFaceWordOccurrenceEquiv word).symm o)) := by
  rw [← ofOneFaceWordMapOccurrence_dart word
    ((ofOneFaceWordOccurrenceEquiv word).symm o)]
  rw [ofOneFaceWordMapOccurrence_comap]

/-- Two distinct occurrences of one finite-cyclic edge force that edge to be internal. -/
theorem IsSurfaceValid.not_isBoundaryEdge_of_distinct_occurrences
    {P : FiniteCyclicPresentation} (_valid : P.IsSurfaceValid)
    (source target : P.BoundaryOccurrence) (hne : source ≠ target)
    (hedge : target.edge = source.edge) :
    ¬P.IsBoundaryEdge source.edge := by
  intro hboundary
  have hcard : (P.edgeOccurrences source.edge).card = 1 := by
    rw [P.card_edgeOccurrences]
    exact hboundary
  obtain ⟨only, hset⟩ := Finset.card_eq_one.mp hcard
  have hsource : source ∈ P.edgeOccurrences source.edge := by
    exact (P.mem_edgeOccurrences source.edge source).mpr rfl
  have htarget : target ∈ P.edgeOccurrences source.edge := by
    exact (P.mem_edgeOccurrences source.edge target).mpr hedge
  have hs : source = only := by simpa only [hset, Finset.mem_singleton] using hsource
  have ht : target = only := by simpa only [hset, Finset.mem_singleton] using htarget
  exact hne (hs.trans ht.symm)

/-- Transport a finite-cyclic pairing back to the original typed one-face word. -/
noncomputable def ofOneFaceWordMapPairing
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) :
    (oneFacePresentation Edge word).BoundaryPairing := by
  let K := oneFacePresentation Edge word
  let source := ofOneFaceWordMapOccurrence word pairing.source
  let target := ofOneFaceWordMapOccurrence word pairing.target
  have hne : source ≠ target :=
    (ofOneFaceWordOccurrenceEquiv word).injective.ne pairing.source_ne_target
  have hcompatible :
      match pairing.direction with
      | .same => K.occurrenceDart target = K.occurrenceDart source
      | .opposite =>
          K.occurrenceDart target = K.inv (K.occurrenceDart source) := by
    cases hdirection : pairing.direction with
    | same =>
        have hp : pairing.target.dart = pairing.source.dart := by
          simpa only [hdirection] using pairing.compatible
        apply (SignedDart.mapEquiv (Fintype.equivFin Edge)).injective
        rw [ofOneFaceWordMapOccurrence_dart,
          ofOneFaceWordMapOccurrence_dart]
        exact hp
    | opposite =>
        have hp : pairing.target.dart = pairing.source.dart.flip := by
          simpa only [hdirection] using pairing.compatible
        apply (SignedDart.mapEquiv (Fintype.equivFin Edge)).injective
        change
          SignedDart.mapEquiv (Fintype.equivFin Edge)
              (K.occurrenceDart target) =
            SignedDart.mapEquiv (Fintype.equivFin Edge)
              (K.occurrenceDart source).flip
        rw [SignedDart.mapEquiv_flip,
          ofOneFaceWordMapOccurrence_dart,
          ofOneFaceWordMapOccurrence_dart]
        exact hp
  have horbit :
      K.Occurs (K.occurrenceDart source) target := by
    cases hdirection : pairing.direction with
    | same =>
        left
        simpa only [hdirection] using hcompatible
    | opposite =>
        right
        simpa only [hdirection] using hcompatible
  have hsourceBoundary :
      ¬K.IsBoundaryDart (K.occurrenceDart source) :=
    SurfaceCellComplex.not_isBoundaryDart_of_occurs_at_ne
      hne (Or.inl rfl) horbit
  have htargetBoundary :
      ¬K.IsBoundaryDart (K.occurrenceDart target) := by
    cases hdirection : pairing.direction with
    | same =>
        have hsame : K.occurrenceDart target = K.occurrenceDart source := by
          simpa only [hdirection] using hcompatible
        rw [hsame]
        exact hsourceBoundary
    | opposite =>
        have hopp :
            K.occurrenceDart target = K.inv (K.occurrenceDart source) := by
          simpa only [hdirection] using hcompatible
        rw [hopp]
        exact ((K.isBoundaryDart_inv_iff
          (K.occurrenceDart source)).not).mpr hsourceBoundary
  exact
    { source := source
      target := target
      source_ne_target := hne
      source_not_boundary := hsourceBoundary
      target_not_boundary := htargetBoundary
      direction := pairing.direction
      compatible := hcompatible }

/-- Pull a typed one-face pairing forward to the enumerated finite-cyclic word. -/
noncomputable def ofOneFaceWordComapPairing
    (word : List (SignedDart Edge))
    (valid : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing) :
    (ofOneFaceWord word).BoundaryPairing := by
  let source := (ofOneFaceWordOccurrenceEquiv word).symm pairing.source
  let target := (ofOneFaceWordOccurrenceEquiv word).symm pairing.target
  have hne : source ≠ target :=
    (ofOneFaceWordOccurrenceEquiv word).symm.injective.ne
      pairing.source_ne_target
  have hcompatible :
      match pairing.direction with
      | .same => target.dart = source.dart
      | .opposite => target.dart = source.dart.flip := by
    cases hdirection : pairing.direction with
    | same =>
        have hp :
            (oneFacePresentation Edge word).occurrenceDart pairing.target =
              (oneFacePresentation Edge word).occurrenceDart pairing.source := by
          simpa only [hdirection] using pairing.compatible
        calc
          target.dart =
              SignedDart.mapEquiv (Fintype.equivFin Edge)
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.target) :=
            (ofOneFaceWordComapOccurrence_dart word pairing.target).symm
          _ = SignedDart.mapEquiv (Fintype.equivFin Edge)
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.source) :=
            congrArg (SignedDart.mapEquiv (Fintype.equivFin Edge)) hp
          _ = source.dart :=
            ofOneFaceWordComapOccurrence_dart word pairing.source
    | opposite =>
        have hp :
            (oneFacePresentation Edge word).occurrenceDart pairing.target =
              (oneFacePresentation Edge word).inv
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.source) := by
          simpa only [hdirection] using pairing.compatible
        change
          (oneFacePresentation Edge word).occurrenceDart pairing.target =
            ((oneFacePresentation Edge word).occurrenceDart
              pairing.source).flip at hp
        calc
          target.dart =
              SignedDart.mapEquiv (Fintype.equivFin Edge)
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.target) :=
            (ofOneFaceWordComapOccurrence_dart word pairing.target).symm
          _ = SignedDart.mapEquiv (Fintype.equivFin Edge)
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.source).flip := by
            exact congrArg
              (SignedDart.mapEquiv (Fintype.equivFin Edge)) hp
          _ = source.dart.flip := by
            rw [SignedDart.mapEquiv_flip,
              ofOneFaceWordComapOccurrence_dart]
  have hedge : target.edge = source.edge := by
    cases hdirection : pairing.direction with
    | same =>
        have hsame : target.dart = source.dart := by
          simpa only [hdirection] using hcompatible
        exact congrArg edgeOfDart hsame
    | opposite =>
        have hopp : target.dart = source.dart.flip := by
          simpa only [hdirection] using hcompatible
        simpa only [BoundaryOccurrence.edge, edgeOfDart_flip] using
          congrArg edgeOfDart hopp
  have hsourceBoundary :
      ¬(ofOneFaceWord word).IsBoundaryEdge source.edge :=
    valid.not_isBoundaryEdge_of_distinct_occurrences source target hne hedge
  have htargetBoundary :
      ¬(ofOneFaceWord word).IsBoundaryEdge target.edge := by
    rw [hedge]
    exact hsourceBoundary
  exact
    { source := source
      target := target
      source_ne_target := hne
      source_not_boundary := hsourceBoundary
      target_not_boundary := htargetBoundary
      direction := pairing.direction
      compatible := hcompatible }

@[simp]
theorem ofOneFaceWordMapPairing_source
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) :
    (ofOneFaceWordMapPairing word pairing).source =
      ofOneFaceWordMapOccurrence word pairing.source :=
  rfl

@[simp]
theorem ofOneFaceWordMapPairing_target
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) :
    (ofOneFaceWordMapPairing word pairing).target =
      ofOneFaceWordMapOccurrence word pairing.target :=
  rfl

@[simp]
theorem ofOneFaceWordMapPairing_direction
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) :
    (ofOneFaceWordMapPairing word pairing).direction = pairing.direction :=
  rfl

@[simp]
theorem ofOneFaceWordComapPairing_source
    (word : List (SignedDart Edge))
    (valid : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing) :
    (ofOneFaceWordComapPairing word valid pairing).source =
      (ofOneFaceWordOccurrenceEquiv word).symm pairing.source :=
  rfl

@[simp]
theorem ofOneFaceWordComapPairing_target
    (word : List (SignedDart Edge))
    (valid : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing) :
    (ofOneFaceWordComapPairing word valid pairing).target =
      (ofOneFaceWordOccurrenceEquiv word).symm pairing.target :=
  rfl

@[simp]
theorem ofOneFaceWordComapPairing_direction
    (word : List (SignedDart Edge))
    (valid : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing) :
    (ofOneFaceWordComapPairing word valid pairing).direction =
      pairing.direction :=
  rfl

theorem ofOneFaceWordPreHomeomorph_pairing_source_point
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) (t : unitInterval) :
    ofOneFaceWordPreHomeomorph word
        (pairing.identification.source.point t) =
      (ofOneFaceWordMapPairing word pairing).identification.source.point t := by
  exact ofOneFaceWordPreHomeomorph_occurrenceSide_point
    word pairing.source t

theorem ofOneFaceWordPreHomeomorph_pairing_target_point
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) (t : unitInterval) :
    ofOneFaceWordPreHomeomorph word
        (pairing.identification.target.point t) =
      (ofOneFaceWordMapPairing word pairing).identification.target.point t := by
  exact ofOneFaceWordPreHomeomorph_occurrenceSide_point
    word pairing.target t

theorem ofOneFaceWordPreHomeomorph_pairing_parameter_point
    (word : List (SignedDart Edge))
    (pairing : (ofOneFaceWord word).BoundaryPairing) (t : unitInterval) :
    ofOneFaceWordPreHomeomorph word
        (pairing.identification.target.point
          (pairing.identification.parameter t)) =
      (ofOneFaceWordMapPairing word pairing).identification.target.point
        ((ofOneFaceWordMapPairing word pairing).identification.parameter t) := by
  rw [ofOneFaceWordPreHomeomorph_pairing_target_point]
  rfl

theorem ofOneFaceWordPreHomeomorph_generator_related
    (word : List (SignedDart Edge))
    (_validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (validTyped :
      (oneFacePresentation Edge word).OccurrencePairingValid)
    (pairing : (ofOneFaceWord word).BoundaryPairing)
    (t : unitInterval) :
    (oneFacePresentation Edge word).PolygonalGluingRel validTyped
      (ofOneFaceWordPreHomeomorph word
        (pairing.identification.source.point t))
      (ofOneFaceWordPreHomeomorph word
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [ofOneFaceWordPreHomeomorph_pairing_source_point,
    ofOneFaceWordPreHomeomorph_pairing_parameter_point]
  exact PolygonGluing.related_of_mem
    (ofOneFaceWordMapPairing word pairing).identification
    (SurfaceCellComplex.pairing_identification_mem validTyped
      (ofOneFaceWordMapPairing word pairing)) t

/-- The enumeration pre-homeomorphism maps the complete finite-cyclic gluing relation into the
typed one-face gluing relation. -/
theorem ofOneFaceWordPreHomeomorph_related
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (validTyped :
      (oneFacePresentation Edge word).OccurrencePairingValid)
    {x y : (ofOneFaceWord word).PolygonalPreRealization}
    (hxy :
      (ofOneFaceWord word).PolygonalGluingRel validFinite x y) :
    (oneFacePresentation Edge word).PolygonalGluingRel validTyped
      (ofOneFaceWordPreHomeomorph word x)
      (ofOneFaceWordPreHomeomorph word y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      ((ofOneFaceWord word).polygonalIdentifications validFinite)) x y at hxy
  induction hxy with
  | rel x y hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact ofOneFaceWordPreHomeomorph_generator_related
            word validFinite validTyped pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem ofOneFaceWordPreHomeomorph_symm_occurrenceSide_point
    (word : List (SignedDart Edge))
    (o : (oneFacePresentation Edge word).BoundaryOccurrence)
    (t : unitInterval) :
    (ofOneFaceWordPreHomeomorph word).symm
        (((oneFacePresentation Edge word).occurrenceSide o).point t) =
      ((ofOneFaceWord word).occurrenceSide
        ((ofOneFaceWordOccurrenceEquiv word).symm o)).point t := by
  apply (ofOneFaceWordPreHomeomorph word).injective
  rw [(ofOneFaceWordPreHomeomorph word).apply_symm_apply]
  rw [ofOneFaceWordPreHomeomorph_occurrenceSide_point]
  rw [ofOneFaceWordMapOccurrence_comap]

theorem ofOneFaceWordPreHomeomorph_symm_pairing_source_point
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing)
    (t : unitInterval) :
    (ofOneFaceWordPreHomeomorph word).symm
        (pairing.identification.source.point t) =
      (ofOneFaceWordComapPairing word validFinite pairing).identification.source.point t := by
  exact ofOneFaceWordPreHomeomorph_symm_occurrenceSide_point
    word pairing.source t

theorem ofOneFaceWordPreHomeomorph_symm_pairing_target_point
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing)
    (t : unitInterval) :
    (ofOneFaceWordPreHomeomorph word).symm
        (pairing.identification.target.point t) =
      (ofOneFaceWordComapPairing word validFinite pairing).identification.target.point t := by
  exact ofOneFaceWordPreHomeomorph_symm_occurrenceSide_point
    word pairing.target t

theorem ofOneFaceWordPreHomeomorph_symm_pairing_parameter_point
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing)
    (t : unitInterval) :
    (ofOneFaceWordPreHomeomorph word).symm
        (pairing.identification.target.point
          (pairing.identification.parameter t)) =
      (ofOneFaceWordComapPairing word validFinite pairing).identification.target.point
        ((ofOneFaceWordComapPairing word validFinite pairing).identification.parameter t) := by
  rw [ofOneFaceWordPreHomeomorph_symm_pairing_target_point]
  rfl

theorem ofOneFaceWordPreHomeomorph_symm_generator_related
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (_validTyped :
      (oneFacePresentation Edge word).OccurrencePairingValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing)
    (t : unitInterval) :
    (ofOneFaceWord word).PolygonalGluingRel validFinite
      ((ofOneFaceWordPreHomeomorph word).symm
        (pairing.identification.source.point t))
      ((ofOneFaceWordPreHomeomorph word).symm
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [ofOneFaceWordPreHomeomorph_symm_pairing_source_point,
    ofOneFaceWordPreHomeomorph_symm_pairing_parameter_point]
  exact PolygonGluing.related_of_mem
    (ofOneFaceWordComapPairing word validFinite pairing).identification
    (pairing_identification_mem validFinite
      (ofOneFaceWordComapPairing word validFinite pairing)) t

/-- The inverse enumeration pre-homeomorphism maps the complete typed gluing relation back into
the finite-cyclic gluing relation. -/
theorem ofOneFaceWordPreHomeomorph_symm_related
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (validTyped :
      (oneFacePresentation Edge word).OccurrencePairingValid)
    {x y : (oneFacePresentation Edge word).PolygonalPreRealization}
    (hxy :
      (oneFacePresentation Edge word).PolygonalGluingRel validTyped x y) :
    (ofOneFaceWord word).PolygonalGluingRel validFinite
      ((ofOneFaceWordPreHomeomorph word).symm x)
      ((ofOneFaceWordPreHomeomorph word).symm y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      ((oneFacePresentation Edge word).polygonalIdentifications validTyped)) x y at hxy
  induction hxy with
  | rel x y hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact ofOneFaceWordPreHomeomorph_symm_generator_related
            word validFinite validTyped pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem ofOneFaceWordPreHomeomorph_related_iff
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (validTyped :
      (oneFacePresentation Edge word).OccurrencePairingValid)
    (x y : (ofOneFaceWord word).PolygonalPreRealization) :
    (ofOneFaceWord word).PolygonalGluingRel validFinite x y ↔
      (oneFacePresentation Edge word).PolygonalGluingRel validTyped
        (ofOneFaceWordPreHomeomorph word x)
        (ofOneFaceWordPreHomeomorph word y) := by
  constructor
  · exact ofOneFaceWordPreHomeomorph_related
      word validFinite validTyped
  · intro hxy
    simpa only [(ofOneFaceWordPreHomeomorph word).symm_apply_apply] using
      ofOneFaceWordPreHomeomorph_symm_related
        word validFinite validTyped hxy

/-- Enumerating the edge names of a typed one-face word preserves its faithful polygonal
realization. -/
noncomputable def ofOneFaceWordRealizationHomeomorph
    (word : List (SignedDart Edge))
    (validFinite : (ofOneFaceWord word).IsSurfaceValid)
    (validTyped :
      (oneFacePresentation Edge word).OccurrencePairingValid) :
    (ofOneFaceWord word).PolygonalRealization validFinite ≃ₜ
      (oneFacePresentation Edge word).PolygonalRealization validTyped :=
  PolygonGluing.realizationCongr (ofOneFaceWordPreHomeomorph word)
    (ofOneFaceWordPreHomeomorph_related_iff
      word validFinite validTyped)

end FiniteCyclicPresentation

namespace NormalForm

/-- The admissible canonical orientable finite-cyclic presentation realizes the exact vendored
Lean-Eval quotient. -/
noncomputable def canonicalOrientableRealizationHomeomorph
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) :
    (canonicalPresentation (.orientable p n)).PolygonalRealization
        (canonicalPresentation_isSurfaceValid (.orientable p n) hvalid) ≃ₜ
      Quot (OrientableRel p n) :=
  (FiniteCyclicPresentation.ofOneFaceWordRealizationHomeomorph
      (orientableBoundaryWord p n)
      (canonicalPresentation_isSurfaceValid (.orientable p n) hvalid)
      (orientableCellComplex_occurrencePairingValid hvalid)).trans
    (orientablePolygonalRealizationHomeomorph hvalid)

/-- The admissible canonical nonorientable finite-cyclic presentation realizes the exact vendored
Lean-Eval quotient. -/
noncomputable def canonicalNonOrientableRealizationHomeomorph
    {p n : ℕ} (hp : 1 ≤ p) :
    (canonicalPresentation (.nonOrientable p n)).PolygonalRealization
        (canonicalPresentation_isSurfaceValid (.nonOrientable p n) hp) ≃ₜ
      Quot (NonOrientableRel p n) :=
  (FiniteCyclicPresentation.ofOneFaceWordRealizationHomeomorph
      (nonOrientableBoundaryWord p n)
      (canonicalPresentation_isSurfaceValid (.nonOrientable p n) hp)
      (nonOrientableCellComplex_occurrencePairingValid hp)).trans
    (nonOrientablePolygonalRealizationHomeomorph hp)

end NormalForm

end LeanEval.Topology.ClassificationOfSurfaces
