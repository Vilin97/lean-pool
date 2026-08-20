/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicSignedRealization
import Mathlib.Data.Fin.Rev

/-!
# Polygonal realization under independently reoriented faces

Gallier--Xu treat a face and the same face read in the opposite direction interchangeably. This
file records that convention explicitly. An `UnorientedPresentationIso` may rename and reorient
edges, relabel faces, cyclically rotate their boundaries, and independently reverse the traversal
orientation of every face.

Unlike `SignedPresentationIso`, this broader comparison does not claim to preserve the current
orientation-sensitive `IsSurfaceValid` predicate. When both endpoints are ordinarily valid, it
does preserve their faithful polygonal realizations. This is the exact extra comparison needed by
the cross-cap pseudo-rewrite, whose common P2 refinement reads one of its two faces backwards.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex
open scoped ComplexConjugate

namespace PolygonCell

/-- Reflection of a polygon cell across the real axis. -/
noncomputable def reflectionHomeomorph (n : ℕ) : PolygonCell n ≃ₜ PolygonCell n where
  toFun z := ⟨conj z.val, by
    simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero, Complex.norm_conj]
      using z.property⟩
  invFun z := ⟨conj z.val, by
    simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero, Complex.norm_conj]
      using z.property⟩
  left_inv z := by
    apply PolygonCell.ext
    exact Complex.conj_conj z.val
  right_inv z := by
    apply PolygonCell.ext
    exact Complex.conj_conj z.val
  continuous_toFun :=
    continuous_induced_rng.2 (Complex.continuous_conj.comp PolygonCell.continuous_val)
  continuous_invFun :=
    continuous_induced_rng.2 (Complex.continuous_conj.comp PolygonCell.continuous_val)

@[simp]
theorem reflectionHomeomorph_apply (n : ℕ) (z : PolygonCell n) :
    (reflectionHomeomorph n z).val = conj z.val :=
  rfl

/-- Reflection reverses both the cyclic side index and its interval parameter. -/
theorem reflectionHomeomorph_side {n : ℕ} (i : Fin n) (t : unitInterval) :
    reflectionHomeomorph n (side i t) =
      side i.rev (unitInterval.symm t) := by
  apply PolygonCell.ext
  change conj (Circle.exp (sideAngle i t) : ℂ) =
    (Circle.exp (sideAngle i.rev (unitInterval.symm t)) : Circle)
  rw [← Circle.coe_inv_eq_conj, ← Circle.exp_neg]
  apply congrArg (fun z : Circle ↦ (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨-1, ?_⟩
  simp only [sideAngle, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
    unitInterval.coe_symm_eq]
  rw [show i.rev.val = n - (i.val + 1) from rfl]
  rw [Nat.cast_sub (Nat.succ_le_iff.mpr i.isLt)]
  push_cast
  field_simp [Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)]
  ring

end PolygonCell

namespace FiniteCyclicPresentation

@[simp] private theorem finCast_self {n : ℕ} (h : n = n) (i : Fin n) :
    Fin.cast h i = i := by
  apply Fin.ext
  rfl

open SurfaceCellComplex

/-- Presentation isomorphism up to independent choices of traversal orientation on target
faces. -/
structure UnorientedPresentationIso (P Q : FiniteCyclicPresentation) where
  /-- The `edgeRelabeling` declaration. -/
  edgeRelabeling : EdgeRelabeling P.Edge Q.Edge
  /-- The `faceEquiv` declaration. -/
  faceEquiv : P.Face ≃ Q.Face
  /-- The `reverseFace` declaration. -/
  reverseFace : P.Face → Bool
  boundary_rotated :
    ∀ f, ((P.boundary f).map edgeRelabeling.mapDart).IsRotated
      (Q.orientedBoundary ⟨faceEquiv f, reverseFace f⟩)

namespace UnorientedPresentationIso

variable {P Q : FiniteCyclicPresentation}

/-- The `edgeEquiv` declaration. -/
abbrev edgeEquiv (e : UnorientedPresentationIso P Q) : P.Edge ≃ Q.Edge :=
  e.edgeRelabeling.edgeEquiv

/-- Ordinary signed presentation isomorphisms are the orientation-preserving special case. -/
def ofSignedPresentationIso (e : SignedPresentationIso P Q) :
    UnorientedPresentationIso P Q where
  edgeRelabeling := e.edgeRelabeling
  faceEquiv := e.faceEquiv
  reverseFace := fun _ ↦ false
  boundary_rotated := by
    intro f
    exact e.boundary_rotated f

/-- Corresponding stored boundaries have the same length. -/
theorem boundary_length_eq (e : UnorientedPresentationIso P Q) (f : P.Face) :
    (P.boundary f).length = (Q.boundary (e.faceEquiv f)).length := by
  rw [← Q.orientedBoundary_length
    (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)]
  simpa only [List.length_map] using
    (e.boundary_rotated f).perm.length_eq

/-- Independent face reversal does not alter edge multiplicity in a corresponding face. -/
theorem faceEdgeMultiplicity_eq (e : UnorientedPresentationIso P Q)
    (f : P.Face) (a : P.Edge) :
    P.faceEdgeMultiplicity f a =
      Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := by
  have h := (e.boundary_rotated f).map edgeOfDart
  have hcount := h.perm.count_eq (e.edgeEquiv a)
  have horiented :=
    Q.orientedBoundary_edgeMultiplicity
      (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)
      (e.edgeEquiv a)
  have hcount' :
      (((P.boundary f).map edgeOfDart).map e.edgeEquiv).count
          (e.edgeEquiv a) =
        Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := by
    rw [← horiented]
    simpa [List.map_map, Function.comp_def] using hcount
  calc
    P.faceEdgeMultiplicity f a =
        (((P.boundary f).map edgeOfDart).map e.edgeEquiv).count
          (e.edgeEquiv a) := by
      symm
      exact List.count_map_of_injective _ e.edgeEquiv e.edgeEquiv.injective a
    _ = Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := hcount'

/-- Total edge multiplicities are invariant under an unoriented presentation isomorphism. -/
theorem edgeMultiplicity_eq (e : UnorientedPresentationIso P Q) (a : P.Edge) :
    P.edgeMultiplicity a = Q.edgeMultiplicity (e.edgeEquiv a) := by
  unfold edgeMultiplicity
  exact Fintype.sum_equiv e.faceEquiv _ _ fun f ↦ e.faceEdgeMultiplicity_eq f a

theorem isBoundaryEdge_iff (e : UnorientedPresentationIso P Q) (a : P.Edge) :
    P.IsBoundaryEdge a ↔ Q.IsBoundaryEdge (e.edgeEquiv a) := by
  unfold IsBoundaryEdge
  rw [e.edgeMultiplicity_eq]

/-- Face adjacency is preserved when target faces may be read in either orientation. -/
theorem map_faceAdjacent (e : UnorientedPresentationIso P Q)
    {f g : P.Face} (h : P.FaceAdjacent f g) :
    Q.FaceAdjacent (e.faceEquiv f) (e.faceEquiv g) := by
  rcases h with ⟨a, hfa, hga⟩
  refine ⟨e.edgeEquiv a, ?_, ?_⟩
  · apply List.count_pos_iff.mp
    change 0 < Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a)
    rw [← e.faceEdgeMultiplicity_eq f a]
    exact List.count_pos_iff.mpr hfa
  · apply List.count_pos_iff.mp
    change 0 < Q.faceEdgeMultiplicity (e.faceEquiv g) (e.edgeEquiv a)
    rw [← e.faceEdgeMultiplicity_eq g a]
    exact List.count_pos_iff.mpr hga

/-- Face-incidence connectivity is preserved by an unoriented presentation isomorphism. -/
theorem isConnected (e : UnorientedPresentationIso P Q)
    (h : P.IsConnected) : Q.IsConnected := by
  refine ⟨e.faceEquiv.nonempty_congr.mp h.1, ?_⟩
  intro q r
  have hchain := h.2 (e.faceEquiv.symm q) (e.faceEquiv.symm r)
  have hmapped :=
    hchain.lift e.faceEquiv fun _ _ hadj ↦ e.map_faceAdjacent hadj
  change Relation.ReflTransGen Q.FaceAdjacent
    (e.faceEquiv (e.faceEquiv.symm q))
      (e.faceEquiv (e.faceEquiv.symm r)) at hmapped
  simpa only [e.faceEquiv.apply_symm_apply] using hmapped

/-- Looking up the reversed signed word reverses the finite index and flips the dart. -/
theorem inverseWord_get_rev {α : Type*}
    (word : List (SignedDart α)) (i : Fin word.length) :
    (inverseWord word).get
        ⟨i.val, by simpa only [inverseWord_length] using i.isLt⟩ =
      (word.get i.rev).flip := by
  simp [inverseWord]
  congr 2
  omega

/-- The target-boundary rotation selected for an unoriented presentation isomorphism. -/
noncomputable def faceRotation (e : UnorientedPresentationIso P Q) (f : P.Face) : ℕ :=
  Classical.choose (e.boundary_rotated f).symm

theorem rotate_target_orientedBoundary
    (e : UnorientedPresentationIso P Q) (f : P.Face) :
    (Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩).rotate
        (e.faceRotation f) =
      (P.boundary f).map e.edgeRelabeling.mapDart :=
  Classical.choose_spec (e.boundary_rotated f).symm

/-- The side index in the chosen orientation of the target face. -/
noncomputable abbrev orientedSideIndex
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) (i : Fin (P.boundary f).length) :
    Fin (Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩).length := by
  have hpos : 0 <
      (Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩).length := by
    rw [Q.orientedBoundary_length]
    exact List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f))
  exact ⟨(i.val + e.faceRotation f) %
    (Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩).length,
      Nat.mod_lt _ hpos⟩

/-- Convert an oriented target-side index to the stored boundary indexing. -/
noncomputable abbrev sideIndex
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) (i : Fin (P.boundary f).length) :
    Fin (Q.boundary (e.faceEquiv f)).length :=
  let j := (e.orientedSideIndex validQ f i).cast
    (Q.orientedBoundary_length
      (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace))
  if e.reverseFace f then j.rev else j

/-- Reflection reverses the side parameter exactly when the target face is read backwards. -/
def sideParameter (e : UnorientedPresentationIso P Q)
    (f : P.Face) (t : unitInterval) : unitInterval :=
  if e.reverseFace f then unitInterval.symm t else t

@[simp]
theorem sideParameter_false (e : UnorientedPresentationIso P Q)
    (f : P.Face) (h : e.reverseFace f = false) (t : unitInterval) :
    e.sideParameter f t = t := by
  simp [sideParameter, h]

@[simp]
theorem sideParameter_true (e : UnorientedPresentationIso P Q)
    (f : P.Face) (h : e.reverseFace f = true) (t : unitInterval) :
    e.sideParameter f t = unitInterval.symm t := by
  simp [sideParameter, h]

@[simp]
theorem sideParameter_sideParameter
    (e : UnorientedPresentationIso P Q) (f : P.Face) (t : unitInterval) :
    e.sideParameter f (e.sideParameter f t) = t := by
  cases h : e.reverseFace f <;>
    simp [sideParameter, h, unitInterval.symm_symm]

/-- The rotated oriented target side carries the relabeled source dart. -/
theorem orientedBoundary_get_orientedSideIndex
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) (i : Fin (P.boundary f).length) :
    (Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩).get
        (e.orientedSideIndex validQ f i) =
      e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
  let target :=
    Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩
  let mapped := (P.boundary f).map e.edgeRelabeling.mapDart
  have hrot : target.rotate (e.faceRotation f) = mapped :=
    e.rotate_target_orientedBoundary f
  have hlen : target.length = mapped.length := by
    rw [← hrot, List.length_rotate]
  have hiTarget : i.val < target.length := by
    rw [hlen]
    simpa only [mapped, List.length_map] using i.isLt
  have hpoint :
      (target.rotate (e.faceRotation f))[i.val]? = mapped[i.val]? :=
    congrArg (fun word => word[i.val]?) hrot
  rw [List.getElem?_rotate hiTarget] at hpoint
  have hmapped :
      mapped[i.val]? =
        some (e.edgeRelabeling.mapDart ((P.boundary f).get i)) := by
    simp [mapped, i.isLt]
  rw [hmapped] at hpoint
  rw [← Option.some_inj, ← hpoint]
  simp [orientedSideIndex, target]

/-- The stored target occurrence carries the relabeled dart, flipped exactly when its face was
read backwards. -/
theorem boundary_get_sideIndex
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) (i : Fin (P.boundary f).length) :
    (Q.boundary (e.faceEquiv f)).get (e.sideIndex validQ f i) =
      if e.reverseFace f then
        (e.edgeRelabeling.mapDart ((P.boundary f).get i)).flip
      else
        e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
  have horiented := e.orientedBoundary_get_orientedSideIndex validQ f i
  cases hreverse : e.reverseFace f
  · simpa [sideIndex, hreverse, orientedBoundary] using horiented
  · let target := inverseWord (Q.boundary (e.faceEquiv f))
    let mapped := (P.boundary f).map e.edgeRelabeling.mapDart
    have hrot : target.rotate (e.faceRotation f) = mapped := by
      simpa only [target, mapped, hreverse, orientedBoundary, if_true] using
        e.rotate_target_orientedBoundary f
    have hlen : target.length = mapped.length := by
      rw [← hrot, List.length_rotate]
    have hiTarget : i.val < target.length := by
      rw [hlen]
      simpa only [mapped, List.length_map] using i.isLt
    let jTarget : Fin target.length :=
      ⟨(i.val + e.faceRotation f) % target.length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt hiTarget)⟩
    have hpoint :
        (target.rotate (e.faceRotation f))[i.val]? = mapped[i.val]? :=
      congrArg (fun word => word[i.val]?) hrot
    rw [List.getElem?_rotate hiTarget] at hpoint
    have horiented' :
        target.get jTarget =
          e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
      have htargetSome :
          target[jTarget.val]? = some (target.get jTarget) := by
        simp [jTarget.isLt]
      have hmappedSome :
          mapped[i.val]? =
            some (e.edgeRelabeling.mapDart ((P.boundary f).get i)) := by
        simp [mapped, i.isLt]
      rw [hmappedSome] at hpoint
      exact Option.some.inj (htargetSome.symm.trans hpoint)
    let j : Fin (Q.boundary (e.faceEquiv f)).length :=
      jTarget.cast (by simp only [target, inverseWord_length])
    have hinverse :=
      inverseWord_get_rev (Q.boundary (e.faceEquiv f)) j
    have hindex :
        (⟨j.val, by simpa only [inverseWord_length] using j.isLt⟩ :
            Fin (inverseWord (Q.boundary (e.faceEquiv f))).length) =
          jTarget := by
      apply Fin.ext
      rfl
    rw [hindex] at hinverse
    have hflipped :=
      congrArg SignedDart.flip (hinverse.symm.trans horiented')
    have hside : e.sideIndex validQ f i = j.rev := by
      apply Fin.ext
      simp [sideIndex, orientedSideIndex, hreverse, j, jTarget, target]
    rw [hside]
    simpa using hflipped

/-- The facewise disk homeomorphism: rotate to the selected cyclic spelling, then reflect if the
target face is read backwards. -/
noncomputable def faceHomeomorph
    (e : UnorientedPresentationIso P Q) (f : P.Face) :
    PolygonCell (P.boundary f).length ≃ₜ
      PolygonCell (Q.boundary (e.faceEquiv f)).length :=
  let rotation :=
    PolygonCell.rotateHomeomorph (e.boundary_length_eq f) (e.faceRotation f)
  if e.reverseFace f then
    rotation.trans
      (PolygonCell.reflectionHomeomorph
        (Q.boundary (e.faceEquiv f)).length)
  else
    rotation

/-- The facewise homeomorphism sends a source side to the corresponding stored target side, with
the interval parameter reversed exactly for a reversed face. -/
theorem faceHomeomorph_side
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) (i : Fin (P.boundary f).length) (t : unitInterval) :
    e.faceHomeomorph f (PolygonCell.side i t) =
      PolygonCell.side (e.sideIndex validQ f i) (e.sideParameter f t) := by
  cases hreverse : e.reverseFace f
  · simp only [faceHomeomorph, hreverse, Bool.false_eq_true, ↓reduceIte,
      sideIndex, sideParameter]
    have hindex :
        (e.orientedSideIndex validQ f i).cast
            (Q.orientedBoundary_length
              (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)) =
          (⟨(i.val + e.faceRotation f) %
              (Q.boundary (e.faceEquiv f)).length,
            Nat.mod_lt _
              (List.length_pos_of_ne_nil
                (validQ.2.1 (e.faceEquiv f)))⟩ :
            Fin (Q.boundary (e.faceEquiv f)).length) := by
      apply Fin.ext
      simp [orientedSideIndex, hreverse, orientedBoundary]
    rw [hindex]
    exact PolygonCell.rotateHomeomorph_side_of_eq
      (e.boundary_length_eq f)
      (List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f)))
      (e.faceRotation f) i t
  · simp only [faceHomeomorph, hreverse, ↓reduceIte, Homeomorph.trans_apply,
      sideIndex, sideParameter]
    have hindex :
        (e.orientedSideIndex validQ f i).cast
            (Q.orientedBoundary_length
              (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)) =
          (⟨(i.val + e.faceRotation f) %
              (Q.boundary (e.faceEquiv f)).length,
            Nat.mod_lt _
              (List.length_pos_of_ne_nil
                (validQ.2.1 (e.faceEquiv f)))⟩ :
            Fin (Q.boundary (e.faceEquiv f)).length) := by
      apply Fin.ext
      simp [orientedSideIndex, hreverse, orientedBoundary]
    rw [hindex]
    rw [PolygonCell.rotateHomeomorph_side_of_eq
      (e.boundary_length_eq f)
      (List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f)))
      (e.faceRotation f) i t]
    exact PolygonCell.reflectionHomeomorph_side _ _

/-- A facewise homeomorphism of polygonal pre-realizations. -/
noncomputable def preHomeomorph (e : UnorientedPresentationIso P Q) :
    P.PolygonalPreRealization ≃ₜ Q.PolygonalPreRealization :=
  (IsHomeomorph.sigmaMap e.faceEquiv.bijective
      (fun f => (e.faceHomeomorph f).isHomeomorph)).homeomorph
    (Sigma.map e.faceEquiv fun f => e.faceHomeomorph f)

@[simp]
theorem preHomeomorph_apply_fst (e : UnorientedPresentationIso P Q)
    (x : P.PolygonalPreRealization) :
    (e.preHomeomorph x).1 = e.faceEquiv x.1 :=
  rfl

@[simp]
theorem preHomeomorph_apply_snd (e : UnorientedPresentationIso P Q)
    (x : P.PolygonalPreRealization) :
    (e.preHomeomorph x).2 = e.faceHomeomorph x.1 x.2 :=
  rfl

/-- Transport a boundary occurrence through the selected cyclic rotation and possible
reflection. -/
noncomputable def mapOccurrence
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid) :
    P.BoundaryOccurrence → Q.BoundaryOccurrence
  | ⟨f, i⟩ => ⟨e.faceEquiv f, e.sideIndex validQ f i⟩

@[simp]
theorem mapOccurrence_fst
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).1 = e.faceEquiv o.1 := by
  cases o
  rfl

@[simp]
theorem mapOccurrence_dart
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).dart =
      if e.reverseFace o.1 then
        (e.edgeRelabeling.mapDart o.dart).flip
      else
        e.edgeRelabeling.mapDart o.dart := by
  rcases o with ⟨f, i⟩
  exact e.boundary_get_sideIndex validQ f i

/-- On a labelled side, the pre-realization map performs its selected cyclic shift and possible
reflection. -/
theorem preHomeomorph_occurrenceSide_point
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (t : unitInterval) :
    e.preHomeomorph ((P.occurrenceSide o).point t) =
      (Q.occurrenceSide (e.mapOccurrence validQ o)).point
        (e.sideParameter o.1 t) := by
  rcases o with ⟨f, i⟩
  apply Sigma.ext
  · rfl
  · simp only [preHomeomorph_apply_snd, PolygonGluing.Side.point]
    apply heq_of_eq
    exact e.faceHomeomorph_side validQ f i t

/-- Cyclic shift followed by an optional finite-index reversal is injective. -/
private theorem sideIndex_injective
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (f : P.Face) :
    Function.Injective (e.sideIndex validQ f) := by
  have horiented :
      Function.Injective (e.orientedSideIndex validQ f) := by
    intro i j hij
    let target :=
      Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩
    have hlen : (P.boundary f).length = target.length := by
      simpa only [target, Q.orientedBoundary_length] using e.boundary_length_eq f
    have hmod :
        i.val + e.faceRotation f ≡ j.val + e.faceRotation f
          [MOD target.length] := by
      exact congrArg Fin.val hij
    have hcancel :
        i.val ≡ j.val [MOD target.length] :=
      Nat.ModEq.add_right_cancel' (e.faceRotation f) hmod
    apply Fin.ext
    unfold Nat.ModEq at hcancel
    rw [← hlen, Nat.mod_eq_of_lt i.isLt,
      Nat.mod_eq_of_lt j.isLt] at hcancel
    exact hcancel
  intro i j hij
  apply horiented
  have hcast :
      (e.orientedSideIndex validQ f i).cast
          (Q.orientedBoundary_length
            (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)) =
        (e.orientedSideIndex validQ f j).cast
          (Q.orientedBoundary_length
            (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)) := by
    by_cases hreverse : e.reverseFace f = true
    · have hrev :
        ((e.orientedSideIndex validQ f i).cast
            (Q.orientedBoundary_length
              (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace))).rev =
          ((e.orientedSideIndex validQ f j).cast
            (Q.orientedBoundary_length
              (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace))).rev := by
        simpa only [sideIndex, if_pos hreverse] using hij
      exact Fin.rev_injective hrev
    · simpa only [sideIndex, if_neg hreverse] using hij
  exact Fin.cast_injective
    (Q.orientedBoundary_length
      (⟨e.faceEquiv f, e.reverseFace f⟩ : Q.OrientedFace)) hcast

/-- Transport of all boundary occurrences is injective. -/
theorem mapOccurrence_injective
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid) :
    Function.Injective (e.mapOccurrence validQ) := by
  rintro ⟨f, i⟩ ⟨g, j⟩ h
  have hface : f = g := by
    apply e.faceEquiv.injective
    exact congrArg Sigma.fst h
  subst g
  have hindex : i = j := by
    apply e.sideIndex_injective validQ f
    exact eq_of_heq ((Sigma.ext_iff.mp h).2)
  subst j
  rfl

@[simp]
theorem mapOccurrence_edge
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).edge = e.edgeEquiv o.edge := by
  change edgeOfDart (e.mapOccurrence validQ o).dart =
    e.edgeEquiv (edgeOfDart o.dart)
  rw [e.mapOccurrence_dart]
  cases e.reverseFace o.1 <;>
    simp [EdgeRelabeling.edgeOfDart_mapDart, edgeOfDart_flip]

/-- Ignoring the selected cyclic shifts and reflections, the occurrence types have equal
cardinality. -/
noncomputable def rawOccurrenceEquiv (e : UnorientedPresentationIso P Q) :
    P.BoundaryOccurrence ≃ Q.BoundaryOccurrence :=
  Equiv.sigmaCongr e.faceEquiv fun f =>
    (Fin.castOrderIso (e.boundary_length_eq f)).toEquiv

/-- Boundary-occurrence transport bundled as an equivalence. -/
noncomputable def occurrenceEquiv
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid) :
    P.BoundaryOccurrence ≃ Q.BoundaryOccurrence :=
  Equiv.ofBijective (e.mapOccurrence validQ)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨e.mapOccurrence_injective validQ,
        Fintype.card_congr e.rawOccurrenceEquiv⟩)

@[simp]
theorem occurrenceEquiv_apply
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) :
    e.occurrenceEquiv validQ o = e.mapOccurrence validQ o :=
  rfl

@[simp]
theorem mapOccurrence_occurrenceEquiv_symm
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.mapOccurrence validQ ((e.occurrenceEquiv validQ).symm o) = o :=
  (e.occurrenceEquiv validQ).apply_symm_apply o

/-- Toggle a gluing direction when exactly one incident face is reflected. -/
def transportDirection (sourceReverse targetReverse : Bool) :
    PolygonGluing.ParameterDirection → PolygonGluing.ParameterDirection
  | .same =>
      if sourceReverse = targetReverse then .same else .opposite
  | .opposite =>
      if sourceReverse = targetReverse then .opposite else .same

/-- The transported gluing parameter commutes with the two optional side reflections. -/
theorem transportDirection_parameter
    (sourceReverse targetReverse : Bool)
    (direction : PolygonGluing.ParameterDirection) (t : unitInterval) :
    (transportDirection sourceReverse targetReverse direction).homeomorph
        (if sourceReverse then unitInterval.symm t else t) =
      if targetReverse then
        unitInterval.symm (direction.homeomorph t)
      else
        direction.homeomorph t := by
  cases sourceReverse <;> cases targetReverse <;> cases direction <;>
    simp [transportDirection, PolygonGluing.ParameterDirection.homeomorph_opposite_apply,
      unitInterval.symm_symm]

/-- Transport a compatible source pairing, toggling its parameter direction precisely when one
of the two incident faces is reflected. -/
noncomputable def mapPairing
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) : Q.BoundaryPairing where
  source := e.mapOccurrence validQ pairing.source
  target := e.mapOccurrence validQ pairing.target
  source_ne_target :=
    (e.mapOccurrence_injective validQ).ne pairing.source_ne_target
  source_not_boundary := by
    rw [e.mapOccurrence_edge]
    exact (e.isBoundaryEdge_iff pairing.source.edge).not.mp
      pairing.source_not_boundary
  target_not_boundary := by
    rw [e.mapOccurrence_edge]
    exact (e.isBoundaryEdge_iff pairing.target.edge).not.mp
      pairing.target_not_boundary
  direction := transportDirection
    (e.reverseFace pairing.source.1)
    (e.reverseFace pairing.target.1)
    pairing.direction
  compatible := by
    rw [e.mapOccurrence_dart, e.mapOccurrence_dart]
    cases hs : e.reverseFace pairing.source.1 <;>
      cases ht : e.reverseFace pairing.target.1 <;>
        cases hd : pairing.direction
    all_goals
      have hcompatible := pairing.compatible
      simp only [hd] at hcompatible
      simp only [↓reduceIte, transportDirection,
        Bool.false_eq_true, Bool.true_eq_false,
        SignedDart.flip_flip]
      first
      | simpa only [EdgeRelabeling.mapDart_flip,
          SignedDart.flip_flip] using
          congrArg e.edgeRelabeling.mapDart hcompatible
      | simpa only [EdgeRelabeling.mapDart_flip,
          SignedDart.flip_flip] using
          congrArg SignedDart.flip
            (congrArg e.edgeRelabeling.mapDart hcompatible)

@[simp]
theorem mapPairing_source
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).source =
      e.mapOccurrence validQ pairing.source :=
  rfl

@[simp]
theorem mapPairing_target
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).target =
      e.mapOccurrence validQ pairing.target :=
  rfl

@[simp]
theorem mapPairing_direction
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).direction =
      transportDirection
        (e.reverseFace pairing.source.1)
        (e.reverseFace pairing.target.1)
        pairing.direction :=
  rfl

/-- The pre-realization map sends a pairing source point to its transported source side. -/
theorem preHomeomorph_pairing_source_point
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph (pairing.identification.source.point t) =
      (e.mapPairing validQ pairing).identification.source.point
        (e.sideParameter pairing.source.1 t) := by
  exact e.preHomeomorph_occurrenceSide_point validQ pairing.source t

/-- The pre-realization map sends a pairing target point to its transported target side. -/
theorem preHomeomorph_pairing_target_point
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph (pairing.identification.target.point t) =
      (e.mapPairing validQ pairing).identification.target.point
        (e.sideParameter pairing.target.1 t) := by
  exact e.preHomeomorph_occurrenceSide_point validQ pairing.target t

/-- Transported side parameters intertwine the source and target pairing maps. -/
theorem mapPairing_parameter_sideParameter
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    (e.mapPairing validQ pairing).identification.parameter
        (e.sideParameter pairing.source.1 t) =
      e.sideParameter pairing.target.1
        (pairing.identification.parameter t) := by
  exact transportDirection_parameter
    (e.reverseFace pairing.source.1)
    (e.reverseFace pairing.target.1)
    pairing.direction t

/-- The facewise homeomorphism sends every source generator into the target generated
relation. -/
theorem preHomeomorph_generator_related
    (e : UnorientedPresentationIso P Q) (_validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing)
    (t : unitInterval) :
    Q.PolygonalGluingRel validQ
      (e.preHomeomorph (pairing.identification.source.point t))
      (e.preHomeomorph
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [e.preHomeomorph_pairing_source_point,
    e.preHomeomorph_pairing_target_point,
    ← e.mapPairing_parameter_sideParameter]
  exact PolygonGluing.related_of_mem
    (e.mapPairing validQ pairing).identification
    (pairing_identification_mem validQ (e.mapPairing validQ pairing))
    (e.sideParameter pairing.source.1 t)

/-- The facewise homeomorphism preserves the generated gluing relation. -/
theorem preHomeomorph_related
    (e : UnorientedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) {x y : P.PolygonalPreRealization}
    (hxy : P.PolygonalGluingRel validP x y) :
    Q.PolygonalGluingRel validQ (e.preHomeomorph x) (e.preHomeomorph y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator (P.polygonalIdentifications validP)) x y at hxy
  induction hxy with
  | rel x y hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact e.preHomeomorph_generator_related validP validQ pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The inverse pre-realization homeomorphism uses the same involutive side-parameter
reflection. -/
theorem preHomeomorph_symm_occurrenceSide_point
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) (t : unitInterval) :
    e.preHomeomorph.symm ((Q.occurrenceSide o).point t) =
      (P.occurrenceSide ((e.occurrenceEquiv validQ).symm o)).point
        (e.sideParameter ((e.occurrenceEquiv validQ).symm o).1 t) := by
  apply e.preHomeomorph.injective
  rw [e.preHomeomorph.apply_symm_apply]
  rw [e.preHomeomorph_occurrenceSide_point validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]
  rw [e.sideParameter_sideParameter]

/-- The relabeled dart of a pulled-back occurrence is the target dart, flipped exactly when its
source face was reflected. -/
theorem occurrenceEquiv_symm_mapDart
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.edgeRelabeling.mapDart ((e.occurrenceEquiv validQ).symm o).dart =
      if e.reverseFace ((e.occurrenceEquiv validQ).symm o).1 then
        o.dart.flip
      else
        o.dart := by
  let p := (e.occurrenceEquiv validQ).symm o
  have hdart := e.mapOccurrence_dart validQ p
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ] at hdart
  cases hreverse : e.reverseFace p.1
  · simpa [p, hreverse] using hdart.symm
  · have hflipped := congrArg SignedDart.flip hdart.symm
    simpa [p, hreverse] using hflipped

/-- The relabeled edge of a pulled-back occurrence is its target edge. -/
theorem occurrenceEquiv_symm_edge
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.edgeEquiv ((e.occurrenceEquiv validQ).symm o).edge = o.edge := by
  rw [← e.mapOccurrence_edge validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]

/-- Pull a compatible target pairing back through the occurrence equivalence. -/
noncomputable def comapPairing
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) : P.BoundaryPairing where
  source := (e.occurrenceEquiv validQ).symm pairing.source
  target := (e.occurrenceEquiv validQ).symm pairing.target
  source_ne_target :=
    (e.occurrenceEquiv validQ).symm.injective.ne pairing.source_ne_target
  source_not_boundary := by
    apply (e.isBoundaryEdge_iff
      ((e.occurrenceEquiv validQ).symm pairing.source).edge).not.mpr
    rw [e.occurrenceEquiv_symm_edge validQ]
    exact pairing.source_not_boundary
  target_not_boundary := by
    apply (e.isBoundaryEdge_iff
      ((e.occurrenceEquiv validQ).symm pairing.target).edge).not.mpr
    rw [e.occurrenceEquiv_symm_edge validQ]
    exact pairing.target_not_boundary
  direction := transportDirection
    (e.reverseFace ((e.occurrenceEquiv validQ).symm pairing.source).1)
    (e.reverseFace ((e.occurrenceEquiv validQ).symm pairing.target).1)
    pairing.direction
  compatible := by
    let source := (e.occurrenceEquiv validQ).symm pairing.source
    let target := (e.occurrenceEquiv validQ).symm pairing.target
    have hsource := e.occurrenceEquiv_symm_mapDart validQ pairing.source
    have htarget := e.occurrenceEquiv_symm_mapDart validQ pairing.target
    change
      e.edgeRelabeling.mapDart source.dart =
        if e.reverseFace source.1 then pairing.source.dart.flip
        else pairing.source.dart at hsource
    change
      e.edgeRelabeling.mapDart target.dart =
        if e.reverseFace target.1 then pairing.target.dart.flip
        else pairing.target.dart at htarget
    change
      match transportDirection
          (e.reverseFace source.1) (e.reverseFace target.1)
          pairing.direction with
        | .same => target.dart = source.dart
        | .opposite => target.dart = source.dart.flip
    cases hs : e.reverseFace source.1 <;>
      cases ht : e.reverseFace target.1 <;>
        cases hd : pairing.direction
    all_goals
      apply e.edgeRelabeling.dartEquiv.injective
      simp only [EdgeRelabeling.dartEquiv_apply,
        EdgeRelabeling.mapDart_flip]
      have hcompatible := pairing.compatible
      simp only [hd] at hcompatible
      simp only [hs, ht, Bool.false_eq_true,
        ↓reduceIte] at hsource htarget
      first
      | simpa only [hsource, htarget,
          Bool.false_eq_true, Bool.true_eq_false,
          ↓reduceIte, SignedDart.flip_flip] using hcompatible
      | simpa only [hsource, htarget,
          Bool.false_eq_true, Bool.true_eq_false,
          ↓reduceIte, SignedDart.flip_flip] using
          congrArg SignedDart.flip hcompatible

@[simp]
theorem comapPairing_source
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) :
    (e.comapPairing validQ pairing).source =
      (e.occurrenceEquiv validQ).symm pairing.source :=
  rfl

@[simp]
theorem comapPairing_target
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) :
    (e.comapPairing validQ pairing).target =
      (e.occurrenceEquiv validQ).symm pairing.target :=
  rfl

@[simp]
theorem comapPairing_direction
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) :
    (e.comapPairing validQ pairing).direction =
      transportDirection
        (e.reverseFace ((e.occurrenceEquiv validQ).symm pairing.source).1)
        (e.reverseFace ((e.occurrenceEquiv validQ).symm pairing.target).1)
        pairing.direction :=
  rfl

/-- The inverse pre-realization map sends a target pairing source to its pulled-back side. -/
theorem preHomeomorph_symm_pairing_source_point
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm (pairing.identification.source.point t) =
      (e.comapPairing validQ pairing).identification.source.point
        (e.sideParameter
          ((e.occurrenceEquiv validQ).symm pairing.source).1 t) := by
  exact e.preHomeomorph_symm_occurrenceSide_point validQ pairing.source t

/-- The inverse pre-realization map sends a target pairing target to its pulled-back side. -/
theorem preHomeomorph_symm_pairing_target_point
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm (pairing.identification.target.point t) =
      (e.comapPairing validQ pairing).identification.target.point
        (e.sideParameter
          ((e.occurrenceEquiv validQ).symm pairing.target).1 t) := by
  exact e.preHomeomorph_symm_occurrenceSide_point validQ pairing.target t

/-- Pulled-back gluing parameters commute with the two side reflections. -/
theorem comapPairing_parameter_sideParameter
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    (e.comapPairing validQ pairing).identification.parameter
        (e.sideParameter
          ((e.occurrenceEquiv validQ).symm pairing.source).1 t) =
      e.sideParameter
        ((e.occurrenceEquiv validQ).symm pairing.target).1
        (pairing.identification.parameter t) := by
  exact transportDirection_parameter
    (e.reverseFace ((e.occurrenceEquiv validQ).symm pairing.source).1)
    (e.reverseFace ((e.occurrenceEquiv validQ).symm pairing.target).1)
    pairing.direction t

/-- The inverse facewise homeomorphism sends every target generator into the source generated
relation. -/
theorem preHomeomorph_symm_generator_related
    (e : UnorientedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (pairing : Q.BoundaryPairing)
    (t : unitInterval) :
    P.PolygonalGluingRel validP
      (e.preHomeomorph.symm (pairing.identification.source.point t))
      (e.preHomeomorph.symm
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [e.preHomeomorph_symm_pairing_source_point,
    e.preHomeomorph_symm_pairing_target_point,
    ← e.comapPairing_parameter_sideParameter]
  exact PolygonGluing.related_of_mem
    (e.comapPairing validQ pairing).identification
    (pairing_identification_mem validP (e.comapPairing validQ pairing))
    (e.sideParameter
      ((e.occurrenceEquiv validQ).symm pairing.source).1 t)

/-- The inverse facewise homeomorphism preserves the generated gluing relation. -/
theorem preHomeomorph_symm_related
    (e : UnorientedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) {x y : Q.PolygonalPreRealization}
    (hxy : Q.PolygonalGluingRel validQ x y) :
    P.PolygonalGluingRel validP
      (e.preHomeomorph.symm x) (e.preHomeomorph.symm y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator (Q.polygonalIdentifications validQ)) x y at hxy
  induction hxy with
  | rel x y hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact e.preHomeomorph_symm_generator_related validP validQ pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The facewise homeomorphism identifies the two generated gluing relations. -/
theorem preHomeomorph_related_iff
    (e : UnorientedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (x y : P.PolygonalPreRealization) :
    P.PolygonalGluingRel validP x y ↔
      Q.PolygonalGluingRel validQ (e.preHomeomorph x) (e.preHomeomorph y) := by
  constructor
  · exact e.preHomeomorph_related validP validQ
  · intro hxy
    simpa only [e.preHomeomorph.symm_apply_apply] using
      e.preHomeomorph_symm_related validP validQ hxy

/-- Independent edge and face reorientation preserves the faithful polygonal realization whenever
both endpoint presentations satisfy ordinary incidence validity. -/
noncomputable def realizationHomeomorph
    (e : UnorientedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonalRealization validP ≃ₜ Q.PolygonalRealization validQ :=
  PolygonGluing.realizationCongr e.preHomeomorph
    (e.preHomeomorph_related_iff validP validQ)

/-- Propositional realization-invariance form for face-reversing presentation comparisons. -/
theorem polygonallyEquivalent
    (e : UnorientedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  ⟨e.realizationHomeomorph validP validQ⟩

end UnorientedPresentationIso

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
