/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSpec
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.LaplacianEquiv
import Mathlib.Tactic

/-!
# Relabeling contracted subdivisions

This is the closed-face analogue of `SubdivisionIso`.  The core vertices of a
`DegSpec` are quotient classes, rather than `Fin n`; consequently a symmetry
on the uncontracted core is not by itself enough to relabel a face.  A caller
must also provide the induced equivalence of the *fixed-point classes*.

Keeping that class equivalence explicit is intentional.  In particular it
lets an `AUTO` certificate replay the finite class map selected by its checker,
without claiming that `compFold`'s canonical representatives commute with a
permutation definitionally.

Slot reversal is part of the datum, just as it is for the positive-length
`SubdivisionGraph.Spec.Relabeling`.  It changes only the finite coordinates
inside a surviving slot; the quotient-class boundary is unchanged.
-/

namespace Utilities.Certificate.DegenerateSpec.DegSpec
open Utilities.Certificate

open Utilities

open Finset

variable {n p n' p' : ℕ} (source : DegSpec n p) (target : DegSpec n' p')

/-- An occurrence-sensitive, orientation-preserving relabeling of two closed
subdivision presentations.  `classEquiv` is the essential extra datum beyond
`SubdivisionGraph.Spec.Relabeling`: it names the bijection after zero slots
have identified core vertices. -/
structure Relabeling where
  classEquiv : source.Class ≃ target.Class
  slotEquiv : Fin p ≃ Fin p'
  reversed : Fin p → Bool
  length_eq : ∀ e : Fin p, source.length e = target.length (slotEquiv e)
  tail_eq : ∀ e : Fin p,
    (if reversed e then
        classEquiv ⟨source.rep (source.core.head e), source.rep_idem _⟩
      else classEquiv ⟨source.rep (source.core.tail e), source.rep_idem _⟩) =
      ⟨target.rep (target.core.tail (slotEquiv e)), target.rep_idem _⟩
  head_eq : ∀ e : Fin p,
    (if reversed e then
        classEquiv ⟨source.rep (source.core.tail e), source.rep_idem _⟩
      else classEquiv ⟨source.rep (source.core.head e), source.rep_idem _⟩) =
      ⟨target.rep (target.core.head (slotEquiv e)), target.rep_idem _⟩

variable (r : Relabeling source target)

namespace Relabeling

/-- Interior coordinates on a reversed slot are read from the other end. -/
def interiorEquiv (e : Fin p) :
    Fin (source.length e - 1) ≃ Fin (target.length (r.slotEquiv e) - 1) :=
  (if r.reversed e then Fin.revPerm else Equiv.refl _).trans
    (finCongr (congrArg (fun k : ℕ => k - 1) (r.length_eq e)))

/-- Unit-step coordinates on a reversed slot are read from the other end. -/
def stepOffsetEquiv (e : Fin p) :
    Fin (source.length e) ≃ Fin (target.length (r.slotEquiv e)) :=
  (if r.reversed e then Fin.revPerm else Equiv.refl _).trans
    (finCongr (r.length_eq e))

/-- The vertex equivalence induced by a closed-face relabeling. -/
def vertexEquiv : source.Vertex ≃ target.Vertex :=
  Equiv.sumCongr r.classEquiv
    (Equiv.sigmaCongr r.slotEquiv
      (fun e => interiorEquiv source target r e))

/-- The unit-step occurrence equivalence induced by a closed-face relabeling. -/
def stepEquiv : source.Step ≃ target.Step :=
  Equiv.sigmaCongr r.slotEquiv (fun e =>
    stepOffsetEquiv source target r e)

@[simp] theorem vertexEquiv_coreVertex (v : Fin n) :
    vertexEquiv source target r (source.coreVertex v) =
      Sum.inl (r.classEquiv ⟨source.rep v, source.rep_idem v⟩) := rfl

@[simp] theorem vertexEquiv_interiorVertex (e : Fin p)
    (o : Fin (source.length e - 1)) :
    vertexEquiv source target r (source.interiorVertex e o) =
      target.interiorVertex (r.slotEquiv e)
        (interiorEquiv source target r e o) := rfl

@[simp] theorem stepEquiv_apply (e : Fin p) (o : Fin (source.length e)) :
    stepEquiv source target r ⟨e, o⟩ =
      ⟨r.slotEquiv e,
        stepOffsetEquiv source target r e o⟩ := rfl

theorem vertexEquiv_tail_of_not_reversed (e : Fin p) (hr : r.reversed e = false) :
    vertexEquiv source target r (source.coreVertex (source.core.tail e)) =
      target.coreVertex (target.core.tail (r.slotEquiv e)) := by
  have h := Relabeling.tail_eq r e
  simp only [coreVertex]
  simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
  exact congrArg Sum.inl h

theorem vertexEquiv_head_of_not_reversed (e : Fin p) (hr : r.reversed e = false) :
    vertexEquiv source target r (source.coreVertex (source.core.head e)) =
      target.coreVertex (target.core.head (r.slotEquiv e)) := by
  have h := Relabeling.head_eq r e
  simp only [coreVertex]
  simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
  exact congrArg Sum.inl h

theorem vertexEquiv_tail_of_reversed (e : Fin p) (hr : r.reversed e = true) :
    vertexEquiv source target r (source.coreVertex (source.core.tail e)) =
      target.coreVertex (target.core.head (r.slotEquiv e)) := by
  have h := Relabeling.head_eq r e
  simp only [coreVertex]
  simp only [hr, ↓reduceIte] at h
  exact congrArg Sum.inl h

theorem vertexEquiv_head_of_reversed (e : Fin p) (hr : r.reversed e = true) :
    vertexEquiv source target r (source.coreVertex (source.core.head e)) =
      target.coreVertex (target.core.tail (r.slotEquiv e)) := by
  have h := Relabeling.tail_eq r e
  simp only [coreVertex]
  simp only [hr, ↓reduceIte] at h
  exact congrArg Sum.inl h

theorem stepLeft_map_of_not_reversed (e : Fin p) (o : Fin (source.length e))
    (hr : r.reversed e = false) :
    target.stepLeft (r.slotEquiv e) (stepOffsetEquiv source target r e o) =
      vertexEquiv source target r (source.stepLeft e o) := by
  by_cases h : o.val = 0
  · rw [show source.stepLeft e o = source.coreVertex (source.core.tail e) from dif_pos h]
    unfold DegSpec.stepLeft
    rw [dif_pos (by simpa [stepOffsetEquiv, hr] using h),
      vertexEquiv_tail_of_not_reversed source target r e hr]
  · rw [show source.stepLeft e o = source.interiorVertex e
          ⟨o.val - 1, by have := o.isLt; omega⟩ from dif_neg h]
    unfold DegSpec.stepLeft
    rw [dif_neg (by simpa [stepOffsetEquiv, hr] using h),
      r.vertexEquiv_interiorVertex]
    congr 2
    simp [stepOffsetEquiv, hr]

theorem stepRight_map_of_not_reversed (e : Fin p) (o : Fin (source.length e))
    (hr : r.reversed e = false) :
    target.stepRight (r.slotEquiv e) (stepOffsetEquiv source target r e o) =
      vertexEquiv source target r (source.stepRight e o) := by
  by_cases h : o.val + 1 = source.length e
  · rw [show source.stepRight e o = source.coreVertex (source.core.head e) from dif_pos h]
    unfold DegSpec.stepRight
    rw [dif_pos (by simpa [Fin.ext_iff, stepOffsetEquiv, hr, r.length_eq e] using h),
      vertexEquiv_head_of_not_reversed source target r e hr]
  · rw [show source.stepRight e o = source.interiorVertex e
          ⟨o.val, by have := o.isLt; omega⟩ from dif_neg h]
    unfold DegSpec.stepRight
    rw [dif_neg (by simpa [Fin.ext_iff, stepOffsetEquiv, hr, r.length_eq e] using h),
      r.vertexEquiv_interiorVertex]
    congr 2
    simp [stepOffsetEquiv, hr]

theorem stepLeft_map_of_reversed (e : Fin p) (o : Fin (source.length e))
    (hr : r.reversed e = true) :
    target.stepLeft (r.slotEquiv e) (stepOffsetEquiv source target r e o) =
      vertexEquiv source target r (source.stepRight e o) := by
  by_cases h : o.val + 1 = source.length e
  · rw [show source.stepRight e o = source.coreVertex (source.core.head e) from dif_pos h]
    unfold DegSpec.stepLeft
    rw [dif_pos (by simp [stepOffsetEquiv, hr, Fin.rev]; omega),
      vertexEquiv_head_of_reversed source target r e hr]
  · rw [show source.stepRight e o = source.interiorVertex e
          ⟨o.val, by have := o.isLt; omega⟩ from dif_neg h]
    unfold DegSpec.stepLeft
    rw [dif_neg (by simp [stepOffsetEquiv, hr, Fin.rev]; omega),
      r.vertexEquiv_interiorVertex]
    congr 2
    simp only [stepOffsetEquiv, hr, ↓reduceIte, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev,
      finCongr_apply, Fin.cast_mk]
    omega

theorem stepRight_map_of_reversed (e : Fin p) (o : Fin (source.length e))
    (hr : r.reversed e = true) :
    target.stepRight (r.slotEquiv e) (stepOffsetEquiv source target r e o) =
      vertexEquiv source target r (source.stepLeft e o) := by
  by_cases h : o.val = 0
  · rw [show source.stepLeft e o = source.coreVertex (source.core.tail e) from dif_pos h]
    unfold DegSpec.stepRight
    rw [dif_pos (by simp [stepOffsetEquiv, hr, Fin.rev, ← r.length_eq e]; omega),
      vertexEquiv_tail_of_reversed source target r e hr]
  · rw [show source.stepLeft e o = source.interiorVertex e
          ⟨o.val - 1, by have := o.isLt; omega⟩ from dif_neg h]
    unfold DegSpec.stepRight
    rw [dif_neg (by simp [stepOffsetEquiv, hr, Fin.rev, ← r.length_eq e]; omega),
      r.vertexEquiv_interiorVertex]
    congr 2
    simp only [stepOffsetEquiv, hr, ↓reduceIte, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev,
      finCongr_apply, Fin.cast_mk]
    omega

theorem unitEdge_stepEquiv (s : source.Step) :
    target.unitEdge (stepEquiv source target r s) =
        (vertexEquiv source target r (source.unitEdge s).1,
         vertexEquiv source target r (source.unitEdge s).2) ∨
      target.unitEdge (stepEquiv source target r s) =
        (vertexEquiv source target r (source.unitEdge s).2,
         vertexEquiv source target r (source.unitEdge s).1) := by
  rcases s with ⟨e, o⟩
  rw [stepEquiv_apply source target r e o]
  by_cases hr : r.reversed e
  · right
    change (target.stepLeft _ _, target.stepRight _ _) = _
    rw [stepLeft_map_of_reversed source target r e o hr,
      stepRight_map_of_reversed source target r e o hr]
    rfl
  · left
    change (target.stepLeft _ _, target.stepRight _ _) = _
    have hr' : r.reversed e = false := Bool.eq_false_of_not_eq_true hr
    rw [stepLeft_map_of_not_reversed source target r e o hr',
      stepRight_map_of_not_reversed source target r e o hr']
    rfl

/-- A vertex and unit-step bijection preserving endpoints gives the closed
face Laplacian equivalence.  This copy is polymorphic in `DegSpec`, while the
older helper is specialized to positive `SubdivisionGraph.Spec`s. -/
noncomputable def laplacianEquiv : LaplacianEquiv source.graph target.graph where
  toEquiv := vertexEquiv source target r
  num_edges_eq := by
    intro x y
    rw [target.num_edges_eq_card_filter_steps, source.num_edges_eq_card_filter_steps]
    let src : source.Step → Prop := fun s =>
      source.unitEdge s = (x, y) ∨ source.unitEdge s = (y, x)
    let tgt : target.Step → Prop := fun s =>
      target.unitEdge s = (vertexEquiv source target r x, vertexEquiv source target r y) ∨
        target.unitEdge s = (vertexEquiv source target r y, vertexEquiv source target r x)
    have hiff (s : source.Step) : tgt (stepEquiv source target r s) ↔ src s := by
      rcases unitEdge_stepEquiv source target r s with hs | hs
      · simp only [tgt, src, hs, Prod.ext_iff,
          (vertexEquiv source target r).injective.eq_iff]
      · simp only [tgt, src, hs, Prod.ext_iff,
          (vertexEquiv source target r).injective.eq_iff]
        tauto
    have hfilter : (Finset.univ.filter src).map (stepEquiv source target r).toEmbedding =
        Finset.univ.filter tgt := by
      ext s
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact (hiff s).2 hs
      · intro hs
        refine ⟨(stepEquiv source target r).symm s, ?_, by simp⟩
        exact (hiff _).1 (by simpa using hs)
    change (Finset.univ.filter tgt).card = (Finset.univ.filter src).card
    rw [← hfilter, Finset.card_map]

theorem bnExists_iff (r : Relabeling source target) (rnk deg : ℤ) :
    BNExists target.graph rnk deg ↔ BNExists source.graph rnk deg :=
  (laplacianEquiv source target r).bnExists_iff rnk deg |>.symm

end Relabeling

end Utilities.Certificate.DegenerateSpec.DegSpec
