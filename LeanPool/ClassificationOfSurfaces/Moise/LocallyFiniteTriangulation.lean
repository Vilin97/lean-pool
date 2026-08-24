/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicComplex
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Locally finite triangle complexes

Rado's induction in Moise Chapter 8 passes through locally finite, usually noncompact, PL
complexes.  Requiring every intermediate complex to be finite loses the frontier-vanishing
construction used in the induction step.  This file provides the corresponding ambient API while
keeping the existing finite `GeometricTriangulation` as the final output.

A face is parametrized by the standard simplex on its three global vertices.  The
`faceMap_eq_iff` field says both that parametrizations agree on common faces and that distinct
geometric points are never identified.  Thus the structure records the full face-to-face
condition, rather than only a family of carriers.  Local finiteness is imposed on the carrier
family in the ambient topology.

The main result is `LocallyFiniteTriangleComplex.toGeometricTriangulation`: on a compact
Hausdorff space, local finiteness makes the face type finite; the no-junk-vertices condition then
makes the vertex type finite, and finite closed pasting produces the required homeomorphism from
the canonical barycentric realization.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Extend barycentric coordinates on a finite face by zero to the global vertex type. -/
def extendFaceCoordinates {V : Type*} [DecidableEq V] (t : Finset V)
    (x : stdSimplex ℝ {v // v ∈ t}) : V → ℝ :=
  fun v ↦ if hv : v ∈ t then x ⟨v, hv⟩ else 0

@[simp] theorem extendFaceCoordinates_of_mem {V : Type*} [DecidableEq V]
    (t : Finset V) (x : stdSimplex ℝ {v // v ∈ t}) {v : V} (hv : v ∈ t) :
    extendFaceCoordinates t x v = x ⟨v, hv⟩ := by
  simp [extendFaceCoordinates, hv]

@[simp] theorem extendFaceCoordinates_of_notMem {V : Type*} [DecidableEq V]
    (t : Finset V) (x : stdSimplex ℝ {v // v ∈ t}) {v : V} (hv : v ∉ t) :
    extendFaceCoordinates t x v = 0 := by
  simp [extendFaceCoordinates, hv]

theorem stdSimplex_map_subtypeVal_eq_extendFaceCoordinates
    {V : Type*} [Fintype V] [DecidableEq V] (t : Finset V)
    (x : stdSimplex ℝ {v // v ∈ t}) :
    (stdSimplex.map Subtype.val x : V → ℝ) = extendFaceCoordinates t x := by
  funext v
  by_cases hv : v ∈ t
  · let w : {w // w ∈ t} := ⟨v, hv⟩
    rw [extendFaceCoordinates_of_mem t x hv]
    simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hfilter : Finset.univ.filter (fun q : {q // q ∈ t} ↦ q.1 = v) = {w} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h ↦ Subtype.ext h
      · exact fun h ↦ congrArg Subtype.val h
    rw [hfilter]
    simp [w]
  · rw [extendFaceCoordinates_of_notMem t x hv]
    simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hempty : Finset.univ.filter (fun w : {w // w ∈ t} ↦ w.1 = v) = ∅ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      exact fun hw ↦ hv (hw ▸ w.2)
    rw [hempty]
    simp

theorem extendFaceCoordinates_map_subset
    {V : Type*} [DecidableEq V] {e t : Finset V}
    (het : e ⊆ t) (x : stdSimplex ℝ {v // v ∈ e}) :
    extendFaceCoordinates t
        (stdSimplex.map (fun v : {v // v ∈ e} ↦ ⟨v.1, het v.2⟩) x) =
      extendFaceCoordinates e x := by
  funext v
  by_cases hve : v ∈ e
  · have hvt : v ∈ t := het hve
    rw [extendFaceCoordinates_of_mem t _ hvt,
      extendFaceCoordinates_of_mem e x hve]
    simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    let w : {w // w ∈ e} := ⟨v, hve⟩
    have hfilter : Finset.univ.filter
        (fun q : {q // q ∈ e} ↦
          (⟨q.1, het q.2⟩ : {q // q ∈ t}) = ⟨v, hvt⟩) = {w} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        apply Subtype.ext
        simpa [w] using congrArg
          (fun z : {z // z ∈ t} ↦ z.1) h
      · intro h
        subst q
        rfl
    rw [hfilter]
    simp [w]
  · rw [extendFaceCoordinates_of_notMem e x hve]
    by_cases hvt : v ∈ t
    · rw [extendFaceCoordinates_of_mem t _ hvt]
      simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
      have hempty : Finset.univ.filter
          (fun q : {q // q ∈ e} ↦
            (⟨q.1, het q.2⟩ : {q // q ∈ t}) = ⟨v, hvt⟩) = ∅ := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        intro h
        apply hve
        have hval : q.1 = v := congrArg (fun z : {z // z ∈ t} ↦ z.1) h
        simpa [hval] using q.2
      rw [hempty]
      simp
    · rw [extendFaceCoordinates_of_notMem t _ hvt]

/-! ## Relabeling a finite face along an embedding -/

/-- The vertices of a finite face are equivalent to the vertices of its image under an
embedding. -/
noncomputable def finsetMapSubtypeEquiv
    {A B : Type*}
    (e : A ↪ B) (t : Finset A) :
    {a // a ∈ t} ≃ {b // b ∈ t.map e} := by
  classical
  let f : {a // a ∈ t} → {b // b ∈ t.map e} :=
    fun a ↦ ⟨e a.1, Finset.mem_map.mpr
      ⟨a.1, a.2, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hab)
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha, hab⟩ := Finset.mem_map.mp hb
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    exact hab

@[simp] theorem finsetMapSubtypeEquiv_apply_val
    {A B : Type*}
    (e : A ↪ B) (t : Finset A) (a : {a // a ∈ t}) :
    (finsetMapSubtypeEquiv e t a).1 = e a.1 := rfl

/-- Pull simplex coordinates on a relabeled face back to the original face. -/
noncomputable def relabelFaceSimplex
    {A B : Type*}
    (e : A ↪ B) (t : Finset A)
    (x : stdSimplex ℝ {b // b ∈ t.map e}) :
    stdSimplex ℝ {a // a ∈ t} :=
  stdSimplex.map (finsetMapSubtypeEquiv e t).symm x

/-- Face relabeling along an embedding is onto. -/
theorem relabelFaceSimplex_surjective
    {A B : Type*}
    (e : A ↪ B) (t : Finset A) :
    Function.Surjective (relabelFaceSimplex e t) := by
  classical
  intro x
  refine ⟨stdSimplex.map (finsetMapSubtypeEquiv e t) x, ?_⟩
  unfold relabelFaceSimplex
  rw [stdSimplex.map_comp_apply]
  have hcomp :
      (finsetMapSubtypeEquiv e t).symm ∘
          (finsetMapSubtypeEquiv e t) = id := by
    funext a
    exact (finsetMapSubtypeEquiv e t).symm_apply_apply a
  rw [hcomp, stdSimplex.map_id_apply]

/-- Pulling coordinates back along a face relabeling preserves the coordinate at every
original vertex. -/
theorem relabelFaceSimplex_extended_apply
    {A B : Type*}
    [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (t : Finset A)
    (x : stdSimplex ℝ {b // b ∈ t.map e}) (a : A) :
    extendFaceCoordinates t (relabelFaceSimplex e t x) a =
      extendFaceCoordinates (t.map e) x (e a) := by
  classical
  by_cases ha : a ∈ t
  · have hea : e a ∈ t.map e :=
      Finset.mem_map.mpr ⟨a, ha, rfl⟩
    rw [extendFaceCoordinates_of_mem t _ ha,
      extendFaceCoordinates_of_mem (t.map e) _ hea]
    simp only [relabelFaceSimplex, stdSimplex.map_coe,
      FunOnFinite.linearMap_apply_apply]
    let q : {b // b ∈ t.map e} := ⟨e a, hea⟩
    have hfilter :
        Finset.univ.filter
            (fun z : {b // b ∈ t.map e} ↦
              (finsetMapSubtypeEquiv e t).symm z = ⟨a, ha⟩) =
          {q} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hz
        apply (finsetMapSubtypeEquiv e t).symm.injective
        calc
          (finsetMapSubtypeEquiv e t).symm z = ⟨a, ha⟩ := hz
          _ = (finsetMapSubtypeEquiv e t).symm q := by
            rw [show q = finsetMapSubtypeEquiv e t ⟨a, ha⟩ by
              apply Subtype.ext
              rfl,
              (finsetMapSubtypeEquiv e t).symm_apply_apply]
      · intro hz
        subst z
        rw [show q = finsetMapSubtypeEquiv e t ⟨a, ha⟩ by
          apply Subtype.ext
          rfl,
          (finsetMapSubtypeEquiv e t).symm_apply_apply]
    rw [hfilter]
    simp [q]
  · have hea : e a ∉ t.map e := by
      intro hea
      obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp hea
      exact ha (e.injective hba ▸ hb)
    rw [extendFaceCoordinates_of_notMem t _ ha,
      extendFaceCoordinates_of_notMem (t.map e) _ hea]

/-- Relabeling two faces by the same embedding preserves equality of their global
zero-extended coordinate functions. -/
theorem relabelFaceSimplex_extended_eq_iff
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) {s t : Finset A}
    {x : stdSimplex ℝ {b // b ∈ s.map e}}
    {y : stdSimplex ℝ {b // b ∈ t.map e}} :
    extendFaceCoordinates s (relabelFaceSimplex e s x) =
        extendFaceCoordinates t (relabelFaceSimplex e t y) ↔
      extendFaceCoordinates (s.map e) x =
        extendFaceCoordinates (t.map e) y := by
  constructor
  · intro h
    funext b
    by_cases hb : b ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hb
      rw [← relabelFaceSimplex_extended_apply e s x a,
        ← relabelFaceSimplex_extended_apply e t y a,
        congrFun h a]
    · have hbs : b ∉ s.map e := by
        intro hbs
        obtain ⟨a, -, hab⟩ := Finset.mem_map.mp hbs
        exact hb ⟨a, hab⟩
      have hbt : b ∉ t.map e := by
        intro hbt
        obtain ⟨a, -, hab⟩ := Finset.mem_map.mp hbt
        exact hb ⟨a, hab⟩
      rw [extendFaceCoordinates_of_notMem _ _ hbs,
        extendFaceCoordinates_of_notMem _ _ hbt]
  · intro h
    funext a
    rw [relabelFaceSimplex_extended_apply e s x a,
      relabelFaceSimplex_extended_apply e t y a,
      congrFun h (e a)]

/-- Relabeling does not change a weighted evaluation of the zero-extended coordinates. -/
theorem sum_extendFaceCoordinates_relabelFaceSimplex
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (t : Finset A)
    (x : stdSimplex ℝ {b // b ∈ t.map e}) (F : B → ℝ) :
    (∑ b : B, extendFaceCoordinates (t.map e) x b * F b) =
      ∑ a : A,
        extendFaceCoordinates t (relabelFaceSimplex e t x) a *
          F (e a) := by
  classical
  calc
    (∑ b : B, extendFaceCoordinates (t.map e) x b * F b) =
        ∑ b ∈ t.map e,
          extendFaceCoordinates (t.map e) x b * F b := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _ hb
      rw [extendFaceCoordinates_of_notMem _ _ hb, zero_mul]
    _ = ∑ a ∈ t,
          extendFaceCoordinates (t.map e) x (e a) * F (e a) := by
      rw [Finset.sum_map]
    _ = ∑ a ∈ t,
          extendFaceCoordinates t (relabelFaceSimplex e t x) a *
            F (e a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [relabelFaceSimplex_extended_apply]
    _ = ∑ a : A,
          extendFaceCoordinates t (relabelFaceSimplex e t x) a *
            F (e a) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      rw [extendFaceCoordinates_of_notMem _ _ ha, zero_mul]

/-- When the source face is the whole finite type, remove the vacuous membership subtype after
pulling coordinates back along an embedding. -/
noncomputable def univMapSubtypeEquiv
    {A B : Type*} [Fintype A]
    (e : A ↪ B) :
    {b // b ∈ (Finset.univ : Finset A).map e} ≃ A :=
  (finsetMapSubtypeEquiv e Finset.univ).symm.trans
    { toFun := fun a ↦ a.1
      invFun := fun a ↦ ⟨a, Finset.mem_univ a⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }

/-- Pull simplex coordinates on the image of a finite type back to that finite type. -/
noncomputable def relabelUnivSimplex
    {A B : Type*} [Fintype A]
    (e : A ↪ B)
    (x : stdSimplex ℝ {b // b ∈ (Finset.univ : Finset A).map e}) :
    stdSimplex ℝ A :=
  stdSimplex.map (univMapSubtypeEquiv e) x

/-- Pullback along an embedded whole finite vertex type is onto: its inverse simply pushes
coordinates forward along the inverse equivalence onto the image. -/
theorem relabelUnivSimplex_surjective
    {A B : Type*} [Fintype A]
    (e : A ↪ B) :
    Function.Surjective (relabelUnivSimplex e) := by
  classical
  intro x
  refine ⟨stdSimplex.map (univMapSubtypeEquiv e).symm x, ?_⟩
  unfold relabelUnivSimplex
  rw [stdSimplex.map_comp_apply]
  have hcomp :
      (univMapSubtypeEquiv e) ∘
          (univMapSubtypeEquiv e).symm = id := by
    funext a
    exact (univMapSubtypeEquiv e).apply_symm_apply a
  rw [hcomp, stdSimplex.map_id_apply]

/-- The whole-type relabeling preserves the coordinate of every embedded source vertex. -/
theorem relabelUnivSimplex_apply
    {A B : Type*} [Fintype A]
    [DecidableEq B]
    (e : A ↪ B)
    (x : stdSimplex ℝ {b // b ∈ (Finset.univ : Finset A).map e})
    (a : A) :
    relabelUnivSimplex e x a =
      extendFaceCoordinates ((Finset.univ : Finset A).map e) x (e a) := by
  classical
  let ea : {b // b ∈ (Finset.univ : Finset A).map e} :=
    ⟨e a, Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  rw [extendFaceCoordinates_of_mem _ _ ea.2]
  simp only [relabelUnivSimplex, stdSimplex.map_coe,
    FunOnFinite.linearMap_apply_apply]
  have hfilter :
      Finset.univ.filter
          (fun z : {b // b ∈ (Finset.univ : Finset A).map e} ↦
            univMapSubtypeEquiv e z = a) =
        {ea} := by
    have hea : univMapSubtypeEquiv e ea = a := by
      have heainv : (univMapSubtypeEquiv e).symm a = ea := by
        apply Subtype.ext
        rfl
      calc
        univMapSubtypeEquiv e ea =
            univMapSubtypeEquiv e ((univMapSubtypeEquiv e).symm a) :=
          congrArg (univMapSubtypeEquiv e) heainv.symm
        _ = a := (univMapSubtypeEquiv e).apply_symm_apply a
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hz
      apply (univMapSubtypeEquiv e).injective
      rw [hz, hea]
    · intro hz
      subst z
      exact hea
  rw [hfilter]
  simp [ea]

/-- An injective vertex map preserves the coordinate at each source vertex. -/
theorem stdSimplex_map_embedding_apply
    {A B : Type*} [Fintype A] [Fintype B]
    (e : A ↪ B) (x : stdSimplex ℝ A) (a : A) :
    stdSimplex.map e x (e a) = x a := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have hfilter :
      Finset.univ.filter (fun q : A ↦ e q = e a) = {a} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact e.injective.eq_iff
  rw [hfilter]
  simp

/-- An injective vertex map has zero coordinate away from its image. -/
theorem stdSimplex_map_embedding_apply_of_notMem_range
    {A B : Type*} [Fintype A] [Fintype B]
    (e : A ↪ B) (x : stdSimplex ℝ A) {b : B}
    (hb : b ∉ Set.range e) :
    stdSimplex.map e x b = 0 := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have hfilter :
      Finset.univ.filter (fun q : A ↦ e q = b) = ∅ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    exact fun hq ↦ hb ⟨q, hq⟩
  rw [hfilter]
  simp

/-- Relabel a finite face family along an embedding of its vertex type. -/
def relabelFaceFamily
    {A B : Type*} [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A)) : Finset (Finset B) := by
  exact F.image fun t ↦ t.map e

end Moise

namespace TriangleFamily

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

/-- Regard a listed face as a face of the family obtained by injectively relabeling its
vertices. -/
def faceOfRelabel (e : A ↪ B) {faces : Finset (Finset A)} :
    Face faces → Face (Moise.relabelFaceFamily e faces) :=
  fun f => ⟨f.1.map e, Finset.mem_image.mpr ⟨f.1, f.2, rfl⟩⟩

omit [DecidableEq A] in
theorem faceOfRelabel_val (e : A ↪ B) {faces : Finset (Finset A)}
    (f : Face faces) : (faceOfRelabel e f).1 = f.1.map e :=
  rfl

omit [DecidableEq A] in
/-- Injective vertex relabeling preserves dual adjacency of listed faces. -/
theorem faceAdjacent_faceOfRelabel (e : A ↪ B) {faces : Finset (Finset A)}
    {f g : Face faces} (hfg : FaceAdjacent faces f g) :
    FaceAdjacent (Moise.relabelFaceFamily e faces)
      (faceOfRelabel e f) (faceOfRelabel e g) := by
  rcases hfg with ⟨edge, hedgeCard, hedgeLeft, hedgeRight⟩
  refine ⟨edge.map e, ?_, ?_, ?_⟩
  · simpa only [Finset.card_map] using hedgeCard
  · exact Finset.map_subset_map.mpr hedgeLeft
  · exact Finset.map_subset_map.mpr hedgeRight

omit [DecidableEq A] in
/-- Injective vertex relabeling carries a finite dual path to the relabeled family. -/
theorem reflTransGen_faceAdjacent_faceOfRelabel (e : A ↪ B)
    {faces : Finset (Finset A)} {f g : Face faces}
    (hfg : Relation.ReflTransGen (FaceAdjacent faces) f g) :
    Relation.ReflTransGen (FaceAdjacent (Moise.relabelFaceFamily e faces))
      (faceOfRelabel e f) (faceOfRelabel e g) := by
  induction hfg with
  | refl => exact Relation.ReflTransGen.refl
  | tail _hab hbc ih =>
      exact ih.tail (faceAdjacent_faceOfRelabel e hbc)

omit [DecidableEq A] in
/-- Dual connectivity is preserved by an injective relabeling of the vertex type. -/
theorem isDualConnected_relabel (e : A ↪ B) {faces : Finset (Finset A)}
    (hfaces : IsDualConnected faces) :
    IsDualConnected (Moise.relabelFaceFamily e faces) := by
  intro f g
  obtain ⟨f', hf', hfeq⟩ := Finset.mem_image.mp f.2
  obtain ⟨g', hg', hgeq⟩ := Finset.mem_image.mp g.2
  let fs : Face faces := ⟨f', hf'⟩
  let gs : Face faces := ⟨g', hg'⟩
  have hpath :=
    reflTransGen_faceAdjacent_faceOfRelabel e (hfaces fs gs)
  have hfval : (faceOfRelabel e fs).1 = f.1 := by
    change f'.map e = f.1
    exact hfeq
  have hgval : (faceOfRelabel e gs).1 = g.1 := by
    change g'.map e = g.1
    exact hgeq
  have hfs : faceOfRelabel e fs = f := Subtype.ext hfval
  have hgs : faceOfRelabel e gs = g := Subtype.ext hgval
  rw [hfs, hgs] at hpath
  exact hpath

omit [DecidableEq A] [DecidableEq B] in
/-- Faces relabeled from different vertex types share an edge when the two source edges have the
same relabeled image. -/
theorem hasCrossEdge_relabel_of_mapped_edge_eq
    {C : Type*} [DecidableEq C]
    (eleft : A ↪ C) (eright : B ↪ C)
    {left : Finset (Finset A)} {right : Finset (Finset B)}
    (fleft : Face left) (fright : Face right)
    (edgeLeft : Finset A) (edgeRight : Finset B)
    (hedgeCard : edgeLeft.card = 2)
    (hedgeLeft : edgeLeft ⊆ fleft.1)
    (hedgeRight : edgeRight ⊆ fright.1)
    (hmap : edgeLeft.map eleft = edgeRight.map eright) :
    HasCrossEdge (Moise.relabelFaceFamily eleft left)
      (Moise.relabelFaceFamily eright right) := by
  refine
    ⟨faceOfRelabel eleft fleft, faceOfRelabel eright fright,
      edgeLeft.map eleft, ?_, ?_, ?_⟩
  · simpa only [Finset.card_map] using hedgeCard
  · exact Finset.map_subset_map.mpr hedgeLeft
  · rw [hmap]
    exact Finset.map_subset_map.mpr hedgeRight

/-- A shared edge remains a shared edge when both families are injectively relabeled. -/
theorem hasCrossEdge_relabel (e : A ↪ B)
    {left right : Finset (Finset A)} (hcross : HasCrossEdge left right) :
    HasCrossEdge (Moise.relabelFaceFamily e left)
      (Moise.relabelFaceFamily e right) := by
  rcases hcross with
    ⟨fleft, fright, edge, hedgeCard, hedgeLeft, hedgeRight⟩
  exact hasCrossEdge_relabel_of_mapped_edge_eq e e
    fleft fright edge edge hedgeCard hedgeLeft hedgeRight rfl

end TriangleFamily

namespace Moise

/-- Push a geometric realization forward along an injective relabeling of all vertices. -/
noncomputable def pushGeometricRealization
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A)) :
    GeometricRealization A F →
      GeometricRealization B (relabelFaceFamily e F) := by
  intro x
  refine ⟨stdSimplex.map e ⟨x.1, x.2.1⟩,
    (stdSimplex.map e ⟨x.1, x.2.1⟩).2, ?_⟩
  obtain ⟨t, ht, hxt⟩ := x.2.2
  refine ⟨t.map e, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
  intro b hb
  by_cases hbrange : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hbrange
    rw [stdSimplex_map_embedding_apply]
    apply hxt
    intro hat
    exact hb (Finset.mem_map.mpr ⟨a, hat, rfl⟩)
  · exact stdSimplex_map_embedding_apply_of_notMem_range e _ hbrange

/-- Pull a point of a relabeled realization back to its original vertex type. -/
noncomputable def pullGeometricRealization
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A)) :
    GeometricRealization B (relabelFaceFamily e F) →
      GeometricRealization A F := by
  intro y
  let u : Finset B := Classical.choose y.2.2
  have huData := Classical.choose_spec y.2.2
  have hu : u ∈ relabelFaceFamily e F := huData.1
  have hyu : ∀ b ∉ u, y.1 b = 0 := huData.2
  let t : Finset A := Classical.choose (Finset.mem_image.mp hu)
  have htData := Classical.choose_spec (Finset.mem_image.mp hu)
  have ht : t ∈ F := htData.1
  have hut : t.map e = u := htData.2
  have hyt : ∀ b ∉ t.map e, y.1 b = 0 := by
    intro b hb
    apply hyu b
    rwa [← hut]
  let x : A → ℝ := fun a ↦ y.1 (e a)
  have hx_nonneg : ∀ a, 0 ≤ x a := fun a ↦ y.2.1.1 (e a)
  have hx_sum : ∑ a, x a = 1 := by
    calc
      ∑ a, x a = ∑ a ∈ t, x a := by
        symm
        apply Finset.sum_subset (Finset.subset_univ t)
        intro a _ ha
        apply hyt (e a)
        intro hea
        obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp hea
        exact ha (e.injective hba ▸ hb)
      _ = ∑ b ∈ t.map e, y.1 b := by
        rw [Finset.sum_map]
      _ = ∑ b, y.1 b := by
        apply Finset.sum_subset (Finset.subset_univ (t.map e))
        intro b _ hb
        exact hyt b hb
      _ = 1 := y.2.1.2
  refine ⟨x, ⟨hx_nonneg, hx_sum⟩, t, ht, ?_⟩
  intro a ha
  apply hyt (e a)
  intro hea
  obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp hea
  exact ha (e.injective hba ▸ hb)

@[simp] theorem pushGeometricRealization_val
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A))
    (x : GeometricRealization A F) :
    (pushGeometricRealization e F x).1 =
      stdSimplex.map e ⟨x.1, x.2.1⟩ := rfl

@[simp] theorem pushGeometricRealization_apply_embedding
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A))
    (x : GeometricRealization A F) (a : A) :
    (pushGeometricRealization e F x).1 (e a) = x.1 a := by
  rw [pushGeometricRealization_val,
    stdSimplex_map_embedding_apply]
  rfl

theorem pushGeometricRealization_apply_of_notMem_range
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A))
    (x : GeometricRealization A F) {b : B}
    (hb : b ∉ Set.range e) :
    (pushGeometricRealization e F x).1 b = 0 := by
  rw [pushGeometricRealization_val]
  exact stdSimplex_map_embedding_apply_of_notMem_range e _ hb

theorem pushGeometricRealization_val_eq_of_val_eq
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F G : Finset (Finset A))
    (x : GeometricRealization A F)
    (y : GeometricRealization A G) (hxy : x.1 = y.1) :
    (pushGeometricRealization e F x).1 =
      (pushGeometricRealization e G y).1 := by
  funext b
  by_cases hb : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hb
    rw [pushGeometricRealization_apply_embedding,
      pushGeometricRealization_apply_embedding]
    exact congrFun hxy a
  · rw [pushGeometricRealization_apply_of_notMem_range e F x hb,
      pushGeometricRealization_apply_of_notMem_range e G y hb]

@[simp] theorem pullGeometricRealization_apply
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A))
    (y : GeometricRealization B (relabelFaceFamily e F)) (a : A) :
    (pullGeometricRealization e F y).1 a = y.1 (e a) := by
  rfl

@[simp] theorem pull_pushGeometricRealization
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A))
    (x : GeometricRealization A F) :
    pullGeometricRealization e F (pushGeometricRealization e F x) = x := by
  apply Subtype.ext
  funext a
  rw [pullGeometricRealization_apply, pushGeometricRealization_val]
  exact stdSimplex_map_embedding_apply e ⟨x.1, x.2.1⟩ a

@[simp] theorem push_pullGeometricRealization
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A))
    (y : GeometricRealization B (relabelFaceFamily e F)) :
    pushGeometricRealization e F (pullGeometricRealization e F y) = y := by
  apply Subtype.ext
  funext b
  by_cases hbrange : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hbrange
    rw [pushGeometricRealization_val]
    rw [stdSimplex_map_embedding_apply]
    exact pullGeometricRealization_apply e F y a
  · rw [pushGeometricRealization_val,
      stdSimplex_map_embedding_apply_of_notMem_range _ _ hbrange]
    obtain ⟨u, hu, hyu⟩ := y.2.2
    obtain ⟨t, -, hut⟩ := Finset.mem_image.mp hu
    symm
    apply hyu
    subst u
    intro hb
    obtain ⟨a, -, hab⟩ := Finset.mem_map.mp hb
    exact hbrange ⟨a, hab⟩

theorem continuous_pushGeometricRealization
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A)) :
    Continuous (pushGeometricRealization e F) := by
  apply Continuous.subtype_mk
  have hin :
      Continuous fun x : GeometricRealization A F ↦
        (⟨x.1, x.2.1⟩ : stdSimplex ℝ A) := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  exact continuous_subtype_val.comp
    ((stdSimplex.continuous_map e).comp hin)

theorem continuous_pullGeometricRealization
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A)) :
    Continuous (pullGeometricRealization e F) := by
  apply Continuous.subtype_mk
  change Continuous fun y :
      GeometricRealization B (relabelFaceFamily e F) ↦
        fun a ↦ y.1 (e a)
  exact continuous_pi fun a ↦
    (continuous_apply (e a)).comp continuous_subtype_val

/-- Relabeling a finite face family along a vertex embedding does not change its realization. -/
noncomputable def relabelGeometricRealizationHomeomorph
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B) (F : Finset (Finset A)) :
    GeometricRealization A F ≃ₜ
      GeometricRealization B (relabelFaceFamily e F) where
  toFun := pushGeometricRealization e F
  invFun := pullGeometricRealization e F
  left_inv := pull_pushGeometricRealization e F
  right_inv := push_pullGeometricRealization e F
  continuous_toFun := continuous_pushGeometricRealization e F
  continuous_invFun := continuous_pullGeometricRealization e F

/-- Weighted evaluation is unchanged by whole-type relabeling. -/
theorem sum_extendFaceCoordinates_relabelUnivSimplex
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (e : A ↪ B)
    (x : stdSimplex ℝ
      {b // b ∈ (Finset.univ : Finset A).map e})
    (F : B → ℝ) :
    (∑ b : B,
        extendFaceCoordinates
          ((Finset.univ : Finset A).map e) x b * F b) =
      ∑ a : A, relabelUnivSimplex e x a * F (e a) := by
  classical
  calc
    (∑ b : B,
        extendFaceCoordinates
          ((Finset.univ : Finset A).map e) x b * F b) =
        ∑ b ∈ (Finset.univ : Finset A).map e,
          extendFaceCoordinates
            ((Finset.univ : Finset A).map e) x b * F b := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _ hb
      rw [extendFaceCoordinates_of_notMem _ _ hb, zero_mul]
    _ = ∑ a : A,
          extendFaceCoordinates
            ((Finset.univ : Finset A).map e) x (e a) *
              F (e a) := by
      rw [Finset.sum_map]
    _ = ∑ a : A, relabelUnivSimplex e x a * F (e a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [relabelUnivSimplex_apply]

/-- A sum over the subtype of a finite face is the corresponding sum of its zero-extended
coordinates over the underlying vertex set. -/
theorem sum_attach_mul_eq_sum_extendFaceCoordinates
    {V : Type*} [DecidableEq V] (t : Finset V)
  (x : stdSimplex ℝ {v // v ∈ t}) (F : V → ℝ) :
    (∑ v : {v // v ∈ t}, x v * F v.1) =
      ∑ v ∈ t, extendFaceCoordinates t x v * F v := by
  rw [Finset.univ_eq_attach]
  calc
    (∑ v ∈ t.attach, x v * F v.1) =
        ∑ v ∈ t.attach, extendFaceCoordinates t x v.1 * F v.1 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [extendFaceCoordinates_of_mem t x v.2]
    _ = ∑ v ∈ t, extendFaceCoordinates t x v * F v :=
      Finset.sum_attach t fun v ↦ extendFaceCoordinates t x v * F v

/-- Equal zero-extended coordinates give equal weighted sums against any scalar-valued
function on the global vertex type. -/
theorem sum_extendFaceCoordinates_eq_of_eq
    {V : Type*} [DecidableEq V] {s t : Finset V}
    (x : stdSimplex ℝ {v // v ∈ s}) (y : stdSimplex ℝ {v // v ∈ t})
    (hxy : extendFaceCoordinates s x = extendFaceCoordinates t y)
    (F : V → ℝ) :
    (∑ v : {v // v ∈ s}, x v * F v.1) =
      ∑ v : {v // v ∈ t}, y v * F v.1 := by
  rw [sum_attach_mul_eq_sum_extendFaceCoordinates s x F,
    sum_attach_mul_eq_sum_extendFaceCoordinates t y F]
  calc
    (∑ v ∈ s, extendFaceCoordinates s x v * F v) =
        ∑ v ∈ s ∪ t, extendFaceCoordinates s x v * F v := by
      apply Finset.sum_subset Finset.subset_union_left
      intro v _ hv
      rw [extendFaceCoordinates_of_notMem s x hv, zero_mul]
    _ = ∑ v ∈ s ∪ t, extendFaceCoordinates t y v * F v := by
      apply Finset.sum_congr rfl
      intro v _
      rw [congrFun hxy v]
    _ = ∑ v ∈ t, extendFaceCoordinates t y v * F v := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro v _ hv
      rw [extendFaceCoordinates_of_notMem t y hv, zero_mul]

/-- A locally finite family of parametrized triangles in an ambient topological space.

`vertex_used` excludes irrelevant vertices.  This matters in the compactness-to-finiteness
bridge: local finiteness controls the number of nonempty faces, and every vertex must then occur
in one of those faces. -/
structure LocallyFiniteTriangleComplex (S : Type*) [TopologicalSpace S] where
  /-- Global vertices, shared literally by incident faces. -/
  Vertex : Type
  /-- Equality of vertices is decidable so that faces are finite sets. -/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- Maximal two-dimensional faces. -/
  Face : Type
  /-- Equality of maximal faces is decidable. -/
  [faceDecidableEq : DecidableEq Face]
  /-- The three global vertices of a maximal face. -/
  faceVertices : Face → Finset Vertex
  /-- Every maximal face is a triangle. -/
  faceVertices_card : ∀ f, (faceVertices f).card = 3
  /-- Every declared global vertex occurs in a maximal face. -/
  vertex_used : ∀ v, ∃ f, v ∈ faceVertices f
  /-- Coordinate map of a closed triangle into the ambient space. -/
  faceMap : ∀ f, stdSimplex ℝ {v // v ∈ faceVertices f} → S
  /-- Each coordinate map is continuous. -/
  faceMap_continuous : ∀ f, Continuous (faceMap f)
  /-- Exact face-to-face compatibility and global injectivity, expressed in barycentric
  coordinates. -/
  faceMap_eq_iff : ∀ {f g} {x y},
    faceMap f x = faceMap g y ↔
      extendFaceCoordinates (faceVertices f) x =
        extendFaceCoordinates (faceVertices g) y
  /-- The closed triangle carriers form a locally finite family. -/
  locallyFinite : LocallyFinite fun f ↦ Set.range (faceMap f)

attribute [instance] LocallyFiniteTriangleComplex.vertexDecidableEq
attribute [instance] LocallyFiniteTriangleComplex.faceDecidableEq

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] (K : LocallyFiniteTriangleComplex S)

/-- The ambient carrier of one maximal face. -/
def faceCarrier (f : K.Face) : Set S :=
  Set.range (K.faceMap f)

/-- The ambient support of the locally finite complex. -/
def support : Set S :=
  ⋃ f, K.faceCarrier f

theorem faceCarrier_nonempty (f : K.Face) : (K.faceCarrier f).Nonempty := by
  have hne : (K.faceVertices f).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := K.faceVertices_card f
    rw [h] at this
    simp at this
  let v : {v // v ∈ K.faceVertices f} := ⟨hne.choose, hne.choose_spec⟩
  exact ⟨K.faceMap f (stdSimplex.vertex v), Set.mem_range_self _⟩

theorem faceMap_injective (f : K.Face) : Function.Injective (K.faceMap f) := by
  intro x y hxy
  have hcoords := K.faceMap_eq_iff.mp hxy
  apply stdSimplex.ext
  funext v
  have hv := congrFun hcoords v.1
  simpa only [extendFaceCoordinates_of_mem (K.faceVertices f) x v.2,
    extendFaceCoordinates_of_mem (K.faceVertices f) y v.2] using hv

theorem isEmbedding_faceMap [T2Space S] (f : K.Face) :
    _root_.Topology.IsEmbedding (K.faceMap f) :=
  ((K.faceMap_continuous f).isClosedEmbedding (K.faceMap_injective f)).isEmbedding

theorem isCompact_faceCarrier (f : K.Face) : IsCompact (K.faceCarrier f) :=
  isCompact_range (K.faceMap_continuous f)

theorem isClosed_faceCarrier [T2Space S] (f : K.Face) : IsClosed (K.faceCarrier f) :=
  (K.isCompact_faceCarrier f).isClosed

theorem isClosed_support [T2Space S] : IsClosed K.support :=
  K.locallyFinite.isClosed_iUnion K.isClosed_faceCarrier

theorem extendFaceCoordinates_vertex (f : K.Face) {v : K.Vertex}
    (hv : v ∈ K.faceVertices f) :
    extendFaceCoordinates (K.faceVertices f)
        (stdSimplex.vertex ⟨v, hv⟩) = Pi.single v 1 := by
  funext w
  by_cases hwv : w = v
  · subst w
    simp [extendFaceCoordinates, hv]
  · by_cases hw : w ∈ K.faceVertices f
    · have hsub : (⟨w, hw⟩ : {w // w ∈ K.faceVertices f}) ≠ ⟨v, hv⟩ := by
        exact fun h ↦ hwv (congrArg Subtype.val h)
      simp [extendFaceCoordinates, hw, hwv, hsub]
    · simp [extendFaceCoordinates, hw, hwv]

/-- A chosen maximal face incident to a global vertex. -/
noncomputable def incidentFace (v : K.Vertex) : K.Face :=
  Classical.choose (K.vertex_used v)

theorem mem_faceVertices_incidentFace (v : K.Vertex) :
    v ∈ K.faceVertices (K.incidentFace v) :=
  Classical.choose_spec (K.vertex_used v)

/-- The ambient point represented by a global vertex. -/
noncomputable def vertexPoint (v : K.Vertex) : S :=
  K.faceMap (K.incidentFace v)
    (stdSimplex.vertex ⟨v, K.mem_faceVertices_incidentFace v⟩)

/-- Every incident face parametrization sends a shared abstract vertex to the same ambient
point. -/
theorem faceMap_vertex_eq_vertexPoint (f : K.Face) {v : K.Vertex}
    (hv : v ∈ K.faceVertices f) :
    K.faceMap f (stdSimplex.vertex ⟨v, hv⟩) = K.vertexPoint v := by
  apply K.faceMap_eq_iff.mpr
  rw [K.extendFaceCoordinates_vertex f hv,
    K.extendFaceCoordinates_vertex (K.incidentFace v)
      (K.mem_faceVertices_incidentFace v)]

theorem vertexPoint_in_faceCarrier (f : K.Face) {v : K.Vertex}
    (hv : v ∈ K.faceVertices f) : K.vertexPoint v ∈ K.faceCarrier f :=
  ⟨stdSimplex.vertex ⟨v, hv⟩, K.faceMap_vertex_eq_vertexPoint f hv⟩

theorem vertexPoint_injective : Function.Injective K.vertexPoint := by
  intro v w hvw
  have hcoords := K.faceMap_eq_iff.mp hvw
  rw [K.extendFaceCoordinates_vertex (K.incidentFace v)
      (K.mem_faceVertices_incidentFace v),
    K.extendFaceCoordinates_vertex (K.incidentFace w)
      (K.mem_faceVertices_incidentFace w)] at hcoords
  by_contra hvw'
  have h := congrFun hcoords v
  simp [hvw'] at h

/-- Singleton carriers of the global vertices form a locally finite family. -/
theorem locallyFinite_vertexPoints :
    LocallyFinite fun v : K.Vertex ↦ ({K.vertexPoint v} : Set S) := by
  intro x
  obtain ⟨U, hUx, hfinite⟩ := K.locallyFinite x
  refine ⟨U, hUx, ?_⟩
  let F : Set K.Face := {f | (K.faceCarrier f ∩ U).Nonempty}
  let V : Set K.Vertex := ⋃ f ∈ F, (K.faceVertices f : Set K.Vertex)
  have hVfinite : V.Finite := hfinite.biUnion fun f _ ↦
    (K.faceVertices f).finite_toSet
  apply hVfinite.subset
  intro v hv
  obtain ⟨p, hpv, hpU⟩ := hv
  have hp : p = K.vertexPoint v := hpv
  subst p
  apply Set.mem_iUnion₂.mpr
  refine ⟨K.incidentFace v, ?_, K.mem_faceVertices_incidentFace v⟩
  exact ⟨K.vertexPoint v,
    K.vertexPoint_in_faceCarrier (K.incidentFace v)
      (K.mem_faceVertices_incidentFace v), hpU⟩

/-! ## Cyclic data on a maximal face -/

/-- A chosen cyclic enumeration of the three vertices of a maximal face. -/
noncomputable def faceVertexEquiv (f : K.Face) : Fin 3 ≃ {v // v ∈ K.faceVertices f} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, K.faceVertices_card f])

/-- Cyclically indexed vertices of a maximal face. -/
noncomputable def faceVertex (f : K.Face) (i : ZMod 3) : K.Vertex :=
  (K.faceVertexEquiv f ((ZMod.finEquiv 3).symm i)).1

theorem faceVertex_mem (f : K.Face) (i : ZMod 3) :
    K.faceVertex f i ∈ K.faceVertices f :=
  (K.faceVertexEquiv f ((ZMod.finEquiv 3).symm i)).2

theorem faceVertex_injective (f : K.Face) : Function.Injective (K.faceVertex f) := by
  intro i j hij
  apply (ZMod.finEquiv 3).symm.injective
  apply (K.faceVertexEquiv f).injective
  exact Subtype.ext hij

theorem faceVertex_ne_next (f : K.Face) (i : ZMod 3) :
    K.faceVertex f i ≠ K.faceVertex f (i + 1) := by
  intro h
  have hi : i = i + 1 := K.faceVertex_injective f h
  have hone : (0 : ZMod 3) = 1 := by
    calc
      0 = i - i := by abel
      _ = (i + 1) - i := congrArg (fun z ↦ z - i) hi
      _ = 1 := by abel
  exact (by decide : (0 : ZMod 3) ≠ 1) hone

theorem faceVertex_ne_add_two (f : K.Face) (i : ZMod 3) :
    K.faceVertex f i ≠ K.faceVertex f (i + 2) := by
  intro h
  have hi : i = i + 2 := K.faceVertex_injective f h
  have htwo : (0 : ZMod 3) = 2 := by
    calc
      0 = i - i := by abel
      _ = (i + 2) - i := congrArg (fun z ↦ z - i) hi
      _ = 2 := by abel
  exact (by decide : (0 : ZMod 3) ≠ 2) htwo

/-! ## Edges -/

/-- A two-element vertex set contained in a maximal face. -/
def IsEdge (e : Finset K.Vertex) : Prop :=
  e.card = 2 ∧ ∃ f : K.Face, e ⊆ K.faceVertices f

/-- The edge type of a locally finite triangle complex. -/
abbrev Edge := {e : Finset K.Vertex // K.IsEdge e}

/-- The chosen first endpoint of an edge. -/
noncomputable def edgeFirst (e : K.Edge) : K.Vertex :=
  (Finset.card_eq_two.mp e.2.1).choose

/-- The chosen second endpoint of an edge. -/
noncomputable def edgeSecond (e : K.Edge) : K.Vertex :=
  (Finset.card_eq_two.mp e.2.1).choose_spec.choose

theorem edgeFirst_ne_edgeSecond (e : K.Edge) :
    K.edgeFirst e ≠ K.edgeSecond e :=
  (Finset.card_eq_two.mp e.2.1).choose_spec.choose_spec.1

theorem edge_eq_pair (e : K.Edge) :
    e.1 = {K.edgeFirst e, K.edgeSecond e} :=
  (Finset.card_eq_two.mp e.2.1).choose_spec.choose_spec.2

theorem edgeFirst_mem (e : K.Edge) : K.edgeFirst e ∈ e.1 := by
  rw [K.edge_eq_pair e]
  simp

theorem edgeSecond_mem (e : K.Edge) : K.edgeSecond e ∈ e.1 := by
  rw [K.edge_eq_pair e]
  simp

/-- The edge joining two consecutive cyclic vertices of a maximal face. -/
noncomputable def faceEdge (f : K.Face) (i : ZMod 3) : K.Edge := by
  refine ⟨{K.faceVertex f i, K.faceVertex f (i + 1)}, ?_⟩
  refine ⟨?_, f, ?_⟩
  · simp [K.faceVertex_ne_next f i]
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact K.faceVertex_mem f i
    · exact K.faceVertex_mem f (i + 1)

@[simp] theorem faceEdge_val (f : K.Face) (i : ZMod 3) :
    (K.faceEdge f i).1 = {K.faceVertex f i, K.faceVertex f (i + 1)} := rfl

/-- Consecutive face edges share exactly their common cyclic vertex. -/
theorem faceEdge_inter_next (f : K.Face) (i : ZMod 3) :
    (K.faceEdge f i).1 ∩ (K.faceEdge f (i + 1)).1 =
      {K.faceVertex f (i + 1)} := by
  ext v
  simp only [faceEdge_val, Finset.mem_inter, Finset.mem_insert,
    Finset.mem_singleton, add_assoc, one_add_one_eq_two]
  constructor
  · rintro ⟨hvi | hvi, hvnext | hvtwo⟩
    · exact (K.faceVertex_ne_next f i (hvi.symm.trans hvnext)).elim
    · exact (K.faceVertex_ne_add_two f i (hvi.symm.trans hvtwo)).elim
    · exact hvi
    · exact hvi
  · intro hv
    exact ⟨Or.inr hv, Or.inl hv⟩

theorem faceEdge_ne_next (f : K.Face) (i : ZMod 3) :
    K.faceEdge f i ≠ K.faceEdge f (i + 1) := by
  intro h
  have hval := congrArg (fun e : K.Edge ↦ e.1) h
  have hmem : K.faceVertex f i ∈ (K.faceEdge f (i + 1)).1 := by
    rw [← hval]
    simp
  simp only [faceEdge_val, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hi | hi
  · exact K.faceVertex_ne_next f i hi
  · have hz : i = i + 2 := K.faceVertex_injective f (by
        simpa only [one_add_one_eq_two, add_assoc] using hi)
    have htwo : (0 : ZMod 3) = 2 := by
      calc
        0 = i - i := by abel
        _ = (i + 2) - i := congrArg (fun z ↦ z - i) hz
        _ = 2 := by abel
    exact (by decide : (0 : ZMod 3) ≠ 2) htwo

/-- The arbitrary endpoint ordering of a cyclic face edge is one of its two cyclic
orientations. -/
theorem faceEdge_endpoint_order (f : K.Face) (i : ZMod 3) :
    (K.edgeFirst (K.faceEdge f i) = K.faceVertex f i ∧
        K.edgeSecond (K.faceEdge f i) = K.faceVertex f (i + 1)) ∨
      (K.edgeFirst (K.faceEdge f i) = K.faceVertex f (i + 1) ∧
        K.edgeSecond (K.faceEdge f i) = K.faceVertex f i) := by
  have hfirst := K.edgeFirst_mem (K.faceEdge f i)
  have hsecond := K.edgeSecond_mem (K.faceEdge f i)
  rw [K.faceEdge_val f i] at hfirst hsecond
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact (K.edgeFirst_ne_edgeSecond (K.faceEdge f i)
      (hfirst.trans hsecond.symm)).elim
  · exact Or.inl ⟨hfirst, hsecond⟩
  · exact Or.inr ⟨hfirst, hsecond⟩
  · exact (K.edgeFirst_ne_edgeSecond (K.faceEdge f i)
      (hfirst.trans hsecond.symm)).elim

/-- The standard one-simplex point at interval parameter `r`. -/
noncomputable def edgeSimplexPath (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) :
    stdSimplex ℝ {v // v ∈ e.1} := by
  let a : {v // v ∈ e.1} := ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
  let b : {v // v ∈ e.1} := ⟨K.edgeSecond e, K.edgeSecond_mem e⟩
  let x := AffineMap.lineMap (stdSimplex.vertex a : {v // v ∈ e.1} → ℝ)
    (stdSimplex.vertex b : {v // v ∈ e.1} → ℝ) r.1
  exact ⟨x, (convex_stdSimplex ℝ {v // v ∈ e.1}).lineMap_mem
    (stdSimplex.vertex a).2 (stdSimplex.vertex b).2 r.2⟩

theorem continuous_edgeSimplexPath (e : K.Edge) :
    Continuous (K.edgeSimplexPath e) := by
  apply Continuous.subtype_mk
  exact (AffineMap.lineMap (k := ℝ)
    (stdSimplex.vertex
      (⟨K.edgeFirst e, K.edgeFirst_mem e⟩ : {v // v ∈ e.1}) :
        {v // v ∈ e.1} → ℝ)
    (stdSimplex.vertex
      (⟨K.edgeSecond e, K.edgeSecond_mem e⟩ : {v // v ∈ e.1}) :
        {v // v ∈ e.1} → ℝ)).continuous_of_finiteDimensional.comp continuous_subtype_val

@[simp] theorem edgeSimplexPath_apply_first (e : K.Edge)
    (r : Set.Icc (0 : ℝ) 1) :
    K.edgeSimplexPath e r ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ = 1 - r.1 := by
  let a : {v // v ∈ e.1} := ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
  let b : {v // v ∈ e.1} := ⟨K.edgeSecond e, K.edgeSecond_mem e⟩
  have hab : a ≠ b := by
    intro h
    exact K.edgeFirst_ne_edgeSecond e (congrArg Subtype.val h)
  change (K.edgeSimplexPath e r).1 a = 1 - r.1
  dsimp only [edgeSimplexPath]
  rw [AffineMap.lineMap_apply_module]
  dsimp only [a, b] at hab ⊢
  simp [hab]

@[simp] theorem edgeSimplexPath_apply_second (e : K.Edge)
    (r : Set.Icc (0 : ℝ) 1) :
    K.edgeSimplexPath e r ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ = r.1 := by
  let a : {v // v ∈ e.1} := ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
  let b : {v // v ∈ e.1} := ⟨K.edgeSecond e, K.edgeSecond_mem e⟩
  have hab : a ≠ b := by
    intro h
    exact K.edgeFirst_ne_edgeSecond e (congrArg Subtype.val h)
  change (K.edgeSimplexPath e r).1 b = r.1
  dsimp only [edgeSimplexPath]
  rw [AffineMap.lineMap_apply_module]
  dsimp only [a, b] at hab ⊢
  simp [hab]

theorem edgeSimplexPath_injective (e : K.Edge) :
    Function.Injective (K.edgeSimplexPath e) := by
  intro r s hrs
  apply Subtype.ext
  have hcoord := congrArg
    (fun x : stdSimplex ℝ {v // v ∈ e.1} =>
      x ⟨K.edgeSecond e, K.edgeSecond_mem e⟩) hrs
  simpa using hcoord

/-- A chosen maximal face incident to an edge. -/
noncomputable def edgeFace (e : K.Edge) : K.Face :=
  Classical.choose e.2.2

theorem edge_subset_faceVertices (e : K.Edge) :
    e.1 ⊆ K.faceVertices (K.edgeFace e) :=
  Classical.choose_spec e.2.2

/-- Include edge-local vertices into a chosen incident maximal face. -/
def edgeVertexToFace (e : K.Edge) :
    {v // v ∈ e.1} → {v // v ∈ K.faceVertices (K.edgeFace e)} :=
  fun v ↦ ⟨v.1, K.edge_subset_faceVertices e v.2⟩

theorem extendFaceCoordinates_map_edgeVertexToFace (e : K.Edge)
    (x : stdSimplex ℝ {v // v ∈ e.1}) :
    extendFaceCoordinates (K.faceVertices (K.edgeFace e))
        (stdSimplex.map (K.edgeVertexToFace e) x) =
      extendFaceCoordinates e.1 x := by
  unfold edgeVertexToFace
  exact extendFaceCoordinates_map_subset (K.edge_subset_faceVertices e) x

/-- Parametrization of a closed edge by its standard one-simplex. -/
noncomputable def edgeMap (e : K.Edge) (x : stdSimplex ℝ {v // v ∈ e.1}) : S :=
  K.faceMap (K.edgeFace e) (stdSimplex.map (K.edgeVertexToFace e) x)

/-- The canonical interval parametrization of an ambient edge carrier. -/
noncomputable def edgePath (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) : S :=
  K.edgeMap e (K.edgeSimplexPath e r)

theorem edgeMap_eq_faceMap (e : K.Edge) (f : K.Face)
    (hef : e.1 ⊆ K.faceVertices f) (x : stdSimplex ℝ {v // v ∈ e.1}) :
    K.edgeMap e x = K.faceMap f
      (stdSimplex.map (fun v : {v // v ∈ e.1} ↦ ⟨v.1, hef v.2⟩) x) := by
  apply K.faceMap_eq_iff.mpr
  calc
    extendFaceCoordinates (K.faceVertices (K.edgeFace e))
        (stdSimplex.map (K.edgeVertexToFace e) x) =
        extendFaceCoordinates e.1 x := by
          exact K.extendFaceCoordinates_map_edgeVertexToFace e x
    _ = extendFaceCoordinates (K.faceVertices f)
        (stdSimplex.map (fun v : {v // v ∈ e.1} ↦ ⟨v.1, hef v.2⟩) x) :=
      (extendFaceCoordinates_map_subset hef x).symm

theorem continuous_edgeMap (e : K.Edge) : Continuous (K.edgeMap e) :=
  (K.faceMap_continuous (K.edgeFace e)).comp
    (stdSimplex.continuous_map (K.edgeVertexToFace e))

theorem continuous_edgePath (e : K.Edge) : Continuous (K.edgePath e) :=
  (K.continuous_edgeMap e).comp (K.continuous_edgeSimplexPath e)

theorem edgeMap_injective (e : K.Edge) : Function.Injective (K.edgeMap e) := by
  intro x y hxy
  have hcoords := K.faceMap_eq_iff.mp hxy
  have hcoords' : extendFaceCoordinates e.1 x = extendFaceCoordinates e.1 y := by
    calc
      extendFaceCoordinates e.1 x =
          extendFaceCoordinates (K.faceVertices (K.edgeFace e))
            (stdSimplex.map (K.edgeVertexToFace e) x) := by
        exact (K.extendFaceCoordinates_map_edgeVertexToFace e x).symm
      _ = extendFaceCoordinates (K.faceVertices (K.edgeFace e))
            (stdSimplex.map (K.edgeVertexToFace e) y) := hcoords
      _ = extendFaceCoordinates e.1 y := by
        exact K.extendFaceCoordinates_map_edgeVertexToFace e y
  apply stdSimplex.ext
  funext v
  have h := congrFun hcoords' v.1
  simpa only [extendFaceCoordinates_of_mem e.1 x v.2,
    extendFaceCoordinates_of_mem e.1 y v.2] using h

theorem edgePath_injective (e : K.Edge) : Function.Injective (K.edgePath e) :=
  (K.edgeMap_injective e).comp (K.edgeSimplexPath_injective e)

theorem range_edgeSimplexPath (e : K.Edge) :
    Set.range (K.edgeSimplexPath e) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let r : Set.Icc (0 : ℝ) 1 :=
    ⟨x ⟨K.edgeSecond e, K.edgeSecond_mem e⟩,
      mem_Icc_of_mem_stdSimplex x.2 ⟨K.edgeSecond e, K.edgeSecond_mem e⟩⟩
  refine ⟨r, ?_⟩
  apply stdSimplex.ext
  funext v
  by_cases hvFirst : v.1 = K.edgeFirst e
  · have hv : v = ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ := Subtype.ext hvFirst
    subst v
    rw [K.edgeSimplexPath_apply_first]
    have hsumPair :
        x ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ +
            x ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ = 1 := by
      let a : {v // v ∈ e.1} := ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
      let b : {v // v ∈ e.1} := ⟨K.edgeSecond e, K.edgeSecond_mem e⟩
      have hab : a ≠ b := by
        intro h
        exact K.edgeFirst_ne_edgeSecond e (congrArg Subtype.val h)
      have huniv : (Finset.univ : Finset {v // v ∈ e.1}) = {a, b} := by
        ext w
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        have hw : w.1 = K.edgeFirst e ∨ w.1 = K.edgeSecond e := by
          simpa only [K.edge_eq_pair e, Finset.mem_insert, Finset.mem_singleton] using w.2
        rcases hw with hw | hw
        · exact Or.inl (Subtype.ext hw)
        · exact Or.inr (Subtype.ext hw)
      calc
        x ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ +
            x ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ =
            ∑ w : {w // w ∈ e.1}, x w := by
              change x a + x b =
                (Finset.univ : Finset {v // v ∈ e.1}).sum (fun w => x w)
              rw [huniv]
              simp [hab]
        _ = 1 := x.2.2
    change 1 - x ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ =
      x ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
    linarith
  · have hvSecond : v.1 = K.edgeSecond e := by
      have hv : v.1 = K.edgeFirst e ∨ v.1 = K.edgeSecond e := by
        simpa only [K.edge_eq_pair e, Finset.mem_insert, Finset.mem_singleton] using v.2
      exact hv.resolve_left hvFirst
    have hv : v = ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ := Subtype.ext hvSecond
    subst v
    rw [K.edgeSimplexPath_apply_second]

/-- The ambient carrier of an edge. -/
def edgeCarrier (e : K.Edge) : Set S :=
  Set.range (K.edgeMap e)

theorem range_edgePath (e : K.Edge) :
    Set.range (K.edgePath e) = K.edgeCarrier e := by
  apply Set.Subset.antisymm
  · rintro y ⟨r, rfl⟩
    exact ⟨K.edgeSimplexPath e r, rfl⟩
  · rintro y ⟨x, rfl⟩
    have hx : x ∈ Set.range (K.edgeSimplexPath e) := by
      rw [K.range_edgeSimplexPath e]
      exact Set.mem_univ x
    obtain ⟨r, rfl⟩ := hx
    exact ⟨r, rfl⟩

theorem edgeMap_vertex_eq_vertexPoint (e : K.Edge) (v : {v // v ∈ e.1}) :
    K.edgeMap e (stdSimplex.vertex v) = K.vertexPoint v.1 := by
  rw [edgeMap, stdSimplex.map_vertex]
  exact K.faceMap_vertex_eq_vertexPoint (K.edgeFace e)
    (K.edge_subset_faceVertices e v.2)

/-- Distinct edge carriers meet only at points represented by their shared abstract vertices. -/
theorem edgeCarrier_inter_subset_sharedVertices {e d : K.Edge} (hed : e ≠ d) :
    K.edgeCarrier e ∩ K.edgeCarrier d ⊆
      {p | ∃ v : K.Vertex, v ∈ e.1 ∧ v ∈ d.1 ∧ p = K.vertexPoint v} := by
  rintro p ⟨⟨x, hxp⟩, ⟨y, hyp⟩⟩
  have hcoords₀ := K.faceMap_eq_iff.mp (hxp.trans hyp.symm)
  have hcoords : extendFaceCoordinates e.1 x = extendFaceCoordinates d.1 y := by
    calc
      extendFaceCoordinates e.1 x =
          extendFaceCoordinates (K.faceVertices (K.edgeFace e))
            (stdSimplex.map (K.edgeVertexToFace e) x) :=
        (K.extendFaceCoordinates_map_edgeVertexToFace e x).symm
      _ = extendFaceCoordinates (K.faceVertices (K.edgeFace d))
            (stdSimplex.map (K.edgeVertexToFace d) y) := hcoords₀
      _ = extendFaceCoordinates d.1 y :=
        K.extendFaceCoordinates_map_edgeVertexToFace d y
  have hex : ∃ v : {v // v ∈ e.1}, 0 < x v := by
    by_contra h
    push Not at h
    have hxzero : ∀ v : {v // v ∈ e.1}, x v = 0 := by
      intro v
      exact le_antisymm (h v) (x.2.1 v)
    have hsum : ∑ v, x v = 0 := by simp [hxzero]
    have hone : (1 : ℝ) = 0 := x.2.2.symm.trans hsum
    norm_num at hone
  obtain ⟨v, hvpos⟩ := hex
  have hvd : v.1 ∈ d.1 := by
    by_contra hvd
    have hc := congrFun hcoords v.1
    rw [extendFaceCoordinates_of_mem e.1 x v.2,
      extendFaceCoordinates_of_notMem d.1 y hvd] at hc
    linarith
  have hxzero : ∀ w : {w // w ∈ e.1}, w ≠ v → x w = 0 := by
    intro w hwv
    by_contra hxw
    have hxwpos : 0 < x w := lt_of_le_of_ne (x.2.1 w) (Ne.symm hxw)
    have hwd : w.1 ∈ d.1 := by
      by_contra hwd
      have hc := congrFun hcoords w.1
      rw [extendFaceCoordinates_of_mem e.1 x w.2,
        extendFaceCoordinates_of_notMem d.1 y hwd] at hc
      linarith
    have hvw : v.1 ≠ w.1 := by
      intro h
      exact hwv (Subtype.ext h.symm)
    let q : Finset K.Vertex := {v.1, w.1}
    have hqcard : q.card = 2 := by simp [q, hvw]
    have hqe : q ⊆ e.1 := by
      intro z hz
      simp only [q, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact v.2
      · exact w.2
    have hqd : q ⊆ d.1 := by
      intro z hz
      simp only [q, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hvd
      · exact hwd
    have hqeEq : q = e.1 :=
      Finset.eq_of_subset_of_card_le hqe (by rw [hqcard, e.2.1])
    have hqdEq : q = d.1 :=
      Finset.eq_of_subset_of_card_le hqd (by rw [hqcard, d.2.1])
    apply hed
    apply Subtype.ext
    exact hqeEq.symm.trans hqdEq
  have hxv : x v = 1 := by
    calc
      x v = ∑ w, x w := by
        rw [Finset.sum_eq_single v]
        · intro w _ hw
          exact hxzero w hw
        · simp
      _ = 1 := x.2.2
  have hxvertex : x = stdSimplex.vertex v := by
    apply stdSimplex.ext
    funext w
    by_cases hwv : w = v
    · subst w
      simp [hxv]
    · rw [hxzero w hwv]
      simp [hwv]
  refine ⟨v.1, v.2, hvd, ?_⟩
  rw [← hxp, hxvertex]
  exact K.edgeMap_vertex_eq_vertexPoint e v

theorem edgeCarrier_inter_eq_sharedVertices {e d : K.Edge} (hed : e ≠ d) :
    K.edgeCarrier e ∩ K.edgeCarrier d =
      {p | ∃ v : K.Vertex, v ∈ e.1 ∧ v ∈ d.1 ∧ p = K.vertexPoint v} := by
  apply Set.Subset.antisymm (K.edgeCarrier_inter_subset_sharedVertices hed)
  rintro p ⟨v, hve, hvd, rfl⟩
  let ve : {w // w ∈ e.1} := ⟨v, hve⟩
  let vd : {w // w ∈ d.1} := ⟨v, hvd⟩
  exact ⟨⟨stdSimplex.vertex ve, K.edgeMap_vertex_eq_vertexPoint e ve⟩,
    ⟨stdSimplex.vertex vd, K.edgeMap_vertex_eq_vertexPoint d vd⟩⟩

theorem isCompact_edgeCarrier (e : K.Edge) : IsCompact (K.edgeCarrier e) :=
  isCompact_range (K.continuous_edgeMap e)

theorem edgeCarrier_subset_faceCarrier (e : K.Edge) :
    K.edgeCarrier e ⊆ K.faceCarrier (K.edgeFace e) := by
  rintro y ⟨x, rfl⟩
  exact ⟨stdSimplex.map (K.edgeVertexToFace e) x, rfl⟩

/-- Edge carriers inherit local finiteness from the maximal-face carriers. -/
theorem locallyFinite_edgeCarriers : LocallyFinite K.edgeCarrier := by
  intro x
  obtain ⟨U, hUx, hfinite⟩ := K.locallyFinite x
  refine ⟨U, hUx, ?_⟩
  let F : Set K.Face := {f | (K.faceCarrier f ∩ U).Nonempty}
  let E : Set K.Edge := ⋃ f ∈ F,
    {e : K.Edge | e.1 ∈ (K.faceVertices f).powersetCard 2}
  have hfiber (f : K.Face) :
      ({e : K.Edge | e.1 ∈ (K.faceVertices f).powersetCard 2} : Set K.Edge).Finite := by
    change ((fun e : K.Edge ↦ e.1) ⁻¹'
      ((K.faceVertices f).powersetCard 2 : Set (Finset K.Vertex))).Finite
    exact Set.Finite.preimage Subtype.val_injective.injOn
      ((K.faceVertices f).powersetCard 2).finite_toSet
  have hEfinite : E.Finite := hfinite.biUnion fun f _ ↦ hfiber f
  apply hEfinite.subset
  intro e he
  obtain ⟨p, hpEdge, hpU⟩ := he
  apply Set.mem_iUnion₂.mpr
  refine ⟨K.edgeFace e, ?_, ?_⟩
  · exact ⟨p, K.edgeCarrier_subset_faceCarrier e hpEdge, hpU⟩
  · exact Finset.mem_powersetCard.mpr
      ⟨K.edge_subset_faceVertices e, e.2.1⟩

theorem edgeSimplexPath_zero (e : K.Edge) :
    K.edgeSimplexPath e ⟨0, by simp⟩ =
      stdSimplex.vertex ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ := by
  apply stdSimplex.ext
  let a : {v // v ∈ e.1} := ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
  let b : {v // v ∈ e.1} := ⟨K.edgeSecond e, K.edgeSecond_mem e⟩
  change AffineMap.lineMap (stdSimplex.vertex a : {v // v ∈ e.1} → ℝ)
    (stdSimplex.vertex b : {v // v ∈ e.1} → ℝ) 0 = stdSimplex.vertex a
  simp [AffineMap.lineMap_apply_module]

theorem edgeSimplexPath_one (e : K.Edge) :
    K.edgeSimplexPath e ⟨1, by simp⟩ =
      stdSimplex.vertex ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ := by
  apply stdSimplex.ext
  let a : {v // v ∈ e.1} := ⟨K.edgeFirst e, K.edgeFirst_mem e⟩
  let b : {v // v ∈ e.1} := ⟨K.edgeSecond e, K.edgeSecond_mem e⟩
  change AffineMap.lineMap (stdSimplex.vertex a : {v // v ∈ e.1} → ℝ)
    (stdSimplex.vertex b : {v // v ∈ e.1} → ℝ) 1 = stdSimplex.vertex b
  simp [AffineMap.lineMap_apply_module]

theorem edgePath_zero (e : K.Edge) :
    K.edgePath e ⟨0, by simp⟩ = K.vertexPoint (K.edgeFirst e) := by
  rw [edgePath, K.edgeSimplexPath_zero e,
    K.edgeMap_vertex_eq_vertexPoint e]

theorem edgePath_one (e : K.Edge) :
    K.edgePath e ⟨1, by simp⟩ = K.vertexPoint (K.edgeSecond e) := by
  rw [edgePath, K.edgeSimplexPath_one e,
    K.edgeMap_vertex_eq_vertexPoint e]

/-- The one-skeleton carrier of a locally finite triangle complex. -/
def oneSkeleton : Set S :=
  ⋃ e : K.Edge, K.edgeCarrier e

theorem edgeCarrier_subset_oneSkeleton (e : K.Edge) :
    K.edgeCarrier e ⊆ K.oneSkeleton :=
  Set.subset_iUnion (fun d : K.Edge ↦ K.edgeCarrier d) e

theorem locallyFinite_oneSkeleton_cover : LocallyFinite K.edgeCarrier :=
  K.locallyFinite_edgeCarriers

/-- The canonical interval parameter of a point known to lie on an edge carrier. -/
noncomputable def edgeParameter (e : K.Edge) (p : S) (hp : p ∈ K.edgeCarrier e) :
    Set.Icc (0 : ℝ) 1 :=
  Classical.choose (by rw [← K.range_edgePath e] at hp; exact hp)

theorem edgePath_edgeParameter (e : K.Edge) (p : S) (hp : p ∈ K.edgeCarrier e) :
    K.edgePath e (K.edgeParameter e p hp) = p :=
  Classical.choose_spec (by rw [← K.range_edgePath e] at hp; exact hp)

theorem edgeParameter_unique (e : K.Edge) (p : S) (hp : p ∈ K.edgeCarrier e)
    (r : Set.Icc (0 : ℝ) 1) (hr : K.edgePath e r = p) :
    K.edgeParameter e p hp = r := by
  apply K.edgePath_injective e
  rw [K.edgePath_edgeParameter e p hp, hr]

theorem vertexPoint_mem_edgeCarrier_iff (v : K.Vertex) (e : K.Edge) :
    K.vertexPoint v ∈ K.edgeCarrier e ↔ v ∈ e.1 := by
  constructor
  · rintro ⟨x, hx⟩
    have hcoords := K.faceMap_eq_iff.mp hx.symm
    rw [K.extendFaceCoordinates_map_edgeVertexToFace e x,
      K.extendFaceCoordinates_vertex (K.incidentFace v)
        (K.mem_faceVertices_incidentFace v)] at hcoords
    by_contra hve
    have h := congrFun hcoords v
    simp [extendFaceCoordinates, hve] at h
  · intro hve
    let w : {w // w ∈ e.1} := ⟨v, hve⟩
    exact ⟨stdSimplex.vertex w, K.edgeMap_vertex_eq_vertexPoint e w⟩

@[simp] theorem edgeParameter_vertexPoint_first (e : K.Edge) :
    K.edgeParameter e (K.vertexPoint (K.edgeFirst e))
      ((K.vertexPoint_mem_edgeCarrier_iff (K.edgeFirst e) e).mpr (K.edgeFirst_mem e)) =
        ⟨0, by simp⟩ := by
  apply K.edgeParameter_unique
  exact K.edgePath_zero e

@[simp] theorem edgeParameter_vertexPoint_second (e : K.Edge) :
    K.edgeParameter e (K.vertexPoint (K.edgeSecond e))
      ((K.vertexPoint_mem_edgeCarrier_iff (K.edgeSecond e) e).mpr (K.edgeSecond_mem e)) =
        ⟨1, by simp⟩ := by
  apply K.edgeParameter_unique
  exact K.edgePath_one e

theorem disjoint_vertexPoint_edgeCarrier {v : K.Vertex} {e : K.Edge}
    (hve : v ∉ e.1) : Disjoint ({K.vertexPoint v} : Set S) (K.edgeCarrier e) := by
  rw [Set.disjoint_singleton_left]
  exact fun h ↦ hve ((K.vertexPoint_mem_edgeCarrier_iff v e).mp h)

theorem isClosed_edgeCarrier [T2Space S] (e : K.Edge) : IsClosed (K.edgeCarrier e) :=
  (K.isCompact_edgeCarrier e).isClosed

/-- The interval parametrization with codomain restricted to the edge carrier. -/
noncomputable def edgePathToCarrier (e : K.Edge) :
    Set.Icc (0 : ℝ) 1 → K.edgeCarrier e :=
  fun r ↦ ⟨K.edgePath e r, by rw [← K.range_edgePath e]; exact Set.mem_range_self r⟩

theorem continuous_edgePathToCarrier (e : K.Edge) :
    Continuous (K.edgePathToCarrier e) := by
  apply Continuous.subtype_mk
  exact K.continuous_edgePath e

theorem edgePathToCarrier_injective (e : K.Edge) :
    Function.Injective (K.edgePathToCarrier e) := by
  intro r s hrs
  apply K.edgePath_injective e
  exact congrArg Subtype.val hrs

theorem edgePathToCarrier_surjective (e : K.Edge) :
    Function.Surjective (K.edgePathToCarrier e) := by
  rintro ⟨p, hp⟩
  rw [← K.range_edgePath e] at hp
  obtain ⟨r, rfl⟩ := hp
  exact ⟨r, rfl⟩

/-- Every closed edge carrier is canonically homeomorphic to the unit interval. -/
noncomputable def edgePathHomeomorph [T2Space S] (e : K.Edge) :
    Set.Icc (0 : ℝ) 1 ≃ₜ K.edgeCarrier e :=
  ((K.continuous_edgePathToCarrier e).isClosedEmbedding
    (K.edgePathToCarrier_injective e)).isEmbedding.toHomeomorphOfSurjective
      (K.edgePathToCarrier_surjective e)

@[simp] theorem edgePathHomeomorph_apply [T2Space S] (e : K.Edge)
    (r : Set.Icc (0 : ℝ) 1) :
    (K.edgePathHomeomorph e r).1 = K.edgePath e r := rfl

theorem edgePathHomeomorph_symm_val [T2Space S] (e : K.Edge)
    (p : K.edgeCarrier e) :
    K.edgePath e ((K.edgePathHomeomorph e).symm p) = p.1 := by
  exact congrArg Subtype.val ((K.edgePathHomeomorph e).apply_symm_apply p)

/-- The union of all edges not incident to a fixed vertex is closed. -/
theorem isClosed_iUnion_edgeCarrier_notMem [T2Space S] (v : K.Vertex) :
    IsClosed (⋃ e : {e : K.Edge // v ∉ e.1}, K.edgeCarrier e.1) := by
  apply (K.locallyFinite_edgeCarriers.comp_injective Subtype.val_injective).isClosed_iUnion
  intro e
  exact K.isClosed_edgeCarrier e.1

theorem vertexPoint_not_mem_iUnion_edgeCarrier_notMem (v : K.Vertex) :
    K.vertexPoint v ∉ ⋃ e : {e : K.Edge // v ∉ e.1}, K.edgeCarrier e.1 := by
  intro hv
  obtain ⟨e, hve⟩ := Set.mem_iUnion.mp hv
  exact e.2 ((K.vertexPoint_mem_edgeCarrier_iff v e.1).mp hve)

/-- Local finiteness on a compact ambient space makes the type of maximal faces finite. -/
@[implicit_reducible] noncomputable def faceFintype [CompactSpace S] : Fintype K.Face :=
  K.locallyFinite.fintypeOfCompact K.faceCarrier_nonempty

/-- If the face type is finite and every vertex is used, then the global vertex type is finite. -/
theorem finite_vertex [Finite K.Face] : Finite K.Vertex := by
  apply Finite.of_finite_univ
  have hrepr : (Set.univ : Set K.Vertex) = ⋃ f : K.Face, (K.faceVertices f : Set K.Vertex) := by
    ext v
    simp only [Set.mem_univ, Set.mem_iUnion, Finset.mem_coe, true_iff]
    exact K.vertex_used v
  rw [hrepr]
  exact Set.finite_iUnion fun f ↦ (K.faceVertices f).finite_toSet

/-- The finite vertex instance induced by compactness and the no-junk-vertices condition. -/
@[implicit_reducible] noncomputable def vertexFintype [CompactSpace S] : Fintype K.Vertex := by
  letI : Fintype K.Face := K.faceFintype
  letI : Finite K.Vertex := K.finite_vertex
  exact Fintype.ofFinite K.Vertex

/-- The `compactFaceFintype` declaration. -/
noncomputable local instance compactFaceFintype [CompactSpace S] : Fintype K.Face :=
  K.faceFintype

/-- The `compactVertexFintype` declaration. -/
noncomputable local instance compactVertexFintype [CompactSpace S] : Fintype K.Vertex :=
  K.vertexFintype

/-- The finite intrinsic complex obtained from a compact locally finite triangle complex. -/
noncomputable def compactIntrinsic [CompactSpace S] : IntrinsicTwoComplex := by
  letI : Fintype K.Face := K.faceFintype
  letI : Fintype K.Vertex := K.vertexFintype
  exact
    { Vertex := K.Vertex
      faces := Finset.univ.image K.faceVertices
      faces_card := by
        intro t ht
        obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp ht
        exact K.faceVertices_card f }

@[simp] theorem compactIntrinsic_faces [CompactSpace S] :
    K.compactIntrinsic.faces = by
      letI : Fintype K.Face := K.faceFintype
      exact Finset.univ.image K.faceVertices := rfl

theorem compactIntrinsic_face_mem [CompactSpace S] (f : K.Face) :
    K.faceVertices f ∈ K.compactIntrinsic.faces := by
  let : Fintype K.Face := K.faceFintype
  exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩

/-- Restrict a global standard-simplex point supported on `t` to the coordinates indexed by
`t`. -/
noncomputable def restrictToFace [Fintype K.Vertex] (t : Finset K.Vertex)
    (x : stdSimplex ℝ K.Vertex) (hx : ∀ v ∉ t, x v = 0) :
    stdSimplex ℝ {v // v ∈ t} := by
  refine ⟨fun v ↦ x v.1, fun v ↦ x.2.1 v.1, ?_⟩
  calc
    ∑ v : {v // v ∈ t}, x v.1 = ∑ v ∈ t, x v := by
      exact Finset.sum_coe_sort t fun v ↦ x v
    _ = ∑ v, x v := by
      apply Finset.sum_subset (Finset.subset_univ t)
      intro v _ hv
      exact hx v hv
    _ = 1 := x.2.2

theorem extendFaceCoordinates_restrictToFace [Fintype K.Vertex]
    (t : Finset K.Vertex) (x : stdSimplex ℝ K.Vertex)
    (hx : ∀ v ∉ t, x v = 0) :
    extendFaceCoordinates t (K.restrictToFace t x hx) = x := by
  funext v
  by_cases hv : v ∈ t
  · rw [extendFaceCoordinates_of_mem t _ hv]
    rfl
  · simp [extendFaceCoordinates, hv, hx v hv]

/-- Every point of the compact realization is supported on one of the original maximal faces. -/
theorem exists_containingFace [CompactSpace S]
    (x : K.compactIntrinsic.realization) :
    ∃ f : K.Face, ∀ v ∉ K.faceVertices f, x.1 v = 0 := by
  let : Fintype K.Face := K.faceFintype
  let : Fintype K.Vertex := K.vertexFintype
  rcases x.2.2 with ⟨t, ht, hxt⟩
  obtain ⟨f, -, hft⟩ := Finset.mem_image.mp ht
  subst hft
  exact ⟨f, hxt⟩

/-- A canonical maximal face containing a point of the compact realization. -/
noncomputable def containingFace [CompactSpace S]
    (x : K.compactIntrinsic.realization) : K.Face :=
  Classical.choose (K.exists_containingFace x)

theorem supported_on_containingFace [CompactSpace S]
    (x : K.compactIntrinsic.realization) :
    ∀ v ∉ K.faceVertices (K.containingFace x), x.1 v = 0 := by
  exact Classical.choose_spec (K.exists_containingFace x)

/-- Evaluation of the compact barycentric realization through the locally finite face maps. -/
noncomputable def compactEval [CompactSpace S]
    (x : K.compactIntrinsic.realization) : S := by
  letI : Fintype K.Face := K.faceFintype
  letI : Fintype K.Vertex := K.vertexFintype
  exact K.faceMap (K.containingFace x)
    (K.restrictToFace _ ⟨x.1, x.2.1⟩ (K.supported_on_containingFace x))

theorem compactEval_eq_faceMap [CompactSpace S]
    (f : K.Face) (x : K.compactIntrinsic.realization)
    (hx : ∀ v ∉ K.faceVertices f, x.1 v = 0) :
    K.compactEval x =
      K.faceMap f (K.restrictToFace (K.faceVertices f) ⟨x.1, x.2.1⟩ hx) := by
  let : Fintype K.Face := K.faceFintype
  let : Fintype K.Vertex := K.vertexFintype
  apply K.faceMap_eq_iff.mpr
  rw [K.extendFaceCoordinates_restrictToFace,
    K.extendFaceCoordinates_restrictToFace]

private theorem continuous_faceRestriction [CompactSpace S] (f : K.Face) :
    Continuous fun x :
      {x : K.compactIntrinsic.realization //
        x ∈ K.compactIntrinsic.faceCarrier (K.faceVertices f)} ↦
      K.restrictToFace (K.faceVertices f) ⟨x.1.1, x.1.2.1⟩ x.2 := by
  let : Fintype K.Face := K.faceFintype
  let : Fintype K.Vertex := K.vertexFintype
  apply Continuous.subtype_mk
  have houter : Continuous fun x :
      {x : K.compactIntrinsic.realization //
        x ∈ K.compactIntrinsic.faceCarrier (K.faceVertices f)} ↦ x.1 :=
    continuous_subtype_val
  have hinner : Continuous fun x : K.compactIntrinsic.realization ↦ x.1 :=
    continuous_subtype_val
  exact continuous_pi fun v ↦ (continuous_apply v.1).comp (hinner.comp houter)

theorem continuous_compactEval [CompactSpace S] : Continuous K.compactEval := by
  let : Fintype K.Face := K.faceFintype
  let : Fintype K.Vertex := K.vertexFintype
  let carriers : K.Face → Set K.compactIntrinsic.realization :=
    fun f ↦ K.compactIntrinsic.faceCarrier (K.faceVertices f)
  have hclosed : ∀ f, IsClosed (carriers f) :=
    fun f ↦ K.compactIntrinsic.faceCarrier_closed (K.faceVertices f)
  have hcover : (Set.univ : Set K.compactIntrinsic.realization) = ⋃ f, carriers f := by
    rw [K.compactIntrinsic.realization_eq_iUnion_faceCarrier]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨t, hxt⟩
      obtain ⟨f, -, hft⟩ := Finset.mem_image.mp t.2
      refine ⟨f, ?_⟩
      simpa only [carriers, hft] using hxt
    · rintro ⟨f, hxf⟩
      exact ⟨⟨K.faceVertices f, K.compactIntrinsic_face_mem f⟩, hxf⟩
  have hlocal : ∀ f, ContinuousOn K.compactEval (carriers f) := by
    intro f
    rw [continuousOn_iff_continuous_domRestrict]
    have hc := (K.faceMap_continuous f).comp (K.continuous_faceRestriction f)
    convert hc using 1
    funext x
    exact K.compactEval_eq_faceMap f x.1 x.2
  exact (locallyFinite_of_finite carriers).continuous hcover.symm hclosed hlocal

theorem injective_compactEval [CompactSpace S] : Function.Injective K.compactEval := by
  let : Fintype K.Face := K.faceFintype
  let : Fintype K.Vertex := K.vertexFintype
  intro x y hxy
  have hcoeff := K.faceMap_eq_iff.mp hxy
  rw [K.extendFaceCoordinates_restrictToFace,
    K.extendFaceCoordinates_restrictToFace] at hcoeff
  exact Subtype.ext hcoeff

/-- The compact evaluation has exactly the ambient support of the locally finite complex as its
range. -/
theorem range_compactEval [CompactSpace S] : Set.range K.compactEval = K.support := by
  let : Fintype K.Face := K.faceFintype
  let : Fintype K.Vertex := K.vertexFintype
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    refine Set.mem_iUnion.mpr ⟨K.containingFace x, ?_⟩
    exact ⟨K.restrictToFace _ ⟨x.1, x.2.1⟩ (K.supported_on_containingFace x), rfl⟩
  · intro y hy
    obtain ⟨f, z, rfl⟩ := Set.mem_iUnion.mp hy
    let x0 : stdSimplex ℝ K.Vertex := stdSimplex.map Subtype.val z
    have hxSupport : ∀ v ∉ K.faceVertices f, x0 v = 0 := by
      intro v hv
      simp only [x0, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
      have hempty :
          Finset.univ.filter (fun w : {w // w ∈ K.faceVertices f} ↦ w.1 = v) = ∅ := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        exact fun hw ↦ hv (hw ▸ w.2)
      rw [hempty]
      simp
    let x : K.compactIntrinsic.realization :=
      ⟨x0, x0.2, ⟨K.faceVertices f, K.compactIntrinsic_face_mem f, hxSupport⟩⟩
    refine ⟨x, ?_⟩
    rw [K.compactEval_eq_faceMap f x hxSupport]
    apply congrArg (K.faceMap f)
    ext w
    change x0 w.1 = z w
    simp only [x0, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hfilter :
        Finset.univ.filter
          (fun q : {q // q ∈ K.faceVertices f} ↦ q.1 = w.1) = {w} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact Subtype.ext_iff.symm
    rw [hfilter]
    simp

/-- A locally finite triangle complex covering a compact Hausdorff space is an honest finite
geometric triangulation. -/
noncomputable def toGeometricTriangulation [CompactSpace S] [T2Space S]
    (hcovers : K.support = Set.univ) : GeometricTriangulation S := by
  letI : Fintype K.Face := K.faceFintype
  letI : Fintype K.Vertex := K.vertexFintype
  let e : K.compactIntrinsic.realization ≃ S :=
    Equiv.ofBijective K.compactEval ⟨K.injective_compactEval, by
      intro y
      have hy : y ∈ K.support := by rw [hcovers]; exact Set.mem_univ y
      rw [← K.range_compactEval] at hy
      exact hy⟩
  exact
    { Vertex := K.compactIntrinsic.Vertex
      faces := K.compactIntrinsic.faces
      faces_card := K.compactIntrinsic.faces_card
      homeo := Continuous.homeoOfEquivCompactToT2 (f := e) K.continuous_compactEval }

/-! ## Finite complexes on their own support -/

/-- Regard a finite ambient triangle complex as a complex whose ambient space is exactly its
support.  This is the finite gluing bridge used in the Rado induction: once a compatible finite
family of old and new triangles has been assembled, no separate ambient coverage proof is
needed. -/
noncomputable def onSupport [Finite K.Face] :
    LocallyFiniteTriangleComplex K.support where
  Vertex := K.Vertex
  Face := K.Face
  faceVertices := K.faceVertices
  faceVertices_card := K.faceVertices_card
  vertex_used := K.vertex_used
  faceMap := fun f x => ⟨K.faceMap f x,
    Set.mem_iUnion.mpr ⟨f, Set.mem_range_self x⟩⟩
  faceMap_continuous := fun f => by
    apply Continuous.subtype_mk
    exact K.faceMap_continuous f
  faceMap_eq_iff := by
    intro f g x y
    rw [Subtype.ext_iff]
    exact K.faceMap_eq_iff
  locallyFinite := locallyFinite_of_finite _

@[simp] theorem onSupport_faceVertices [Finite K.Face] (f : K.Face) :
    K.onSupport.faceVertices f = K.faceVertices f := rfl

@[simp] theorem onSupport_faceMap_val [Finite K.Face] (f : K.Face)
    (x : stdSimplex ℝ {v // v ∈ K.faceVertices f}) :
    (K.onSupport.faceMap f x).1 = K.faceMap f x := rfl

/-- The support-restricted complex covers its ambient support subtype. -/
theorem onSupport_support [Finite K.Face] : K.onSupport.support = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨p, hp⟩
  obtain ⟨f, hpf⟩ := Set.mem_iUnion.mp hp
  obtain ⟨x, rfl⟩ := hpf
  exact Set.mem_iUnion.mpr ⟨f, ⟨x, rfl⟩⟩

/-- A finite ambient triangle complex has compact support, independently of compactness of the
ambient space. -/
theorem isCompact_support_of_finite [Finite K.Face] : IsCompact K.support := by
  let : Fintype K.Face := Fintype.ofFinite K.Face
  exact isCompact_iUnion fun f => K.isCompact_faceCarrier f

/-- A finite compatible triangle family triangulates its own support. -/
noncomputable def finiteSupportGeometricTriangulation [Finite K.Face] [T2Space S] :
    GeometricTriangulation K.support := by
  letI : CompactSpace K.support :=
    isCompact_iff_compactSpace.mp K.isCompact_support_of_finite
  exact K.onSupport.toGeometricTriangulation K.onSupport_support

end LocallyFiniteTriangleComplex

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

/-- Include the standard simplex on one maximal face into the global barycentric realization. -/
noncomputable def faceStandardMap (t : K.Face)
    (x : stdSimplex ℝ {v // v ∈ t.1}) : K.realization := by
  let x0 : stdSimplex ℝ K.Vertex := stdSimplex.map Subtype.val x
  have hxSupport : ∀ v ∉ t.1, x0 v = 0 := by
    intro v hv
    simp only [x0, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hempty :
        Finset.univ.filter (fun w : {w // w ∈ t.1} ↦ w.1 = v) = ∅ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      exact fun hw ↦ hv (hw ▸ w.2)
    rw [hempty]
    simp
  exact ⟨x0, x0.2, ⟨t.1, t.2, hxSupport⟩⟩

/-- Restrict an intrinsic realization point supported on one maximal face to that face's
standard simplex. -/
noncomputable def restrictToFaceSimplex (t : K.Face) (x : K.realization)
    (hx : ∀ v ∉ t.1, x.1 v = 0) :
    stdSimplex ℝ {v // v ∈ t.1} := by
  refine ⟨fun v ↦ x.1 v.1, fun v ↦ x.2.1.1 v.1, ?_⟩
  calc
    ∑ v : {v // v ∈ t.1}, x.1 v.1 = ∑ v ∈ t.1, x.1 v := by
      exact Finset.sum_coe_sort t.1 fun v ↦ x.1 v
    _ = ∑ v, x.1 v := by
      apply Finset.sum_subset (Finset.subset_univ t.1)
      intro v _ hv
      exact hx v hv
    _ = 1 := x.2.1.2

theorem faceStandardMap_val (t : K.Face)
    (x : stdSimplex ℝ {v // v ∈ t.1}) :
    (K.faceStandardMap t x).1 = extendFaceCoordinates t.1 x := by
  funext v
  by_cases hv : v ∈ t.1
  · let w : {w // w ∈ t.1} := ⟨v, hv⟩
    change (stdSimplex.map Subtype.val x : K.Vertex → ℝ) v = _
    rw [extendFaceCoordinates_of_mem t.1 x hv]
    simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hfilter :
        Finset.univ.filter (fun q : {q // q ∈ t.1} ↦ q.1 = v) = {w} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h ↦ Subtype.ext h
      · exact fun h ↦ congrArg Subtype.val h
    rw [hfilter]
    simp [w]
  · change (stdSimplex.map Subtype.val x : K.Vertex → ℝ) v = _
    rw [extendFaceCoordinates_of_notMem t.1 x hv]
    simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hempty :
        Finset.univ.filter (fun w : {w // w ∈ t.1} ↦ w.1 = v) = ∅ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      exact fun hw ↦ hv (hw ▸ w.2)
    rw [hempty]
    simp

theorem faceStandardMap_restrictToFaceSimplex (t : K.Face) (x : K.realization)
    (hx : ∀ v ∉ t.1, x.1 v = 0) :
    K.faceStandardMap t (K.restrictToFaceSimplex t x hx) = x := by
  apply Subtype.ext
  rw [K.faceStandardMap_val]
  funext v
  by_cases hv : v ∈ t.1
  · rw [extendFaceCoordinates_of_mem _ _ hv]
    rfl
  · rw [extendFaceCoordinates_of_notMem _ _ hv, hx v hv]

theorem continuous_faceStandardMap (t : K.Face) : Continuous (K.faceStandardMap t) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp (stdSimplex.continuous_map Subtype.val)

/-- Regard a finite intrinsic complex with no unused vertices as a locally finite ambient
triangle complex. -/
noncomputable def toLocallyFiniteTriangleComplex {S : Type*} [TopologicalSpace S]
    (hused : ∀ v : K.Vertex, ∃ t ∈ K.faces, v ∈ t)
    (e : K.realization → S) (he : _root_.Topology.IsEmbedding e) :
    LocallyFiniteTriangleComplex S where
  Vertex := K.Vertex
  Face := K.Face
  faceVertices := fun t ↦ t.1
  faceVertices_card := fun t ↦ K.faces_card t.1 t.2
  vertex_used := by
    intro v
    obtain ⟨t, ht, hvt⟩ := hused v
    exact ⟨⟨t, ht⟩, hvt⟩
  faceMap := fun t x ↦ e (K.faceStandardMap t x)
  faceMap_continuous := fun t ↦ he.continuous.comp (K.continuous_faceStandardMap t)
  faceMap_eq_iff := by
    intro f g x y
    constructor
    · intro hxy
      have hsource : K.faceStandardMap f x = K.faceStandardMap g y := he.injective hxy
      rw [← K.faceStandardMap_val f x, ← K.faceStandardMap_val g y]
      exact congrArg Subtype.val hsource
    · intro hxy
      apply congrArg e
      apply Subtype.ext
      simpa only [K.faceStandardMap_val] using hxy
  locallyFinite := locallyFinite_of_finite _

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
