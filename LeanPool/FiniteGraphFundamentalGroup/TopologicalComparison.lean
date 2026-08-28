/-
Copyright (c) 2026 Arthur Freitas Ramos, David Hulak, Ruy de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Hulak, Ruy de Queiroz
-/

import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.GroupTheory.FreeGroup.Reduce
import LeanPool.FiniteGraphFundamentalGroup.Cover
import LeanPool.FiniteGraphFundamentalGroup.Realization
import LeanPool.FiniteGraphFundamentalGroup.TopologicalCover
import LeanPool.FiniteGraphFundamentalGroup.TreeContraction
import LeanPool.FiniteGraphFundamentalGroup.Consequences

/-!
# Comparison of combinatorial and topological fundamental groups

This module identifies the free-groupoid computation with the fundamental group of the realization.
-/

attribute [local implicit_reducible]
  Quiver.Symmetrify Quiver.FreeGroupoid Quiver.FreeGroupoid.of IsFreeGroupoid.Generators
  WideSubquiver WideSubquiver.toType WideSubquiver.quiver IsFreeGroupoid.quiverGenerators
  Quiver.symmetrifyQuiver Quiver.wideSubquiverSymmetrify

open Set Function
open CategoryTheory CategoryTheory.SingleObj Quiver
open unitInterval
open ContinuousMap

noncomputable section

universe u

namespace FiniteGraphFreeGroup

variable {V : Type u} [Quiver.{u} V]

/-- Evaluates a symmetric path in the canonical cover as a base free-groupoid morphism. -/
def coverSymPathValue {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    (graphCoverSymmetricFreeGroupoidMap root).obj a ⟶
      (graphCoverSymmetricFreeGroupoidMap root).obj b :=
  (CategoryTheory.Paths.lift (graphCoverSymmetricFreeGroupoidMap root)).map p

theorem coverSymPathValue_cons {root : V}
    {a b c : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b)
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) b c) :
    coverSymPathValue (@Quiver.Path.cons (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) _ _ _ p e) =
      coverSymPathValue p ≫ (graphCoverSymmetricFreeGroupoidMap root).map e := by
  exact CategoryTheory.Paths.lift_cons (graphCoverSymmetricFreeGroupoidMap root) p e

theorem graphCoverSymmetricFreeGroupoidMap_endpoint {root : V}
    {y z : Symmetrify (graphCoverVertex root)}
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) y z) :
    (z : graphCoverVertex root).2 =
      (y : graphCoverVertex root).2 ≫
        (graphCoverSymmetricFreeGroupoidMap root).map e := by
  change graphCoverVertex root at y z
  cases e with
  | inl e =>
      exact e.property.symm
  | inr e =>
      change z.2 = y.2 ≫ Groupoid.inv ((Quiver.FreeGroupoid.of V).map e.1)
      simpa only [Groupoid.inv_eq_inv] using (IsIso.eq_comp_inv _).2 e.property

theorem coverSymPathValue_endpoint {root : V} (x : graphCoverVertex root)
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) x) :
    x.2 = coverSymPathValue p := by
  induction p using
      (@Quiver.Path.rec (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))) with
  | nil =>
      rfl
  | @cons y z p e ih =>
      change graphCoverVertex root at y z
      rw [coverSymPathValue_cons]
      exact (graphCoverSymmetricFreeGroupoidMap_endpoint e).trans
        (congrArg (fun q => q ≫ (graphCoverSymmetricFreeGroupoidMap root).map e) ih)

/-- Evaluates a symmetric path in the base graph's free groupoid. -/
abbrev baseSymPathValue {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) a b) :
    (Quiver.FreeGroupoid.of V).obj a ⟶ (Quiver.FreeGroupoid.of V).obj b :=
  Quot.mk _ p

theorem coverSymPathValue_eq_baseSymPathValue {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    coverSymPathValue p =
      baseSymPathValue ((graphCoverProjection root).symmetrify.mapPath p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [coverSymPathValue_cons, ih]
      cases e <;> rfl
/-- Sends every graph edge to its generator in the free group on total edges. -/
def graphFreeGroupPrefunctor {V : Type u} [Quiver.{u} V] :
    V ⥤q CategoryTheory.SingleObj (FreeGroup (Quiver.Total V)) where
  obj _ := ()
  map e := FreeGroup.of ⟨_, _, e⟩

/-- Extracts the monoid value represented by a morphism in a one-object category. -/
abbrev singleObjHomValue {M : Type u}
    {x y : CategoryTheory.SingleObj M} (f : x ⟶ y) : M := f

/-- The functor from the free graph groupoid to the free group on total edges. -/
abbrev graphFreeGroupoidToFreeGroup {V : Type u} [Quiver.{u} V] :
    Quiver.FreeGroupoid V ⥤ CategoryTheory.SingleObj (FreeGroup (Quiver.Total V)) :=
  Quiver.FreeGroupoid.lift (graphFreeGroupPrefunctor (V := V))

/-- The signed base-edge letter represented by an edge of the symmetric cover. -/
def coverSymEdgeLetter {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    Quiver.Total V × Bool := by
  cases e with
  | inl e => exact (⟨_, _, e.1⟩, true)
  | inr e => exact (⟨_, _, e.1⟩, false)

/-- The signed base-edge word represented by a path in the symmetric cover. -/
def coverSymPathWord {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    List (Quiver.Total V × Bool) := by
  induction p with
  | nil => exact []
  | cons p e ih => exact coverSymEdgeLetter e :: ih

theorem coverSymPathWord_cons {root : V}
    {a b c : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b)
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) b c) :
    coverSymPathWord
      (@Quiver.Path.cons (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root)) _ _ _ p e) =
      coverSymEdgeLetter e :: coverSymPathWord p := by
  rfl

/-- Paths in a symmetrified quiver that never immediately traverse an edge and its reverse. -/
inductive symPathNoBacktrack {W : Type u} [Quiver.{u} W]
    {a : Symmetrify W} : ∀ {b : Symmetrify W},
      @Quiver.Path (Symmetrify W) (Quiver.symmetrifyQuiver W) a b → Prop
  | nil : symPathNoBacktrack
      (@Quiver.Path.nil (Symmetrify W) (Quiver.symmetrifyQuiver W) a)
  | cons {b c : Symmetrify W}
      (p : @Quiver.Path (Symmetrify W) (Quiver.symmetrifyQuiver W) a b)
      (e : @Quiver.Hom (Symmetrify W) (Quiver.symmetrifyQuiver W) b c) :
      symPathNoBacktrack p →
      (∀ {d : Symmetrify W}
        (q : @Quiver.Path (Symmetrify W) (Quiver.symmetrifyQuiver W) a d)
        (f : @Quiver.Hom (Symmetrify W) (Quiver.symmetrifyQuiver W) d b),
        p = @Quiver.Path.cons (Symmetrify W) (Quiver.symmetrifyQuiver W)
          _ _ _ q f →
          (⟨b, c, e⟩ : Quiver.Total (Symmetrify W)) ≠
            ⟨b, d, Quiver.reverse f⟩) →
      symPathNoBacktrack
        (@Quiver.Path.cons (Symmetrify W) (Quiver.symmetrifyQuiver W)
          _ _ _ p e)

theorem symPathNoBacktrack_of_shortest {W : Type u} [Quiver.{u} W]
    {r a : Symmetrify W}
    (p : @Quiver.Path (Symmetrify W) (Quiver.symmetrifyQuiver W) r a)
    (hshort : ∀ q : @Quiver.Path (Symmetrify W)
      (Quiver.symmetrifyQuiver W) r a, p.length ≤ q.length) :
    symPathNoBacktrack p := by
  induction p using
      (@Quiver.Path.rec (Symmetrify W) (Quiver.symmetrifyQuiver W)) with
  | nil =>
      exact symPathNoBacktrack.nil
  | @cons b c p e ih =>
      apply symPathNoBacktrack.cons p e
      · apply ih
        intro q
        have h := hshort
          (@Quiver.Path.cons (Symmetrify W) (Quiver.symmetrifyQuiver W)
            _ _ _ q e)
        simp only [Quiver.Path.length_cons] at h ⊢
        omega
      · intro d q f hpq hcancel
        have hc : c = d := congrArg Quiver.Total.right hcancel
        cases hc
        have h := hshort q
        rw [hpq] at h
        simp only [Quiver.Path.length_cons] at h
        omega

theorem coverSymEdgeLetter_cancel {root : V}
    {a b c : Symmetrify (graphCoverVertex root)}
    (f : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b)
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) b c)
    (hbase : (coverSymEdgeLetter e).1 = (coverSymEdgeLetter f).1)
    (hbool : (coverSymEdgeLetter e).2 = !(coverSymEdgeLetter f).2) :
    (⟨b, c, e⟩ : Quiver.Total (Symmetrify (graphCoverVertex root))) =
      ⟨b, a, Quiver.reverse f⟩ := by
  change graphCoverVertex root at a b c
  cases e with
  | inl e =>
      cases f with
      | inl f => simp [coverSymEdgeLetter] at hbool
      | inr f =>
          have htot :
              (⟨b.1, c.1, e.1⟩ : Quiver.Total V) =
                ⟨b.1, a.1, f.1⟩ := by
            simpa [coverSymEdgeLetter] using hbase
          have hstar := graphCoverStarEquiv_map_eq_of_total_eq
            b ⟨b, c, e⟩ ⟨b, a, f⟩ rfl rfl htot
          have hstar' := (graphCoverStarEquiv root b).injective hstar
          have htotal := graphCover_total_eq_of_star_eq
            b ⟨b, c, e⟩ ⟨b, a, f⟩ rfl rfl hstar'
          cases htotal
          rfl
  | inr e =>
      cases f with
      | inr f => simp [coverSymEdgeLetter] at hbool
      | inl f =>
          have htot :
              (⟨c.1, b.1, e.1⟩ : Quiver.Total V) =
                ⟨a.1, b.1, f.1⟩ := by
            simpa [coverSymEdgeLetter] using hbase
          have hcostar := graphCoverCostarEquiv_map_eq_of_total_eq
            b ⟨c, b, e⟩ ⟨a, b, f⟩ rfl rfl htot
          have hcostar' := (graphCoverCostarEquiv root b).injective hcostar
          have htotal := graphCover_total_eq_of_costar_eq
            b ⟨c, b, e⟩ ⟨a, b, f⟩ rfl rfl hcostar'
          cases htotal
          rfl

theorem coverSymPathWord_isReduced {root : V}
    {a : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a)
    (hp : symPathNoBacktrack p) :
    FreeGroup.IsReduced (coverSymPathWord p) := by
  induction hp with
  | nil =>
      exact FreeGroup.IsReduced.nil
  | @cons b c p e hp hlast ih =>
      rw [coverSymPathWord_cons]
      cases p with
      | nil =>
          exact FreeGroup.IsReduced.singleton
      | @cons d b q f =>
          rw [coverSymPathWord_cons]
          rw [FreeGroup.isReduced_cons_cons]
          constructor
          · intro hbase
            by_contra hbool
            have hopp : (coverSymEdgeLetter e).2 =
                !(coverSymEdgeLetter f).2 := Bool.eq_not_iff.mpr hbool
            have htotal := coverSymEdgeLetter_cancel f e hbase hopp
            exact hlast q f rfl htotal
          · exact ih

/-- Evaluates a symmetric cover path in the free group on base edges. -/
abbrev coverFreeGroupValue {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    FreeGroup (Quiver.Total V) :=
  singleObjHomValue ((graphFreeGroupoidToFreeGroup (V := V)).map
    (coverSymPathValue p))

theorem coverFreeGroupValue_nil {root : V} (x : graphCoverVertex root) :
    coverFreeGroupValue
      (Quiver.Path.nil : @Quiver.Path (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root)) x x) = 1 := by
  change (1 : FreeGroup (Quiver.Total V)) = 1
  rfl

theorem coverFreeGroupValue_cons {root : V}
    {a b c : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b)
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) b c) :
    coverFreeGroupValue (@Quiver.Path.cons (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) _ _ _ p e) =
      singleObjHomValue ((graphFreeGroupoidToFreeGroup (V := V)).map
          ((graphCoverSymmetricFreeGroupoidMap root).map e)) *
        coverFreeGroupValue p := by
  unfold coverFreeGroupValue
  rw [coverSymPathValue_cons, Functor.map_comp, SingleObj.comp_as_mul]

theorem graphFreeGroupoidToFreeGroup_map_pos {V : Type u} [Quiver.{u} V]
    (e : Quiver.Total V) :
    singleObjHomValue ((graphFreeGroupoidToFreeGroup (V := V)).map
      ((Quiver.FreeGroupoid.of V).map e.hom)) =
      FreeGroup.of e := by
  change (Quiver.FreeGroupoid.lift (graphFreeGroupPrefunctor (V := V))).map
      ((Quiver.FreeGroupoid.of V).map e.hom) =
      (graphFreeGroupPrefunctor (V := V)).map e.hom
  have h := Quiver.FreeGroupoid.lift_spec (graphFreeGroupPrefunctor (V := V))
  have hm := congrArg (fun ψ => ψ.map e.hom) h
  have hm' : singleObjHomValue
        ((Quiver.FreeGroupoid.lift (graphFreeGroupPrefunctor (V := V))).map
          ((Quiver.FreeGroupoid.of V).map e.hom)) =
      singleObjHomValue ((graphFreeGroupPrefunctor (V := V)).map e.hom) := by
    exact hm
  simpa [graphFreeGroupPrefunctor] using hm'

theorem coverFreeGroupMap_letter {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    singleObjHomValue ((graphFreeGroupoidToFreeGroup (V := V)).map
      ((graphCoverSymmetricFreeGroupoidMap root).map e)) =
      FreeGroup.mk [coverSymEdgeLetter e] := by
  cases e with
  | inl e =>
      rw [graphCoverSymmetricFreeGroupoidMap_map_pos]
      have h := graphFreeGroupoidToFreeGroup_map_pos
        (V := V) (⟨_, _, e.1⟩ : Quiver.Total V)
      exact h
  | inr e =>
      change singleObjHomValue ((graphFreeGroupoidToFreeGroup (V := V)).map
        (Groupoid.inv ((Quiver.FreeGroupoid.of V).map e.1))) = _
      rw [Groupoid.inv_eq_inv, Functor.map_inv, SingleObj.inv_as_inv]
      have h := graphFreeGroupoidToFreeGroup_map_pos
        (V := V) (⟨_, _, e.1⟩ : Quiver.Total V)
      exact congrArg (fun q => q⁻¹) h

theorem coverFreeGroupValue_cons_letter {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a)
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    coverFreeGroupValue
      (@Quiver.Path.cons (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) _ _ _ p e) =
      FreeGroup.mk [coverSymEdgeLetter e] * coverFreeGroupValue p := by
  rw [coverFreeGroupValue_cons, coverFreeGroupMap_letter]

theorem coverFreeGroupValue_eq_word {root : V}
    {a : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a) :
    coverFreeGroupValue p = FreeGroup.mk (coverSymPathWord p) := by
  induction p using
      (@Quiver.Path.rec (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))) with
  | nil =>
      change (1 : FreeGroup (Quiver.Total V)) = FreeGroup.mk []
      exact FreeGroup.one_eq_mk
  | @cons y z p e ih =>
      rw [coverFreeGroupValue_cons_letter, ih, FreeGroup.mul_mk]
      rfl

theorem coverSymPathWord_length {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    (coverSymPathWord p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [coverSymPathWord_cons, List.length_cons, Quiver.Path.length_cons]
      simp [ih]

theorem coverFreeGroupValue_eq_of_endpoint {root : V}
    {a : Symmetrify (graphCoverVertex root)}
    (p q : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a) :
    coverFreeGroupValue p = coverFreeGroupValue q := by
  have hvalue : coverSymPathValue p = coverSymPathValue q :=
    (coverSymPathValue_endpoint a p).symm.trans
      (coverSymPathValue_endpoint a q)
  exact congrArg (fun h => singleObjHomValue
    ((graphFreeGroupoidToFreeGroup (V := V)).map h)) hvalue

theorem coverSymEdge_star_eq_of_letter_eq {root : V}
    {a b c : Symmetrify (graphCoverVertex root)}
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b)
    (f : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a c)
    (h : coverSymEdgeLetter e = coverSymEdgeLetter f) :
    (⟨b, e⟩ : Quiver.Star a) = ⟨c, f⟩ := by
  change graphCoverVertex root at a b c
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          have htot :
              (⟨a.1, b.1, e.1⟩ : Quiver.Total V) =
                ⟨a.1, c.1, f.1⟩ := by
            simpa [coverSymEdgeLetter] using congrArg Prod.fst h
          have hstar := graphCoverStarEquiv_map_eq_of_total_eq
            a ⟨a, b, e⟩ ⟨a, c, f⟩ rfl rfl htot
          have hstar' := (graphCoverStarEquiv root a).injective hstar
          cases hstar'
          rfl
      | inr f => simp [coverSymEdgeLetter] at h
  | inr e =>
      cases f with
      | inl f => simp [coverSymEdgeLetter] at h
      | inr f =>
          have htot :
              (⟨b.1, a.1, e.1⟩ : Quiver.Total V) =
                ⟨c.1, a.1, f.1⟩ := by
            simpa [coverSymEdgeLetter] using congrArg Prod.fst h
          have hcostar := graphCoverCostarEquiv_map_eq_of_total_eq
            a ⟨b, a, e⟩ ⟨c, a, f⟩ rfl rfl htot
          have hcostar' := (graphCoverCostarEquiv root a).injective hcostar
          cases hcostar'
          rfl

theorem coverSymEdge_eq_of_letter_eq {root : V}
    {a b c : Symmetrify (graphCoverVertex root)}
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b)
    (f : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a c)
    (h : coverSymEdgeLetter e = coverSymEdgeLetter f) : HEq e f := by
  have hstar := coverSymEdge_star_eq_of_letter_eq e f h
  exact (Sigma.ext_iff.mp hstar).2

theorem coverSymPathStar_eq_of_word_eq {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a)
    (q : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) b)
    (h : coverSymPathWord p = coverSymPathWord q) :
    (⟨a, p⟩ : Σ c : Symmetrify (graphCoverVertex root),
      @Quiver.Path (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))
        (graphCoverRootVertex root) c) =
      ⟨b, q⟩ := by
  induction p using
      (@Quiver.Path.rec (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))) generalizing b with
  | nil =>
      cases q with
      | nil => rfl
      | cons q f => cases h
  | @cons c d p e ih =>
      cases q with
      | nil => cases h
      | @cons c' d' q f =>
          have h' : coverSymEdgeLetter e :: coverSymPathWord p =
              coverSymEdgeLetter f :: coverSymPathWord q := by
            simpa [coverSymPathWord] using h
          injection h' with hhead htail
          have hpq := ih q htail
          cases hpq
          have hstar := coverSymEdge_star_eq_of_letter_eq e f hhead
          cases hstar
          rfl

theorem coverSymPath_eq_of_same_endpoint_of_noBacktrack {root : V}
    {a : Symmetrify (graphCoverVertex root)}
    (p q : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a)
    (hp : symPathNoBacktrack p) (hq : symPathNoBacktrack q) : p = q := by
  classical
  have hgroup := coverFreeGroupValue_eq_of_endpoint p q
  rw [coverFreeGroupValue_eq_word p, coverFreeGroupValue_eq_word q] at hgroup
  have hword : coverSymPathWord p = coverSymPathWord q := by
    have hred := FreeGroup.reduce.sound hgroup
    simpa [(coverSymPathWord_isReduced p hp).reduce_eq,
      (coverSymPathWord_isReduced q hq).reduce_eq] using hred
  have hstar := coverSymPathStar_eq_of_word_eq p q hword
  exact eq_of_heq (Sigma.ext_iff.mp hstar).2

theorem graphCoverSymmetric_rootedConnected {V : Type u} [Quiver.{u} V]
    (root : V) :
    @RootedConnected (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) := by
  refine ⟨?_⟩
  intro x
  rcases x with ⟨v, p⟩
  refine Quot.inductionOn p ?_
  intro p
  let φ := (graphCoverProjection root).symmetrify
  obtain ⟨⟨x, q⟩, hq⟩ :=
    ((graphCoverProjection_isCovering root).symmetrify.pathStar_bijective
      (graphCoverRootVertex root)).2 ⟨v, p⟩
  have hqparts := Sigma.mk.inj_iff.mp hq
  obtain ⟨hq', hq''⟩ := hqparts
  change x.1 = v at hq'
  cases hq'
  have hmap : φ.mapPath q = p := eq_of_heq hq''
  have hx2 : x.2 = baseSymPathValue p := by
    have hx2' := (coverSymPathValue_endpoint x q).trans
      (coverSymPathValue_eq_baseSymPathValue q)
    rw [hmap] at hx2'
    exact hx2'
  have hx : x = ⟨x.1, Quot.mk _ p⟩ := by
    refine Sigma.ext (x := x) (y := ⟨x.1, Quot.mk _ p⟩) rfl ?_
    exact heq_of_eq hx2
  rw [← hx]
  exact ⟨q⟩

noncomputable instance graphCoverSymmetricRootedConnected
    {V : Type u} [Quiver.{u} V] (root : V) :
    @RootedConnected (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) :=
  graphCoverSymmetric_rootedConnected root

/-- The canonical geodesic spanning tree of the symmetrified graph cover. -/
noncomputable def graphCoverSymmetricTree {V : Type u} [Quiver.{u} V]
    (root : V) :
    WideSubquiver (Symmetrify (graphCoverVertex root)) :=
  geodesicSubtree (graphCoverRootVertex root)

noncomputable instance graphCoverSymmetricTreeArborescence
    {V : Type u} [Quiver.{u} V] (root : V) :
    Quiver.Arborescence (graphCoverSymmetricTree root) := by
  dsimp [graphCoverSymmetricTree]
  exact @Quiver.geodesicArborescence
    (Symmetrify (graphCoverVertex root))
    (Quiver.symmetrifyQuiver (graphCoverVertex root))
    (graphCoverRootVertex root)
    (graphCoverSymmetricRootedConnected root)

theorem graphCoverSymmetric_edge_or_reverse_mem_tree {V : Type u} [Quiver.{u} V]
    (root : V)
    {a b : Symmetrify (graphCoverVertex root)}
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    e ∈ graphCoverSymmetricTree root a b ∨
      Quiver.reverse e ∈ graphCoverSymmetricTree root b a := by
  classical
  change e ∈ @geodesicSubtree (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) _ a b ∨
    Quiver.reverse e ∈ @geodesicSubtree (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) _ b a
  generalize hP : @shortestPath (Symmetrify (graphCoverVertex root))
    (Quiver.symmetrifyQuiver (graphCoverVertex root))
    (graphCoverRootVertex root) _ a = p
  have hp : symPathNoBacktrack p := by
    apply symPathNoBacktrack_of_shortest p
    intro q
    rw [← hP]
    exact @shortest_path_spec (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) _ a q
  by_cases hnb : symPathNoBacktrack (p.cons e)
  · left
    change ∃ q : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a,
      @shortestPath (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))
        (graphCoverRootVertex root) _ b = q.cons e
    refine ⟨p, ?_⟩
    have hq : symPathNoBacktrack (@shortestPath
        (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))
        (graphCoverRootVertex root) _ b) := by
      apply symPathNoBacktrack_of_shortest
      intro q
      exact @shortest_path_spec (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))
        (graphCoverRootVertex root) _ b q
    exact (coverSymPath_eq_of_same_endpoint_of_noBacktrack
      (p.cons e) (@shortestPath (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))
        (graphCoverRootVertex root) _ b) hnb hq).symm
  · cases p with
    | nil =>
        exfalso
        apply hnb
        apply symPathNoBacktrack.cons (Quiver.Path.nil) e
          symPathNoBacktrack.nil
        intro d q f hpq hcancel
        exact (Quiver.Path.nil_ne_cons q f) hpq
    | @cons d a q f =>
        have hnot : ¬ ((⟨a, b, e⟩ : Quiver.Total
            (Symmetrify (graphCoverVertex root))) ≠
            ⟨a, d, Quiver.reverse f⟩) := by
          intro hne
          apply hnb
          apply symPathNoBacktrack.cons (q.cons f) e hp
          intro d' q' f' hpq' hcancel'
          have hdd : d = d' :=
            Quiver.Path.obj_eq_of_cons_eq_cons hpq'
          cases hdd
          have hff : HEq f f' :=
            Quiver.Path.hom_heq_of_cons_eq_cons hpq'
          have hff' : f = f' := eq_of_heq hff
          cases hff'
          exact hne hcancel'
        have htotal : (⟨a, b, e⟩ : Quiver.Total
            (Symmetrify (graphCoverVertex root))) =
            ⟨a, d, Quiver.reverse f⟩ := Classical.not_not.mp hnot
        right
        have hbd : b = d := (Quiver.Total.ext_iff.mp htotal).2.1
        cases hbd
        have hef : e = Quiver.reverse f :=
          eq_of_heq (Quiver.Total.ext_iff.mp htotal).2.2
        change ∃ r : @Quiver.Path (Symmetrify (graphCoverVertex root))
          (Quiver.symmetrifyQuiver (graphCoverVertex root))
          (graphCoverRootVertex root) b,
          @shortestPath (Symmetrify (graphCoverVertex root))
            (Quiver.symmetrifyQuiver (graphCoverVertex root))
            (graphCoverRootVertex root) _ a =
            r.cons (Quiver.reverse e)
        have hfmem : f ∈ @geodesicSubtree (Symmetrify (graphCoverVertex root))
            (Quiver.symmetrifyQuiver (graphCoverVertex root))
            (graphCoverRootVertex root) _ b a := by
          change ∃ r : @Quiver.Path (Symmetrify (graphCoverVertex root))
            (Quiver.symmetrifyQuiver (graphCoverVertex root))
            (graphCoverRootVertex root) b,
            @shortestPath (Symmetrify (graphCoverVertex root))
              (Quiver.symmetrifyQuiver (graphCoverVertex root))
              (graphCoverRootVertex root) _ a = r.cons f
          exact ⟨q, hP⟩
        change ∃ r : @Quiver.Path (Symmetrify (graphCoverVertex root))
          (Quiver.symmetrifyQuiver (graphCoverVertex root))
          (graphCoverRootVertex root) b,
          @shortestPath (Symmetrify (graphCoverVertex root))
            (Quiver.symmetrifyQuiver (graphCoverVertex root))
            (graphCoverRootVertex root) _ a = r.cons f at hfmem
        rw [hef, Quiver.reverse_reverse]
        exact hfmem

/-- The representative-level realization map induced by a signed edge map. -/
def graphRealizationSignedPreMap {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (f : U → W) (g : Quiver.Total U → Quiver.Total W)
    (r : Quiver.Total U → C(I, I)) :
    graphRealizationPre U → graphRealizationPre W :=
  Sum.elim
    (fun v => Sum.inl (graphDiscreteVertex (f (graphVertexUnderlying v))))
    (fun z =>
      let e := graphEdgeUnderlying z.1
      Sum.inr ⟨graphDiscreteEdge (g e), r e z.2⟩)

theorem graphRealizationSignedPreMap_continuous
    {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (f : U → W) (g : Quiver.Total U → Quiver.Total W)
    (r : Quiver.Total U → C(I, I)) :
    Continuous (graphRealizationSignedPreMap f g r) := by
  apply continuous_sumElim.2
  constructor
  · exact continuous_inl.comp continuous_of_discreteTopology
  · apply continuous_inr.comp
    apply continuous_sigma
    intro e
    change Continuous (fun t : I =>
      (⟨graphDiscreteEdge (g (graphEdgeUnderlying e)),
        r (graphEdgeUnderlying e) t⟩ :
        Σ _e : WithDiscreteTopology (Quiver.Total W), I))
    exact (continuous_sigmaMk (i :=
      graphDiscreteEdge (g (graphEdgeUnderlying e)))).comp
      (r (graphEdgeUnderlying e)).continuous

/-- The continuous realization map induced by a signed edge map. -/
def graphRealizationSignedMap {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (f : U → W) (g : Quiver.Total U → Quiver.Total W)
    (r : Quiver.Total U → C(I, I))
    (h0 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 0⟩) =
        graphVertex (f e.left))
    (h1 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 1⟩) =
        graphVertex (f e.right)) :
    graphRealization U → graphRealization W := by
  let F : graphRealizationPre U → graphRealization W := fun x =>
    graphRealizationQuotient (graphRealizationSignedPreMap f g r x)
  refine Quotient.lift F ?_
  intro x y h
  induction h with
  | rel x y h =>
      cases h with
      | source e => simpa [F, graphRealizationSignedPreMap] using h0 e
      | target e => simpa [F, graphRealizationSignedPreMap] using h1 e
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

theorem continuous_graphRealizationSignedMap
    {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (f : U → W) (g : Quiver.Total U → Quiver.Total W)
    (r : Quiver.Total U → C(I, I))
    (h0 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 0⟩) =
        graphVertex (f e.left))
    (h1 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 1⟩) =
        graphVertex (f e.right)) :
    Continuous (graphRealizationSignedMap f g r h0 h1) := by
  let F : graphRealizationPre U → graphRealization W := fun x =>
    graphRealizationQuotient (graphRealizationSignedPreMap f g r x)
  have hcont : Continuous F :=
    continuous_quotient_mk'.comp (graphRealizationSignedPreMap_continuous f g r)
  change Continuous (Quotient.lift F _)
  exact hcont.quotient_lift _

@[simp]
theorem graphRealizationSignedMap_vertex
    {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (f : U → W) (g : Quiver.Total U → Quiver.Total W)
    (r : Quiver.Total U → C(I, I))
    (h0 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 0⟩) =
        graphVertex (f e.left))
    (h1 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 1⟩) =
        graphVertex (f e.right))
    (v : U) :
    graphRealizationSignedMap f g r h0 h1 (graphVertex v) = graphVertex (f v) := rfl

@[simp]
theorem graphRealizationSignedMap_edgePath
    {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (f : U → W) (g : Quiver.Total U → Quiver.Total W)
    (r : Quiver.Total U → C(I, I))
    (h0 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 0⟩) =
        graphVertex (f e.left))
    (h1 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 1⟩) =
        graphVertex (f e.right))
    (e : Quiver.Total U) (t : I) :
    graphRealizationSignedMap f g r h0 h1 (graphEdgePath e t) =
      graphEdgePath (g e) (r e t) := rfl

/-- The underlying cover edge represented by an edge of the symmetric cover tree. -/
def graphCoverTreeEdgeBase {V : Type u} [Quiver.{u} V]
    (root : V)
    (d : Quiver.Total (graphCoverSymmetricTree root)) :
    Quiver.Total (graphCoverVertex root) := by
  rcases d with ⟨a, b, ⟨f, hf⟩⟩
  change graphCoverVertex root at a b
  cases f with
  | inl e => exact ⟨a, b, e⟩
  | inr e => exact ⟨b, a, e⟩

/-- The orientation of a symmetric cover-tree edge relative to its underlying cover edge. -/
def graphCoverTreeEdgeSign {V : Type u} [Quiver.{u} V]
    (root : V)
    (d : Quiver.Total (graphCoverSymmetricTree root)) : Bool := by
  cases d.hom.1 with
  | inl _ => exact true
  | inr _ => exact false

/-- The specification for choosing the symmetric tree edge above an underlying cover edge. -/
def graphCoverTreeEdgeChoiceProperty {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root))
    (d : Quiver.Total (graphCoverSymmetricTree root)) : Prop :=
  graphCoverTreeEdgeBase root d = e

theorem graphCoverTreeEdgeChoice_exists {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root)) :
    Nonempty {d : Quiver.Total (graphCoverSymmetricTree root) //
      graphCoverTreeEdgeChoiceProperty root e d} := by
  have hr := graphCoverSymmetric_edge_or_reverse_mem_tree root (Sum.inl e.hom)
  rcases hr with hpos | hneg
  · exact ⟨⟨⟨(show Symmetrify (graphCoverVertex root) from e.left),
        (show Symmetrify (graphCoverVertex root) from e.right),
        ⟨Sum.inl e.hom, hpos⟩⟩, by
      change (⟨e.left, e.right, e.hom⟩ : Quiver.Total (graphCoverVertex root)) = e
      rfl⟩⟩
  · exact ⟨⟨⟨(show Symmetrify (graphCoverVertex root) from e.right),
        (show Symmetrify (graphCoverVertex root) from e.left),
        ⟨Sum.inr e.hom, hneg⟩⟩, by
      change (⟨e.left, e.right, e.hom⟩ : Quiver.Total (graphCoverVertex root)) = e
      rfl⟩⟩

/-- Chooses a symmetric tree edge above an underlying cover edge. -/
noncomputable def graphCoverTreeEdgeChoice {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root)) :
    Quiver.Total (graphCoverSymmetricTree root) :=
  (Classical.choice (graphCoverTreeEdgeChoice_exists root e)).1

theorem graphCoverTreeEdgeChoice_base {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root)) :
    graphCoverTreeEdgeBase root (graphCoverTreeEdgeChoice root e) = e :=
  (Classical.choice (graphCoverTreeEdgeChoice_exists root e)).2

/-- Forgets membership in the symmetric cover tree from a tree vertex. -/
def graphCoverTreeVertexForget {V : Type u} [Quiver.{u} V]
    (root : V)
    (v : graphCoverSymmetricTree root) : graphCoverVertex root := by
  change graphCoverVertex root at v
  exact v

/-- The continuous orientation-reversing involution of the unit interval. -/
def graphRealizationIntervalSymm : C(I, I) where
  toFun := σ
  continuous_toFun := by fun_prop

@[simp]
theorem graphRealizationIntervalSymm_apply (t : I) :
    graphRealizationIntervalSymm t = σ t := rfl

theorem graphRealizationIntervalSymm_zero :
    graphRealizationIntervalSymm 0 = 1 := by simp [graphRealizationIntervalSymm]

theorem graphRealizationIntervalSymm_one :
    graphRealizationIntervalSymm 1 = 0 := by simp [graphRealizationIntervalSymm]

theorem graphRealizationIntervalSymm_symm (t : I) :
    graphRealizationIntervalSymm (graphRealizationIntervalSymm t) = t := by
  apply Subtype.ext
  simp [graphRealizationIntervalSymm]

/-- The interval coordinate used when folding the symmetric cover tree into the cover. -/
def graphCoverTreeFoldCoordinate {V : Type u} [Quiver.{u} V]
    (root : V)
    (d : Quiver.Total (graphCoverSymmetricTree root)) : C(I, I) := by
  rcases d with ⟨a, b, ⟨f, hf⟩⟩
  change graphCoverVertex root at a b
  cases f with
  | inl _ => exact ContinuousMap.id I
  | inr _ => exact graphRealizationIntervalSymm

theorem graphCoverTreeFoldCoordinate_positive {V : Type u} [Quiver.{u} V]
    (root : V) {a b : graphCoverVertex root}
    (e : a ⟶ b) (h : Sum.inl e ∈ graphCoverSymmetricTree root a b) :
    graphCoverTreeFoldCoordinate root
        ⟨a, b, ⟨Sum.inl e, h⟩⟩ = ContinuousMap.id I := by
  rfl

theorem graphCoverTreeFoldCoordinate_negative {V : Type u} [Quiver.{u} V]
    (root : V) {a b : graphCoverVertex root}
    (e : a ⟶ b) (h : Sum.inr e ∈ graphCoverSymmetricTree root b a) :
    graphCoverTreeFoldCoordinate root
        ⟨b, a, ⟨Sum.inr e, h⟩⟩ = graphRealizationIntervalSymm := by
  rfl

theorem graphCoverTreeFold_h0 {V : Type u} [Quiver.{u} V]
    (root : V) (d : Quiver.Total (graphCoverSymmetricTree root)) :
    graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (graphCoverTreeEdgeBase root d),
            graphCoverTreeFoldCoordinate root d 0⟩) =
        graphVertex (graphCoverTreeVertexForget root d.left) := by
  rcases d with ⟨a, b, ⟨f, hf⟩⟩
  change graphCoverVertex root at a b
  cases f with
  | inl e =>
      change graphEdgePath (⟨a, b, e⟩ : Quiver.Total (graphCoverVertex root)) 0 =
        graphVertex (graphCoverTreeVertexForget root a)
      rw [graphEdgePath_zero]
      rfl
  | inr e =>
      dsimp [graphCoverTreeEdgeBase, graphCoverTreeFoldCoordinate,
        graphRealizationIntervalSymm]
      rw [show σ (0 : I) = 1 by simp]
      change graphEdgePath (⟨b, a, e⟩ : Quiver.Total (graphCoverVertex root)) 1 =
        graphVertex (graphCoverTreeVertexForget root a)
      rw [graphEdgePath_one]
      rfl

theorem graphCoverTreeFold_h1 {V : Type u} [Quiver.{u} V]
    (root : V) (d : Quiver.Total (graphCoverSymmetricTree root)) :
    graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (graphCoverTreeEdgeBase root d),
            graphCoverTreeFoldCoordinate root d 1⟩) =
        graphVertex (graphCoverTreeVertexForget root d.right) := by
  rcases d with ⟨a, b, ⟨f, hf⟩⟩
  change graphCoverVertex root at a b
  cases f with
  | inl e =>
      change graphEdgePath (⟨a, b, e⟩ : Quiver.Total (graphCoverVertex root)) 1 =
        graphVertex (graphCoverTreeVertexForget root b)
      rw [graphEdgePath_one]
      rfl
  | inr e =>
      dsimp [graphCoverTreeEdgeBase, graphCoverTreeFoldCoordinate,
        graphRealizationIntervalSymm]
      rw [show σ (1 : I) = 0 by simp]
      change graphEdgePath (⟨b, a, e⟩ : Quiver.Total (graphCoverVertex root)) 0 =
        graphVertex (graphCoverTreeVertexForget root b)
      rw [graphEdgePath_zero]
      rfl

/-- The realization map folding the symmetric cover tree onto the canonical cover. -/
noncomputable def graphCoverTreeToCover {V : Type u} [Quiver.{u} V]
    (root : V) :
    graphRealization (graphCoverSymmetricTree root) →
      graphRealization (graphCoverVertex root) :=
  graphRealizationSignedMap
    (graphCoverTreeVertexForget root)
    (graphCoverTreeEdgeBase root)
    (graphCoverTreeFoldCoordinate root)
    (graphCoverTreeFold_h0 root)
    (graphCoverTreeFold_h1 root)

theorem continuous_graphCoverTreeToCover {V : Type u} [Quiver.{u} V]
    (root : V) :
    Continuous (graphCoverTreeToCover root) :=
  continuous_graphRealizationSignedMap _ _ _ _ _

@[simp]
theorem graphCoverTreeToCover_vertex {V : Type u} [Quiver.{u} V]
    (root : V) (v : graphCoverSymmetricTree root) :
    graphCoverTreeToCover root (graphVertex v) =
      graphVertex (graphCoverTreeVertexForget root v) := rfl

@[simp]
theorem graphCoverTreeToCover_edgePath {V : Type u} [Quiver.{u} V]
    (root : V)
    (e : Quiver.Total (graphCoverSymmetricTree root)) (t : I) :
    graphCoverTreeToCover root (graphEdgePath e t) =
      graphEdgePath (graphCoverTreeEdgeBase root e)
        (graphCoverTreeFoldCoordinate root e t) := rfl

/-- Embeds a canonical-cover vertex into the symmetric cover tree. -/
def graphCoverVertexEmbed {V : Type u} [Quiver.{u} V]
    (root : V) (v : graphCoverVertex root) :
    graphCoverSymmetricTree root := by
  change graphCoverVertex root at v
  exact v

/-- The signed interval coordinate used by the section from the cover to its tree model. -/
noncomputable def graphCoverSectionCoordinate {V : Type u} [Quiver.{u} V]
    (root : V)
    (e : Quiver.Total (graphCoverVertex root)) : C(I, I) :=
  match graphCoverTreeEdgeSign root (graphCoverTreeEdgeChoice root e) with
  | true => ContinuousMap.id I
  | false => graphRealizationIntervalSymm

theorem graphCoverSectionCoordinate_positive {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root))
    (h : graphCoverTreeEdgeSign root (graphCoverTreeEdgeChoice root e) = true) :
    graphCoverSectionCoordinate root e = ContinuousMap.id I := by
  simp [graphCoverSectionCoordinate, h]

theorem graphCoverSectionCoordinate_negative {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root))
    (h : graphCoverTreeEdgeSign root (graphCoverTreeEdgeChoice root e) = false) :
    graphCoverSectionCoordinate root e = graphRealizationIntervalSymm := by
  simp [graphCoverSectionCoordinate, h]

theorem graphCoverSection_h0 {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root)) :
    graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (graphCoverTreeEdgeChoice root e),
            graphCoverSectionCoordinate root e 0⟩) =
        graphVertex (graphCoverVertexEmbed root e.left) := by
  classical
  let d := graphCoverTreeEdgeChoice root e
  have hbase : graphCoverTreeEdgeBase root d = e :=
    graphCoverTreeEdgeChoice_base root e
  have hd : graphCoverTreeEdgeChoice root e = d := rfl
  dsimp [graphCoverSectionCoordinate]
  rw [hd]
  rcases d with ⟨a, b, ⟨f, hf⟩⟩
  change graphCoverVertex root at a b
  cases f with
  | inl f =>
      change graphEdgePath
          (⟨a, b, ⟨Sum.inl f, hf⟩⟩ :
            Quiver.Total (graphCoverSymmetricTree root)) 0 =
        graphVertex (graphCoverVertexEmbed root e.left)
      rw [graphEdgePath_zero]
      have he : (⟨a, b, f⟩ : Quiver.Total (graphCoverVertex root)) = e := by
        simpa [graphCoverTreeEdgeBase] using hbase
      cases he
      rfl
  | inr f =>
      have hs : graphCoverTreeEdgeSign root
          ⟨(show Symmetrify (graphCoverVertex root) from a),
            (show Symmetrify (graphCoverVertex root) from b),
            ⟨Sum.inr f, hf⟩⟩ = false := rfl
      rw [hs]
      rw [show graphRealizationIntervalSymm 0 = 1 by simp]
      change graphEdgePath
          (⟨(show Symmetrify (graphCoverVertex root) from a),
            (show Symmetrify (graphCoverVertex root) from b),
            ⟨Sum.inr f, hf⟩⟩ :
            Quiver.Total (graphCoverSymmetricTree root)) 1 =
        graphVertex (graphCoverVertexEmbed root e.left)
      rw [graphEdgePath_one]
      have he : (⟨b, a, f⟩ : Quiver.Total (graphCoverVertex root)) = e := by
        simpa [graphCoverTreeEdgeBase] using hbase
      cases he
      rfl

theorem graphCoverSection_h1 {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root)) :
    graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (graphCoverTreeEdgeChoice root e),
            graphCoverSectionCoordinate root e 1⟩) =
        graphVertex (graphCoverVertexEmbed root e.right) := by
  classical
  let d := graphCoverTreeEdgeChoice root e
  have hbase : graphCoverTreeEdgeBase root d = e :=
    graphCoverTreeEdgeChoice_base root e
  have hd : graphCoverTreeEdgeChoice root e = d := rfl
  dsimp [graphCoverSectionCoordinate]
  rw [hd]
  rcases d with ⟨a, b, ⟨f, hf⟩⟩
  change graphCoverVertex root at a b
  cases f with
  | inl f =>
      change graphEdgePath
          (⟨a, b, ⟨Sum.inl f, hf⟩⟩ :
            Quiver.Total (graphCoverSymmetricTree root)) 1 =
        graphVertex (graphCoverVertexEmbed root e.right)
      rw [graphEdgePath_one]
      have he : (⟨a, b, f⟩ : Quiver.Total (graphCoverVertex root)) = e := by
        simpa [graphCoverTreeEdgeBase] using hbase
      cases he
      rfl
  | inr f =>
      have hs : graphCoverTreeEdgeSign root
          ⟨(show Symmetrify (graphCoverVertex root) from a),
            (show Symmetrify (graphCoverVertex root) from b),
            ⟨Sum.inr f, hf⟩⟩ = false := rfl
      rw [hs]
      rw [show graphRealizationIntervalSymm 1 = 0 by simp]
      change graphEdgePath
          (⟨(show Symmetrify (graphCoverVertex root) from a),
            (show Symmetrify (graphCoverVertex root) from b),
            ⟨Sum.inr f, hf⟩⟩ :
            Quiver.Total (graphCoverSymmetricTree root)) 0 =
        graphVertex (graphCoverVertexEmbed root e.right)
      rw [graphEdgePath_zero]
      have he : (⟨b, a, f⟩ : Quiver.Total (graphCoverVertex root)) = e := by
        simpa [graphCoverTreeEdgeBase] using hbase
      cases he
      rfl

/-- A continuous section from the canonical cover realization to its symmetric tree model. -/
noncomputable def graphCoverToTree {V : Type u} [Quiver.{u} V]
    (root : V) :
    graphRealization (graphCoverVertex root) →
      graphRealization (graphCoverSymmetricTree root) :=
  graphRealizationSignedMap
    (graphCoverVertexEmbed root)
    (graphCoverTreeEdgeChoice root)
    (graphCoverSectionCoordinate root)
    (graphCoverSection_h0 root)
    (graphCoverSection_h1 root)

theorem continuous_graphCoverToTree {V : Type u} [Quiver.{u} V]
    (root : V) :
    Continuous (graphCoverToTree root) :=
  continuous_graphRealizationSignedMap _ _ _ _ _

@[simp]
theorem graphCoverToTree_vertex {V : Type u} [Quiver.{u} V]
    (root : V) (v : graphCoverVertex root) :
    graphCoverToTree root (graphVertex v) =
      graphVertex (graphCoverVertexEmbed root v) := rfl

@[simp]
theorem graphCoverToTree_edgePath {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root))
    (t : I) :
    graphCoverToTree root (graphEdgePath e t) =
      graphEdgePath (graphCoverTreeEdgeChoice root e)
        (graphCoverSectionCoordinate root e t) := rfl

theorem graphRealization_map_ext {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (F G : graphRealization U → graphRealization W)
    (hv : ∀ v : U, F (graphVertex v) = G (graphVertex v))
    (he : ∀ (e : Quiver.Total U) (t : I),
      F (graphEdgePath e t) = G (graphEdgePath e t)) :
    F = G := by
  funext x
  refine Quotient.inductionOn x ?_
  intro x
  cases x with
  | inl v => exact hv (graphVertexUnderlying v)
  | inr z =>
      rcases z with ⟨e, t⟩
      exact he (graphEdgeUnderlying e) t

theorem graphCoverTreeVertexForget_embed {V : Type u} [Quiver.{u} V]
    (root : V) (v : graphCoverVertex root) :
    graphCoverTreeVertexForget root (graphCoverVertexEmbed root v) = v := by
  rfl

theorem graphCoverTreeToCover_comp_graphCoverToTree
    {V : Type u} [Quiver.{u} V] (root : V) :
    (graphCoverTreeToCover root) ∘ (graphCoverToTree root) =
      (id : graphRealization (graphCoverVertex root) →
        graphRealization (graphCoverVertex root)) := by
  apply graphRealization_map_ext
  · intro v
    change graphCoverTreeToCover root (graphCoverToTree root (graphVertex v)) =
      graphVertex v
    rw [graphCoverToTree_vertex, graphCoverTreeToCover_vertex,
      graphCoverTreeVertexForget_embed]
  · intro e t
    change graphCoverTreeToCover root (graphCoverToTree root (graphEdgePath e t)) =
      graphEdgePath e t
    rw [graphCoverToTree_edgePath, graphCoverTreeToCover_edgePath]
    let d := graphCoverTreeEdgeChoice root e
    have hbase : graphCoverTreeEdgeBase root d = e :=
      graphCoverTreeEdgeChoice_base root e
    have hd : graphCoverTreeEdgeChoice root e = d := rfl
    dsimp [graphCoverSectionCoordinate]
    rw [hd]
    rcases d with ⟨a, b, ⟨f, hf⟩⟩
    change graphCoverVertex root at a b
    cases f with
    | inl f =>
        change graphEdgePath
            (⟨a, b, f⟩ : Quiver.Total (graphCoverVertex root))
            ((ContinuousMap.id I) ((ContinuousMap.id I) t)) =
          graphEdgePath e t
        rw [ContinuousMap.id_apply, ContinuousMap.id_apply]
        have he : (⟨a, b, f⟩ : Quiver.Total (graphCoverVertex root)) = e := by
          simpa [graphCoverTreeEdgeBase] using hbase
        rw [he]
    | inr f =>
        have hs : graphCoverTreeEdgeSign root
            ⟨(show Symmetrify (graphCoverVertex root) from a),
              (show Symmetrify (graphCoverVertex root) from b),
              ⟨Sum.inr f, hf⟩⟩ = false := rfl
        rw [hs]
        change graphEdgePath
            (⟨b, a, f⟩ : Quiver.Total (graphCoverVertex root))
            (graphRealizationIntervalSymm
              (graphRealizationIntervalSymm t)) =
          graphEdgePath e t
        rw [graphRealizationIntervalSymm_symm]
        have he : (⟨b, a, f⟩ : Quiver.Total (graphCoverVertex root)) = e := by
          simpa [graphCoverTreeEdgeBase] using hbase
        rw [he]

theorem graphCoverTreeEdgeBase_injective
    {V : Type u} [Quiver.{u} V] (root : V)
    (d₁ d₂ : Quiver.Total (graphCoverSymmetricTree root))
    (h : graphCoverTreeEdgeBase root d₁ =
      graphCoverTreeEdgeBase root d₂) : d₁ = d₂ := by
  classical
  rcases d₁ with ⟨a, b, ⟨f, hf⟩⟩
  rcases d₂ with ⟨c, d, ⟨g, hg⟩⟩
  change graphCoverVertex root at a b c d
  cases f with
  | inl f =>
      cases g with
      | inl g =>
          have htotal : (⟨a, b, f⟩ : Quiver.Total (graphCoverVertex root)) =
              ⟨c, d, g⟩ := by
            simpa [graphCoverTreeEdgeBase] using h
          cases htotal
          rfl
      | inr g =>
          have htotal : (⟨a, b, f⟩ : Quiver.Total (graphCoverVertex root)) =
              ⟨d, c, g⟩ := by
            simpa [graphCoverTreeEdgeBase] using h
          have hsrc : a = d := congrArg Quiver.Total.left htotal
          have htgt : b = c := congrArg Quiver.Total.right htotal
          have hhom : HEq f g := (Quiver.Total.ext_iff.mp htotal).2.2
          cases hsrc
          cases htgt
          have hhom' : f = g := eq_of_heq hhom
          cases hhom'
          exact False.elim (no_reverse_edges (graphCoverSymmetricTree root)
            f hf hg)
  | inr f =>
      cases g with
      | inl g =>
          have htotal : (⟨b, a, f⟩ : Quiver.Total (graphCoverVertex root)) =
              ⟨c, d, g⟩ := by
            simpa [graphCoverTreeEdgeBase] using h
          have hsrc : b = c := congrArg Quiver.Total.left htotal
          have htgt : a = d := congrArg Quiver.Total.right htotal
          have hhom : HEq f g := (Quiver.Total.ext_iff.mp htotal).2.2
          cases hsrc
          cases htgt
          have hhom' : f = g := eq_of_heq hhom
          cases hhom'
          exact False.elim (no_reverse_edges (graphCoverSymmetricTree root)
            f hg hf)
      | inr g =>
          have htotal : (⟨b, a, f⟩ : Quiver.Total (graphCoverVertex root)) =
              ⟨d, c, g⟩ := by
            simpa [graphCoverTreeEdgeBase] using h
          cases htotal
          rfl

theorem graphCoverToTree_comp_graphCoverTreeToCover
    {V : Type u} [Quiver.{u} V] (root : V) :
    (graphCoverToTree root) ∘ (graphCoverTreeToCover root) =
      (id : graphRealization (graphCoverSymmetricTree root) →
        graphRealization (graphCoverSymmetricTree root)) := by
  apply graphRealization_map_ext
  · intro v
    change graphCoverToTree root (graphCoverTreeToCover root (graphVertex v)) =
      graphVertex v
    rw [graphCoverTreeToCover_vertex, graphCoverToTree_vertex]
    rfl
  · intro d t
    change graphCoverToTree root
        (graphCoverTreeToCover root (graphEdgePath d t)) =
      graphEdgePath d t
    rw [graphCoverTreeToCover_edgePath, graphCoverToTree_edgePath]
    have hchoice : graphCoverTreeEdgeChoice root
          (graphCoverTreeEdgeBase root d) = d := by
      apply graphCoverTreeEdgeBase_injective root
      exact graphCoverTreeEdgeChoice_base root
        (graphCoverTreeEdgeBase root d)
    dsimp [graphCoverSectionCoordinate]
    rw [hchoice]
    rcases d with ⟨a, b, ⟨f, hf⟩⟩
    change graphCoverVertex root at a b
    cases f with
    | inl f =>
        dsimp [graphCoverSectionCoordinate, graphCoverTreeFoldCoordinate]
        change graphEdgePath
            (⟨(show Symmetrify (graphCoverVertex root) from a),
              (show Symmetrify (graphCoverVertex root) from b),
              ⟨Sum.inl f, hf⟩⟩ :
              Quiver.Total (graphCoverSymmetricTree root))
            ((ContinuousMap.id I) ((ContinuousMap.id I) t)) =
          graphEdgePath
            (⟨a, b, ⟨Sum.inl f, hf⟩⟩ :
              Quiver.Total (graphCoverSymmetricTree root)) t
        rw [ContinuousMap.id_apply, ContinuousMap.id_apply]
    | inr f =>
        dsimp [graphCoverSectionCoordinate, graphCoverTreeFoldCoordinate]
        have hs : graphCoverTreeEdgeSign root
            ⟨(show Symmetrify (graphCoverVertex root) from a),
              (show Symmetrify (graphCoverVertex root) from b),
              ⟨Sum.inr f, hf⟩⟩ = false := rfl
        rw [hs]
        change graphEdgePath
            (⟨(show Symmetrify (graphCoverVertex root) from a),
              (show Symmetrify (graphCoverVertex root) from b),
              ⟨Sum.inr f, hf⟩⟩ :
              Quiver.Total (graphCoverSymmetricTree root))
            (graphRealizationIntervalSymm
              (graphRealizationIntervalSymm t)) =
          graphEdgePath
            (⟨(show Symmetrify (graphCoverVertex root) from a),
              (show Symmetrify (graphCoverVertex root) from b),
              ⟨Sum.inr f, hf⟩⟩ :
              Quiver.Total (graphCoverSymmetricTree root)) t
        rw [graphRealizationIntervalSymm_symm]

/-- The homotopy equivalence between the canonical cover and its symmetric spanning tree. -/
noncomputable def graphCoverRealizationHomotopyEquiv
    {V : Type u} [Quiver.{u} V] (root : V) :
    graphRealization (graphCoverVertex root) ≃ₕ
      graphRealization (graphCoverSymmetricTree root) := by
  let f : C(graphRealization (graphCoverVertex root),
      graphRealization (graphCoverSymmetricTree root)) :=
    ⟨graphCoverToTree root, continuous_graphCoverToTree root⟩
  let g : C(graphRealization (graphCoverSymmetricTree root),
      graphRealization (graphCoverVertex root)) :=
    ⟨graphCoverTreeToCover root, continuous_graphCoverTreeToCover root⟩
  refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }
  · have hcomp : g.comp f = ContinuousMap.id _ := by
      ext x
      exact congrFun (graphCoverTreeToCover_comp_graphCoverToTree root) x
    rw [hcomp]
  · have hcomp : f.comp g = ContinuousMap.id _ := by
      ext x
      exact congrFun (graphCoverToTree_comp_graphCoverTreeToCover root) x
    rw [hcomp]

noncomputable instance graphCoverRealization_contractible
    {V : Type u} [Quiver.{u} V] (root : V) :
    ContractibleSpace (graphRealization (graphCoverVertex root)) := by
  exact (graphCoverRealizationHomotopyEquiv root).contractibleSpace

/-- Evaluates a symmetric base-graph path in the free graph groupoid. -/
abbrev graphBaseSymPathValue {V : Type u} [Quiver.{u} V]
    {a b : V}
    (p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) a b) :
    (Quiver.FreeGroupoid.of V).obj a ⟶ (Quiver.FreeGroupoid.of V).obj b :=
  @baseSymPathValue V _ (show Symmetrify V from a)
    (show Symmetrify V from b) p

theorem graphFreeGroupoidToTopological_map_path {V : Type u} [Quiver.{u} V]
    {a b : V}
    (p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) a b) :
    (graphFreeGroupoidToTopological (V := V)).map (graphBaseSymPathValue p) =
      FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk
          (@graphRealizationQuiverPath V _ a b p)) := by
  induction p with
  | nil =>
      rfl
  | cons p e ih =>
      change (CategoryTheory.Paths.lift
        (Quiver.Symmetrify.lift (graphRealizationQuiverMap (V := V)))).map
          (@Quiver.Path.cons (Symmetrify V) (Quiver.symmetrifyQuiver V)
            _ _ _ p e) = _
      rw [CategoryTheory.Paths.lift_cons]
      have ih' :
          (CategoryTheory.Paths.lift
            (Quiver.Symmetrify.lift (graphRealizationQuiverMap (V := V)))).map p =
          FundamentalGroupoid.fromPath
            (Path.Homotopic.Quotient.mk
              (@graphRealizationQuiverPath V _ _ _ p)) := by
        exact ih
      rw [ih']
      cases e with
      | inl e =>
          rfl
      | inr e =>
          rfl
variable {V : Type u} [Quiver.{u} V] [WeaklyConnected V]

omit [WeaklyConnected V] in
theorem graphCoverRealization_fiber_vertex
    (root : V) {z : graphCoverRealization root}
    (hz : graphCoverRealizationProjection root z = graphVertex root) :
    ∃ x : graphCoverVertex root, z = graphVertex x ∧ x.1 = root := by
  revert hz
  refine Quotient.inductionOn z ?_
  intro z hz
  cases z with
  | inl v =>
      let x : graphCoverVertex root := graphVertexUnderlying v
      have hzx : graphRealizationQuotient (Sum.inl v) = graphVertex x := by
        rfl
      have hproj : graphVertex x.1 = graphVertex root := by
        dsimp [graphCoverRealizationProjection] at hz
        change graphRealizationMap (graphCoverProjection root)
            (graphRealizationQuotient (Sum.inl v)) = graphVertex root at hz
        rw [hzx] at hz
        rw [graphRealizationMap_vertex] at hz
        exact hz
      refine ⟨x, hzx, ?_⟩
      exact graphVertex_injective hproj
  | inr z =>
      rcases z with ⟨ze, t⟩
      let e : Quiver.Total (graphCoverVertex root) := graphEdgeUnderlying ze
      have hze : ze = graphDiscreteEdge e := by
        simp [e, graphDiscreteEdge, graphEdgeUnderlying]
      have hzedge : graphRealizationQuotient
          (Sum.inr ⟨ze, t⟩) = graphEdgePath e t := by
        rw [hze]
        rfl
      have hzproj : graphEdgePath
          ⟨(graphCoverProjection root).obj e.left,
            (graphCoverProjection root).obj e.right,
            (graphCoverProjection root).map e.hom⟩ t =
          graphVertex root := by
        rw [← graphRealizationMap_edgePath (graphCoverProjection root) e t]
        rw [← hzedge]
        dsimp [graphCoverRealizationProjection] at hz
        exact hz
      have ht : t = 0 ∨ t = 1 := by
        exact graphRealization_vertex_edge_endpoint (V := V) (v := root)
          (e := ⟨(graphCoverProjection root).obj e.left,
            (graphCoverProjection root).obj e.right,
            (graphCoverProjection root).map e.hom⟩) (t := t) hzproj.symm
      rcases ht with rfl | rfl
      · refine ⟨e.left, ?_, ?_⟩
        · exact hzedge.trans (graphEdgePath_zero e)
        · exact graphVertex_injective (by
            simpa [graphCoverProjection] using hzproj)
      · refine ⟨e.right, ?_, ?_⟩
        · exact hzedge.trans (graphEdgePath_one e)
        · exact graphVertex_injective (by
            simpa [graphCoverProjection] using hzproj)

omit [WeaklyConnected V] in
theorem graphCoverRealizationQuiverPath_map
    (root : V) {a b : graphCoverVertex root}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    (@graphRealizationQuiverPath (graphCoverVertex root)
      (graphCoverQuiver root) a b p).map
        (continuous_graphCoverRealizationProjection root) =
      @graphRealizationQuiverPath V (inferInstance : Quiver V) a.1 b.1
        ((graphCoverProjection root).symmetrify.mapPath p) := by
  induction p with
  | nil =>
      rfl
  | cons p e ih =>
      change ((@graphRealizationQuiverPath (graphCoverVertex root)
          (graphCoverQuiver root) _ _ p).trans
          (graphRealizationSymmetricEdgePath e)).map
          (continuous_graphCoverRealizationProjection root) =
        @graphRealizationQuiverPath V (inferInstance : Quiver V) _ _
          ((graphCoverProjection root).symmetrify.mapPath
            (@Quiver.Path.cons (Symmetrify (graphCoverVertex root))
              (Quiver.symmetrifyQuiver (graphCoverVertex root)) _ _ _ p e))
      rw [Prefunctor.mapPath_cons, Path.map_trans, ih]
      cases e with
      | inl e =>
          rfl
      | inr e =>
          rfl

/-- The distinguished point in the covering fiber over the realized root vertex. -/
def graphCoverRootFiberPoint (root : V) :
    (graphCoverRealizationProjection root) ⁻¹' {graphVertex root} :=
  ⟨graphVertex (graphCoverRootVertex root), by
    change graphVertex ((graphCoverProjection root).obj
      (graphCoverRootVertex root)) = graphVertex root
    rfl
  ⟩

theorem graphRealizationQuiverPath_cast
    {W : Type u} [Quiver.{u} W]
    {a b a' b' : W} (ha : a = a') (hb : b = b')
    (p : @Quiver.Path (Symmetrify W) (Quiver.symmetrifyQuiver W) a b) :
    @graphRealizationQuiverPath W _ a' b' (Quiver.Path.cast ha hb p) =
      (@graphRealizationQuiverPath W _ a b p).cast
        (congrArg graphVertex ha).symm (congrArg graphVertex hb).symm := by
  cases ha
  cases hb
  rfl

theorem graphCombinatorialToTopological_surjective_of_path
    (root : V) (γ : Path (graphVertex root) (graphVertex root)) :
    ∃ p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V)
        (show Symmetrify V from root) root,
      graphCombinatorialToTopological root (graphBaseSymPathValue p) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) := by
  let P := graphCoverRealizationProjection root
  let cov := graphCoverRealizationProjection_isCovering root
  let e₀ := graphCoverRootFiberPoint root
  have h₀ : γ 0 = P (e₀ : graphCoverRealization root) := by
    exact γ.source.trans e₀.2.symm
  let L := cov.liftPath γ.toContinuousMap (e₀ : graphCoverRealization root) h₀
  let z : graphCoverRealization root := L 1
  have hz : P z = graphVertex root := by
    have hL := congr_fun (cov.liftPath_lifts γ.toContinuousMap
      (e₀ : graphCoverRealization root) h₀) 1
    exact hL.trans γ.target
  obtain ⟨x, hzx, hx⟩ := graphCoverRealization_fiber_vertex root hz
  have : @RootedConnected (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) := graphCoverSymmetric_rootedConnected root
  obtain ⟨q⟩ := (inferInstance : Nonempty
    (@Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (show Symmetrify (graphCoverVertex root) from graphCoverRootVertex root) x))
  have hpstart : (graphCoverProjection root).symmetrify.obj
        (graphCoverRootVertex root) = (show Symmetrify V from root) := by
    rfl
  have hpend : (graphCoverProjection root).symmetrify.obj x =
        (show Symmetrify V from root) := by
    change x.1 = root
    exact hx
  let p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V)
      (show Symmetrify V from root) root :=
    Quiver.Path.cast hpstart hpend
      ((graphCoverProjection root).symmetrify.mapPath q)
  let qtop : Path (graphVertex (graphCoverRootVertex root)) (graphVertex x) :=
    @graphRealizationQuiverPath (graphCoverVertex root)
      (graphCoverQuiver root) _ _ q
  let Lpath : Path (graphVertex (graphCoverRootVertex root)) (graphVertex x) := {
    toContinuousMap := L
    source' := by
      exact cov.liftPath_zero γ.toContinuousMap (e₀ : graphCoverRealization root) h₀
    target' := hzx }
  have hpaths : Lpath.Homotopic qtop :=
    SimplyConnectedSpace.paths_homotopic Lpath qtop
  have hclasses : Path.Homotopic.Quotient.mk Lpath =
      Path.Homotopic.Quotient.mk qtop := Quotient.sound hpaths
  have hstart : graphVertex root = P (graphVertex (graphCoverRootVertex root)) :=
    e₀.2.symm
  have hxP : P (graphVertex x) = graphVertex root := by
    calc
      P (graphVertex x) = P z := congrArg P hzx.symm
      _ = graphVertex root := hz
  have htarget : graphVertex root = P (graphVertex x) := hxP.symm
  let qbase : Path (graphVertex root) (graphVertex root) :=
    (qtop.map cov.continuous).cast hstart htarget
  let Lbase : Path (graphVertex root) (graphVertex root) :=
    (Lpath.map cov.continuous).cast hstart htarget
  have hmap : Path.Homotopic.Quotient.mk γ =
      Path.Homotopic.Quotient.mk qbase := by
    have hmap' := congrArg (fun r => r.map ⟨P, cov.continuous⟩) hclasses
    rw [← Path.Homotopic.Quotient.mk_map] at hmap'
    have hcast := congrArg
      (fun r : Path.Homotopic.Quotient
          (P (graphVertex (graphCoverRootVertex root))) (P (graphVertex x)) =>
        r.cast hstart htarget) hmap'
    rw [← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast] at hcast
    have hLmap : Lbase = γ := by
      ext t
      exact congr_fun (cov.liftPath_lifts γ.toContinuousMap
        (e₀ : graphCoverRealization root) h₀) t
    rw [← hLmap]
    exact hcast
  refine ⟨p, ?_⟩
  change (graphFreeGroupoidToTopological (V := V)).map
      (graphBaseSymPathValue p) = _
  rw [graphFreeGroupoidToTopological_map_path]
  apply congrArg FundamentalGroup.fromPath
  have hqmap₀ := graphCoverRealizationQuiverPath_map root q
  have hqcast := graphRealizationQuiverPath_cast (W := V) hpstart hpend
    ((graphCoverProjection root).symmetrify.mapPath q)
  have hqmap : qbase =
      @graphRealizationQuiverPath V (inferInstance : Quiver V) root root p := by
    ext t
    calc
      qbase t = (qtop.map cov.continuous) t := rfl
      _ = (@graphRealizationQuiverPath V (inferInstance : Quiver V)
          ((graphCoverProjection root).symmetrify.obj
            (graphCoverRootVertex root))
          ((graphCoverProjection root).symmetrify.obj x)
          ((graphCoverProjection root).symmetrify.mapPath q)) t := by
        exact congrArg (fun r => r t) hqmap₀
      _ = (@graphRealizationQuiverPath V (inferInstance : Quiver V) root root p) t :=
        (congrArg (fun r => r t) hqcast).symm
  rw [← hqmap, ← hmap]

theorem graphCombinatorialToTopological_surjective
    (root : V) :
    Function.Surjective (graphCombinatorialToTopological root) := by
  intro g
  refine Quotient.inductionOn g ?_
  intro γ
  obtain ⟨p, hp⟩ := graphCombinatorialToTopological_surjective_of_path root γ
  refine ⟨graphBaseSymPathValue p, ?_⟩
  simpa [graphCombinatorialToTopological, graphFreeGroupoidToTopological] using hp

theorem baseSymPathValue_cast_heq
    {V : Type u} [Quiver.{u} V]
    {a b a' b' : Symmetrify V} (ha : a = a') (hb : b = b')
    (p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) a b) :
    HEq (baseSymPathValue (Quiver.Path.cast ha hb p))
      (baseSymPathValue p) := by
  cases ha
  cases hb
  rfl

private theorem graphCombinatorialToTopological_injective_of_paths
    (root : V)
    (p q : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) root root)
    (htop : Path.Homotopic.Quotient.mk
      (@graphRealizationQuiverPath V _ _ _ p) =
      Path.Homotopic.Quotient.mk
        (@graphRealizationQuiverPath V _ _ _ q)) :
    baseSymPathValue p = baseSymPathValue q := by
  have hpstart : (graphCoverProjection root).symmetrify.obj
        (graphCoverRootVertex root) = (show Symmetrify V from root) := by
    rfl
  let p' := Quiver.Path.cast hpstart.symm (rfl : root = root) p
  let q' := Quiver.Path.cast hpstart.symm (rfl : root = root) q
  obtain ⟨⟨xp, rp⟩, hpstar⟩ :=
    ((graphCoverProjection_isCovering root).symmetrify.pathStar_bijective
      (graphCoverRootVertex root)).2 ⟨root, p'⟩
  obtain ⟨⟨xq, rq⟩, hqstar⟩ :=
    ((graphCoverProjection_isCovering root).symmetrify.pathStar_bijective
      (graphCoverRootVertex root)).2 ⟨root, q'⟩
  have hp_parts := Sigma.mk.inj_iff.mp hpstar
  have hq_parts := Sigma.mk.inj_iff.mp hqstar
  obtain ⟨hxp, hrp⟩ := hp_parts
  obtain ⟨hxq, hrq⟩ := hq_parts
  change xp.1 = root at hxp
  change xq.1 = root at hxq
  let P := graphCoverRealizationProjection root
  let cov := graphCoverRealizationProjection_isCovering root
  let e₀ := graphCoverRootFiberPoint root
  have hxp' : (show Symmetrify V from root) =
        (graphCoverProjection root).symmetrify.obj xp := by
    change root = xp.1
    exact hxp.symm
  have hxq' : (show Symmetrify V from root) =
        (graphCoverProjection root).symmetrify.obj xq := by
    change root = xq.1
    exact hxq.symm
  have hrp_cast : (graphCoverProjection root).symmetrify.mapPath rp =
        (p'.cast rfl hxp') := by
    exact (Quiver.Path.eq_cast_iff_heq rfl hxp' p'
      ((graphCoverProjection root).symmetrify.mapPath rp)).2 hrp
  have hrq_cast : (graphCoverProjection root).symmetrify.mapPath rq =
        (q'.cast rfl hxq') := by
    exact (Quiver.Path.eq_cast_iff_heq rfl hxq' q'
      ((graphCoverProjection root).symmetrify.mapPath rq)).2 hrq
  let ptop : Path (graphVertex root) (graphVertex root) :=
    @graphRealizationQuiverPath V _ _ _ p
  let qtop : Path (graphVertex root) (graphVertex root) :=
    @graphRealizationQuiverPath V _ _ _ q
  let plift : Path (graphVertex (graphCoverRootVertex root))
      (graphVertex xp) :=
    @graphRealizationQuiverPath (graphCoverVertex root)
      (graphCoverQuiver root) _ _ rp
  let qlift : Path (graphVertex (graphCoverRootVertex root))
      (graphVertex xq) :=
    @graphRealizationQuiverPath (graphCoverVertex root)
      (graphCoverQuiver root) _ _ rq
  let pbase : Path
      (graphVertex (V := V) ((graphCoverProjection root).symmetrify.obj
        (show Symmetrify (graphCoverVertex root) from graphCoverRootVertex root)))
      (graphVertex (V := V) ((graphCoverProjection root).symmetrify.obj xp)) :=
    @graphRealizationQuiverPath V _ _ _
      ((graphCoverProjection root).symmetrify.mapPath rp)
  let qbase : Path
      (graphVertex (V := V) ((graphCoverProjection root).symmetrify.obj
        (show Symmetrify (graphCoverVertex root) from graphCoverRootVertex root)))
      (graphVertex (V := V) ((graphCoverProjection root).symmetrify.obj xq)) :=
    @graphRealizationQuiverPath V _ _ _
      ((graphCoverProjection root).symmetrify.mapPath rq)
  have hpmap : plift.map cov.continuous = pbase := by
    exact graphCoverRealizationQuiverPath_map root rp
  have hqmap : qlift.map cov.continuous = qbase := by
    exact graphCoverRealizationQuiverPath_map root rq
  have hep : P (graphVertex xp) = graphVertex root := by
    change graphVertex xp.1 = graphVertex root
    exact congrArg graphVertex hxp
  have heq : P (graphVertex xq) = graphVertex root := by
    change graphVertex xq.1 = graphVertex root
    exact congrArg graphVertex hxq
  have hpbase_cast : pbase = ptop.cast e₀.2 hep := by
    dsimp [pbase, ptop]
    rw [hrp_cast]
    have h1 := graphRealizationQuiverPath_cast (W := V)
      (rfl : (graphCoverProjection root).symmetrify.obj
        (show Symmetrify (graphCoverVertex root) from graphCoverRootVertex root) =
        (graphCoverProjection root).symmetrify.obj
          (show Symmetrify (graphCoverVertex root) from graphCoverRootVertex root))
      hxp' p'
    have h2 := graphRealizationQuiverPath_cast (W := V)
      hpstart.symm (rfl : root = root) p
    rw [h1, h2]
    ext t
    rfl
  have hqbase_cast : qbase = qtop.cast e₀.2 heq := by
    dsimp [qbase, qtop]
    rw [hrq_cast]
    have h1 := graphRealizationQuiverPath_cast (W := V)
      (rfl : (graphCoverProjection root).symmetrify.obj
        (show Symmetrify (graphCoverVertex root) from graphCoverRootVertex root) =
        (graphCoverProjection root).symmetrify.obj
          (show Symmetrify (graphCoverVertex root) from graphCoverRootVertex root))
      hxq' q'
    have h2 := graphRealizationQuiverPath_cast (W := V)
      hpstart.symm (rfl : root = root) q
    rw [h1, h2]
    ext t
    rfl
  let ep : P ⁻¹' {graphVertex root} :=
    ⟨graphVertex (V := graphCoverVertex root) (xp : graphCoverVertex root), hep⟩
  let eqp : P ⁻¹' {graphVertex root} :=
    ⟨graphVertex (V := graphCoverVertex root) (xq : graphCoverVertex root), heq⟩
  have hpclass :
      (Path.Homotopic.Quotient.mk plift).map
          ⟨P, cov.continuous⟩ =
        (Path.Homotopic.Quotient.mk ptop).cast e₀.2 hep := by
    rw [← Path.Homotopic.Quotient.mk_map, hpmap, hpbase_cast]
    rfl
  have hqclass :
      (Path.Homotopic.Quotient.mk qlift).map
          ⟨P, cov.continuous⟩ =
        (Path.Homotopic.Quotient.mk qtop).cast e₀.2 heq := by
    rw [← Path.Homotopic.Quotient.mk_map, hqmap, hqbase_cast]
    rfl
  have hpmono : cov.monodromy (Path.Homotopic.Quotient.mk ptop) e₀ = ep := by
    exact cov.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk plift) hpclass
  have hqmono : cov.monodromy (Path.Homotopic.Quotient.mk qtop) e₀ = eqp := by
    exact cov.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk qlift) hqclass
  have hepf : ep = eqp := by
    calc
      ep = cov.monodromy (Path.Homotopic.Quotient.mk ptop) e₀ := hpmono.symm
      _ = cov.monodromy (Path.Homotopic.Quotient.mk qtop) e₀ := by
        congr 1
      _ = eqp := hqmono
  have hvertex :
      graphVertex (V := graphCoverVertex root) (xp : graphCoverVertex root) =
        graphVertex (V := graphCoverVertex root) (xq : graphCoverVertex root) := by
    exact congrArg (fun z : P ⁻¹' {graphVertex root} =>
      (z : graphCoverRealization root)) hepf
  have hxpq : (xp : graphCoverVertex root) = (xq : graphCoverVertex root) := by
    apply graphVertex_injective (V := graphCoverVertex root)
    exact hvertex
  cases hxpq
  have hval : coverSymPathValue rp = coverSymPathValue rq := by
    exact (coverSymPathValue_endpoint (xp : graphCoverVertex root) rp).symm.trans
      (coverSymPathValue_endpoint (xp : graphCoverVertex root) rq)
  have hbase :
      baseSymPathValue ((graphCoverProjection root).symmetrify.mapPath rp) =
        baseSymPathValue ((graphCoverProjection root).symmetrify.mapPath rq) := by
    rw [← coverSymPathValue_eq_baseSymPathValue rp,
      ← coverSymPathValue_eq_baseSymPathValue rq]
    exact hval
  have hbase' := hbase
  rw [hrp_cast, hrq_cast] at hbase'
  have hpcast :
      Quiver.Path.cast rfl hxp' p' =
        Quiver.Path.cast hpstart.symm hxp' p := by
    dsimp [p']
    rw [Quiver.Path.cast_cast]
  have hqcast :
      Quiver.Path.cast rfl hxq' q' =
        Quiver.Path.cast hpstart.symm hxq' q := by
    dsimp [q']
    rw [Quiver.Path.cast_cast]
  have hpvaleq :
      baseSymPathValue (Quiver.Path.cast rfl hxp' p') =
        baseSymPathValue (Quiver.Path.cast hpstart.symm hxp' p) := by
    rw [hpcast]
  have hqvaleq :
      baseSymPathValue (Quiver.Path.cast rfl hxq' q') =
        baseSymPathValue (Quiver.Path.cast hpstart.symm hxq' q) := by
    rw [hqcast]
  have hpval : HEq
      (baseSymPathValue (Quiver.Path.cast rfl hxp' p'))
      (baseSymPathValue p) :=
    (heq_of_eq hpvaleq).trans
      (baseSymPathValue_cast_heq hpstart.symm hxp' p)
  have hqval : HEq
      (baseSymPathValue (Quiver.Path.cast rfl hxq' q'))
      (baseSymPathValue q) :=
    (heq_of_eq hqvaleq).trans
      (baseSymPathValue_cast_heq hpstart.symm hxq' q)
  have hmid : HEq (baseSymPathValue p)
      (baseSymPathValue (Quiver.Path.cast rfl hxq' q')) :=
    hpval.symm.trans (heq_of_eq hbase')
  exact eq_of_heq (hmid.trans hqval)

theorem graphCombinatorialToTopological_injective
    (root : V) :
    Function.Injective (graphCombinatorialToTopological root) := by
  intro g h heq
  revert h
  refine Quot.inductionOn g ?_
  intro p h heq
  revert heq
  refine Quot.inductionOn h ?_
  intro q heq
  change @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) root root at p q
  apply graphCombinatorialToTopological_injective_of_paths root p q
  change (graphFreeGroupoidToTopological (V := V)).map
      (Quot.mk _ p) =
    (graphFreeGroupoidToTopological (V := V)).map (Quot.mk _ q) at heq
  change (graphFreeGroupoidToTopological (V := V)).map (graphBaseSymPathValue p) =
    (graphFreeGroupoidToTopological (V := V)).map (graphBaseSymPathValue q) at heq
  rw [graphFreeGroupoidToTopological_map_path,
    graphFreeGroupoidToTopological_map_path] at heq
  exact heq

/-- The explicit isomorphism between combinatorial and topological graph fundamental groups. -/
noncomputable def graphCombinatorialToTopologicalEquiv
    {V : Type u} [Quiver.{u} V] [WeaklyConnected V] (root : V) :
    graphFundamentalGroup root ≃*
      FundamentalGroup (graphRealization V) (graphVertex root) :=
  MulEquiv.ofBijective (graphCombinatorialToTopological root)
    ⟨graphCombinatorialToTopological_injective root,
      graphCombinatorialToTopological_surjective root⟩

/-- Identifies a finite connected graph's topological fundamental group with a free group. -/
noncomputable def graphTopologicalFundamentalGroupEquiv
    {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V]
    [WeaklyConnected V] (root : V) :
    FundamentalGroup (graphRealization V) (graphVertex root) ≃*
      FreeGroup (Fin (cycleRank (V := V))) :=
  (graphCombinatorialToTopologicalEquiv root).symm.trans
    (graphFundamentalGroupEquiv root)

theorem proved_topological_fundamental_group_free_rank
    {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V]
    [WeaklyConnected V] (root : V) :
    Nonempty (FundamentalGroup (graphRealization V) (graphVertex root) ≃*
      FreeGroup (Fin (edgeCount (V := V) + 1 - vertexCount (V := V)))) := by
  exact ⟨graphTopologicalFundamentalGroupEquiv root⟩

end FiniteGraphFreeGroup
