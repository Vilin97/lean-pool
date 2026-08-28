/-
Copyright (c) 2026 Arthur Freitas Ramos, David Hulak, Ruy de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Hulak, Ruy de Queiroz
-/

import Mathlib.Combinatorics.Quiver.Covering
import LeanPool.FiniteGraphFundamentalGroup.Proof

/-!
# The path-lifting graph cover

This module constructs the standard combinatorial unfolding of a rooted quiver.
-/

open CategoryTheory Quiver

noncomputable section

universe u

namespace FiniteGraphFreeGroup

/-!
# The path-lifting cover

For a root `r`, a vertex of the cover remembers both a graph vertex `v` and a
morphism from `r` to `v` in the free groupoid.  An edge is a base edge whose
lift has exactly the prescribed endpoint.  This is the standard combinatorial
unfolding construction; the covering proof below is independent of the rank
calculation.
-/

/-- Vertices of the path-lifting cover over a chosen root. -/
abbrev graphCoverVertex {V : Type u} [Quiver.{u} V] (root : V) :=
  Σ v : V, ((Quiver.FreeGroupoid.of V).obj root ⟶
    (Quiver.FreeGroupoid.of V).obj v)

/-- The lifted edges whose endpoint is prescribed by composition in the free groupoid. -/
instance graphCoverQuiver {V : Type u} [Quiver.{u} V] (root : V) :
    Quiver (graphCoverVertex root) where
  Hom x y := {e : x.1 ⟶ y.1 //
    x.2 ≫ (Quiver.FreeGroupoid.of V).map e = y.2}

/-- The projection from the path-lifting cover to the original quiver. -/
def graphCoverProjection {V : Type u} [Quiver.{u} V] (root : V) :
    graphCoverVertex root ⥤q V where
  obj x := x.1
  map e := e.1

lemma graphCoverStar_ext {V : Type u} [Quiver.{u} V] {root : V}
    {x z y : graphCoverVertex root} (hy : z = y)
    {f : x ⟶ z} {e : x ⟶ y} (h : HEq f.1 e.1) :
    (⟨z, f⟩ : Quiver.Star x) = ⟨y, e⟩ := by
  cases hy
  refine Sigma.ext rfl ?_
  exact heq_of_eq (Subtype.ext (eq_of_heq h))

lemma graphCoverCostar_ext {V : Type u} [Quiver.{u} V] {root : V}
    {x z y : graphCoverVertex root} (hy : z = y)
    {f : z ⟶ x} {e : y ⟶ x} (h : HEq f.1 e.1) :
    (⟨z, f⟩ : Quiver.Costar x) = ⟨y, e⟩ := by
  cases hy
  refine Sigma.ext rfl ?_
  exact heq_of_eq (Subtype.ext (eq_of_heq h))

/-- Explicit lifting of a star at a cover vertex. -/
def graphCoverStarEquiv {V : Type u} [Quiver.{u} V] (root : V)
    (x : graphCoverVertex root) :
    Quiver.Star x ≃ Quiver.Star x.1 where
  toFun := (graphCoverProjection root).star x
  invFun := fun e =>
    ⟨⟨e.1, x.2 ≫ (Quiver.FreeGroupoid.of V).map e.2⟩,
      ⟨e.2, rfl⟩⟩
  left_inv := by
    rintro ⟨y, e⟩
    have hy :
        (⟨y.1, x.2 ≫ (Quiver.FreeGroupoid.of V).map e.1⟩ :
          graphCoverVertex root) = y := by
      apply Sigma.ext
      · rfl
      · exact heq_of_eq e.property
    let z : graphCoverVertex root :=
      ⟨y.1, x.2 ≫ (Quiver.FreeGroupoid.of V).map e.1⟩
    let f : x ⟶ z := ⟨e.1, rfl⟩
    change (⟨z, f⟩ : Quiver.Star x) = ⟨y, e⟩
    exact graphCoverStar_ext hy HEq.rfl
  right_inv := by
    rintro ⟨y, e⟩
    rfl

/-- Explicit lifting of a costar at a cover vertex. -/
def graphCoverCostarEquiv {V : Type u} [Quiver.{u} V] (root : V)
    (x : graphCoverVertex root) :
    Quiver.Costar x ≃ Quiver.Costar x.1 where
  toFun := (graphCoverProjection root).costar x
  invFun := fun e =>
    ⟨⟨e.1, x.2 ≫ Groupoid.inv ((Quiver.FreeGroupoid.of V).map e.2)⟩,
      ⟨e.2, by simp [Category.assoc]⟩⟩
  left_inv := by
    rintro ⟨y, e⟩
    have hpath :
        x.2 ≫ Groupoid.inv ((Quiver.FreeGroupoid.of V).map e.1) = y.2 := by
      calc
        x.2 ≫ Groupoid.inv ((Quiver.FreeGroupoid.of V).map e.1) =
            (y.2 ≫ (Quiver.FreeGroupoid.of V).map e.1) ≫
              Groupoid.inv ((Quiver.FreeGroupoid.of V).map e.1) :=
          congrArg (fun q => q ≫ Groupoid.inv ((Quiver.FreeGroupoid.of V).map e.1))
            e.property.symm
        _ = y.2 := by simp [Category.assoc]
    have hy :
        (⟨y.1, x.2 ≫ Groupoid.inv ((Quiver.FreeGroupoid.of V).map e.1)⟩ :
          graphCoverVertex root) = y := by
      apply Sigma.ext
      · rfl
      · exact heq_of_eq hpath
    let z : graphCoverVertex root :=
      ⟨y.1, x.2 ≫ Groupoid.inv ((Quiver.FreeGroupoid.of V).map e.1)⟩
    let f : z ⟶ x := ⟨e.1, by simp [z, Category.assoc]⟩
    change (⟨z, f⟩ : Quiver.Costar x) = ⟨y, e⟩
    exact graphCoverCostar_ext hy HEq.rfl
  right_inv := by
    rintro ⟨y, e⟩
    rfl

/-- The path-lifting projection is a covering of quivers. -/
theorem graphCoverProjection_isCovering {V : Type u} [Quiver.{u} V] (root : V) :
    (graphCoverProjection root).IsCovering := by
  refine ⟨fun x => (graphCoverStarEquiv root x).bijective,
    fun x => (graphCoverCostarEquiv root x).bijective⟩

end FiniteGraphFreeGroup
