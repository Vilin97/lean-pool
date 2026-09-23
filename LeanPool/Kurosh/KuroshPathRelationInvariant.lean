/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.Kurosh.KuroshPathRelation

/-!
# Kurosh Path Relation Invariant

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

@[expose] public section

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section
/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshPathRelationInvariantDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α
universe u v
namespace GraphCoveringTheory.Kurosh

theorem catStep {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {b c d : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj
        ((coverPrefunctor G H).symmetrify.obj
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b)
    (e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) b c)
    (q : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj b ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj d) :
    let ep : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj b ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj c := e.toPath
      let en : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj c ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b :=
      (Quiver.reverse e).toPath
    (coverPathLiftData G H
      (catPathToRaw G (p ≫ (𝟙 _ ≫ q)))).x =
      (coverPathLiftData G H
        (catPathToRaw G (p ≫ (ep ≫ en) ≫ q))).x := by
  dsimp only
  let ep : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj b ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj c := e.toPath
  let en : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj c ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b :=
      (Quiver.reverse e).toPath
  have hb := Internal.coverPathLiftData_backtrack_endpoint G H
    (catPathToRaw G p) e
  have ha := Internal.coverPathLiftData_append_endpoint G H
    (catPathToRaw G p)
    (((catPathToRaw G p).comp e.toPath).cons (Quiver.reverse e)) hb.symm
    (catPathToRaw G q)
  have hleft : catPathToRaw G (p ≫ (𝟙 _ ≫ q)) =
      (catPathToRaw G p).comp (catPathToRaw G q) := by
    simp only [Category.id_comp]
    rfl
  have hright : catPathToRaw G (p ≫ (ep ≫ en) ≫ q) =
      (((catPathToRaw G p).comp e.toPath).cons
        (Quiver.reverse e)).comp (catPathToRaw G q) := by
    -- The category-path expression is the same raw path after reassociation.
    rw [← Category.assoc p (ep ≫ en) q, ← Category.assoc p ep en]
    have hcomp : catPathToRaw G (((p ≫ ep) ≫ en) ≫ q) =
        (catPathToRaw G ((p ≫ ep) ≫ en)).comp
          (catPathToRaw G q) := by
      rfl
    have hpe : catPathToRaw G (p ≫ ep) =
        (catPathToRaw G p).cons e := by
      change p ≫ ep = Quiver.Path.cons p e
      rfl
    have hpen0 : catPathToRaw G ((p ≫ ep) ≫ en) =
        (catPathToRaw G (p ≫ ep)).cons (Quiver.reverse e) := by
      change (p ≫ ep) ≫ en =
        Quiver.Path.cons (p ≫ ep) (Quiver.reverse e)
      rfl
    rw [hcomp, hpen0, hpe]
    rfl
  rw [hleft, hright]
  exact ha

theorem catEqv {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p q : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj
        ((coverPrefunctor G H).symmetrify.obj
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) ⟶
      (CategoryTheory.Paths.of
        (Quiver.Symmetrify (RawBassSerreVertex G))).obj a)
    (h : Relation.EqvGen
      (@CategoryTheory.HomRel.CompClosure
        (CategoryTheory.Paths (Quiver.Symmetrify (RawBassSerreVertex G))) _
        (@Quiver.FreeGroupoid.redStep (RawBassSerreVertex G)
          (rawBassSerreQuiver G)) _ _)
      p q) :
    (coverPathLiftData G H (catPathToRaw G p)).x =
      (coverPathLiftData G H (catPathToRaw G q)).x := by
  induction h with
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ih₁ ih₂ => exact ih₁.trans ih₂
  | rel x y hxy =>
      rcases hxy with ⟨A, B, f, m₁, m₂, g, hstep⟩
      cases hstep with
      | step X Z e =>
          exact catStep G H f e g

end GraphCoveringTheory.Kurosh
