/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.Kurosh.KuroshPathRelationInvariant

/-!
# Kurosh Path Injective

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section
/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshPathInjectiveDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α
universe u v
namespace GraphCoveringTheory.Kurosh

/-- Interpret a raw symmetrified Bass-Serre path in the path category. -/
def rawPathToCat {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    {a b : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) a b) :
    (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj a ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b := p

theorem rawPathToCat_catPathToRaw {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj a ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b) :
    rawPathToCat G (catPathToRaw G p) = p := rfl

theorem catPathToRaw_rawPathToCat {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) a b) :
    catPathToRaw G (rawPathToCat G p) = p := rfl

theorem coverPathLiftData_eq_of_quotient_map_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p q : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      ((coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) a)
    (h :
      (CategoryTheory.Quotient.functor
        (@Quiver.FreeGroupoid.redStep (RawBassSerreVertex G)
          (rawBassSerreQuiver G))).map (rawPathToCat G p) =
      (CategoryTheory.Quotient.functor
        (@Quiver.FreeGroupoid.redStep (RawBassSerreVertex G)
          (rawBassSerreQuiver G))).map (rawPathToCat G q)) :
    (coverPathLiftData G H p).x =
      (coverPathLiftData G H q).x := by
  have hrel : Relation.EqvGen
      (@CategoryTheory.HomRel.CompClosure
        (CategoryTheory.Paths (Quiver.Symmetrify (RawBassSerreVertex G))) _
        (@Quiver.FreeGroupoid.redStep (RawBassSerreVertex G)
          (rawBassSerreQuiver G)) _ _)
      (rawPathToCat G p) (rawPathToCat G q) :=
    (CategoryTheory.Quotient.functor_homRel_eq_compClosure_eqvGen
      (@Quiver.FreeGroupoid.redStep (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      (rawPathToCat G p) (rawPathToCat G q)).mp h
  have hcat := catEqv G H (rawPathToCat G p) (rawPathToCat G q) hrel
  simpa only [catPathToRaw_rawPathToCat] using hcat

theorem testRawFreeGroupoid_hom_subsingleton {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    {x y : Quiver.FreeGroupoid (RawBassSerreVertex G)} :
    Subsingleton (x ⟶ y) := by
  let : Quiver.RootedConnected
      (show Quiver.Symmetrify (RawBassSerreVertex G) from
        RawBassSerreVertex.central 1) := rawBassSerre_rootedConnected G
  let : IsConnected (Quiver.FreeGroupoid (RawBassSerreVertex G)) :=
    testFreeGroupoid_isConnected_of_rootedConnected
      (RawBassSerreVertex.central 1)
  obtain ⟨p⟩ := CategoryTheory.nonempty_hom_of_preconnected_groupoid
    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
      (RawBassSerreVertex.central 1)) x
  obtain ⟨q⟩ := CategoryTheory.nonempty_hom_of_preconnected_groupoid
    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
      (RawBassSerreVertex.central 1)) y
  constructor
  intro f g
  have hroot : p ≫ f ≫ Groupoid.inv q =
      p ≫ g ≫ Groupoid.inv q := by
    exact @Subsingleton.elim _ (testRawFreeGroupoid_end_subsingleton G) _ _
  have hcancel := congrArg
    (fun z => Groupoid.inv p ≫ z ≫ q) hroot
  simpa [Category.assoc] using hcancel

theorem coverCatPathLiftData_eq_of_target_tree {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p q : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj
        ((coverPrefunctor G H).symmetrify.obj
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) ⟶
      (CategoryTheory.Paths.of
        (Quiver.Symmetrify (RawBassSerreVertex G))).obj a) :
    (coverPathLiftData G H (catPathToRaw G p)).x =
      (coverPathLiftData G H (catPathToRaw G q)).x := by
  have hquot :
      (CategoryTheory.Quotient.functor
        (@Quiver.FreeGroupoid.redStep (RawBassSerreVertex G)
          (rawBassSerreQuiver G))).map p =
      (CategoryTheory.Quotient.functor
        (@Quiver.FreeGroupoid.redStep (RawBassSerreVertex G)
          (rawBassSerreQuiver G))).map q := by
    exact @Subsingleton.elim _ (testRawFreeGroupoid_hom_subsingleton G) _ _
  have hrel : Relation.EqvGen
      (@CategoryTheory.HomRel.CompClosure
        (CategoryTheory.Paths (Quiver.Symmetrify (RawBassSerreVertex G))) _
        (@Quiver.FreeGroupoid.redStep (RawBassSerreVertex G)
          (rawBassSerreQuiver G)) _ _)
      p q :=
    (CategoryTheory.Quotient.functor_homRel_eq_compClosure_eqvGen
      (@Quiver.FreeGroupoid.redStep (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) p q).mp hquot
  exact catEqv G H p q hrel

end GraphCoveringTheory.Kurosh
