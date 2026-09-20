/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.Kurosh.KuroshPathInjective

/-!
# Kurosh Path Endpoint

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section
/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshPathEndpointDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α
universe u v
namespace GraphCoveringTheory.Kurosh

theorem test_coverVertexMap_root {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    (coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) =
      RawBassSerreVertex.central 1 := by
  change coverVertexMap G H
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) = _
  simp [coverVertexMk, coverVertexMap_mk, test_rawTreeRepresentative_root]

theorem test_coverPathLiftData_endpoint_eq_of_mapPath {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {x : CoverVertex G H}
    (s : @Quiver.Path (Quiver.Symmetrify (CoverVertex G H))
      (@Quiver.symmetrifyQuiver (CoverVertex G H)
        (coverQuiver G H))
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) x)
    {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      ((coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) v)
    (hobj : (coverPrefunctor G H).symmetrify.obj x = v)
    (hmap : Quiver.Path.cast rfl hobj
      ((coverPrefunctor G H).symmetrify.mapPath s) = p) :
    x = (coverPathLiftData G H p).x := by
  let d := coverPathLiftData G H p
  have hmapd : Quiver.Path.cast rfl d.endpoint
      ((coverPrefunctor G H).symmetrify.mapPath d.path) = p :=
    test_coverPathLiftData_map G H p
  have hvertex : (coverPrefunctor G H).symmetrify.obj x =
      (coverPrefunctor G H).symmetrify.obj d.x := hobj.trans d.endpoint.symm
  have hcast : Quiver.Path.cast rfl hvertex
      ((coverPrefunctor G H).symmetrify.mapPath s) =
        (coverPrefunctor G H).symmetrify.mapPath d.path := by
    have hh := congrArg (fun z =>
        Quiver.Path.cast rfl d.endpoint.symm z) (hmap.trans hmapd.symm)
    simpa [Quiver.Path.cast_cast] using hh
  have hpaths : HEq
      ((coverPrefunctor G H).symmetrify.mapPath s)
      ((coverPrefunctor G H).symmetrify.mapPath d.path) :=
    (Quiver.Path.cast_eq_iff_heq rfl hvertex _ _).mp hcast
  have hstar :
      (coverPrefunctor G H).symmetrify.pathStar
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) ⟨x, s⟩ =
        (coverPrefunctor G H).symmetrify.pathStar
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
            ⟨d.x, d.path⟩ := by
    exact Sigma.ext hvertex hpaths
  have hstar_inj :=
    (coverPrefunctor G H).symmetrify.pathStar_injective
      (fun y =>
        ((test_coverSymmCovering G H).star_bijective y).1)
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) hstar
  exact congrArg Sigma.fst hstar_inj

theorem test_coverPathLiftData_closed_endpoint {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      ((coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1))
      ((coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1))} :
    (coverPathLiftData G H p).x =
      coverVertexMk G H (rawBassSerreOrbitRoot G H) 1 := by
  have h := coverCatPathLiftData_eq_of_target_tree G H
    (rawPathToCat G p)
    (rawPathToCat G
      (Quiver.Path.nil : @Quiver.Path
        (Quiver.Symmetrify (RawBassSerreVertex G))
        (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
          (rawBassSerreQuiver G))
        ((coverPrefunctor G H).symmetrify.obj
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1))
        ((coverPrefunctor G H).symmetrify.obj
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1))))
  simpa [catPathToRaw_rawPathToCat, coverPathLiftData] using h

theorem test_coverVertexMk_eq_root_of_treeKuroshProductToH_eq_one {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (z : CoverSource G H)
    (hz : treeKuroshProductToH G H z = 1) :
    coverVertexMk G H (rawBassSerreOrbitRoot G H) z =
      coverVertexMk G H (rawBassSerreOrbitRoot G H) 1 := by
  let x := coverVertexMk G H (rawBassSerreOrbitRoot G H) z
  have hobj : (coverPrefunctor G H).symmetrify.obj x =
      (coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) := by
    dsimp [x]
    change coverVertexMap G H
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) z) =
      coverVertexMap G H
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
    simp [coverVertexMk, hz, test_rawTreeRepresentative_root]
  let : Quiver.RootedConnected
      (show Quiver.Symmetrify (CoverVertex G H) from
        coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) :=
    test_coverSource_rootedConnected G H
  obtain ⟨s⟩ :=
    @Quiver.RootedConnected.nonempty_path
      (Quiver.Symmetrify (CoverVertex G H))
      (@Quiver.symmetrifyQuiver (CoverVertex G H)
        (coverQuiver G H))
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) _ x
  let t := Quiver.Path.cast rfl hobj
      ((coverPrefunctor G H).symmetrify.mapPath s)
  have hs := test_coverPathLiftData_endpoint_eq_of_mapPath G H s t hobj rfl
  have ht := test_coverPathLiftData_closed_endpoint G H (p := t)
  exact hs.trans ht

end GraphCoveringTheory.Kurosh
