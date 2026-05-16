/-
Copyright (c) 2026 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Condensed.Light.Epi
import Mathlib.Condensed.Light.Explicit
import Mathlib.Condensed.Light.Functors
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Common
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Spectral.Prespectral

/-!
# Effective epimorphisms in light condensed sets

The Yoneda embedding `lightProfiniteToLightCondSet` preserves epimorphisms
and effective epimorphisms. This file gives explicit colimit cones
exhibiting an effective epimorphism `π : X ⟶ Y` in `LightProfinite` as a
coequalizer of its pullback projections inside `LightCondSet`.
-/

open Function CategoryTheory Limits Opposite

universe u

lemma surj_pullback' {X Y Z : LightProfinite.{u}} (f : X ⟶ Z) {g : Y ⟶ Z}
    (hf : Function.Surjective f) : Function.Surjective (CompHausLike.pullback.snd f g) := by
  intro y
  obtain ⟨x, hx⟩ := hf (g y)
  refine ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

instance : lightProfiniteToLightCondSet.PreservesEpimorphisms := {
  preserves f hf := (LightCondSet.epi_iff_locallySurjective_on_lightProfinite _).mpr
    fun _ g ↦ ⟨CompHausLike.pullback f g,
      CompHausLike.pullback.snd _ _,
      surj_pullback' f ((LightProfinite.epi_iff_surjective f).mp hf),
      CompHausLike.pullback.fst _ _,
      CompHausLike.pullback.condition _ _⟩ }

/-- The parallel pair of pullback projections, mapped into `LightCondSet`. -/
noncomputable def πpair {X Y : LightProfinite} (π : X ⟶ Y) : WalkingParallelPair ⥤ LightCondSet :=
  parallelPair
    (lightProfiniteToLightCondSet.map <| CompHausLike.pullback.fst π π)
    (lightProfiniteToLightCondSet.map <| CompHausLike.pullback.snd π π)

/-- The regular cofork on `π : X ⟶ Y` in `LightCondSet`, given by mapping
`π` itself through the Yoneda embedding. -/
noncomputable def regular {X Y : LightProfinite} (π : X ⟶ Y) :
    Cofork (lightProfiniteToLightCondSet.map <| CompHausLike.pullback.fst π π)
      (lightProfiniteToLightCondSet.map <| CompHausLike.pullback.snd π π) :=
  Cofork.ofπ (lightProfiniteToLightCondSet.map <| π) (by
    rw [← lightProfiniteToLightCondSet.map_comp, ← lightProfiniteToLightCondSet.map_comp,
      CompHausLike.pullback.condition])

/-- Abbreviation for cones over `πpair π`. -/
def cfork {X Y : LightProfinite} (π : X ⟶ Y) :=
  Cofork (lightProfiniteToLightCondSet.map (CompHausLike.pullback.fst π π))
    (lightProfiniteToLightCondSet.map (CompHausLike.pullback.snd π π))

/-- The element of `cone.pt.obj.obj (op Y)` corresponding to a cone on the
pullback parallel pair of an effective epimorphism `π`. -/
noncomputable def regularLiftElem {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π]
    (cone : cfork π) : cone.pt.obj.obj (op Y) :=
  let fX := yonedaEquiv cone.π.hom
  have : cone.pt.obj.map (CompHausLike.pullback.fst π π).op fX =
      cone.pt.obj.map (CompHausLike.pullback.snd π π).op fX := by
    have this : (lightProfiniteToLightCondSet.map (CompHausLike.pullback.fst π π) ≫ cone.π).hom =
      (yoneda.map (CompHausLike.pullback.fst π π) ≫ cone.π.hom) := rfl
    have this' : (lightProfiniteToLightCondSet.map (CompHausLike.pullback.snd π π) ≫ cone.π).hom =
      (yoneda.map (CompHausLike.pullback.snd π π) ≫ cone.π.hom) := rfl
    erw [yonedaEquiv_naturality (F := cone.pt.obj) cone.π.hom (CompHausLike.pullback.fst π π),
      yonedaEquiv_naturality (F := cone.pt.obj) cone.π.hom (CompHausLike.pullback.snd π π),
      ← this, ← this', cone.condition]
  LightCondensed.equalizerCondition cone.pt
    |>.bijective_mapToEqualizer_pullback' _ (CompHausLike.pullback.isLimit π π)
    |>.surjective ⟨fX, this⟩
    |>.choose

private lemma cone_elem {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π] (cone : cfork π) :
    cone.pt.obj.map (CompHausLike.pullback.fst π π).op (yonedaEquiv cone.π.hom) =
      cone.pt.obj.map (CompHausLike.pullback.snd π π).op (yonedaEquiv cone.π.hom) := by
  have this : (lightProfiniteToLightCondSet.map (CompHausLike.pullback.fst π π) ≫ cone.π).hom =
    (yoneda.map (CompHausLike.pullback.fst π π) ≫ cone.π.hom) := rfl
  have this' : (lightProfiniteToLightCondSet.map (CompHausLike.pullback.snd π π) ≫ cone.π).hom =
    (yoneda.map (CompHausLike.pullback.snd π π) ≫ cone.π.hom) := rfl
  rw [yonedaEquiv_naturality (F := cone.pt.obj) cone.π.hom (CompHausLike.pullback.fst π π),
    yonedaEquiv_naturality (F := cone.pt.obj) cone.π.hom (CompHausLike.pullback.snd π π),
    ← this, ← this', cone.condition]

/-- The lift `Y ⟶ cone.pt` produced by an effective epimorphism `π : X ⟶ Y`. -/
noncomputable def regularLift {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π]
    (cone : cfork π) : lightProfiniteToLightCondSet.obj Y ⟶ cone.pt :=
  ObjectProperty.homMk (yonedaEquiv.symm (regularLiftElem π cone))

private lemma regularLift_prop {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π]
    (cone : cfork π) :
    regularTopology.mapToEqualizer cone.pt.obj π
      (CompHausLike.pullback.fst π π)
      (CompHausLike.pullback.snd π π)
      (CompHausLike.pullback.condition _ _)
      (regularLiftElem π cone) =
    ⟨yonedaEquiv cone.π.hom, cone_elem π cone⟩ :=
  LightCondensed.equalizerCondition cone.pt
    |>.bijective_mapToEqualizer_pullback' _ (CompHausLike.pullback.isLimit π π)
    |>.surjective ⟨yonedaEquiv cone.π.hom, cone_elem π cone⟩
    |>.choose_spec

lemma regularLift_comp {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π] (cone : cfork π) :
    (regular π).π ≫ regularLift π cone = cone.π := by
  refine Sheaf.hom_ext (yonedaEquiv.injective ?_)
  change yonedaEquiv (yoneda.map π ≫ yonedaEquiv.symm (regularLiftElem π cone)) =
    yonedaEquiv cone.π.hom
  rw [← yonedaEquiv_naturality (F := cone.pt.obj) _ π, Equiv.apply_symm_apply]
  have h := regularLift_prop π cone
  exact (Subtype.ext_iff.mp h)

lemma regularLift_unique {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π] (cone : cfork π)
    (m : (lightProfiniteToLightCondSet.obj Y) ⟶ cone.pt) (hm : (regular π).π ≫ m = cone.π) :
    m = regularLift π cone := by
  erw [Cofork.π_ofπ, ← regularLift_comp π cone] at hm
  exact Epi.left_cancellation _ _ hm

/-- The `regular` cofork is a colimit. -/
noncomputable abbrev regular_IsColimit {X Y : LightProfinite} (π : X ⟶ Y)
    [EffectiveEpi π] : IsColimit (regular π) :=
  Cofork.IsColimit.mk _ (regularLift π) (regularLift_comp π) (regularLift_unique π)

/-- Any epimorphism `π : X ⟶ Y` in `LightProfinite` gives a colimit `regular` cofork
in `LightCondSet`. -/
noncomputable def explicitRegularIsColimit {X Y : LightProfinite} (π : X ⟶ Y) [hepi : Epi π] :
    IsColimit (regular π) := by
  rw [LightProfinite.epi_iff_surjective, ← LightProfinite.effectiveEpi_iff_surjective] at hepi
  exact regular_IsColimit π

noncomputable instance {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π] :
    IsRegularEpi (lightProfiniteToLightCondSet.map π) := ⟨⟨{
  W := lightProfiniteToLightCondSet.obj (CompHausLike.pullback π π)
  left := lightProfiniteToLightCondSet.map (CompHausLike.pullback.fst π π)
  right := lightProfiniteToLightCondSet.map (CompHausLike.pullback.snd π π)
  w := by
    rw [← lightProfiniteToLightCondSet.map_comp, ← lightProfiniteToLightCondSet.map_comp,
      CompHausLike.pullback.condition]
  isColimit := regular_IsColimit π }⟩⟩

instance : lightProfiniteToLightCondSet.PreservesEffectiveEpis where
  preserves _ _ := inferInstance
