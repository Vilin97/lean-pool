/-
Copyright (c) 2026 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.Condensed.Light.Explicit
import Mathlib.Condensed.Light.Functors

/-!
# Preservation of finite coproducts by the topology-level Yoneda

For a subcanonical Grothendieck topology `J` such that every sheaf
preserves finite products, the canonical embedding `J.yoneda` preserves
finite coproducts. As a corollary, the light-profinite to light
condensed-set functor preserves finite coproducts.
-/

open CategoryTheory Functor Opposite Limits Function GrothendieckTopology

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [Subcanonical J]
  [∀ X : Sheaf J (Type v), PreservesFiniteProducts X.obj]
  [HasWeakSheafify J (Type v)]

instance {n : ℕ} (S : Fin n → C) :
    PreservesColimit (Discrete.functor S) J.yoneda where
  preserves {c} hc := ⟨by
    suffices IsLimit (coyoneda.mapCone (J.yoneda.mapCocone c).op) from
      isColimitOfOp (isLimitOfReflects _ this)
    apply evaluationJointlyReflectsLimits
    intro X
    let i : (J.yoneda.op ⋙ coyoneda ⋙
        ((evaluation (Sheaf J (Type v)) (Type (max u v))).obj X)) ≅ X.obj ⋙ uliftFunctor := by
      refine NatIso.ofComponents (fun Y ↦ equivEquivIso (J.yonedaEquiv.trans Equiv.ulift.symm)) ?_
      intro Y Z f
      ext a
      apply ULift.ext
      exact (J.yonedaEquiv_naturality' a f).symm
    suffices IsLimit ((X.obj ⋙ uliftFunctor).mapCone c.op) from IsLimit.mapConeEquiv i.symm this
    have := preservesLimitsOfShape_of_equiv (Discrete.opposite (Fin n)).symm X.obj
    exact isLimitOfPreserves _ hc.op⟩

instance Subcanonical.preservesFiniteCoproductsYoneda :
    PreservesFiniteCoproducts J.yoneda where
  preserves _ := { preservesColimit {S} :=
    let i : S ≅ Discrete.functor (fun i ↦ S.obj ⟨i⟩) := Discrete.natIso (fun _ ↦ Iso.refl _)
    preservesColimit_of_iso_diagram J.yoneda i.symm }

instance : PreservesFiniteCoproducts lightProfiniteToLightCondSet.{u} :=
  Subcanonical.preservesFiniteCoproductsYoneda
