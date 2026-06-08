/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.Defs
import LeanPool.WhiteheadTheorem.Exponential
import LeanPool.WhiteheadTheorem.Shapes.Maps
import LeanPool.WhiteheadTheorem.Shapes.Pushout
import LeanPool.WhiteheadTheorem.Shapes.UnitInterval
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# LeanPool.WhiteheadTheorem.Shapes.MappingCylinder

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Shapes.MappingCylinder`.
-/

open CategoryTheory
open scoped unitInterval ContinuousMap


universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)


namespace TopCat


/-- The mapping cylinder of a continuous map `f : X ⟶ Y`. -/
noncomputable def MapCyl : TopCat.{u} := Limits.pushout f (Cyl.i₀ X)


namespace MapCyl

/-- `inl` -/
noncomputable abbrev inl : Y ⟶ MapCyl f := Limits.pushout.inl _ _
/-- `inr` -/
noncomputable abbrev inr : TopCat.of (X × I) ⟶ MapCyl f := Limits.pushout.inr _ _
/-- `condition` -/
lemma condition : f ≫ inl f = Cyl.i₀ X ≫ inr f := Limits.pushout.condition

/-- Inclusion map from the domain `X` to the mapping cylinder of `f : X ⟶ Y` -/
noncomputable abbrev domIncl : X ⟶ MapCyl f := Cyl.i₁ X ≫ inr f

/-- Inclusion map from the codomain `Y` to the mapping cylinder of `f : X ⟶ Y` -/
noncomputable alias codIncl := inl

/-- The top surface of the mapping cylinder -/
abbrev top : Set (MapCyl f) := Set.range (domIncl f)



lemma domIncl_hom_eq_pushoutInr'_comp :
    (domIncl f).hom = (pushoutInr' _ _).comp (Cyl.i₁ToComplRangeI₀ X) := by
  ext x
  simp_all only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rfl

theorem isEmbedding_domIncl : Topology.IsEmbedding (domIncl f) := by
  change Topology.IsEmbedding ((domIncl f).hom)
  rw [domIncl_hom_eq_pushoutInr'_comp]
  have em_inr : Topology.IsOpenEmbedding (pushoutInr' f (Cyl.i₀ X)) := by
    apply isOpenEmbedding_pushoutInr'
    apply Cyl.isClosed_range_i₀
  have em_i₁ : Topology.IsClosedEmbedding (Cyl.i₁ToComplRangeI₀ X) := by
    apply Cyl.isClosedEmbedding_i₁ToComplRangeI₀
  convert em_inr.toIsEmbedding.comp em_i₁.toIsEmbedding

/-- The domain `X` of a continuous map `f` is homeomorphic to the top surface of
the mapping cylinder of `f`. -/
noncomputable def domHomeoTop : X ≃ₜ top f := (isEmbedding_domIncl f).toHomeomorph

/-- `domInclToTop` -/
noncomputable def domInclToTop : C(X, top f) := toContinuousMap (domHomeoTop f)
/-- `domInclFromTop` -/
def domInclFromTop : C(top f, MapCyl f) := ⟨Subtype.val, continuous_subtype_val⟩

lemma domIncl_hom_eq_domInclFromTop_comp_domInclToTop :
  (domIncl f).hom = (domInclFromTop f).comp (domInclToTop f) := rfl
lemma domIncl_toFun_eq_domInclFromTop_comp_domInclToTop :
  (domIncl f).hom.toFun = domInclFromTop f ∘ domInclToTop f := rfl

lemma isHomeomorph_domInclToTop : IsHomeomorph (domInclToTop f) :=
  isHomeomorph_iff_exists_homeomorph.mpr ⟨domHomeoTop f, rfl⟩



/-- The retraction from a mapping cylinder of `f : X ⟶ Y` to its base `Y` -/
noncomputable def retr : MapCyl f ⟶ Y :=
  Limits.pushout.desc (𝟙 Y) (Cyl.r₀ X ≫ f)
    (by rw [Category.comp_id, ← Category.assoc, Cyl.i₀_r₀_eq_id, Category.id_comp])

lemma domIncl_retr_eq : domIncl f ≫ retr f = f := by
  unfold domIncl retr
  change Cyl.i₁ X ≫ Limits.pushout.inr f (Cyl.i₀ X) ≫ _ = f
  rw [Limits.pushout.inr_desc, ← Category.assoc, Cyl.i₁_r₀_eq_id, Category.id_comp]
lemma domIncl_retr_eq_assoc : domIncl f ≫ retr f ≫ h = f ≫ h := by
  rw [← Category.assoc, domIncl_retr_eq f]

lemma inl_retr_eq_id : inl f ≫ retr f = 𝟙 Y := by
  change Limits.pushout.inl f (Cyl.i₀ X) ≫ _ = _
  rw [retr, Limits.pushout.inl_desc]
lemma codIncl_retr_eq_id : codIncl f ≫ retr f = 𝟙 Y := inl_retr_eq_id f
-- alias codIncl_retr_eq_id := inl_retr_eq_id

/-- The curried form of the deformation retraction
from a mapping cylinder of `f : X ⟶ Y` to its base `Y`.
This is a curried homotopy from `retr f ≫ inl f` (when `t = 0`) to `𝟙 (MapCyl f)` (when `t = 1`).
The curried form facilitates the proof of continuity (see `MapCyl.equivBase.left_inv`),
and is equal to uncurried form when evaluated at any `t : I`
(see `curriedDeformRetrEvalAt_eq_deformRetrEvalAt`).

Note: `s * t` uses the instance `unitInterval.continuousMul` in `Shapes/Maps.lean`. -/
noncomputable def curriedDeformRetr : MapCyl f ⟶ TopCat.of C(I, MapCyl f) :=
  Limits.pushout.desc (PathSpace.homToConstPaths (inl f))
    (ofHom <| ContinuousMap.curry
      { toFun := fun ⟨⟨x, s⟩, t⟩ ↦ (inr f).hom ⟨x, s * t⟩
        continuous_toFun := by fun_prop } )
    (by
      simp only [PathSpace.homToConstPaths]
      ext x t
      simp only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.curry_apply,
        ContinuousMap.coe_mk, zero_mul]
      exact congr_fun (congr_arg (ContinuousMap.toFun ∘ Hom.hom) (condition f)) x )

/-- `curriedDeformRetrEvalAt` -/
noncomputable def curriedDeformRetrEvalAt (t : I) : MapCyl f ⟶ MapCyl f :=
  ofHom <| (curriedDeformRetr f).hom.uncurry.curryLeft t

lemma curriedDeformRetrEvalAt_hom_apply (t : I) (z : MapCyl f) :
    (curriedDeformRetrEvalAt f t).hom z = ((curriedDeformRetr f).hom z) t :=
  rfl

/-- The homotopy (deformation retraction)
from `retr f ≫ inl f` (when `t = 0`) to `𝟙 (MapCyl f)` (when `t = 1`),
evaluated at `t`. -/
noncomputable def deformRetrEvalAt (t : I) : MapCyl f ⟶ MapCyl f :=
  Limits.pushout.desc (inl f)
    (ofHom (ContinuousMap.id _ |>.prodMap <| ContinuousMap.mulRight t) ≫ inr f)
    -- fun ⟨x, s⟩ ↦ (inr f).hom ⟨x, s * t⟩
    (by
      ext x
      simp only [hom_comp, ContinuousMap.comp_apply, hom_ofHom, ContinuousMap.comp_assoc,
        ContinuousMap.coe_mk, ContinuousMap.prodMap_apply, ContinuousMap.coe_id,
        ContinuousMap.coe_mulRight, Prod.map_apply, id_eq, zero_mul]
      exact congr_fun (congr_arg (ContinuousMap.toFun ∘ Hom.hom) (condition f)) x )

lemma deformRetrEvalAt_zero : deformRetrEvalAt f 0 = retr f ≫ inl f := by
  simp only [deformRetrEvalAt, ContinuousMap.mulRight_zero]
  apply Limits.pushout.hom_ext
  · rw [Limits.pushout.inl_desc, retr]
    change inl f = Limits.pushout.inl f (Cyl.i₀ X) ≫ Limits.pushout.desc (𝟙 Y) (Cyl.r₀ X ≫ f) _ ≫ _
    rw [Limits.pushout.inl_desc_assoc, Category.id_comp]
  · rw [Limits.pushout.inr_desc, retr]
    change ofHom ((ContinuousMap.id ↑X).prodMap (ContinuousMap.const (↑I) 0)) ≫ inr f =
      Limits.pushout.inr f (Cyl.i₀ X) ≫ Limits.pushout.desc (𝟙 Y) (Cyl.r₀ X ≫ f) _ ≫ _
    rw [Limits.pushout.inr_desc_assoc, Category.assoc, condition f, ← Category.assoc]
    congr

lemma deformRetrEvalAt_one : deformRetrEvalAt f 1 = 𝟙 _ := by
  simp only [deformRetrEvalAt, ContinuousMap.mulRight_one]
  apply Limits.pushout.desc_inl_inr

lemma curriedDeformRetrEvalAt_eq_deformRetrEvalAt (t : I) :
    curriedDeformRetrEvalAt f t = deformRetrEvalAt f t := by
  apply Limits.pushout.hom_ext
  · rw [deformRetrEvalAt, Limits.pushout.inl_desc]
    ext y
    simp only [hom_comp, ContinuousMap.comp_apply]
    change ((inl f ≫ curriedDeformRetr f) y) t = _  -- curriedDeformRetrEvalAt_hom_apply
    rw [curriedDeformRetr]
    change ((ConcreteCategory.hom (Limits.pushout.inl f (Cyl.i₀ X) ≫
        Limits.pushout.desc (PathSpace.homToConstPaths (inl f)) _ _)) y) t = _
    rw [Limits.pushout.inl_desc]
    simp only [PathSpace.homToConstPaths, hom_ofHom, ContinuousMap.curry_apply,
      ContinuousMap.coe_mk]
  · rw [deformRetrEvalAt, Limits.pushout.inr_desc]
    ext z
    simp only [hom_comp, ContinuousMap.comp_apply, hom_ofHom, ContinuousMap.prodMap_apply,
      ContinuousMap.coe_id, ContinuousMap.coe_mulRight]
    change ((inr f ≫ curriedDeformRetr f) z) t = _
    rw [curriedDeformRetr]
    change ((ConcreteCategory.hom (Limits.pushout.inr f (Cyl.i₀ X) ≫
        Limits.pushout.desc (PathSpace.homToConstPaths (inl f)) _ _)) z) t = _
    rw [Limits.pushout.inr_desc]
    congr

/-- The mapping cylinder of `f : X ⟶ Y` is homotopy equivalent to its base `Y`. -/
noncomputable def homotopyEquivBase : MapCyl f ≃ₕ Y where
  toFun := (retr f).hom
  invFun := (inl f).hom
  left_inv := Nonempty.intro
    { toContinuousMap := (curriedDeformRetr f).hom.uncurry.argSwap
      map_zero_left z := by
        simp only [ContinuousMap.argSwap, ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe,
          ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply,
          Function.uncurry_apply_pair]
        rw [← curriedDeformRetrEvalAt_hom_apply, curriedDeformRetrEvalAt_eq_deformRetrEvalAt]
        rw [deformRetrEvalAt_zero, hom_comp, ContinuousMap.comp_apply]
      map_one_left z := by
        simp only [ContinuousMap.argSwap, ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe,
          ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply,
          Function.uncurry_apply_pair, ContinuousMap.id_apply]
        rw [← curriedDeformRetrEvalAt_hom_apply, curriedDeformRetrEvalAt_eq_deformRetrEvalAt]
        rw [deformRetrEvalAt_one, hom_id, ContinuousMap.id_apply] }
  right_inv := by rw [← hom_comp, inl_retr_eq_id, hom_id]

/-!
TODO: Show `inl f` is a topological embedding using `inl f ≫ retr f = 𝟙 Y`, i.e.,
using `homotopyEquivBase.right_inv`.
-/

theorem isHomotopyEquiv_retr : IsHomotopyEquiv (retr f).hom :=
  ⟨homotopyEquivBase f, rfl⟩

end MapCyl


end TopCat
