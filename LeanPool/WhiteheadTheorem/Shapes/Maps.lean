/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import Mathlib.Topology.UnitInterval
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Category.TopCat.Basic

/-!
# LeanPool.WhiteheadTheorem.Shapes.Maps

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Shapes.Maps`.
-/
-- import Mathlib.Topology.Category.TopCat.Limits.Basic

open scoped Topology unitInterval CategoryTheory


namespace ContinuousMap

lemma mulRight_one (X : Type*) [TopologicalSpace X]
    [mulOne : MulOneClass X] [ContinuousMul X] :
    ContinuousMap.mulRight 1 = ContinuousMap.id X := by
  ext x
  simpa only [coe_mulRight, id_apply] using mulOne.mul_one x

lemma mulRight_zero (X : Type*) [TopologicalSpace X]
    [mulOne : MulZeroClass X] [ContinuousMul X] :
    ContinuousMap.mulRight 0 = ContinuousMap.const X 0 := by
  ext x
  simp only [coe_mulRight]
  exact mulOne.mul_zero x

lemma prodMap_id_id (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    ContinuousMap.prodMap (ContinuousMap.id X) (ContinuousMap.id Y) = ContinuousMap.id _ :=
  rfl

end ContinuousMap



namespace TopCat

-- /-- The cylinder whose base is `A` -/
-- abbrev Cyl (A : TopCat.{u}) : TopCat.{u} := TopCat.of (A × I)

namespace Cyl

/-- The inclusion map a ↦ ⟨a, 0⟩ from `A` to the cylinder whose base is `A` -/
abbrev i₀ (A : TopCat.{u}) : A ⟶ TopCat.of (A × I) :=
  ofHom
    { toFun a := ⟨a, 0⟩
      continuous_toFun := continuous_id.prodMk continuous_const }

/-- The inclusion map a ↦ ⟨a, 1⟩ from `A` to the cylinder whose base is `A` -/
abbrev i₁ (A : TopCat.{u}) : A ⟶ TopCat.of (A × I) :=
  ofHom
    { toFun a := ⟨a, 1⟩
      continuous_toFun := continuous_id.prodMk continuous_const }

/-- The retraction from a cylinder to its base -/
abbrev r₀ (A : TopCat.{u}) : TopCat.of (A × I) ⟶ A :=
  ofHom
    { toFun := fun ⟨a, _⟩ ↦ a
      continuous_toFun := continuous_fst }

@[simp]
lemma i₀_r₀_eq_id {A : TopCat.{u}} : i₀ A ≫ r₀ A = 𝟙 _ := rfl

@[simp]
lemma i₁_r₀_eq_id {A : TopCat.{u}} : i₁ A ≫ r₀ A = 𝟙 _ := rfl

lemma set_neq_zero_eq_compl_range_i₀ (X : TopCat.{u}) :
    {⟨_, t⟩ : TopCat.of (X × I) | t ≠ 0} = (Set.range (Cyl.i₀ X))ᶜ := by
  rw [(by rfl: (Set.range (Cyl.i₀ X))ᶜ = {z | z ∉ Set.range (Cyl.i₀ X)})]
  simp only [ne_eq, hom_ofHom, ContinuousMap.coe_mk, Set.mem_range, not_exists]
  apply Set.eq_of_subset_of_subset
  · intro z hz x heq
    subst heq
    simp only [Set.mem_setOf_eq, not_true_eq_false] at hz
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    obtain ⟨fst, snd⟩ := z
    obtain ⟨val, property⟩ := snd
    simp only [Prod.mk.injEq, not_and, forall_eq] at hz ⊢
    intro a
    simp_all only [not_true_eq_false]

/-- `i₁ToComplRangeI₀` -/
def i₁ToComplRangeI₀ (X : TopCat.{u}) :
    C(X, (Set.range (Cyl.i₀ X)).compl) where
  toFun x := ⟨Cyl.i₁ _ x, by
      rw [(by rfl: (Set.range (Cyl.i₀ X)).compl = {z | z ∉ Set.range (Cyl.i₀ X)})]
      simp_all only [hom_ofHom, ContinuousMap.coe_mk, Set.mem_range, not_exists, Set.mem_setOf_eq,
        Prod.mk.injEq, zero_ne_one, and_false, not_false_eq_true, implies_true] ⟩
  continuous_toFun := (ContinuousMap.continuous _).subtype_mk _

lemma isClosed_range_i₀ (X : TopCat.{u}) :
    IsClosed <| Set.range (Cyl.i₀ X) := by
  have : {xt : TopCat.of (X × I) | xt.snd = 0} = Set.range (Cyl.i₀ X) := by
    apply compl_inj_iff.mp
    rw [← Cyl.set_neq_zero_eq_compl_range_i₀ X]
    ext ⟨fst, t⟩
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  rw [← this]
  exact isClosed_eq continuous_snd continuous_const

lemma isClosedEmbedding_i₁ToComplRangeI₀ (X : TopCat.{u}) :
    Topology.IsClosedEmbedding (Cyl.i₁ToComplRangeI₀ X) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (ContinuousMap.continuous _)
  · unfold Cyl.i₁ToComplRangeI₀
    intro x₁ x₂ hx
    simp_all only [hom_ofHom, ContinuousMap.coe_mk, Subtype.mk.injEq, Prod.mk.injEq, and_true]
  · intro s hs
    have isClosed_of_isClosed_subtype_val
        {X : Type u} [TopologicalSpace X] {A : Set X} {B : Set A}
        (hB : IsClosed (Subtype.val '' B)) : IsClosed B := by
      apply isClosed_induced_iff.mpr
      use Subtype.val '' B
      simp_all only [Subtype.val_injective, Set.preimage_image_eq, and_self]
    change IsClosed ((Cyl.i₁ToComplRangeI₀ X) '' s)
    have : Subtype.val '' ((Cyl.i₁ToComplRangeI₀ X) '' s) = s ×ˢ {1} := by
      unfold Cyl.i₁ToComplRangeI₀ Cyl.i₁
      simp only [hom_ofHom, ContinuousMap.coe_mk]
      ext x : 1
      simp_all only [Set.mem_image, exists_exists_and_eq_and, Set.mem_prod, Set.mem_singleton_iff]
      obtain ⟨fst, snd⟩ := x
      obtain ⟨val, property⟩ := snd
      simp_all only [Prod.mk.injEq, existsAndEq, true_and, and_congr_right_iff]
      intro a
      apply Iff.intro
      · intro a_1
        simp_all only
      · intro a_1
        simp_all only
    have : IsClosed (Subtype.val '' ((Cyl.i₁ToComplRangeI₀ X) '' s)) := by
      rw [this]
      exact IsClosed.prod hs isClosed_singleton
    exact isClosed_of_isClosed_subtype_val this

/-- used in `isEmbedding_domIncl` -/
noncomputable instance decidableInRangeI₀ :
    ∀ z, Decidable (z ∈ Set.range (Cyl.i₀ X)) := fun z ↦ by
  have : z ∈ Set.range (Cyl.i₀ X) ↔ z.snd = 0 := by
    constructor
    · intro hz
      simp_all only [hom_ofHom, ContinuousMap.coe_mk, Set.mem_range]
      obtain ⟨fst, snd⟩ := z
      obtain ⟨val, property⟩ := snd
      obtain ⟨w, h⟩ := hz
      simp_all only [Prod.mk.injEq]
    · intro hz
      simp_all only [hom_ofHom, ContinuousMap.coe_mk, Set.mem_range]
      apply Exists.intro
      · ext : 1
        · rfl
        · ext : 1; simp_all only [Set.Icc.coe_zero]
  rw [this]
  infer_instance

end Cyl


-- /-- The space of paths in `Y` -/
-- abbrev PathSpace (Y : TopCat.{u}) : TopCat.{u} := TopCat.of C(I, Y)

namespace PathSpace

/-- Given a path, return its source point (value at 0).
The continuity of this function, through typeclass resolution,
implicitly relies on the fact that `I` is locally compact. -/
abbrev eval₀ (Y : TopCat.{u}) : TopCat.of C(I, Y) ⟶ Y :=
  ofHom
    { toFun f := f 0
      continuous_toFun := Continuous.eval continuous_id continuous_const }

/-- Given a path, return its target point (value at 1).
The continuity of this function, through typeclass resolution,
implicitly relies on the fact that `I` is locally compact. -/
abbrev eval₁ (Y : TopCat.{u}) : TopCat.of C(I, Y) ⟶ Y :=
  ofHom
    { toFun f := f 1
      continuous_toFun := Continuous.eval continuous_id continuous_const }

/-- `evalAt` -/
abbrev evalAt (Y : TopCat.{u}) (t : I) : TopCat.of C(I, Y) ⟶ Y :=
  ofHom
    { toFun f := f t
      continuous_toFun := Continuous.eval continuous_id continuous_const }

/-- Given a morphism `f : X ⟶ Y`, return a morphism `X ⟶ TopCat.of C(I, Y)`
that sends each point `x : X` to the constant path at `f x : Y`. -/
abbrev homToConstPaths {X Y : TopCat.{u}} (f : X ⟶ Y) : X ⟶ TopCat.of C(I, Y) :=
  ofHom <| ContinuousMap.curry
    { toFun := fun ⟨x, _⟩ ↦ f x
      continuous_toFun := by fun_prop }

end PathSpace

end TopCat
