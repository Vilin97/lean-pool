/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# LeanPool.WhiteheadTheorem.Shapes.Pushout

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Shapes.Pushout`.
-/

/-!
TODO:
* Dualize some of the results in `Mathlib.Topology.Category.TopCat.Limits.Pullbacks`
  to give explicit descriptions of the topology on pushouts.
* Simplify the proofs in this file using `Mathlib.CategoryTheory.Limits.Types`.
-/


open CategoryTheory
open CategoryTheory.Limits


universe u

variable {X Y Z : TopCat.{u}}
variable (f : X ⟶ Y) (g : X ⟶ Z)


namespace TopCat

/-- Explicit description of the topology on the pushout -/
lemma pushout_isOpen (s : Set (pushout f g).carrier)
    (hl : IsOpen <| (pushout.inl f g) ⁻¹' s)
    (hr : IsOpen <| (pushout.inr f g) ⁻¹' s) : IsOpen s := by
  rw [TopCat.colimit_isOpen_iff]
  exact fun j ↦ match j with
  | WalkingSpan.zero => by
      change IsOpen ((colimit.ι (span f g) WalkingSpan.zero).hom ⁻¹' s)
      have : colimit.ι (span f g) WalkingSpan.zero = f ≫ pushout.inl f g := by
        change colimit.ι (span f g) WalkingSpan.zero =
          (span f g).map WalkingSpan.Hom.fst ≫ colimit.ι (span f g) WalkingSpan.left
        exact (colimit.w (span f g) WalkingSpan.Hom.fst).symm
      rw [this]
      simp only [span_zero, hom_comp]
      change IsOpen ((pushout.inl f g).hom ∘ f.hom ⁻¹' s)
      rw [Set.preimage_comp]
      apply Continuous.isOpen_preimage (ContinuousMap.continuous _)
      exact hl
  | WalkingSpan.left => hl
  | WalkingSpan.right => hr

/-- Construct a morphism into a discrete space `Y` using a function into `Y`. -/
abbrev homToDiscreteSpaceOfFun {X : TopCat.{u}} {Y : Type u} (f : ↑X → Y) : X ⟶ @TopCat.of Y ⊤ :=
  @TopCat.ofHom _ _ _ ⊤ <| @ContinuousMap.mk _ _ _ ⊤ f continuous_top

open Classical in  -- Decidable (b = a)
/--
In the pushout square below,
the image of `inl` and the image of `inr` cover the space `(pushout f g).carrier`.
```
X ----f----> Y
|            |
g           inl
|            |
v            v
Z ---inr---> pushout f g
```
-/
lemma eq_inl_or_eq_inr_of_mem_pushout (a : (pushout f g).carrier) :
    (∃ y, a = pushout.inl f g y) ∨ (∃ z, a = pushout.inr f g z) := by
  -- Let A' be the union of the pushout with an extra point, with the discrete topology
  let A' := @TopCat.of (Option (pushout f g).carrier) ⊤
  let inl' : Y ⟶ A' := homToDiscreteSpaceOfFun fun y ↦ some (pushout.inl f g y)
  let inr' : Z ⟶ A' := homToDiscreteSpaceOfFun fun z ↦ some (pushout.inr f g z)
  have w' : f ≫ inl' = g ≫ inr' := by
    ext x : 1
    change some ((f ≫ pushout.inl f g) x) = some ((g ≫ pushout.inr f g) x)
    rw [pushout.condition]
  let d1 : pushout f g ⟶ A' := homToDiscreteSpaceOfFun fun b ↦ some b
  let d2 : pushout f g ⟶ A' := homToDiscreteSpaceOfFun fun b ↦ if b = a then none else some b
  by_contra! h
  have : d1 = d2 := by
    apply pushout.hom_ext
    all_goals
      ext y : 1
      simp only [d1, d2, hom_comp, hom_ofHom, ContinuousMap.comp_apply]
      change some _ = if _ = a then _ else _
    · simp only [(h.left y).symm, ↓reduceIte]
    · simp only [(h.right y).symm, ↓reduceIte]
  have d_eq : d1 a = d2 a := by rw [this]
  have d_ne : d1 a ≠ d2 a := by
    change some _ ≠ if _ then _ else _
    simp only [↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]
  exact d_ne d_eq

end TopCat


namespace TopCat

/-- `pushoutInr'` -/
noncomputable abbrev pushoutInr' := (pushout.inr f g).hom.restrict (Set.range g)ᶜ

/--
In the pushout square below, the map `inr` restricted to `{z | z ∉ Set.range g}` is injective.
```
X ----f----> Y
|            |
g           inl
|            |
v            v
Z ---inr---> pushout f g
```
The proof is similar to the one in
https://math.stackexchange.com/questions/3906319/pushout-of-injective-is-injective
TODO: prove this in the category of types.
-/
lemma injective_pushoutInr' : Function.Injective <| pushoutInr' f g := by
  haveI : ∀ z : Z, Decidable (z ∈ Set.range g) := fun _ ↦ Classical.dec _
  obtain emp | nemp := Set.eq_empty_or_nonempty (Set.range g)ᶜ
  · have : IsEmpty {z | z ∉ Set.range g} := Set.isEmpty_coe_sort.mpr emp
    apply Function.injective_of_subsingleton
  · have z₀ : {z | z ∉ Set.range g} := Nonempty.some <| Set.Nonempty.to_subtype nemp
    let Z' := @TopCat.of {z | z ∉ Set.range g} ⊤  -- with the indiscrete topology
    let pZ : Z ⟶ Z' := @TopCat.ofHom _ _ _ ⊤ <| @ContinuousMap.mk _ _ _ ⊤
        (fun z ↦ if _ : z ∉ Set.range g then ⟨z, ‹_›⟩ else z₀) continuous_top
    let pY : Y ⟶ Z' := @TopCat.ofHom _ _ _ ⊤ <| @ContinuousMap.const _ _ _ ⊤ z₀
    let pYZ : pushout f g ⟶ Z' := pushout.desc pY pZ (by
      ext x
      have hgx : g x ∈ Set.range g := Set.mem_range_self x
      simp only [hom_comp, hom_ofHom, ContinuousMap.const_comp, ContinuousMap.comp_apply,
        ContinuousMap.const_apply, ContinuousMap.coe_mk, pY, pZ]
      rw [dif_neg (not_not.mpr hgx)] )
    let inr' := (pushout.inr f g).hom.restrict {z | z ∉ Set.range g}
    change Function.Injective inr'
    have : pYZ.hom ∘ inr' = ContinuousMap.id _ := by
      ext ⟨z, hz⟩
      have heq : (pushout.inr f g ≫ pYZ).hom z =
          (if h : z ∉ Set.range g then (⟨z, h⟩ : {z | z ∉ Set.range g}) else z₀) := by
        rw [pushout.inr_desc]; rfl
      change (pYZ.hom ((pushout.inr f g).hom z) : Z) = _
      have hfinal : (pushout.inr f g ≫ pYZ).hom z = (⟨z, hz⟩ : {z | z ∉ Set.range g}) := by
        rw [heq]
        exact dif_pos hz
      exact congrArg Subtype.val hfinal
    have : Function.Injective (pYZ.hom ∘ inr') := by
      rw [this]
      exact fun ⦃a₁ a₂⦄ a ↦ a
    exact Function.Injective.of_comp this

lemma pushoutInr_neq_pushoutInr_of_mem_compl_range_of_mem_range :
    ∀ z ∈ (Set.range g)ᶜ, ∀ z' ∈ Set.range g, (pushout.inr f g) z ≠ (pushout.inr f g) z' := by
  haveI : ∀ z : Z, Decidable (z ∈ Set.range g) := fun _ ↦ Classical.dec _
  obtain emp | nemp := Set.eq_empty_or_nonempty (Set.range g)ᶜ
  · have : IsEmpty {z | z ∉ Set.range g} := Set.isEmpty_coe_sort.mpr emp
    intro z hz z' hz'
    simp_all only [Set.compl_empty_iff, Set.mem_univ, not_true_eq_false, Set.setOf_false,
      Set.isEmpty_coe_sort, Set.compl_univ, Set.mem_empty_iff_false]
  · have z₀ : {z | z ∉ Set.range g} := Nonempty.some <| Set.Nonempty.to_subtype nemp
    let B := @TopCat.of (ULift Bool) ⊤  -- with the indiscrete topology
    let pZ : Z ⟶ B := @TopCat.ofHom _ _ _ ⊤ <| @ContinuousMap.mk _ _ _ ⊤
        (fun z ↦ if _ : z ∉ Set.range g then ⟨true⟩ else ⟨false⟩) continuous_top
    let pY : Y ⟶ B := @TopCat.ofHom _ _ _ ⊤ <| @ContinuousMap.const _ _ _ ⊤ ⟨false⟩
    let pYZ : pushout f g ⟶ B := pushout.desc pY pZ (by
      ext x
      simp only [hom_comp, hom_ofHom, ContinuousMap.const_comp, ContinuousMap.const_apply,
        Set.mem_range, not_exists, dite_eq_ite, ite_not, ContinuousMap.comp_apply, Bool.false_eq,
        pY, pZ, B]
      have : g x ∈ Set.range g := Set.mem_range_self x
      simp only [Set.mem_range, ContinuousMap.coe_mk, this, ↓reduceIte] )
    intro z hz z' hz'
    have p_neq : pYZ ((pushout.inr f g) z) ≠ pYZ ((pushout.inr f g) z') := by
      change (pushout.inr f g ≫ pYZ) z ≠ (pushout.inr f g ≫ pYZ) z'
      unfold pYZ
      rw [pushout.inr_desc]
      simp only [Set.mem_range, not_exists, dite_eq_ite, ite_not, hom_ofHom, ne_eq, pZ, B]
      simp_all only [Set.mem_compl_iff, Set.mem_range, not_exists, ContinuousMap.coe_mk,
        exists_false, ↓reduceIte, ULift.up.injEq, Bool.true_eq_false, not_false_eq_true, B]
    exact fun heq ↦ p_neq (congrArg pYZ heq)

/-- TODO: re-use the code in `pushoutInr_neq_pushoutInr_of_mem_compl_range_of_mem_range` -/
lemma pushoutInr_neq_pushoutInl_of_mem_compl_range :
    ∀ z ∈ (Set.range g)ᶜ, ∀ y : Y, (pushout.inr f g) z ≠ (pushout.inl f g) y := by
  haveI : ∀ z : Z, Decidable (z ∈ Set.range g) := fun _ ↦ Classical.dec _
  obtain emp | nemp := Set.eq_empty_or_nonempty (Set.range g)ᶜ
  · have : IsEmpty {z | z ∉ Set.range g} := Set.isEmpty_coe_sort.mpr emp
    intro z hz y hy
    simp_all only [Set.compl_empty_iff, Set.mem_univ, not_true_eq_false, Set.setOf_false,
      Set.isEmpty_coe_sort, Set.compl_univ, Set.mem_empty_iff_false]
  · have z₀ : {z | z ∉ Set.range g} := Nonempty.some <| Set.Nonempty.to_subtype nemp
    let B := @TopCat.of (ULift Bool) ⊤  -- with the indiscrete topology
    let pZ : Z ⟶ B := @TopCat.ofHom _ _ _ ⊤ <| @ContinuousMap.mk _ _ _ ⊤
        (fun z ↦ if _ : z ∉ Set.range g then ⟨true⟩ else ⟨false⟩) continuous_top
    let pY : Y ⟶ B := @TopCat.ofHom _ _ _ ⊤ <| @ContinuousMap.const _ _ _ ⊤ ⟨false⟩
    let pYZ : pushout f g ⟶ B := pushout.desc pY pZ (by
      ext x
      simp only [hom_comp, hom_ofHom, ContinuousMap.const_comp, ContinuousMap.const_apply,
        Set.mem_range, not_exists, dite_eq_ite, ite_not, ContinuousMap.comp_apply, Bool.false_eq,
        pY, pZ, B]
      have : g x ∈ Set.range g := Set.mem_range_self x
      simp only [Set.mem_range, ContinuousMap.coe_mk, this, ↓reduceIte] )
    intro z hz y
    have p_neq : pYZ ((pushout.inr f g) z) ≠ pYZ ((pushout.inl f g) y) := by
      have hl : (pushout.inl f g ≫ pYZ).hom y = (⟨false⟩ : ULift Bool) := by
        rw [pushout.inl_desc]; rfl
      have hr : (pushout.inr f g ≫ pYZ).hom z = (⟨true⟩ : ULift Bool) := by
        rw [pushout.inr_desc]
        change (if _ : z ∉ Set.range g then (⟨true⟩ : ULift Bool) else ⟨false⟩) = ⟨true⟩
        exact dif_pos hz
      change (pushout.inr f g ≫ pYZ).hom z ≠ (pushout.inl f g ≫ pYZ).hom y
      rw [hl, hr]
      decide
    exact fun heq ↦ p_neq (congrArg pYZ heq)

lemma _root_.Function.Injective.preimage_image_of_restrict
    (X Y : Type u) (A : Set X) (s : Set A) (f : X → Y)
    (inj_f : Function.Injective (Set.restrict A f)) (hf : ∀ a ∈ A, ∀ b ∉ A, f a ≠ f b) :
    f ⁻¹' ((Set.restrict A f) '' s) = s := by
  apply Set.eq_of_subset_of_subset
  · intro x hx
    obtain ⟨a, has, ha⟩ := hx
    have hxA : x ∈ A := by
      by_contra hnxA
      exact hf a a.property x hnxA ha
    rw [(by rfl : f x = Set.restrict A f ⟨x, hxA⟩)] at ha
    have hax := inj_f ha
    subst hax
    use ⟨x, hxA⟩
  · intro x hx
    apply Set.mem_preimage.mpr
    obtain ⟨a, has, hax⟩ := hx
    subst hax
    exact ⟨a, has, rfl⟩

/--
In the pushout square below, if `g X` is closed in `Z`,
then the map `inr` restricted to `{z | z ∉ Set.range g}` is an open map.
```
X ----f----> Y
|            |
g           inl
|            |
v            v
Z ---inr---> pushout f g
```
-/
lemma isOpenMap_pushoutInr' (hg : IsClosed {z | z ∈ Set.range g}) :
    IsOpenMap <| pushoutInr' f g := by
  haveI : ∀ z : Z, Decidable (z ∈ Set.range g) := fun _ ↦ Classical.dec _
  intro s hs
  apply TopCat.pushout_isOpen
  · simp only []
    have : colimit (span f g) = pushout f g := rfl
    change IsOpen <| (colimit.ι (span f g) WalkingSpan.left) ⁻¹' ((pushoutInr' f g) '' s)
    change IsOpen <| (pushout.inl f g) ⁻¹' ((pushoutInr' f g) '' s)
    have : (pushout.inl f g) ⁻¹' ((pushoutInr' f g) '' s) = ∅ := by
      apply Set.preimage_eq_empty
      have : Set.range (pushout.inl f g).hom = (pushout.inl f g).hom '' Set.univ :=
        Set.image_univ.symm
      rw [this]
      apply Set.disjoint_image_image
      intro z hz y hy
      convert pushoutInr_neq_pushoutInl_of_mem_compl_range f g z z.property y using 2
      rfl
    rw [this]
    exact isOpen_empty
  · simp only []
    change IsOpen <| (pushout.inr f g) ⁻¹' ((pushoutInr' f g) '' s)
    unfold pushoutInr'
    have : (pushout.inr f g) ⁻¹' ((pushoutInr' f g) '' s) = s := by
      apply Function.Injective.preimage_image_of_restrict
      · exact injective_pushoutInr' f g
      · intro z hz z' hz'
        exact pushoutInr_neq_pushoutInr_of_mem_compl_range_of_mem_range f g
          z hz z' (Set.notMem_compl_iff.mp hz')
    rw [this]
    apply IsOpen.isOpenMap_subtype_val (isOpen_compl_iff.mpr hg)
    assumption

/--
In the pushout square below, if `g X` is closed in `Z`,
then the map `inr` restricted to `{z | z ∉ Set.range g}` is an open embedding.
```
X ----f----> Y
|            |
g           inl
|            |
v            v
Z ---inr---> pushout f g
```
-/
theorem isOpenEmbedding_pushoutInr' (hg : IsClosed {z | z ∈ Set.range g}) :
    Topology.IsOpenEmbedding <| pushoutInr' f g := by
  haveI : ∀ z : Z, Decidable (z ∈ Set.range g) := fun _ ↦ Classical.dec _
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (ContinuousMap.continuous _) (injective_pushoutInr' _ _) (isOpenMap_pushoutInr' _ _ hg)

end TopCat
