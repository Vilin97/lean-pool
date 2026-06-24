/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.Defs
import LeanPool.QuasiBorelSpaces.MeasureTheory.Pack
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# LeanPool.QuasiBorelSpaces.Basic

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Basic`.
-/

open scoped MeasureTheory


namespace QuasiBorelSpace

variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {C : Type*} {_ : QuasiBorelSpace C}
  {I : Type*} [Countable I]

lemma isVar_cases
    {ix : ℝ → I} {φ : I → ℝ → A}
    (hix : Measurable[_, ⊤] ix) (hφ : ∀ n, IsVar (φ n))
    : IsVar (fun r ↦ φ (ix r) r) := by
  have hI : Nonempty I := ⟨ix 0⟩
  have ⟨k, hk⟩ := Countable.exists_injective_nat I
  have hk' : ∀i, k.invFun (k i) = i := Function.leftInverse_invFun hk
  have hix' : Measurable (fun x ↦ k (ix x)) := Measurable.fun_comp measurable_from_top hix
  have hφk (n) : IsVar (φ (Function.invFun k n)) := by
    simp only [hφ]
  have := isVar_cases' hix' hφk
  simp only [hk'] at this
  apply this

@[simp]
lemma isVar_iff_isHom {A : Type*} {_ : QuasiBorelSpace A} (f : ℝ → A) : IsVar f ↔ IsHom f := by
  apply Iff.intro
  · intro hf
    constructor
    intro φ hφ
    apply isVar_comp hφ hf
  · rintro ⟨hf⟩
    exact hf measurable_id

@[simp]
lemma isHom_ofMeasurableSpace
    {A : Type*} {_ : MeasurableSpace A} (φ : ℝ → A)
    : IsHom[_, ofMeasurableSpace] φ ↔ Measurable φ := by
  rw [←isVar_iff_isHom]
  rfl

instance {A : Type*} {_ : MeasurableSpace A} : @MeasurableQuasiBorelSpace A ofMeasurableSpace _ :=
  @MeasurableQuasiBorelSpace.mk A ofMeasurableSpace _ fun _ ↦ by
    simp only [isHom_ofMeasurableSpace]

lemma isHom_def
    {A : Type*} {_ : QuasiBorelSpace A}
    {B : Type*} {_ : QuasiBorelSpace B}
    (f : A → B)
    : IsHom f ↔ (∀⦃φ : ℝ → A⦄, IsHom φ → IsHom fun x ↦ f (φ x)) := by
  apply Iff.intro
  · rintro ⟨hf⟩
    simp only [isVar_iff_isHom] at hf
    exact hf
  · intro hf
    constructor
    simpa only [isVar_iff_isHom] using hf

namespace IsHom

instance {f : A → B}
    : CoeFun (IsHom f) (fun _ ↦ ∀⦃φ : ℝ → A⦄, IsHom φ → IsHom fun x ↦ f (φ x)) where
  coe := by
    rw [←isHom_def]
    simp only [imp_self]

end IsHom

@[simp]
lemma isHom_iff_measurable
    {_ : MeasurableSpace A} [MeasurableQuasiBorelSpace A]
    (φ : ℝ → A)
    : IsHom φ ↔ Measurable φ :=
  MeasurableQuasiBorelSpace.isHom_iff_measurable φ

@[fun_prop]
lemma isHom_of_measurable
    {_ : MeasurableSpace A} [MeasurableQuasiBorelSpace A]
    {_ : MeasurableSpace B} [MeasurableQuasiBorelSpace B]
    (f : A → B) (hf : Measurable f)
    : IsHom f := by
  rw [isHom_def]
  simp only [isHom_iff_measurable]
  fun_prop

@[simp]
lemma isHom_id : IsHom (A := A) id := by
  rw [isHom_def]
  simp only [id_eq, imp_self, implies_true]

@[fun_prop, simp]
lemma isHom_id' : IsHom (fun x : A ↦ x) :=
  isHom_id

lemma isHom_comp
    {f : B → C} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (f ∘ g) := by
  rw [isHom_def]
  intro φ hφ
  exact hf (hg hφ)

@[fun_prop]
lemma isHom_comp'
    {f : B → C} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (fun x ↦ f (g x)) :=
  isHom_comp hf hg

@[simp]
lemma isHom_const (x : B) : IsHom (Function.const A x) := by
  constructor
  simp only [isVar_const, Function.const, implies_true]

@[fun_prop, simp]
lemma isHom_const' (x : B) : IsHom (fun _ : A ↦ x) :=
  isHom_const x

lemma isHom_cases
    {ix : A → I} {f : I → A → B}
    (hix : IsHom[_, default] ix) (hf : ∀ n, IsHom (f n))
    : IsHom (fun x ↦ f (ix x) x) := by
  constructor
  intro φ hφ
  simp only [isVar_iff_isHom] at hφ
  apply isVar_cases (ix := fun x ↦ ix (φ x)) (φ := fun n x ↦ f n (φ x))
  · replace hix := hix hφ
    simp only [isHom_ofMeasurableSpace] at hix
    exact hix
  · intro n
    simp only [isVar_iff_isHom]
    refine hf _ ?_
    apply hφ

@[simp, fun_prop]
lemma isHom_of_discrete_countable
    {_ : MeasurableSpace A} [DiscreteQuasiBorelSpace A] [Countable A]
    (f : A → B) : IsHom f := by
  apply isHom_cases (ix := fun x ↦ x) (f := fun x _ ↦ f x)
  · rw [isHom_def]
    intro φ hφ
    simp only [isHom_iff_measurable, isHom_ofMeasurableSpace] at ⊢ hφ
    intro X hX
    apply hφ
    apply MeasurableSet.of_discrete
  · fun_prop

@[simp]
lemma isHom_to_subsingleton [Subsingleton B] (f : A → B) : IsHom f := by
  rw [isHom_def]
  intro φ hφ
  have : ∀r, f (φ r) = f (φ 0) := by subsingleton
  simp only [this, isHom_const']

@[simp]
lemma isHom_of_subsingleton [Subsingleton A] (f : A → B) : IsHom f := by
  rw [isHom_def]
  intro φ hφ
  have : ∀r, φ r = φ 0 := by subsingleton
  simp only [this, isHom_const']

lemma isHom_of_lift {A} (f : A → B) : IsHom[lift f, _] f := by
  apply @IsHom.intro _ _ (lift f)
  intro φ hφ
  apply hφ

lemma isHom_to_lift
    {A} (f : A → B) (g : C → A)
    : IsHom[_, lift f] g ↔ IsHom (fun x ↦ f (g x)) := by
  apply Iff.intro
  · rintro ⟨hg⟩
    constructor
    exact hg
  · rintro ⟨hg⟩
    apply @IsHom.intro _ _ _ (lift f)
    exact hg

@[fun_prop]
lemma isHom_unpack
    [Nonempty A] {_ : MeasurableSpace A} [MeasurableQuasiBorelSpace A] [StandardBorelSpace A]
    : IsHom (MeasureTheory.unpack (A := A)) := by
  simp only [isHom_iff_measurable, MeasureTheory.measurable_unpack]

@[fun_prop]
lemma isHom_mem_Icc {a b : ℝ} : IsHom (· ∈ Set.Icc a b) := by
  simp only [isHom_ofMeasurableSpace, measurable_mem, measurableSet_Icc]

lemma isHom_cast
    {B} {instB : QuasiBorelSpace B}
    {C} {instC : QuasiBorelSpace C}
    {eq : B = C} (heq : ∀ (φ : ℝ → B), IsHom φ ↔ IsHom fun x ↦ cast eq (φ x))
    (f : A → B)
    : IsHom (fun x ↦ cast eq (f x)) ↔ IsHom f := by
  subst eq
  have : instB = instC := by
    ext
    simp only [isVar_iff_isHom]
    apply heq
  subst this
  rfl

@[fun_prop]
lemma measurable_of_isHom
    {_ : MeasurableSpace A} [MeasurableQuasiBorelSpace A]
    {_ : MeasurableSpace B} [MeasurableQuasiBorelSpace B] [StandardBorelSpace B]
    (f : B → A) (hf : IsHom f)
    : Measurable f := by
  wlog hB : Nonempty B
  · simp only [not_nonempty_iff] at hB
    apply measurable_of_empty
  have : f = (fun a ↦ f (MeasureTheory.unpack a)) ∘ MeasureTheory.pack := by
    ext
    simp only [Function.comp_apply, MeasureTheory.unpack_pack]
  rw [this]
  apply Measurable.comp
  · rw [← MeasurableQuasiBorelSpace.isHom_iff_measurable]
    apply isHom_comp
    · exact hf
    · rw [MeasurableQuasiBorelSpace.isHom_iff_measurable]
      fun_prop
  · simp only [MeasureTheory.measurable_pack]

namespace NonEmpty

@[fun_prop]
lemma isHom_some (f : A → Nonempty B) : IsHom fun x ↦ (f x).some := by
  rw [isHom_def]
  intro φ hφ
  change IsHom fun _ ↦ (f (φ 0)).some
  apply isHom_const

end NonEmpty

lemma isHom_mono
    {B : Type*} {f : A → B} {inst₁ inst₂ : QuasiBorelSpace B}
    (hf : IsHom[_, inst₁] f)
    (hinst : ∀ φ : ℝ → B, inst₁.IsVar φ → inst₂.IsVar φ)
    : IsHom[_, inst₂] f := by
  rw [isHom_def] at ⊢ hf
  intro φ hφ
  specialize hf hφ
  rw [← isVar_iff_isHom] at ⊢ hf
  apply hinst
  apply hf

lemma measurableSet_toMeasurableSpace
    (X : Set A)
    : MeasurableSet[toMeasurableSpace] X
    ↔ ∀{φ : ℝ → A}, IsHom φ → MeasurableSet (φ ⁻¹' X) := by
  rfl

end QuasiBorelSpace
