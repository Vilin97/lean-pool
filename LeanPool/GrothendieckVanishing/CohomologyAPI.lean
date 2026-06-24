/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Skyscraper
import LeanPool.GrothendieckVanishing.ClosedImmersion

/-!
# Sheaf Cohomology API

Centralizes results about sheaf cohomology `Sheaf.H`, keeping the underlying `Ext`
calculations internal so downstream files never need to unfold `Sheaf.H` directly.

## Main results

* `subsingleton_sheafH_of_shortExact_middle`: middle-term cohomology vanishing
* `sheafH_subsingleton_of_isEmpty`: empty-space vanishing
* `sheaf_isZero_of_zero_stalks`: zero stalks imply zero sheaf
* `sheafH_subsingleton_of_isZero`: bundled zero-sheaf vanishing
* `stalk_zero_of_ses_g_iso`: stalk vanishing from SES with iso on `g`
* `stalk_zero_of_shortExact_kernel`: stalk vanishing from SES kernel
* `stalk_zero_of_g_is_cokernel_of_stalk_epi`: sheaf-level stalk
  vanishing from a cokernel and stalk-epi hypothesis
* `cokernel_stalk_zero_of_stalk_surj`: actual-cokernel specialization of the same stalk
  vanishing under stalk-surjectivity
* `sheafHSuccMap`: successor connecting morphism
* `sheafH_succ_map_exists_preimage_of_subsingleton_middle`: successor-map
  preimage wrapper
* `sheafH0EquivSections`: sheaf-level wrapper for `H^0(F) ≃+ F(⊤)`
* `sheafH0EquivSections_natural`: sheaf-level naturality of the above
* `sheafH1CokernelIsoOfSubsingletonMiddle`: sheaf-level form of the
  `H¹` cokernel identification
* `sheafH1_cokernel_iso_of_subsingleton_middle_natural`: sheaf-level
  naturality for the same `H¹` cokernel identification
* `sheafHSuccIsoOfSubsingletonMiddle`: sheaf-level form of the
  higher-degree connecting isomorphism
* `sheafH_succ_iso_of_subsingleton_middle_natural`: sheaf-level
  naturality for the same connecting isomorphism
* `sheafH0_surj_of_epi_app_top`: sheaf-level surjectivity on top sections
  gives H^0 surjectivity
* `sheafH_subsingleton_H1_via_surj`: sheaf-level H^1 vanishing via
  H^0-surjectivity
* `sheafH_subsingleton_H1_via_epi_app_top`: sheaf-level H^1 vanishing via
  surjective top sections
* `sheafH_subsingleton_of_injective`: positive-degree cohomology of an injective sheaf
  is subsingleton
* `sheafH_subsingleton_H1_of_injective_of_epi_app_top`: sheaf-level
  injective-middle-term `H¹` vanishing
* `sheafH_dimension_shift_of_both`: sheaf-level forward dimension shift
  for short exact sequences
* `sheafH_dimension_shift_of_mono`: forward dimension shift for a monomorphism
* `sheafH_dimension_shift_of_injective`: forward dimension shift with injective middle term
* `sheafH_dimension_shift_X₃_of_locallySurjective`: reverse dimension shift for locally
  surjective morphisms
-/

universe w' w v u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift ℤ)
    intro A B f g h
    simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq',
      ULift.forall]
    intro x
    specialize h (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y ↦ y • x) fun y z ↦ by simp only [add_smul])) 1
    aesop

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

instance {C : Type*} [Category C] {D : Type*} [Category D] [Preadditive D] :
    (Functor.const Cᵒᵖ : D ⥤ Cᵒᵖ ⥤ D).Additive where

instance instPreadditivePresheafLeanPool
    {C : Type*} [Category C] [Preadditive C] {X : TopCat.{u}} :
    Preadditive (TopCat.Presheaf C X) := by
  delta TopCat.Presheaf
  exact functorCategoryPreadditive

instance {X : TopCat.{u}} :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive :=
  inferInstanceAs ((Functor.const (Opens X)ᵒᵖ ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive)

noncomputable instance sheafHasExt (X : TopCat.{u}) :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X))

/-! ## Internal Ext helpers -/

section ExtDimShift
variable {C' : Type*} [Category C'] [Abelian C'] [HasExt C']

/-- Dimension shift for Ext via LES: given `0 → X₁ → X₂ → X₃ → 0` short exact,
    `Ext^n(Z, X₃) = 0` and `Ext^{n+1}(Z, X₂) = 0` imply `Ext^{n+1}(Z, X₁) = 0`. -/
private theorem ext_dimension_shift (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₃ : Subsingleton (Ext Z S.X₃ n))
    (h₂ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Subsingleton (Ext Z S.X₁ (n + 1)) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hS a (@Subsingleton.elim _ h₂ _ _) rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hS b (@Subsingleton.elim _ h₂ _ _) rfl
  rw [← hc, ← hd, @Subsingleton.elim _ h₃ c d]

/-- Reverse dimension shift: `Ext^n(Z, X₂) = 0` and `Ext^{n+1}(Z, X₁) = 0` imply
    `Ext^n(Z, X₃) = 0`. Uses exactness at X₃ in the covariant LES. -/
private theorem ext_dimension_shift_X₃ (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂ : Subsingleton (Ext Z S.X₂ n))
    (h₁ : Subsingleton (Ext Z S.X₁ (n + 1))) :
    Subsingleton (Ext Z S.X₃ n) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₃ _ hS a rfl (@Subsingleton.elim _ h₁ _ _)
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₃ _ hS b rfl (@Subsingleton.elim _ h₁ _ _)
  rw [← hc, ← hd, @Subsingleton.elim _ h₂ c d]

/-- If the middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the
    connecting morphism `Ext^n(Z, X₃) → Ext^(n+1)(Z, X₁)` is bijective. -/
private theorem extClass_postcomp_bijective_of_subsingleton_middle
    (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Ext Z S.X₂ n))
    (h₂succ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Function.Bijective (hS.extClass.postcomp Z (rfl : n + 1 = n + 1)) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hzero : (x - y).comp hS.extClass rfl = 0 := by
      change (hS.extClass.postcomp Z (rfl : n + 1 = n + 1)) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ Z hS (x - y) rfl hzero
    have hz0 : z = 0 := Subsingleton.elim _ _
    apply sub_eq_zero.mp
    rw [← hz, hz0, Ext.zero_comp]
  · intro x
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Z hS x
      (@Subsingleton.elim _ h₂succ _ _) rfl
    exact ⟨y, hy⟩

/-- The connecting morphism in the covariant long exact sequence as an additive equivalence,
    assuming the middle cohomology groups in degrees `n` and `n + 1` vanish. -/
private noncomputable def extClass_postcompAddEquiv_of_subsingleton_middle
    (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Ext Z S.X₂ n))
    (h₂succ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Ext Z S.X₃ n ≃+ Ext Z S.X₁ (n + 1) :=
  AddEquiv.ofBijective (hS.extClass.postcomp Z (rfl : n + 1 = n + 1))
    (extClass_postcomp_bijective_of_subsingleton_middle Z hS n h₂n h₂succ)

/-- Naturality of the extension class: given a morphism `φ : S₁ ⟶ S₂` of short exact sequences,
    the connecting homomorphism commutes with the induced maps on Ext groups.
    Proved via the triangulated category axiom TR3 (`complete_distinguished_triangle_morphism₁`),
    fullness/faithfulness of `singleFunctor`, and mono cancellation. -/
private lemma extClass_naturality {S₁ S₂ : ShortComplex C'} (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    (Ext.mk₀ φ.τ₃).comp hS₂.extClass (zero_add 1) =
    hS₁.extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1) := by
  letI := HasDerivedCategory.standard C'
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShortComplex.ShortExact.extClass_hom]
  rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  have comm₂ : hS₁.singleTriangle.mor₂ ≫ (DerivedCategory.singleFunctor C' 0).map φ.τ₃ =
      (DerivedCategory.singleFunctor C' 0).map φ.τ₂ ≫ hS₂.singleTriangle.mor₂ := by
    change (DerivedCategory.singleFunctor C' 0).map S₁.g ≫
      (DerivedCategory.singleFunctor C' 0).map φ.τ₃ =
      (DerivedCategory.singleFunctor C' 0).map φ.τ₂ ≫
      (DerivedCategory.singleFunctor C' 0).map S₂.g
    simp [← Functor.map_comp, φ.comm₂₃]
  obtain ⟨a', ha₁, ha₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    hS₁.singleTriangle hS₂.singleTriangle
    hS₁.singleTriangle_distinguished hS₂.singleTriangle_distinguished
    ((DerivedCategory.singleFunctor C' 0).map φ.τ₂)
    ((DerivedCategory.singleFunctor C' 0).map φ.τ₃) comm₂
  simp only [ShortComplex.ShortExact.singleTriangle_mor₃] at ha₃
  have ha' : a' = (DerivedCategory.singleFunctor C' 0).map φ.τ₁ := by
    obtain ⟨a'', rfl⟩ := (DerivedCategory.singleFunctor C' 0).map_surjective a'
    congr 1
    have h : S₁.f ≫ φ.τ₂ = a'' ≫ S₂.f := by
      have := ha₁
      simp only [ShortComplex.ShortExact.singleTriangle_mor₁] at this
      exact (DerivedCategory.singleFunctor C' 0).map_injective <| by
        rwa [Functor.map_comp, Functor.map_comp]
    haveI : Mono S₂.f := hS₂.mono_f
    exact (cancel_mono S₂.f).mp (by rw [← φ.comm₁₂.symm, h])
  rw [ha'] at ha₃
  exact ha₃.symm

/-- Internal helper: if `Y` is zero in an abelian category, `Ext X Y n` is subsingleton
    for all `X`, `n`.
    Proof: `𝟙 Y = 0` because `Y` is zero, so `x = x ∘ mk₀(𝟙 Y) = x ∘ mk₀(0) = x ∘ 0 = 0`. -/
private theorem ext_subsingleton_of_isZero_tgt {X Y : C'} (hY : IsZero Y) (n : ℕ) :
    Subsingleton (Ext X Y n) :=
  ⟨fun a b ↦ by
    have eq : ∀ x : Ext X Y n, x = 0 := fun x ↦ by
      have h := Ext.comp_mk₀_id x
      rw [show (𝟙 Y : Y ⟶ Y) = 0 from hY.eq_of_src _ _, Ext.mk₀_zero] at h
      exact h.symm.trans (Ext.comp_zero x Y 0 n (add_zero n))
    exact (eq a).trans (eq b).symm⟩

end ExtDimShift

/-! ## Stalks and zero sheaves -/

/-- Naturality of the connecting map on sheaf cohomology for a morphism of short exact
    sequences, with the associativity rewrites needed for nested `comp` expressions. -/
private theorem sheafH_comp_extClass_naturality {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ)
    (y : Sheaf.H S₁.X₃ n) :
    (y.comp hS₁.extClass rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) =
      (y.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hS₂.extClass rfl := by
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero]
  exact congrArg (fun t ↦ y.comp t rfl) (extClass_naturality hS₁ hS₂ φ).symm

/-- Successor connecting morphism attached to a short exact sequence of sheaves. -/
noncomputable def sheafHSuccMap {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H S.X₃ n) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ (n + 1)) :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun y ↦ y.comp hS.extClass rfl)
      (by
        intro a b
        change (a + b).comp hS.extClass rfl = a.comp hS.extClass rfl + b.comp hS.extClass rfl
        change (hS.extClass.postcomp _ (rfl : n + 1 = n + 1)) (a + b) =
          (hS.extClass.postcomp _ (rfl : n + 1 = n + 1)) a +
            (hS.extClass.postcomp _ (rfl : n + 1 = n + 1)) b
        exact (hS.extClass.postcomp _ (rfl : n + 1 = n + 1)).map_add a b)

private theorem sheafH_succ_map_apply {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (n : ℕ)
    (y : Sheaf.H S.X₃ n) :
    ConcreteCategory.hom (sheafHSuccMap hS n) y = y.comp hS.extClass rfl := rfl

/-- If the middle term has subsingleton cohomology in degree `n + 1`, every
`H^(n+1)(S.X₁)` class comes from some `H^n(S.X₃)` class via the successor map. -/
theorem sheafH_succ_map_exists_preimage_of_subsingleton_middle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (n : ℕ)
    (h₂H : Subsingleton (Sheaf.H S.X₂ (n + 1)))
    (x : Sheaf.H S.X₁ (n + 1)) :
    ∃ y : Sheaf.H S.X₃ n, ConcreteCategory.hom (sheafHSuccMap hS n) y = x := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x (@Subsingleton.elim _ h₂H _ _) rfl
  refine ⟨y, ?_⟩
  rwa [sheafH_succ_map_apply]

theorem sheaf_isZero_of_zero_stalks (X : TopCat.{u})
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    (hstalk : ∀ (x : X)
      (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F), a = 0) :
    IsZero ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
  have hZ : IsZero F := Functor.isZero F (fun ⟨U⟩ ↦
    @AddCommGrpCat.isZero_of_subsingleton _
      ⟨fun s t ↦ by
        apply hF.section_ext
        intro x hx
        obtain ⟨W, hxW, iU, iV, hEq⟩ := F.germ_eq x hx hx s t
          ((hstalk x _).trans (hstalk x _).symm)
        rw [Subsingleton.elim iU iV] at hEq
        have hWU : W ≤ U := leOfHom iV
        rw [Subsingleton.elim iV (homOfLE hWU)] at hEq
        exact ⟨W, hWU, hxW, hEq⟩⟩)
  exact IsZero.mk
    (fun G ↦ ⟨{ default := 0, uniq := fun f ↦ InducedCategory.Hom.ext (NatTrans.ext (funext
      fun U ↦ (hZ.obj U).eq_zero_of_src (f.hom.app U))) }⟩)
    (fun G ↦ ⟨{ default := 0, uniq := fun f ↦ InducedCategory.Hom.ext (NatTrans.ext (funext
      fun U ↦ (hZ.obj U).eq_zero_of_tgt (f.hom.app U))) }⟩)

/-- If a bundled sheaf is zero, then its cohomology is subsingleton in every degree. -/
theorem sheafH_subsingleton_of_isZero {X : TopCat.{u}}
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (hzero : IsZero F) (n : ℕ) :
    Subsingleton (Sheaf.H F n) :=
  ext_subsingleton_of_isZero_tgt hzero n

/-- The stalk map of `S.f` at `x` is a monomorphism when `S` is short exact. -/
private theorem stalkFunctor_map_f_mono {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (hS : S.ShortExact) (x : X) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.hom) := by
  haveI : Mono S.f := (Sheaf.Hom.mono_iff_presheaf_mono
    (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) S.f).2
    ((Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) S.f).1 hS.mono_f)
  haveI := TopCat.Presheaf.stalkFunctor_preserves_mono (C := AddCommGrpCat.{u}) (X := X) x
  exact show Mono ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f) from
    Functor.map_mono (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) S.f

/-- In a short exact sequence `X₁ → X₂ → X₃`, if the stalk map of `g` at `x` is an
isomorphism, then the stalk of `X₁` at `x` vanishes. -/
theorem stalk_zero_of_ses_g_iso
    {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (hS : S.ShortExact)
    (x : X)
    (hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.hom))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₁.obj) :
    a = 0 := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hTf_mono : Mono (T.map S.f.hom) := stalkFunctor_map_f_mono S hS x
  have hf0 : T.map S.f.hom = 0 := by
    have : T.map S.f.hom ≫ T.map S.g.hom = 0 := by
      have hzero : S.f.hom ≫ S.g.hom = 0 := congrArg InducedCategory.Hom.hom S.zero
      have hcomp_map : T.map (S.f.hom ≫ S.g.hom) = 0 :=
        (congrArg (fun h ↦ T.map h) hzero).trans
          (Functor.map_zero T S.X₁.obj S.X₃.obj)
      simpa [Functor.map_comp] using hcomp_map
    rw [show T.map S.f.hom = (T.map S.f.hom ≫ T.map S.g.hom) ≫ inv (T.map S.g.hom) by simp,
      this, zero_comp]
  exact (AddCommGrpCat.mono_iff_injective _).mp hTf_mono
    (show ConcreteCategory.hom (T.map S.f.hom) a = ConcreteCategory.hom (T.map S.f.hom) 0 by
      simp [hf0])

/-- In a short exact sequence `X₁ → X₂ → X₃`, if all stalks of `X₂` at `x` vanish, then
    all stalks of `X₁` at `x` vanish (by mono-injectivity of `f`). -/
theorem stalk_zero_of_shortExact_kernel
    {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (hS : S.ShortExact)
    (x : X)
    (hX₂ : ∀ (b : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₂.obj), b = 0)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₁.obj) :
    a = 0 := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hTf_mono : Mono (T.map S.f.hom) := stalkFunctor_map_f_mono S hS x
  exact (AddCommGrpCat.mono_iff_injective _).mp hTf_mono
    ((hX₂ _).trans (map_zero _).symm)

/-- If `g` is a cokernel of `f` and the stalk map of `f` at `x` is epi, then the stalk
of `S.X₃` at `x` vanishes. -/
theorem stalk_zero_of_g_is_cokernel_of_stalk_epi
    {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hg : IsColimit (CokernelCofork.ofπ S.g S.zero))
    (x : X)
    (hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.hom))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₃.obj) :
    a = 0 := by
  let T : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ ↦ Classical.dec _
  haveI : T.IsLeftAdjoint :=
    (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) (X := X) (p₀ := x)).isLeftAdjoint
  haveI : Epi (T.map S.f) :=
    show Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.hom) from hepi
  have hzero_map : T.map S.f ≫ T.map S.g = 0 := by
    rw [← T.map_comp, S.zero, Functor.map_zero]
  have hzero : IsZero (T.obj S.X₃) :=
    CokernelCofork.IsColimit.isZero_of_epi (CokernelCofork.mapIsColimit _ hg T)
  haveI := AddCommGrpCat.subsingleton_of_isZero hzero
  change T.obj S.X₃ at a
  change (a : T.obj S.X₃) = 0
  exact Subsingleton.elim _ _

/-- Actual-cokernel specialization of
`stalk_zero_of_g_is_cokernel_of_stalk_epi`: if the stalk map of `f` at `x`
is surjective, then the stalk of `cokernel f` at `x` vanishes. -/
theorem cokernel_stalk_zero_of_stalk_surj
    {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (x : X)
    (hf : Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom)))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (Limits.cokernel f).obj) :
    a = 0 := by
  let S := ShortComplex.mk f (Limits.cokernel.π f) (Limits.cokernel.condition f)
  have hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) := by
    simpa using (AddCommGrpCat.epi_iff_surjective _).mpr hf
  simpa [S] using stalk_zero_of_g_is_cokernel_of_stalk_epi
    (S := S)
    (by simpa [S] using (cokernelIsCokernel f))
    x hepi a

/-! ## H⁰ ≅ Sections -/

/-- If `F` is a sheaf, then `H F 0` is equivalent to sections on `⊤`. -/
noncomputable def sheafH0EquivSections {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Sheaf.H F 0 ≃+ F.obj.obj (op ⊤) :=
  Ext.addEquiv₀.trans
    (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat
        Limits.isTerminalTop).homAddEquiv _ F).trans
      ((@AddCommGrpCat.homAddEquiv (AddCommGrpCat.of (ULift ℤ)) (F.obj.obj (op ⊤))).trans
        (AddEquiv.mk' (uliftZMultiplesHom (F.obj.obj (op ⊤))) (by
          intro x y
          ext
          simp_all only [uliftZMultiplesHom_apply_apply, smul_add, AddMonoidHom.add_apply])).symm))

/-- Naturality of `sheafH0EquivSections`: composing `x` with `mk₀ f` at
    degree 0 corresponds to applying `f.app(⊤)` on sections. -/
lemma sheafH0EquivSections_natural {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (x : Sheaf.H F 0) :
    sheafH0EquivSections G (x.comp (Ext.mk₀ f) (add_zero 0)) =
    ConcreteCategory.hom (f.hom.app (op ⊤)) (sheafH0EquivSections F x) := by
  conv_lhs => rw [show x = Ext.mk₀ (Ext.addEquiv₀ x) from
    (Ext.mk₀_addEquiv₀_apply x).symm, Ext.mk₀_comp_mk₀]
  unfold sheafH0EquivSections
  erw [AddEquiv.trans_apply, AddEquiv.trans_apply,
    AddEquiv.trans_apply, AddEquiv.trans_apply]
  have key :
      Ext.addEquiv₀ (Ext.mk₀ (Ext.addEquiv₀ x ≫ f)) = Ext.addEquiv₀ x ≫ f :=
    by
      change Ext.addEquiv₀ (Ext.addEquiv₀.symm (Ext.addEquiv₀ x ≫ f)) = Ext.addEquiv₀ x ≫ f
      simpa using Ext.addEquiv₀.apply_symm_apply (Ext.addEquiv₀ x ≫ f)
  erw [Adjunction.homAddEquiv_apply, Adjunction.homAddEquiv_apply, key,
    Adjunction.homEquiv_naturality_right, Adjunction.homAddEquiv_apply]
  rfl

/-- `H¹(S.X₁)` as the cokernel of top sections for a short exact sequence of sheaves,
    assuming `H¹(S.X₂)` is subsingleton. -/
noncomputable def sheafH1CokernelIsoOfSubsingletonMiddle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (h₂H : Subsingleton (Sheaf.H S.X₂ 1)) :
  cokernel (S.g.hom.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H S.X₁ 1) := by
  let δ : S.X₃.obj.obj (op ⊤) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ 1) :=
    AddCommGrpCat.ofHom ((sheafH0EquivSections S.X₃).symm.toAddMonoidHom) ≫
      sheafHSuccMap hS 0
  have hδ : S.g.hom.app (op ⊤) ≫ δ = 0 := by
    ext s
    let y : Sheaf.H S.X₂ 0 := (sheafH0EquivSections S.X₂).symm s
    change ConcreteCategory.hom (sheafHSuccMap hS 0)
      ((sheafH0EquivSections S.X₃).symm
        (ConcreteCategory.hom (S.g.hom.app (op ⊤)) s)) = 0
    rw [← show y.comp (Ext.mk₀ S.g) (add_zero 0) =
        (sheafH0EquivSections S.X₃).symm
          (ConcreteCategory.hom (S.g.hom.app (op ⊤)) s) from
          (sheafH0EquivSections S.X₃).injective (by
            simpa [y] using sheafH0EquivSections_natural (f := S.g) (x := y)),
      sheafH_succ_map_apply]
    rw [show (Ext.comp y (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl =
        Ext.comp y ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1)) rfl from
      Ext.comp_assoc_of_second_deg_zero y (Ext.mk₀ S.g) hS.extClass rfl]
    rw [hS.comp_extClass]
    exact Ext.comp_zero y S.X₁ 1 1 (zero_add 1)
  let πH : cokernel (S.g.hom.app (op ⊤)) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ 1) :=
    cokernel.desc _ δ hδ
  have hπH_epi : Epi πH := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro x
    obtain ⟨y, hy⟩ := sheafH_succ_map_exists_preimage_of_subsingleton_middle hS 0 h₂H x
    refine ⟨ConcreteCategory.hom (cokernel.π (S.g.hom.app (op ⊤)))
      (sheafH0EquivSections S.X₃ y), ?_⟩
    simpa [πH, δ] using hy
  have hπH_mono : Mono πH := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    apply sub_eq_zero.mp
    obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective
      (cokernel.π (S.g.hom.app (op ⊤)))).mp inferInstance (a - b)
    rw [← hs]
    have hzero :
        ((((sheafH0EquivSections S.X₃).symm s).comp hS.extClass rfl) :
            Sheaf.H S.X₁ 1) = 0 := by
      have hmap :
          ConcreteCategory.hom (sheafHSuccMap hS 0) ((sheafH0EquivSections S.X₃).symm s) =
            0 := by
        simpa [πH, δ, ← hs] using (by
          rw [map_sub, hab, sub_self] : ConcreteCategory.hom πH (a - b) = 0)
      exact (sheafH_succ_map_apply hS 0 ((sheafH0EquivSections S.X₃).symm s)).symm.trans hmap
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ hS
      ((sheafH0EquivSections S.X₃).symm s) rfl hzero
    have hy_sec :=
      (sheafH0EquivSections_natural (f := S.g) (x := y)).symm.trans <|
        congrArg (sheafH0EquivSections S.X₃) hy
    simpa using
      congrArg (ConcreteCategory.hom (cokernel.π (S.g.hom.app (op ⊤)))) hy_sec.symm
  haveI : IsIso πH := isIso_of_mono_of_epi πH
  exact asIso πH

@[simp] theorem sheafH1_cokernel_iso_of_subsingleton_middle_hom_π {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (h₂H : Subsingleton (Sheaf.H S.X₂ 1))
    (s : S.X₃.obj.obj (op ⊤)) :
    ConcreteCategory.hom
        ((sheafH1CokernelIsoOfSubsingletonMiddle hS h₂H).hom)
        (ConcreteCategory.hom (cokernel.π (S.g.hom.app (op ⊤))) s) =
      ((sheafH0EquivSections S.X₃).symm s).comp hS.extClass rfl := by
  simpa [sheafH1CokernelIsoOfSubsingletonMiddle] using
    sheafH_succ_map_apply hS 0 ((sheafH0EquivSections S.X₃).symm s)

/-- If a sheaf morphism is surjective on top sections, then every degree-zero cohomology
    class of the target lifts along it. -/
theorem sheafH0_surj_of_epi_app_top {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : Epi (f.hom.app (op ⊤))) :
    ∀ y : Sheaf.H G 0, ∃ z : Sheaf.H F 0, z.comp (Ext.mk₀ f) (add_zero 0) = y := by
  intro y
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hf
    (sheafH0EquivSections G y)
  refine ⟨(sheafH0EquivSections F).symm s, ?_⟩
  apply (sheafH0EquivSections G).injective
  rw [sheafH0EquivSections_natural (f := f), AddEquiv.apply_symm_apply, hs]

/-- Internal helper for `H^1` vanishing via degree-zero surjectivity. -/
private theorem subsingleton_H1_via_surj {C' : Type*} [Category C'] [Abelian C'] [HasExt C']
    (Z : C') {S : ShortComplex C'} (hSE : S.ShortExact)
    (hJ : Subsingleton (Ext Z S.X₂ 1))
    (h_surj : ∀ y : Ext Z S.X₃ 0,
      ∃ z : Ext Z S.X₂ 0, z.comp (Ext.mk₀ S.g) (add_zero 0) = y) :
    Subsingleton (Ext Z S.X₁ 1) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hSE a (@Subsingleton.elim _ hJ _ _) rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hSE b (@Subsingleton.elim _ hJ _ _) rfl
  obtain ⟨c', hc'⟩ := h_surj c; obtain ⟨d', hd'⟩ := h_surj d
  simp only [← hc, ← hd, ← hc', ← hd', Ext.comp_assoc_of_second_deg_zero _ (Ext.mk₀ S.g)
    hSE.extClass rfl, hSE.comp_extClass, Ext.comp_zero _ _ 1 1 rfl]

/-- `H¹` vanishing via degree-zero surjectivity. -/
theorem sheafH_subsingleton_H1_via_surj {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (h₂H : Subsingleton (Sheaf.H S.X₂ 1))
    (h_surj : ∀ y : Sheaf.H S.X₃ 0,
      ∃ z : Sheaf.H S.X₂ 0, z.comp (Ext.mk₀ S.g) (add_zero 0) = y) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  subsingleton_H1_via_surj _ hS h₂H h_surj

/-- `H¹` vanishing criterion from surjective top sections. -/
theorem sheafH_subsingleton_H1_via_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (h₂H : Subsingleton (Sheaf.H S.X₂ 1))
    (hg : Epi (S.g.hom.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  sheafH_subsingleton_H1_via_surj hS h₂H (sheafH0_surj_of_epi_app_top S.g hg)

/-- Positive-degree cohomology of an injective sheaf is subsingleton. -/
theorem sheafH_subsingleton_of_injective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (I : Sheaf J AddCommGrpCat.{w}) [Injective I] (n : ℕ) :
    Subsingleton (Sheaf.H I (n + 1)) := by
  simpa [Sheaf.H] using
    (Ext.subsingleton_of_injective
      ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))) I n)

/-- `H¹` vanishing criterion with injective middle term. -/
theorem sheafH_subsingleton_H1_of_injective_of_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    [hI : Injective S.X₂]
    (hg : Epi (S.g.hom.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  sheafH_subsingleton_H1_via_epi_app_top hS
    (@sheafH_subsingleton_of_injective (Opens X) _ (Opens.grothendieckTopology X)
      _ _ S.X₂ hI 0) hg

/-- Forward dimension shift for a short exact sequence of sheaves. -/
theorem sheafH_dimension_shift_of_both {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (n : ℕ)
    (h₃H : Subsingleton (Sheaf.H S.X₃ n))
    (h₂H : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n h₃H h₂H

/-- Forward dimension shift for a monomorphism of sheaves:
    if `f : F ⟶ G` is mono, the cokernel sheaf has subsingleton `H^n`, and
    `G` has subsingleton `H^(n+1)`, then `F` has subsingleton `H^(n+1)`. -/
theorem sheafH_dimension_shift_of_mono {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) [Mono f] (n : ℕ)
    (h₃ : Subsingleton (Sheaf.H (cokernel f) n))
    (h₂ : Subsingleton (Sheaf.H G (n + 1))) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
    inferInstance inferInstance
  change Subsingleton (Sheaf.H S.X₁ (n + 1))
  exact sheafH_dimension_shift_of_both hS n h₃ h₂

/-- Forward dimension shifting with injective middle term:
    if `0 → S.X₁ → S.X₂ → S.X₃ → 0` is short exact, `S.X₂` is injective,
    and `H^n(S.X₃)=0`, then `H^(n+1)(S.X₁)=0`. -/
theorem sheafH_dimension_shift_of_injective {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    [Injective S.X₂]
    (n : ℕ)
    (h₃H : Subsingleton (Sheaf.H S.X₃ n)) :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n h₃H (Ext.subsingleton_of_injective _ _ n)

/-- Reverse dimension shift for a locally surjective morphism:
    if `f : F ⟶ G` is locally surjective, `H^n(F)` is subsingleton, and
    `H^(n+1)(kernel f)` is subsingleton, then `H^n(G)` is subsingleton. -/
theorem sheafH_dimension_shift_X₃_of_locallySurjective {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (hf : TopCat.Presheaf.IsLocallySurjective f.hom) (n : ℕ)
    (h₂ : Subsingleton (Sheaf.H F n))
    (h₁ : Subsingleton (Sheaf.H (kernel f) (n + 1))) :
    Subsingleton (Sheaf.H G n) := by
  letI : Balanced (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) := balanced_of_strongEpiCategory
  haveI : Epi f := by
    rw [← TopCat.Sheaf.isLocallySurjective_iff_epi f]
    simpa using hf
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f)) inferInstance inferInstance
  change Subsingleton (Sheaf.H S.X₃ n)
  exact ext_dimension_shift_X₃ _ hS n h₂ h₁

/-- If `X` is empty, then the cohomology of every sheaf on `X` is subsingleton. -/
theorem sheafH_subsingleton_of_isEmpty {X : TopCat.{u}} [IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Subsingleton (Sheaf.H F n) :=
  sheafH_subsingleton_of_isZero
    (sheaf_isZero_of_zero_stalks X F.property (fun x _ ↦ (IsEmpty.false x).elim)) n

/-! ## Sheaf Cohomology Functor -/

/-- The sheaf cohomology functor `H^n : Sheaf(X, Ab) ⥤ Ab`, defined as the covariant
    Ext functor `Ext^n(ℤ_X, −)` where `ℤ_X` is the constant sheaf of integers. -/
noncomputable def sheafCohomologyFunctor (X : TopCat.{u}) (n : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  extFunctorObj ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))) n

@[simp]
theorem sheafCohomologyFunctor_map_apply (X : TopCat.{u}) (n : ℕ)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (x : Sheaf.H F n) :
    ConcreteCategory.hom ((sheafCohomologyFunctor X n).map f) x =
    x.comp (Ext.mk₀ f) (add_zero n) := rfl

-- If both ends of a short exact sequence have vanishing H^n, so does the middle.
/-- Middle-term cohomology vanishing: if `f : F ⟶ G` is mono and the cohomology of `F`
and `cokernel f` are subsingleton in degree `n`, then so is the cohomology of `G`. -/
theorem subsingleton_sheafH_of_shortExact_middle {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) [Mono f] (n : ℕ)
    (h₁ : Subsingleton (Sheaf.H F n))
    (h₃ : Subsingleton (Sheaf.H (cokernel f) n)) :
    Subsingleton (Sheaf.H G n) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
    inferInstance inferInstance
  have h₁' : Subsingleton (Sheaf.H S.X₁ n) := h₁
  have h₃' : Subsingleton (Sheaf.H S.X₃ n) := h₃
  constructor
  intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₂ _ hS a
    (@Subsingleton.elim _ ((add_zero n) ▸ h₃') _ _)
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₂ _ hS b
    (@Subsingleton.elim _ ((add_zero n) ▸ h₃') _ _)
  rw [← hc, ← hd, @Subsingleton.elim _ h₁' c d]

/-- Naturality of `sheafH1CokernelIsoOfSubsingletonMiddle` for a morphism between
    two short exact sequences of sheaves. -/
theorem sheafH1_cokernel_iso_of_subsingleton_middle_natural {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (h₁₂H : Subsingleton (Sheaf.H S₁.X₂ 1))
    (h₂₂H : Subsingleton (Sheaf.H S₂.X₂ 1)) :
    cokernel.map (S₁.g.hom.app (op ⊤)) (S₂.g.hom.app (op ⊤))
        (φ.τ₂.hom.app (op ⊤)) (φ.τ₃.hom.app (op ⊤))
        (by
          change (S₁.g ≫ φ.τ₃).hom.app (op ⊤) =
            (φ.τ₂ ≫ S₂.g).hom.app (op ⊤)
          exact congrArg (fun α : S₁.X₂ ⟶ S₂.X₃ ↦ α.hom.app (op ⊤)) φ.comm₂₃.symm) ≫
      (sheafH1CokernelIsoOfSubsingletonMiddle hS₂ h₂₂H).hom =
    (sheafH1CokernelIsoOfSubsingletonMiddle hS₁ h₁₂H).hom ≫
      (sheafCohomologyFunctor X 1).map φ.τ₁ := by
  apply (cancel_epi (cokernel.π (S₁.g.hom.app (op ⊤)))).mp
  rw [cokernel.π_desc_assoc, Category.assoc]
  ext s
  have hs :
      (((sheafH0EquivSections S₁.X₃).symm s).comp
          (Ext.mk₀ φ.τ₃) (add_zero 0)) =
        (sheafH0EquivSections S₂.X₃).symm
          (ConcreteCategory.hom (φ.τ₃.hom.app (op ⊤)) s) := by
    apply (sheafH0EquivSections S₂.X₃).injective
    simpa using
      (sheafH0EquivSections_natural (f := φ.τ₃)
        (x := (sheafH0EquivSections S₁.X₃).symm s))
  change ConcreteCategory.hom
      (cokernel.π (S₂.g.hom.app (op ⊤)) ≫
        (sheafH1CokernelIsoOfSubsingletonMiddle hS₂ h₂₂H).hom)
      (ConcreteCategory.hom (φ.τ₃.hom.app (op ⊤)) s) =
    ConcreteCategory.hom
      ((sheafH1CokernelIsoOfSubsingletonMiddle hS₁ h₁₂H).hom ≫
        (sheafCohomologyFunctor X 1).map φ.τ₁)
      (ConcreteCategory.hom (cokernel.π (S₁.g.hom.app (op ⊤))) s)
  simp only [ConcreteCategory.comp_apply]
  rw [sheafH1_cokernel_iso_of_subsingleton_middle_hom_π,
    sheafH1_cokernel_iso_of_subsingleton_middle_hom_π]
  change (((sheafH0EquivSections S₂.X₃).symm
        (ConcreteCategory.hom (φ.τ₃.hom.app (op ⊤)) s)).comp hS₂.extClass rfl) =
      ((((sheafH0EquivSections S₁.X₃).symm s).comp hS₁.extClass rfl).comp
        (Ext.mk₀ φ.τ₁) (add_zero 1))
  rw [← hs]
  simpa using
    (sheafH_comp_extClass_naturality hS₁ hS₂ φ 0
      ((sheafH0EquivSections S₁.X₃).symm s)).symm

/-- The degree-`0` sheaf cohomology functor is naturally isomorphic to taking sections on `⊤`. -/
noncomputable def sheafH0NatIsoSections {X : TopCat.{u}} :
    sheafCohomologyFunctor X 0 ≅
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents (fun F ↦ (sheafH0EquivSections F).toAddCommGrpIso)
    fun {F G} f ↦ by
    ext x
    exact show
        (sheafH0EquivSections G)
            (ConcreteCategory.hom ((sheafCohomologyFunctor X 0).map f) x) =
          ConcreteCategory.hom (f.hom.app (op ⊤)) ((sheafH0EquivSections F) x) from
      (sheafH0EquivSections_natural (f := f) (x := x))

/-- Higher-degree connecting additive equivalence for a short exact sequence of sheaves:
if the middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the
connecting morphism induces an additive equivalence `H^n(S.X₃) ≃+ H^(n+1)(S.X₁)`. -/
private noncomputable def sheafH_extClassAddEquiv_of_subsingleton_middle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    Sheaf.H S.X₃ n ≃+ Sheaf.H S.X₁ (n + 1) :=
  extClass_postcompAddEquiv_of_subsingleton_middle _ hS n h₂n h₂succ

@[simp] private theorem sheafH_extClassAddEquiv_of_subsingleton_middle_apply
    {X : TopCat.{u}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1)))
    (y : Sheaf.H S.X₃ n) :
    sheafH_extClassAddEquiv_of_subsingleton_middle hS n h₂n h₂succ y =
      y.comp hS.extClass rfl := rfl

/-- Higher-degree connecting isomorphism for a short exact sequence of sheaves: if the
middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the connecting
morphism induces an isomorphism `H^n(S.X₃) ≅ H^(n+1)(S.X₁)`. -/
noncomputable def sheafHSuccIsoOfSubsingletonMiddle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    AddCommGrpCat.of (Sheaf.H S.X₃ n) ≅ AddCommGrpCat.of (Sheaf.H S.X₁ (n + 1)) :=
  (sheafH_extClassAddEquiv_of_subsingleton_middle hS n h₂n h₂succ).toAddCommGrpIso

private theorem sheafH_succ_iso_of_subsingleton_middle_hom_apply {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1)))
    (y : Sheaf.H S.X₃ n) :
    ConcreteCategory.hom
        ((sheafHSuccIsoOfSubsingletonMiddle hS n h₂n h₂succ).hom) y =
      y.comp hS.extClass rfl :=
  sheafH_extClassAddEquiv_of_subsingleton_middle_apply hS n h₂n h₂succ y

/-- Naturality of `sheafHSuccIsoOfSubsingletonMiddle` for a morphism between two
short exact sequences of sheaves. -/
theorem sheafH_succ_iso_of_subsingleton_middle_natural {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ)
    (h₁₂n : Subsingleton (Sheaf.H S₁.X₂ n))
    (h₁₂succ : Subsingleton (Sheaf.H S₁.X₂ (n + 1)))
    (h₂₂n : Subsingleton (Sheaf.H S₂.X₂ n))
    (h₂₂succ : Subsingleton (Sheaf.H S₂.X₂ (n + 1))) :
    (sheafHSuccIsoOfSubsingletonMiddle hS₁ n h₁₂n h₁₂succ).hom ≫
        (sheafCohomologyFunctor X (n + 1)).map φ.τ₁ =
      (sheafCohomologyFunctor X n).map φ.τ₃ ≫
        (sheafHSuccIsoOfSubsingletonMiddle hS₂ n h₂₂n h₂₂succ).hom := by
  ext y
  rw [AddCommGrpCat.hom_comp]
  change
      (ConcreteCategory.hom ((sheafCohomologyFunctor X (n + 1)).map φ.τ₁)
        (ConcreteCategory.hom ((sheafHSuccIsoOfSubsingletonMiddle
          hS₁ n h₁₂n h₁₂succ).hom) y)) =
      (ConcreteCategory.hom ((sheafHSuccIsoOfSubsingletonMiddle
        hS₂ n h₂₂n h₂₂succ).hom)
        (ConcreteCategory.hom ((sheafCohomologyFunctor X n).map φ.τ₃) y))
  rw [sheafH_succ_iso_of_subsingleton_middle_hom_apply,
    sheafCohomologyFunctor_map_apply, sheafCohomologyFunctor_map_apply,
    sheafH_succ_iso_of_subsingleton_middle_hom_apply]
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero]
  exact congrArg (fun t ↦ y.comp t rfl) (extClass_naturality hS₁ hS₂ φ).symm
