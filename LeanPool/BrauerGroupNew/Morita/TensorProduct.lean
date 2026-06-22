/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.Morita.ChangeOfRings

/-!
# LeanPool.BrauerGroupNew.Morita.TensorProduct

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Morita.TensorProduct`.
-/

universe u v w

open scoped TensorProduct

variable (R : Type u) [CommRing R]

namespace ModuleCat

/-- Bundling a scaled linear map agrees with scaling the bundled morphism. -/
@[simp]
lemma ofHom_smul {R S : Type*} [Ring R] [Semiring S] {M N : ModuleCat R}
    [Module S N] [SMulCommClass R S N] (r : S) (f : M →ₗ[R] N) :
    ofHom (r • f) = r • ofHom f := by
  apply hom_ext
  simp only [hom_ofHom]
  exact ((homLinearEquiv (R := R) (S := S) (M := M) (N := N)).map_smul r (ofHom f)).symm

end ModuleCat

namespace Morita

open CategoryTheory

variable (A B C D : Type v) [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  (e1 : ModuleCat A ⥤ ModuleCat B) [e1.Additive] [e1.Linear R]

variable (M : ModuleCat (A ⊗[R] C))

noncomputable instance instModuleCarrierLeanPool (N : ModuleCat B) : Module R N :=
  .compHom _ (algebraMap R B)

instance (N : ModuleCat B) : IsScalarTower R B N := .of_algebraMap_smul fun _ _ ↦ rfl

/-- Transport endomorphisms across an `R`-linear additive functor between module categories. -/
noncomputable abbrev aux0 (N : ModuleCat A) : Module.End A N →ₐ[R] Module.End B (e1.obj N) where
  toFun f := (e1.map (ModuleCat.ofHom f)).hom
  map_one' := by ext; simp [Module.End.one_eq_id]
  map_mul' f1 f2 := by ext; simp [Module.End.mul_eq_comp]
  map_zero' := by ext; simp [show ModuleCat.ofHom 0 = 0 from rfl]
  map_add' f1 f2 := by simp [show ModuleCat.ofHom (f1 + f2) = ModuleCat.ofHom f1 +
    ModuleCat.ofHom f2 from rfl]
  commutes' r := by
    ext n
    simp [Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id]

/-- Restrict scalars on an endomorphism algebra to a smaller scalar ring. -/
abbrev _root_.Module.End.restrictScalars (R S M R₁ : Type*) [Ring R] [Ring S] [CommRing R₁]
    [AddCommGroup M] [Module R M] [Module R₁ M] [Module S M] [Algebra R₁ R] [IsScalarTower R₁ R M]
    [Algebra R₁ S] [IsScalarTower R₁ S M] [LinearMap.CompatibleSMul M M R S] :
    Module.End S M →ₐ[R₁] (M →ₗ[R] M) :=
  AlgHom.ofLinearMap (LinearMap.restrictScalarsₗ R S M M R₁) (by rfl) (by intros; rfl)

noncomputable section

/-- The right tensor factor acts on an `A ⊗ C`-module after restriction to an `A`-module. -/
abbrev moduleMapAux : C →ₐ[R] Module.End A ((ModuleCat.restrictScalars
    Algebra.TensorProduct.includeLeftRingHom).obj M) where
  toFun c := {
    toFun (m : M) := ((1 : A) ⊗ₜ[R] c) • m
    map_add' := by intros; exact smul_add _ _ _
    map_smul' r (m : M) := by simp [smul_smul]
  }
  map_one' := by ext; simp [← Algebra.TensorProduct.one_def]
  map_mul' c1 c2 := by ext; simp [smul_smul]
  map_zero' := by ext m; simp; rfl
  map_add' c1 c2 := by ext m; simp [TensorProduct.tmul_add, add_smul]; rfl
  commutes' r := by
    ext m; simp [Algebra.algebraMap_eq_smul_one, ← Algebra.TensorProduct.one_def]; rfl

/-- The tensor-product algebra action obtained after applying a Morita equivalence
to the left factor. -/
abbrev moduleMap : B ⊗[R] C →ₐ[R]
    Module.End R (e1.obj ((ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeLeftRingHom)).obj M)) :=
  Algebra.TensorProduct.lift (Algebra.lsmul _ _ _) ((Module.End.restrictScalars R B _ R).comp
    ((aux0 R A B e1 _).comp (moduleMapAux R A C _))) fun b c ↦ by ext; simp

instance modulefromtensor (M : ModuleCat (A ⊗[R] C)) :
  Module (B ⊗[R] C) (e1.obj ((ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeLeftRingHom)).obj M)) :=
  Module.compHom _ (moduleMap R A B C e1 M).toRingHom

end

end Morita

noncomputable section newcat

open CategoryTheory

variable (R : Type u) [CommRing R] (A B C D : Type v) [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

/-- use `Action` instead once it's generalized to enriched categories. -/
structure TensorModule where
  /-- The underlying module over the left tensor factor. -/
  carrier : ModuleCat.{v} A
  /-- The action of the right tensor factor by left-factor-linear endomorphisms. -/
  morphism : C →ₐ[R] Module.End A carrier

instance : CoeSort (TensorModule R A C) (Type v) where
  coe M := M.carrier

/-- Morphisms of tensor modules are maps that commute with the right tensor-factor action. -/
@[ext]
structure TensorModule.Hom (M N : TensorModule R A C) where
  /-- The underlying map of modules over the left tensor factor. -/
  hom : M.carrier ⟶ N.carrier
  /-- Compatibility with the right tensor-factor action. -/
  commutes : ∀ c, hom ≫ ModuleCat.ofHom (N.morphism c) = ModuleCat.ofHom (M.morphism c) ≫ hom

attribute [reassoc (attr := simp)] TensorModule.Hom.commutes

@[simp]
lemma TensorModule.commutes_apply (M N : TensorModule R A C) (f : TensorModule.Hom R A C M N)
    (c : C) (m : M) : f.hom.hom ((M.morphism c) m) = (N.morphism c) (f.hom.hom m) := by
  have := f.commutes c
  rw [ModuleCat.hom_ext_iff, LinearMap.ext_iff] at this
  specialize this m
  simp only [ModuleCat.of_coe, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply] at this
  exact this.symm

instance : Category (TensorModule R A C) where
  Hom := TensorModule.Hom R A C
  id M := {
    hom := 𝟙 _
    commutes _ := rfl
  }
  comp f g := {
    hom := f.hom ≫ g.hom
    commutes _ := by simp
  }
  id_comp f := by simp
  comp_id f := by simp
  assoc _ _ := by simp

@[simp]
lemma TensorModule.hom_id (M : TensorModule R A C) :
  TensorModule.Hom.hom (𝟙 M) = 𝟙 M.carrier := rfl

@[simp]
lemma TensorModule.hom_comp {M N K : TensorModule R A C} (f : M ⟶ N) (g : N ⟶ K) :
  (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[ext]
lemma TensorModule.hom_ext {M N : TensorModule R A C} (f g : M ⟶ N) (h : f.hom = g.hom) :
  f = g := by
  rcases f
  rcases g
  simp_all

/-- Build an isomorphism of tensor modules from an isomorphism of the underlying modules. -/
@[simps]
def TensorModule.IsoMk {M N : TensorModule R A C} (f : M.carrier ≅ N.carrier)
    (h : ∀ c, f.hom ≫ ModuleCat.ofHom (N.morphism c) =
    ModuleCat.ofHom (M.morphism c) ≫ f.hom) :
  M ≅ N := {
  hom := {
    hom := f.hom
    commutes := h
  }
  inv := {
    hom := f.inv
    commutes := by
      intro c
      rw [f.inv_comp_eq, reassoc_of%h]
      simp
  }
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp
}

instance (M N : TensorModule R A C) : Coe (M ⟶ N) (M.carrier ⟶ N.carrier) where
  coe f := f.hom

instance (M N : TensorModule R A C) : AddCommGroup (M ⟶ N) where
  add f g := ⟨f.hom + g.hom, by simp⟩
  add_assoc f g h := by ext1; exact add_assoc _ _ _
  zero := ⟨0, by simp⟩
  zero_add _ := by ext1; exact zero_add _
  add_zero _ := by ext1; exact add_zero _
  nsmul n f := ⟨n • f.hom, by simp⟩
  nsmul_zero _ := by ext1; exact zero_nsmul _
  nsmul_succ _ _ := by ext1; exact AddMonoid.nsmul_succ _ _
  neg f := ⟨-f.hom, by simp⟩
  sub f g := ⟨f.hom - g.hom, by simp⟩
  sub_eq_add_neg f g := by ext1; exact sub_eq_add_neg _ _
  zsmul z f := ⟨z • f.hom, by simp⟩
  zsmul_zero' _ := by ext1; exact zero_zsmul _
  zsmul_succ' _ _ := by ext1; exact SubNegMonoid.zsmul_succ' _ _
  zsmul_neg' _ _ := by ext1; exact SubNegMonoid.zsmul_neg' _ _
  neg_add_cancel _ := by ext1; exact neg_add_cancel _
  add_comm _ _ := by ext1; exact add_comm _ _

instance : Preadditive (TensorModule R A C) where
  add_comp _ _ _ _ _ _ := by ext1; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := by ext1; exact Preadditive.comp_add _ _ _ _ _ _

instance (M N : TensorModule R A C) : Module R (M ⟶ N) where
  smul r g := ⟨r • g.hom, by simp⟩
  smul_add _ _ _ := by ext1; exact smul_add _ _ _
  add_smul _ _ _ := by ext1; exact add_smul _ _ _
  mul_smul _ _ _ := by ext1; exact mul_smul _ _ _
  one_smul _ := by ext1; exact one_smul _ _
  zero_smul _ := by ext1; exact zero_smul _ _
  smul_zero _ := by ext1; exact smul_zero _

instance : Linear R (TensorModule R A C) where
  smul_comp _ _ _ _ _ _ := by ext1; exact Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ _ _ _ := by ext1; exact Linear.comp_smul _ _ _ _ _ _

/-- The `A ⊗ C` action associated to a tensor module. -/
abbrev moduleAux (M : TensorModule R A C) : A ⊗[R] C →ₐ[R] Module.End R M :=
  Algebra.TensorProduct.lift (Algebra.lsmul _ _ _)
    ((Module.End.restrictScalars R A M R).comp M.morphism) fun a c ↦ by ext; simp

lemma moduleAux_apply (M : TensorModule R A C) (a : A) (c : C) (m : M) :
    moduleAux R A C M (a ⊗ₜ[R] c) m = a • (M.morphism c) m := by
  simp [moduleAux]

instance moduletotensor (M : TensorModule R A C) : Module (A ⊗[R] C) M :=
  Module.compHom _ (moduleAux R A C M).toRingHom

@[simp]
lemma smul_tensormod (x : A ⊗[R] C) (M : TensorModule R A C) (m : M) :
    x • m = moduleAux R A C M x m := rfl

/-- View a tensor module as a module over the tensor-product algebra. -/
abbrev toModuleOverTensor : TensorModule R A C ⥤ ModuleCat (A ⊗[R] C) where
  obj M := ModuleCat.of _ M
  map {M N} f := ModuleCat.ofHom {
    __ := f.hom.hom
    map_smul' ac m := by
      induction ac using TensorProduct.induction_on with
      | zero => simp
      | tmul a c => simp
      | add _ _ _ _ => simp_all [add_smul]
  }
  map_id M := by ext; simp
  map_comp _ _ := by ext; simp

/-- Split an `A ⊗ C`-module into an `A`-module with a compatible `C`-action. -/
abbrev fromModuleOverTensor : ModuleCat (A ⊗[R] C) ⥤ TensorModule R A C where
  obj M := {
    carrier := (ModuleCat.restrictScalars (Algebra.TensorProduct.includeLeftRingHom)).obj M
    morphism := by exact Morita.moduleMapAux R A C M
  }
  map f := {
    hom := (ModuleCat.restrictScalars (Algebra.TensorProduct.includeLeftRingHom)).map f
    commutes c := by ext; simp
  }
  map_id M := by ext; simp
  map_comp _ _ := by ext; simp

/-- The unit component comparing tensor modules with modules over the tensor-product algebra. -/
abbrev e01 (M : TensorModule R A C) :
    (𝟭 (TensorModule R A C)).obj M ≅ (toModuleOverTensor R A C ⋙
    fromModuleOverTensor R A C).obj M := TensorModule.IsoMk R A C
  (LinearEquiv.toModuleIso (by
    apply (config := {allowSynthFailures := true, newGoals := .all}) @LinearEquiv.mk
    · apply (config := {allowSynthFailures := true, newGoals := .all}) @LinearMap.mk
      · exact AddHom.id _
      · intro a m
        change a • m = (moduleAux R A C M (a ⊗ₜ[R] (1 : C))) m
        simp
        rfl
    · exact id
    · exact congrFun rfl
    · exact congrFun rfl)) fun c ↦ by
      ext m
      change moduleAux R A C M ((1 : A) ⊗ₜ[R] c) m = (M.morphism c) m
      rw [moduleAux_apply]
      simp

/-- Naturality of the tensor-module unit comparison. -/
lemma e01_naturality {X Y : TensorModule R A C} (f : X ⟶ Y) :
    (𝟭 (TensorModule R A C)).map f ≫ (e01 R A C Y).hom =
    (e01 R A C X).hom ≫ (toModuleOverTensor R A C ⋙ fromModuleOverTensor R A C).map f := by
  ext (x : X)
  simp
  rfl

/-- The unit isomorphism for the equivalence between tensor modules and modules over `A ⊗ C`. -/
abbrev eModunitIso : 𝟭 (TensorModule R A C) ≅ toModuleOverTensor R A C ⋙
    fromModuleOverTensor R A C :=
  NatIso.ofComponents (e01 R A C) <| e01_naturality R A C

/-- The counit component comparing modules over the tensor-product algebra with tensor modules. -/
abbrev e02 (M : ModuleCat (A ⊗[R] C)) :
    (fromModuleOverTensor R A C ⋙ toModuleOverTensor R A C).obj M ≅
      (𝟭 (ModuleCat (A ⊗[R] C))).obj M := LinearEquiv.toModuleIso <| by
  apply (config := {allowSynthFailures := true, newGoals := .all}) @LinearEquiv.mk
  · apply (config := {allowSynthFailures := true, newGoals := .all}) @LinearMap.mk
    · exact AddHom.id _
    · intro ac m
      induction ac using TensorProduct.induction_on with
      | zero =>
      conv_lhs => erw [AddHom.toFun_eq_coe, AddHom.id_apply]
      rw [RingHom.id_apply, zero_smul]
      rfl
      | tmul a c =>
      conv_lhs => erw [AddHom.toFun_eq_coe, AddHom.id_apply]
      rw [RingHom.id_apply, AddHom.toFun_eq_coe]
      conv_rhs => erw [AddHom.id_apply]
      rw [smul_tensormod]
      simp [smul_smul]
      | add x y h1 h2 =>
      rw [RingHom.id_apply, AddHom.toFun_eq_coe]
      erw [AddHom.id_apply, AddHom.id_apply]
      conv_rhs => rw [add_smul]
      erw [AddHom.toFun_eq_coe, AddHom.id_apply] at h1 h2
      simp only [RingHom.id_apply] at h1 h2
      erw [AddHom.id_apply] at h1 h2
      rw [← h1, ← h2]
      rw [smul_tensormod, map_add]
      rfl
  · exact id
  · exact congrFun rfl
  · exact congrFun rfl

/-- The counit isomorphism for the equivalence between tensor modules and modules over `A ⊗ C`. -/
abbrev eModcounitIso :
    fromModuleOverTensor R A C ⋙ toModuleOverTensor R A C ≅ 𝟭 (ModuleCat (A ⊗[R] C)) :=
  NatIso.ofComponents (e02 R A C) fun {X Y} f ↦ by ext (x : X); simp; rfl

/-- Tensor modules are equivalent to modules over the tensor-product algebra. -/
abbrev equivModuleOverTensor : TensorModule R A C ≌ ModuleCat (A ⊗[R] C) where
  functor := toModuleOverTensor R A C
  inverse := fromModuleOverTensor R A C
  unitIso := eModunitIso R A C
  counitIso := eModcounitIso R A C
  functor_unitIso_comp M := by
    ext
    simp
    rfl

instance : (equivModuleOverTensor R A C).functor.Additive where
  map_add := by intros; ext; rfl

instance : (equivModuleOverTensor R A C).functor.Linear R where
  map_smul {M N} f r := by
    ext m
    simp only [ConcreteCategory.hom_ofHom, LinearMap.coe_mk, LinearMap.coe_toAddHom,
      ModuleCat.hom_smul, LinearMap.smul_apply]
    change (r • f.hom.hom) m = _
    rw [LinearMap.smul_apply]
    congr 1
    simp

instance : (equivModuleOverTensor R A C).inverse.Linear R where
  map_smul {M N} f r := by
    ext1
    rfl

/-- Apply an `R`-linear additive functor to the left factor of a tensor module. -/
abbrev toBCfunctor (F : ModuleCat A ⥤ ModuleCat B) [F.Additive] [F.Linear R] :
    TensorModule R A C ⥤ TensorModule R B C where
  obj M := {
    carrier := F.obj M.1
    morphism := (Morita.aux0 R A B F M.1).comp M.morphism
  }
  map {M N} f := {
    hom := F.map f.hom
    commutes c := by
      simp only
      rw [AlgHom.comp_apply, AlgHom.comp_apply]
      simp_rw [ModuleCat.of_coe, AlgHom.coe_mk, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk, ModuleCat.ofHom_hom]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact f.commutes c
  }
  map_id M := by ext : 1; exact F.map_id M.1
  map_comp f g := by ext1; exact F.map_comp f.hom g.hom

/-- Tensor a Morita equivalence on the left with the identity on the right tensor factor. -/
abbrev MoritaTensorAux0 (e : ModuleCat A ≌ ModuleCat B) [e.functor.Additive]
    [e.functor.Linear R] : TensorModule R A C ≌ TensorModule R B C where
  functor := toBCfunctor R A B C e.functor
  inverse := toBCfunctor R B A C e.inverse
  unitIso := NatIso.ofComponents
    (fun M ↦ TensorModule.IsoMk _ _ _
      (e.unitIso.app M.1) fun c ↦ by
        change (e.unitIso.app M.carrier).hom ≫
            e.inverse.map (e.functor.map (ModuleCat.ofHom (M.morphism c))) =
          ModuleCat.ofHom (M.morphism c) ≫ (e.unitIso.app M.carrier).hom
        exact (e.unitIso.hom.naturality (ModuleCat.ofHom (M.morphism c))).symm)
    (fun {M N} f ↦ by
      ext x
      change (ModuleCat.Hom.hom (f.hom ≫ e.unitIso.hom.app N.carrier)) x =
        (ModuleCat.Hom.hom
          (e.unitIso.hom.app M.carrier ≫ e.inverse.map (e.functor.map f.hom))) x
      exact LinearMap.ext_iff.mp (ModuleCat.hom_ext_iff.mp
        (e.unitIso.hom.naturality f.hom)) x)
  counitIso := NatIso.ofComponents
    (fun M ↦ TensorModule.IsoMk _ _ _
      (e.counitIso.app M.1) fun c ↦ by
        change (e.counitIso.app M.carrier).hom ≫ ModuleCat.ofHom (M.morphism c) =
          e.functor.map (e.inverse.map (ModuleCat.ofHom (M.morphism c))) ≫
            (e.counitIso.app M.carrier).hom
        exact (e.counitIso.hom.naturality (ModuleCat.ofHom (M.morphism c))).symm)
    (fun {M N} f ↦ by
      ext x
      change (ModuleCat.Hom.hom
          (e.functor.map (e.inverse.map f.hom) ≫ e.counitIso.hom.app N.carrier)) x =
        (ModuleCat.Hom.hom (e.counitIso.hom.app M.carrier ≫ f.hom)) x
      exact LinearMap.ext_iff.mp (ModuleCat.hom_ext_iff.mp
        (e.counitIso.hom.naturality f.hom)) x)
  functor_unitIso_comp M := by ext; simp

instance (e : ModuleCat A ≌ ModuleCat B) [e.functor.Additive] [e.functor.Linear R] :
    (MoritaTensorAux0 R A B C e).functor.Additive where
  map_add := by intros; ext1; exact e.functor.map_add

instance (e : ModuleCat A ≌ ModuleCat B) [e.functor.Additive] [e.functor.Linear R] :
    (MoritaTensorAux0 R A B C e).functor.Linear R where
  map_smul {M N} f r := by
    ext1
    exact e.functor.map_smul _ _

/-- The induced equivalence of module categories over tensor-product algebras. -/
abbrev MoritaTensorAux1 (e : ModuleCat A ≌ ModuleCat B) [e.functor.Additive] [e.functor.Linear R] :
    ModuleCat (A ⊗[R] C) ≌ ModuleCat (B ⊗[R] C) :=
  (equivModuleOverTensor R A C).symm.trans ((MoritaTensorAux0 R A B C e).trans
      (equivModuleOverTensor R B C))

instance : Functor.Linear R (@ModuleCat.restrictScalars A (A ⊗[R] C) _ _
    Algebra.TensorProduct.includeLeftRingHom) where
  map_smul {X Y} f r := by
    ext1; rfl

instance MoritaTensorAux1_linear (e : ModuleCat A ≌ ModuleCat B) [e.functor.Additive]
    [e.functor.Linear R] : (MoritaTensorAux1 R A B C e).functor.Linear R := by
  dsimp [MoritaTensorAux1]
  change Functor.Linear R ((equivModuleOverTensor R A C).inverse ⋙
    ((MoritaTensorAux0 R A B C e).functor ⋙ (equivModuleOverTensor R B C).functor))
  infer_instance

/-- Morita equivalence is preserved by tensoring on the right. -/
theorem MoritaTensorLeft (e : IsMoritaEquivalent R A B) :
    IsMoritaEquivalent R (A ⊗[R] C) (B ⊗[R] C) where
  cond := ⟨⟨MoritaTensorAux1 R A B C e.cond.some.eqv, inferInstance⟩⟩

open ModuleCat in
/-- Tensor products of Morita equivalent algebras are Morita equivalent. -/
theorem MoritaTensor (e1 : IsMoritaEquivalent R A B) (e2 : IsMoritaEquivalent R C D) :
    IsMoritaEquivalent R (A ⊗[R] C) (B ⊗[R] D) :=
  IsMoritaEquivalent.trans R (MoritaTensorLeft R A B C e1) <| IsMoritaEquivalent.trans R
    (IsMoritaEquivalent.of_algEquiv R (Algebra.TensorProduct.comm R B C)) <|
    IsMoritaEquivalent.trans R (MoritaTensorLeft R _ _ _ e2) <| IsMoritaEquivalent.of_algEquiv R
    (Algebra.TensorProduct.comm R D B)

end newcat
