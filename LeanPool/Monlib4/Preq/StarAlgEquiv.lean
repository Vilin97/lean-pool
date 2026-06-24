/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Star.Pi

/-!
 # Some stuff on star algebra equivalences

 This file contains some obvious definitions and lemmas on star algebra equivalences.
-/


theorem AlgEquiv.comp_inj {R A B C : Type _} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : B ≃ₐ[R] C) (S T : A →ₗ[R] B) :
    f.toLinearMap ∘ₗ S = f.toLinearMap ∘ₗ T ↔ S = T := by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    f.injective.eq_iff]

theorem AlgEquiv.inj_comp {R A B C : Type _} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : C ≃ₐ[R] A) (S T : A →ₗ[R] B) :
    S ∘ₗ f.toLinearMap = T ∘ₗ f.toLinearMap ↔ S = T := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply] at h ⊢
  intro x
  specialize h (f.symm x)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h

/-- The linear map underlying a star algebra equivalence. -/
@[simps]
def StarAlgEquiv.toLinearMap {R A B : Type*} [Semiring R] [AddCommMonoid A]
  [AddCommMonoid B]
  [Mul A] [Mul B] [Module R A] [Module R B] [Star A] [Star B]
  (f : A ≃⋆ₐ[R] B) : A →ₗ[R] B where
    toFun x := f x
    map_add' _ _ := by simp only [map_add]
    map_smul' _ _ := by simp only [map_smul, RingHom.id_apply]

theorem StarAlgEquiv.injective {R A B : Type _} [Add A] [Add B] [Mul A] [Mul B]
  [SMul R A] [SMul R B] [Star A] [Star B]
  (f : A ≃⋆ₐ[R] B) : Function.Injective f :=
EquivLike.injective f

theorem StarAlgEquiv.comp_inj {R A B C : Type*} [Semiring R] [AddCommMonoid A]
  [AddCommMonoid B]
  [AddCommMonoid C] [Mul B] [Mul C] [Module R A] [Module R B] [Module R C]
  [Star B] [Star C]
  (f : B ≃⋆ₐ[R] C) (S T : A →ₗ[R] B) :
    f.toLinearMap ∘ₗ S = f.toLinearMap ∘ₗ T ↔ S = T := by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply,
    f.injective.eq_iff]

theorem StarAlgEquiv.inj_comp {R A B C : Type*} [Semiring R] [AddCommMonoid A]
  [AddCommMonoid B]
  [AddCommMonoid C] [Mul A] [Mul C] [Module R A] [Module R B] [Module R C]
  [Star A] [Star C] (f : C ≃⋆ₐ[R] A) (S T : A →ₗ[R] B) :
    S ∘ₗ f.toLinearMap = T ∘ₗ f.toLinearMap ↔ S = T := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply] at h ⊢
  intro x
  specialize h (f.symm x)
  rw [StarAlgEquiv.apply_symm_apply] at h
  exact h

/-- The linear equivalence underlying a star algebra equivalence. -/
@[simps]
def StarAlgEquiv.toLinearEquiv {R A B : Type*} [Semiring R] [AddCommMonoid A]
  [AddCommMonoid B]
  [Mul A] [Mul B] [Module R A] [Module R B] [Star A] [Star B]
  (f : A ≃⋆ₐ[R] B) : A ≃ₗ[R] B where
    toFun x := f x
    invFun x := f.symm x
    left_inv x := by simp only [symm_apply_apply]
    right_inv x := by simp only [apply_symm_apply]
    map_add' _ _ := by simp only [map_add]
    map_smul' _ _ := by simp only [map_smul, RingHom.id_apply]

theorem StarAlgEquiv.symm_apply_eq {R A B : Type _}
  [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A] [Star B]
  (f : A ≃⋆ₐ[R] B) (x : A) (y : B) :
    f.symm y = x ↔ y = f x :=
  EquivLike.inv_apply_eq (e := f)

@[simp]
theorem StarAlgEquiv.ofAlgEquiv_coe {R A B : Type _}
    [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Star A] [Star B]
    (f : A ≃ₐ[R] B) (hf : ∀ x : A, f (star x) = star (f x)) :
    ⇑(StarAlgEquiv.ofAlgEquiv f hf) = f :=
  rfl

@[simp]
theorem StarAlgEquiv.ofAlgEquiv_symm_coe {R A B : Type _}
    [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Star A] [Star B]
    (f : A ≃ₐ[R] B) (hf : ∀ x : A, f (star x) = star (f x)) :
    ⇑(StarAlgEquiv.ofAlgEquiv f hf).symm = f.symm :=
  rfl

theorem StarAlgEquiv.comp_eq_iff {R E₁ E₂ E₃ : Type _} [CommSemiring R]
    [AddCommMonoid E₁] [AddCommMonoid E₂] [AddCommMonoid E₃]
    [Module R E₁] [Module R E₂] [Module R E₃] [Star E₁] [Star E₂] [Mul E₁] [Mul E₂]
    (f : E₁ ≃⋆ₐ[R] E₂) (x : E₂ →ₗ[R] E₃) (y : E₁ →ₗ[R] E₃) :
    x ∘ₗ f.toLinearMap = y ↔ x = y ∘ₗ f.symm.toLinearMap := by
  constructor
  · intro h
    ext1
    rw [← h]
    simp only [LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply,
      StarAlgEquiv.apply_symm_apply]
  · rintro rfl
    ext1
    simp only [LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply, StarAlgEquiv.symm_apply_apply]

theorem AlgEquiv.map_eq_zero_iff {R E₁ E₂ : Type _} [CommSemiring R] [Semiring E₁] [Semiring E₂]
    [Algebra R E₁] [Algebra R E₂] (f : E₁ ≃ₐ[R] E₂) (x : E₁) : f x = 0 ↔ x = 0 :=
  RingEquiv.map_eq_zero_iff f.toRingEquiv

theorem StarAlgEquiv.map_eq_zero_iff {R A B : Type _}
  [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
  [SMul R A] [SMul R B] [Star A] [Star B]
  (f : A ≃⋆ₐ[R] B) (x : A) :
    f x = 0 ↔ x = 0 :=
  RingEquiv.map_eq_zero_iff f.toRingEquiv

theorem IsIdempotentElem.mulEquiv {H₁ H₂ : Type _} [Mul H₁] [Mul H₂]
  -- (f : H₁ ≃* H₂)
  {F : Type*} [EquivLike F H₁ H₂] [MulEquivClass F H₁ H₂] {f : F} {x : H₁} :
    IsIdempotentElem (f x) ↔ IsIdempotentElem x := by
  simp_rw [IsIdempotentElem, ← _root_.map_mul]
  exact EmbeddingLike.apply_eq_iff_eq f

theorem IsIdempotentElem.algEquiv {R H₁ H₂ : Type _} [CommSemiring R] [Semiring H₁] [Semiring H₂]
    [Algebra R H₁] [Algebra R H₂] (f : H₁ ≃ₐ[R] H₂) {x : H₁} :
    IsIdempotentElem (f x) ↔ IsIdempotentElem x :=
IsIdempotentElem.mulEquiv

theorem IsIdempotentElem.starAlgEquiv {R A B : Type _}
   [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A] [Star B]
   (f : A ≃⋆ₐ[R] B) {x : A} :
    IsIdempotentElem (f x) ↔ IsIdempotentElem x :=
IsIdempotentElem.mulEquiv

lemma _root_.isIdempotentElem_pi_iff
  {ι : Type*} {A : ι → Type*} [Π i, Mul (A i)] {a : Π i, A i} :
  IsIdempotentElem a ↔ ∀ i, IsIdempotentElem (a i) := by
  simp only [IsIdempotentElem, Pi.mul_def, funext_iff]

theorem AlgEquiv.eq_apply_iff_symm_eq {R A B : Type _} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A ≃ₐ[R] B) {a : B} {b : A} : a = f b ↔ f.symm a = b := by
  have : ∀ e : A ≃ B, a = e b ↔ e.symm a = b := by
    intro e
    rw [← Equiv.apply_eq_iff_eq e, Equiv.apply_symm_apply]
  exact this f

theorem StarAlgEquiv.eq_apply_iff_symm_eq {R A B : Type _}
  [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A] [Star B]
  (f : A ≃⋆ₐ[R] B) {a : B} {b : A} :
    a = f b ↔ f.symm a = b := by
  rw [eq_comm]
  nth_rw 2 [eq_comm]
  exact Equiv.apply_eq_iff_eq_symm_apply f.toRingEquiv.toEquiv

lemma AlgEquiv.apply_eq_iff_eq {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Semiring B] [Algebra R B]
  (f : A ≃ₐ[R] B) {x y : A} :
  f x = f y ↔ x = y :=
Equiv.apply_eq_iff_eq f.toEquiv

lemma MulEquiv.image_center {F A B : Type*} [Semigroup A] [Semigroup B]
  [EquivLike F A B] [MulEquivClass F A B]
  (f : F) :
  f '' (Set.center A) = Set.center B := by
  let f' : A ≃* B := f
  ext x
  symm
  calc x ∈ Set.center B ↔ ∀ y, y * x = x * y := Semigroup.mem_center_iff
    _ ↔ ∀ y, f'.symm y * f'.symm x = f'.symm x * f'.symm y := by
      simp only [MulEquiv.apply_eq_iff_eq, ← map_mul]
    _ ↔ ∀ y, y * f'.symm x = f'.symm x * y := by
      refine ⟨fun h y => ?_, fun h y => h _⟩
      specialize h (f' y)
      simp_all only [MulEquiv.symm_apply_apply]
    _ ↔ f'.symm x ∈ Set.center A := Semigroup.mem_center_iff.symm
    _ ↔ x ∈ f '' Set.center A := Set.mem_image_equiv.symm

instance
  {F R A B : Type*} [Monoid R] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
  [DistribMulAction R A] [DistribMulAction R B]
  [EquivLike F A B] [NonUnitalAlgHomClass F R A B] :
  MulEquivClass F A B where
  map_mul := MulHomClass.map_mul

lemma NonUnitalAlgEquiv.image_span_center {F R A B : Type*} [Semiring R]
  [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R A] [Module R B]
  [EquivLike F A B] [NonUnitalAlgHomClass F R A B] (f : F) :
  f '' (Submodule.span R (Set.center A)) = Submodule.span R (Set.center B) := by
  change (LinearMapClass.linearMap f : A → B) ''
      (Submodule.span R (Set.center A) : Set A) =
    (Submodule.span R (Set.center B) : Set B)
  rw [← Submodule.map_coe (LinearMapClass.linearMap f) (Submodule.span R (Set.center A)),
    Submodule.map_span]
  rw [show (LinearMapClass.linearMap f : A → B) '' Set.center A = Set.center B by
    change f '' Set.center A = Set.center B
    exact MulEquiv.image_center f]

lemma NonUnitalAlgEquiv.map_span_center {F R A B : Type*} [Semiring R]
  [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R A] [Module R B]
  [EquivLike F A B] [NonUnitalAlgHomClass F R A B] (f : F) :
  Submodule.map (LinearMapClass.linearMap f) (Submodule.span R (Set.center A)) =
    Submodule.span R (Set.center B) := by
  rw [Submodule.map_span]
  rw [show (LinearMapClass.linearMap f : A → B) '' Set.center A = Set.center B by
    change f '' Set.center A = Set.center B
    exact MulEquiv.image_center f]

/-- Assemble pointwise star algebra equivalences into a star algebra equivalence of dependent
functions. -/
@[simps apply]
def StarAlgEquiv.piCongrRight {R ι : Type*} {A₁ A₂ : ι → Type*}
  [(i : ι) → Add (A₁ i)] [(i : ι) → Add (A₂ i)]
  [(i : ι) → Mul (A₁ i)] [(i : ι) → Mul (A₂ i)]
  [(i : ι) → Star (A₁ i)] [(i : ι) → Star (A₂ i)]
  [(i : ι) → SMul R (A₁ i)] [(i : ι) → SMul R (A₂ i)]
  (e : (i : ι) → A₁ i ≃⋆ₐ[R] A₂ i) :
  ((i : ι) → A₁ i) ≃⋆ₐ[R] (i : ι) → A₂ i where
    toFun x j := e j (x j)
    invFun x j := (e j).symm (x j)
    map_add' _ _ := by simp only [Pi.add_apply, map_add]; rfl
    map_mul' _ _ := by simp only [Pi.mul_apply, map_mul]; rfl
    map_star' _ := by simp only [Pi.star_apply, map_star]; rfl
    map_smul' _ _ := by simp only [Pi.smul_apply, map_smul]; rfl
    left_inv _ := by simp only [symm_apply_apply]
    right_inv _ := by simp only [apply_symm_apply]

theorem AlgEquiv.coe_comp
  {R A₁ A₂ A₃ : Type*} [CommSemiring R] [Semiring A₁] [Semiring A₂]
  [Semiring A₃] [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]
  (e : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
  e₂.toLinearMap.comp e.toLinearMap = (e.trans e₂).toLinearMap :=
rfl

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem AlgEquiv.refl_toLinearMap :
  (AlgEquiv.refl (R := R) (A₁ := A)).toLinearMap = LinearMap.id :=
rfl
theorem AlgEquiv.symm_comp_toLinearMap (e : A ≃ₐ[R] B) :
  e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id :=
by simp only [coe_comp, self_trans_symm]; rfl
theorem AlgEquiv.comp_symm_toLinearMap (e : A ≃ₐ[R] B) :
  e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id :=
by simp only [coe_comp, symm_trans_self]; rfl
