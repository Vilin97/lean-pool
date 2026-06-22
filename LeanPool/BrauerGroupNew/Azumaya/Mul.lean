/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.Azumaya.Basic
import Mathlib.Algebra.Azumaya.Matrix
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Opposite

/-!
# LeanPool.BrauerGroupNew.Azumaya.Mul

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Azumaya.Mul`.
-/

suppress_compilation

open Function
open scoped TensorProduct

universe u v

variable (R : Type u) [CommRing R]

section formathlib

variable (R : Type u) [CommRing R] (M N P Q : Type*) [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N] [Module.Projective R M]
  [Module.Projective R N] [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module R Q]

/-- The rank of a finite free module used to split a finite projective module. -/
abbrev nn : ℕ := (Module.Finite.exists_comp_eq_id_of_projective R M).choose

/-- The surjective map from a finite free module onto a finite projective module. -/
abbrev f0 : (Fin (nn R M) → R) →ₗ[R] M :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose

/-- The injective splitting map from a finite projective module into a finite free module. -/
abbrev g0 : M →ₗ[R] Fin (nn R M) → R :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose

lemma f0_surj : Function.Surjective (f0 R M) :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.1

lemma g0_inj : Function.Injective (g0 R M) :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.2.1

lemma fg : (f0 R M) ∘ₗ (g0 R M) = LinearMap.id :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.2.2

/-- Precomposition with `f0`, embedding maps out of `M` into maps out of a finite free module. -/
abbrev inclusion1 : (M →ₗ[R] P) →ₗ[R] ((Fin (nn R M) → R) →ₗ[R] P) where
  toFun := fun f ↦ f.comp (f0 R M)
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]

/-- Precomposition with `g0`, projecting maps from the finite free cover
back to maps out of `M`. -/
abbrev projection1 : ((Fin (nn R M) → R) →ₗ[R] P) →ₗ[R] (M →ₗ[R] P) where
  toFun := fun f ↦ f.comp (g0 R M)
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]

/-- Hom(M, P) ⊗ Hom(N, Q) →ₗ[R] Hom(Rⁿ, P) ⊗ Hom(Rᵐ, Q) -/
abbrev tensorInclusion1 :
    (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) →ₗ[R]
      ((Fin (nn R M) → R) →ₗ[R] P) ⊗[R] ((Fin (nn R N) → R) →ₗ[R] Q) :=
  TensorProduct.map (inclusion1 R M P) (inclusion1 R N Q)

/-- Tensor product of the two first projection maps. -/
abbrev tensorProjection1 := TensorProduct.map (projection1 R M P) (projection1 R N Q)

lemma projection_inlusion1 : (projection1 R M P).comp (inclusion1 R M P) = LinearMap.id := by
  ext f : 1
  simp [LinearMap.comp_assoc, fg]

lemma tensorInclusion1_projection1 : (tensorProjection1 R M N P Q).comp
    (tensorInclusion1 R M N P Q) = LinearMap.id := by
  simp [← TensorProduct.map_comp, projection_inlusion1]

lemma tensorInclusion1_projection1_apply (x : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)) :
    tensorProjection1 R M N P Q (tensorInclusion1 R M N P Q x) = x :=
  DFunLike.congr_fun (tensorInclusion1_projection1 R M N P Q) x

lemma tensorInclusion1_inj : Function.Injective (tensorInclusion1 R M N P Q) :=
  Function.LeftInverse.injective (g := tensorProjection1 R M N P Q)
    <| DFunLike.congr_fun <| tensorInclusion1_projection1 R M N P Q

open TensorProduct in
lemma Tensor_isDirectSummand : ∃(s0 : M ⊗[R] N →ₗ[R] (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R))
    (s1 : (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R] M ⊗[R] N), s1.comp s0 = .id :=
  ⟨map (g0 R M) (g0 R N), map (f0 R M) (f0 R N), by simp [← map_comp, fg]⟩

variable {R M N} in
/-- The tensor-product inclusion induced by the free-module splittings of `M` and `N`. -/
abbrev inclusion2 : M ⊗[R] N →ₗ[R] (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) :=
  TensorProduct.map (g0 R M) (g0 R N)

variable {R M N} in
/-- The tensor-product projection induced by the free-module covers of `M` and `N`. -/
abbrev projection2 : (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R] M ⊗[R] N :=
  TensorProduct.map (f0 R M) (f0 R N)

variable {M N} in
/-- Precomposition with `projection2` on homs out of `M ⊗ N`. -/
abbrev tensorInclusion2 : (M ⊗[R] N →ₗ[R] P ⊗[R] Q) →ₗ[R]
    ((Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R] P ⊗[R] Q) where
  toFun := fun f ↦ f.comp projection2
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]

variable {M N} in
/-- Precomposition with `inclusion2` on homs out of the finite free tensor product. -/
abbrev tensorProjection2 : ((Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R]
    P ⊗[R] Q) →ₗ[R] (M ⊗[R] N →ₗ[R] P ⊗[R] Q) where
  toFun := fun f ↦ f.comp inclusion2
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]

lemma projection2_inclusion2 : (projection2).comp (inclusion2) =
    LinearMap.id (R := R) (M := M ⊗[R] N) :=
  by simp [← TensorProduct.map_comp, fg]

lemma projection2_inclusion2_apply (x : M ⊗[R] N) : (projection2) ((inclusion2) x) = x :=
  DFunLike.congr_fun (projection2_inclusion2 R M N) x

lemma tensorProjection2_inclusion2 : (tensorProjection2 R P Q).comp (tensorInclusion2 R P Q) =
    LinearMap.id (R := R) (M := M ⊗[R] N →ₗ[R] P ⊗[R] Q) := by
  ext f : 1
  simp [LinearMap.comp_assoc, projection2_inclusion2]

lemma tensorInclusion2_inj : Function.Injective (tensorInclusion2 R (M := M) (N := N) P Q) :=
  Function.LeftInverse.injective (g := tensorProjection2 R P Q)
    <| DFunLike.congr_fun <| tensorProjection2_inclusion2 R M N P Q

/-- This proves the following square commutes:
               `TensorProduct.homTensorHomMap`
Hom(M, P) ⊗ Hom(N, Q) ---------------> Hom(M ⊗ N, P ⊗ Q)
    |       |                             |      |
 i  |       |  j                       i' |      |  j'
    |       |                             |      |
    |       |                             |      |
Hom(Rⁿ, P) ⊗ Hom(Rᵐ, Q) -------------> Hom(Rⁿ ⊗ Rᵐ, P ⊗ Q)
-/
lemma comm_square2 : (homTensorHomEquiv R (Fin (nn R M) → R) (Fin (nn R N) → R) P Q).toLinearMap ∘ₗ
    tensorInclusion1 R M N P Q =
      tensorInclusion2 R P Q ∘ₗ TensorProduct.homTensorHomMap _ M N P Q := by
  ext f g : 4
  refine LinearMap.ext fun v ↦ LinearMap.ext fun u ↦ ?_
  simp

lemma comm_square2_apply (f : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)) :
  (homTensorHomEquiv R (Fin (nn R M) → R) (Fin (nn R N) → R) P Q).toLinearMap
    (tensorInclusion1 R M N P Q f) =
      tensorInclusion2 R P Q (TensorProduct.homTensorHomMap _ M N P Q f) :=
  DFunLike.congr_fun (comm_square2 R M N P Q) f

lemma homTensorHomMap_inj : Function.Injective (TensorProduct.homTensorHomMap (.id R) M N P Q) := by
  apply Function.Injective.of_comp (f := tensorInclusion2 R P Q)
  rw [← LinearMap.coe_comp, ← comm_square2]
  exact Function.Injective.comp (f := tensorInclusion1 R M N P Q)
    (homTensorHomEquiv R (Fin (nn R M) → R) (Fin (nn R N) → R) P Q).injective <|
    tensorInclusion1_inj R M N P Q

lemma comm_square3 : (homTensorHomEquiv R _ _ _ _).toLinearMap ∘ₗ
    tensorInclusion1 R M N P Q ∘ₗ tensorProjection1 R M N P Q = tensorInclusion2 R P Q ∘ₗ
    tensorProjection2 R P Q ∘ₗ (homTensorHomEquiv R _ _ _ _).toLinearMap := by
  ext f g : 4
  refine LinearMap.ext fun v ↦ LinearMap.ext fun u ↦ ?_
  simp

lemma comm_square3_apply (f : ((Fin (nn R M) → R) →ₗ[R] P) ⊗[R] ((Fin (nn R N) → R) →ₗ[R] Q)) :
    (homTensorHomEquiv R _ _ _ _) (tensorInclusion1 R M N P Q (tensorProjection1 R M N P Q f)) =
    tensorInclusion2 R P Q (tensorProjection2 R P Q (homTensorHomEquiv R _ _ _ _ f)) :=
  DFunLike.congr_fun (comm_square3 R M N P Q) f

lemma comm_square1 :
    tensorProjection1 R M N P Q ∘ₗ (homTensorHomEquiv R _ _ P Q).symm.toLinearMap ∘ₗ
      tensorInclusion2 R P Q ∘ₗ TensorProduct.homTensorHomMap _ M N P Q =
        .id (R := R) (M := (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)) := by
  rw [← comm_square2]
  apply LinearMap.ext
  simp [-homTensorHomEquiv_toLinearMap, -homTensorHomEquiv_apply,
    tensorInclusion1_projection1_apply]

lemma comm_square4 :
    TensorProduct.homTensorHomMap _ M N P Q ∘ₗ tensorProjection1 R M N P Q ∘ₗ
      (homTensorHomEquiv R _ _ _ _).symm.toLinearMap ∘ₗ tensorInclusion2 R P Q =
        .id (R := R) (M := (M ⊗[R] N) →ₗ[R] P ⊗[R] Q) := by
  apply LinearMap.ext
  intro fgfg
  simp only [LinearMap.comp_apply]
  apply tensorInclusion2_inj
  rw [← comm_square2_apply, LinearEquiv.coe_toLinearMap, comm_square3_apply]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq]
  apply LinearMap.ext
  simp [projection2_inclusion2_apply]

lemma homTensorHomMap_surj : Surjective (TensorProduct.homTensorHomMap (.id R) M N P Q) := by
  apply Function.Surjective.of_comp (g := (tensorProjection1 R M N P Q ∘ₗ
    (homTensorHomEquiv R _ _ _ _).symm.toLinearMap ∘ₗ tensorInclusion2 R P Q))
  rw [← LinearMap.coe_comp, comm_square4]
  exact CharacterModule.surjective_of_dual_injective LinearMap.id fun ⦃a₁ a₂⦄ a ↦ a

end formathlib

open MulOpposite

/-- An Azumaya algebra over a commutative base ring, bundled as an algebra object. -/
structure Azumaya (R : Type u) [CommRing R] extends AlgCat R where
  isAzumaya : IsAzumaya R carrier

@[coe]
instance : CoeSort (Azumaya R) (Type v) where
  coe s := s.carrier

attribute [instance] Azumaya.isAzumaya

/-- Morita equivalence of the carrier algebras of two bundled Azumaya algebras. -/
def Azumaya.IsMoritaEquivalent : Azumaya R → Azumaya R → Prop :=
    fun A B ↦ _root_.IsMoritaEquivalent R A.carrier B.carrier

lemma Azumaya.IsMoritaEquivalent.iff {A B : Azumaya R} :
  Azumaya.IsMoritaEquivalent R A B ↔ _root_.IsMoritaEquivalent R A.carrier B.carrier :=
  Iff.rfl

lemma AzuMorita.equiv : Equivalence (Azumaya.IsMoritaEquivalent R) where
  refl _ := .refl R _
  symm := .symm R
  trans := .trans R

/-- The setoid on Azumaya algebras induced by Morita equivalence. -/
abbrev AzumayaSetoid : Setoid (Azumaya R) where
  r := Azumaya.IsMoritaEquivalent R
  iseqv := AzuMorita.equiv R

namespace Azumaya

variable (A B : Type v) [Ring A] [Ring B] [Algebra R A] [Algebra R B]
instance [Module.Finite R A] [Module.Finite R B] :
    Module.Finite R (A ⊗[R] B) := Module.Finite.tensorProduct R A B

variable {R A B} in
instance faithfulSMulTensor [Module.Projective R A] [Module.Projective R B]
    [FaithfulSMul R A] [FaithfulSMul R B] :
    FaithfulSMul R (A ⊗[R] B) where
  eq_of_smul_eq_smul {r1 r2} eq := by
    specialize eq 1
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul'] at eq
    have := Algebra.TensorProduct.includeLeft_injective (R := R) (S := R)
      (fun r1 r2 h ↦ by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at h
        exact eq_of_smul_eq_smul (M := R) (α := B) (m₁ := r1) (m₂ := r2) (by
          intro b
          rw [← one_mul b, ← smul_mul_assoc, h, smul_mul_assoc, one_mul])) eq
    exact eq_of_smul_eq_smul (M := R) (α := A) (m₁ := r1) (m₂ := r2) <|
      fun a ↦ by rw [← one_mul a, ← smul_mul_assoc, this, smul_mul_assoc, one_mul]

open Algebra.TensorProduct (assoc congr opAlgEquiv) in
variable {R A B} in
/-- Rebracketing equivalence used to compare `mulLeftRight` with tensor products. -/
abbrev e : (A ⊗[R] Aᵐᵒᵖ) ⊗[R] (B ⊗[R] Bᵐᵒᵖ) ≃ₐ[R] (A ⊗[R] B) ⊗[R] (A ⊗[R] B)ᵐᵒᵖ :=
  (assoc R R R A B (Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ)|>.trans <|
  (congr .refl (assoc R R R B Aᵐᵒᵖ Bᵐᵒᵖ)).symm.trans <|
  congr .refl (congr (Algebra.TensorProduct.comm R _ _) .refl) |>.trans
  <| congr .refl (assoc R R R Aᵐᵒᵖ B Bᵐᵒᵖ) |>.trans
  <| assoc R R R A Aᵐᵒᵖ (B ⊗[R] Bᵐᵒᵖ)|>.symm).symm.trans
  <| Algebra.TensorProduct.congr .refl <| opAlgEquiv R R A B

lemma e_apply (a : A) (b : B) (a' : Aᵐᵒᵖ) (b' : Bᵐᵒᵖ) :
    e ((a ⊗ₜ a') ⊗ₜ (b ⊗ₜ b')) = (a ⊗ₜ b) ⊗ₜ op (a'.unop ⊗ₜ[R] b'.unop) := rfl

open TensorProduct.AlgebraTensorModule in
lemma top_square_comm'' (A B : Azumaya R) :
    (TensorProduct.homTensorHomMap _ A B A B) ∘ₗ (Algebra.TensorProduct.congr
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R A) A.isAzumaya.bij)
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R B) B.isAzumaya.bij)).toLinearMap
    = (AlgHom.mulLeftRight R (A ⊗[R] B)).toLinearMap ∘ₗ
    (e (R := R) (A := A) (B := B)).toLinearEquiv.toLinearMap := by
  ext a b c d a' b'
  dsimp
  simp [AlgHom.mulLeftRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.homTensorHomMap_apply, unop_op]

lemma top_square_comm (A B : Azumaya R) :
    (TensorProduct.homTensorHomMap _ A B A B) ∘ (Algebra.TensorProduct.congr
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R A) A.isAzumaya.bij)
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R B) B.isAzumaya.bij))
    = (AlgHom.mulLeftRight R (A ⊗[R] B)) ∘ e :=
  congr_arg DFunLike.coe <| top_square_comm'' R A B

/--
A ⊗ Aᵐᵒᵖ ⊗ B ⊗ B ᵐᵒᵖ --------> (A ⊗ B) ⊗ (A ⊗ B)ᵐᵒᵖ
        |                              |
        |                              |
        |                              |
        |                              |
      f ⊗ g            ---->         f ⊗ g
End R A ⊗ End R B ---------------> End R (A ⊗ B)
    |     |                           |   |
  i |     | j                     i'  |   |  j'
    |     |                           |   |
    |     |   `homTensorHomEquiv`     |   |
End R Rⁿ ⊗ End R Rᵐ -------------> End R (Rⁿ ⊗ Rᵐ)
-/
lemma bij_homtensorhom (A B : Azumaya.{u, v} R) :
    Function.Bijective (TensorProduct.homTensorHomMap (.id R) A B A B) :=
  ⟨homTensorHomMap_inj R A B A B, homTensorHomMap_surj R A B A B⟩

/-- The hom-tensor-hom equivalence for the carriers of two Azumaya algebras. -/
abbrev e1 (A B : Azumaya.{u, v} R) :
    (Module.End R A ⊗[R] Module.End R B) ≃ₗ[R] Module.End R (A ⊗[R] B) :=
  .ofBijective (TensorProduct.homTensorHomMap _ A B A B) <| bij_homtensorhom R A B

/-- The tensor-product equivalence induced by the two `mulLeftRight` bijections. -/
abbrev e2 (A B : Azumaya R) := (Algebra.TensorProduct.congr
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R A) A.isAzumaya.bij)
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R B) B.isAzumaya.bij))

lemma top_square_comm_apply (A B : Azumaya R) (x : (A ⊗[R] Aᵐᵒᵖ) ⊗[R] (B ⊗[R] Bᵐᵒᵖ)) :
    (e1 R A B) (e2 R A B x) = (AlgHom.mulLeftRight R (A ⊗[R] B)) (e.toAlgHom x) := by
  erw [← AlgHom.comp_apply, AlgHom.coe_comp, ← top_square_comm]
  rfl

lemma bij_mulLeftRight (A B : Azumaya.{u, v} R) :
    Function.Bijective (AlgHom.mulLeftRight R (A ⊗[R] B)) :=
  Function.Bijective.of_comp_iff (AlgHom.mulLeftRight R (A ⊗[R] B))
    (e (R := R) (A := A) (B := B)).bijective|>.1 <| by
  rw [← top_square_comm]
  change Function.Bijective (e1 R A B ∘ e2 R A B)
  exact (e1 R A B).bijective.comp (e2 R A B).bijective

/-- Tensor product of bundled Azumaya algebras. -/
abbrev mul (A B : Azumaya R) : Azumaya R where
  __ := AlgCat.of R (A.carrier ⊗[R] B.carrier)
  isAzumaya.out := Module.Projective.tensorProduct|>.out
  isAzumaya.eq_of_smul_eq_smul := Azumaya.faithfulSMulTensor|>.eq_of_smul_eq_smul
  isAzumaya.fg_top := Module.Finite.tensorProduct R A B|>.fg_top
  isAzumaya.bij := bij_mulLeftRight R A B

instance : Mul (Azumaya R) where
  mul A B := mul R A B

lemma mul_coe (A B : Azumaya.{u, v} R) :
    (A * B) = ⟨.of R (A ⊗[R] B), ⟨bij_mulLeftRight R A B⟩⟩ := rfl

instance : One (Azumaya R) where
  one := ⟨.of R R, IsAzumaya_R R⟩

instance : FaithfulSMul R Rᵐᵒᵖ where
  eq_of_smul_eq_smul {r1 r2} hr := by
    specialize hr 1
    change op _ = op _ at hr
    simp only [unop_one, smul_eq_mul, mul_one, op_inj] at hr
    exact hr

/--
A ⊗ Aᵐᵒᵖ  ------------> B ⊗ Bᵐᵒᵖ
  |                        |
  |                        |
  |                        |
  |                        |
End R A   ------------> End R B
-/
lemma small_comm_square (e : A ≃ₐ[R] B) :
    (AlgHom.mulLeftRight R B).comp (Algebra.TensorProduct.congr e e.op).toAlgHom =
      (e.toLinearEquiv.conjAlgEquiv R).toAlgHom.comp (AlgHom.mulLeftRight R A) := by
  apply AlgHom.ext
  intro a
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a a' =>
    ext
    simp [AlgHom.mulLeftRight_apply, LinearEquiv.conjAlgEquiv]
  | add _ _ _ _ => simp_all [map_add]

lemma _root_.IsAzumaya.ofAlgEquiv (e : A ≃ₐ[R] B) (hA : IsAzumaya R A) : IsAzumaya R B :=
  let _ : Module.Projective R B := .of_equiv e.toLinearEquiv
  let _ : FaithfulSMul R B := .of_injective e e.injective
  let _ : Module.Finite R B := .equiv e.toLinearEquiv
  ⟨Function.Bijective.of_comp_iff (AlgHom.mulLeftRight R B)
    (Algebra.TensorProduct.congr e e.op).bijective |>.1 <| by
    erw [← AlgHom.coe_comp, small_comm_square]
    simp [hA.bij]⟩

/-- Inclusion of endomorphisms induced by a finite free cover of a projective module. -/
abbrev inclusion' (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : Module.End R M →ₗ[R] Module.End R (Fin (nn R M) → R) where
  toFun := fun f ↦ g0 R M ∘ₗ f ∘ₗ f0 R M
  map_add' := fun _ _ ↦ by simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' := fun _ _ ↦ by simp [LinearMap.smul_comp, LinearMap.comp_smul]

/-- Projection of endomorphisms induced by a splitting of the finite free cover. -/
abbrev projection' (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : Module.End R (Fin (nn R M) → R) →ₗ[R] Module.End R M where
  toFun := fun f ↦ f0 R M ∘ₗ f ∘ₗ g0 R M
  map_add' := fun _ _ ↦ by simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' := fun _ _ ↦ by simp [LinearMap.smul_comp, LinearMap.comp_smul]

lemma projection'_inclusion' (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : projection' R M ∘ₗ inclusion' R M = LinearMap.id := by
  ext f : 1
  simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, comp_apply, LinearMap.id_coe,
    id_eq]
  simp only [LinearMap.comp_assoc, fg, LinearMap.comp_id]
  rw [← LinearMap.comp_assoc, fg, LinearMap.id_comp]

lemma projection'_surj (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : Function.Surjective (projection' R M) :=
  Function.Surjective.of_comp (g := inclusion' R M) <| by
  rw [← LinearMap.coe_comp, projection'_inclusion']
  exact Function.surjective_id

lemma _root_.Module.Projective.ofEnd (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : Module.Projective R (Module.End R M) :=
  .of_split (M := Module.End R (Fin (nn R M) → R)) (inclusion' R M) (projection' R M)
    <| projection'_inclusion' R M

instance _root_.Module.Finite.End (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : Module.Finite R (Module.End R M) :=
  Module.Finite.of_surjective (projection' R M) (projection'_surj R M)

instance (M : Type v) [AddCommGroup M] [Module R M] [FaithfulSMul R M] :
    FaithfulSMul R (Module.End R M) where
  eq_of_smul_eq_smul {r1 r2} h12 := by
    specialize h12 1
    rw [LinearMap.ext_iff] at h12
    simp only [LinearMap.smul_apply, Module.End.one_apply] at h12
    exact eq_of_smul_eq_smul h12

/-- The matrix algebra as a bundled Azumaya algebra. -/
abbrev MatrixAlg (n : ℕ) [NeZero n] : Azumaya R := {
  __ := AlgCat.of R (_root_.Matrix (Fin n) (Fin n) R)
  isAzumaya := IsAzumaya.matrix R (Fin n) }

/-- The endomorphism algebra of `R^n` as a bundled Azumaya algebra. -/
abbrev EndRn (n : ℕ) [NeZero n] : Azumaya R := {
  __ := AlgCat.of R (Module.End R (Fin n → R))
  isAzumaya := IsAzumaya.ofAlgEquiv R _ _
    LinearMap.toMatrixAlgEquiv'.symm <| IsAzumaya.matrix R (Fin n)
}

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M]

open MulOpposite

/-- Tensor inclusion on endomorphism algebras induced by `inclusion'`. -/
abbrev tensorInclusion1' : (Module.End R M) ⊗[R] (Module.End R M)ᵐᵒᵖ →ₗ[R]
    (Module.End R (Fin (nn R M) → R)) ⊗[R] (Module.End R (Fin (nn R M) → R))ᵐᵒᵖ :=
  TensorProduct.map (inclusion' R M) <|
    (opLinearEquiv R).toLinearMap ∘ₗ (inclusion' R M) ∘ₗ (opLinearEquiv R).symm.toLinearMap

/-- Tensor projection on endomorphism algebras induced by `projection'`. -/
abbrev tensorProjection1' :
    Module.End R (Fin (nn R M) → R) ⊗[R] (Module.End R (Fin (nn R M) → R))ᵐᵒᵖ →ₗ[R]
      Module.End R M ⊗[R] (Module.End R M)ᵐᵒᵖ :=
  TensorProduct.map (projection' R M) <|
    (opLinearEquiv R).toLinearMap ∘ₗ (projection' R M) ∘ₗ (opLinearEquiv R).symm.toLinearMap

lemma tensor_projection_inclusion1' : tensorProjection1' R M ∘ₗ tensorInclusion1' R M = .id := by
  ext f g
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
    TensorProduct.curry_apply, LinearMap.coe_comp, comp_apply, TensorProduct.map_tmul,
    LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_coe, coe_opLinearEquiv,
    coe_opLinearEquiv_symm, unop_op, LinearMap.id_coe, id_eq]
  simp only [LinearMap.comp_assoc, fg, LinearMap.comp_id]
  rw [← LinearMap.comp_assoc, fg, LinearMap.id_comp]
  rw [← LinearMap.comp_assoc, fg, LinearMap.id_comp, op_unop]

lemma tensorInclusion1'_inj : Function.Injective (tensorInclusion1' R M) :=
  Function.LeftInverse.injective (g := tensorProjection1' R M)
    <| DFunLike.congr_fun <| tensor_projection_inclusion1' R M

/-- Inclusion between second endomorphism algebras induced by the free-module splitting. -/
abbrev inclusion2' : Module.End R (Module.End R M) →ₗ[R]
    Module.End R (Module.End R (Fin (nn R M) → R)) where
  toFun f := inclusion' R M ∘ₗ f ∘ₗ projection' R M
  map_add' _ _ := by simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' := by simp [LinearMap.smul_comp, LinearMap.comp_smul]

/-- Projection between second endomorphism algebras induced by the free-module splitting. -/
abbrev projection2' : Module.End R (Module.End R (Fin (nn R M) → R)) →ₗ[R]
    Module.End R (Module.End R M) where
  toFun f := projection' R M ∘ₗ f ∘ₗ inclusion' R M
  map_add' _ _ := by simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' := by simp [LinearMap.smul_comp, LinearMap.comp_smul]

lemma projection2'_inclusion2' : projection2' R M ∘ₗ inclusion2' R M = LinearMap.id := by
  ext f g : 2
  simp [LinearMap.comp_assoc, fg]
  simp [← LinearMap.comp_assoc, fg]

lemma projection2'_surj : Function.Surjective (projection2' R M) :=
  Function.RightInverse.surjective <| DFunLike.congr_fun <| projection2'_inclusion2' R M

/--
End R M ⊗ (End R M)ᵐᵒᵖ ------------> End R (End R M)
    |         |                        |      |
    |         |                        |      |
    |         |                        |      |
    |         |                        |      |
End R Rⁿ ⊗ (End R Rⁿ)ᵐᵒᵖ ----------> End R (End R Rⁿ)
-/
lemma comm_square_endend :
    inclusion2' R M ∘ₗ (AlgHom.mulLeftRight R (Module.End R M)).toLinearMap =
    (AlgHom.mulLeftRight R (Module.End R (Fin (nn R M) → R))).toLinearMap ∘ₗ
      (tensorInclusion1' R M) := by
  ext f1 g1 : 3
  apply LinearMap.ext
  intro f2
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp,
    TensorProduct.curry_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply, AlgHom.toLinearMap_apply,
    TensorProduct.map_tmul, LinearEquiv.coe_coe, coe_opLinearEquiv, coe_opLinearEquiv_symm,
    AlgHom.mulLeftRight_apply, unop_op]
  ext i j
  simp

lemma comm_square_endend' :
    (AlgHom.mulLeftRight R (Module.End R M)).toLinearMap ∘ₗ tensorProjection1' R M =
    projection2' R M ∘ₗ
      (AlgHom.mulLeftRight R (Module.End R (Fin (nn R M) → R))).toLinearMap := by
  ext f1 g1 : 3
  apply LinearMap.ext
  intro f2
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp,
    TensorProduct.curry_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, TensorProduct.map_tmul, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.coe_coe, coe_opLinearEquiv, coe_opLinearEquiv_symm, AlgHom.toLinearMap_apply,
    AlgHom.mulLeftRight_apply, unop_op]
  ext m
  simp

variable [Nontrivial M]

instance : NeZero (nn R M) := ⟨by
  by_contra! hn
  have : Subsingleton (Fin (nn R M) → R) := by
    rw [hn]
    exact Unique.instSubsingleton
  have : Subsingleton M := Function.Surjective.subsingleton (f0_surj R M)
  have : ¬ (Subsingleton M) := not_subsingleton_iff_nontrivial.2 inferInstance
  tauto⟩

lemma inj_endM : Function.Injective (AlgHom.mulLeftRight R (Module.End R M)) := by
  refine .of_comp (f := inclusion2' R M) ?_
  suffices Function.Injective ((inclusion2' R M) ∘ₗ (AlgHom.mulLeftRight _ _).toLinearMap) by
    rw [LinearMap.coe_comp] at this; exact this
  rw [comm_square_endend, LinearMap.coe_comp]
  exact (EndRn R (nn R M)).isAzumaya.bij.injective.comp <| tensorInclusion1'_inj R M

lemma surj_endM : Function.Surjective (AlgHom.mulLeftRight R (Module.End R M)) := by
  refine .of_comp (g := tensorProjection1' R M) ?_
  change Function.Surjective
    ((AlgHom.mulLeftRight R (Module.End R M)).toLinearMap ∘ₗ tensorProjection1' R M)
  rw [comm_square_endend', LinearMap.coe_comp]
  exact (projection2'_surj R M).comp (EndRn R (nn R M)).isAzumaya.bij.surjective

lemma bij_endM : Function.Bijective (AlgHom.mulLeftRight R (Module.End R M)) :=
  ⟨inj_endM R M, surj_endM R M⟩

/-- The endomorphism algebra of a faithful finite projective module is Azumaya. -/
abbrev ofEnd [FaithfulSMul R M] : Azumaya R where
  __ := AlgCat.of R (Module.End R M)
  isAzumaya.out := Module.Projective.ofEnd R M|>.out
  isAzumaya.bij := bij_endM R M

end Azumaya
