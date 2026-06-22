/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.RingTheory.TensorProduct.Basic
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.BasicLemmas
import LeanPool.Monlib4.LinearAlgebra.DirectSumFromTo

/-!
# LeanPool.Monlib4.LinearAlgebra.PiDirectSum

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.PiDirectSum`.
-/

open scoped TensorProduct

local notation x " ⊗ₘ " y => TensorProduct.map x y

theorem DirectSum.tensor_coe_zero {R : Type _} [CommRing R] {ι₁ : Type _} {ι₂ : Type _}
    {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _} [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)]
    [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)] [∀ i₁ : ι₁, Module R (M₁ i₁)]
    [∀ i₂ : ι₂, Module R (M₂ i₂)] :
    ⇑(0 : DirectSum (ι₁ × ι₂) fun i : ι₁ × ι₂ => M₁ i.fst ⊗[R] M₂ i.snd) = 0 :=
  rfl

theorem DirectSum.tensor_coe_add {R : Type _} [CommRing R] {ι₁ : Type _} {ι₂ : Type _}
    {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _} [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)]
    [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)] [∀ i₁ : ι₁, Module R (M₁ i₁)]
    [∀ i₂ : ι₂, Module R (M₂ i₂)]
    (x y : DirectSum (ι₁ × ι₂) fun i : ι₁ × ι₂ => M₁ i.fst ⊗[R] M₂ i.snd) :
    ⇑(x + y : DirectSum (ι₁ × ι₂) fun i : ι₁ × ι₂ => M₁ i.fst ⊗[R] M₂ i.snd) = x + y :=
  rfl

theorem DirectSum.tensor_coe_smul {R : Type _} [CommRing R] {ι₁ : Type _} {ι₂ : Type _}
    {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _} [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)]
    [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)] [∀ i₁ : ι₁, Module R (M₁ i₁)]
    [∀ i₂ : ι₂, Module R (M₂ i₂)]
    (x : DirectSum (ι₁ × ι₂) fun i : ι₁ × ι₂ => M₁ i.fst ⊗[R] M₂ i.snd) (r : R) :
    ⇑(r • x : DirectSum (ι₁ × ι₂) fun i : ι₁ × ι₂ => M₁ i.fst ⊗[R] M₂ i.snd) = r • x :=
  rfl

/-- Include one coordinate tensor factor into the tensor product of dependent function spaces. -/
noncomputable def Pi.tensorOf {R : Type _} [CommSemiring R] {ι₁ ι₂ : Type _}
    [DecidableEq ι₁] [DecidableEq ι₂] {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _}
    [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)]
    [∀ i₁ : ι₁, Module R (M₁ i₁)] [∀ i₂ : ι₂, Module R (M₂ i₂)]
    (i : ι₁ × ι₂) : M₁ i.fst ⊗[R] M₂ i.snd →ₗ[R] (∀ j, M₁ j) ⊗[R] ∀ j, M₂ j :=
  @LinearMap.single R ι₁ _ M₁ _ _ _ i.fst ⊗ₘ @LinearMap.single R ι₂ _ M₂ _ _ _ i.snd

/-- Project the tensor product of dependent function spaces onto one coordinate tensor factor. -/
noncomputable def Pi.tensorProj {R : Type _} [CommSemiring R] {ι₁ ι₂ : Type _} {M₁ : ι₁ → Type _}
    {M₂ : ι₂ → Type _} [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)]
    [∀ i₁ : ι₁, Module R (M₁ i₁)] [∀ i₂ : ι₂, Module R (M₂ i₂)] (i : ι₁ × ι₂) :
    ((∀ j, M₁ j) ⊗[R] ∀ j, M₂ j) →ₗ[R] M₁ i.fst ⊗[R] M₂ i.snd :=
  @LinearMap.proj R ι₁ _ M₁ _ _ i.fst ⊗ₘ @LinearMap.proj R ι₂ _ M₂ _ _ i.snd

/-- The coordinatewise map from a tensor product of dependent functions to tensor factors. -/
noncomputable def directSumTensorToFun {R : Type _} [CommSemiring R] {ι₁ : Type _} {ι₂ : Type _}
    {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _} [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)]
    [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)] [∀ i₁ : ι₁, Module R (M₁ i₁)] [∀ i₂ : ι₂, Module R (M₂ i₂)] :
    ((∀ i, M₁ i) ⊗[R] ∀ i, M₂ i) →ₗ[R] ∀ i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd
    where
  toFun x i := Pi.tensorProj i x
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' r x := by
    simp only [_root_.map_smul, RingHom.id_apply]
    rfl

theorem directSumTensorToFun_apply {R : Type _} [CommSemiring R] {ι₁ : Type _} {ι₂ : Type _}
    {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _} [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)]
    [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)] [∀ i₁ : ι₁, Module R (M₁ i₁)] [∀ i₂ : ι₂, Module R (M₂ i₂)]
    (x : ∀ i, M₁ i) (y : ∀ i, M₂ i) (i : ι₁ × ι₂) :
    directSumTensorToFun (x ⊗ₜ[R] y) i = x i.1 ⊗ₜ[R] y i.2 :=
  rfl

open scoped BigOperators

/-- The finite-sum inverse to `directSumTensorToFun`. -/
noncomputable def directSumTensorInvFun {R : Type _} [CommRing R] {ι₁ : Type _} {ι₂ : Type _}
    [DecidableEq ι₁] [DecidableEq ι₂] [Fintype ι₁] [Fintype ι₂]
    {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _}
    [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)]
    [∀ i₁ : ι₁, Module R (M₁ i₁)] [∀ i₂ : ι₂, Module R (M₂ i₂)] :
    (∀ i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd) →ₗ[R] (∀ i, M₁ i) ⊗[R] ∀ i, M₂ i
    where
  toFun x := ∑ i : ι₁ × ι₂, Pi.tensorOf i (x i)
  map_add' x y := by simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [_root_.map_smul, Pi.smul_apply, RingHom.id_apply]
    rw [← Finset.smul_sum]

theorem Function.sum_update_eq_self {ι₁ : Type _} [DecidableEq ι₁] [Fintype ι₁] {M₁ : ι₁ → Type _}
    [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] (x : ∀ i, M₁ i) :
    ∑ x_1 : ι₁, Function.update (0 : Π (j : ι₁), M₁ j) x_1 (x x_1) = x := by
  ext
  simp only [Finset.sum_apply, Function.update, Finset.sum_dite_eq, Finset.mem_univ, if_true,
    Pi.zero_apply]

theorem directSumTensorInvFun_apply_to_fun {R : Type _} [CommRing R] {ι₁ : Type _} {ι₂ : Type _}
    [DecidableEq ι₁] [DecidableEq ι₂] [Fintype ι₁] [Fintype ι₂] {M₁ : ι₁ → Type _}
    {M₂ : ι₂ → Type _} [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)]
    [∀ i₁ : ι₁, Module R (M₁ i₁)] [∀ i₂ : ι₂, Module R (M₂ i₂)] (x : (∀ i, M₁ i) ⊗[R] ∀ i, M₂ i) :
    directSumTensorInvFun (directSumTensorToFun x) = x :=
  x.induction_on (by simp only [map_zero])
    (fun x y => by
    simp only [directSumTensorInvFun, LinearMap.coe_mk]
    calc
      ∑ i : ι₁ × ι₂, (Pi.tensorOf i) (x i.fst ⊗ₜ[R] y i.snd) =
          ∑ i : ι₁, ∑ j : ι₂, (Pi.tensorOf (i, j)) (x i ⊗ₜ[R] y j) :=
        by simp only [← Finset.sum_product', Finset.univ_product_univ]
      _ =
          ∑ x_1 : ι₁, ∑ x_2 : ι₂,
            Function.update (0 : _) (x_1, x_2).fst (x x_1) ⊗ₜ[R]
              Function.update (0 : _) (x_1, x_2).snd (y x_2) :=
        by simp only [Pi.tensorOf, TensorProduct.map_tmul]; rfl
      _ =
          ∑ x_1 : ι₁, ∑ x_2 : ι₂,
            Function.update (0 : _) x_1 (x x_1) ⊗ₜ[R]
              Function.update (0 : _) x_2 (y x_2) := rfl
      _ =
          (∑ x_1 : ι₁, Function.update (0 : _) x_1 (x x_1)) ⊗ₜ[R]
            ∑ x_2 : ι₂, Function.update (0 : _) x_2 (y x_2) :=
        by simp_rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum]
      _ = x ⊗ₜ[R] y := by congr <;> exact @Function.sum_update_eq_self _ _ _ _ _ _)
  (fun x y hx hy => by simp only [map_add, hx, hy])

theorem Pi.tensorProj_apply_pi_tensorOf {R : Type _} [CommRing R] {ι₁ : Type _} {ι₂ : Type _}
    [DecidableEq ι₁] [DecidableEq ι₂] {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _}
    [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)]
    [∀ i₁ : ι₁, Module R (M₁ i₁)] [∀ i₂ : ι₂, Module R (M₂ i₂)] (i j : ι₁ × ι₂)
    (x : ∀ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2) :
    (Pi.tensorProj i) (Pi.tensorOf j (x j)) = ite (i = j) (x i) 0 := by
  have t1 :
    ∀ i j : ι₁,
      (LinearMap.proj j).comp (LinearMap.single _ _ i) = (directSumFromTo i j : M₁ i →ₗ[R] M₁ j) :=
    fun i j => rfl
  have t2 :
    ∀ i j : ι₂,
      (LinearMap.proj j).comp (LinearMap.single _ _ i) = (directSumFromTo i j : M₂ i →ₗ[R] M₂ j) :=
    fun i j => rfl
  simp only [Pi.tensorOf, Pi.tensorProj, ← LinearMap.comp_apply, ← TensorProduct.map_comp, t1, t2]
  split_ifs with h
  · rw [h]
    simp only [directSumFromTo_apply_same, TensorProduct.map_one, Module.End.one_apply]
  · rw [Prod.eq_iff_fst_eq_snd_eq, not_and_or] at h
    rcases h with (h | h)
    · rw [directSumFromTo_apply_ne_same h, TensorProduct.map_zero_left, LinearMap.zero_apply]
    · rw [directSumFromTo_apply_ne_same h, TensorProduct.map_zero_right, LinearMap.zero_apply]

theorem directSumTensorToFun_apply_inv_fun {R : Type _} [CommRing R] {ι₁ : Type _} {ι₂ : Type _}
    [DecidableEq ι₁] [DecidableEq ι₂] [Fintype ι₁] [Fintype ι₂] {M₁ : ι₁ → Type _}
    {M₂ : ι₂ → Type _} [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)]
    [∀ i₁ : ι₁, Module R (M₁ i₁)] [∀ i₂ : ι₂, Module R (M₂ i₂)]
    (x : ∀ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2) :
    directSumTensorToFun (directSumTensorInvFun x) = x := by
  simp only [directSumTensorToFun, directSumTensorInvFun, LinearMap.coe_mk, map_sum,
    Pi.tensorProj_apply_pi_tensorOf, Fintype.sum_prod_type, AddHom.coe_mk, map_sum]
  ext
  simp only [← Finset.sum_product', Finset.univ_product_univ, Finset.sum_ite_eq,
    Finset.sum_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Linear equivalence between tensor products of finite dependent products and products of tensor
factors. -/
@[simps]
noncomputable def directSumTensor {R : Type _} [CommRing R] {ι₁ : Type _} {ι₂ : Type _}
    [DecidableEq ι₁] [DecidableEq ι₂] [Fintype ι₁] [Fintype ι₂]
    {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _}
    [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)]
    [∀ i₁ : ι₁, Module R (M₁ i₁)] [∀ i₂ : ι₂, Module R (M₂ i₂)] :
    ((∀ i, M₁ i) ⊗[R] ∀ i, M₂ i) ≃ₗ[R] ∀ i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd
    where
  toFun := directSumTensorToFun
  invFun := directSumTensorInvFun
  left_inv x := directSumTensorInvFun_apply_to_fun x
  right_inv x := directSumTensorToFun_apply_inv_fun x
  map_add' _ _ := map_add _ _ _
  map_smul' _ _ := _root_.map_smul _ _ _

theorem directSumTensorToFun.map_mul {R : Type _} [CommRing R] {ι₁ : Type _} {ι₂ : Type _}
    {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _} [∀ i₁ : ι₁, Ring (M₁ i₁)]
    [∀ i₂ : ι₂, Ring (M₂ i₂)]
    [∀ i₁ : ι₁, Algebra R (M₁ i₁)] [∀ i₂ : ι₂, Algebra R (M₂ i₂)]
    (x y : (∀ i, M₁ i) ⊗[R] ∀ i, M₂ i) :
    directSumTensorToFun (x * y) = directSumTensorToFun x * directSumTensorToFun y :=
letI : ZeroHomClass
    (((i : ι₁) → M₁ i) ⊗[R] ((i : ι₂) → M₂ i) →ₗ[R]
      (i : ι₁ × ι₂) → M₁ i.1 ⊗[R] M₂ i.2) _ _ :=
⟨fun x => by simp only [LinearMap.map_zero]⟩
x.induction_on
  (by
    simp only [zero_mul, map_zero]
    )
  (fun x₁ x₂ =>
    y.induction_on
    (by simp only [MulZeroClass.mul_zero, map_zero])
    (fun y₁ y₂ => by
      ext
      simp only [Pi.mul_apply, directSumTensorToFun_apply, Algebra.TensorProduct.tmul_mul_tmul])
    (fun y₁ y₂ hy₁ hy₂ => by simp only [mul_add, map_add, hy₁, hy₂]))
  (fun x₁ x₂ hx hy => by simp only [add_mul, map_add, hx, hy])

theorem directSumTensorToFun.map_one {R : Type _} [CommRing R] {ι₁ : Type _} {ι₂ : Type _}
    {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _} [∀ i₁ : ι₁, Ring (M₁ i₁)]
    [∀ i₂ : ι₂, Ring (M₂ i₂)]
    [∀ i₁ : ι₁, Algebra R (M₁ i₁)] [∀ i₂ : ι₂, Algebra R (M₂ i₂)] :
    directSumTensorToFun (1 : (∀ i, M₁ i) ⊗[R] ∀ i, M₂ i) = 1 :=
  rfl

/-- Algebra equivalence induced by `directSumTensor` for finite dependent products. -/
@[simps]
noncomputable def directSumTensorAlgEquiv (R : Type _) {ι₁ ι₂ : Type _} [CommRing R]
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (M₁ : ι₁ → Type _) (M₂ : ι₂ → Type _) [∀ i₁ : ι₁, Ring (M₁ i₁)]
    [∀ i₂ : ι₂, Ring (M₂ i₂)] [∀ i₁ : ι₁, Algebra R (M₁ i₁)]
    [∀ i₂ : ι₂, Algebra R (M₂ i₂)] :
    ((∀ i, M₁ i) ⊗[R] ∀ i, M₂ i) ≃ₐ[R] ∀ i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd
    where
  toFun x i := directSumTensorToFun x i
  invFun x := (directSumTensorInvFun : _ →ₗ[R] _) (x : ∀ i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd)
  right_inv x := by
    simp only
    rw [directSumTensorToFun_apply_inv_fun]
  left_inv x := by
    simp only
    rw [directSumTensorInvFun_apply_to_fun]
  map_add' x y := by simp only [map_add]
  map_mul' x y := by
    ext
    rw [directSumTensorToFun.map_mul]
  commutes' r := by
    ext
    simp_rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, Pi.smul_apply,
      directSumTensorToFun.map_one]

theorem Pi.tensor_ext_iff {R : Type _} [CommRing R] {ι₁ : Type _} {ι₂ : Type _}
    [Finite ι₁] [Finite ι₂] {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _}
    [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)]
    [∀ i₁ : ι₁, Module R (M₁ i₁)] [∀ i₂ : ι₂, Module R (M₂ i₂)] (x z : ∀ i, M₁ i)
    (y w : ∀ i, M₂ i) :
    x ⊗ₜ[R] y = z ⊗ₜ[R] w ↔ ∀ i j, x i ⊗ₜ[R] y j = z i ⊗ₜ[R] w j := by
  classical
  letI := Fintype.ofFinite ι₁
  letI := Fintype.ofFinite ι₂
  rw [← Function.Injective.eq_iff directSumTensor.injective]
  simp_rw [funext_iff, directSumTensor_apply, directSumTensorToFun_apply, Prod.forall]

theorem Pi.tensor_ext {R : Type _} [CommRing R] {ι₁ : Type _} {ι₂ : Type _}
    [Finite ι₁] [Finite ι₂] {M₁ : ι₁ → Type _} {M₂ : ι₂ → Type _}
    [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₂ : ι₂, AddCommGroup (M₂ i₂)]
    [∀ i₁ : ι₁, Module R (M₁ i₁)] [∀ i₂ : ι₂, Module R (M₂ i₂)] {x z : ∀ i, M₁ i}
    (y w : ∀ i, M₂ i) :
    (∀ i j, x i ⊗ₜ[R] y j = z i ⊗ₜ[R] w j) → x ⊗ₜ[R] y = z ⊗ₜ[R] w := by
  rw [Pi.tensor_ext_iff]
  simp only [imp_self]

/-- Reindex linear maps out of a product-shaped dependent family. -/
@[simps!]
def LinearMap.piPiProd (R : Type _) {ι₁ ι₂ : Type _} [Semiring R] (φ : ι₁ → Type _)
    (ψ : ι₂ → Type _) [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]
    [∀ i, AddCommMonoid (ψ i)] [∀ i, Module R (ψ i)] (S : Type _) [Semiring S]
    [∀ i, Module S (ψ i)] [∀ i, SMulCommClass R S (ψ i)] :
    (∀ i : ι₁ × ι₂, φ i.1 →ₗ[R] ψ i.2) ≃ₗ[S] ∀ i j, φ i →ₗ[R] ψ j
    where
  toFun f j k := f (j, k)
  invFun f i := f i.1 i.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Swap the two function arguments in a doubly-indexed family of linear maps. -/
@[simps!]
def LinearMap.piProdSwap (R : Type _) {ι₁ ι₂ : Type _} [Semiring R] (φ : ι₁ → Type _)
    (ψ : ι₂ → Type _) [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]
    [∀ i, AddCommMonoid (ψ i)] [∀ i, Module R (ψ i)] (S : Type _) [Semiring S]
    [∀ i, Module S (ψ i)] [∀ i, SMulCommClass R S (ψ i)] :
    (∀ i j, φ i →ₗ[R] ψ j) ≃ₗ[S] ∀ j i, φ i →ₗ[R] ψ j
    where
  toFun f j i := f i j
  invFun f i j := f j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Linear equivalence between maps into a dependent product and dependent products of maps. -/
@[simps!]
def LinearMap.rsum (R : Type _) {M : Type _} {ι : Type _} [Semiring R] (φ : ι → Type _)
    [∀ i : ι, AddCommMonoid (φ i)] [∀ i : ι, Module R (φ i)] (S : Type _) [AddCommMonoid M]
    [Module R M] [Semiring S] [∀ i, Module S (φ i)] [∀ i, SMulCommClass R S (φ i)] :
    (∀ i, M →ₗ[R] φ i) ≃ₗ[S] M →ₗ[R] ∀ i, φ i
    where
  toFun f := LinearMap.pi f
  invFun f i := LinearMap.proj i ∘ₗ f
  map_add' f g := by ext; simp only [LinearMap.pi_apply, Pi.add_apply, LinearMap.add_apply]
  map_smul' r f := by
    ext
    simp only [LinearMap.pi_apply, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]
  left_inv f := by ext i x; simp only [LinearMap.proj_pi]
  right_inv f := by
    ext; simp only [LinearMap.comp_apply, LinearMap.pi_apply]
    rfl

/-- Combine `piPiProd`, `piProdSwap`, `lsum`, and `rsum` into a two-sided reindexing equivalence. -/
@[simps!]
def LinearMap.lrsum (R : Type _) {ι₁ ι₂ : Type _} [Semiring R] (φ : ι₁ → Type _) (ψ : ι₂ → Type _)
    [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)] [∀ i, AddCommMonoid (ψ i)]
    [∀ i, Module R (ψ i)] (S : Type _) [Fintype ι₁] [DecidableEq ι₁] [Semiring S]
    [∀ i, Module S (ψ i)] [∀ i, SMulCommClass R S (ψ i)] :
    (∀ i : ι₁ × ι₂, φ i.1 →ₗ[R] ψ i.2) ≃ₗ[S] (∀ i, φ i) →ₗ[R] ∀ i, ψ i := by
  let h₂ : (∀ (j : ι₂) (i : ι₁), φ i →ₗ[R] ψ j) ≃ₗ[S] ∀ j, (∀ i, φ i) →ₗ[R] ψ j := by
    apply LinearEquiv.piCongrRight
    intro j
    exact LinearMap.lsum R φ S
  exact
    (((LinearMap.piPiProd R φ ψ S).trans (LinearMap.piProdSwap R φ ψ S)).trans h₂).trans
      (LinearMap.rsum R ψ S)
