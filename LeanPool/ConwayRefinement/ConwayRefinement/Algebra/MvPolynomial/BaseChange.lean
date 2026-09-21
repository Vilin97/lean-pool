/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Flat.Basic

import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# Algebraic independence under a flat extension of scalars

Let `A` be a commutative `K`-algebra and `y i ∈ A` algebraically independent over `K`: evaluation
`K[X_i] → A`, `X_i ↦ y i`, is injective. For a flat commutative `K`-algebra `L`, the elements
`y i ⊗ 1` of `A ⊗_K L` are algebraically independent over `L`: evaluation `L[X_i] → A ⊗_K L`,
`X_i ↦ y i ⊗ 1`, `l ↦ 1 ⊗ l`, is injective. Through the identification `K[X_i] ⊗_K L ≅ L[X_i]`
this evaluation is the base change of `K[X_i] → A` to `L`, which flatness keeps injective; and
if the `y i` generate `A` over `K`, the `y i ⊗ 1` generate `A ⊗_K L` over `L`.
-/

open scoped TensorProduct

universe u v w x

public noncomputable section

namespace MvPolynomial

variable {K : Type u} {A : Type v} {L : Type w} {σ : Type x}
variable [CommRing K] [CommRing A] [Algebra K A] [CommRing L] [Algebra K L]

/-- The identification `K[X_i] ⊗_K L ≅ L[X_i]` on a variable tensor. -/
theorem scalarRTensorAlgEquiv_X_tmul_one [DecidableEq σ] (i : σ) :
    scalarRTensorAlgEquiv (σ := σ) (R := K) (N := L) (X i ⊗ₜ[K] 1) = X i := by
  classical
  refine MvPolynomial.ext _ _ fun d ↦ ?_
  simp [scalarRTensorAlgEquiv, rTensorAlgEquiv_apply, coeff_rTensorAlgHom_tmul, coeff_map,
    coeff_X, Algebra.smul_def, mul_one, apply_ite (algebraMap K L)]

/-- The identification `K[X_i] ⊗_K L ≅ L[X_i]` on a scalar tensor. -/
theorem scalarRTensorAlgEquiv_one_tmul [DecidableEq σ] (l : L) :
    scalarRTensorAlgEquiv (σ := σ) (R := K) (N := L) (1 ⊗ₜ[K] l) = C l := by
  classical
  refine MvPolynomial.ext _ _ fun d ↦ ?_
  simp [scalarRTensorAlgEquiv, rTensorAlgEquiv_apply, coeff_rTensorAlgHom_tmul, coeff_map,
    coeff_C, coeff_one, apply_ite]
  split_ifs with hd <;> simp [hd]

variable (K L) in
/-- Evaluation `L[X_i] → A ⊗_K L`, `X_i ↦ y i ⊗ 1`, `l ↦ 1 ⊗ l`, as a `K`-algebra
homomorphism. -/
def aevalTmulOne (y : σ → A) : MvPolynomial σ L →ₐ[K] A ⊗[K] L :=
  aevalTower (Algebra.TensorProduct.includeRight : L →ₐ[K] A ⊗[K] L) fun i ↦ y i ⊗ₜ[K] 1

theorem aevalTmulOne_X (y : σ → A) (i : σ) : aevalTmulOne K L y (X i) = y i ⊗ₜ[K] 1 :=
  aevalTower_X _ _ i

theorem aevalTmulOne_C (y : σ → A) (l : L) : aevalTmulOne K L y (C l) = (1 : A) ⊗ₜ[K] l :=
  aevalTower_C _ _ l

/-- Through `K[X_i] ⊗_K L ≅ L[X_i]`, evaluation at the `y i ⊗ 1` is the base change to `L` of
evaluation at the `y i`. -/
theorem aevalTmulOne_comp_scalarRTensorAlgEquiv [DecidableEq σ] (y : σ → A) :
    (aevalTmulOne K L y).comp
        (scalarRTensorAlgEquiv (σ := σ) (R := K) (N := L)).toAlgHom =
      Algebra.TensorProduct.map (aeval y : MvPolynomial σ K →ₐ[K] A) (AlgHom.id K L) := by
  refine Algebra.TensorProduct.ext ?_ ?_
  · refine MvPolynomial.algHom_ext fun i ↦ ?_
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, AlgEquiv.coe_algHom,
      scalarRTensorAlgEquiv_X_tmul_one, aevalTmulOne_X, Algebra.TensorProduct.map_tmul,
      aeval_X, AlgHom.coe_id, id_eq]
  · refine AlgHom.ext fun l ↦ ?_
    simp only [AlgHom.coe_restrictScalars', AlgHom.comp_apply,
      Algebra.TensorProduct.includeRight_apply, AlgEquiv.coe_algHom,
      scalarRTensorAlgEquiv_one_tmul, aevalTmulOne_C, Algebra.TensorProduct.map_tmul,
      map_one, AlgHom.coe_id, id_eq]

/-- Evaluation at the `y i ⊗ 1` of a polynomial with coefficients in `K` is the evaluation at the
`y i` tensored with `1`. -/
theorem aevalTmulOne_map (y : σ → A) (G : MvPolynomial σ K) :
    aevalTmulOne K L y (map (algebraMap K L) G) = aeval y G ⊗ₜ[K] 1 := by
  induction G using MvPolynomial.induction_on with
  | C c =>
    rw [map_C, aevalTmulOne_C, aeval_C, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, TensorProduct.add_tmul]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, map_X, aevalTmulOne_X, map_mul, aeval_X,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- Elements generating `A` over `K` generate `A ⊗_K L` over `L`. -/
theorem aevalTmulOne_surjective {y : σ → A}
    (hy : Function.Surjective (aeval y : MvPolynomial σ K →ₐ[K] A)) :
    Function.Surjective (aevalTmulOne K L y) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a l =>
    obtain ⟨G, rfl⟩ := hy a
    refine ⟨C l * map (algebraMap K L) G, ?_⟩
    rw [map_mul, aevalTmulOne_C, aevalTmulOne_map, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one]
  | add z w hz hw =>
    obtain ⟨F, rfl⟩ := hz
    obtain ⟨G, rfl⟩ := hw
    exact ⟨F + G, map_add _ _ _⟩

/-- Elements algebraically independent over `K` remain algebraically independent over `L` after
a flat extension of scalars `K → L`. -/
theorem aevalTmulOne_injective [Module.Flat K L] {y : σ → A}
    (hy : Function.Injective (aeval y : MvPolynomial σ K →ₐ[K] A)) :
    Function.Injective (aevalTmulOne K L y) := by
  classical
  have hrt : Function.Injective
      (Algebra.TensorProduct.map (aeval y : MvPolynomial σ K →ₐ[K] A) (AlgHom.id K L)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (R := K) (M := L)
      (aeval y : MvPolynomial σ K →ₐ[K] A).toLinearMap hy
  set e := scalarRTensorAlgEquiv (σ := σ) (R := K) (N := L)
  have key : ∀ u, aevalTmulOne K L y (e u) =
      Algebra.TensorProduct.map (aeval y : MvPolynomial σ K →ₐ[K] A) (AlgHom.id K L) u :=
    fun u ↦ congrFun (congrArg (fun f : _ →ₐ[K] _ ↦ (f : _ → _))
      (aevalTmulOne_comp_scalarRTensorAlgEquiv y)) u
  intro a b hab
  rw [← e.apply_symm_apply a, ← e.apply_symm_apply b, key, key] at hab
  rw [← e.apply_symm_apply a, ← e.apply_symm_apply b, hrt hab]

end MvPolynomial
