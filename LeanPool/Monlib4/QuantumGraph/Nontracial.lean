/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.LinearAlgebra.Ips.MatIps
import LeanPool.Monlib4.LinearAlgebra.Ips.Nontracial
import LeanPool.Monlib4.LinearAlgebra.Ips.TensorHilbert
import LeanPool.Monlib4.LinearAlgebra.IsReal
import LeanPool.Monlib4.LinearAlgebra.Ips.Frob
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.FiniteDimensional
import LeanPool.Monlib4.LinearAlgebra.Ips.OpUnop
import LeanPool.Monlib4.LinearAlgebra.LmulRmul
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.SchurMul
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Symm
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Instances

/-!
 # Quantum graphs: quantum adjacency matrices

 This file defines the quantum adjacency matrix of a quantum graph.
-/


variable {n p : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

open scoped TensorProduct BigOperators Kronecker

local notation "ℍ" => Matrix n n ℂ
local notation "ℍ₂" => Matrix p p ℂ

local notation "⊗K" => Matrix (n × n) (n × n) ℂ

local notation "l(" x ")" => x →ₗ[ℂ] x

local notation "L(" x ")" => x →L[ℂ] x

local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)

variable {φ : Module.Dual ℂ (Matrix n n ℂ)} {ψ : Module.Dual ℂ (Matrix p p ℂ)}

open scoped Matrix

open Matrix

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ ℍ

local notation "η" => Algebra.linearMap ℂ ℍ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" =>
  LinearEquiv.toLinearMap (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ))

local notation "υ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n
    ℂ) (Matrix n n ℂ)))

local notation "ϰ" =>
  LinearEquiv.toLinearMap ((TensorProduct.comm ℂ (Matrix n n ℂ) ℂ))

local notation "ϰ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.comm ℂ (Matrix n n ℂ) ℂ))

local notation "τ" =>
  LinearEquiv.toLinearMap (TensorProduct.lid ℂ (Matrix n n ℂ))

local notation "τ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.lid ℂ (Matrix n n ℂ)))

local notation "id" => (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

open TensorProduct

theorem Finset.sum_fin_one {α : Type _} [AddCommMonoid α] (f : Fin 1 → α) : ∑ i, f i = f 0 := by
  have h : (Finset.univ : Finset (Fin 1)) = {0} := by
    ext i
    simp [Subsingleton.elim i 0]
  rw [h, Finset.sum_singleton]

-- theorem LinearMap.IsReal.adjoint_isReal_iff_commute_with_sig  [hφ : φ.IsFaithfulPosMap] {f : ℍ
-- →ₗ[ℂ] ℍ} (hf : LinearMap.IsReal f) :
--     LinearMap.IsReal (LinearMap.adjoint f) ↔ Commute f (hφ.sig 1).toLinearMap :=
--   by
--   rw [LinearMap.isReal_iff] at hf
--   let σ := hφ.sig
--   have : Commute f (σ 1).toLinearMap ↔ Commute (LinearMap.adjoint f) (σ 1).toLinearMap :=
--     by
--     simp_rw [σ]
--     nth_rw 2 [← Module.Dual.IsFaithfulPosMap.sig_adjoint]
--     rw [commute.adjoint_adjoint_lm]
--   rw [this]
--   clear this
--   rw [LinearMap.isReal_iff, LinearMap.adjoint_real_apply, hf, ← LinearMap.comp_assoc,
-- comp_sig_eq,
--     neg_neg]
--   simp_rw [Commute, SemiconjBy, LinearMap.mul_eq_comp, @eq_comm _ _ ((σ 1).toLinearMap ∘ₗ _)]

theorem sig_apply_posDef_matrix_hMul [hφ : φ.IsFaithfulPosMap] (t : ℝ) (x : ℍ) :
    hφ.sig t (hφ.matrixIsPosDef.rpow t * x) = x * hφ.matrixIsPosDef.rpow t := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, ← Matrix.mul_assoc, PosDef.rpow_mul_rpow,
    neg_add_cancel, PosDef.rpow_zero, Matrix.one_mul]

theorem sig_apply_posDef_matrix_mul' [hφ : φ.IsFaithfulPosMap] (x : ℍ) :
  hφ.sig 1 (φ.matrix * x) = x * φ.matrix :=
  by
  nth_rw 2 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  rw [← sig_apply_posDef_matrix_hMul, PosDef.rpow_one_eq_self]

theorem sig_apply_matrix_hMul_posDef [hφ : φ.IsFaithfulPosMap] (t : ℝ) (x : ℍ) :
    hφ.sig t (x * hφ.matrixIsPosDef.rpow (-t)) = hφ.matrixIsPosDef.rpow (-t) * x :=
  by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, PosDef.rpow_mul_rpow,
    neg_add_cancel, PosDef.rpow_zero, Matrix.mul_one]

theorem sig_apply_matrix_hMul_posDef' [hφ : φ.IsFaithfulPosMap] (x : ℍ) : hφ.sig (-1) (x *
  φ.matrix) = φ.matrix * x :=
  by
  nth_rw 2 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  nth_rw 2 [← neg_neg (1 : ℝ)]
  rw [← sig_apply_matrix_hMul_posDef, neg_neg, PosDef.rpow_one_eq_self]

theorem sig_apply_matrix_hMul_posDef'' [hφ : φ.IsFaithfulPosMap] (x : ℍ) : hφ.sig 1 (x *
  φ.matrix⁻¹) = φ.matrix⁻¹ * x :=
  by
  nth_rw 2 [← PosDef.rpow_neg_one_eq_inv_self hφ.matrixIsPosDef]
  rw [← sig_apply_matrix_hMul_posDef, PosDef.rpow_neg_one_eq_inv_self]

theorem sig_apply_basis [hφ : φ.IsFaithfulPosMap] (i : n × n) :
    hφ.sig 1 (hφ.basis i) =
      φ.matrix⁻¹ * e_{i.1,i.2} * hφ.matrixIsPosDef.rpow (1 / 2) :=
  by
  rw [Module.Dual.IsFaithfulPosMap.basis_apply]
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, PosDef.rpow_mul_rpow,
    PosDef.rpow_neg_one_eq_inv_self]
  norm_num

omit [DecidableEq n] in
theorem Qam.symm'_symm_real_apply_adjoint_tFAE [hφ : φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ) :
    letI : DecidableEq n := Classical.decEq n
    withMatrixQuantum[φ]
      (List.TFAE
        [symmMap ℂ ℍ _ A = A, (symmMap ℂ ℍ _).symm A = A,
          A.real = LinearMap.adjoint A,
          ∀ x y, φ (A x * y) = φ (x * A y)]) :=
by
  classical
  exact withMatrixQuantum[φ] (by
    letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
    suffices φ = Coalgebra.counit by
      simp_rw [this]
      exact symmMap_eq_self_tfae _ rfl
    ext
    simp_rw [← Coalgebra.inner_eq_counit', Module.Dual.IsFaithfulPosMap.inner_eq,
      conjTranspose_one, one_mul])

theorem sig_comp_eq_iff [hφ : φ.IsFaithfulPosMap] (t : ℝ) (A B : ℍ →ₗ[ℂ] ℍ) :
    (hφ.sig t).toLinearMap.comp A = B ↔ A = (hφ.sig (-t)).toLinearMap.comp B :=
by
  rw [AlgEquiv.comp_linearMap_eq_iff, Module.Dual.IsFaithfulPosMap.sig_symm_eq]

theorem stdBasisMatrix_squash (i j k l : n) (x : Matrix n n ℂ) :
    e_{i,j} * x * e_{k,l} = x j k • e_{i,l} := by
  ext i_1 j_1
  simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.stdBasisMatrix, Matrix.single,
    smul_eq_mul, ite_and]
  split_ifs <;> rfl

open scoped ComplexOrder
private theorem nontracial_basis_apply {Q : ℍ} (hQ : Q.PosDef) (i j k l : n) :
    (e_{i,j} * hQ.rpow (-(1 / 2))) k l = ite (i = k) (hQ.rpow (-(1 / 2)) j l) 0 := by
  simp [Matrix.mul_apply, Matrix.stdBasisMatrix, Matrix.single, ite_and]

-- theorem tenSwap_sig [hφ : φ.IsFaithfulPosMap] (x y : ℝ) :
--     (tenSwap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ
--         TensorProduct.map ((hφ.sig x).toLinearMap : l(ℍ)) (sigop hφ y : l(ℍᵐᵒᵖ)) =
--       (((hφ.sig y).toLinearMap : l(ℍ)) ⊗ₘ sigop hφ x : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ tenSwap :=
--   by
--   rw [TensorProduct.ext_iff]
--   intro x y
--   simp only [LinearMap.comp_apply, map_tmul, tenSwap_apply, op_apply, unop_apply,
--     MulOpposite.unop_op, MulOpposite.op_unop]
--   rfl

private theorem Psi.adjoint_rank_one [hφ : φ.IsFaithfulPosMap] (a b : ℍ) (t s : ℝ) :
    withMatrixQuantum[φ]
      (hφ.psi (ψ := φ) t s (LinearMap.adjoint ((|a⟩⟨b|).toLinearMap)) =
        ((hφ.sig (t - s)).toLinearMap ⊗ₘ (hφ.sig (t - s)).op.toLinearMap)
          (tenSwap ℂ (Star.star (hφ.psi (ψ := φ) t s (|a⟩⟨b|).toLinearMap)))) :=
by
  exact withMatrixQuantum[φ] (Psi.adjoint_apply (A := ℍ) (B := ℍ) t s (|a⟩⟨b|).toLinearMap)

-- set_option maxHeartbeats 0 in
-- set_option synthInstance.maxHeartbeats 0 in
-- theorem map_sig_star [hφ : φ.IsFaithfulPosMap] (t s : ℝ) (x : ℍ ⊗[ℂ] ℍᵐᵒᵖ) :
--     star (((hφ.sig t).toLinearMap ⊗ₘ (hφ.sig s).op.toLinearMap) x) =
--       ((hφ.sig (-t)).toLinearMap ⊗ₘ (hφ.sig (-s)).op.toLinearMap) (star x) :=
-- x.induction_on
--   (by simp only [star_zero, map_zero])
--   (fun _ _ =>
--     by simp only [map_tmul, tensor_op_star_apply, Module.Dual.IsFaithfulPosMap.sig_conjTranspose,
--     LinearMap.comp_apply, op_apply, unop_apply, MulOpposite.unop_op, MulOpposite.op_unop,
--     AlgEquiv.toLinearMap_apply, sigop, star_eq_conjTranspose])
--   (fun z w hz hw => by simp only [_root_.map_add, hz, hw, StarAddMonoid.star_add])

theorem map_sig_mulLeft_injective [hφ : φ.IsFaithfulPosMap] (t s : ℝ) :
    Function.Injective
      (LinearMap.mulLeft ℂ
        (hφ.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
          ((op ℂ (A := ℍ)).toLinearMap : ℍ →ₗ[ℂ] ℍᵐᵒᵖ)
            (hφ.matrixIsPosDef.rpow s))) :=
  by
  intro a b h
  have :
    ∀ a,
      a =
        (LinearMap.mulLeft ℂ
            (hφ.matrixIsPosDef.rpow (-t) ⊗ₜ[ℂ]
              ((op ℂ (A := ℍ)).toLinearMap : ℍ →ₗ[ℂ] ℍᵐᵒᵖ)
                (hφ.matrixIsPosDef.rpow (-s))))
          (LinearMap.mulLeft ℂ
            (hφ.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
              ((op ℂ (A := ℍ)).toLinearMap : ℍ →ₗ[ℂ] ℍᵐᵒᵖ)
                (hφ.matrixIsPosDef.rpow s))
            a) :=
    by
    intro a
    simp_rw [← LinearMap.comp_apply, ← LinearMap.mulLeft_mul, Algebra.TensorProduct.tmul_mul_tmul,
      LinearEquiv.coe_coe, op_apply, ← MulOpposite.op_mul, PosDef.rpow_mul_rpow, neg_add_cancel,
      add_neg_cancel, PosDef.rpow_zero, MulOpposite.op_one, ← Algebra.TensorProduct.one_def,
      LinearMap.mulLeft_one, LinearMap.id_apply]
  rw [this a, h, ← this]

theorem map_sig_mulRight_injective [hφ : φ.IsFaithfulPosMap] (t s : ℝ) :
    Function.Injective
      (LinearMap.mulRight ℂ
        (hφ.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
          ((op ℂ (A := ℍ)).toLinearMap : ℍ →ₗ[ℂ] ℍᵐᵒᵖ)
            (hφ.matrixIsPosDef.rpow s))) :=
  by
  intro a b h
  have :
    ∀ a,
      a =
        (LinearMap.mulRight ℂ
            (hφ.matrixIsPosDef.rpow (-t) ⊗ₜ[ℂ]
              ((op ℂ (A := ℍ)).toLinearMap : ℍ →ₗ[ℂ] ℍᵐᵒᵖ)
                (hφ.matrixIsPosDef.rpow (-s))))
          (LinearMap.mulRight ℂ
            (hφ.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
              ((op ℂ (A := ℍ)).toLinearMap : ℍ →ₗ[ℂ] ℍᵐᵒᵖ)
                (hφ.matrixIsPosDef.rpow s))
            a) :=
    by
    intro a
    simp_rw [← LinearMap.comp_apply, ← LinearMap.mulRight_mul, Algebra.TensorProduct.tmul_mul_tmul,
      LinearEquiv.coe_coe, op_apply, ← MulOpposite.op_mul, PosDef.rpow_mul_rpow, neg_add_cancel,
      add_neg_cancel, PosDef.rpow_zero, MulOpposite.op_one, ← Algebra.TensorProduct.one_def,
      LinearMap.mulRight_one, LinearMap.id_apply]
  rw [this a, h, ← this]

theorem LinearMap.matrix.mulRight_adjoint [hφ : φ.IsFaithfulPosMap] (x : ℍ) :
    withMatrixQuantum[φ]
      (LinearMap.adjoint (LinearMap.mulRight ℂ x) =
        LinearMap.mulRight ℂ (hφ.sig (-1) xᴴ)) :=
  by
  exact withMatrixQuantum[φ] (by
    symm
    rw [@LinearMap.eq_adjoint_iff ℂ _]
    intro a b
    simp_rw [LinearMap.mulRight_apply, Module.Dual.IsFaithfulPosMap.sig_apply,
      neg_neg, PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self, ←
      Module.Dual.IsFaithfulPosMap.inner_left_conj])

omit [DecidableEq n] in
theorem LinearMap.matrix.mulLeft_adjoint [hφ : φ.IsFaithfulPosMap] (x : ℍ) :
    letI : DecidableEq n := Classical.decEq n
    withMatrixQuantum[φ]
      (LinearMap.adjoint (LinearMap.mulLeft ℂ x) = LinearMap.mulLeft ℂ xᴴ) :=
  by
  classical
  exact withMatrixQuantum[φ] (by
    symm
    rw [@LinearMap.eq_adjoint_iff ℂ _]
    intro a b
    simp_rw [LinearMap.mulLeft_apply, ←
      Module.Dual.IsFaithfulPosMap.inner_right_hMul])
