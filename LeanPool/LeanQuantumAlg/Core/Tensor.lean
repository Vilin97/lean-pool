/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Gate
public import LeanPool.LeanQuantumAlg.Util.FinPow
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Tensor products of vectors, states, operators, and gates

Raw tensor products are defined at the `StateVector` and `HilbertOperator`
layers. `PureState.tensor` and `Gate.tensor` wrap these raw tensors with the
normalization/unitarity proofs needed to stay in their semantic types.
-/

@[expose] public section

namespace QuantumAlg

open Kronecker

variable {m n : ℕ}

namespace StateVector

section

/-- Tensor product of raw Hilbert-space vectors. -/
noncomputable def tensor (ψ : StateVector m) (φ : StateVector n) : StateVector (m + n) :=
  WithLp.toLp 2 fun i => ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2

@[simp]
theorem tensor_apply (ψ : StateVector m) (φ : StateVector n)
    (i : Fin (2 ^ (m + n))) :
    tensor ψ φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 :=
  rfl

theorem tensor_apply_prod (ψ : StateVector m) (φ : StateVector n)
    (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    tensor ψ φ (prodEquiv (x, y)) = ψ x * φ y := by
  rw [tensor_apply, Equiv.symm_apply_apply]

@[simp]
theorem add_tensor (ψ ψ' : StateVector m) (φ : StateVector n) :
    tensor (ψ + ψ') φ = tensor ψ φ + tensor ψ' φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (ψ + ψ') φ i = (tensor ψ φ + tensor ψ' φ) i
  simp [add_mul]

@[simp]
theorem sub_tensor (ψ ψ' : StateVector m) (φ : StateVector n) :
    tensor (ψ - ψ') φ = tensor ψ φ - tensor ψ' φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (ψ - ψ') φ i = (tensor ψ φ - tensor ψ' φ) i
  simp [sub_mul]

@[simp]
theorem smul_tensor (c : ℂ) (ψ : StateVector m) (φ : StateVector n) :
    tensor (c • ψ) φ = c • tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (c • ψ) φ i = (c • tensor ψ φ) i
  simp [mul_assoc]

@[simp]
theorem tensor_add (ψ : StateVector m) (φ φ' : StateVector n) :
    tensor ψ (φ + φ') = tensor ψ φ + tensor ψ φ' := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (φ + φ') i = (tensor ψ φ + tensor ψ φ') i
  simp [mul_add]

@[simp]
theorem tensor_sub (ψ : StateVector m) (φ φ' : StateVector n) :
    tensor ψ (φ - φ') = tensor ψ φ - tensor ψ φ' := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (φ - φ') i = (tensor ψ φ - tensor ψ φ') i
  simp [mul_sub]

@[simp]
theorem tensor_smul (c : ℂ) (ψ : StateVector m) (φ : StateVector n) :
    tensor ψ (c • φ) = c • tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (c • φ) i = (c • tensor ψ φ) i
  simp [mul_left_comm]

@[simp]
theorem neg_tensor (ψ : StateVector m) (φ : StateVector n) :
    tensor (-ψ) φ = -tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (-ψ) φ i = (-tensor ψ φ) i
  simp [tensor_apply]

@[simp]
theorem tensor_neg (ψ : StateVector m) (φ : StateVector n) :
    tensor ψ (-φ) = -tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (-φ) i = (-tensor ψ φ) i
  simp [tensor_apply]

@[simp]
theorem zero_tensor (φ : StateVector n) :
    tensor (0 : StateVector m) φ = 0 := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (0 : StateVector m) φ i = (0 : StateVector (m + n)) i
  simp [tensor_apply]

@[simp]
theorem tensor_zero (ψ : StateVector m) :
    tensor ψ (0 : StateVector n) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (0 : StateVector n) i = (0 : StateVector (m + n)) i
  simp [tensor_apply]

/-- The norm is multiplicative under tensor products. -/
theorem norm_tensor (ψ : StateVector m) (φ : StateVector n) :
    ‖tensor ψ φ‖ = ‖ψ‖ * ‖φ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (show (0 : ℝ) ≤ ∑ i, ‖ψ i‖ ^ 2 from
      Finset.sum_nonneg fun i _ => sq_nonneg ‖ψ i‖)]
  congr 1
  rw [← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun i => ‖tensor ψ φ i‖ ^ 2),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, Equiv.symm_apply_apply, norm_mul, mul_pow]

/-- The inner product factors over tensor products. -/
theorem inner_tensor_tensor (ψ ψ' : StateVector m) (φ φ' : StateVector n) :
    inner ℂ (tensor ψ φ) (tensor ψ' φ')
      = inner ℂ ψ ψ' * inner ℂ φ φ' := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun i => tensor ψ' φ' i * starRingEnd ℂ (tensor ψ φ i)),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, tensor_apply, Equiv.symm_apply_apply, map_mul,
    mul_mul_mul_comm]

end

end StateVector

namespace PureState

section

/-- Tensor product of pure states. -/
noncomputable def tensor (ψ : PureState m) (φ : PureState n) : PureState (m + n) :=
  ofVec (StateVector.tensor (ψ : StateVector m) (φ : StateVector n)) (by
    rw [StateVector.norm_tensor, ψ.norm_eq_one, φ.norm_eq_one, one_mul])

@[simp]
theorem tensor_apply (ψ : PureState m) (φ : PureState n)
    (i : Fin (2 ^ (m + n))) :
    ψ.tensor φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 := by
  change StateVector.tensor (ψ : StateVector m) (φ : StateVector n) i
      = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2
  rfl

theorem tensor_apply_prod (ψ : PureState m) (φ : PureState n)
    (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    ψ.tensor φ (prodEquiv (x, y)) = ψ x * φ y := by
  rw [tensor_apply, Equiv.symm_apply_apply]

-- Compatibility names for linear raw-vector tensor proofs.
theorem add_tensor (ψ ψ' : StateVector m) (φ : StateVector n) :
    StateVector.tensor (ψ + ψ') φ = StateVector.tensor ψ φ + StateVector.tensor ψ' φ :=
  StateVector.add_tensor ψ ψ' φ

theorem sub_tensor (ψ ψ' : StateVector m) (φ : StateVector n) :
    StateVector.tensor (ψ - ψ') φ = StateVector.tensor ψ φ - StateVector.tensor ψ' φ :=
  StateVector.sub_tensor ψ ψ' φ

theorem smul_tensor (c : ℂ) (ψ : StateVector m) (φ : StateVector n) :
    StateVector.tensor (c • ψ) φ = c • StateVector.tensor ψ φ :=
  StateVector.smul_tensor c ψ φ

theorem tensor_add (ψ : StateVector m) (φ φ' : StateVector n) :
    StateVector.tensor ψ (φ + φ') = StateVector.tensor ψ φ + StateVector.tensor ψ φ' :=
  StateVector.tensor_add ψ φ φ'

theorem tensor_sub (ψ : StateVector m) (φ φ' : StateVector n) :
    StateVector.tensor ψ (φ - φ') = StateVector.tensor ψ φ - StateVector.tensor ψ φ' :=
  StateVector.tensor_sub ψ φ φ'

theorem tensor_smul (c : ℂ) (ψ : StateVector m) (φ : StateVector n) :
    StateVector.tensor ψ (c • φ) = c • StateVector.tensor ψ φ :=
  StateVector.tensor_smul c ψ φ

theorem neg_tensor (ψ : StateVector m) (φ : StateVector n) :
    StateVector.tensor (-ψ) φ = -StateVector.tensor ψ φ :=
  StateVector.neg_tensor ψ φ

theorem tensor_neg (ψ : StateVector m) (φ : StateVector n) :
    StateVector.tensor ψ (-φ) = -StateVector.tensor ψ φ :=
  StateVector.tensor_neg ψ φ

theorem zero_tensor (φ : StateVector n) :
    StateVector.tensor (0 : StateVector m) φ = 0 :=
  StateVector.zero_tensor φ

theorem tensor_zero (ψ : StateVector m) :
    StateVector.tensor ψ (0 : StateVector n) = 0 :=
  StateVector.tensor_zero ψ

/-- Basis kets tensor to basis kets: `|x⟩ ⊗ |y⟩ = |xy⟩`. -/
theorem tensor_ket (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    (ket x).tensor (ket y) = ket (prodEquiv (x, y)) := by
  ext i
  rw [tensor_apply, ket_apply, ket_apply, ket_apply]
  by_cases h : i = prodEquiv (x, y)
  · rw [if_pos h, if_pos (by rw [h, Equiv.symm_apply_apply]),
      if_pos (by rw [h, Equiv.symm_apply_apply]), one_mul]
  · have h' : ¬((prodEquiv.symm i).1 = x ∧ (prodEquiv.symm i).2 = y) := by
      rintro ⟨h1, h2⟩
      exact h (by
        rw [← Equiv.apply_symm_apply (prodEquiv (m := m) (n := n)) i]
        exact congrArg prodEquiv (Prod.ext h1 h2))
    rw [if_neg h]
    rcases not_and_or.mp h' with h1 | h2
    · rw [if_neg h1, zero_mul]
    · rw [if_neg h2, mul_zero]

theorem norm_tensor (ψ : PureState m) (φ : PureState n) :
    ‖ψ.tensor φ‖ = ‖ψ‖ * ‖φ‖ := by
  change ‖StateVector.tensor (ψ : StateVector m) (φ : StateVector n)‖
      = ‖(ψ : StateVector m)‖ * ‖(φ : StateVector n)‖
  rw [StateVector.norm_tensor]

theorem inner_tensor_tensor (ψ ψ' : PureState m) (φ φ' : PureState n) :
    inner ℂ (ψ.tensor φ) (ψ'.tensor φ')
      = inner ℂ ψ ψ' * inner ℂ φ φ' := by
  change inner ℂ
      (StateVector.tensor (ψ : StateVector m) (φ : StateVector n))
      (StateVector.tensor (ψ' : StateVector m) (φ' : StateVector n))
    = inner ℂ (ψ : StateVector m) (ψ' : StateVector m)
      * inner ℂ (φ : StateVector n) (φ' : StateVector n)
  rw [StateVector.inner_tensor_tensor]

end

end PureState

namespace HilbertOperator

section

/-- Tensor product of Hilbert-space operators. -/
noncomputable def tensor
    (G : HilbertOperator m) (K : HilbertOperator n) : HilbertOperator (m + n) :=
  Matrix.reindex prodEquiv prodEquiv (G ⊗ₖ K)

@[simp]
theorem tensor_apply (G : HilbertOperator m) (K : HilbertOperator n)
    (i j : Fin (2 ^ (m + n))) :
    tensor G K i j
      = G (prodEquiv.symm i).1 (prodEquiv.symm j).1
        * K (prodEquiv.symm i).2 (prodEquiv.symm j).2 := rfl

@[simp]
theorem zero_tensor (K : HilbertOperator n) :
    tensor (0 : HilbertOperator m) K = 0 := by
  ext i j
  simp [tensor_apply]

@[simp]
theorem tensor_zero (G : HilbertOperator m) :
    tensor G (0 : HilbertOperator n) = 0 := by
  ext i j
  simp [tensor_apply]

theorem add_tensor (G G' : HilbertOperator m) (K : HilbertOperator n) :
    tensor (G + G') K = tensor G K + tensor G' K := by
  ext i j
  simp [tensor_apply, add_mul]

theorem tensor_add (G : HilbertOperator m) (K K' : HilbertOperator n) :
    tensor G (K + K') = tensor G K + tensor G K' := by
  ext i j
  simp [tensor_apply, mul_add]

theorem tensor_mul_tensor (G G' : HilbertOperator m) (K K' : HilbertOperator n) :
    tensor G K * tensor G' K' = tensor (G * G') (K * K') := by
  rw [tensor, tensor, tensor, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul]

theorem conjTranspose_tensor (G : HilbertOperator m) (K : HilbertOperator n) :
    (tensor G K).conjTranspose = tensor G.conjTranspose K.conjTranspose := by
  rw [tensor, tensor, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]

@[simp]
theorem one_tensor_one : tensor (1 : HilbertOperator m) (1 : HilbertOperator n) = 1 := by
  rw [tensor, Matrix.one_kronecker_one, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv]

theorem tensor_mem_unitaryGroup {G : HilbertOperator m} {K : HilbertOperator n}
    (hG : G ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ)
    (hK : K ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    tensor G K ∈ Matrix.unitaryGroup (Fin (2 ^ (m + n))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hG hK ⊢
  rw [tensor, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul, hG, hK, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

theorem tensor_applyVec_tensor (G : HilbertOperator m) (K : HilbertOperator n)
    (ψ : StateVector m) (φ : StateVector n) :
    applyVec (tensor G K) (StateVector.tensor ψ φ)
      = StateVector.tensor (applyVec G ψ) (applyVec K φ) := by
  apply WithLp.ofLp_injective
  funext i
  change applyVec (tensor G K) (StateVector.tensor ψ φ) i
      = StateVector.tensor (applyVec G ψ) (applyVec K φ) i
  rw [StateVector.tensor_apply, applyVec_apply, applyVec_apply, applyVec_apply,
    Finset.sum_mul_sum,
    ← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun j => tensor G K i j * StateVector.tensor ψ φ j),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, StateVector.tensor_apply, Equiv.symm_apply_apply,
    mul_mul_mul_comm]

end

end HilbertOperator

namespace Gate

noncomputable section

/-- Tensor product of unitary gates. -/
def tensor (G : Gate m) (K : Gate n) : Gate (m + n) :=
  ofUnitary (HilbertOperator.tensor (G : HilbertOperator m) (K : HilbertOperator n))
    (HilbertOperator.tensor_mem_unitaryGroup G.unitary K.unitary)

@[simp]
theorem tensor_apply (G : Gate m) (K : Gate n)
    (i j : Fin (2 ^ (m + n))) :
    G.tensor K i j
      = G (prodEquiv.symm i).1 (prodEquiv.symm j).1
        * K (prodEquiv.symm i).2 (prodEquiv.symm j).2 := rfl

theorem tensor_mul_tensor (G G' : Gate m) (K K' : Gate n) :
    G.tensor K * G'.tensor K' = tensor (G * G') (K * K') := by
  ext i j
  change (HilbertOperator.tensor (G : HilbertOperator m) (K : HilbertOperator n)
        * HilbertOperator.tensor (G' : HilbertOperator m) (K' : HilbertOperator n)) i j
      = HilbertOperator.tensor ((G : HilbertOperator m) * (G' : HilbertOperator m))
          ((K : HilbertOperator n) * (K' : HilbertOperator n)) i j
  rw [HilbertOperator.tensor_mul_tensor]

theorem conjTranspose_tensor (G : Gate m) (K : Gate n) :
    (G.tensor K).conjTranspose = tensor G.conjTranspose K.conjTranspose := by
  ext i j
  change (HilbertOperator.tensor (G : HilbertOperator m) (K : HilbertOperator n)).conjTranspose i j
      = HilbertOperator.tensor ((G : HilbertOperator m).conjTranspose)
          ((K : HilbertOperator n).conjTranspose) i j
  rw [HilbertOperator.conjTranspose_tensor]

@[simp]
theorem one_tensor_one : (1 : Gate m).tensor (1 : Gate n) = 1 := by
  ext i j
  change HilbertOperator.tensor (1 : HilbertOperator m) (1 : HilbertOperator n) i j
      = (1 : HilbertOperator (m + n)) i j
  rw [HilbertOperator.one_tensor_one]

theorem tensor_mem_unitaryGroup {G : Gate m} {K : Gate n}
    (_hG : (G : HilbertOperator m) ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ)
    (_hK : (K : HilbertOperator n) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    (G.tensor K : HilbertOperator (m + n))
      ∈ Matrix.unitaryGroup (Fin (2 ^ (m + n))) ℂ :=
  (G.tensor K).unitary

theorem tensor_apply_tensor (G : Gate m) (K : Gate n)
    (ψ : PureState m) (φ : PureState n) :
    (G.tensor K).apply (ψ.tensor φ) = (G.apply ψ).tensor (K.apply φ) := by
  ext i
  change HilbertOperator.applyVec
      (HilbertOperator.tensor (G : HilbertOperator m) (K : HilbertOperator n))
      (StateVector.tensor (ψ : StateVector m) (φ : StateVector n)) i
    = StateVector.tensor
      (HilbertOperator.applyVec (G : HilbertOperator m) (ψ : StateVector m))
      (HilbertOperator.applyVec (K : HilbertOperator n) (φ : StateVector n)) i
  rw [HilbertOperator.tensor_applyVec_tensor]

theorem tensor_applyVec_tensor (G : Gate m) (K : Gate n)
    (ψ : StateVector m) (φ : StateVector n) :
    (G.tensor K).applyVec (StateVector.tensor ψ φ)
      = StateVector.tensor (G.applyVec ψ) (K.applyVec φ) := by
  exact HilbertOperator.tensor_applyVec_tensor (G : HilbertOperator m)
    (K : HilbertOperator n) ψ φ

end

end Gate

end QuantumAlg
