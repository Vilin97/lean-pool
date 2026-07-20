/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Components.Gates

/-!
# Controlled gates

`Gate.controlled U` is the `(1 + n)`-qubit gate that applies the `n`-qubit
gate `U` on the target register exactly when the control qubit is in `|1>`,
and does nothing when it is in `|0>` [CEMM98, cemm6.tex:127]. As a matrix it
is the block decomposition `c-U = |0><0| ⊗ 1 + |1><1| ⊗ U`.

The projectors `proj0` and `proj1` are `HilbertOperator`s, not gates.
-/

@[expose] public section

namespace QuantumAlg

namespace Gate

open PureState

noncomputable section

variable {n : ℕ}

/-- The one-qubit projector `|0><0| = [[1, 0], [0, 0]]`. -/
def proj0 : HilbertOperator 1 := !![(1 : ℂ), 0; 0, 0]

/-- The one-qubit projector `|1><1| = [[0, 0], [0, 1]]`. -/
def proj1 : HilbertOperator 1 := !![(0 : ℂ), 0; 0, 1]

@[simp]
theorem proj0_conjTranspose : proj0.conjTranspose = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.conjTranspose_apply]

@[simp]
theorem proj1_conjTranspose : proj1.conjTranspose = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.conjTranspose_apply]

theorem proj0_mul_proj0 : proj0 * proj0 = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.mul_apply]

theorem proj0_mul_proj1 : proj0 * proj1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.mul_apply]

theorem proj1_mul_proj0 : proj1 * proj0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.mul_apply]

theorem proj1_mul_proj1 : proj1 * proj1 = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.mul_apply]

theorem proj0_add_proj1 : proj0 + proj1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, Matrix.add_apply]

@[simp]
theorem proj0_applyVec_ket0 :
    HilbertOperator.applyVec proj0 (ket0 : StateVector 1) = (ket0 : StateVector 1) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [HilbertOperator.applyVec, proj0, ket0, PureState.ket]

@[simp]
theorem proj0_applyVec_ket1 :
    HilbertOperator.applyVec proj0 (ket1 : StateVector 1) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [HilbertOperator.applyVec, proj0, ket1, PureState.ket]

@[simp]
theorem proj1_applyVec_ket0 :
    HilbertOperator.applyVec proj1 (ket0 : StateVector 1) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [HilbertOperator.applyVec, proj1, ket0, PureState.ket]

@[simp]
theorem proj1_applyVec_ket1 :
    HilbertOperator.applyVec proj1 (ket1 : StateVector 1) = (ket1 : StateVector 1) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [HilbertOperator.applyVec, proj1, ket1, PureState.ket]

/-- Raw controlled-operator matrix. -/
def controlledOp (U : Gate n) : HilbertOperator (1 + n) :=
  HilbertOperator.tensor proj0 (1 : HilbertOperator n)
    + HilbertOperator.tensor proj1 (U : HilbertOperator n)

/-- The controlled gate `c-U`. -/
def controlled (U : Gate n) : Gate (1 + n) :=
  ofUnitary (controlledOp U) (by
    have hU : (U : HilbertOperator n) * (U : HilbertOperator n).conjTranspose = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.mp U.unitary
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    rw [controlledOp, Matrix.conjTranspose_add, HilbertOperator.conjTranspose_tensor,
      HilbertOperator.conjTranspose_tensor, proj0_conjTranspose, proj1_conjTranspose,
      Matrix.conjTranspose_one, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
      HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor, hU]
    simp only [Matrix.one_mul, Matrix.mul_one, proj0_mul_proj0, proj0_mul_proj1,
      proj1_mul_proj0, proj1_mul_proj1, HilbertOperator.zero_tensor,
      zero_add, add_zero]
    rw [← HilbertOperator.add_tensor, proj0_add_proj1, HilbertOperator.one_tensor_one])

/-- On the `|0>` control branch `c-U` does nothing. -/
@[simp]
theorem controlled_applyVec_ket0_tensor (U : Gate n) (psi : StateVector n) :
    HilbertOperator.applyVec (controlled U : HilbertOperator (1 + n))
        (StateVector.tensor (ket0 : StateVector 1) psi)
      = StateVector.tensor (ket0 : StateVector 1) psi := by
  apply WithLp.ofLp_injective
  funext i
  change HilbertOperator.applyVec (controlledOp U)
        (StateVector.tensor (ket0 : StateVector 1) psi) i
      = StateVector.tensor (ket0 : StateVector 1) psi i
  rw [controlledOp, HilbertOperator.add_applyVec, HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.tensor_applyVec_tensor, proj0_applyVec_ket0, proj1_applyVec_ket0,
    HilbertOperator.one_applyVec, StateVector.zero_tensor, PiLp.add_apply]
  simp

/-- On the `|1>` control branch `c-U` applies `U`. -/
@[simp]
theorem controlled_applyVec_ket1_tensor (U : Gate n) (psi : StateVector n) :
    HilbertOperator.applyVec (controlled U : HilbertOperator (1 + n))
        (StateVector.tensor (ket1 : StateVector 1) psi)
      = StateVector.tensor (ket1 : StateVector 1) (U.applyVec psi) := by
  apply WithLp.ofLp_injective
  funext i
  change HilbertOperator.applyVec (controlledOp U)
        (StateVector.tensor (ket1 : StateVector 1) psi) i
      = StateVector.tensor (ket1 : StateVector 1)
        (HilbertOperator.applyVec (U : HilbertOperator n) psi) i
  rw [controlledOp, HilbertOperator.add_applyVec, HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.tensor_applyVec_tensor, proj0_applyVec_ket1, proj1_applyVec_ket1,
    StateVector.zero_tensor, PiLp.add_apply]
  simp

/-- On the `|0>` control branch `c-U` does nothing. -/
@[simp]
theorem controlled_apply_ket0_tensor (U : Gate n) (psi : PureState n) :
    (controlled U).apply (ket0.tensor psi) = ket0.tensor psi := by
  ext i
  change HilbertOperator.applyVec (controlled U : HilbertOperator (1 + n))
        (StateVector.tensor (ket0 : StateVector 1) (psi : StateVector n)) i
      = StateVector.tensor (ket0 : StateVector 1) (psi : StateVector n) i
  rw [controlled_applyVec_ket0_tensor]

/-- On the `|1>` control branch `c-U` applies `U`. -/
@[simp]
theorem controlled_apply_ket1_tensor (U : Gate n) (psi : PureState n) :
    (controlled U).apply (ket1.tensor psi) = ket1.tensor (U.apply psi) := by
  ext i
  change HilbertOperator.applyVec (controlled U : HilbertOperator (1 + n))
        (StateVector.tensor (ket1 : StateVector 1) (psi : StateVector n)) i
      = StateVector.tensor (ket1 : StateVector 1)
        (U.applyVec (psi : StateVector n)) i
  rw [controlled_applyVec_ket1_tensor]

/-- `c-U` is unitary. -/
theorem controlled_mem_unitaryGroup {U : Gate n}
    (_hU : (U : HilbertOperator n) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    (controlled U : HilbertOperator (1 + n))
      ∈ Matrix.unitaryGroup (Fin (2 ^ (1 + n))) ℂ :=
  (controlled U).unitary

/-- Sanity check: the controlled Pauli-X gate is exactly `CNOT`. -/
theorem controlled_X : controlled X = CNOT := by
  have hX : ∀ i j : Fin (2 ^ 1), (X : HilbertOperator 1) i j
      = if i = Equiv.swap 0 1 j then 1 else 0 := by
    intro i j
    rw [← apply_ket X j i, X, ofPerm_apply_ket, Equiv.swap_inv, PureState.ket_apply]
  have hC : ∀ i j : Fin (2 ^ 2), CNOT i j
      = if i = Equiv.swap 2 3 j then 1 else 0 := by
    intro i j
    rw [← apply_ket CNOT j i, CNOT_apply_ket, PureState.ket_apply]
  ext i j
  change controlledOp X i j = CNOT i j
  rw [hC]
  fin_cases i <;> fin_cases j <;>
    simp +decide [controlledOp, HilbertOperator.tensor_apply, proj0, proj1,
      hX, Matrix.one_apply, prodEquiv, finProdFinEquiv, finCongr,
      Fin.divNat, Fin.modNat]

end

end Gate

end QuantumAlg
