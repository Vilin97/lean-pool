/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Components.Gates

/-!
# Bell pair (EPR pair) and its preparation

The Bell state (EPR-pair) `(|00⟩ + |11⟩)/√2` [dW19, qcnotes.tex:622] is
prepared from `|00⟩` by a Hadamard on qubit 0 followed by a CNOT with
control qubit 0:

`CNOT · (H ⊗ I) · |00⟩ = (|00⟩ + |11⟩)/√2`.

This is a `Primitives` module: the Bell pair is a reusable resource state, so
it lives below `Algorithms/` and is shared by the protocols that consume it
(superdense coding, teleportation) without those algorithms importing one
another. The registered `bell-state-prep` target is `bell_state_prep` here.

## Main results

- `LeanPool.LeanQuantumAlg.bell` — the Bell state, as a `PureState 2`.
- `LeanPool.LeanQuantumAlg.BellStatePreparation.main` — the preparation-circuit equality.
- `LeanPool.LeanQuantumAlg.bell_eq_tensor` — the Bell state in per-qubit tensor form.
- `LeanPool.LeanQuantumAlg.norm_bell` — the Bell state is normalized.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- Raw Bell-state vector `( |00⟩ + |11⟩ ) / √2` [dW19, qcnotes.tex:622].
In the big-endian basis labelling, `|00⟩ = ket 0` and `|11⟩ = ket 3`. -/
def bellVec : StateVector 2 :=
  invSqrt2 • ((ket 0 : PureState 2) + (ket 3 : PureState 2) : StateVector 2)

/-- The raw Bell-state vector has unit norm. -/
theorem norm_bellVec : ‖bellVec‖ = 1 := by
  rw [bellVec, norm_smul, norm_invSqrt2]
  have h : ‖((ket 0 : PureState 2) + (ket 3 : PureState 2) : StateVector 2)‖
      = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq]
    have hsum :
        ∑ i, ‖(((ket 0 : PureState 2) + (ket 3 : PureState 2)
          : StateVector 2) i)‖ ^ 2 = 2 := by
      refine (Fin.sum_univ_four (f := fun i : Fin (2 ^ 2) =>
        ‖(((ket 0 : PureState 2) + (ket 3 : PureState 2)
          : StateVector 2) i)‖ ^ 2)).trans ?_
      simp +decide [PureState.ket_apply]
      all_goals norm_num
    rw [hsum]
  rw [h, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))]

/-- The Bell state (EPR-pair) as a normalized pure state. -/
def bell : PureState 2 := ofVec bellVec norm_bellVec

/-- The Bell state in per-qubit tensor form: `(|0⟩⊗|0⟩ + |1⟩⊗|1⟩)/√2`. -/
theorem bell_eq_tensor :
    (bell : StateVector 2)
      = invSqrt2 • ((ket0.tensor ket0 + ket1.tensor ket1 : StateVector 2)) := by
  change bellVec
    = invSqrt2 • ((ket0.tensor ket0 + ket1.tensor ket1 : StateVector 2))
  rw [bellVec, ket0, ket1, PureState.tensor_ket, PureState.tensor_ket]
  change invSqrt2 • ((ket 0 : PureState 2) + (ket 3 : PureState 2) : StateVector 2)
    = invSqrt2 • ((ket 0 : PureState 2) + (ket 3 : PureState 2) : StateVector 2)
  rfl

/-- Bell-state preparation: a Hadamard on qubit 0 followed by a CNOT
(control = qubit 0) turns `|00⟩` into the Bell state. -/
theorem BellStatePreparation.main :
    CNOT.apply ((H.tensor (1 : Gate 1)).apply (ket0.tensor ket0)) = bell := by
  rw [Gate.tensor_apply_tensor, H_apply_ket0, Gate.one_apply]
  ext i
  fin_cases i <;>
    simp +decide [bell, bellVec, ketPlus, ketPlusVec, ket0, ket1,
      PureState.tensor_apply, PureState.ket_apply, Gate.apply_apply, CNOT,
      Gate.ofPerm, Fin.sum_univ_four]

/-- The Bell state is normalized by construction. -/
@[simp]
theorem norm_bell : ‖bell‖ = 1 := bell.norm_eq_one

end

end QuantumAlg
