/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Components.Gates

/-!
# GHZ state preparation

The three-qubit GHZ state `(|000⟩ + |111⟩)/√2`, prepared from `|000⟩` by a
Hadamard on qubit 0 followed by a CNOT cascade:

`(I ⊗ CNOT) · (CNOT ⊗ I) · (H ⊗ I ⊗ I) · |000⟩ = (|000⟩ + |111⟩)/√2`.

States of this multipartite family are due to Greenberger, Horne and
Zeilinger (1989), whose original argument uses a four-particle spin state
(reprinted as arXiv:0712.0921). The three-qubit form and the name "GHZ
state" are standard textbook material (e.g. Nielsen and Chuang 2000). In
[dW19] the unnormalized states `|000⟩ ± |111⟩` appear as
the code blocks of Shor's 9-qubit code [dW19, qcnotes.tex:7456], and a
locally-equivalent three-qubit state powers Mermin's game
[dW19, qcnotes.tex:6667].

## Conventions

- Big-endian basis labelling as in `Core/State.lean`: `|000⟩ = ket 0` and
  `|111⟩ = ket 7`.
- Qubit 0 carries the Hadamard and controls the first CNOT (target
  qubit 1); qubit 1 controls the second CNOT (target qubit 2).
- The circuit factors use the qubit groupings `1+2`, `2+1`, `1+2`; the
  index types all reduce to `Fin (2^3)` definitionally.

## Main results

- `LeanPool.LeanQuantumAlg.ghz` — the three-qubit GHZ state, as a `PureState 3`.
- `LeanPool.LeanQuantumAlg.ghzCircuit` — the preparation circuit, as a `Gate 3`.
- `LeanPool.LeanQuantumAlg.ghz_state_prep` — the preparation-circuit equality.
- `LeanPool.LeanQuantumAlg.norm_ghz` — the GHZ state is normalized.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- The three-qubit GHZ state `(|000⟩ + |111⟩)/√2` (Greenberger, Horne and
Zeilinger 1989; three-qubit form standard, e.g. Nielsen and Chuang 2000).
In the big-endian basis labelling, `|000⟩ = ket 0` and `|111⟩ = ket 7`. -/
def ghzVec : StateVector 3 :=
  invSqrt2 • ((ket 0 : PureState 3) + (ket 7 : PureState 3) : StateVector 3)

/-- The raw GHZ vector has unit norm. -/
theorem norm_ghzVec : ‖ghzVec‖ = 1 := by
  rw [ghzVec, norm_smul, norm_invSqrt2]
  have h : ‖((ket 0 : PureState 3) + (ket 7 : PureState 3) : StateVector 3)‖
      = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ i,
        ‖(((ket 0 : PureState 3) + (ket 7 : PureState 3) : StateVector 3) i)‖ ^ 2 = 2 := by
      refine (Fin.sum_univ_eight (f := fun i : Fin (2 ^ 3) =>
        ‖(((ket 0 : PureState 3) + (ket 7 : PureState 3) : StateVector 3) i)‖ ^ 2)).trans ?_
      simp +decide [PureState.ket_apply]
      all_goals norm_num
    rw [hsum]
  rw [h, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))]

/-- The normalized GHZ state. -/
def ghz : PureState 3 := PureState.ofVec ghzVec norm_ghzVec

/-- The GHZ preparation circuit: a Hadamard on qubit 0, a CNOT with
control 0 and target 1, then a CNOT with control 1 and target 2 —
`(I ⊗ CNOT) · (CNOT ⊗ I) · (H ⊗ I ⊗ I)`. -/
def ghzCircuit : Gate 3 :=
  Gate.tensor (1 : Gate 1) CNOT
    * (Gate.tensor CNOT (1 : Gate 1) * Gate.tensor H (1 : Gate 2))

/-- **GHZ state preparation**: the cascade circuit turns `|000⟩` into the
GHZ state, extending Bell-state preparation (`bell_state_prep`) by one
CNOT. -/
theorem GHZStatePreparation.main :
    ghzCircuit.applyVec
        (StateVector.tensor (ket0 : StateVector 1)
          (StateVector.tensor (ket0 : StateVector 1) (ket0 : StateVector 1)))
      = (ghz : StateVector 3) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp +decide [ghzCircuit, ghz, ghzVec, Gate.applyVec, HilbertOperator.applyVec,
      Gate.tensor, HilbertOperator.tensor, Gate.ofUnitary, Gate.ofPerm, H, HOp,
      CNOT, ket0, PureState.ket, StateVector.tensor, prodEquiv,
      Matrix.mulVec, Matrix.mul_apply, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.one_apply, Equiv.Perm.permMatrix, dotProduct, Fin.sum_univ_eight]


/-- The GHZ state is normalized. -/
@[simp]
theorem norm_ghz : ‖ghz‖ = 1 := ghz.norm_eq_one

end

end QuantumAlg
