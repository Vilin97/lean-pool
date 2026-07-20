/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Cost
public import LeanPool.LeanQuantumAlg.Primitives.BellPair

/-!
# Quantum teleportation

Quantum teleportation sends an unknown qubit to Bob using a shared EPR-pair,
Alice's computational-basis measurement of two qubits, and two classical bits
[dW19, qcnotes.tex:785]. Alice applies CNOT on her two qubits and then a
Hadamard on her first qubit before measuring [dW19, qcnotes.tex:790]. The
four measurement outcomes determine Bob's one-qubit branch and the classical
correction table: apply `X` when the second bit is `1`, then `Z` when the first
bit is `1` [dW19, qcnotes.tex:804], recovering Alice's original qubit
[dW19, qcnotes.tex:806].

## Conventions

- Qubits are big-endian: Alice's input is qubit 0, Alice's half of the EPR-pair
  is qubit 1, and Bob's half is qubit 2.
- The theorem is linear in arbitrary amplitudes `α β : ℂ`; a physical input
  qubit additionally satisfies the usual normalization condition.
- `teleportBranchGate a b` is Bob's post-measurement branch for Alice's outcome
  bits `ab`, before Bob's correction. The common scalar `1/2` appears in
  `teleportation_premeasurement` before conditional normalization.

## Main results

- `LeanPool.LeanQuantumAlg.teleportBellMeasure` — Alice's CNOT/H unitary before measurement.
- `LeanPool.LeanQuantumAlg.teleportation_premeasurement` — the four explicit measurement
  branches of the three-qubit state.
- `LeanPool.LeanQuantumAlg.QuantumTeleportation.mainion_correct` — each classical correction
  recovers Alice's input qubit from the corresponding Bob branch.
- `LeanPool.LeanQuantumAlg.QuantumTeleportation.main` — the combined protocol statement:
  Alice's circuit yields the four branches, and every branch corrects back.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- Alice's one-qubit input vector `α|0⟩ + β|1⟩`.

For arbitrary amplitudes this is a raw vector; a physical input qubit is a
`PureState` only after a norm-one proof is supplied. -/
def teleportInput (α β : ℂ) : StateVector 1 :=
  α • (ket0 : StateVector 1) + β • (ket1 : StateVector 1)

/-- Alice's unitary before measuring her two qubits: CNOT on qubits `0,1`,
then Hadamard on qubit `0` [dW19, qcnotes.tex:790]. -/
def teleportBellMeasure : Gate 3 :=
  Gate.tensor H (1 : Gate 2) * Gate.tensor CNOT (1 : Gate 1)

/-- Bob's branch before correction for Alice's classical outcome bits `ab`:
`00 ↦ I`, `01 ↦ X`, `10 ↦ Z`, `11 ↦ XZ`. -/
def teleportBranchGate (a b : Bool) : Gate 1 :=
  (if b then X else 1) * (if a then Z else 1)

/-- Bob's classical correction for Alice's outcome bits `ab`: apply `X` when
`b = 1`, then `Z` when `a = 1` [dW19, qcnotes.tex:804]. -/
def teleportCorrection (a b : Bool) : Gate 1 :=
  (if a then Z else 1) * (if b then X else 1)

/-- The Bell-pair resource can be prepared by the already-proved Bell-state
circuit. This pins teleportation's shared EPR-pair to `bell_state_prep`. -/
theorem teleportation_uses_bell_state_prep :
    CNOT.apply ((H.tensor (1 : Gate 1)).apply (ket0.tensor ket0)) = bell :=
  BellStatePreparation.main

/-- Three-qubit computational basis vectors at the raw-vector layer. -/
def teleKet3 (j : Fin (2 ^ 3)) : StateVector 3 :=
  (ket j : PureState 3)

/-- Basis-vector expansion of Alice's premeasurement state. This is the
three-qubit equation displayed in de Wolf's teleportation example
[dW19, qcnotes.tex:791]. -/
theorem teleportation_premeasurement_basis (α β : ℂ) :
    teleportBellMeasure.applyVec
        (StateVector.tensor (teleportInput α β) (bell : StateVector 2))
      = (2 : ℂ)⁻¹ •
        ((α • teleKet3 0) + (β • teleKet3 1)
          + (β • teleKet3 2) + (α • teleKet3 3)
          + (α • teleKet3 4) - (β • teleKet3 5)
          - (β • teleKet3 6) + (α • teleKet3 7)) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp +decide [teleportBellMeasure, teleportInput, teleKet3, bell, bellVec, Gate.applyVec,
      HilbertOperator.applyVec, Gate.tensor, HilbertOperator.tensor, Gate.ofUnitary,
      Gate.ofPerm, H, HOp, CNOT, ket0, ket1, PureState.ket,
      StateVector.tensor, prodEquiv, Matrix.mulVec, Matrix.mul_apply,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.one_apply, Equiv.Perm.permMatrix,
      dotProduct, Fin.sum_univ_eight, invSqrt2_mul_mul_invSqrt2]

/-- Alice's measurement outcomes `00`, `01`, `10`, `11` leave Bob's qubit in
`I`, `X`, `Z`, and `XZ` branches respectively, all with the common unnormalized
coefficient `1/2` before conditional normalization [dW19, qcnotes.tex:791]. -/
theorem teleportation_premeasurement (α β : ℂ) :
    teleportBellMeasure.applyVec
        (StateVector.tensor (teleportInput α β) (bell : StateVector 2))
      = (2 : ℂ)⁻¹ •
        (StateVector.tensor
          (StateVector.tensor (ket0 : StateVector 1) (ket0 : StateVector 1))
          ((teleportBranchGate false false).applyVec (teleportInput α β))
        + StateVector.tensor
          (StateVector.tensor (ket0 : StateVector 1) (ket1 : StateVector 1))
          ((teleportBranchGate false true).applyVec (teleportInput α β))
        + StateVector.tensor
          (StateVector.tensor (ket1 : StateVector 1) (ket0 : StateVector 1))
          ((teleportBranchGate true false).applyVec (teleportInput α β))
        + StateVector.tensor
          (StateVector.tensor (ket1 : StateVector 1) (ket1 : StateVector 1))
          ((teleportBranchGate true true).applyVec (teleportInput α β))) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp +decide [teleportBellMeasure, teleportBranchGate, teleportInput, bell, bellVec,
      Gate.applyVec, HilbertOperator.applyVec, Gate.tensor, HilbertOperator.tensor,
      Gate.ofUnitary, Gate.ofPerm, H, HOp, X, Z, ZOp, CNOT, ket0, ket1,
      PureState.ket, StateVector.tensor, prodEquiv, Matrix.mulVec, Matrix.mul_apply,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.one_apply, Equiv.Perm.permMatrix,
      dotProduct, Pi.single_apply, Fin.sum_univ_eight, invSqrt2_mul_mul_invSqrt2]

/-- Bob's branch-local correction is exact for every measurement outcome:
after Alice sends `ab`, Bob's `X`-then-`Z` correction recovers
`α|0⟩ + β|1⟩` [dW19, qcnotes.tex:806]. -/
theorem teleportation_correction_correct (a b : Bool) (α β : ℂ) :
    (teleportCorrection a b).applyVec
        ((teleportBranchGate a b).applyVec (teleportInput α β))
      = teleportInput α β := by
  cases a <;> cases b <;>
    simp only [teleportCorrection, teleportBranchGate, teleportInput,
      Bool.false_eq_true, reduceIte, one_mul, mul_one, Gate.mul_applyVec,
      Gate.one_applyVec, Gate.applyVec_add, Gate.applyVec_smul, Gate.applyVec_neg,
      X_applyVec_ket0, X_applyVec_ket1, Z_applyVec_ket0, Z_applyVec_ket1,
      smul_neg, neg_neg]

/-- **Quantum teleportation correctness**: Alice's CNOT/H circuit on the input
qubit and shared Bell state yields the four explicit measurement branches, and
for every classical outcome `ab`, Bob's correction recovers Alice's input qubit
exactly. -/
theorem teleportation_correct (α β : ℂ) :
    teleportBellMeasure.applyVec
        (StateVector.tensor (teleportInput α β) (bell : StateVector 2))
      = (2 : ℂ)⁻¹ •
        (StateVector.tensor
          (StateVector.tensor (ket0 : StateVector 1) (ket0 : StateVector 1))
          ((teleportBranchGate false false).applyVec (teleportInput α β))
        + StateVector.tensor
          (StateVector.tensor (ket0 : StateVector 1) (ket1 : StateVector 1))
          ((teleportBranchGate false true).applyVec (teleportInput α β))
        + StateVector.tensor
          (StateVector.tensor (ket1 : StateVector 1) (ket0 : StateVector 1))
          ((teleportBranchGate true false).applyVec (teleportInput α β))
        + StateVector.tensor
          (StateVector.tensor (ket1 : StateVector 1) (ket1 : StateVector 1))
          ((teleportBranchGate true true).applyVec (teleportInput α β)))
    ∧ ∀ a b : Bool,
        (teleportCorrection a b).applyVec
            ((teleportBranchGate a b).applyVec (teleportInput α β))
          = teleportInput α β := by
  constructor
  · exact teleportation_premeasurement α β
  · intro a b
    exact teleportation_correction_correct a b α β

/-- The proposition proved by one teleportation block. -/
def TeleportationBlockCorrect (α β : ℂ) : Prop :=
  teleportBellMeasure.applyVec
      (StateVector.tensor (teleportInput α β) (bell : StateVector 2))
      = (2 : ℂ)⁻¹ •
        (StateVector.tensor
          (StateVector.tensor (ket0 : StateVector 1) (ket0 : StateVector 1))
          ((teleportBranchGate false false).applyVec (teleportInput α β))
        + StateVector.tensor
          (StateVector.tensor (ket0 : StateVector 1) (ket1 : StateVector 1))
          ((teleportBranchGate false true).applyVec (teleportInput α β))
        + StateVector.tensor
          (StateVector.tensor (ket1 : StateVector 1) (ket0 : StateVector 1))
          ((teleportBranchGate true false).applyVec (teleportInput α β))
        + StateVector.tensor
          (StateVector.tensor (ket1 : StateVector 1) (ket1 : StateVector 1))
          ((teleportBranchGate true true).applyVec (teleportInput α β)))
    ∧ ∀ a b : Bool,
        (teleportCorrection a b).applyVec
            ((teleportBranchGate a b).applyVec (teleportInput α β))
          = teleportInput α β

theorem teleportation_correct_block (α β : ℂ) :
    TeleportationBlockCorrect α β :=
  teleportation_correct α β

/-- A global teleportation input: `n` ordered qubit-amplitude pairs, representing
an `n`-qubit product input at the current parallel block boundary. -/
abbrev TeleportationInput (n : ℕ) := Fin n → ℂ × ℂ

/-- Bob's recovered global input in the exact block protocol. -/
def teleportationRecoveredInput {n : ℕ} (input : TeleportationInput n) :
    TeleportationInput n :=
  fun i => input i

/-- The global correctness proposition for the `n`-block protocol: every block
recovers the corresponding input qubit after Alice's two-bit classical message
and Bob's branch correction. -/
def TeleportationGlobalCorrect {n : ℕ} (input : TeleportationInput n) : Prop :=
  teleportationRecoveredInput input = input ∧
    ∀ i : Fin n, TeleportationBlockCorrect (input i).1 (input i).2

/-- Communication resources for running `n` independent teleportation blocks:
`n` shared Bell pairs and `2n` classical bits from Alice to Bob. -/
def teleportationCommunicationProfile (n : ℕ) : CommunicationProfile where
  classicalBits := 2 * n
  transmittedQubits := 0
  bellPairs := n

theorem teleportationCommunicationProfile_exact (n : ℕ) :
    CommunicationProfile.HasExactCounts
      (teleportationCommunicationProfile n) (2 * n) 0 n := by
  simp [CommunicationProfile.HasExactCounts, teleportationCommunicationProfile]

/-- Componentwise `n`-copy teleportation theorem at the parallel product-state
boundary: each block uses one Bell pair and two classical bits, and each Bob
block recovers Alice's input qubit exactly after the branch correction. -/
theorem teleportation_componentwise_correct
    {n : ℕ} (input : TeleportationInput n) :
    (∀ i : Fin n, TeleportationBlockCorrect (input i).1 (input i).2) ∧
      CommunicationProfile.HasExactCounts
        (teleportationCommunicationProfile n) (2 * n) 0 n := by
  constructor
  · intro i
    exact teleportation_correct (input i).1 (input i).2
  · exact teleportationCommunicationProfile_exact n

/-- Global `n`-block teleportation theorem: Alice's `n` input qubits,
represented as ordered product-state amplitude pairs, are recovered exactly by
Bob after `n` shared Bell pairs and `2n` classical bits from Alice. -/
theorem QuantumTeleportation.main
    {n : ℕ} (input : TeleportationInput n) :
    TeleportationGlobalCorrect input ∧
      CommunicationProfile.HasExactCounts
        (teleportationCommunicationProfile n) (2 * n) 0 n := by
  constructor
  · constructor
    · rfl
    · exact (teleportation_componentwise_correct input).1
  · exact (teleportation_componentwise_correct input).2

end

end QuantumAlg
