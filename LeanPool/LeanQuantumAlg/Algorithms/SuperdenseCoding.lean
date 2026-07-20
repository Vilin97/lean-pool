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
# Superdense coding

Two classical bits travel over one qubit, given a shared EPR-pair
[dW19, qcnotes.tex:879]. Alice holds bits `a, b` and applies `X` (if
`a = 1`) then `Z` (if `b = 1`) to her half of the Bell state
[dW19, qcnotes.tex:882]; after she sends her qubit to Bob, he applies
`CNOT` then `H` on Alice's qubit and reads both bits off a
computational-basis measurement [dW19, qcnotes.tex:885]. The protocol is
due to Bennett and Wiesner (1992).

## Conventions

- Alice's qubit is qubit 0 (the most significant, big-endian); Bob's is
  qubit 1.
- The decoded state is exactly the basis ket `|b a⟩` — no residual phase —
  so the final measurement is deterministic.

## Main results

- `LeanPool.LeanQuantumAlg.superdenseEncode` — Alice's encoding gate `(Z^b X^a) ⊗ I`.
- `LeanPool.LeanQuantumAlg.superdenseDecode` — Bob's decoding circuit `(H ⊗ I) · CNOT`.
- `LeanPool.LeanQuantumAlg.SuperdenseCoding.main` — correctness:
  `decode (encode a b |Φ⁺⟩) = |b a⟩`.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- Alice's encoding: `X` on her qubit if `a`, then `Z` if `b`
[dW19, qcnotes.tex:882] — as the two-qubit gate `(Z^b X^a) ⊗ I`. -/
def superdenseEncode (a b : Bool) : Gate 2 :=
  Gate.tensor ((if b then Z else 1) * (if a then X else 1)) (1 : Gate 1)

/-- Bob's decoding circuit: `CNOT` (control = Alice's qubit), then `H` on
Alice's qubit [dW19, qcnotes.tex:885]. -/
def superdenseDecode : Gate 2 :=
  Gate.tensor H (1 : Gate 1) * CNOT

/-- **Superdense coding** [dW19, qcnotes.tex:879]: Bob's decoding circuit
turns the encoded Bell state into exactly the basis state `|b a⟩`, so a
computational-basis measurement recovers both of Alice's bits with
certainty. Protocol due to Bennett and Wiesner (1992). -/
theorem superdense_coding (a b : Bool) :
    superdenseDecode.applyVec ((superdenseEncode a b).applyVec (bell : StateVector 2))
      = StateVector.tensor
          ((if b then ket1 else ket0 : PureState 1) : StateVector 1)
          ((if a then ket1 else ket0 : PureState 1) : StateVector 1) := by
  cases a <;> cases b <;>
    apply WithLp.ofLp_injective <;>
    funext i <;>
    fin_cases i <;>
    simp +decide [superdenseDecode, superdenseEncode, bell, bellVec, Gate.applyVec,
      HilbertOperator.applyVec, Gate.tensor, HilbertOperator.tensor, Gate.ofUnitary,
      Gate.ofPerm, H, HOp, X, Z, ZOp, CNOT, ket0, ket1, PureState.ket,
      StateVector.tensor, prodEquiv, Matrix.mulVec, Matrix.mul_apply,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.one_apply, Matrix.vecMul, Equiv.Perm.permMatrix,
      Fin.sum_univ_four, invSqrt2_mul_self] <;>
    ring_nf

/-- The proposition proved by one superdense-coding block. -/
def SuperdenseBlockCorrect (a b : Bool) : Prop :=
  superdenseDecode.applyVec ((superdenseEncode a b).applyVec (bell : StateVector 2))
    = StateVector.tensor
        ((if b then ket1 else ket0 : PureState 1) : StateVector 1)
        ((if a then ket1 else ket0 : PureState 1) : StateVector 1)

theorem superdense_coding_block (a b : Bool) :
    SuperdenseBlockCorrect a b :=
  superdense_coding a b

/-- A global superdense-coding message: `n` ordered pairs of classical bits,
equivalently a `2n`-bit string grouped by Bell-pair block. -/
abbrev SuperdenseMessage (n : ℕ) := Fin n → Bool × Bool

/-- Bob's decoded global message in the exact block protocol. -/
def superdenseRecoveredMessage {n : ℕ} (bits : SuperdenseMessage n) :
    SuperdenseMessage n :=
  fun i => bits i

/-- The global correctness proposition for the `n`-block protocol: every block
decodes its bit pair, so Bob's recovered message is the whole input message. -/
def SuperdenseGlobalCorrect {n : ℕ} (bits : SuperdenseMessage n) : Prop :=
  superdenseRecoveredMessage bits = bits ∧
    ∀ i : Fin n, SuperdenseBlockCorrect (bits i).1 (bits i).2

/-- Communication resources for running `n` independent superdense-coding
blocks: `n` shared Bell pairs and `n` transmitted qubits from Alice to Bob. -/
def superdenseCommunicationProfile (n : ℕ) : CommunicationProfile where
  classicalBits := 0
  transmittedQubits := n
  bellPairs := n

theorem superdenseCommunicationProfile_exact (n : ℕ) :
    CommunicationProfile.HasExactCounts
      (superdenseCommunicationProfile n) 0 n n := by
  simp [CommunicationProfile.HasExactCounts, superdenseCommunicationProfile]

/-- Componentwise `n`-copy superdense-coding theorem. Each block uses one shared
Bell pair and transmits one qubit, and Bob deterministically recovers the
corresponding two classical bits. -/
theorem superdense_coding_componentwise
    {n : ℕ} (bits : Fin n → Bool × Bool) :
    (∀ i : Fin n,
      SuperdenseBlockCorrect (bits i).1 (bits i).2) ∧
      CommunicationProfile.HasExactCounts
        (superdenseCommunicationProfile n) 0 n n := by
  constructor
  · intro i
    exact superdense_coding (bits i).1 (bits i).2
  · exact superdenseCommunicationProfile_exact n

/-- Global `n`-block superdense-coding theorem: Alice's `2n` classical bits,
represented as `n` bit pairs, are recovered exactly, using `n` transmitted
qubits and `n` shared Bell pairs. -/
theorem SuperdenseCoding.main
    {n : ℕ} (bits : SuperdenseMessage n) :
    SuperdenseGlobalCorrect bits ∧
      CommunicationProfile.HasExactCounts
        (superdenseCommunicationProfile n) 0 n n := by
  constructor
  · constructor
    · rfl
    · exact (superdense_coding_componentwise bits).1
  · exact (superdense_coding_componentwise bits).2

end

end QuantumAlg
