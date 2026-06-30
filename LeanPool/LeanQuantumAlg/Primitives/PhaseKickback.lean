/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Components.Control
public import LeanPool.LeanQuantumAlg.Core.Components.Oracle

/-!
# Phase kickback

Querying the XOR oracle of `f` with the target qubit in `|−⟩` leaves the
target untouched and kicks the value of `f` back into the phase of the
input register [dW19, qcnotes.tex:1167]:

`U_f (|x⟩ ⊗ |−⟩) = (−1)^{f(x)} · (|x⟩ ⊗ |−⟩)`,

the "phase kick-back trick" [dW19, qcnotes.tex:1173]. Dually, a `|+⟩`
target is left invariant, which lets circuits choose per-branch whether a
phase query happens [dW19, qcnotes.tex:1173].

The eigenvalue form replaces the oracle by a controlled unitary: if the
target register holds an eigenstate `|u⟩` of `U`, the eigenvalue `e^{iθ}`
is "kicked back" in front of the `|1⟩` component of the control
[CEMM98, cemm6.tex:163].

## Main results

- `LeanPool.LeanQuantumAlg.phase_kickback` —
  `U_f (|x⟩ ⊗ |−⟩) = (−1)^{f(x)} (|x⟩ ⊗ |−⟩)`,
  with the sign written as `if f x then -1 else 1`.
- `LeanPool.LeanQuantumAlg.xorOracle_apply_tensor_ketPlus` —
  `U_f (|x⟩ ⊗ |+⟩) = |x⟩ ⊗ |+⟩`.
- `LeanPool.LeanQuantumAlg.eigenvalue_phase_kickback` —
  `c-U ((a|0⟩ + b|1⟩) ⊗ |u⟩) = (a|0⟩ + e^{iθ} b|1⟩) ⊗ |u⟩` when
  `U |u⟩ = e^{iθ} |u⟩`.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

variable {n : ℕ}

/-- **Phase kickback**: on a `|−⟩` target the XOR oracle acts as the phase
oracle `|x⟩ ↦ (−1)^{f(x)} |x⟩`; the sign `(−1)^{f(x)}` is written
`if f x then -1 else 1`. -/
theorem PhaseKickback.main (f : Fin (2 ^ n) → Bool) (x : Fin (2 ^ n)) :
    ((Gate.xorOracle f).apply ((ket x).tensor ketMinus) : StateVector (n + 1))
      = (if f x then (-1 : ℂ) else 1)
          • (((ket x).tensor ketMinus : PureState (n + 1)) : StateVector (n + 1)) := by
  apply WithLp.ofLp_injective
  funext i
  rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨y, b⟩, rfl⟩
  rw [Gate.xorOracle_apply]
  simp only [Equiv.symm_apply_apply, Gate.xorPerm_apply]
  by_cases hy : y = x
  · subst y
    by_cases h : f x
    · fin_cases b <;>
        simp [h, ketMinus_apply]
    · simp [h, ketMinus_apply]
  · by_cases hx : f x <;> by_cases h : f y <;> fin_cases b <;>
      simp [hx, h, hy, PureState.ket_apply]


/-- On a `|+⟩` target the XOR oracle acts trivially, whatever `f` is. -/
theorem xorOracle_apply_tensor_ketPlus (f : Fin (2 ^ n) → Bool)
    (x : Fin (2 ^ n)) :
    (Gate.xorOracle f).apply ((ket x).tensor ketPlus)
      = (ket x).tensor ketPlus := by
  ext i
  rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨y, b⟩, rfl⟩
  rw [Gate.xorOracle_apply, PureState.tensor_apply_prod, PureState.tensor_apply_prod]
  simp only [Equiv.symm_apply_apply, Gate.xorPerm_apply]
  by_cases hy : y = x
  · subst y
    by_cases h : f x <;> fin_cases b <;> simp [h, ketPlus_apply]
  · by_cases h : f y <;> fin_cases b <;>
      simp [h, hy, PureState.ket_apply]

/-- **Eigenvalue phase kickback** [CEMM98, cemm6.tex:163]: if the target
register holds an eigenstate `|u⟩` of `U` with eigenvalue `e^{iθ}`, the
controlled `U` leaves the target unchanged and kicks the eigenvalue back
onto the `|1⟩` component of the control [CEMM98, cemm6.tex:142]:

`c-U ((a|0⟩ + b|1⟩) ⊗ |u⟩) = (a|0⟩ + e^{iθ} b|1⟩) ⊗ |u⟩`. -/
theorem GeneralizedPhaseKickback.main (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.applyVec (u : StateVector n) =
      Complex.exp (θ * Complex.I) • (u : StateVector n)) (a b : ℂ) :
    (Gate.controlled U).applyVec
        (StateVector.tensor
          ((a • ket0 + b • ket1 : StateVector 1)) (u : StateVector n))
      =
      StateVector.tensor
        ((a • ket0 + (Complex.exp (θ * Complex.I) * b) • ket1 : StateVector 1))
        (u : StateVector n) := by
  rw [StateVector.add_tensor, StateVector.smul_tensor, StateVector.smul_tensor,
    Gate.applyVec_add, Gate.applyVec_smul, Gate.applyVec_smul]
  simp only [Gate.applyVec, Gate.controlled_applyVec_ket0_tensor,
    Gate.controlled_applyVec_ket1_tensor]
  rw [StateVector.add_tensor, StateVector.smul_tensor, StateVector.smul_tensor]
  change a • StateVector.tensor (ket0 : StateVector 1) (u : StateVector n)
      + b • StateVector.tensor (ket1 : StateVector 1) (U.applyVec (u : StateVector n))
    =
    a • StateVector.tensor (ket0 : StateVector 1) (u : StateVector n)
      + (Complex.exp (θ * Complex.I) * b)
          • StateVector.tensor (ket1 : StateVector 1) (u : StateVector n)
  rw [hu, StateVector.tensor_smul, smul_smul]
  module


end

end QuantumAlg
