/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Measurement

/-!
# Named one-qubit kets

The standard one-qubit computational- and Hadamard-basis kets, as named
instances of the generic basis ket `LeanPool.LeanQuantumAlg.PureState.ket`:

`|0>`, `|1>`, `|+> = (|0> + |1>)/sqrt 2`, and
`|-> = (|0> - |1>)/sqrt 2`.

Linear combinations are formed at the raw `StateVector` layer and then bundled
as `PureState` values once their unit norm has been proved.
-/

@[expose] public section

namespace QuantumAlg

namespace PureState

noncomputable section

/-- `|0>`, the first one-qubit basis ket. -/
def ket0 : PureState 1 := ket 0

/-- `|1>`, the second one-qubit basis ket. -/
def ket1 : PureState 1 := ket 1

/-- `(sqrt 2)^-1 : ℂ`, the ubiquitous normalization scalar. -/
def invSqrt2 : ℂ := (Real.sqrt 2 : ℂ)⁻¹

@[simp]
theorem invSqrt2_mul_self : invSqrt2 * invSqrt2 = (2 : ℂ)⁻¹ := by
  rw [invSqrt2, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

@[simp]
theorem invSqrt2_sq : invSqrt2 ^ 2 = (2 : ℂ)⁻¹ := by
  rw [sq, invSqrt2_mul_self]

@[simp]
theorem invSqrt2_mul_mul_invSqrt2 (z : ℂ) :
    invSqrt2 * (z * invSqrt2) = (2 : ℂ)⁻¹ * z := by
  calc
    invSqrt2 * (z * invSqrt2) = z * (invSqrt2 * invSqrt2) := by ring
    _ = z * (2 : ℂ)⁻¹ := by rw [invSqrt2_mul_self]
    _ = (2 : ℂ)⁻¹ * z := by ring

@[simp]
theorem star_invSqrt2 : star invSqrt2 = invSqrt2 := by
  rw [invSqrt2, star_inv₀, Complex.star_def, Complex.conj_ofReal]

@[simp]
theorem norm_invSqrt2 : ‖invSqrt2‖ = (Real.sqrt 2)⁻¹ := by
  rw [invSqrt2, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg 2)]

theorem invSqrt2_ne_zero : invSqrt2 ≠ 0 :=
  inv_ne_zero <| Complex.ofReal_ne_zero.mpr <|
    Real.sqrt_ne_zero'.mpr (by norm_num)

/-- Raw vector for the Hadamard-basis state `|+⟩`. -/
def ketPlusVec : StateVector 1 :=
  invSqrt2 • ((ket0 : StateVector 1) + (ket1 : StateVector 1))

/-- Raw vector for the Hadamard-basis state `|-⟩`. -/
def ketMinusVec : StateVector 1 :=
  invSqrt2 • ((ket0 : StateVector 1) - (ket1 : StateVector 1))

@[simp]
theorem ketPlusVec_apply (i : Fin (2 ^ 1)) :
    ketPlusVec i = invSqrt2 := by
  fin_cases i <;>
    simp [ketPlusVec, ket0, ket1, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]

@[simp]
theorem ketMinusVec_apply (i : Fin (2 ^ 1)) :
    ketMinusVec i = if i = 0 then invSqrt2 else -invSqrt2 := by
  fin_cases i <;>
    simp [ketMinusVec, ket0, ket1, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]

theorem norm_sq_invSqrt2 : ‖invSqrt2‖ ^ 2 = 2⁻¹ := by
  rw [norm_invSqrt2, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Norm over `Fin (2 ^ 1)` as a two-term sum. -/
theorem norm_eq_two_terms (psi : StateVector 1) :
    ‖psi‖ = √(‖psi 0‖ ^ 2 + ‖psi 1‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  exact Fin.sum_univ_two (f := fun i : Fin (2 ^ 1) => ‖psi i‖ ^ 2)

theorem norm_ketPlusVec : ‖ketPlusVec‖ = 1 := by
  rw [norm_eq_two_terms, ketPlusVec_apply, ketPlusVec_apply, ← two_mul,
    norm_sq_invSqrt2]
  norm_num

theorem norm_ketMinusVec : ‖ketMinusVec‖ = 1 := by
  rw [norm_eq_two_terms, ketMinusVec_apply, ketMinusVec_apply, if_pos rfl,
    if_neg (show (1 : Fin (2 ^ 1)) ≠ 0 by decide), norm_neg, ← two_mul,
    norm_sq_invSqrt2]
  norm_num

/-- `|+> = (|0> + |1>)/sqrt 2`. -/
def ketPlus : PureState 1 := ofVec ketPlusVec norm_ketPlusVec

/-- `|-> = (|0> - |1>)/sqrt 2`. -/
def ketMinus : PureState 1 := ofVec ketMinusVec norm_ketMinusVec

@[simp]
theorem ketPlus_apply (i : Fin (2 ^ 1)) : ketPlus i = invSqrt2 := by
  change ketPlusVec i = invSqrt2
  rw [ketPlusVec_apply]

@[simp]
theorem ketMinus_apply (i : Fin (2 ^ 1)) :
    ketMinus i = if i = 0 then invSqrt2 else -invSqrt2 := by
  change ketMinusVec i = if i = 0 then invSqrt2 else -invSqrt2
  rw [ketMinusVec_apply]

@[simp]
theorem norm_ketPlus : ‖ketPlus‖ = 1 := by
  exact ketPlus.norm_eq_one

@[simp]
theorem norm_ketMinus : ‖ketMinus‖ = 1 := by
  exact ketMinus.norm_eq_one

/-- Workhorse for test circuits: on `|0> ⊗ alpha + |1> ⊗ beta` the probability
of reading `0` on qubit 0 is `‖alpha‖^2`. -/
theorem probQubit0_ket0_tensor_add_ket1_tensor {n : ℕ}
    (alpha beta : StateVector n) :
    StateVector.probQubit0
        (StateVector.tensor (ket0 : StateVector 1) alpha
          + StateVector.tensor (ket1 : StateVector 1) beta) 0
      = ‖alpha‖ ^ 2 := by
  rw [StateVector.probQubit0, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖alpha i‖)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PiLp.add_apply, StateVector.tensor_apply_prod, StateVector.tensor_apply_prod,
    ket0, ket1, ket_apply, ket_apply, if_pos rfl,
    if_neg (show (0 : Fin (2 ^ 1)) ≠ 1 by decide), one_mul, zero_mul,
    add_zero]

/-- On `|0> ⊗ alpha + |1> ⊗ beta` the probability of reading `1` on qubit 0 is
`‖beta‖^2`. -/
theorem probQubit1_ket0_tensor_add_ket1_tensor {n : ℕ}
    (alpha beta : StateVector n) :
    StateVector.probQubit0
        (StateVector.tensor (ket0 : StateVector 1) alpha
          + StateVector.tensor (ket1 : StateVector 1) beta) 1
      = ‖beta‖ ^ 2 := by
  rw [StateVector.probQubit0, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖beta i‖)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PiLp.add_apply, StateVector.tensor_apply_prod, StateVector.tensor_apply_prod,
    ket0, ket1, ket_apply, ket_apply, if_pos rfl,
    if_neg (show (1 : Fin (2 ^ 1)) ≠ 0 by decide), one_mul, zero_mul,
    zero_add]

end

end PureState

end QuantumAlg
