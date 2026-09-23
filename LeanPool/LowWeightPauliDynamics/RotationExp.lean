/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import Mathlib.Topology.Instances.Matrix
public import LeanPool.LowWeightPauliDynamics.Rotation
public import LeanPool.LowWeightPauliDynamics.Pauli.Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Closed-form Pauli rotations are genuine matrix exponentials

`apd:eq:pauli_rotation_branch` is stated for the exponential gates `e^{±i G dt/2}`, whereas
`rot` (`Rotation.lean`) is an algebraic closed form. This file proves that the two are equal,
using Mathlib's `NormedSpace.exp` rather than a separate exponential definition, and restates
both branches of the rule with genuine exponentials.

Even powers of an involution are `1`, odd powers are the generator. The exponential series
therefore splits into the convergent complex cosine and sine series. This needs only a
Hausdorff topological complex algebra with continuous scalar multiplication: no particular
norm, completeness hypothesis, spectral theorem, or matrix-norm convention is required.
The concrete Pauli corollary uses the matrices' ordinary product topology.

The sign is positive and the angle is halved: `rot G θ = exp ((I * (θ/2)) • G)`.
Thus the paper's negative-exponent gate `e^{-i G θ/2}` is `rot G (-θ)`. The Pauli corollaries
are about the entrywise matrix model `PauliString.toMatrix`; that this model is the tensor
product of one-qubit Pauli matrices is a separate statement, proved in `Pauli/Tensor.lean`.

## Main results

* `exp_smul_I_of_involution`: `exp ((I * z) • G) = cos z • 1 + (I * sin z) • G` for `G * G = 1`
  and any complex `z`.
* `rot_eq_exp`, `rot_neg_eq_exp`: `rot G (±θ) = exp ((±I * (θ/2)) • G)` for `G * G = 1`.
* `exp_conj_of_commute`, `exp_conj_of_anticommute`: the two branches of
  `apd:eq:pauli_rotation_branch` with genuine exponentials.
* `PauliString.rot_toMatrix_eq_exp`, `PauliString.rot_toMatrix_neg_eq_exp`: the same identities
  for the matrix of a Hermitian Pauli string.
-/

@[expose] public section

namespace Lean4LPD

open scoped Nat

section TopologicalAlgebra

variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A}

/-- The even terms of the exponential series of `(z * I) • G` are scalar multiples of `1` when
`G * G = 1`: they are the terms of the cosine series of `z`. -/
theorem exp_term_even_of_involution (hG : G * G = 1) (z : ℂ) (n : ℕ) :
    ((2 * n)!⁻¹ : ℂ) • ((z * Complex.I) • G) ^ (2 * n) =
      ((z * Complex.I) ^ (2 * n) / (2 * n)!) • (1 : A) := by
  have hp : G ^ (2 * n) = 1 := by rw [pow_mul, pow_two, hG, one_pow]
  rw [smul_pow, hp, smul_smul]
  congr 1
  ring

/-- The odd terms of the exponential series of `(z * I) • G` are scalar multiples of `G` when
`G * G = 1`: they are `I` times the terms of the sine series of `z`. There is no division by the
angle, so the zero-angle case needs no separate argument. -/
theorem exp_term_odd_of_involution (hG : G * G = 1) (z : ℂ) (n : ℕ) :
    ((2 * n + 1)!⁻¹ : ℂ) • ((z * Complex.I) • G) ^ (2 * n + 1) =
      (((z * Complex.I) ^ (2 * n + 1) / (2 * n + 1)! / Complex.I) * Complex.I) • G := by
  have hp : G ^ (2 * n + 1) = G := by
    rw [pow_succ, pow_mul, pow_two, hG, one_pow, one_mul]
  rw [smul_pow, hp, smul_smul, div_mul_cancel₀ _ Complex.I_ne_zero]
  congr 1
  ring

variable [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℂ A] [T2Space A]

/-- **The exponential of an involution**, for a complex angle `z`: if `G * G = 1` then
`exp ((I * z) • G) = cos z • 1 + (I * sin z) • G`. This is the gate identity underlying
`apd:eq:pauli_rotation_branch`, proved by summing the even and odd subsequences of Mathlib's
exponential series (`HasSum.even_add_odd`). -/
theorem exp_smul_I_of_involution (hG : G * G = 1) (z : ℂ) :
    NormedSpace.exp ((Complex.I * z) • G) =
      Complex.cos z • (1 : A) + (Complex.I * Complex.sin z) • G := by
  have hc := (Complex.hasSum_cos' z).smul_const (1 : A)
  have hs := ((Complex.hasSum_sin' z).mul_right Complex.I).smul_const G
  have hsum : HasSum (fun n : ℕ => (n !⁻¹ : ℂ) • ((z * Complex.I) • G) ^ n)
      (Complex.cos z • (1 : A) + (Complex.sin z * Complex.I) • G) := by
    refine HasSum.even_add_odd ?_ ?_
    · convert hc using 1
      ext n
      exact exp_term_even_of_involution hG z n
    · convert hs using 1
      ext n
      exact exp_term_odd_of_involution hG z n
  rw [mul_comm Complex.I z, NormedSpace.exp_eq_tsum ℂ, mul_comm Complex.I (Complex.sin z)]
  exact hsum.tsum_eq

/-- **The closed-form rotation is the genuine exponential gate**: for `G * G = 1`,
`rot G θ = exp ((I * (θ/2)) • G)`. The sign is positive and the angle is halved, which is the
factor standing on the left of the Heisenberg conjugation in `apd:eq:pauli_rotation_branch`. -/
theorem rot_eq_exp (hG : G * G = 1) (θ : ℝ) :
    rot G θ = NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • G) := by
  rw [exp_smul_I_of_involution hG, rot, Complex.ofReal_cos, Complex.ofReal_sin]

/-- The negative-exponent gate `e^{-i G θ/2}` of `apd:eq:pauli_rotation_branch` is the
negative-angle rotation `rot G (-θ)`, not `rot G θ`. -/
theorem rot_neg_eq_exp (hG : G * G = 1) (θ : ℝ) :
    rot G (-θ) = NormedSpace.exp ((-Complex.I * (θ / 2 : ℝ)) • G) := by
  simpa only [neg_div, Complex.ofReal_neg, mul_neg, neg_mul] using rot_eq_exp hG (-θ)

/-- The commuting branch of `apd:eq:pauli_rotation_branch`, stated with genuine exponentials
rather than the algebraic closed form: if `G * G = 1` and `G` commutes with `P`, conjugation by
`e^{i G θ/2}` leaves `P` unchanged. This is `rot_conj_of_commute` transported along
`rot_eq_exp`. -/
theorem exp_conj_of_commute (hG : G * G = 1) (h : Commute G P) (θ : ℝ) :
    NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • G) * P *
      NormedSpace.exp ((-Complex.I * (θ / 2 : ℝ)) • G) = P := by
  rw [← rot_eq_exp hG θ, ← rot_neg_eq_exp hG θ]
  exact rot_conj_of_commute hG h

/-- The anticommuting branch of `apd:eq:pauli_rotation_branch`, stated with genuine
exponentials: if `G * G = 1` and `G * P = -(P * G)`, conjugation by `e^{i G θ/2}` sends `P` to
`cos θ • P + (I * sin θ) • (G * P)`. The conjugation angle is `θ`, not `θ/2`, and the partner is
`G * P`. This is `rot_conj_of_anticommute` transported along `rot_eq_exp`. -/
theorem exp_conj_of_anticommute (hG : G * G = 1) (h : G * P = -(P * G)) (θ : ℝ) :
    NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • G) * P *
      NormedSpace.exp ((-Complex.I * (θ / 2 : ℝ)) • G) =
      (Real.cos θ : ℂ) • P + (Complex.I * Real.sin θ) • (G * P) := by
  rw [← rot_eq_exp hG θ, ← rot_neg_eq_exp hG θ]
  exact rot_conj_of_anticommute hG h

end TopologicalAlgebra

namespace PauliString

variable {n : ℕ} {G : PauliString n}

/-- For every Hermitian Pauli string `G`, the closed-form rotation of its matrix is the genuine
matrix exponential `exp ((I * (θ/2)) • toMatrix G)`, the gate of
`apd:eq:pauli_rotation_branch`, in the entrywise `toMatrix` model. The product topology on
finite matrices supplies all analytic instances without choosing a norm. -/
theorem rot_toMatrix_eq_exp (hG : IsSelfAdjoint G) (θ : ℝ) :
    rot (toMatrix G) θ =
      NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • toMatrix G) :=
  rot_eq_exp (toMatrix_mul_self_of_isSelfAdjoint hG) θ

/-- The negative-angle rotation of a Hermitian Pauli matrix is the exponential with the negative
sign, `exp ((-I * (θ/2)) • toMatrix G)`: the factor standing on the right of the conjugation in
`apd:eq:pauli_rotation_branch`. -/
theorem rot_toMatrix_neg_eq_exp (hG : IsSelfAdjoint G) (θ : ℝ) :
    rot (toMatrix G) (-θ) =
      NormedSpace.exp ((-Complex.I * (θ / 2 : ℝ)) • toMatrix G) :=
  rot_neg_eq_exp (toMatrix_mul_self_of_isSelfAdjoint hG) θ

end PauliString
end Lean4LPD
