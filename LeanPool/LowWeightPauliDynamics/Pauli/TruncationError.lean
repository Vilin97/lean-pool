/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Pauli.TrotterTruncate

/-!
# Telescoping of the truncation error and the Pauli-norm triangle bound

This file formalizes the norm-level part of `apd:thm:triangle` for the step-boundary truncation
of `TrotterTruncate.lean`. The difference between the untruncated evolution and the LPD output
after `r` Trotter steps telescopes into the discarded operators `X_{d+1}`
(`apd:eq:step_component`), each evolved through the remaining whole steps
(`trotterStep_telescoping`). Conjugation by rotations with Hermitian Pauli generators preserves
`pauliNorm`, so Minkowski's inequality in coefficient space bounds the error by the sum of the
Pauli norms of the discarded operators (`pauliNorm_trotterStep_error_le`).

## Main definitions

* `blockEnd Gs θ period`: one untruncated block of `period` rotations as an additive endomorphism
  of matrices; its `r`-th power is the untruncated evolution through `r` steps.

## Main results

* `pauliNorm_add_le`, `pauliNorm_sum_le`: Minkowski's inequality for the Pauli 2-norm.
* `trotterStep_telescoping`, `periodic_traj_sub_trotterStepTraj`: the operator telescope, in
  terms of `blockEnd` and in terms of the rotation-indexed `traj`.
* `blockEnd_pow_eq_periodic_traj`: powers of `blockEnd` are `traj` of the rotations repeated
  modulo `period`.
* `pauliNorm_trotterStep_error_le`, `pauliNorm_periodic_traj_error_le`,
  `pauliNorm_trotterTraj_error_le`, `pauliNorm_trotterStep_error_le_highNorm`: the Pauli-norm
  triangle bound, for the three descriptions of the two trajectories and with the discarded
  norms written as high-weight norms.

## Scope

`pauliNorm` is the normalized Hilbert–Schmidt (Pauli 2-) norm, not the matrix operator norm. The
telescope needs no Hermiticity, locality, small-angle or entanglement hypothesis; the norm bound
needs only Hermitian generators. The step of `apd:thm:triangle` that passes from Pauli norms to
expectation values in a state, where the entanglement of the evolved state enters, is not
formalized. The quantitative bound on the sum of the discarded norms is in `LayerError.lean`.
-/

public section

namespace Lean4LPD
namespace PauliString

open Finset

variable {n : ℕ}

/-- Coefficients are additive, the coefficient-space helper for the triangle inequality in
`apd:thm:triangle`. -/
theorem coeff_add (A B : Matrix (Bits n) (Bits n) ℂ) (p : PauliIndex n) :
    coeff (A + B) p = coeff A p + coeff B p := by
  rw [coeff, coeff, coeff, Matrix.mul_add, Matrix.trace_add, mul_add]

/-- Coefficient vectors preserve addition, allowing the Pauli-norm form of the triangle step
in `apd:thm:triangle` without choosing a norm instance on matrices. -/
theorem coeffVec_add (A B : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (A + B) = coeffVec A + coeffVec B := by
  ext p
  change coeff (A + B) p = coeff A p + coeff B p
  exact coeff_add A B p

/-- Zero contributes no error to the sum in `apd:thm:triangle`. -/
@[simp] theorem pauliNorm_zero : pauliNorm (0 : Matrix (Bits n) (Bits n) ℂ) = 0 := by
  rw [← norm_coeffVec]
  have hzero : coeffVec (0 : Matrix (Bits n) (Bits n) ℂ) = 0 := by
    ext p
    simp [coeffVec, coeff]
  rw [hzero, norm_zero]

/-- Minkowski's inequality for the Pauli 2-norm, used on the operator telescope of
`apd:thm:triangle`. This is an inequality for the `ℓ²` norm of the coefficient vector, not for
the matrix operator norm. -/
theorem pauliNorm_add_le (A B : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (A + B) ≤ pauliNorm A + pauliNorm B := by
  simpa only [← norm_coeffVec, coeffVec_add] using norm_add_le (coeffVec A) (coeffVec B)

/-- Finite-sum Minkowski for the normalized Pauli norm, the norm-level triangle step associated
with the operator telescope in `apd:thm:triangle`. -/
theorem pauliNorm_sum_le {ι : Type*} (S : Finset ι)
    (A : ι → Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (∑ i ∈ S, A i) ≤ ∑ i ∈ S, pauliNorm (A i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact (pauliNorm_add_le _ _).trans (add_le_add le_rfl ih)

/-- A block's untruncated evolution is additive. This is the linearity used by the telescope
in `apd:thm:triangle`; the generators need not be Hermitian here. -/
theorem traj_add (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (A B : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    traj Gs θ (A + B) g = traj Gs θ A g + traj Gs θ B g := by
  induction g with
  | zero => rfl
  | succ g ih => simp only [traj_succ, ih, Matrix.mul_add, Matrix.add_mul]

/-- Zero remains zero under a whole untruncated block, the additive-map helper for
`apd:thm:triangle`. -/
theorem traj_zero_input (Gs : ℕ → PauliString n) (θ : ℕ → ℝ) (g : ℕ) :
    traj Gs θ (0 : Matrix (Bits n) (Bits n) ℂ) g = 0 := by
  induction g with
  | zero => rfl
  | succ g ih => simp only [traj_succ, ih, Matrix.mul_zero, Matrix.zero_mul]

/-- A complete untruncated rotation block, as an additive endomorphism. Its powers represent
the residual whole-step evolutions in `apd:thm:triangle`. -/
@[expose]
noncomputable def blockEnd (Gs : ℕ → PauliString n) (θ : ℕ → ℝ) (period : ℕ) :
    AddMonoid.End (Matrix (Bits n) (Bits n) ℂ) where
  toFun A := traj Gs θ A period
  map_zero' := traj_zero_input Gs θ period
  map_add' A B := traj_add Gs θ A B period

/-- `blockEnd` applies the untruncated `traj` through one block, the evolution that appears in
`apd:eq:step_component`. -/
@[simp] theorem blockEnd_apply (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period : ℕ) (A : Matrix (Bits n) (Bits n) ℂ) :
    blockEnd Gs θ period A = traj Gs θ A period := rfl

/-- **The operator telescope.** The identity of `apd:thm:triangle`: the untruncated evolution
minus the LPD output after `r` steps is the sum of the discarded operators, each evolved through
the remaining whole steps. Here `discardedStep d` is the zero-based `X_{d+1}` of
`apd:eq:step_component`; its description as a high-weight projection is
`discardedStep_eq_truncOp`. The proof is an induction on `r` that unfolds the definition of
`discardedStep`; it needs no Hermiticity, locality or angle hypothesis. -/
theorem trotterStep_telescoping (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    ((blockEnd Gs θ period) ^ r) O - trotterStepTraj Gs θ period wstar O r =
      ∑ d ∈ range r, ((blockEnd Gs θ period) ^ (r - 1 - d))
        (discardedStep Gs θ period wstar O d) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hrec : ((blockEnd Gs θ period) ^ (r + 1)) O -
          trotterStepTraj Gs θ period wstar O (r + 1) =
          blockEnd Gs θ period
            (((blockEnd Gs θ period) ^ r) O - trotterStepTraj Gs θ period wstar O r) +
          discardedStep Gs θ period wstar O r := by
        rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, map_sub, discardedStep]
        simp only [blockEnd_apply]
        abel
      rw [hrec, ih, map_sum, Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, AddMonoid.End.one_apply]
      congr 1
      refine Finset.sum_congr rfl fun d hd => ?_
      have hpow : r - d = r - 1 - d + 1 := by
        have hd' := Finset.mem_range.1 hd
        omega
      rw [hpow, pow_succ', AddMonoid.End.coe_mul, Function.comp_apply]

/-- The untruncated, modulo-indexed run executes the specified block between successive
boundaries, as used in `apd:thm:triangle`. The endpoint `i = period` is
included. No positivity assumption is needed; `period = 0` admits only `i = 0`. -/
theorem traj_periodic_within_step (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d i : ℕ) (hi : i ≤ period) :
    traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (d * period + i) =
      traj Gs θ
        (traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (d * period)) i := by
  induction i with
  | zero => simp only [Nat.add_zero, traj_zero]
  | succ i ih =>
      have hi' : i < period := by omega
      have hmod : (d * period + i) % period = i := by
        simp [Nat.add_mod, Nat.mod_eq_of_lt hi']
      rw [Nat.add_succ, traj_succ, ih (by omega), hmod, traj_succ]

/-- The `r`-th power of the block evolution is the rotation-indexed untruncated `traj` at
`r * period`, with the rotations repeated modulo `period`. This identifies the untruncated
operator in `apd:thm:triangle`. It holds for every block length, including the empty block. -/
theorem blockEnd_pow_eq_periodic_traj (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    ((blockEnd Gs θ period) ^ r) O =
      traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (r * period) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, blockEnd_apply, ih,
        Nat.add_mul, one_mul,
        traj_periodic_within_step Gs θ period O r period le_rfl]

/-- The operator telescope of `apd:thm:triangle`, entirely in terms of
the rotation-indexed `traj`, the kept trajectory `trotterStepTraj` and the discarded operators
`discardedStep`. -/
theorem periodic_traj_sub_trotterStepTraj (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (r * period) -
        trotterStepTraj Gs θ period wstar O r =
      ∑ d ∈ range r, traj (fun g => Gs (g % period)) (fun g => θ (g % period))
        (discardedStep Gs θ period wstar O d) ((r - 1 - d) * period) := by
  simpa only [blockEnd_pow_eq_periodic_traj] using
    trotterStep_telescoping Gs θ period wstar O r

/-- Evolution through whole blocks preserves the Pauli 2-norm, the invariance needed for the
norm-level part of `apd:thm:triangle`. This is where Hermiticity of the generators is used. -/
theorem pauliNorm_blockEnd_pow {Gs : ℕ → PauliString n}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ) (period : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((blockEnd Gs θ period) ^ r) O) = pauliNorm O := by
  rw [blockEnd_pow_eq_periodic_traj]
  exact pauliNorm_traj (fun g => hG (g % period)) _ _ _

/-- **The truncation error is bounded at Pauli-norm level.** The operator telescope of
`apd:thm:triangle`, Minkowski's inequality and invariance of the Pauli norm bound the error by
the sum of the Pauli norms of the discarded operators `X_{d+1}` (`apd:eq:step_component`).
This is the norm-level part of `apd:thm:triangle`; the passage to expectation values in a
state is not formalized. -/
theorem pauliNorm_trotterStep_error_le {Gs : ℕ → PauliString n}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ) (period wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((blockEnd Gs θ period) ^ r) O - trotterStepTraj Gs θ period wstar O r) ≤
      ∑ d ∈ range r, pauliNorm (discardedStep Gs θ period wstar O d) := by
  rw [trotterStep_telescoping]
  refine (pauliNorm_sum_le _ _).trans ?_
  exact le_of_eq (Finset.sum_congr rfl fun d _ => pauliNorm_blockEnd_pow hG θ period _ _)

/-- The Pauli-norm triangle bound of `apd:thm:triangle` with the untruncated side written as
the rotation-indexed `traj` of the repeated block. The only hypothesis is Hermiticity of the
generators. -/
theorem pauliNorm_periodic_traj_error_le {Gs : ℕ → PauliString n}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ) (period wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (r * period) -
        trotterStepTraj Gs θ period wstar O r) ≤
      ∑ d ∈ range r, pauliNorm (discardedStep Gs θ period wstar O d) := by
  simpa only [blockEnd_pow_eq_periodic_traj] using
    pauliNorm_trotterStep_error_le hG θ period wstar O r

/-- The norm-level error bound of `apd:thm:triangle` for the rotation-indexed execution
`trotterTraj` with cuts at step boundaries. Positive block length is needed only to identify
this scheduled trajectory with the step-indexed recurrence `trotterStepTraj`. -/
theorem pauliNorm_trotterTraj_error_le {Gs : ℕ → PauliString n}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ) (period wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) (hp : 0 < period) :
    pauliNorm (traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (r * period) -
        trotterTraj Gs θ period wstar O (r * period)) ≤
      ∑ d ∈ range r, pauliNorm (discardedStep Gs θ period wstar O d) := by
  rw [trotterTraj_at_boundary Gs θ period wstar O r hp]
  exact pauliNorm_periodic_traj_error_le hG θ period wstar O r

/-- The norm-level triangle bound with the discarded norms written as the high-weight norms of
the operators before truncation, as in the last equality of `apd:thm:triangle`. These are not
the high-weight norms of the kept operators, which vanish. -/
theorem pauliNorm_trotterStep_error_le_highNorm {Gs : ℕ → PauliString n}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ) (period wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((blockEnd Gs θ period) ^ r) O - trotterStepTraj Gs θ period wstar O r) ≤
      ∑ d ∈ range r,
        highNorm wstar (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period) := by
  simpa only [pauliNorm_discardedStep] using
    pauliNorm_trotterStep_error_le hG θ period wstar O r

end PauliString
end Lean4LPD
