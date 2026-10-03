/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Pauli.Discard

/-!
# A repeated Trotter block with truncation at step boundaries

In LPD the Heisenberg-evolved observable is truncated at the end of each Trotter step, not after
every rotation (`apd:thm:triangle`). Here a step is a fixed block of `period` rotations: the
first `period` entries of `Gs` and `θ` specify the block, and the rotation-indexed trajectory
repeats them modulo `period`. The schedule cuts after the rotations with index `period - 1`,
`2 * period - 1`, ….

## Main definitions

* `trotterSchedule period wstar`: the retained set after rotation `g`, namely the Paulis of
  weight at most `wstar` if `g + 1` is a multiple of `period`, and all Paulis otherwise.
* `trotterTraj`: the rotation-indexed truncated trajectory `trajTrunc` with this schedule.
* `trotterStepTraj`: the step-indexed recurrence: apply the whole untruncated block, then cut.
* `discardedStep d`: the discarded operator `X_{d+1}` of `apd:eq:step_component`.

## Main results

* `trotterTraj_at_boundary`: the two executions agree at every step boundary.
* `discardedStep_eq_truncOp`: `X_{d+1}` is the projection onto weights above `wstar` of the
  operator before truncation.
* `pauliNorm_discardedStep`: the Pauli norm of `X_{d+1}` is the high-weight norm before
  truncation. By contrast the kept operator has no high-weight mass
  (`highNorm_trotterStepTraj_succ`).
* `pauliNorm_discardedStep_le`: the single-rotation flow bound `apd:thm:local_flow_k_local`
  applied to the last rotation of a step.

## Implementation notes

`trotterStepTraj` is defined independently of `trotterTraj`, so their agreement at step
boundaries is a theorem and not a definition. The hypothesis `0 < period` is needed only for this
identification. The operator identities of this file assume neither locality of the generators
nor any bound on the angles. The telescoping error estimate is in `TruncationError.lean`, and the
layer-level version with its quantitative bound is in `LayerError.lean`.
-/

public section

namespace Lean4LPD
namespace PauliString

open Finset

variable {n : ℕ}

/-- The end-of-step schedule of `apd:thm:triangle`: rotation `g` is followed
by a cut exactly when `g+1` is a multiple of the block length. -/
@[expose]
def trotterSchedule (period wstar : ℕ) (g : ℕ) : Finset (PauliIndex n) :=
  if (g + 1) % period = 0 then (highSet n wstar)ᶜ else univ

/-- No cutoff inside a block, as required by `apd:thm:triangle`. -/
theorem trotterSchedule_interior (period wstar d i : ℕ) (hi : i + 1 < period) :
    trotterSchedule (n := n) period wstar (d * period + i) = univ := by
  have hmod : (d * period + i + 1) % period = i + 1 := by
    rw [Nat.add_assoc, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hi
  simp only [trotterSchedule, hmod, Nat.add_one_ne_zero, ↓reduceIte]

/-- The last rotation of each nonempty block is followed by the weight cut
(`apd:thm:triangle`). -/
theorem trotterSchedule_boundary (period wstar d : ℕ) (hp : 0 < period) :
    trotterSchedule (n := n) period wstar (d * period + (period - 1)) =
      (highSet n wstar)ᶜ := by
  have hlast : d * period + (period - 1) + 1 = (d + 1) * period := by
    rw [Nat.add_assoc, Nat.sub_add_cancel hp, Nat.add_mul, one_mul]
  simp [trotterSchedule, hlast]

/-- Rotation-indexed execution of a fixed repeated block with end-of-step truncation
(`apd:thm:triangle`; `apd:eq:step_component`). -/
@[expose]
noncomputable def trotterTraj (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    ℕ → Matrix (Bits n) (Bits n) ℂ :=
  trajTrunc (fun g => Gs (g % period)) (fun g => θ (g % period))
    (trotterSchedule period wstar) O

/-- The trajectory starts at the input observable: no truncation is applied before the first
rotation (`apd:eq:step_component`). -/
@[simp] theorem trotterTraj_zero (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    trotterTraj Gs θ period wstar O 0 = O := rfl

/-- One rotation of the boundary-scheduled execution (`apd:thm:triangle`). -/
theorem trotterTraj_succ (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    trotterTraj Gs θ period wstar O (g + 1) =
      truncOp (trotterSchedule period wstar g)
        (rot (toMatrix (Gs (g % period))) (θ (g % period)) *
          trotterTraj Gs θ period wstar O g *
          rot (toMatrix (Gs (g % period))) (-(θ (g % period)))) := rfl

/-- The step-indexed recurrence, defined independently of `trotterTraj`: evolve through a whole
block, then cut (`apd:eq:step_component`; `apd:thm:triangle`). -/
@[expose]
noncomputable def trotterStepTraj (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    ℕ → Matrix (Bits n) (Bits n) ℂ
  | 0 => O
  | d + 1 => truncOp (highSet n wstar)ᶜ
      (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period)

/-- The step-indexed recurrence starts at the input observable itself
(`apd:eq:step_component`). -/
@[simp] theorem trotterStepTraj_zero (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    trotterStepTraj Gs θ period wstar O 0 = O := rfl

/-- The recurrence of the kept operator: evolve through the whole block, then cut
(`apd:eq:step_component`). -/
theorem trotterStepTraj_succ (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    trotterStepTraj Gs θ period wstar O (d + 1) =
      truncOp (highSet n wstar)ᶜ
        (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period) := rfl

/-- Before the boundary, no truncation interrupts the block's ordinary `traj`
(`apd:thm:triangle`). -/
theorem trotterTraj_within_step (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d i : ℕ) (hi : i < period) :
    trotterTraj Gs θ period wstar O (d * period + i) =
      traj Gs θ (trotterTraj Gs θ period wstar O (d * period)) i := by
  induction i with
  | zero => simp only [Nat.add_zero, traj_zero]
  | succ i ih =>
      have hi' : i < period := by omega
      have hmod : (d * period + i) % period = i := by
        simp [Nat.add_mod, Nat.mod_eq_of_lt hi']
      rw [Nat.add_succ, trotterTraj_succ,
        trotterSchedule_interior period wstar d i hi, truncOp_univ, ih hi', hmod,
        traj_succ]

/-- Over one complete block, the scheduled trajectory evolves without truncation and is then
cut (`apd:eq:step_component`). -/
theorem trotterTraj_next_boundary (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hp : 0 < period) :
    trotterTraj Gs θ period wstar O ((d + 1) * period) =
      truncOp (highSet n wstar)ᶜ
        (traj Gs θ (trotterTraj Gs θ period wstar O (d * period)) period) := by
  have hlast : (d + 1) * period = d * period + (period - 1) + 1 := by
    rw [Nat.add_assoc, Nat.sub_add_cancel hp, Nat.add_mul, one_mul]
  have hlt : period - 1 < period := by omega
  have hmod : (d * period + (period - 1)) % period = period - 1 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]
  rw [hlast, trotterTraj_succ, trotterSchedule_boundary period wstar d hp,
    trotterTraj_within_step Gs θ period wstar O d (period - 1) hlt, hmod]
  have htraj := traj_succ Gs θ
    (trotterTraj Gs θ period wstar O (d * period)) (period - 1)
  rw [Nat.sub_add_cancel hp] at htraj
  exact congrArg (truncOp (highSet n wstar)ᶜ) htraj.symm

/-- The rotation-indexed execution agrees with the independently defined step recurrence
at every boundary (`apd:eq:step_component`). -/
theorem trotterTraj_at_boundary (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hp : 0 < period) :
    trotterTraj Gs θ period wstar O (d * period) =
      trotterStepTraj Gs θ period wstar O d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [trotterTraj_next_boundary Gs θ period wstar O d hp, ih, trotterStepTraj_succ]

/-- The discarded operator `X_{d+1}` of `apd:eq:step_component`: the operator at the end of the
block before truncation, minus the kept operator. The zero-based index `d` is the number of
steps completed before. -/
@[expose]
noncomputable def discardedStep (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    Matrix (Bits n) (Bits n) ℂ :=
  traj Gs θ (trotterStepTraj Gs θ period wstar O d) period -
    trotterStepTraj Gs θ period wstar O (d + 1)

/-- The discarded operator is the projection of the pre-truncation operator onto the Paulis of
weight above `wstar` (`apd:eq:step_component`). -/
theorem discardedStep_eq_truncOp (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    discardedStep Gs θ period wstar O d = truncOp (highSet n wstar)
      (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period) := by
  rw [discardedStep, trotterStepTraj_succ, sub_truncOp_compl]

/-- The discarded operator's Pauli norm is the pre-truncation high-weight mass
(`apd:thm:triangle`; `apd:eq:step_component`). -/
theorem pauliNorm_discardedStep (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    pauliNorm (discardedStep Gs θ period wstar O d) =
      highNorm wstar (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period) := by
  rw [discardedStep, trotterStepTraj_succ, pauliNorm_sub_truncOp_highSet_compl]

/-- The retained operator has zero high-weight mass after each completed step. This is a
support theorem, not an error bound (`apd:eq:step_component`). -/
theorem highNorm_trotterStepTraj_succ (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    highNorm wstar (trotterStepTraj Gs θ period wstar O (d + 1)) = 0 := by
  rw [trotterStepTraj_succ, highNorm_truncOp_compl]

/-- The pre-truncation operator of a block is the last rotation of the block applied to the
scheduled trajectory just before the boundary (`apd:eq:step_component`). This connects the
step-indexed recurrence to the rotation-indexed local flow of `Truncate.lean`. -/
theorem trotterBlock_eq_boundary_pre (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hp : 0 < period) :
    traj Gs θ (trotterStepTraj Gs θ period wstar O d) period =
      rot (toMatrix (Gs (period - 1))) (θ (period - 1)) *
        trotterTraj Gs θ period wstar O (d * period + (period - 1)) *
        rot (toMatrix (Gs (period - 1))) (-(θ (period - 1))) := by
  rw [trotterTraj_within_step Gs θ period wstar O d (period - 1) (by omega),
    trotterTraj_at_boundary Gs θ period wstar O d hp]
  have htraj := traj_succ Gs θ (trotterStepTraj Gs θ period wstar O d) (period - 1)
  rw [Nat.sub_add_cancel hp] at htraj
  exact htraj

/-- `X_{d+1}` is the operator after the last rotation of the block and before the cut, minus
the scheduled trajectory at the boundary (`apd:eq:step_component`). -/
theorem discardedStep_eq_boundary_sub (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hp : 0 < period) :
    discardedStep Gs θ period wstar O d =
      rot (toMatrix (Gs (period - 1))) (θ (period - 1)) *
        trotterTraj Gs θ period wstar O (d * period + (period - 1)) *
        rot (toMatrix (Gs (period - 1))) (-(θ (period - 1))) -
      trotterTraj Gs θ period wstar O ((d + 1) * period) := by
  rw [discardedStep, trotterBlock_eq_boundary_pre Gs θ period wstar O d hp,
    trotterTraj_at_boundary Gs θ period wstar O (d + 1) hp]

/-- At a Trotter boundary, the Pauli norm of the discarded operator is the high-weight norm of
the last rotation applied to the scheduled trajectory, which is the quantity that the local-flow
bound controls (`apd:thm:triangle`). No such identification is made at interior rotations, where
nothing is discarded. -/
theorem pauliNorm_discardedStep_eq_boundary_highNorm (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hp : 0 < period) :
    pauliNorm (discardedStep Gs θ period wstar O d) = highNorm wstar
      (rot (toMatrix (Gs (period - 1))) (θ (period - 1)) *
        trotterTraj Gs θ period wstar O (d * period + (period - 1)) *
        rot (toMatrix (Gs (period - 1))) (-(θ (period - 1)))) := by
  rw [pauliNorm_discardedStep, trotterBlock_eq_boundary_pre Gs θ period wstar O d hp]

/-- The single-rotation flow bound `highNorm_conj_trajTrunc_le`, applied to the last rotation
of a step, bounds the discarded operator `X_{d+1}`
(`apd:eq:step_component`; `apd:thm:local_flow_k_local`). This is a one-rotation estimate: its
right-hand side still contains the two ladder rungs of the trajectory just before the boundary.
The multi-layer bound on the sum of the discarded norms is in `LayerError.lean`. -/
theorem pauliNorm_discardedStep_le {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {period wstar ko kh m : ℕ} {O : Matrix (Bits n) (Bits n) ℂ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (hp : 0 < period) (hm : 1 ≤ m) (hcut : wstar = rungWeight ko kh m) (d : ℕ) :
    let g := d * period + (period - 1)
    pauliNorm (discardedStep Gs θ period wstar O d) ≤
      ladderNTrunc (fun j => Gs (j % period)) (fun j => θ (j % period))
          (trotterSchedule period wstar) O ko kh m g +
        |Real.sin (θ (period - 1))| *
          ladderNTrunc (fun j => Gs (j % period)) (fun j => θ (j % period))
            (trotterSchedule period wstar) O ko kh (m - 1) g := by
  dsimp only
  have hlt : period - 1 < period := by omega
  have hmod : (d * period + (period - 1)) % period = period - 1 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]
  have hflow := highNorm_conj_trajTrunc_le
    (Gs := fun j => Gs (j % period)) (θ := fun j => θ (j % period))
    (S := trotterSchedule period wstar) (O := O) (ko := ko) (kh := kh)
    (fun j => hG (j % period)) (fun j => hk (j % period))
    m (d * period + (period - 1)) hm
  rw [hmod] at hflow
  rw [pauliNorm_discardedStep_eq_boundary_highNorm Gs θ period wstar O d hp]
  simpa only [trotterTraj, hcut] using hflow

end PauliString
end Lean4LPD
