/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Pauli.Flow

/-!
# Truncation, and the ladder for the flow LPD actually runs

`Pauli/Flow.lean` builds `pauliLadder` over `traj`, the **untruncated** Heisenberg trajectory
`O^{(g)} = U_g† O U_g`. LPD does not run that flow: it discards every Pauli above the weight
threshold `w*` and carries the truncated observable `Õ^{(d)}_{≤w*}` forward. The component
discarded at Trotter step `d`, `Õ^{(d)}_{≥w*+1} = (1 - Π_{≤w*}) U_tilde† Õ^{(d-1)}_{≤w*} U_tilde`
(`apd:eq:step_component`), is the object the error accounting of `apd:thm:triangle` sums.
This file defines the truncation as an operator, defines the trajectory with truncations
interleaved, and proves that the damped ladder of `apd:thm:local_flow_k_local` survives arbitrary
interleaved restrictions. `Pauli/TrotterTruncate.lean` then specializes to the algorithm's
schedule: a named boundary schedule, a step recurrence, and the discarded-operator identity.

## Main definitions

* `PauliString.truncOp`: the truncation `∑_{p ∈ S} x_p P_p` of an operator to a set `S` of Pauli
  classes; it is `Π_{≤ w*}` at `S = (highSet n w*)ᶜ`.
* `PauliString.trajTrunc`: the trajectory that conjugates by one rotation and then truncates to
  `S g`, for a family `S : ℕ → Finset (PauliIndex n)` of retained sets.
* `PauliString.ladderNTrunc`: the family of high-weight norms along `trajTrunc`.
* `PauliString.pauliLadderTrunc`, `PauliString.pauliWeightedLadderTrunc`,
  `PauliString.pauliLadderTruncAt`: the `Ladder` and `WeightedLadder` instances over `trajTrunc`.

## Main results

* `PauliString.coeff_truncOp`, `PauliString.coeffVec_truncOp`: `truncOp S` keeps the coefficients
  in `S` and zeroes the rest; on coefficient vectors it is `restr S`.
* `PauliString.truncOp_univ`, `PauliString.sum_coeff_smul_toMatrix_herm`: completeness of the
  Pauli expansion, `O = ∑_P x_P P`.
* `PauliString.highNorm_truncOp_le`, `PauliString.pauliNorm_truncOp_le`,
  `PauliString.highNorm_truncOp_compl`: truncation only removes mass, and `Π_{≤ w}` leaves none
  above `w`.
* `PauliString.trajTrunc_univ`: truncating nothing recovers `traj`.
* `PauliString.highNorm_conj_trajTrunc_le`, `PauliString.ladderNTrunc_step`: the flow bound
  before and after the truncation of a step.

The mathematical content is a single observation. Truncating zeroes some Pauli coefficients and
leaves the others alone, so no high-weight norm `N_{≥m}` can increase under it; the flow recursion
therefore remains valid when truncations are inserted between the rotations, which is how
`apd:cor:norm_cumulation_jump` is applied to the LPD trajectory. `Flow.lean`'s
`highNorm_restr_le` is the monotonicity half of that observation, on the coefficient side.
`truncOp` supplies the *operator* to apply it to and `trajTrunc` the *trajectory* to interleave
it into.

## The truncation is an operator here, not a projector on a space

`truncOp S O := ∑_{p ∈ S} x_p P_p` rebuilds the observable from the retained coefficients. It is
`Π_{≤ w*}` at `S = (highSet n w*)ᶜ`, and it is stated at a general `S` because nothing below needs
`S` to be a weight cut. That generality is not decoration: **LPD truncates at the end of a Trotter
step, not after every rotation** (this is the setting of `apd:thm:triangle`), and `trajTrunc`
takes a *family* `S : ℕ → Finset`, so `S g = univ` at the rotations inside a step and
`S g = (highSet n w*)ᶜ` at its boundary is the algorithm's own schedule. `trajTrunc_univ` shows
the constant-`univ` family recovers `traj` on the nose.

That last statement needs `truncOp univ O = O`, i.e. **completeness of the Pauli expansion**. It
needs neither a `finrank` count nor an `InnerProductSpace` instance on `Matrix`: Parseval
(`sum_norm_coeff_sq`) plus the reproducing property (`coeff_truncOp`) gives it in a dozen lines,
because a difference with vanishing coefficients has vanishing `‖·‖_{2,normalized}`, hence
vanishing entries.
`truncOp_univ` is that proof.

## What the truncated ladder does and does not say

`pauliLadderTrunc` needs **exactly `pauliLadder`'s hypotheses** — Hermitian `k_h`-local generators,
a `k_o`-local observable, `a` dominating every `|sin(θ_g)|` — and **nothing whatever about `S`**.
Not that it is a weight cut, not that `w* ≥ k_o`, not that the schedule is periodic. Truncation
only ever removes mass, so an arbitrary family of retained sets is safe. Anything stronger in the
statement would be an artefact.

Two readings to keep apart, because the ladder is on one side of the truncation and the error is
on the other.

* `ladderNTrunc m g` is the high-weight mass of the observable **after** step `g`'s truncation.
  At the truncation rung it is zero by construction (`highNorm_truncOp_compl`) and says nothing.
* The quantity the error analysis sums is the mass **discarded** at step `g`, i.e. the high-weight
  part of the conjugate *before* truncation — the norm of the discarded component of
  `apd:eq:step_component`. That is `highNorm_conj_trajTrunc_le`, and it is the sharper statement:
  the ladder step is what is left of it after `highNorm_truncOp_le` throws mass away.

This file supplies general restriction trajectories. `Pauli/TrotterTruncate.lean` identifies the
discard at the algorithm's schedule, `Pauli/TruncationError.lean` proves the telescoping bound of
`apd:thm:triangle` at the level of Pauli norms, and `Pauli/LayerError.lean` derives the
quantitative bound on the discarded mass that `total_truncation_error` (`Constants/Total.lean`)
takes as its hypothesis `hstep`. The passage to expectation values in a physical state and the
Trotter approximation of the Hamiltonian evolution are separate from all of this.

As in `Flow.lean`, everything is stated with the closed-form rotation `rot` and the entrywise
matrices `toMatrix`; their identification with the matrix exponential and with tensor products is
proved in `RotationExp.lean` and `Pauli/Tensor.lean`.
-/

public section

namespace Lean4LPD

open Finset

namespace PauliString

variable {n ko kh : ℕ}

/-! ### The truncation `Π_{≤ w*}`

On coefficient vectors the truncation `Π_{≤ w*}` zeroes the coefficients above the threshold. On
the operator side that is a rebuild from the retained coefficients, which is what `truncOp` is. -/

/-- **The truncation of an observable to a set of Pauli classes** — the projector `Π_{≤ w*}` of
`apd:eq:step_component` at `S = (highSet n w*)ᶜ`, stated at a general `S`.

Defined as the rebuild `∑_{p ∈ S} x_p P_p` from the retained coefficients `x_p = coeff O p`, with
`P_p` the self-adjoint representative `herm p`. That this *is* a truncation — that it keeps the
coefficients in `S` and kills the rest — is `coeff_truncOp`, and it does not depend on the Pauli
expansion being complete. -/
@[expose]
noncomputable def truncOp (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    Matrix (Bits n) (Bits n) ℂ :=
  ∑ p ∈ S, coeff O p • toMatrix (herm p)

/-- **`Π_S` keeps the coefficients in `S` and zeroes the rest**, as an equation between
coefficients. The reproducing property of the Pauli family (`coeff_toMatrix_herm`) is the whole
content. -/
theorem coeff_truncOp (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ)
    (q : PauliIndex n) :
    coeff (truncOp S O) q = if q ∈ S then coeff O q else 0 := by
  have hc : ∀ A : Matrix (Bits n) (Bits n) ℂ,
      coeff A q = ((2 : ℂ) ^ n)⁻¹ * (toMatrix (herm q) * A).trace := fun _ => rfl
  have hterm : ∀ p ∈ S,
      ((2 : ℂ) ^ n)⁻¹ * (toMatrix (herm q) * (coeff O p • toMatrix (herm p))).trace
        = if q = p then coeff O p else 0 := by
    intro p _
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc,
      mul_comm (((2 : ℂ) ^ n)⁻¹) (coeff O p), mul_assoc, ← hc, coeff_toMatrix_herm]
    split <;> simp
  rw [hc, truncOp, Finset.mul_sum, Matrix.trace_sum, Finset.mul_sum,
    Finset.sum_congr rfl hterm, Finset.sum_ite_eq]

/-- `Π_S` on the coefficient side is `restr S`, which is the bridge to everything `Coeff.lean` and
`Flow.lean` prove about restriction. -/
theorem coeffVec_truncOp (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (truncOp S O) = restr S (coeffVec O) := by
  ext p
  rw [coeffVec_apply, restr_apply, coeff_truncOp]
  simp only [coeffVec_apply]

/-- **Completeness of the Pauli expansion**: `O = ∑_P x_P P`, the expansion from which the proof
of `apd:thm:local_flow_k_local` starts and the companion of Parseval in `Pauli/Coeff.lean`.

Proved from Parseval, not from a dimension count. `sum_norm_coeff_sq` says
`∑_p ‖x_p‖² = ‖O‖_{2,normalized}²`, so an operator all of whose coefficients vanish has
`‖·‖_{2,normalized} = 0`, hence all
entries zero; `coeff_truncOp` says the difference `∑_p x_p P_p − O` is such an operator. No
`InnerProductSpace` instance on `Matrix` and no `finrank` count is involved. -/
theorem truncOp_univ (O : Matrix (Bits n) (Bits n) ℂ) : truncOp univ O = O := by
  have hsub : ∀ (A B : Matrix (Bits n) (Bits n) ℂ) (q : PauliIndex n),
      coeff (A - B) q = coeff A q - coeff B q := by
    intro A B q
    rw [coeff, coeff, coeff, Matrix.mul_sub, Matrix.trace_sub, mul_sub]
  have hcoeff : ∀ q : PauliIndex n, coeff (truncOp univ O - O) q = 0 := by
    intro q
    rw [hsub, coeff_truncOp, ite_eq_left (Finset.mem_univ q), sub_self]
  have hnorm : pauliNormSq (truncOp univ O - O) = 0 := by
    rw [← sum_norm_coeff_sq]
    exact Finset.sum_eq_zero fun q _ => by rw [hcoeff q, norm_zero]; norm_num
  have hsum : ∑ a : Bits n, ∑ b : Bits n, ‖(truncOp univ O - O) a b‖ ^ 2 = 0 := by
    rw [pauliNormSq] at hnorm
    exact (mul_eq_zero.1 hnorm).resolve_left (by positivity)
  refine sub_eq_zero.1 (Matrix.ext fun a b => ?_)
  have ha := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ => Finset.sum_nonneg fun b _ => by positivity)).1 hsum a (Finset.mem_univ a)
  have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by positivity)).1 ha b
    (Finset.mem_univ b)
  exact norm_eq_zero.1 ((pow_eq_zero_iff (n := 2) (by norm_num)).1 hb)

/-- **The Pauli expansion** `O = ∑_P x_P P` in its usual form: the same statement as
`truncOp_univ`, written without the truncation operator. The basis operators are the
self-adjoint representatives `toMatrix (herm p)`; `Pauli/Tensor.lean` identifies them with the
correctly phased tensor products of one-qubit Pauli matrices (`herm p` is not always the tensor
product with coefficient `+1`; it can differ from it by a sign). -/
theorem sum_coeff_smul_toMatrix_herm (O : Matrix (Bits n) (Bits n) ℂ) :
    ∑ p : PauliIndex n, coeff O p • toMatrix (herm p) = O := truncOp_univ O

/-- **Truncation only decreases the high-weight mass**, on operators. This is
`Flow.lean`'s `highNorm_restr_le` composed with `coeffVec_truncOp`. -/
theorem highNorm_truncOp_le (w : ℕ) (S : Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) : highNorm w (truncOp S O) ≤ highNorm w O := by
  rw [highNorm, highNorm, coeffVec_truncOp]
  exact highNorm_restr_le S (coeffVec O)

/-- Truncation only decreases the total mass, which is what keeps the ladder's `reservoir` field
true along a truncated trajectory. -/
theorem pauliNorm_truncOp_le (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (truncOp S O) ≤ pauliNorm O := by
  rw [← norm_coeffVec, ← norm_coeffVec, coeffVec_truncOp]
  exact norm_restr_le _ _

/-- **`Π_{≤ w}` leaves nothing above `w`.** The defining property of the algorithm's state: after
truncating at threshold `w`, the high-weight mass is exactly zero, not merely smaller. Without
this, `trajTrunc` would be a flow with *some* mass removed rather than the LPD one. -/
theorem highNorm_truncOp_compl (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm w (truncOp (highSet n w)ᶜ O) = 0 :=
  highNorm_eq_zero w fun p hp => by
    rw [coeff_truncOp, ite_eq_right (by simp [Finset.mem_compl, mem_highSet.2 hp])]

/-! ### The truncated trajectory -/

/-- **The trajectory LPD actually runs**: conjugate by one rotation, then truncate, with `traj`'s
angle convention. At the schedule described below its value at a Trotter-step boundary is the
truncated observable that enters `apd:eq:step_component`.

The retained set is a *family* `S : ℕ → Finset (PauliIndex n)`, one per rotation, because the
algorithm truncates at the end of each Trotter step rather than after each rotation:
`S g = univ` inside a step and `S g = (highSet n w*)ᶜ` at its boundary is that schedule.
`trajTrunc_univ` records that the all-`univ` family is `traj` itself. -/
@[expose]
noncomputable def trajTrunc (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    ℕ → Matrix (Bits n) (Bits n) ℂ
  | 0 => O
  | g + 1 => truncOp (S g)
      (rot (toMatrix (Gs g)) (θ g) * trajTrunc Gs θ S O g * rot (toMatrix (Gs g)) (-(θ g)))

@[simp] lemma trajTrunc_zero (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    trajTrunc Gs θ S O 0 = O := rfl

lemma trajTrunc_succ (Gs : ℕ → PauliString n) (θ : ℕ → ℝ) (S : ℕ → Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    trajTrunc Gs θ S O (g + 1)
      = truncOp (S g)
          (rot (toMatrix (Gs g)) (θ g) * trajTrunc Gs θ S O g
            * rot (toMatrix (Gs g)) (-(θ g))) := rfl

/-- **Truncating nothing is `traj`.** The guard that `trajTrunc` generalizes `Flow.lean`'s
trajectory rather than replacing it with an incomparable object; it is an equality of *operators*,
which is what `truncOp_univ` buys. -/
theorem trajTrunc_univ (Gs : ℕ → PauliString n) (θ : ℕ → ℝ) (O : Matrix (Bits n) (Bits n) ℂ)
    (g : ℕ) : trajTrunc Gs θ (fun _ => univ) O g = traj Gs θ O g := by
  induction g with
  | zero => rfl
  | succ g ih => rw [trajTrunc_succ, ih, truncOp_univ, traj_succ]

/-- The total mass never grows along the truncated trajectory: conjugation preserves it
(`pauliNorm_conj`) and truncation can only shrink it. `traj` has this with equality; here only the
inequality holds, and it is all `Ladder.reservoir` asks for. -/
theorem pauliNorm_trajTrunc_le {Gs : ℕ → PauliString n} (hG : ∀ g, IsSelfAdjoint (Gs g))
    (θ : ℕ → ℝ) (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    pauliNorm (trajTrunc Gs θ S O g) ≤ pauliNorm O := by
  induction g with
  | zero => exact le_rfl
  | succ g ih =>
    rw [trajTrunc_succ]
    exact le_trans (pauliNorm_truncOp_le _ _)
      (le_trans (le_of_eq (pauliNorm_conj (hG g) (θ g) _)) ih)

/-- **The per-rotation-cut state carries no weight above `w*`.** A support fact, **not** a
non-vacuity witness: its conclusion follows from `highNorm_truncOp_compl`.
The algorithm's boundary-scheduled version is `highNorm_trotterStepTraj_succ` in
`Pauli/TrotterTruncate.lean` (`apd:eq:step_component`). -/
theorem highNorm_trajTrunc_succ (wstar : ℕ) (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    highNorm wstar (trajTrunc Gs θ (fun _ => (highSet n wstar)ᶜ) O (g + 1)) = 0 := by
  rw [trajTrunc_succ]
  exact highNorm_truncOp_compl wstar _

/-! ### The ladder family, and the two instances -/

/-- **The ladder family for the truncated flow**, `ladderN`'s counterpart over `trajTrunc`:
the high-weight norm `N m g` of `apd:eq:def_high_weight_norm` above the rung weight `w_m`,
evaluated on the truncated trajectory, with rung `0` the reservoir (the total Pauli 2-norm).
Rung `0` is distinguished for the reason `Ladder/Defs.lean` gives, not for convenience. -/
noncomputable def ladderNTrunc (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (ko kh : ℕ) : ℕ → ℕ → ℝ
  | 0, g => pauliNorm (trajTrunc Gs θ S O g)
  | m + 1, g => highNorm (rungWeight ko kh (m + 1)) (trajTrunc Gs θ S O g)

lemma ladderNTrunc_nonneg (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (ko kh m g : ℕ) :
    0 ≤ ladderNTrunc Gs θ S O ko kh m g := by
  cases m with
  | zero => exact pauliNorm_nonneg _
  | succ m => exact highNorm_nonneg _ _

/-- `init`: truncation has not happened yet at `g = 0`, so this is `ladderN_init` verbatim — a
`k_o`-local observable carries no mass above any rung `m ≥ 1`. -/
lemma ladderNTrunc_init {Gs : ℕ → PauliString n} {θ : ℕ → ℝ} {S : ℕ → Finset (PauliIndex n)}
    {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ}
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (m : ℕ) (hm : 1 ≤ m) :
    ladderNTrunc Gs θ S O ko kh m 0 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine highNorm_eq_zero _ fun p hp => hloc p (lt_of_le_of_lt ?_ hp)
  simp only [rungWeight, Nat.add_sub_cancel]
  exact Nat.le_add_right ko (m * (kh - 1))

/-- **The pre-truncation high-weight mass, bounded by the ladder**, at any rung `m ≥ 1`.
At this generality `S g` need not cut that mass: for example `S g = univ` discards nothing.
At the truncation rung and an actual Trotter boundary, `pauliNorm_discardedStep_le` in
`Pauli/TrotterTruncate.lean` identifies this scalar with the norm of the discarded operator of
`apd:eq:step_component`.

This is `apd:thm:local_flow_k_local` along the truncated trajectory, and
`ladderNTrunc_step` is what survives of it once the truncation throws mass away. Read the two
apart: `ladderNTrunc m (g+1)` measures retained mass, while this measures pre-cut high mass.
Only after identifying the retained set at a boundary is the latter the discarded-error summand. -/
theorem highNorm_conj_trajTrunc_le {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {S : ℕ → Finset (PauliIndex n)} {O : Matrix (Bits n) (Bits n) ℂ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh) (m g : ℕ) (hm : 1 ≤ m) :
    highNorm (rungWeight ko kh m)
        (rot (toMatrix (Gs g)) (θ g) * trajTrunc Gs θ S O g * rot (toMatrix (Gs g)) (-(θ g)))
      ≤ ladderNTrunc Gs θ S O ko kh m g
        + |Real.sin (θ g)| * ladderNTrunc Gs θ S O ko kh (m - 1) g := by
  match m, hm with
  | 1, _ =>
    change highNorm (rungWeight ko kh 1) _
      ≤ highNorm (rungWeight ko kh 1) (trajTrunc Gs θ S O g)
        + |Real.sin (θ g)| * pauliNorm (trajTrunc Gs θ S O g)
    exact highNorm_conj_le_pauliNorm (hG g) (θ g) _
  | (m + 2), _ =>
    change highNorm (rungWeight ko kh (m + 2)) _
      ≤ highNorm (rungWeight ko kh (m + 2)) (trajTrunc Gs θ S O g)
        + |Real.sin (θ g)| * highNorm (rungWeight ko kh (m + 1)) (trajTrunc Gs θ S O g)
    exact highNorm_conj_le_highNorm (w := rungWeight ko kh (m + 2))
      (w' := rungWeight ko kh (m + 1)) (hG g) (hk g) (rungWeight_add_two ko kh m).ge (θ g) _

/-- **The damped ladder step survives interleaved truncation**: the flow bound of
`apd:thm:local_flow_k_local`, then `highNorm_truncOp_le`. No hypothesis on the retained sets `S`
is used, and none is available to use. -/
theorem ladderNTrunc_step {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {S : ℕ → Finset (PauliIndex n)} {O : Matrix (Bits n) (Bits n) ℂ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh) (m g : ℕ) (hm : 1 ≤ m) :
    ladderNTrunc Gs θ S O ko kh m (g + 1)
      ≤ ladderNTrunc Gs θ S O ko kh m g
        + |Real.sin (θ g)| * ladderNTrunc Gs θ S O ko kh (m - 1) g := by
  refine le_trans ?_ (highNorm_conj_trajTrunc_le (ko := ko) hG hk m g hm)
  match m, hm with
  | (m + 1), _ =>
    change highNorm (rungWeight ko kh (m + 1)) (trajTrunc Gs θ S O (g + 1)) ≤ _
    rw [trajTrunc_succ]
    exact highNorm_truncOp_le _ _ _

/-- **The arbitrarily restricted Pauli model inhabits `Lean4LPD.Ladder`**: the recursion of
`apd:thm:local_flow_k_local` is stable under interleaved restrictions.

`pauliLadder` is a ladder for `traj`, the flow the algorithm does *not* run. This is the same
ladder for `trajTrunc`, the flow it does, and the hypotheses are **exactly** `pauliLadder`'s:
Hermitian `k_h`-local generators, a `k_o`-local observable, and `a` dominating
every `|sin(θ_g)|`. Nothing is assumed about the retained sets `S` — not that they are weight
cuts, not that the threshold exceeds `k_o`, not that the schedule is periodic — because
truncation can only remove mass, and removing mass is safe in every direction the ladder cares
about.

The `Ladder` consequences therefore apply to this restricted trajectory. The independent
multi-layer `MultiLadder` recurrence is not discharged here; see `pauliMultiLadder` in
`Pauli/LayerLadder.lean`. -/
noncomputable def pauliLadderTrunc {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {S : ℕ → Finset (PauliIndex n)} {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ} {a : ℝ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (ha : ∀ g, |Real.sin (θ g)| ≤ a)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    Ladder a (pauliNorm O) where
  N := ladderNTrunc Gs θ S O ko kh
  nonneg := ladderNTrunc_nonneg Gs θ S O ko kh
  reservoir g := pauliNorm_trajTrunc_le hG θ S O g
  init := ladderNTrunc_init hloc
  step m g hm :=
    le_trans (ladderNTrunc_step hG hk m g hm)
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (ha g)
        (ladderNTrunc_nonneg Gs θ S O ko kh (m - 1) g)))

/-- **The same family inhabits `Lean4LPD.WeightedLadder`**, mirroring `pauliWeightedLadder`. The
caveat there applies here unchanged: the flow bound is not rung-dependent, so a constant `c` is the
natural instance and the rung dependence `Ladder/Weighted.lean` exploits enters later, from the
per-layer factors `w_{j+1} sin(dt)` of `apd:cor:norm_cumulation_jump`. What this discharges is
applicability. -/
noncomputable def pauliWeightedLadderTrunc {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {S : ℕ → Finset (PauliIndex n)} {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ} {c : ℕ → ℝ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (hc : ∀ g m, |Real.sin (θ g)| ≤ c m)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    WeightedLadder c (pauliNorm O) where
  N := ladderNTrunc Gs θ S O ko kh
  nonneg := ladderNTrunc_nonneg Gs θ S O ko kh
  reservoir g := pauliNorm_trajTrunc_le hG θ S O g
  init := ladderNTrunc_init hloc
  step m g hm :=
    le_trans (ladderNTrunc_step hG hk m g hm)
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hc g m)
        (ladderNTrunc_nonneg Gs θ S O ko kh (m - 1) g)))

/-- The instance at a **per-rotation** cut: `Π_{≤ w*}` after every rotation, at a fixed
threshold. This is *not* the algorithm's schedule, which truncates at the end of each Trotter
step; that schedule is the family that is `univ` inside a Trotter step and `(highSet n w*)ᶜ` at
its boundary, which the general `S`-family form of `pauliLadderTrunc` expresses. The per-rotation
cut is a specialization of `pauliLadderTrunc`, recorded so that the general `S` is not the only
form on offer. -/
noncomputable def pauliLadderTruncAt {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ} {a : ℝ} (wstar : ℕ)
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (ha : ∀ g, |Real.sin (θ g)| ≤ a)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    Ladder a (pauliNorm O) :=
  pauliLadderTrunc (S := fun _ => (highSet n wstar)ᶜ) (ko := ko) (kh := kh) hG hk ha hloc

/-- Fully concrete, mirroring `Flow.lean`'s example so that nothing above is inhabited only in
principle: one qubit, every generator `X`, observable `Z`, conjugation angle `dt`, and the weight
cut at `w* = 1`. -/
noncomputable example (dt : ℝ) : Ladder |Real.sin dt| (pauliNorm (toMatrix Z1)) := by
  have hz : herm (cls Z1) = Z1 := by decide
  refine hz ▸ pauliLadderTruncAt (ko := wt (cls Z1)) (kh := 1) (Gs := fun _ => X1)
    (θ := fun _ => dt) 1 (fun _ => isSelfAdjoint_X1) (fun _ => ?_) (fun _ => le_rfl)
    (fun _ hp => coeff_toMatrix_herm_eq_zero hp)
  decide

end PauliString

end Lean4LPD
