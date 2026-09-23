/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/
import LeanPool.LowWeightPauliDynamics.Pauli.LayerLadder
import LeanPool.LowWeightPauliDynamics.Pauli.TruncationError
import LeanPool.LowWeightPauliDynamics.Constants.AssemblyBound

/-!
# The LPD truncation error of a layered Trotter circuit, in Pauli norm

This file assembles the norm-level truncation-error bound for a Trotter step made of `Γ`
disjoint-support layers of Pauli rotations, with truncation to Pauli weight at most `w*` at the
end of every step. The main result is `pauliNorm_layerStep_error_le_model_of_source_regime`: for
a `k_o`-local observable `O` and `r` Trotter steps in the paper's parameter regime,

  `‖U^r(O) - O_r‖ ≤ (t / t₀)^(m+1) · (e (m+1))^(k_o / (k_h - 1)) · ‖O‖`,

where `‖·‖` is the normalized Pauli 2-norm `pauliNorm`, `U` is the untruncated step
(`layerBlockEnd`), `O_r` is the LPD output (`layerStepTraj`), the cutoff is
`w* = rungWeight ko kh (m + 1) = k_o + m (k_h - 1)`, and `t₀ = 1 / (2 Γ (k_h - 1) α)` is
`tZeroModel Γ k_h α`. This is the Pauli-norm counterpart of `apd:thm:one_step_truncation_error`
with the time condition `apd:eq:time_condition`.

## Main definitions

* `layerBlockTraj`: the untruncated evolution through the first `i` layers of a block.
* `layerStepTraj`: the LPD recurrence: a whole block of `Γ` layers, then the weight cut.
* `layerScheduledTraj`: the same execution indexed by layers, as a `layerTraj` with the schedule
  `trotterSchedule Γ wstar`. Here the schedule counts layers, not individual rotations.
* `discardedLayerStep`: the discarded operator `X_{d+1}` of `apd:eq:step_component`.
* `layerStepMass`: the high-weight norm inside a step, before the cut.
* `layerBlockEnd`: one block as an additive endomorphism; its powers are the untruncated
  evolution.

## Main results

* `layerScheduledTraj_at_boundary`: the layer-indexed and the step-indexed executions agree at
  step boundaries.
* `pauliNorm_discardedLayerStep`: `‖X_{d+1}‖` is the high-weight norm of the operator before the
  cut.
* `layerStepMass_reset`, `layerStepMass_inflow`: the two hypotheses of
  `MultiLadder.sum_block_inflow_le`, proved for the Pauli model.
* `sum_pauliNorm_discardedLayerStep_le_chain`: the shifted-chain bound on `∑_d ‖Õ^{(d)}_{≥w*+1}‖` of
  `apd:eq:total_high_weight_norm`.
* `layerStep_telescoping`, `pauliNorm_layerStep_error_le`: the telescoping identity and the
  norm-level triangle bound of `apd:thm:triangle`, for layered steps.
* `sum_pauliNorm_discardedLayerStep_le_cZero`, `pauliNorm_layerStep_error_le_cZero`: the bound
  with the constant `c₀` of `apd:eq:c0`.
* `source_entry_inflation_le_one`, `source_beta_le_half`: the paper's step-count condition gives
  `4eβ ≤ 1` and `β ≤ 1/2`.
* `pauliNorm_layerStep_error_le_model`, `pauliNorm_layerStep_error_le_model_of_source_regime`:
  the final bound with the threshold `tZeroModel`.

## Implementation notes

The discarded operator `Õ^{(d)}_{≥w*+1}` lives at a step boundary, and its norm is the high-weight
norm of
the operator *before* the cut. The kept trajectory, whose rung masses `pauliMultiLadder`
controls, has no mass above the cutoff right after a boundary. The bridge is `layerStepMass`:
within a step it starts from zero (`layerStepMass_reset`) and grows by the multi-jump inflow from
the lower rungs of the kept trajectory (`layerStepMass_inflow`). With these two facts,
`MultiLadder.sum_block_inflow_le` bounds `∑_d ‖Õ^{(d)}_{≥w*+1}‖` by the shifted-chain sum of
`apd:eq:total_high_weight_norm`, and `MultiLadder.sum_block_epsJump_le_cZero` by the `c₀` form.

`layerStepTraj` and `layerScheduledTraj` are defined independently, and their agreement at step
boundaries is a theorem. Every hypothesis of the final theorems concerns the circuit (layer
structure, Hermiticity, sine bound), the observable (locality) or the parameters
(`Admissible`, `1 ≤ m`, `5 ≤ r`, the step-count condition); no recurrence, reset or intermediate
bound is assumed.

All bounds are in the normalized Pauli 2-norm. Expectation values in a state, and the comparison
of the Trotter circuit with the Hamiltonian evolution, are not treated here.
-/

namespace Lean4LPD

/-- In the paper's parameter regime, the step-count condition `r ≥ 8e² w₂ A` together with
`a ≤ A / r` gives `B = 4eβ ≤ 1`, where `β = 2e w₂ a` (`apd:eq:multijump_factor`; `apd:eq:c0`;
`apd:thm:one_step_truncation_error`). This is the hypothesis `B ≤ 1` of `cZero_le_two`. The
proof multiplies through by `r`; no division by `a` occurs. -/
theorem source_entry_inflation_le_one {kh1 c a A r : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (hr : 0 < r) (haA : a ≤ A / r)
    (hsteps : 8 * (Real.exp 1) ^ 2 * rungW kh1 c 2 * A ≤ r) :
    4 * Real.exp 1 * betaOf kh1 c a ≤ 1 := by
  have hw : 0 ≤ rungW kh1 c 2 := rungW_nonneg hkh hc (by decide)
  have hcoef : 0 ≤ 8 * (Real.exp 1) ^ 2 * rungW kh1 c 2 := by positivity
  have haAr : a * r ≤ A := (le_div_iff₀ hr).mp haA
  have hmul : (4 * Real.exp 1 * betaOf kh1 c a) * r ≤ r := by
    calc
      (4 * Real.exp 1 * betaOf kh1 c a) * r =
          (8 * (Real.exp 1) ^ 2 * rungW kh1 c 2) * (a * r) := by
        unfold betaOf
        ring
      _ ≤ (8 * (Real.exp 1) ^ 2 * rungW kh1 c 2) * A :=
        mul_le_mul_of_nonneg_left haAr hcoef
      _ ≤ r := hsteps
  exact (mul_le_mul_iff_left₀ hr).mp (by simpa only [one_mul] using hmul)

/-- In the paper's parameter regime, the same step-count condition gives `β ≤ 1/2`, the regime
of the entry-factor bound `entryFactor_le`
(`apd:eq:multijump_factor`; `apd:eq:entry_bound`). -/
theorem source_beta_le_half {kh1 c a A r : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (hr : 0 < r) (haA : a ≤ A / r)
    (hsteps : 8 * (Real.exp 1) ^ 2 * rungW kh1 c 2 * A ≤ r) :
    betaOf kh1 c a ≤ 1 / 2 := by
  have hB := source_entry_inflation_le_one hkh hc hr haA hsteps
  have hb0 := betaOf_nonneg_for_chain hkh hc ha
  have he : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  nlinarith [mul_nonneg (sub_nonneg.mpr he) hb0]

end Lean4LPD

namespace Lean4LPD.PauliString

open Finset

variable {n : ℕ}

/-- The untruncated evolution through the first `i` layers of a fixed block, as used to define
`Õ^{(d)}_{≥w*+1}` in `apd:eq:step_component`. -/
noncomputable def layerBlockTraj (layers : ℕ → List (PauliString n × ℝ))
    (O : Matrix (Bits n) (Bits n) ℂ) : ℕ → Matrix (Bits n) (Bits n) ℂ
  | 0 => O
  | i + 1 => layerConj (layers i) (layerBlockTraj layers O i)

/-- The fixed block begins at the supplied operator (`apd:eq:step_component`). -/
@[simp] theorem layerBlockTraj_zero (layers : ℕ → List (PauliString n × ℝ))
    (O : Matrix (Bits n) (Bits n) ℂ) : layerBlockTraj layers O 0 = O := rfl

/-- One more untruncated layer of the fixed block (`apd:eq:step_component`). -/
theorem layerBlockTraj_succ (layers : ℕ → List (PauliString n × ℝ))
    (O : Matrix (Bits n) (Bits n) ℂ) (i : ℕ) :
    layerBlockTraj layers O (i + 1) = layerConj (layers i) (layerBlockTraj layers O i) := rfl

/-- The LPD recurrence: evolve through a whole block of `Γ` layers, then keep Pauli weights at
most `wstar`. This is the recurrence of the kept operator in `apd:eq:step_component`. It is
defined directly, not as a subsequence of `layerScheduledTraj`. -/
noncomputable def layerStepTraj (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) : ℕ → Matrix (Bits n) (Bits n) ℂ
  | 0 => O
  | d + 1 => truncOp (highSet n wstar)ᶜ
      (layerBlockTraj layers (layerStepTraj layers Γ wstar O d) Γ)

/-- The recurrence starts at the input observable; no cut is applied at step `0`
(`apd:eq:step_component`). -/
@[simp] theorem layerStepTraj_zero (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) : layerStepTraj layers Γ wstar O 0 = O := rfl

/-- One complete step: evolve through the block, then cut (`apd:eq:step_component`). -/
theorem layerStepTraj_succ (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    layerStepTraj layers Γ wstar O (d + 1) = truncOp (highSet n wstar)ᶜ
      (layerBlockTraj layers (layerStepTraj layers Γ wstar O d) Γ) := rfl

/-- Execute the repeated fixed block with a cut after each multiple of `Γ` **layers**.
This uses the boundary convention of `apd:thm:triangle`. -/
noncomputable def layerScheduledTraj (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) : ℕ → Matrix (Bits n) (Bits n) ℂ :=
  layerTraj (fun T => layers (T % Γ)) (trotterSchedule Γ wstar) O

/-- The scheduled execution starts at the input observable
(`apd:eq:step_component`). -/
@[simp] theorem layerScheduledTraj_zero (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    layerScheduledTraj layers Γ wstar O 0 = O := rfl

/-- A single scheduled layer: conjugation by the layer, then the scheduled projection
(`apd:thm:triangle`). -/
theorem layerScheduledTraj_succ (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (T : ℕ) :
    layerScheduledTraj layers Γ wstar O (T + 1) = truncOp (trotterSchedule Γ wstar T)
      (layerConj (layers (T % Γ)) (layerScheduledTraj layers Γ wstar O T)) := rfl

/-- Before a boundary, the scheduled execution is the untruncated prefix of the fixed block,
started from the scheduled operator at the previous boundary (`apd:eq:step_component`). -/
theorem layerScheduledTraj_within_step (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d i : ℕ) (hi : i < Γ) :
    layerScheduledTraj layers Γ wstar O (d * Γ + i) =
      layerBlockTraj layers (layerScheduledTraj layers Γ wstar O (d * Γ)) i := by
  induction i with
  | zero => simp only [Nat.add_zero, layerBlockTraj_zero]
  | succ i ih =>
    have hi' : i < Γ := by omega
    have hmod : (d * Γ + i) % Γ = i := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hi']
    rw [Nat.add_succ, layerScheduledTraj_succ,
      trotterSchedule_interior Γ wstar d i hi, truncOp_univ, ih hi', hmod,
      layerBlockTraj_succ]

/-- Over one full block, the scheduled execution evolves without truncation and is then cut
(`apd:eq:step_component`). -/
theorem layerScheduledTraj_next_boundary (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hΓ : 0 < Γ) :
    layerScheduledTraj layers Γ wstar O ((d + 1) * Γ) = truncOp (highSet n wstar)ᶜ
      (layerBlockTraj layers (layerScheduledTraj layers Γ wstar O (d * Γ)) Γ) := by
  have hlast : (d + 1) * Γ = d * Γ + (Γ - 1) + 1 := by
    rw [Nat.add_assoc, Nat.sub_add_cancel hΓ, Nat.add_mul, one_mul]
  have hlt : Γ - 1 < Γ := by omega
  have hmod : (d * Γ + (Γ - 1)) % Γ = Γ - 1 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]
  rw [hlast, layerScheduledTraj_succ, trotterSchedule_boundary Γ wstar d hΓ,
    layerScheduledTraj_within_step layers Γ wstar O d (Γ - 1) hlt, hmod]
  have hpre := layerBlockTraj_succ layers
    (layerScheduledTraj layers Γ wstar O (d * Γ)) (Γ - 1)
  rw [Nat.sub_add_cancel hΓ] at hpre
  exact congrArg (truncOp (highSet n wstar)ᶜ) hpre.symm

/-- **The layer-indexed and the step-indexed executions agree at step boundaries**
(`apd:eq:step_component`). Both sides are defined independently, so this is a theorem. -/
theorem layerScheduledTraj_at_boundary (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hΓ : 0 < Γ) :
    layerScheduledTraj layers Γ wstar O (d * Γ) = layerStepTraj layers Γ wstar O d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [layerScheduledTraj_next_boundary layers Γ wstar O d hΓ, ih, layerStepTraj_succ]

/-- Inside a step, the untruncated prefix of the block equals the scheduled trajectory at the
corresponding layer. This identification lets the rung masses of `pauliMultiLadder` be used in
`apd:eq:total_high_weight_norm`. The endpoint `i = Γ` is excluded: there the scheduled
trajectory has already been cut. -/
theorem layerBlockTraj_eq_scheduled_prefix (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d i : ℕ) (hi : i < Γ) :
    layerBlockTraj layers (layerStepTraj layers Γ wstar O d) i =
      layerScheduledTraj layers Γ wstar O (d * Γ + i) := by
  rw [layerScheduledTraj_within_step layers Γ wstar O d i hi,
    layerScheduledTraj_at_boundary layers Γ wstar O d (by omega)]

/-- The discarded operator `X_{d+1}` of `apd:eq:step_component`: the operator at the end of
step `d + 1` before the cut, minus the kept operator. The index `d` is zero-based. -/
noncomputable def discardedLayerStep (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) : Matrix (Bits n) (Bits n) ℂ :=
  layerBlockTraj layers (layerStepTraj layers Γ wstar O d) Γ -
    layerStepTraj layers Γ wstar O (d + 1)

/-- The Pauli norm of the discarded operator is the high-weight norm of the operator **before**
the cut (`apd:thm:triangle`; `apd:eq:step_component`). -/
theorem pauliNorm_discardedLayerStep (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    pauliNorm (discardedLayerStep layers Γ wstar O d) =
      highNorm wstar (layerBlockTraj layers (layerStepTraj layers Γ wstar O d) Γ) := by
  rw [discardedLayerStep, layerStepTraj_succ, pauliNorm_sub_truncOp_highSet_compl]

/-- After every completed step the kept operator has no mass above the cutoff. This gives the
reset condition in `apd:eq:total_high_weight_norm`. It is a statement about the kept operator,
not about the discarded one. -/
theorem highNorm_layerStepTraj_succ (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    highNorm wstar (layerStepTraj layers Γ wstar O (d + 1)) = 0 := by
  rw [layerStepTraj_succ, highNorm_truncOp_compl]

/-- The high-weight norm inside step `d + 1`, after `i` untruncated layers and before the cut,
as used in `apd:eq:total_high_weight_norm`. It is defined from the matrix evolution; its
recurrence is `layerStepMass_inflow`. -/
noncomputable def layerStepMass (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d i : ℕ) : ℝ :=
  highNorm wstar (layerBlockTraj layers (layerStepTraj layers Γ wstar O d) i)

/-- **Reset at the start of every step**, as required by `apd:eq:total_high_weight_norm`: the
mass above the cutoff vanishes at layer `0` of each step. For the first step this follows from
`k_o`-locality of the input and `k_o ≤ wstar`; for later steps from the preceding cut. -/
theorem layerStepMass_reset (layers : ℕ → List (PauliString n × ℝ))
    {Γ wstar ko : ℕ} {O : Matrix (Bits n) (Bits n) ℂ}
    (hcut : ko ≤ wstar) (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (d : ℕ) :
    layerStepMass layers Γ wstar O d 0 = 0 := by
  rw [layerStepMass, layerBlockTraj_zero]
  cases d with
  | zero =>
    rw [layerStepTraj_zero]
    exact highNorm_eq_zero wstar fun p hp => hloc p (hcut.trans_lt hp)
  | succ d => exact highNorm_layerStepTraj_succ layers Γ wstar O d

/-- **Inflow inside a step.** One more layer increases the mass above the cutoff by at most the
multi-jump inflow from the lower rungs of the kept trajectory `layerN`, plus the entry factor
times the Pauli norm of the input. This is the inflow hypothesis of
`MultiLadder.sum_block_inflow_le` for `apd:eq:total_high_weight_norm`, derived here from
`highNorm_layerConj_le_multi`. -/
theorem layerStepMass_inflow (layers : ℕ → List (PauliString n × ℝ))
    (Γ : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m : ℕ}
    (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a) (hm : 1 ≤ m)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (d i : ℕ) (hi : i < Γ) :
    layerStepMass layers Γ (rungWeight ko kh m) O d (i + 1) ≤
      layerStepMass layers Γ (rungWeight ko kh m) O d i +
        (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
          layerN (fun T => layers (T % Γ)) (trotterSchedule Γ (rungWeight ko kh m)) O ko kh
            (m - j) (d * Γ + i)) +
        entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a m * pauliNorm O := by
  let A := layerBlockTraj layers (layerStepTraj layers Γ (rungWeight ko kh m) O d) i
  have hA : A = layerScheduledTraj layers Γ (rungWeight ko kh m) O (d * Γ + i) :=
    layerBlockTraj_eq_scheduled_prefix layers Γ _ O d i hi
  have hnorm : pauliNorm A ≤ pauliNorm O := by
    rw [hA]
    exact pauliNorm_layerTraj_le _ (fun T => hherm (T % Γ)) _ O _
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  have hE := entryFactor_nonneg_all hkh1
    (div_nonneg (Nat.cast_nonneg ko) hkh1.le) ha m
  have hflow := highNorm_layerConj_le_multi (layers i) hkh (hL i) (hherm i) ha (hsin i) hm hb A
  have hsum : (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
      highNorm (rungWeight ko kh (m - j)) A) =
      ∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
        layerN (fun T => layers (T % Γ)) (trotterSchedule Γ (rungWeight ko kh m)) O ko kh
          (m - j) (d * Γ + i) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [layerN_eq_highNorm _ _ _ _ _ _ _ (by have := Finset.mem_Ico.1 hj; omega), hA]
    rfl
  rw [hsum] at hflow
  exact hflow.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hnorm hE))

/-- **The sum of the discarded Pauli norms obeys the shifted-chain bound.**
This is the step of `apd:eq:total_high_weight_norm` that sums the per-step inflows over the
layer slots, with `X_{d+1}` defined by `apd:eq:step_component`: a chain with `k + 1` jumps
carries the factor `((r + 1) Γ)^(k+1) / (k+1)!`. The reset and the inflow recurrence required by
`MultiLadder.sum_block_inflow_le` are supplied by `layerStepMass_reset` and
`layerStepMass_inflow`, so they are not hypotheses. -/
theorem sum_pauliNorm_discardedLayerStep_le_chain
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a) (hm : 1 ≤ m)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (r : ℕ) :
    (∑ d ∈ range r, pauliNorm (discardedLayerStep layers Γ (rungWeight ko kh m) O d)) ≤
      pauliNorm O * ∑ k ∈ range m,
        ((((r : ℝ) + 1) * Γ) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) *
          chain (epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a)
            (entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) (k + 1) m := by
  let ML := pauliMultiLadder (fun T => layers (T % Γ))
    (trotterSchedule Γ (rungWeight ko kh m)) O hkh
    (fun T => hL (T % Γ)) (fun T => hherm (T % Γ)) ha
    (fun T => hsin (T % Γ)) hb hloc
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  have hc : 0 ≤ (ko : ℝ) / (kh - 1 : ℕ) := div_nonneg (Nat.cast_nonneg _) hkh1.le
  have h := MultiLadder.sum_block_inflow_le ML (epsJump_nonneg_all hkh1 hc ha)
    (entryFactor_nonneg_all hkh1 hc ha) (pauliNorm_nonneg O) hm hΓ r
    (layerStepMass layers Γ (rungWeight ko kh m) O)
    (fun d _ => layerStepMass_reset layers (Nat.le_add_right ko _) hloc d)
    (fun d _ i hi => layerStepMass_inflow layers Γ O hkh hL hherm ha hsin hm hb d i hi)
  simpa only [pauliNorm_discardedLayerStep, layerStepMass] using h

/-- Layer conjugation is additive, supporting the operator telescope of
`apd:thm:triangle`. -/
theorem layerConj_add (L : List (PauliString n × ℝ)) (A B : Matrix (Bits n) (Bits n) ℂ) :
    layerConj L (A + B) = layerConj L A + layerConj L B := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    simp only [layerConj, ih, Matrix.mul_add, Matrix.add_mul]

/-- Layer conjugation preserves zero, the additive-map helper for
`apd:thm:triangle`. -/
@[simp] theorem layerConj_zero (L : List (PauliString n × ℝ)) :
    layerConj L (0 : Matrix (Bits n) (Bits n) ℂ) = 0 := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [layerConj, ih, Matrix.mul_zero, Matrix.zero_mul]

/-- The evolution through a block of layers is additive, as required by
`apd:thm:triangle`. -/
theorem layerBlockTraj_add (layers : ℕ → List (PauliString n × ℝ))
    (A B : Matrix (Bits n) (Bits n) ℂ) (i : ℕ) :
    layerBlockTraj layers (A + B) i = layerBlockTraj layers A i + layerBlockTraj layers B i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [layerBlockTraj_succ, ih, layerConj_add, layerBlockTraj_succ, layerBlockTraj_succ]

/-- A zero input stays zero through a block of layers (`apd:thm:triangle`). -/
@[simp] theorem layerBlockTraj_zero_input (layers : ℕ → List (PauliString n × ℝ)) (i : ℕ) :
    layerBlockTraj layers (0 : Matrix (Bits n) (Bits n) ℂ) i = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => rw [layerBlockTraj_succ, ih, layerConj_zero]

/-- The untruncated evolution through a fixed block of `Γ` layers, as an additive endomorphism
of matrices. Its powers are the untruncated whole-step evolutions in `apd:thm:triangle`. -/
noncomputable def layerBlockEnd (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ) :
    AddMonoid.End (Matrix (Bits n) (Bits n) ℂ) where
  toFun A := layerBlockTraj layers A Γ
  map_zero' := layerBlockTraj_zero_input layers Γ
  map_add' A B := layerBlockTraj_add layers A B Γ

/-- `layerBlockEnd` applies the matrix evolution `layerBlockTraj` through `Γ` layers
(`apd:thm:triangle`). -/
@[simp] theorem layerBlockEnd_apply (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (A : Matrix (Bits n) (Bits n) ℂ) : layerBlockEnd layers Γ A = layerBlockTraj layers A Γ := rfl

/-- **The operator telescope for layered steps.** This is the identity in `apd:thm:triangle`:
the untruncated evolution minus the LPD output after `r` steps is the sum of the discarded
operators `discardedLayerStep`, each evolved through the remaining whole blocks. -/
theorem layerStep_telescoping (layers : ℕ → List (PauliString n × ℝ)) (Γ wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    ((layerBlockEnd layers Γ) ^ r) O - layerStepTraj layers Γ wstar O r =
      ∑ d ∈ range r, ((layerBlockEnd layers Γ) ^ (r - 1 - d))
        (discardedLayerStep layers Γ wstar O d) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hrec : ((layerBlockEnd layers Γ) ^ (r + 1)) O - layerStepTraj layers Γ wstar O (r + 1) =
        layerBlockEnd layers Γ
          (((layerBlockEnd layers Γ) ^ r) O - layerStepTraj layers Γ wstar O r) +
        discardedLayerStep layers Γ wstar O r := by
      rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, map_sub, discardedLayerStep]
      simp only [layerBlockEnd_apply]
      abel
    rw [hrec, ih, map_sum, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, AddMonoid.End.one_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    have hpow : r - d = r - 1 - d + 1 := by have := Finset.mem_range.1 hd; omega
    rw [hpow, pow_succ', AddMonoid.End.coe_mul, Function.comp_apply]

/-- A whole Hermitian layer block preserves the normalized Pauli norm, supporting the
norm-level triangle counterpart of `apd:thm:triangle`. -/
theorem pauliNorm_layerBlockTraj (layers : ℕ → List (PauliString n × ℝ))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1)
    (O : Matrix (Bits n) (Bits n) ℂ) (i : ℕ) :
    pauliNorm (layerBlockTraj layers O i) = pauliNorm O := by
  induction i with
  | zero => rfl
  | succ i ih => rw [layerBlockTraj_succ, pauliNorm_layerConj _ (hherm i), ih]

/-- Every power of the block evolution preserves the normalized Pauli norm, for Hermitian
generators (`apd:thm:triangle`). -/
theorem pauliNorm_layerBlockEnd_pow (layers : ℕ → List (PauliString n × ℝ))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O) = pauliNorm O := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, layerBlockEnd_apply,
      pauliNorm_layerBlockTraj layers hherm, ih]

/-- **The truncation error is at most the sum of the discarded Pauli norms.**
This is the norm-level part of `apd:thm:triangle`, in the normalized Pauli 2-norm. It is neither
a bound on expectation values nor a bound in the matrix operator norm. -/
theorem pauliNorm_layerStep_error_le (layers : ℕ → List (PauliString n × ℝ))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) (Γ wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O - layerStepTraj layers Γ wstar O r) ≤
      ∑ d ∈ range r, pauliNorm (discardedLayerStep layers Γ wstar O d) := by
  rw [layerStep_telescoping]
  refine (pauliNorm_sum_le _ _).trans ?_
  exact le_of_eq (Finset.sum_congr rfl fun d _ => pauliNorm_layerBlockEnd_pow layers hherm Γ _ _)

/-- **The truncation error obeys the shifted-chain bound.**
This composes the norm-level triangle bound of `apd:thm:triangle` with the shifted-chain bound
`sum_pauliNorm_discardedLayerStep_le_chain` of `apd:eq:total_high_weight_norm`. Besides `0 < Γ`
and `1 ≤ m`, the hypotheses concern only the generators (layer structure, Hermiticity, sine
bound, `betaOf < 1`) and the locality of the observable. -/
theorem pauliNorm_layerStep_error_le_chain
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a) (hm : 1 ≤ m)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (r : ℕ) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O -
        layerStepTraj layers Γ (rungWeight ko kh m) O r) ≤
      pauliNorm O * ∑ k ∈ range m,
        ((((r : ℝ) + 1) * Γ) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) *
          chain (epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a)
            (entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) (k + 1) m :=
  (pauliNorm_layerStep_error_le layers hherm Γ _ O r).trans
    (sum_pauliNorm_discardedLayerStep_le_chain layers Γ O hΓ hkh hL hherm ha hsin hm hb hloc r)

/-- **The sum of the discarded Pauli norms obeys the `c₀` bound.**
`MultiLadder.sum_block_epsJump_le_cZero` (`apd:eq:total_high_weight_norm`; `apd:eq:c0`) applied
to `pauliMultiLadder`, with reset and inflow supplied by `layerStepMass_reset` and
`layerStepMass_inflow`. The conclusion has the form of the hypothesis `hstep` of
`total_truncation_error`, which is therefore a theorem for the Pauli model. Here `A` stands for
the product `α t`, the cutoff is rung `m + 1`, and `B = 4eβ`. -/
theorem sum_pauliNorm_discardedLayerStep_le_cZero
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m r : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a A : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a ≤ 1 / 2)
    (hA : 0 ≤ A) (hr : 1 ≤ r) (haA : a ≤ A / (r : ℝ))
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    (∑ d ∈ range r, pauliNorm (discardedLayerStep layers Γ (rungWeight ko kh (m + 1)) O d)) ≤
      (cZero (r : ℝ) (m : ℝ) (Γ : ℝ)
          (4 * Real.exp 1 * betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) * Γ * A) ^ (m + 1) *
        (∏ j ∈ range (m + 1), rungW (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) (j + 2)) /
          (Nat.factorial (m + 1) : ℝ) * pauliNorm O := by
  have hb1 : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1 := by linarith
  let ML := pauliMultiLadder (fun T => layers (T % Γ))
    (trotterSchedule Γ (rungWeight ko kh (m + 1))) O hkh
    (fun T => hL (T % Γ)) (fun T => hherm (T % Γ)) ha
    (fun T => hsin (T % Γ)) hb1 hloc
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  have hc : 0 ≤ (ko : ℝ) / (kh - 1 : ℕ) := div_nonneg (Nat.cast_nonneg _) hkh1.le
  have h := MultiLadder.sum_block_epsJump_le_cZero ML hkh1 hc ha hb hA (pauliNorm_nonneg O)
    hΓ hr haA m (layerStepMass layers Γ (rungWeight ko kh (m + 1)) O)
    (fun d _ => layerStepMass_reset layers (Nat.le_add_right ko _) hloc d)
    (fun d _ i hi => layerStepMass_inflow layers Γ O hkh hL hherm ha hsin (by omega) hb1 d i hi)
  simpa only [pauliNorm_discardedLayerStep, layerStepMass] using h

/-- The truncation error obeys the `c₀` bound
(`apd:thm:triangle`; `apd:eq:total_high_weight_norm`; `apd:eq:c0`).
This is a statement in the normalized Pauli norm, not about expectation values. -/
theorem pauliNorm_layerStep_error_le_cZero
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m r : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a A : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a ≤ 1 / 2)
    (hA : 0 ≤ A) (hr : 1 ≤ r) (haA : a ≤ A / (r : ℝ))
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O -
        layerStepTraj layers Γ (rungWeight ko kh (m + 1)) O r) ≤
      (cZero (r : ℝ) (m : ℝ) (Γ : ℝ)
          (4 * Real.exp 1 * betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) * Γ * A) ^ (m + 1) *
        (∏ j ∈ range (m + 1), rungW (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) (j + 2)) /
          (Nat.factorial (m + 1) : ℝ) * pauliNorm O :=
  (pauliNorm_layerStep_error_le layers hherm Γ _ O r).trans
    (sum_pauliNorm_discardedLayerStep_le_cZero layers Γ O hΓ hkh hL hherm ha hsin hb hA hr haA hloc)

/-- **The truncation error with the threshold `tZeroModel`.**
This is the Pauli-norm counterpart of `apd:thm:one_step_truncation_error` and
`apd:eq:time_condition`: the error is at most `q^(m+1) (e (m+1))^(k_o/(k_h-1)) ‖O‖` with
`q = decayBase Γ k_h α t = t / tZeroModel Γ k_h α`, a threshold that depends only on `Γ`, `k_h`
and `α`. The hypotheses `1 ≤ m` and `5 ≤ r`, under which `c₀ ≤ 2` (`cZero_le_two`), are explicit,
as is `B = 4eβ ≤ 1`, which also implies `β ≤ 1/2`. Since `c₀ ≤ 2` under these hypotheses,
`tZeroModel` is at most the threshold `tZero` with the constant `c₀` (`tZeroModel_le_tZero`), so
`t < tZeroModel` is the more restrictive time condition. The hypothesis `hstep` of the scalar
theorem `total_truncation_error_product_bound` is supplied by
`pauliNorm_layerStep_error_le_cZero`. -/
theorem pauliNorm_layerStep_error_le_model
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m r : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a α t : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a)
    (hα : 0 < α) (ht : 0 ≤ t) (haA : a ≤ α * t / (r : ℝ))
    (hB : 4 * Real.exp 1 * betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a ≤ 1)
    (hadm : Admissible (r : ℝ) (m : ℝ) (Γ : ℝ)) (hm : 1 ≤ m) (hr : 5 ≤ r)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O -
        layerStepTraj layers Γ (rungWeight ko kh (m + 1)) O r) ≤
      decayBase (Γ : ℝ) (kh : ℝ) α t ^ (m + 1) *
        (Real.exp 1 * ((m : ℝ) + 1)) ^ ((ko : ℝ) / (kh - 1 : ℕ)) * pauliNorm O := by
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  have hc : 0 ≤ (ko : ℝ) / (kh - 1 : ℕ) := div_nonneg (Nat.cast_nonneg _) hkh1.le
  have hb0 := betaOf_nonneg_for_chain hkh1 hc ha
  have hB0 : 0 ≤ 4 * Real.exp 1 * betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a := by
    positivity
  have he := Real.add_one_le_exp (1 : ℝ)
  have hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a ≤ 1 / 2 := by
    nlinarith [mul_nonneg hb0 (show 0 ≤ 4 * Real.exp 1 - 2 by linarith)]
  have hstep := pauliNorm_layerStep_error_le_cZero layers Γ O hΓ hkh hL hherm ha hsin hb
    (mul_nonneg hα.le ht) (by omega : 1 ≤ r) haA hloc (m := m)
  have h := total_truncation_error_product_bound
    (a := α) (t := t) (by simpa only [mul_assoc] using hstep) hadm
    (by exact_mod_cast hm) (by exact_mod_cast hr) hB0 hB hkh1 hc hα ht (pauliNorm_nonneg O)
  have hcast : ((kh - 1 : ℕ) : ℝ) + 1 = (kh : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ kh)
  simpa only [hcast] using h

/-- **The norm-level truncation bound in the paper's parameter regime.**
This is `apd:thm:one_step_truncation_error` with `apd:eq:time_condition` at the level of the
normalized Pauli norm. Let `O` be `k_o`-local, let each step consist of `Γ` disjoint-support
layers of Hermitian rotations of weight at most `k_h`, `2 ≤ k_h`, with
`|sin θ| ≤ a ≤ α t / r`, and let the cutoff be `w* = k_o + m (k_h - 1)`. If `Admissible r m Γ`
(in particular `m ≤ r` and `8 (m + 1)² ≤ r Γ`), `1 ≤ m`, `5 ≤ r` and
`r ≥ 8e² (k_o + k_h - 1) α t`, then

  `‖U^r(O) - O_r‖ ≤ (t / t₀)^(m+1) · (e (m+1))^(k_o/(k_h-1)) · ‖O‖`,  `t₀ = tZeroModel Γ k_h α`.

The step-count condition gives `B = 4eβ ≤ 1` (`source_entry_inflation_le_one`) and hence
`β ≤ 1/2`, so neither is a separate hypothesis. The base `t / t₀` is below one whenever
`t < tZeroModel Γ k_h α`, by `decayBase_lt_one`. Nothing is asserted about expectation values in
a state or about the Trotter approximation of the Hamiltonian evolution. -/
theorem pauliNorm_layerStep_error_le_model_of_source_regime
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m r : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a α t : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a)
    (hα : 0 < α) (ht : 0 ≤ t) (haA : a ≤ α * t / (r : ℝ))
    (hsteps : 8 * (Real.exp 1) ^ 2 * ((ko : ℝ) + kh - 1) * α * t ≤ (r : ℝ))
    (hadm : Admissible (r : ℝ) (m : ℝ) (Γ : ℝ)) (hm : 1 ≤ m) (hr : 5 ≤ r)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O -
        layerStepTraj layers Γ (rungWeight ko kh (m + 1)) O r) ≤
      decayBase (Γ : ℝ) (kh : ℝ) α t ^ (m + 1) *
        (Real.exp 1 * ((m : ℝ) + 1)) ^ ((ko : ℝ) / (kh - 1 : ℕ)) * pauliNorm O := by
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  have hc : 0 ≤ (ko : ℝ) / (kh - 1 : ℕ) := div_nonneg (Nat.cast_nonneg _) hkh1.le
  have hW : rungW (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) 2 = (ko : ℝ) + kh - 1 := by
    rw [← rungWeight_cast_eq_rungW hkh (by decide : 1 ≤ 2)]
    simp only [rungWeight, Nat.reduceSub, one_mul, Nat.cast_add,
      Nat.cast_sub (by omega : 1 ≤ kh), Nat.cast_one]
    ring
  have hB := source_entry_inflation_le_one hkh1 hc
    (by exact_mod_cast (by omega : 0 < r)) haA
    (by simpa only [hW, mul_assoc] using hsteps)
  exact pauliNorm_layerStep_error_le_model layers Γ O hΓ hkh hL hherm ha hsin hα ht haA
    hB hadm hm hr hloc

end Lean4LPD.PauliString
