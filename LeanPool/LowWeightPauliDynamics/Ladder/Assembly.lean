/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Constants.StepSum
public import LeanPool.LowWeightPauliDynamics.Ladder.MultiJump

/-!
# Globally sampled mass of an abstract multi-jump ladder

This file bounds the sum `∑_{d=1}^{r} N m (dΓ)` of the rung masses of an abstract `MultiLadder`,
sampled at the end of each block of `Γ` layers, by summing the first-passage majorant over the
blocks (`MultiLadder.sum_steps_le`).

`sum_steps_le` is a general bound on the abstract ladder. It does not identify the sampled
quantity with the components discarded by the truncation: along a truncated trajectory the mass
above the truncation rung is zero at every block boundary, where it has just been cut, even when
the discarded component is nonzero (`retained_mass_ne_discarded_norm` in
`tests/AssemblyBound.lean`).

The per-step summation of `apd:eq:total_high_weight_norm` is handled by
`Lean4LPD/Ladder/ChainBound.lean` and `Lean4LPD/Pauli/LayerError.lean`: there every block starts
from a reset state, and merging the last inflow into the chain produces the shifted slot sum
over `chain (k+1)`. The present file is the simpler, globally sampled variant, kept as a general
theorem next to `ChainBound.lean`.

## Main results

* `MultiLadder.majorant_eq_sum_range`: the outer sum of the majorant truncates at `m + 1`,
  uniformly in the number of layers.
* `MultiLadder.sum_steps_le`: the bound on the globally sampled mass.
-/

@[expose] public section

namespace Lean4LPD.MultiLadder

open Finset

variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}

/-- The outer sum of `majorant` truncates at `m + 1` **uniformly in `T`**, which is what lets the
sum over Trotter steps be exchanged with it. Both directions vanish: terms with `k > m` have
`chain = 0` (a path to rung `m` cannot use more than `m` jumps), and terms with `k > T` have
`C(T,k) = 0` (there are not enough layers). -/
lemma majorant_eq_sum_range {m : ℕ} (hm : 1 ≤ m) (T : ℕ) :
    majorant eps E M m T = M * ∑ k ∈ range (m + 1), (T.choose k : ℝ) * chain eps E k m := by
  have hvanish_chain : ∀ k ∈ range (max (T + 1) (m + 1)), k ∉ range (m + 1) →
      (T.choose k : ℝ) * chain eps E k m = 0 := by
    intro k _ hk
    rw [Finset.mem_range] at hk
    rw [chain_eq_zero_of_lt k m hm (by omega), mul_zero]
  have hvanish_choose : ∀ k ∈ range (max (T + 1) (m + 1)), k ∉ range (T + 1) →
      (T.choose k : ℝ) * chain eps E k m = 0 := by
    intro k _ hk
    rw [Finset.mem_range] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  have hT : ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m
      = ∑ k ∈ range (max (T + 1) (m + 1)), (T.choose k : ℝ) * chain eps E k m :=
    Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.le_max_left _ _))) hvanish_choose
  have hm' : ∑ k ∈ range (m + 1), (T.choose k : ℝ) * chain eps E k m
      = ∑ k ∈ range (max (T + 1) (m + 1)), (T.choose k : ℝ) * chain eps E k m :=
    Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.le_max_right _ _))) hvanish_chain
  unfold majorant
  rw [hT, ← hm']

/-- **The globally sampled abstract ladder mass over `r` blocks.**

  `∑_{d=1}^{r} N_{≥m}^{(dΓ)} ≤ ‖O‖ · ∑_{k≤m} [((r+1)Γ)^{k+1} / (Γ·(k+1)!)] · chain_k^{(m)}`.

Each ingredient is a theorem already proved rather than an estimate made here:
`MultiLadder.le_majorant` for the per-block bound, `majorant_eq_sum_range` to make the outer sum
uniform (it needs no sign hypotheses at all — both vanishings are structural), and the slot
count `Lean4LPD.sum_choose_mul_le` for the sum over blocks. `Γ` is a positive **integer**, as
appropriate for a number of layers.

The sum has the same structure as the sum over Trotter steps in the proof of
`apd:thm:one_step_truncation_error`, but with the slot count `C(dΓ, k)` of the accumulated mass
where that proof has the shifted count of the per-step inflow; see `MultiLadder.sum_block_inflow_le`
for the latter. A separate identification is needed before interpreting this abstract mass as
discarded error. -/
theorem sum_steps_le (L : MultiLadder eps E M) (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m)
    (hM : 0 ≤ M) {G : ℕ} (hG : 1 ≤ G) {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    ∑ d ∈ range r, L.N m ((d + 1) * G)
      ≤ M * ∑ k ∈ range (m + 1),
          ((((r : ℝ) + 1) * G) ^ (k + 1) / ((G : ℝ) * (Nat.factorial (k + 1) : ℝ)))
            * chain eps E k m := by
  have hchain : ∀ k, 0 ≤ chain eps E k m := fun k => chain_nonneg heps hE k m
  -- step 1: the mass sampled at the end of each block is at most its majorant
  have h1 : ∑ d ∈ range r, L.N m ((d + 1) * G)
      ≤ ∑ d ∈ range r, M * ∑ k ∈ range (m + 1),
          ((((d + 1) * G).choose k : ℝ)) * chain eps E k m := by
    refine Finset.sum_le_sum fun d _ => ?_
    have := L.le_majorant heps ((d + 1) * G) m hm
    rwa [majorant_eq_sum_range hm ((d + 1) * G)] at this
  -- step 2: exchange the sums
  have h2 : ∑ d ∈ range r, M * ∑ k ∈ range (m + 1),
        ((((d + 1) * G).choose k : ℝ)) * chain eps E k m
      = M * ∑ k ∈ range (m + 1),
          (∑ d ∈ range r, (((d + 1) * G).choose k : ℝ)) * chain eps E k m := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
  -- step 3: the slot count, per k
  have h3 : ∑ k ∈ range (m + 1),
        (∑ d ∈ range r, (((d + 1) * G).choose k : ℝ)) * chain eps E k m
      ≤ ∑ k ∈ range (m + 1),
          ((((r : ℝ) + 1) * G) ^ (k + 1) / ((G : ℝ) * (Nat.factorial (k + 1) : ℝ)))
            * chain eps E k m := by
    refine Finset.sum_le_sum fun k _ => ?_
    exact mul_le_mul_of_nonneg_right (sum_choose_mul_le k r G hG) (hchain k)
  calc ∑ d ∈ range r, L.N m ((d + 1) * G)
      ≤ ∑ d ∈ range r, M * ∑ k ∈ range (m + 1),
          ((((d + 1) * G).choose k : ℝ)) * chain eps E k m := h1
    _ = M * ∑ k ∈ range (m + 1),
          (∑ d ∈ range r, (((d + 1) * G).choose k : ℝ)) * chain eps E k m := h2
    _ ≤ M * ∑ k ∈ range (m + 1),
          ((((r : ℝ) + 1) * G) ^ (k + 1) / ((G : ℝ) * (Nat.factorial (k + 1) : ℝ)))
            * chain eps E k m := mul_le_mul_of_nonneg_left h3 hM

end Lean4LPD.MultiLadder
