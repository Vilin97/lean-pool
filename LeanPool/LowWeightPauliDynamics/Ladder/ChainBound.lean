/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Constants.StepSum
public import LeanPool.LowWeightPauliDynamics.Ladder.MultiJump
public import LeanPool.LowWeightPauliDynamics.Ladder.HockeyStick

/-!
# The last-inflow sum, with the shifted chain index

This file proves the abstract slot-count part of `apd:eq:total_high_weight_norm`: a bound on the
sum over Trotter steps of the mass that flows above the truncation rung during each step, in
terms of the chain sums of `apd:eq:composition_majorant`, and the composition count that bounds
those chain sums by binomial coefficients.

The proof of `apd:eq:total_high_weight_norm` starts from the *new inflow* during each step, not
from a sum of globally accumulated rung norms. Each step starts from a reset state, the mass
above the truncation rung having just been discarded, and mass enters only through the per-layer
inflow from the lower rungs, which the first-passage majorant bounds. Merging that final jump
into the chain gives a chain with one more jump and no extra layer slot: a chain with `K` jumps
carries the slot count `C(dΓ, K-1)`, and the layer of its last jump is accounted for by the
prefactor `Γ`. `MultiLadder.sum_steps_le` (in `Lean4LPD/Ladder/Assembly.lean`) bounds a different
abstract quantity, with `C(dΓ, K)`, and does not supply an identification with discarded
operators.

`eps` and `E` stay abstract here: no physical layer estimate, entry-tail estimate or
chain-product estimate is assumed. The reset and the per-layer inflow recurrence are explicit
hypotheses of `block_inflow_le` and `sum_block_inflow_le`; they are proved for the truncated
Pauli evolution in `Lean4LPD/Pauli/LayerError.lean`.

## Main results

* `MultiLadder.majorant_inflow_eq_shifted_chain`: the last inflow of the majorants is the
  shifted chain sum `M · ∑_k C(T,k) · chain (k+1) m`.
* `MultiLadder.shifted_chain_sum_eq_range`: the shifted sum truncates at `k < m`.
* `MultiLadder.sum_inflow_majorant_le`: the slot bound for the last-inflow majorants summed over
  the steps.
* `MultiLadder.block_inflow_le`, `MultiLadder.sum_block_inflow_le`: the same bounds for any
  within-step mass obeying the reset and the per-layer inflow recurrence.
* `sum_reverse_choose`: the reversed hockey-stick count.
* `chain_le_weighted_choose`: the composition count,
  `chain (k+1) m ≤ C · R^{m-(k+1)} · W m · C(m-1, k)`.
-/

public section

namespace Lean4LPD.MultiLadder

open Finset

variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}

/-- Merging the final inflow with `apd:eq:composition_majorant` gives a chain with one more
jump and no extra layer slot: the algebraic merge in `apd:eq:total_high_weight_norm`. -/
theorem majorant_inflow_eq_shifted_chain (m T : ℕ) :
    (∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) T) + E m * M =
      M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m := by
  have hsum : (∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) T) =
      M * ∑ j ∈ Ico 1 m, eps j m *
        ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold majorant
    ring
  rw [hsum, sum_chain_shift]
  ring

/-- The merged chains in `apd:eq:total_high_weight_norm` have at most `m` jumps.
This cuts the shifted slot sum to `k < m` uniformly in the layer count `T`. -/
theorem shifted_chain_sum_eq_range {m : ℕ} (hm : 1 ≤ m) (T : ℕ) :
    (∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m) =
      ∑ k ∈ range m, (T.choose k : ℝ) * chain eps E (k + 1) m := by
  rcases le_total (T + 1) m with h | h
  · apply Finset.sum_subset (Finset.range_mono h)
    intro k _ hk
    rw [Finset.mem_range] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  · symm
    apply Finset.sum_subset (Finset.range_mono h)
    intro k _ hk
    rw [Finset.mem_range] at hk
    rw [chain_eq_zero_of_lt (k + 1) m hm (by omega), mul_zero]

/-- The last-inflow majorants summed over steps satisfy the shifted slot count of
`apd:eq:total_high_weight_norm`: the outside `Γ` cancels the slot-bound denominator,
leaving exponent `K` and factorial `K!` for the chain with `K = k+1` jumps. -/
theorem sum_inflow_majorant_le (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m)
    (hM : 0 ≤ M) {G m : ℕ} (hG : 1 ≤ G) (hm : 1 ≤ m) (r : ℕ) :
    (G : ℝ) * ∑ d ∈ range r,
      ((∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) ((d + 1) * G)) + E m * M) ≤
      M * ∑ k ∈ range m,
        ((((r : ℝ) + 1) * G) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) *
          chain eps E (k + 1) m := by
  have hGpos : (0 : ℝ) < G := by exact_mod_cast hG
  have hslots (k : ℕ) : (G : ℝ) *
      (∑ d ∈ range r, (((d + 1) * G).choose k : ℝ)) ≤
      (((r : ℝ) + 1) * G) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
    calc
      (G : ℝ) * (∑ d ∈ range r, (((d + 1) * G).choose k : ℝ)) ≤
          G * ((((r : ℝ) + 1) * G) ^ (k + 1) /
            ((G : ℝ) * (Nat.factorial (k + 1) : ℝ))) :=
        mul_le_mul_of_nonneg_left (sum_choose_mul_le k r G hG) hGpos.le
      _ = (((r : ℝ) + 1) * G) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
        field_simp
  have hswap : (G : ℝ) * ∑ d ∈ range r,
      M * ∑ k ∈ range m, (((d + 1) * G).choose k : ℝ) * chain eps E (k + 1) m =
      M * ∑ k ∈ range m,
        ((G : ℝ) * ∑ d ∈ range r, (((d + 1) * G).choose k : ℝ)) *
          chain eps E (k + 1) m := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  simp_rw [majorant_inflow_eq_shifted_chain, shifted_chain_sum_eq_range hm]
  rw [hswap]
  apply mul_le_mul_of_nonneg_left _ hM
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_right (hslots k) (chain_nonneg heps hE (k + 1) m)

/-- Iterate the per-layer inflow from a reset state over the `G` layers of a block, as in the
first step of `apd:eq:total_high_weight_norm`. Only the majorant, not the lower-rung norms
themselves, is moved to the end of the block (`majorant_mono`). The local recurrence `hinflow`
and the reset `hreset` must be supplied by the model. -/
theorem block_inflow_le (L : MultiLadder eps E M) (heps : ∀ j m, 0 ≤ eps j m)
    (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M) {m T G : ℕ}
    (x : ℕ → ℝ) (hreset : x 0 = 0)
    (hinflow : ∀ i, i < G → x (i + 1) ≤ x i +
      (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (T + i)) + E m * M) :
    x G ≤ (G : ℝ) *
      ((∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) (T + G)) + E m * M) := by
  let C := (∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) (T + G)) + E m * M
  have hbound : ∀ i, i ≤ G → x i ≤ (i : ℝ) * C := by
    intro i
    induction i with
    | zero => intro _; simp [hreset]
    | succ i ih =>
      intro hi
      have hi' : i ≤ G := by omega
      have hsum : (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (T + i)) ≤
          ∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) (T + G) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' := Finset.mem_Ico.mp hj
        apply mul_le_mul_of_nonneg_left _ (heps j m)
        refine le_trans (L.le_majorant heps (T + i) (m - j) (by omega)) ?_
        exact (monotone_nat_of_le_succ
          (majorant_mono heps hE hM (m - j))) (Nat.add_le_add_left hi' T)
      calc
        x (i + 1) ≤ x i + (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (T + i)) + E m * M :=
          hinflow i (by omega)
        _ ≤ (i : ℝ) * C +
            (∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) (T + G)) + E m * M :=
          add_le_add (add_le_add (ih hi') hsum) le_rfl
        _ = ((i + 1 : ℕ) : ℝ) * C := by dsimp [C]; push_cast; ring
  exact hbound G le_rfl

/-- The reset-and-layer-inflow route to the merged-chain bound of
`apd:eq:total_high_weight_norm`. `x d i` is the within-step mass before the final cut; its reset
and per-layer recurrence are explicit premises, not an assumed end-to-end truncation bound. -/
theorem sum_block_inflow_le (L : MultiLadder eps E M) (heps : ∀ j m, 0 ≤ eps j m)
    (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M) {m G : ℕ} (hm : 1 ≤ m) (hG : 1 ≤ G)
    (r : ℕ) (x : ℕ → ℕ → ℝ)
    (hreset : ∀ d, d < r → x d 0 = 0)
    (hinflow : ∀ d, d < r → ∀ i, i < G → x d (i + 1) ≤ x d i +
      (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (d * G + i)) + E m * M) :
    (∑ d ∈ range r, x d G) ≤ M * ∑ k ∈ range m,
      ((((r : ℝ) + 1) * G) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) *
        chain eps E (k + 1) m := by
  refine le_trans ?_ (sum_inflow_majorant_le heps hE hM hG hm r)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  have hd' := Finset.mem_range.mp hd
  have h := block_inflow_le L heps hE hM (x d) (hreset d hd') (hinflow d hd')
  simpa only [Nat.add_mul, Nat.one_mul] using h

end Lean4LPD.MultiLadder

namespace Lean4LPD
open Finset

/-- The reversed hockey-stick count `∑_{j=1}^{m-1} C(m-j-1, k) = C(m-1, k+1)`, used to sum over
the final jump in `apd:eq:composition_majorant` and obtain the composition count in
`apd:eq:total_high_weight_norm`. -/
lemma sum_reverse_choose {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    (∑ j ∈ Ico 1 m, ((m - j - 1).choose k : ℝ)) = ((m - 1).choose (k + 1) : ℝ) := by
  simp_rw [show ∀ j : ℕ, m - j - 1 = (m - 1) - j from fun j => by omega]
  rw [Finset.sum_Ico_reflect (fun j => (j.choose k : ℝ)) 1 (by omega)]
  rw [Nat.sub_add_cancel hm, Nat.sub_self, Nat.Ico_zero_eq_range, sum_range_choose_real]

/-- The composition-count part of `apd:eq:total_high_weight_norm`:

  `chain ε E (k+1) m ≤ C · R^{m-(k+1)} · W m · C(m-1, k)`.

Local jump ratios cost at most `R^(j-1)`, while the entry estimate carries `C` exactly once;
summing the recursively defined chains gives the binomial count, rather than assuming that count.
The weight function `W` and its local ratio estimates remain explicit model inputs. -/
theorem chain_le_weighted_choose {eps : ℕ → ℕ → ℝ} {E W : ℕ → ℝ} {C R : ℝ}
    (heps : ∀ j m, 0 ≤ eps j m) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hentry : ∀ m, 1 ≤ m → E m ≤ C * R ^ (m - 1) * W m)
    (hjump : ∀ j m, 1 ≤ j → j < m →
      eps j m * W (m - j) ≤ R ^ (j - 1) * W m) :
    ∀ k m, 1 ≤ m → chain eps E (k + 1) m ≤
      C * R ^ (m - (k + 1)) * W m * ((m - 1).choose k : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro m hm
    simpa using hentry m hm
  | succ k ih =>
    intro m hm
    change chain eps E (k + 2) m ≤
      C * R ^ (m - (k + 2)) * W m * ((m - 1).choose (k + 1) : ℝ)
    by_cases hk : m < k + 2
    · rw [chain_eq_zero_of_lt (k + 2) m hm hk,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    · have hkm : k + 2 ≤ m := by omega
      rw [chain_succ_succ]
      have hterm : ∀ j ∈ Ico 1 m, eps j m * chain eps E (k + 1) (m - j) ≤
          (C * R ^ (m - (k + 2)) * W m) * ((m - j - 1).choose k : ℝ) := by
        intro j hj
        obtain ⟨hj1, hjm⟩ := Finset.mem_Ico.mp hj
        by_cases hk' : m - j < k + 1
        · rw [chain_eq_zero_of_lt (k + 1) (m - j) (by omega) hk',
            Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero]
        · have hpows : R ^ (m - j - (k + 1)) * R ^ (j - 1) = R ^ (m - (k + 2)) := by
            rw [← pow_add]
            congr 1
            omega
          calc
            eps j m * chain eps E (k + 1) (m - j) ≤
                eps j m * (C * R ^ (m - j - (k + 1)) * W (m - j) *
                  ((m - j - 1).choose k : ℝ)) :=
              mul_le_mul_of_nonneg_left (ih (m - j) (by omega)) (heps j m)
            _ = (C * R ^ (m - j - (k + 1)) * ((m - j - 1).choose k : ℝ)) *
                (eps j m * W (m - j)) := by ring
            _ ≤ (C * R ^ (m - j - (k + 1)) * ((m - j - 1).choose k : ℝ)) *
                (R ^ (j - 1) * W m) :=
              mul_le_mul_of_nonneg_left (hjump j m hj1 hjm) (by positivity)
            _ = C * (R ^ (m - j - (k + 1)) * R ^ (j - 1)) * W m *
                ((m - j - 1).choose k : ℝ) := by ring
            _ = (C * R ^ (m - (k + 2)) * W m) * ((m - j - 1).choose k : ℝ) := by
              rw [hpows]
      calc
        (∑ j ∈ Ico 1 m, eps j m * chain eps E (k + 1) (m - j)) ≤
            ∑ j ∈ Ico 1 m, (C * R ^ (m - (k + 2)) * W m) *
              ((m - j - 1).choose k : ℝ) := Finset.sum_le_sum hterm
        _ = C * R ^ (m - (k + 2)) * W m * ((m - 1).choose (k + 1) : ℝ) := by
          rw [← Finset.mul_sum, sum_reverse_choose hm k]

end Lean4LPD
