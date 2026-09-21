/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Order.Filter.Cofinite
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Finiteness/escape-to-infinity lemmas for genus‑1 style summability hypotheses.

These are the “cheap topology” inputs used repeatedly when working with canonical products:
from summability of `1 / ‖z i‖^2` (and a nonzero hypothesis), we get that only finitely many
indices have `‖z i‖ ≤ R` for any fixed `R > 0`.
-/

open Filter

namespace Hadamard
namespace OrderOne

lemma finite_norm_le_of_summable_inv_norm_sq {ι : Type} {z : ι → ℂ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i => (1 : ℝ) / ‖z i‖ ^ 2))
    {R : ℝ} (hR : 0 < R) :
    ({i : ι | ‖z i‖ ≤ R} : Set ι).Finite := by
  have ht : Tendsto (fun i : ι => (1 : ℝ) / ‖z i‖ ^ 2) cofinite (nhds 0) :=
    h.tendsto_cofinite_zero
  have hpos : (0 : ℝ) < (1 / R ^ 2 : ℝ) := by positivity
  have hsmall : ∀ᶠ i in cofinite, (1 : ℝ) / ‖z i‖ ^ 2 < 1 / R ^ 2 :=
    ht.eventually (Iio_mem_nhds hpos)
  have hfinite_compl : ({i : ι | ¬((1 : ℝ) / ‖z i‖ ^ 2 < 1 / R ^ 2)} : Set ι).Finite := by
    have : ({i : ι | (1 : ℝ) / ‖z i‖ ^ 2 < 1 / R ^ 2} : Set ι) ∈ (cofinite : Filter ι) := hsmall
    have : ({i : ι | (1 : ℝ) / ‖z i‖ ^ 2 < 1 / R ^ 2} : Set ι)ᶜ.Finite :=
      (Filter.mem_cofinite.1 this)
    simpa [Set.compl_ofPred] using this
  refine hfinite_compl.subset ?_
  intro i hi
  have hzpos : 0 < (‖z i‖ : ℝ) := norm_pos_iff.2 (hz0 i)
  have hzpos_sq : 0 < (‖z i‖ : ℝ) ^ 2 := by positivity
  have hsq_le : (‖z i‖ : ℝ) ^ 2 ≤ R ^ 2 := by
    have : (‖z i‖ : ℝ) ≤ R := hi
    have habs : |(‖z i‖ : ℝ)| ≤ |R| := by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_pos hR] using this
    simpa using (sq_le_sq.2 habs)
  have hcontra : (1 : ℝ) / R ^ 2 ≤ (1 : ℝ) / ‖z i‖ ^ 2 :=
    one_div_le_one_div_of_le hzpos_sq hsq_le
  intro hlt
  exact (lt_irrefl (1 / R ^ 2)) (lt_of_le_of_lt hcontra hlt)

/-- **General-exponent finiteness.**

The `exponent ≥ 1` analogue of `finite_norm_le_of_summable_inv_norm_sq`:
given `∑ 1/‖z i‖^(p+1) < ∞` (for `p : ℕ`) and all `z i ≠ 0`, only finitely
many `i` have `‖z i‖ ≤ R`. -/
lemma finite_norm_le_of_summable_inv_norm_pow {ι : Type*} {z : ι → ℂ} {p : ℕ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i : ι => (1 : ℝ) / ‖z i‖ ^ (p + 1)))
    {R : ℝ} (hR : 0 < R) :
    ({i : ι | ‖z i‖ ≤ R} : Set ι).Finite := by
  have ht : Tendsto (fun i : ι => (1 : ℝ) / ‖z i‖ ^ (p + 1)) cofinite (nhds 0) :=
    h.tendsto_cofinite_zero
  have hpos : (0 : ℝ) < (1 / R ^ (p + 1) : ℝ) := by positivity
  have hsmall : ∀ᶠ i in cofinite, (1 : ℝ) / ‖z i‖ ^ (p + 1) < 1 / R ^ (p + 1) :=
    ht.eventually (Iio_mem_nhds hpos)
  have hfinite_compl :
      ({i : ι | ¬((1 : ℝ) / ‖z i‖ ^ (p + 1) < 1 / R ^ (p + 1))} : Set ι).Finite := by
    have : ({i : ι | (1 : ℝ) / ‖z i‖ ^ (p + 1) < 1 / R ^ (p + 1)} : Set ι) ∈
        (cofinite : Filter ι) := hsmall
    have : ({i : ι | (1 : ℝ) / ‖z i‖ ^ (p + 1) < 1 / R ^ (p + 1)} : Set ι)ᶜ.Finite :=
      (Filter.mem_cofinite.1 this)
    simpa [Set.compl_ofPred] using this
  refine hfinite_compl.subset ?_
  intro i hi
  have hzpos : 0 < (‖z i‖ : ℝ) := norm_pos_iff.2 (hz0 i)
  have hzpos_pow : 0 < (‖z i‖ : ℝ) ^ (p + 1) := by positivity
  have hpow_le : (‖z i‖ : ℝ) ^ (p + 1) ≤ R ^ (p + 1) := by
    exact pow_le_pow_left₀ (norm_nonneg _) hi (p + 1)
  have hcontra : (1 : ℝ) / R ^ (p + 1) ≤ (1 : ℝ) / ‖z i‖ ^ (p + 1) :=
    one_div_le_one_div_of_le hzpos_pow hpow_le
  intro hlt
  exact (lt_irrefl (1 / R ^ (p + 1))) (lt_of_le_of_lt hcontra hlt)

lemma tendsto_norm_atTop_of_summable_inv_norm_sq {ι : Type} {z : ι → ℂ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i => (1 : ℝ) / ‖z i‖ ^ 2)) :
    Tendsto (fun i : ι => ‖z i‖) cofinite atTop := by
  refine tendsto_atTop.mpr ?_
  intro R
  by_cases hR : 0 < R
  · have hfin_le : ({i : ι | ‖z i‖ ≤ R} : Set ι).Finite :=
      finite_norm_le_of_summable_inv_norm_sq (z := z) hz0 h (R := R) hR
    have hfin_lt : ({i : ι | ‖z i‖ < R} : Set ι).Finite := by
      refine hfin_le.subset ?_
      intro i hi
      exact le_of_lt (by simpa [Set.mem_ofPred_eq] using hi)
    have : ({i : ι | ¬R ≤ ‖z i‖} : Set ι).Finite := by
      simpa [not_le] using hfin_lt
    exact (Filter.eventually_cofinite.2 this)
  · -- If `R ≤ 0`, this is trivial since norms are nonnegative.
    have hR' : R ≤ 0 := le_of_not_gt hR
    refine Filter.Eventually.of_forall ?_
    intro i
    have : (0 : ℝ) ≤ ‖z i‖ := norm_nonneg _
    linarith

end OrderOne
end Hadamard
