/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Finset.Max
import Mathlib.Order.Filter.AtTopBot.Basic
import LeanPool.LiCriterion.Hadamard.OrderOne.TailEstimates

/-!
## Summability of `∑ analyticOrderNatAt(f, ρ) / ‖ρ‖²` from order-≤1 bounds

This is the multiplicity-aware analogue of `Summability.lean`: we weight each zero `ρ` by its
vanishing order `analyticOrderNatAt f ρ`.

The key input is the Jensen/divisor bound upgraded to multiplicities
(`ZeroCounting.sum_zeros_multiplicity_le_of_max_one_maxModulus`) and the derived `O(r^(1+ε))`
bound in `TailEstimates.sum_multiplicity_zeros_le_rpow`.
-/

open scoped BigOperators

namespace Hadamard

open Complex Filter Metric MeromorphicOn Real

namespace OrderOne

/-! ### Dyadic ball finsets (no summability hypothesis) -/

theorem zerosBallFinite_of_entire
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (n : ℕ) : ({ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n} : Set Z.Zero).Finite := by
  classical
  have hf0 : f 0 ≠ 0 := by
    intro hf0
    rcases (h_zeros_only 0).1 hf0 with ⟨ρ, hρ⟩
    exact (h_z_ne_zero ρ) (by simp [hρ])
  have hRpos : 0 < (2 : ℝ) ^ n := by positivity
  have hD :
      ((MeromorphicOn.divisor f (closedBall (0 : ℂ) |(2 : ℝ) ^ n|)).support : Set ℂ).Finite :=
    (MeromorphicOn.divisor f (closedBall (0 : ℂ) |(2 : ℝ) ^ n|)).finiteSupport
      (isCompact_closedBall (0 : ℂ) |(2 : ℝ) ^ n|)
  have hImage :
      (Z.z '' ({ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n} : Set Z.Zero))
        ⊆ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |(2 : ℝ) ^ n|)).support := by
    intro u hu
    rcases hu with ⟨ρ, hρ, rfl⟩
    have hu_mem : Z.z ρ ∈ closedBall (0 : ℂ) |(2 : ℝ) ^ n| := by
      simpa [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos, Set.mem_ofPred_eq] using hρ
    exact
      mem_divisor_support_of_zero (f := f) hf_entire (u := Z.z ρ) (R := (2 : ℝ) ^ n) hu_mem hf0
        (Z.isZero ρ)
  exact
    Set.Finite.of_finite_image (f := Z.z)
      (s := ({ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n} : Set Z.Zero)) (h := hD.subset hImage)
      (hi := h_inj.injOn)

noncomputable def zerosBallFinset_of_entire
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (n : ℕ) : Finset Z.Zero :=
  (zerosBallFinite_of_entire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
        (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) n).toFinset

@[simp]
lemma mem_zerosBallFinset_of_entire_iff
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (n : ℕ) (ρ : Z.Zero) :
    ρ ∈ zerosBallFinset_of_entire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) n ↔
      ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n := by
  classical
  simp [zerosBallFinset_of_entire]

/-! ### Main summability lemma -/

theorem summable_analyticOrderNatAt_div_norm_sq_of_order_le_one
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) (hf_order_le : order f ≤ 1)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) :
    Summable (fun ρ : Z.Zero => (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2) := by
  classical
  -- Use the vanishing-tail criterion for summability.
  refine
    (summable_iff_vanishing_norm
        (f := fun ρ : Z.Zero => (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2)).2 ?_
  intro ε hε
  -- Pick a small exponent `εcount < 1` for the weighted zero-counting bound.
  let εcount : ℝ := (1 : ℝ) / 2
  have hεcount_pos : 0 < εcount := by norm_num [εcount]
  have hεcount_lt1 : εcount < 1 := by norm_num [εcount]
  -- Weighted zero-counting bound `W(r) = O(r^(1+εcount))`.
  obtain ⟨Rcount, Ccount, hCcount_nonneg, hW_le⟩ :=
    sum_multiplicity_zeros_le_rpow (f := f) hf_entire hf_finite hf_order_le Z h_zeros_only h_inj
      h_z_ne_zero εcount hεcount_pos
  -- Choose `nR` so that `max Rcount 1 ≤ 2^nR`.
  let R0 : ℝ := max Rcount 1
  have hR0_le : ∃ nR : ℕ, R0 ≤ (2 : ℝ) ^ nR := by
    have h : ∃ n : ℕ, R0 < (2 : ℝ) ^ n := by
      simpa using (pow_unbounded_of_one_lt R0 (by norm_num : (1 : ℝ) < 2))
    refine ⟨Nat.find h, le_of_lt (Nat.find_spec h)⟩
  obtain ⟨nR, hnR⟩ := hR0_le
  -- Geometric ratio `q = 2^(εcount-1)` with `0 < q < 1`.
  let q : ℝ := (2 : ℝ) ^ (εcount - 1)
  have hq_pos : 0 < q := by
    simpa [q] using Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (εcount - 1)
  have hq_lt_one : q < 1 := by
    have hneg : εcount - 1 < 0 := by linarith [hεcount_lt1]
    simpa [q] using Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) hneg
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  -- Constant controlling the geometric tail.
  let C : ℝ := (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount * q / (1 - q)
  have hC_nonneg : 0 ≤ C := by
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) + εcount) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
    have hden_pos : 0 < (1 - q) := sub_pos.mpr hq_lt_one
    have hnum_nonneg : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount * q :=
      mul_nonneg (mul_nonneg hpow_nonneg hCcount_nonneg) hq_nonneg
    exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
  -- Choose `n₀` so that `C * q^n₀ < ε`.
  have hlim : Tendsto (fun n : ℕ => C * q ^ n) atTop (nhds (0 : ℝ)) := by
    have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (nhds (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
    simpa [mul_zero] using (Tendsto.const_mul C hpow)
  have h_event : ∀ᶠ n : ℕ in atTop, |C * q ^ n| < ε := by
    have hball : Metric.ball (0 : ℝ) ε ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ hε
    have hmem := hlim hball
    simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, sub_zero] using hmem
  obtain ⟨N, hN⟩ := (eventually_atTop.1 h_event)
  let n₀ : ℕ := max nR N
  have hn₀_ge_nR : nR ≤ n₀ := le_max_left _ _
  have hn₀_ge_N : N ≤ n₀ := le_max_right _ _
  have hn₀_lt : |C * q ^ n₀| < ε := hN n₀ hn₀_ge_N
  -- Use the dyadic ball `‖Z.z ρ‖ ≤ 2^(n₀+1)` as the "finite head" for the Cauchy criterion.
  refine ⟨
    zerosBallFinset_of_entire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
      (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (n₀ + 1),
    ?_⟩
  intro t ht
  -- If `t` is disjoint from the ball, then each element has norm strictly larger than `2^(n₀+1)`.
  have hcond : ∀ ρ : Z.Zero, ρ ∈ t → (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖ := by
    intro ρ hρt
    have hnot :
        ρ ∉
          zerosBallFinset_of_entire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (n₀ + 1) :=
      (Finset.disjoint_left.1 ht) hρt
    have hnot' : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (n₀ + 1) := by
      simpa
        [mem_zerosBallFinset_of_entire_iff
          (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero)]
        using hnot
    exact lt_of_not_ge hnot'
  -- Define an indicator function cutting off the "small zeros".
  let g : Z.Zero → ℝ := fun ρ =>
    if (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖ then
      (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2
    else 0
  have hg_nonneg : ∀ ρ : Z.Zero, 0 ≤ g ρ := by
    intro ρ
    by_cases hρ : (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖
    · have : 0 ≤ (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2 := by positivity
      simpa [g, hρ] using this
    · simp [g, hρ]
  have hsum_eq :
      (∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2) = ∑ ρ ∈ t, g ρ := by
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    have hρ' := hcond ρ hρ
    simp [g, hρ']
  -- Place `t` inside a large dyadic ball `ball m`.
  have ht_subset :
      ∃ m : ℕ,
        t ⊆
          zerosBallFinset_of_entire
            (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m := by
    classical
    by_cases ht0 : t = ∅
    · refine ⟨0, ?_⟩
      simp [ht0]
    · have ht_ne : t.Nonempty := Finset.nonempty_iff_ne_empty.2 ht0
      let R : ℝ := t.sup' ht_ne fun ρ : Z.Zero => ‖Z.z ρ‖
      have hR : ∀ ρ : Z.Zero, ρ ∈ t → ‖Z.z ρ‖ ≤ R := by
        intro ρ hρ
        exact Finset.le_sup' (f := fun ρ : Z.Zero => ‖Z.z ρ‖) hρ
      have hpow : ∃ m : ℕ, max R 1 < (2 : ℝ) ^ m := by
        simpa using pow_unbounded_of_one_lt (max R 1) (by norm_num : (1 : ℝ) < 2)
      refine ⟨Nat.find hpow, ?_⟩
      intro ρ hρt
      have hρ_leR : ‖Z.z ρ‖ ≤ R := hR ρ hρt
      have hρ_le : ‖Z.z ρ‖ ≤ max R 1 := le_trans hρ_leR (le_max_left _ _)
      have hmax_le : max R 1 ≤ (2 : ℝ) ^ Nat.find hpow := le_of_lt (Nat.find_spec hpow)
      have hρ_ball : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ Nat.find hpow := le_trans hρ_le hmax_le
      exact
        (mem_zerosBallFinset_of_entire_iff
          (hf_entire := hf_entire) (Z := Z)
          (h_zeros_only := h_zeros_only) (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) _ _).2
          hρ_ball
  rcases ht_subset with ⟨m, htm⟩
  -- Bound `∑_{ρ ∈ t} g ρ` by a dyadic-shell geometric estimate.
  have hball :
      (∑ ρ ∈
          zerosBallFinset_of_entire
            (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m,
        g ρ)
        ≤ C * ((2 : ℝ) ^ n₀) ^ (εcount - 1) := by
    let w : Z.Zero → ℝ := fun ρ => (analyticOrderNatAt f (Z.z ρ) : ℝ)
    have hsub_ball :
        ∀ k : ℕ,
          zerosBallFinset_of_entire
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k ⊆
            zerosBallFinset_of_entire
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) := by
      intro k ρ hρ
      have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k :=
        (mem_zerosBallFinset_of_entire_iff
          (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k ρ).1 hρ
      have hk_le : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ k)
      exact
        (mem_zerosBallFinset_of_entire_iff
          (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) ρ).2 (le_trans hnorm hk_le)
    have hshell :
        ∀ k : ℕ, n₀ + 1 ≤ k →
          (∑ ρ ∈
              zerosBallFinset_of_entire
                    (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
                    (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) \
                zerosBallFinset_of_entire
                    (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
                    (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k,
              g ρ)
            ≤ (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount * q ^ k := by
      intro k hk
      let ball : ℕ → Finset Z.Zero := fun t =>
        zerosBallFinset_of_entire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) t
      let diff : Finset Z.Zero := ball (k + 1) \ ball k
      have hk_pow_le : (2 : ℝ) ^ (n₀ + 1) ≤ (2 : ℝ) ^ k :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
      have hdiff_simp :
          (∑ ρ ∈ diff, g ρ) = ∑ ρ ∈ diff, w ρ / ‖Z.z ρ‖ ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro ρ hρ
        have hnot : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k := by
          intro hle
          have : ρ ∈ ball k :=
            (mem_zerosBallFinset_of_entire_iff
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k ρ).2 hle
          exact (Finset.mem_sdiff.1 hρ).2 this
        have hlt : (2 : ℝ) ^ k < ‖Z.z ρ‖ := lt_of_not_ge hnot
        have hcond' : (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖ :=
          lt_of_lt_of_le (hk_pow_le.trans_lt hlt) (le_rfl)
        simp [g, w, hcond']
      have hterm_le :
          ∀ ρ, ρ ∈ diff → w ρ / ‖Z.z ρ‖ ^ 2 ≤ w ρ / ((2 : ℝ) ^ k) ^ 2 := by
        intro ρ hρ
        have hnot : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k := by
          intro hle
          have : ρ ∈ ball k :=
            (mem_zerosBallFinset_of_entire_iff
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k ρ).2 hle
          exact (Finset.mem_sdiff.1 hρ).2 this
        have hk_le_norm : (2 : ℝ) ^ k ≤ ‖Z.z ρ‖ := le_of_lt (lt_of_not_ge hnot)
        have hk2_pos : 0 < ((2 : ℝ) ^ k) ^ 2 := by positivity
        have hk2_le : ((2 : ℝ) ^ k) ^ 2 ≤ ‖Z.z ρ‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) hk_le_norm 2
        have hw_nonneg : 0 ≤ w ρ := by positivity [w]
        have hfrac : (1 : ℝ) / ‖Z.z ρ‖ ^ 2 ≤ (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2 := by
          simpa [one_div, inv_pow] using (one_div_le_one_div_of_le hk2_pos hk2_le)
        simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left hfrac hw_nonneg)
      have hsum_le :
          (∑ ρ ∈ diff, w ρ / ‖Z.z ρ‖ ^ 2) ≤ ∑ ρ ∈ diff, w ρ / ((2 : ℝ) ^ k) ^ 2 :=
        Finset.sum_le_sum hterm_le
      have hRcount_le : Rcount ≤ (2 : ℝ) ^ (k + 1) := by
        have hRcount_le_R0 : Rcount ≤ R0 := le_max_left _ _
        have hnR_le_k : nR ≤ k := le_trans hn₀_ge_nR (le_trans (Nat.le_succ n₀) hk)
        have hnR_le_k1 : nR ≤ k + 1 := Nat.le_succ_of_le hnR_le_k
        have hpow : (2 : ℝ) ^ nR ≤ (2 : ℝ) ^ (k + 1) :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnR_le_k1
        exact le_trans (le_trans hRcount_le_R0 hnR) hpow
      have hcount_ball :
          (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0) ≤
            Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + εcount) :=
        hW_le ((2 : ℝ) ^ (k + 1)) hRcount_le
      have hball_finsum :
          (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0) =
            ∑ ρ ∈ ball (k + 1), w ρ := by
        have hsupp :
            Function.support (fun ρ : Z.Zero => if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0) ⊆
              ball (k + 1) := by
          intro ρ hρ
          have hne :
              (if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0) ≠ 0 :=
            Function.mem_support.1 hρ
          have hle : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) := by
            by_contra hle
            apply hne
            simp [hle]
          exact
            (mem_zerosBallFinset_of_entire_iff
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) ρ).2 hle
        have this :=
          finsum_eq_sum_of_support_subset
            (f := fun ρ : Z.Zero => if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0)
            (s := ball (k + 1)) hsupp
        have hsum_if :
            (∑ ρ ∈ ball (k + 1), if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0) =
              ∑ ρ ∈ ball (k + 1), w ρ := by
          refine Finset.sum_congr rfl ?_
          intro ρ hρ
          have hle : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) :=
            (mem_zerosBallFinset_of_entire_iff
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) ρ).1 hρ
          simp [hle]
        simpa [hsum_if] using this
      have hsum_ball :
          (∑ ρ ∈ ball (k + 1), w ρ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + εcount) := by
        simpa [hball_finsum] using hcount_ball
      have hsum_mult_diff :
          (∑ ρ ∈ diff, w ρ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + εcount) := by
        have hdiff_le_ball :
            (∑ ρ ∈ diff, w ρ) ≤ ∑ ρ ∈ ball (k + 1), w ρ := by
          have hw_nonneg :
              ∀ ρ ∈ ball (k + 1), ρ ∉ diff → 0 ≤ w ρ := by
            intro ρ _ _
            positivity [w]
          exact
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.sdiff_subset : diff ⊆ ball (k + 1)) hw_nonneg
        exact le_trans hdiff_le_ball hsum_ball
      -- Put everything together and rewrite into `q^k`.
      have hqk : q ^ k = ((2 : ℝ) ^ k) ^ (εcount - 1) := by
        simpa [q] using
          (Real.rpow_pow_comm (x := (2 : ℝ)) (hx := by positivity) (εcount - 1) k)
      have hdiv :
          ((2 : ℝ) ^ k) ^ (εcount - 1) =
            ((2 : ℝ) ^ k) ^ ((1 : ℝ) + εcount) / ((2 : ℝ) ^ k) ^ (2 : ℕ) := by
        have hk_pos : 0 < (2 : ℝ) ^ k := by positivity
        have hsub : ((1 : ℝ) + εcount) - (2 : ℝ) = εcount - 1 := by ring
        simpa [hsub, Real.rpow_natCast ((2 : ℝ) ^ k) 2] using
          (Real.rpow_sub hk_pos ((1 : ℝ) + εcount) (2 : ℝ))
      have hrewrite :
          Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + εcount) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2)
            = (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount * q ^ k := by
        have hpow_succ : (2 : ℝ) ^ (k + 1) = (2 : ℝ) * (2 : ℝ) ^ k := by
          simp [pow_succ, mul_comm]
        have hpowk_nonneg : 0 ≤ (2 : ℝ) ^ k := by positivity
        have h2_nonneg : 0 ≤ (2 : ℝ) := by norm_num
        calc
          Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + εcount) *
              ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2)
              =
              Ccount * (((2 : ℝ) * (2 : ℝ) ^ k) ^ ((1 : ℝ) + εcount)) *
                ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by
                simp [hpow_succ]
          _ =
              Ccount * ((2 : ℝ) ^ ((1 : ℝ) + εcount) * ((2 : ℝ) ^ k) ^ ((1 : ℝ) + εcount)) *
                  ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by
                have hsplit :
                    ((2 : ℝ) * (2 : ℝ) ^ k) ^ ((1 : ℝ) + εcount) =
                      (2 : ℝ) ^ ((1 : ℝ) + εcount) * ((2 : ℝ) ^ k) ^ ((1 : ℝ) + εcount) := by
                  simpa using
                    (Real.mul_rpow (x := (2 : ℝ)) (y := (2 : ℝ) ^ k) (z := (1 : ℝ) + εcount)
                      h2_nonneg hpowk_nonneg)
                simp [hsplit, mul_assoc,
                  -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
          _ =
              (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount *
                  (((2 : ℝ) ^ k) ^ ((1 : ℝ) + εcount) / ((2 : ℝ) ^ k) ^ (2 : ℕ)) := by
                simp [div_eq_mul_inv, mul_assoc, mul_comm,
                  -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
          _ = (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount * ((2 : ℝ) ^ k) ^ (εcount - 1) := by
                simp [hdiv, mul_assoc, mul_comm,
                  -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
          _ = (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount * q ^ k := by
                simp [hqk]
      have hmain :
          (∑ ρ ∈ diff, g ρ) ≤ (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount * q ^ k := by
        calc
          (∑ ρ ∈ diff, g ρ) = ∑ ρ ∈ diff, w ρ / ‖Z.z ρ‖ ^ 2 := by
            simp [hdiff_simp]
          _ ≤ ∑ ρ ∈ diff, w ρ / ((2 : ℝ) ^ k) ^ 2 := hsum_le
          _ = (∑ ρ ∈ diff, w ρ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by
            simp [div_eq_mul_inv, Finset.sum_mul]
          _ ≤ (Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + εcount)) *
                ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by
            have hconst_nonneg : 0 ≤ (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_right hsum_mult_diff hconst_nonneg
          _ = (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount * q ^ k := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hrewrite
      simpa [ball, diff] using hmain
    -- Sum the shell estimates.
    by_cases hm : m ≤ n₀ + 1
    · have hsum0 :
          (∑ ρ ∈
              zerosBallFinset_of_entire
                (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
                (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m,
            g ρ) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro ρ hρ
        have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ m :=
          (mem_zerosBallFinset_of_entire_iff
            (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m ρ).1 hρ
        have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (n₀ + 1) :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
        have : ¬ (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖ := not_lt_of_ge (le_trans hnorm hpow)
        simp [g, this]
      have hrhs_nonneg : 0 ≤ C * ((2 : ℝ) ^ n₀) ^ (εcount - 1) := by
        have : 0 ≤ ((2 : ℝ) ^ n₀) ^ (εcount - 1) :=
          Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n₀) _
        exact mul_nonneg hC_nonneg this
      simpa [hsum0] using hrhs_nonneg
    · have hm_ge : n₀ + 1 < m := lt_of_not_ge hm
      let ball : ℕ → Finset Z.Zero := fun t =>
        zerosBallFinset_of_entire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) t
      -- Write `m = (n₀+1) + t` for some `t > 0` and sum shells.
      set t' : ℕ := m - (n₀ + 1) with ht'_def
      have ht'_pos : 0 < t' := Nat.sub_pos_of_lt hm_ge
      have hm_eq : m = n₀ + 1 + t' := (Nat.add_sub_cancel' (le_of_lt hm_ge)).symm
      have hind :
          ∀ t : ℕ,
            (∑ ρ ∈ ball (n₀ + 1 + t), g ρ) ≤
              (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount *
                (∑ i ∈ Finset.range t, q ^ (n₀ + 1 + i)) := by
        intro t
        induction t using Nat.rec with
        | zero =>
            have hsum0 :
                (∑ ρ ∈ ball (n₀ + 1), g ρ) = 0 := by
              refine Finset.sum_eq_zero ?_
              intro ρ hρ
              have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (n₀ + 1) :=
                (mem_zerosBallFinset_of_entire_iff
                  (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
                  (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (n₀ + 1) ρ).1 hρ
              have : ¬ (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖ := not_lt_of_ge hnorm
              simp [g, this]
            simp [ball, hsum0]
        | succ j ih =>
            set k : ℕ := n₀ + 1 + j
            have hk : n₀ + 1 ≤ k := Nat.le_add_right _ _
            have hsub : ball k ⊆ ball (k + 1) := by
              simpa [ball] using hsub_ball k
            have hdecomp :=
              (Finset.sum_sdiff (s₁ := ball k) (s₂ := ball (k + 1)) (f := g) hsub).symm
            have hshell_le :
                (∑ ρ ∈ ball (k + 1) \ ball k, g ρ)
                  ≤ (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount * q ^ k := hshell k hk
            have hgeom :
                (∑ i ∈ Finset.range (j + 1), q ^ (n₀ + 1 + i))
                  = (∑ i ∈ Finset.range j, q ^ (n₀ + 1 + i)) + q ^ k := by
              simpa [k, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (Finset.sum_range_succ (f := fun i => q ^ (n₀ + 1 + i)) j)
            have ih' :
                (∑ ρ ∈ ball k, g ρ) ≤
                  (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount *
                    (∑ i ∈ Finset.range j, q ^ (n₀ + 1 + i)) := by
              simpa [k, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih
            calc
              (∑ ρ ∈ ball (k + 1), g ρ)
                  = (∑ ρ ∈ ball (k + 1) \ ball k, g ρ) + (∑ ρ ∈ ball k, g ρ) := by
                        simpa [k, add_assoc, add_comm, add_left_comm] using hdecomp
              _ ≤ (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount * q ^ k +
                    (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount *
                      (∑ i ∈ Finset.range j, q ^ (n₀ + 1 + i)) := by
                        gcongr
              _ = (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount *
                    ((∑ i ∈ Finset.range j, q ^ (n₀ + 1 + i)) + q ^ k) := by
                        ring
              _ = (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount *
                    (∑ i ∈ Finset.range (j + 1), q ^ (n₀ + 1 + i)) := by
                        simp [hgeom]
      have hfinite_le :
          (∑ ρ ∈ ball m, g ρ) ≤
            (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount *
              (∑ i ∈ Finset.range t', q ^ (n₀ + 1 + i)) := by
        simpa [hm_eq, ball] using hind t'
      have hgeom_le :
          (∑ i ∈ Finset.range t', q ^ (n₀ + 1 + i)) ≤ (q ^ (n₀ + 1)) * (1 - q)⁻¹ := by
        have hsum : Summable (fun i : ℕ => q ^ i) :=
          summable_geometric_of_lt_one (le_of_lt hq_pos) hq_lt_one
        have hsum' : Summable (fun i : ℕ => q ^ (n₀ + 1) * q ^ i) :=
          hsum.mul_left (q ^ (n₀ + 1))
        have hnonneg : ∀ i : ℕ, 0 ≤ q ^ (n₀ + 1) * q ^ i := by
          intro i; positivity
        have hle_tsum :
            (∑ i ∈ Finset.range t', q ^ (n₀ + 1) * q ^ i) ≤ ∑' i : ℕ, q ^ (n₀ + 1) * q ^ i := by
          refine
            Summable.sum_le_tsum
              (s := Finset.range t')
              (f := fun i : ℕ => q ^ (n₀ + 1) * q ^ i) ?_ hsum'
          intro i hi
          exact hnonneg i
        have hpow_add : ∀ i : ℕ, q ^ (n₀ + 1 + i) = q ^ (n₀ + 1) * q ^ i := by
          intro i
          simp [pow_add, mul_assoc]
        have hsum_eq :
            (∑ i ∈ Finset.range t', q ^ (n₀ + 1 + i)) =
              (∑ i ∈ Finset.range t', q ^ (n₀ + 1) * q ^ i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [hpow_add i]
        have htsum_eq :
            (∑' i : ℕ, q ^ (n₀ + 1) * q ^ i) = (q ^ (n₀ + 1)) * (1 - q)⁻¹ := by
          have hgeom0 : (∑' i : ℕ, q ^ i) = (1 - q)⁻¹ :=
            tsum_geometric_of_lt_one (h₁ := le_of_lt hq_pos) (h₂ := hq_lt_one)
          calc
            (∑' i : ℕ, q ^ (n₀ + 1) * q ^ i) = (q ^ (n₀ + 1)) * ∑' i : ℕ, q ^ i := by
                rw [tsum_mul_left]
            _ = (q ^ (n₀ + 1)) * (1 - q)⁻¹ := by rw [hgeom0]
        have : (∑ i ∈ Finset.range t', q ^ (n₀ + 1 + i)) ≤ (q ^ (n₀ + 1)) * (1 - q)⁻¹ := by
          have hle_tsum' :
              (∑ i ∈ Finset.range t', q ^ (n₀ + 1 + i)) ≤ ∑' i : ℕ, q ^ (n₀ + 1) * q ^ i := by
            rw [hsum_eq]
            exact hle_tsum
          exact le_trans hle_tsum' (by rw [htsum_eq])
        exact this
      -- Combine and simplify to the desired bound.
      have hqpow : q ^ (n₀ + 1) = q ^ n₀ * q := by simp [pow_succ]
      have hqk : q ^ n₀ = ((2 : ℝ) ^ n₀) ^ (εcount - 1) := by
        simpa [q] using
          (Real.rpow_pow_comm (x := (2 : ℝ)) (hx := by positivity) (εcount - 1) n₀)
      have hfinal :
          (∑ ρ ∈ ball m, g ρ) ≤ C * ((2 : ℝ) ^ n₀) ^ (εcount - 1) := by
        have hden_pos : 0 < (1 - q) := sub_pos.mpr hq_lt_one
        calc
          (∑ ρ ∈ ball m, g ρ)
              ≤ (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount * (q ^ (n₀ + 1) * (1 - q)⁻¹) := by
                    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) + εcount) :=
                      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
                    have hconst_nonneg : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount :=
                      mul_nonneg hpow_nonneg hCcount_nonneg
                    have hmult :
                        (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount *
                            (∑ i ∈ Finset.range t', q ^ (n₀ + 1 + i))
                          ≤ (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount *
                            (q ^ (n₀ + 1) * (1 - q)⁻¹) := by
                      simpa [mul_assoc] using
                        mul_le_mul_of_nonneg_left hgeom_le hconst_nonneg
                    exact le_trans hfinite_le hmult
          _ = (2 : ℝ) ^ ((1 : ℝ) + εcount) * Ccount * q / (1 - q) * q ^ n₀ := by
                    field_simp [hden_pos.ne']
                    ring
          _ = C * q ^ n₀ := by
                    simp [C, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
          _ = C * ((2 : ℝ) ^ n₀) ^ (εcount - 1) := by
                    simp [hqk]
      simpa [ball] using hfinal
  have hsum_le :
      (∑ ρ ∈ t, g ρ) ≤
        ∑ ρ ∈
            zerosBallFinset_of_entire
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m,
          g ρ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg htm ?_
    intro ρ _ _
    exact hg_nonneg ρ
  have hbound :
      (∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2) ≤
        C * ((2 : ℝ) ^ n₀) ^ (εcount - 1) := by
    calc
      (∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2) = ∑ ρ ∈ t, g ρ := hsum_eq
      _ ≤
          ∑ ρ ∈ zerosBallFinset_of_entire
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m,
            g ρ := hsum_le
      _ ≤ C * ((2 : ℝ) ^ n₀) ^ (εcount - 1) := hball
  -- Convert `((2^n₀)^(εcount-1))` to `q^n₀` and use `C*q^n₀ < ε`.
  have hqpow : q ^ n₀ = ((2 : ℝ) ^ n₀) ^ (εcount - 1) := by
    simpa [q] using (Real.rpow_pow_comm (x := (2 : ℝ)) (hx := by positivity) (εcount - 1) n₀)
  have hCq_lt : C * q ^ n₀ < ε := by
    have habs : |C * q ^ n₀| = C * q ^ n₀ := by
      have : 0 ≤ C * q ^ n₀ := by
        have : 0 ≤ q ^ n₀ := by positivity
        exact mul_nonneg hC_nonneg this
      rw [abs_of_nonneg this]
    have hlt : |C * q ^ n₀| < ε := hn₀_lt
    rwa [habs] at hlt
  have hsmall : C * ((2 : ℝ) ^ n₀) ^ (εcount - 1) < ε := by
    simpa [hqpow] using hCq_lt
  have hsum_nonneg :
      0 ≤ ∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro ρ hρ
    positivity
  have hnorm_lt :
      ‖∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2‖ < ε := by
    have hsum_lt :
        (∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2) < ε :=
      lt_of_le_of_lt hbound hsmall
    have habs_eq :
        |∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2| =
          ∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2 :=
      abs_of_nonneg hsum_nonneg
    have habs_lt :
        |∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2| < ε := by
      simpa [habs_eq] using hsum_lt
    simpa [Real.norm_eq_abs] using habs_lt
  exact hnorm_lt

/-! ### General-order summability at exponent `p + 1` -/

/-- **Summability of `∑ ord_ρ(f) / ‖ρ‖^(p+1)` from `order f ≤ lam`** where
`p = ⌊lam⌋₊`.

This is the general-order analogue of
`summable_analyticOrderNatAt_div_norm_sq_of_order_le_one`: given
`order f ≤ lam`, the multiplicity-weighted sum converges at the exponent
`⌊lam⌋₊ + 1` (which is strictly greater than `lam`, giving a geometric decay
ratio `< 1`).

The proof is the same dyadic shell argument as the order-1 version, but
with:
* `εcount := (p + 1 - lam) / 2` in place of `εcount := 1/2`, ensuring
  `lam + εcount < p + 1` so that `q := 2 ^ ((lam + εcount) - (p + 1))` is in
  `(0, 1)`;
* the exponent `p + 1` in place of `2`;
* the generalized weighted counting bound
  `sum_multiplicity_zeros_le_rpow_of_order_le` in place of
  `sum_multiplicity_zeros_le_rpow`. -/
theorem summable_analyticOrderNatAt_div_norm_pow_of_order_le
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f)
    {lam : ℝ} (hlam_nonneg : 0 ≤ lam) (hf_order_le : order f ≤ lam)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) :
    Summable (fun ρ : Z.Zero =>
      (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (Nat.floor lam + 1)) := by
  classical
  set p : ℕ := Nat.floor lam with hp_def
  have hlam_lt_p1 : lam < (p : ℝ) + 1 := by
    simpa [p, hp_def] using (Nat.lt_floor_add_one lam)
  -- Pick `εcount > 0` with `lam + εcount < p + 1`, i.e. the midpoint.
  set εcount : ℝ := ((p : ℝ) + 1 - lam) / 2 with hεcount_def
  have hεcount_pos : 0 < εcount := by
    have : 0 < (p : ℝ) + 1 - lam := sub_pos.mpr hlam_lt_p1
    simpa [εcount] using half_pos this
  have hεcount_lt_gap : lam + εcount < (p : ℝ) + 1 := by
    have heq : lam + ((p : ℝ) + 1 - lam) / 2 = (lam + ((p : ℝ) + 1)) / 2 := by ring
    rw [hεcount_def]; rw [heq]; linarith [hlam_lt_p1]
  -- Vanishing-tail criterion for summability.
  refine
    (summable_iff_vanishing_norm
        (f := fun ρ : Z.Zero =>
          (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (p + 1))).2 ?_
  intro ε hε
  -- Weighted counting bound at exponent `lam + εcount`.
  obtain ⟨Rcount, Ccount, hCcount_nonneg, hW_le⟩ :=
    Hadamard.OrderOne.sum_multiplicity_zeros_le_rpow_of_order_le (f := f) hf_entire hf_finite
      hf_order_le hlam_nonneg Z h_zeros_only h_inj h_z_ne_zero εcount hεcount_pos
  -- Pick a dyadic `2^nR ≥ max Rcount 1`.
  let R0 : ℝ := max Rcount 1
  have hR0_le : ∃ nR : ℕ, R0 ≤ (2 : ℝ) ^ nR := by
    have h : ∃ n : ℕ, R0 < (2 : ℝ) ^ n := by
      simpa using (pow_unbounded_of_one_lt R0 (by norm_num : (1 : ℝ) < 2))
    refine ⟨Nat.find h, le_of_lt (Nat.find_spec h)⟩
  obtain ⟨nR, hnR⟩ := hR0_le
  -- Geometric ratio `q := 2^((lam + εcount) - (p + 1))`, strictly in `(0, 1)`.
  let q : ℝ := (2 : ℝ) ^ ((lam + εcount) - ((p : ℝ) + 1))
  have hq_pos : 0 < q := by
    simpa [q] using Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hq_lt_one : q < 1 := by
    have hneg : (lam + εcount) - ((p : ℝ) + 1) < 0 := by linarith
    simpa [q] using Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) hneg
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  -- Geometric tail constant.
  let C : ℝ := (2 : ℝ) ^ (lam + εcount) * Ccount * q / (1 - q)
  have hC_nonneg : 0 ≤ C := by
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (lam + εcount) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
    have hden_pos : 0 < (1 - q) := sub_pos.mpr hq_lt_one
    exact div_nonneg (mul_nonneg (mul_nonneg hpow_nonneg hCcount_nonneg) hq_nonneg)
      (le_of_lt hden_pos)
  -- Pick `n₀` with `C * q^n₀ < ε`.
  have hlim : Tendsto (fun n : ℕ => C * q ^ n) atTop (nhds (0 : ℝ)) := by
    have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (nhds (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
    simpa [mul_zero] using (Tendsto.const_mul C hpow)
  have h_event : ∀ᶠ n : ℕ in atTop, |C * q ^ n| < ε := by
    have hball : Metric.ball (0 : ℝ) ε ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ hε
    simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, sub_zero] using hlim hball
  obtain ⟨N, hN⟩ := (eventually_atTop.1 h_event)
  let n₀ : ℕ := max nR N
  have hn₀_ge_nR : nR ≤ n₀ := le_max_left _ _
  have hn₀_ge_N : N ≤ n₀ := le_max_right _ _
  have hn₀_lt : |C * q ^ n₀| < ε := hN n₀ hn₀_ge_N
  -- Finite head: the dyadic ball `‖Z.z ρ‖ ≤ 2^(n₀+1)`.
  refine ⟨
    zerosBallFinset_of_entire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
      (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (n₀ + 1),
    ?_⟩
  intro t ht
  have hcond : ∀ ρ : Z.Zero, ρ ∈ t → (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖ := by
    intro ρ hρt
    have hnot :
        ρ ∉
          zerosBallFinset_of_entire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (n₀ + 1) :=
      (Finset.disjoint_left.1 ht) hρt
    have hnot' : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (n₀ + 1) := by
      simpa
        [mem_zerosBallFinset_of_entire_iff
          (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero)]
        using hnot
    exact lt_of_not_ge hnot'
  let g : Z.Zero → ℝ := fun ρ =>
    if (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖ then
      (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (p + 1)
    else 0
  have hg_nonneg : ∀ ρ : Z.Zero, 0 ≤ g ρ := by
    intro ρ
    by_cases hρ : (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖
    · have : 0 ≤ (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (p + 1) := by positivity
      simpa [g, hρ] using this
    · simp [g, hρ]
  have hsum_eq :
      (∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (p + 1)) = ∑ ρ ∈ t, g ρ := by
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    have hρ' := hcond ρ hρ
    simp [g, hρ']
  -- Enclose `t` in a dyadic ball `ball m` for some `m`.
  have ht_subset :
      ∃ m : ℕ,
        t ⊆
          zerosBallFinset_of_entire
            (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m := by
    classical
    by_cases ht0 : t = ∅
    · exact ⟨0, by simp [ht0]⟩
    · have ht_ne : t.Nonempty := Finset.nonempty_iff_ne_empty.2 ht0
      let R : ℝ := t.sup' ht_ne fun ρ : Z.Zero => ‖Z.z ρ‖
      have hR : ∀ ρ : Z.Zero, ρ ∈ t → ‖Z.z ρ‖ ≤ R := by
        intro ρ hρ
        exact Finset.le_sup' (f := fun ρ : Z.Zero => ‖Z.z ρ‖) hρ
      have hpow : ∃ m : ℕ, max R 1 < (2 : ℝ) ^ m := by
        simpa using pow_unbounded_of_one_lt (max R 1) (by norm_num : (1 : ℝ) < 2)
      refine ⟨Nat.find hpow, ?_⟩
      intro ρ hρt
      have hρ_leR : ‖Z.z ρ‖ ≤ R := hR ρ hρt
      have hρ_le : ‖Z.z ρ‖ ≤ max R 1 := le_trans hρ_leR (le_max_left _ _)
      have hmax_le : max R 1 ≤ (2 : ℝ) ^ Nat.find hpow := le_of_lt (Nat.find_spec hpow)
      have hρ_ball : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ Nat.find hpow := le_trans hρ_le hmax_le
      exact
        (mem_zerosBallFinset_of_entire_iff
          (hf_entire := hf_entire) (Z := Z)
          (h_zeros_only := h_zeros_only) (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) _ _).2
          hρ_ball
  rcases ht_subset with ⟨m, htm⟩
  -- Dyadic-shell bound for the "cumulative ball sum" of `g`.
  have hball :
      (∑ ρ ∈
          zerosBallFinset_of_entire
            (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m,
        g ρ)
        ≤ C * q ^ n₀ := by
    let w : Z.Zero → ℝ := fun ρ => (analyticOrderNatAt f (Z.z ρ) : ℝ)
    have hsub_ball :
        ∀ k : ℕ,
          zerosBallFinset_of_entire
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k ⊆
            zerosBallFinset_of_entire
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) := by
      intro k ρ hρ
      have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k :=
        (mem_zerosBallFinset_of_entire_iff
          (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k ρ).1 hρ
      have hk_le : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ k)
      exact
        (mem_zerosBallFinset_of_entire_iff
          (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) ρ).2 (le_trans hnorm hk_le)
    have hshell :
        ∀ k : ℕ, n₀ + 1 ≤ k →
          (∑ ρ ∈
              zerosBallFinset_of_entire
                    (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
                    (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) \
                zerosBallFinset_of_entire
                    (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
                    (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k,
              g ρ)
            ≤ (2 : ℝ) ^ (lam + εcount) * Ccount * q ^ k := by
      intro k hk
      let ball : ℕ → Finset Z.Zero := fun t =>
        zerosBallFinset_of_entire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) t
      let diff : Finset Z.Zero := ball (k + 1) \ ball k
      have hk_pow_le : (2 : ℝ) ^ (n₀ + 1) ≤ (2 : ℝ) ^ k :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
      have hdiff_simp :
          (∑ ρ ∈ diff, g ρ) = ∑ ρ ∈ diff, w ρ / ‖Z.z ρ‖ ^ (p + 1) := by
        refine Finset.sum_congr rfl ?_
        intro ρ hρ
        have hnot : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k := by
          intro hle
          have : ρ ∈ ball k :=
            (mem_zerosBallFinset_of_entire_iff
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k ρ).2 hle
          exact (Finset.mem_sdiff.1 hρ).2 this
        have hlt : (2 : ℝ) ^ k < ‖Z.z ρ‖ := lt_of_not_ge hnot
        have hcond' : (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖ :=
          lt_of_lt_of_le (hk_pow_le.trans_lt hlt) (le_rfl)
        simp [g, w, hcond']
      have hterm_le :
          ∀ ρ, ρ ∈ diff → w ρ / ‖Z.z ρ‖ ^ (p + 1) ≤ w ρ / ((2 : ℝ) ^ k) ^ (p + 1) := by
        intro ρ hρ
        have hnot : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k := by
          intro hle
          have : ρ ∈ ball k :=
            (mem_zerosBallFinset_of_entire_iff
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k ρ).2 hle
          exact (Finset.mem_sdiff.1 hρ).2 this
        have hk_le_norm : (2 : ℝ) ^ k ≤ ‖Z.z ρ‖ := le_of_lt (lt_of_not_ge hnot)
        have hk2_pos : 0 < ((2 : ℝ) ^ k) ^ (p + 1) := by positivity
        have hk2_le : ((2 : ℝ) ^ k) ^ (p + 1) ≤ ‖Z.z ρ‖ ^ (p + 1) :=
          pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) hk_le_norm (p + 1)
        have hw_nonneg : 0 ≤ w ρ := by positivity [w]
        have hfrac : (1 : ℝ) / ‖Z.z ρ‖ ^ (p + 1) ≤ (1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1) := by
          simpa [one_div, inv_pow] using (one_div_le_one_div_of_le hk2_pos hk2_le)
        simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left hfrac hw_nonneg)
      have hsum_le :
          (∑ ρ ∈ diff, w ρ / ‖Z.z ρ‖ ^ (p + 1)) ≤ ∑ ρ ∈ diff, w ρ / ((2 : ℝ) ^ k) ^ (p + 1) :=
        Finset.sum_le_sum hterm_le
      have hRcount_le : Rcount ≤ (2 : ℝ) ^ (k + 1) := by
        have hRcount_le_R0 : Rcount ≤ R0 := le_max_left _ _
        have hnR_le_k : nR ≤ k := le_trans hn₀_ge_nR (le_trans (Nat.le_succ n₀) hk)
        have hnR_le_k1 : nR ≤ k + 1 := Nat.le_succ_of_le hnR_le_k
        have hpow : (2 : ℝ) ^ nR ≤ (2 : ℝ) ^ (k + 1) :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnR_le_k1
        exact le_trans (le_trans hRcount_le_R0 hnR) hpow
      have hcount_ball :
          (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0) ≤
            Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + εcount) :=
        hW_le ((2 : ℝ) ^ (k + 1)) hRcount_le
      have hball_finsum :
          (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0) =
            ∑ ρ ∈ ball (k + 1), w ρ := by
        have hsupp :
            Function.support (fun ρ : Z.Zero => if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0) ⊆
              ball (k + 1) := by
          intro ρ hρ
          have hne : (if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0) ≠ 0 :=
            Function.mem_support.1 hρ
          have hle : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) := by
            by_contra hle; apply hne; simp [hle]
          exact
            (mem_zerosBallFinset_of_entire_iff
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) ρ).2 hle
        have this :=
          finsum_eq_sum_of_support_subset
            (f := fun ρ : Z.Zero => if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0)
            (s := ball (k + 1)) hsupp
        have hsum_if :
            (∑ ρ ∈ ball (k + 1), if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0) =
              ∑ ρ ∈ ball (k + 1), w ρ := by
          refine Finset.sum_congr rfl ?_
          intro ρ hρ
          have hle : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) :=
            (mem_zerosBallFinset_of_entire_iff
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) ρ).1 hρ
          simp [hle]
        simpa [hsum_if] using this
      have hsum_ball :
          (∑ ρ ∈ ball (k + 1), w ρ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + εcount) := by
        simpa [hball_finsum] using hcount_ball
      have hsum_mult_diff :
          (∑ ρ ∈ diff, w ρ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + εcount) := by
        have hdiff_le_ball :
            (∑ ρ ∈ diff, w ρ) ≤ ∑ ρ ∈ ball (k + 1), w ρ := by
          have hw_nonneg : ∀ ρ ∈ ball (k + 1), ρ ∉ diff → 0 ≤ w ρ := by
            intro ρ _ _
            positivity [w]
          exact
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.sdiff_subset : diff ⊆ ball (k + 1)) hw_nonneg
        exact le_trans hdiff_le_ball hsum_ball
      -- Put everything together.
      have hpow_rat :
          ((2 : ℝ) ^ k) ^ ((lam + εcount) - ((p : ℝ) + 1)) =
            ((2 : ℝ) ^ k) ^ (lam + εcount) / ((2 : ℝ) ^ k) ^ (p + 1 : ℕ) := by
        have hk_pos : 0 < (2 : ℝ) ^ k := by positivity
        have hsub : (lam + εcount) - ((p : ℝ) + 1) = (lam + εcount) - (↑(p + 1) : ℝ) := by
          push_cast; ring
        have hnat : ((2 : ℝ) ^ k) ^ (p + 1 : ℕ) = ((2 : ℝ) ^ k) ^ ((p + 1 : ℕ) : ℝ) := by
          simpa using (Real.rpow_natCast ((2 : ℝ) ^ k) (p + 1)).symm
        rw [hnat]
        rw [hsub]
        exact Real.rpow_sub hk_pos (lam + εcount) ((p + 1 : ℕ) : ℝ)
      have hqk : q ^ k = ((2 : ℝ) ^ k) ^ ((lam + εcount) - ((p : ℝ) + 1)) := by
        simpa [q] using
          (Real.rpow_pow_comm (x := (2 : ℝ)) (hx := by positivity)
            ((lam + εcount) - ((p : ℝ) + 1)) k)
      have hrewrite :
          Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + εcount) *
              ((1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1))
            = (2 : ℝ) ^ (lam + εcount) * Ccount * q ^ k := by
        have hpow_succ : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
          simp [pow_succ, mul_comm]
        have hpowk_nonneg : 0 ≤ (2 : ℝ) ^ k := by positivity
        have h2_nonneg : (0 : ℝ) ≤ 2 := by norm_num
        calc
          Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + εcount) *
              ((1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1))
              =
              Ccount * ((2 * (2 : ℝ) ^ k) ^ (lam + εcount)) *
                ((1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1)) := by
                simp [hpow_succ]
          _ =
              Ccount * ((2 : ℝ) ^ (lam + εcount) * ((2 : ℝ) ^ k) ^ (lam + εcount)) *
                  ((1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1)) := by
                have hsplit :
                    ((2 : ℝ) * (2 : ℝ) ^ k) ^ (lam + εcount) =
                      (2 : ℝ) ^ (lam + εcount) * ((2 : ℝ) ^ k) ^ (lam + εcount) := by
                  simpa using
                    (Real.mul_rpow (x := (2 : ℝ)) (y := (2 : ℝ) ^ k) (z := lam + εcount)
                      h2_nonneg hpowk_nonneg)
                simp [hsplit, mul_assoc,
                  -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
          _ =
              (2 : ℝ) ^ (lam + εcount) * Ccount *
                  (((2 : ℝ) ^ k) ^ (lam + εcount) / ((2 : ℝ) ^ k) ^ (p + 1)) := by
                simp [div_eq_mul_inv, mul_assoc, mul_comm,
                  -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
          _ = (2 : ℝ) ^ (lam + εcount) * Ccount *
                (((2 : ℝ) ^ k) ^ ((lam + εcount) - ((p : ℝ) + 1))) := by
                rw [hpow_rat]
          _ = (2 : ℝ) ^ (lam + εcount) * Ccount * q ^ k := by
                rw [← hqk]
      calc
        (∑ ρ ∈ diff, g ρ) = ∑ ρ ∈ diff, w ρ / ‖Z.z ρ‖ ^ (p + 1) := hdiff_simp
        _ ≤ ∑ ρ ∈ diff, w ρ / ((2 : ℝ) ^ k) ^ (p + 1) := hsum_le
        _ = (∑ ρ ∈ diff, w ρ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1)) := by
              simp [div_eq_mul_inv, Finset.sum_mul]
        _ ≤ (Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + εcount)) *
              ((1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1)) := by
              have hconst_nonneg : 0 ≤ (1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1) := by positivity
              exact mul_le_mul_of_nonneg_right hsum_mult_diff hconst_nonneg
        _ = (2 : ℝ) ^ (lam + εcount) * Ccount * q ^ k := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hrewrite
    -- Sum the shells from `n₀ + 1` through `m - 1`.
    by_cases hm : m ≤ n₀ + 1
    · have hsum0 :
          (∑ ρ ∈
              zerosBallFinset_of_entire
                (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
                (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m,
            g ρ) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro ρ hρ
        have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ m :=
          (mem_zerosBallFinset_of_entire_iff
            (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m ρ).1 hρ
        have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (n₀ + 1) :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
        have : ¬ (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖ := not_lt_of_ge (le_trans hnorm hpow)
        simp [g, this]
      have hrhs_nonneg : 0 ≤ C * q ^ n₀ := mul_nonneg hC_nonneg (by positivity)
      simpa [hsum0] using hrhs_nonneg
    · have hm_ge : n₀ + 1 < m := lt_of_not_ge hm
      let ball : ℕ → Finset Z.Zero := fun t =>
        zerosBallFinset_of_entire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) t
      set t' : ℕ := m - (n₀ + 1) with ht'_def
      have ht'_pos : 0 < t' := Nat.sub_pos_of_lt hm_ge
      have hm_eq : m = n₀ + 1 + t' := (Nat.add_sub_cancel' (le_of_lt hm_ge)).symm
      have hind :
          ∀ t : ℕ,
            (∑ ρ ∈ ball (n₀ + 1 + t), g ρ) ≤
              (2 : ℝ) ^ (lam + εcount) * Ccount *
                (∑ i ∈ Finset.range t, q ^ (n₀ + 1 + i)) := by
        intro t
        induction t using Nat.rec with
        | zero =>
            have hsum0 :
                (∑ ρ ∈ ball (n₀ + 1), g ρ) = 0 := by
              refine Finset.sum_eq_zero ?_
              intro ρ hρ
              have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (n₀ + 1) :=
                (mem_zerosBallFinset_of_entire_iff
                  (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
                  (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (n₀ + 1) ρ).1 hρ
              have : ¬ (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖ := not_lt_of_ge hnorm
              simp [g, this]
            simp [ball, hsum0]
        | succ j ih =>
            set k : ℕ := n₀ + 1 + j
            have hk : n₀ + 1 ≤ k := Nat.le_add_right _ _
            have hsub : ball k ⊆ ball (k + 1) := by
              simpa [ball] using hsub_ball k
            have hdecomp :=
              (Finset.sum_sdiff (s₁ := ball k) (s₂ := ball (k + 1)) (f := g) hsub).symm
            have hshell_le :
                (∑ ρ ∈ ball (k + 1) \ ball k, g ρ)
                  ≤ (2 : ℝ) ^ (lam + εcount) * Ccount * q ^ k := hshell k hk
            have hgeom :
                (∑ i ∈ Finset.range (j + 1), q ^ (n₀ + 1 + i))
                  = (∑ i ∈ Finset.range j, q ^ (n₀ + 1 + i)) + q ^ k := by
              simpa [k, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (Finset.sum_range_succ (f := fun i => q ^ (n₀ + 1 + i)) j)
            have ih' :
                (∑ ρ ∈ ball k, g ρ) ≤
                  (2 : ℝ) ^ (lam + εcount) * Ccount *
                    (∑ i ∈ Finset.range j, q ^ (n₀ + 1 + i)) := by
              simpa [k, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih
            calc
              (∑ ρ ∈ ball (k + 1), g ρ)
                  = (∑ ρ ∈ ball (k + 1) \ ball k, g ρ) + (∑ ρ ∈ ball k, g ρ) := by
                        simpa [k, add_assoc, add_comm, add_left_comm] using hdecomp
              _ ≤ (2 : ℝ) ^ (lam + εcount) * Ccount * q ^ k +
                    (2 : ℝ) ^ (lam + εcount) * Ccount *
                      (∑ i ∈ Finset.range j, q ^ (n₀ + 1 + i)) := by
                        gcongr
              _ = (2 : ℝ) ^ (lam + εcount) * Ccount *
                    ((∑ i ∈ Finset.range j, q ^ (n₀ + 1 + i)) + q ^ k) := by
                        ring
              _ = (2 : ℝ) ^ (lam + εcount) * Ccount *
                    (∑ i ∈ Finset.range (j + 1), q ^ (n₀ + 1 + i)) := by
                        simp [hgeom]
      have hfinite_le :
          (∑ ρ ∈ ball m, g ρ) ≤
            (2 : ℝ) ^ (lam + εcount) * Ccount *
              (∑ i ∈ Finset.range t', q ^ (n₀ + 1 + i)) := by
        simpa [hm_eq, ball] using hind t'
      have hgeom_le :
          (∑ i ∈ Finset.range t', q ^ (n₀ + 1 + i)) ≤ (q ^ (n₀ + 1)) * (1 - q)⁻¹ := by
        have hsum : Summable (fun i : ℕ => q ^ i) :=
          summable_geometric_of_lt_one (le_of_lt hq_pos) hq_lt_one
        have hsum' : Summable (fun i : ℕ => q ^ (n₀ + 1) * q ^ i) :=
          hsum.mul_left (q ^ (n₀ + 1))
        have hnonneg : ∀ i : ℕ, 0 ≤ q ^ (n₀ + 1) * q ^ i := by
          intro i; positivity
        have hle_tsum :
            (∑ i ∈ Finset.range t', q ^ (n₀ + 1) * q ^ i) ≤ ∑' i : ℕ, q ^ (n₀ + 1) * q ^ i := by
          refine
            Summable.sum_le_tsum
              (s := Finset.range t')
              (f := fun i : ℕ => q ^ (n₀ + 1) * q ^ i) ?_ hsum'
          intro i hi; exact hnonneg i
        have hpow_add : ∀ i : ℕ, q ^ (n₀ + 1 + i) = q ^ (n₀ + 1) * q ^ i := by
          intro i; simp [pow_add, mul_assoc]
        have hsum_eq :
            (∑ i ∈ Finset.range t', q ^ (n₀ + 1 + i)) =
              (∑ i ∈ Finset.range t', q ^ (n₀ + 1) * q ^ i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi; simp [hpow_add i]
        have htsum_eq :
            (∑' i : ℕ, q ^ (n₀ + 1) * q ^ i) = (q ^ (n₀ + 1)) * (1 - q)⁻¹ := by
          have hgeom0 : (∑' i : ℕ, q ^ i) = (1 - q)⁻¹ :=
            tsum_geometric_of_lt_one (h₁ := le_of_lt hq_pos) (h₂ := hq_lt_one)
          calc
            (∑' i : ℕ, q ^ (n₀ + 1) * q ^ i) = (q ^ (n₀ + 1)) * ∑' i : ℕ, q ^ i := by
                rw [tsum_mul_left]
            _ = (q ^ (n₀ + 1)) * (1 - q)⁻¹ := by rw [hgeom0]
        calc
          (∑ i ∈ Finset.range t', q ^ (n₀ + 1 + i))
              = (∑ i ∈ Finset.range t', q ^ (n₀ + 1) * q ^ i) := hsum_eq
          _ ≤ ∑' i : ℕ, q ^ (n₀ + 1) * q ^ i := hle_tsum
          _ = (q ^ (n₀ + 1)) * (1 - q)⁻¹ := htsum_eq
      have hden_pos : 0 < (1 - q) := sub_pos.mpr hq_lt_one
      have hfinal :
          (∑ ρ ∈ ball m, g ρ) ≤ C * q ^ n₀ := by
        calc
          (∑ ρ ∈ ball m, g ρ)
              ≤ (2 : ℝ) ^ (lam + εcount) * Ccount * (q ^ (n₀ + 1) * (1 - q)⁻¹) := by
                have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (lam + εcount) :=
                  Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
                have hconst_nonneg : 0 ≤ (2 : ℝ) ^ (lam + εcount) * Ccount :=
                  mul_nonneg hpow_nonneg hCcount_nonneg
                have hmult :
                    (2 : ℝ) ^ (lam + εcount) * Ccount *
                        (∑ i ∈ Finset.range t', q ^ (n₀ + 1 + i))
                      ≤ (2 : ℝ) ^ (lam + εcount) * Ccount *
                        (q ^ (n₀ + 1) * (1 - q)⁻¹) := by
                  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hgeom_le hconst_nonneg
                exact le_trans hfinite_le hmult
          _ = (2 : ℝ) ^ (lam + εcount) * Ccount * q / (1 - q) * q ^ n₀ := by
                have hqsucc : q ^ (n₀ + 1) = q ^ n₀ * q := by
                  simp [pow_succ]
                rw [hqsucc]
                field_simp [hden_pos.ne']
          _ = C * q ^ n₀ := by
                simp [C, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
      simpa [ball] using hfinal
  have hsum_le :
      (∑ ρ ∈ t, g ρ) ≤
        ∑ ρ ∈
            zerosBallFinset_of_entire
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m,
          g ρ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg htm ?_
    intro ρ _ _
    exact hg_nonneg ρ
  have hbound :
      (∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (p + 1)) ≤ C * q ^ n₀ := by
    calc
      (∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (p + 1)) = ∑ ρ ∈ t, g ρ := hsum_eq
      _ ≤ _ := hsum_le
      _ ≤ C * q ^ n₀ := hball
  have hCq_lt : C * q ^ n₀ < ε := by
    have habs : |C * q ^ n₀| = C * q ^ n₀ := by
      have : 0 ≤ C * q ^ n₀ := mul_nonneg hC_nonneg (by positivity)
      rw [abs_of_nonneg this]
    have hlt : |C * q ^ n₀| < ε := hn₀_lt
    rwa [habs] at hlt
  have hsum_nonneg :
      0 ≤ ∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (p + 1) := by
    refine Finset.sum_nonneg ?_
    intro ρ _
    positivity
  have hnorm_lt :
      ‖∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (p + 1)‖ < ε := by
    have hsum_lt :
        (∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (p + 1)) < ε :=
      lt_of_le_of_lt hbound hCq_lt
    have habs_eq :
        |∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (p + 1)| =
          ∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (p + 1) :=
      abs_of_nonneg hsum_nonneg
    have habs_lt :
        |∑ ρ ∈ t, (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (p + 1)| < ε := by
      simpa [habs_eq] using hsum_lt
    simpa [Real.norm_eq_abs] using habs_lt
  exact hnorm_lt

end OrderOne

end Hadamard
