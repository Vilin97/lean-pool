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

open Hadamard.DyadicBounds

/-! ### Dyadic ball finsets (no summability hypothesis) -/

theorem zerosBallFinite_of_entire
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (Z : ZeroSet f)
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

/-- The finite set of indexed zeros of an entire function in the closed disk of radius `2 ^ n`. -/
noncomputable def zerosBallFinsetOfEntire
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (Z : ZeroSet f)
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (n : ℕ) : Finset Z.Zero :=
  (zerosBallFinite_of_entire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
        (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) n).toFinset

@[simp]
lemma mem_zerosBallFinset_of_entire_iff
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (Z : ZeroSet f)
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (n : ℕ) (ρ : Z.Zero) :
    ρ ∈ zerosBallFinsetOfEntire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) n ↔
      ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n := by
  classical
  simp [zerosBallFinsetOfEntire]

/-! ### Main summability lemma -/

/-! ### General-order summability at exponent `p + 1` -/

/-- **Summability of `∑ ord_ρ(f) / ‖ρ‖^(p+1)` from `order f ≤ lam`** where
`p = ⌊lam⌋₊`.

This is the general-order analogue of
`summable_analyticOrderNatAt_div_norm_sq_of_order_le_one`: given
`order f ≤ lam`, the multiplicity-weighted sum converges at the exponent
`⌊lam⌋₊ + 1` (which is strictly greater than `lam`, giving a geometric decay
ratio `< 1`).

The proof uses the weighted dyadic shell argument with:
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
    (Z : ZeroSet f)
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
    zerosBallFinsetOfEntire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
      (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (n₀ + 1),
    ?_⟩
  intro t ht
  have hcond : ∀ ρ : Z.Zero, ρ ∈ t → (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖ := by
    intro ρ hρt
    have hnot :
        ρ ∉
          zerosBallFinsetOfEntire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
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
          zerosBallFinsetOfEntire
            (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m := by
    exact dyadic_ball_cofinal Z.z _
      (mem_zerosBallFinset_of_entire_iff hf_entire Z h_zeros_only h_inj h_z_ne_zero) t
  rcases ht_subset with ⟨m, htm⟩
  -- Dyadic-shell bound for the "cumulative ball sum" of `g`.
  have hball :
      (∑ ρ ∈
          zerosBallFinsetOfEntire
            (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m,
        g ρ)
        ≤ C * q ^ n₀ := by
    let w : Z.Zero → ℝ := fun ρ => (analyticOrderNatAt f (Z.z ρ) : ℝ)
    have hsub_ball :
        ∀ k : ℕ,
          zerosBallFinsetOfEntire
              (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
              (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k ⊆
            zerosBallFinsetOfEntire
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
              zerosBallFinsetOfEntire
                    (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
                    (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) \
                zerosBallFinsetOfEntire
                    (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
                    (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k,
              g ρ)
            ≤ (2 : ℝ) ^ (lam + εcount) * Ccount * q ^ k := by
      intro k hk
      let ball : ℕ → Finset Z.Zero := fun t =>
        zerosBallFinsetOfEntire (hf_entire := hf_entire) (Z := Z) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) t
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
            ∑ ρ ∈ ball (k + 1), w ρ :=
        cutoff_finsum_eq_sum (ball (k + 1)) _ w
          (mem_zerosBallFinset_of_entire_iff hf_entire Z h_zeros_only h_inj h_z_ne_zero (k + 1))
      have hsum_ball :
          (∑ ρ ∈ ball (k + 1), w ρ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + εcount) := by
        simpa [hball_finsum] using hcount_ball
      exact dyadic_shell_sum_bound Z.z w (fun ρ => Nat.cast_nonneg _) ball
        (mem_zerosBallFinset_of_entire_iff hf_entire Z h_zeros_only h_inj h_z_ne_zero)
        p n₀ k hk Ccount lam εcount hsum_ball
    apply sum_le_of_geometric_shells _ g ((2 : ℝ) ^ (lam + εcount) * Ccount) q
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hCcount_nonneg)
      hq_pos hq_lt_one n₀ m hsub_ball _ hshell
    intro k hk
    apply Finset.sum_eq_zero
    intro ρ hρ
    have hnorm := (mem_zerosBallFinset_of_entire_iff hf_entire Z h_zeros_only h_inj
      h_z_ne_zero k ρ).1 hρ
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    simp only [g, not_lt_of_ge (hnorm.trans hpow), ↓reduceIte]
  have hsum_le :
      (∑ ρ ∈ t, g ρ) ≤
        ∑ ρ ∈
            zerosBallFinsetOfEntire
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
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun ρ _ => by positivity)]
  exact hbound.trans_lt ((le_abs_self _).trans_lt hn₀_lt)

theorem summable_analyticOrderNatAt_div_norm_sq_of_order_le_one
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) (hf_order_le : order f ≤ 1)
    (Z : ZeroSet f)
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) :
    Summable (fun ρ : Z.Zero => (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2) := by
  simpa using summable_analyticOrderNatAt_div_norm_pow_of_order_le hf_entire hf_finite
    (lam := 1) (by norm_num) hf_order_le Z h_zeros_only h_inj h_z_ne_zero

end OrderOne

end Hadamard
