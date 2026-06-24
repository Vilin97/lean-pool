/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import LeanPool.LeanModularForms.Modularforms.SerreDerivativeSlash
public import LeanPool.LeanModularForms.Modularforms.DimensionFormulas
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # EisensteinAsymptotics -/


@[expose] public section

/-!
# Asymptotic Behavior of Eisenstein Series

This file establishes the asymptotic behavior of Eisenstein series as z → i∞,
and constructs the ModularForm structures for Serre derivatives.

## Main definitions

* `serreDE₄ModularForm`, `serreDE₆ModularForm`, `serreDE₂ModularForm` :
  Package serre derivatives as modular forms

## Main results

* `D_tendsto_zero_of_tendsto_const` : Cauchy estimate: D f → 0 at i∞ if f is bounded
* `E₂_tendsto_one_atImInfty` : E₂ → 1 at i∞
* `serre_DE₄_tendsto_atImInfty`, `serre_DE₆_tendsto_atImInfty`,
  `serre_DE₂_tendsto_atImInfty` : Limits of serre derivatives (for determining scalars)
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap
open ModularForm hiding E₄ E₆
open EisensteinSeries TopologicalSpace Set MeasureTheory
open Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped ModularForm MatrixGroups Manifold Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

/-! ## Limits of Eisenstein series at infinity -/

/-- exp(-c * y) → 0 as y → +∞ (for c > 0). -/
lemma tendsto_exp_neg_mul_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun y : ℝ => Real.exp (-c * y)) Filter.atTop (nhds 0) := by
  have : Filter.Tendsto (fun y => -c * y) Filter.atTop Filter.atBot := by
    simpa using Filter.tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc)
  exact Real.tendsto_exp_atBot.comp this

/-- If f = O(exp(-c * Im z)) as z → i∞ for c > 0, then f → 0 at i∞. -/
lemma tendsto_zero_of_exp_decay {f : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hO : f =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    Filter.Tendsto f atImInfty (nhds 0) :=
  hO.trans_tendsto ((tendsto_exp_neg_mul_atTop hc).comp tendsto_im_atImInfty)

/-- A modular form tends to its value at infinity as z → i∞. -/
lemma modular_form_tendsto_atImInfty {k : ℤ} (f : ModularForm (Gamma 1) k) :
    Filter.Tendsto f.toFun atImInfty (nhds ((qExpansion 1 f).coeff 0)) := by
  obtain ⟨c, hc, hO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
  rw [qExpansion_coeff_zero (f := ⇑f) (by norm_num : (0 : ℝ) < 1)
    (ModularFormClass.analyticAt_cuspFunction_zero f one_pos (by simp))
    (SlashInvariantFormClass.periodic_comp_ofComplex f (by simp))]
  simpa using (tendsto_zero_of_exp_decay hc hO).add_const (valueAtInfty f.toFun)

/-- E₂ - 1 = O(exp(-2π·Im z)) at infinity. -/
lemma E₂_sub_one_isBigO_exp : (fun z : ℍ => E₂ z - 1) =O[atImInfty]
    fun z => Real.exp (-(2 * π) * z.im) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨192, Filter.eventually_atImInfty.mpr ⟨1, fun z hz => ?_⟩⟩
  -- E₂ z - 1 = -24 * ∑' n, n·qⁿ/(1-qⁿ)
  have hsub : E₂ z - 1 = -24 * ∑' (n : ℕ+), ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
      (1 - cexp (2 * π * Complex.I * ↑n * ↑z)) := by rw [E₂_eq z]; ring
  rw [hsub, norm_mul, show ‖(-24 : ℂ)‖ = 24 by simp, Real.norm_of_nonneg (Real.exp_pos _).le]
  set q : ℂ := cexp (2 * π * Complex.I * z)
  -- Rewrite sum in terms of q^n
  simp_rw [show ∀ n : ℕ, cexp (2 * π * Complex.I * n * z) = q ^ n by
    intro n; rw [← Complex.exp_nat_mul]; congr 1; ring]
  -- Key bounds: ‖q‖ ≤ exp(-2π) < 1/2
  have hq_bound : ‖q‖ ≤ Real.exp (-2 * π) := norm_exp_two_pi_I_le_exp_neg_two_pi z hz
  have hexp_lt_half : Real.exp (-2 * π) < 1 / 2 := by
    have : 1 < 2 * π := by nlinarith [pi_gt_three]
    calc Real.exp (-2 * π) < Real.exp (-1) := Real.exp_strictMono (by linarith)
      _ < 1 / 2 := by
        rw [Real.exp_neg, one_div, inv_lt_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2)]
        have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
  have hq_lt_half : ‖q‖ < 1 / 2 := lt_of_le_of_lt hq_bound hexp_lt_half
  have hone_sub_q_gt_half : 1 / 2 < 1 - ‖q‖ := by linarith
  -- Use norm_tsum_logDeriv_expo_le and bound r/(1-r)³ ≤ 8r for r < 1/2
  have htsum_bound := norm_tsum_logDeriv_expo_le (norm_exp_two_pi_I_lt_one z)
  have hsum_le_8q : ‖q‖ / (1 - ‖q‖) ^ 3 ≤ 8 * ‖q‖ := by
    have h1 : (1 / 8 : ℝ) ≤ (1 - ‖q‖) ^ 3 := by nlinarith [sq_nonneg (1 - ‖q‖)]
    calc ‖q‖ / (1 - ‖q‖) ^ 3 ≤ ‖q‖ / (1 / 8) := by
          apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) h1
      _ = 8 * ‖q‖ := by ring
  have hq_eq_exp : ‖q‖ = Real.exp (-2 * π * z.im) := by
    have hre : (2 * ↑π * Complex.I * (z : ℂ)).re = -2 * π * z.im := by
      rw [show (2 : ℂ) * ↑π * Complex.I * z = Complex.I * (2 * π * z) by ring]
      simp [Complex.I_re, Complex.I_im, mul_comm]
    rw [Complex.norm_exp, hre]
  calc 24 * ‖∑' n : ℕ+, ↑n * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ 24 * (‖q‖ / (1 - ‖q‖) ^ 3) := by gcongr
    _ ≤ 24 * (8 * ‖q‖) := by gcongr
    _ = 192 * ‖q‖ := by ring
    _ = 192 * Real.exp (-(2 * π) * z.im) := by rw [hq_eq_exp]; ring_nf

/-- E₂ → 1 at i∞. -/
lemma E₂_tendsto_one_atImInfty : Filter.Tendsto E₂ atImInfty (nhds 1) := by
  simpa using (tendsto_zero_of_exp_decay (by positivity : 0 < 2 * π)
    E₂_sub_one_isBigO_exp).add_const 1

/-- E₄ → 1 at i∞. -/
lemma E₄_tendsto_one_atImInfty : Filter.Tendsto E₄.toFun atImInfty (nhds 1) :=
  E4_q_exp_zero ▸ modular_form_tendsto_atImInfty E₄

/-- E₆ → 1 at i∞. -/
lemma E₆_tendsto_one_atImInfty : Filter.Tendsto E₆.toFun atImInfty (nhds 1) :=
  E6_q_exp_zero ▸ modular_form_tendsto_atImInfty E₆

/-! ## Boundedness lemmas -/

/-- E₆ is bounded at infinity (as a modular form). -/
lemma E₆_isBoundedAtImInfty : IsBoundedAtImInfty E₆.toFun :=
  ModularFormClass.bdd_at_infty E₆

/-- serreD 1 E₂ is bounded at infinity. -/
lemma serre_DE₂_isBoundedAtImInfty : IsBoundedAtImInfty (serreD 1 E₂) :=
  serre_D_isBoundedAtImInfty_of_bounded 1 E₂_holo' E₂_isBoundedAtImInfty

/-- D E₄ is bounded at infinity (by Cauchy estimate: D f → 0 when f is bounded). -/
lemma DE₄_isBoundedAtImInfty : IsBoundedAtImInfty (D E₄.toFun) :=
  D_isBoundedAtImInfty_of_bounded E₄.holo' E₄_isBoundedAtImInfty

/-- serreD 4 E₄ is bounded at infinity. -/
lemma serre_DE₄_isBoundedAtImInfty : IsBoundedAtImInfty (serreD 4 E₄.toFun) :=
  serre_D_isBoundedAtImInfty_of_bounded 4 E₄.holo' E₄_isBoundedAtImInfty

/-! ## Construction of ModularForm from serreD -/

/-- serreD 4 E₄ is a weight-6 modular form. -/
def serreDE₄ModularForm : ModularForm (CongruenceSubgroup.Gamma 1) 6 :=
  serreDModularForm 4 E₄

/-- serreD 6 E₆ is bounded at infinity. -/
lemma serre_DE₆_isBoundedAtImInfty : IsBoundedAtImInfty (serreD 6 E₆.toFun) :=
  serre_D_isBoundedAtImInfty_of_bounded 6 E₆.holo' E₆_isBoundedAtImInfty

/-- serreD 6 E₆ is a weight-8 modular form. -/
def serreDE₆ModularForm : ModularForm (CongruenceSubgroup.Gamma 1) 8 :=
  serreDModularForm 6 E₆

/-! ## Limit of serreD at infinity (for determining scalar) -/

/-- General limit: if `f → c` at i∞ and f is holomorphic and bounded, then `serreD k f → -k*c/12`.

This is the continuous mapping theorem applied to `serreD k f = D f - (k/12) * E₂ * f`:
- D f → 0 (Cauchy estimate from boundedness)
- E₂ → 1
- f → c
Therefore `serreD k f → 0 - (k/12) * 1 * c = -k*c/12`. -/
lemma serre_D_tendsto_of_tendsto (k : ℤ) (f : ℍ → ℂ) (c : ℂ)
    (hf_holo : MDiff f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds c)) :
    Filter.Tendsto (serreD k f) atImInfty (nhds (-(k : ℂ) * c / 12)) := by
  rw [show serreD k f = fun z => D f z - (k : ℂ) * 12⁻¹ * E₂ z * f z from serre_D_eq k f]
  have hD := D_tendsto_zero_of_isBoundedAtImInfty hf_holo hf_bdd
  have hlim : (0 : ℂ) - (k : ℂ) * 12⁻¹ * 1 * c = -(k : ℂ) * c / 12 := by ring
  rw [← hlim]
  refine hD.sub ?_
  convert (tendsto_const_nhds (x := (k : ℂ) * 12⁻¹)).mul
    (E₂_tendsto_one_atImInfty.mul hf_lim) using 1 <;> ring_nf

/-- Special case: if `f → 1` at i∞, then `serreD k f → -k/12`. -/
lemma serre_D_tendsto_neg_k_div_12 (k : ℤ) (f : ℍ → ℂ)
    (hf_holo : MDiff f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds 1)) :
    Filter.Tendsto (serreD k f) atImInfty (nhds (-(k : ℂ) / 12)) := by
  simpa using serre_D_tendsto_of_tendsto k f 1 hf_holo hf_bdd hf_lim

/-- Special case: if `f → 0` at i∞, then `serreD k f → 0`. -/
lemma serre_D_tendsto_zero_of_tendsto_zero (k : ℤ) (f : ℍ → ℂ)
    (hf_holo : MDiff f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds 0)) :
    Filter.Tendsto (serreD k f) atImInfty (nhds 0) := by
  simpa using serre_D_tendsto_of_tendsto k f 0 hf_holo hf_bdd hf_lim

/-- serreD 4 E₄ → -1/3 at i∞. -/
lemma serre_DE₄_tendsto_atImInfty :
    Filter.Tendsto (serreD 4 E₄.toFun) atImInfty (nhds (-(1/3 : ℂ))) := by
  convert serre_D_tendsto_neg_k_div_12 4 E₄.toFun E₄.holo'
    (ModularFormClass.bdd_at_infty E₄) E₄_tendsto_one_atImInfty using 2
  · rw [show ((4 : ℤ) : ℂ) = 4 from by norm_num]
  · norm_num

/-- serreD 6 E₆ → -1/2 at i∞. -/
lemma serre_DE₆_tendsto_atImInfty :
    Filter.Tendsto (serreD 6 E₆.toFun) atImInfty (nhds (-(1/2 : ℂ))) := by
  convert serre_D_tendsto_neg_k_div_12 6 E₆.toFun E₆.holo'
    E₆_isBoundedAtImInfty E₆_tendsto_one_atImInfty using 2
  · rw [show ((6 : ℤ) : ℂ) = 6 from by norm_num]
  · norm_num

/-- serreD 1 E₂ is a weight-4 modular form.
Note: E₂ itself is NOT a modular form, but serreD 1 E₂ IS. -/
def serreDE₂ModularForm : ModularForm (CongruenceSubgroup.Gamma 1) 4 where
  toSlashInvariantForm := {
    toFun := serreD 1 E₂
    slash_action_eq' := fun γ hγ => by
      rw [Subgroup.mem_map] at hγ
      obtain ⟨γ', _, rfl⟩ := hγ
      exact serre_DE₂_slash_invariant γ'
  }
  holo' := serre_D_differentiable E₂_holo'
  bdd_at_cusps' := fun hc =>
    bounded_at_cusps_of_bounded_at_infty hc fun _ hA => by
      obtain ⟨A', rfl⟩ := MonoidHom.mem_range.mp hA
      exact (serre_DE₂_slash_invariant A').symm ▸ serre_DE₂_isBoundedAtImInfty

/-- serreD 1 E₂ → -1/12 at i∞. -/
lemma serre_DE₂_tendsto_atImInfty :
    Filter.Tendsto (serreD 1 E₂) atImInfty (nhds (-(1/12 : ℂ))) := by
  simpa [Int.cast_one, neg_div] using
    serre_D_tendsto_neg_k_div_12 1 E₂ E₂_holo' E₂_isBoundedAtImInfty E₂_tendsto_one_atImInfty

/-! ## Generic q-expansion summability and derivative bounds -/

/-- Summability of (m+1)^k * exp(-2πm) via comparison with shifted sum. -/
lemma summable_pow_shift (k : ℕ) :
    Summable fun m : ℕ => (m + 1 : ℝ) ^ k * rexp (-2 * π * m) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul k (by positivity : 0 < 2 * π)
  have h_eq : ∀ m : ℕ, (m + 1 : ℝ) ^ k * rexp (-2 * π * m) =
      rexp (2 * π) * ((m + 1) ^ k * rexp (-2 * π * (m + 1))) := fun m => by
    have : rexp (-2 * π * m) = rexp (2 * π) * rexp (-2 * π * (m + 1)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  simp_rw [h_eq]
  apply Summable.mul_left
  refine (h.comp_injective Nat.succ_injective).congr (fun m => ?_)
  simp [Function.comp_apply, Nat.succ_eq_add_one]

/-- Derivative bounds for q-expansion coefficients.
Given `‖a n‖ ≤ n^k`, produces bounds
`‖a n * 2πin * exp(2πin z)‖ ≤ 2π * n^(k+1) * exp(-2πn * y_min)`
on compact K ⊆ {z : 0 < z.im}. This is a key hypothesis for `D_qexp_tsum_pnat`. -/
lemma qexp_deriv_bound_of_coeff_bound {a : ℕ+ → ℂ} {k : ℕ}
    (ha : ∀ n : ℕ+, ‖a n‖ ≤ (n : ℝ)^k) :
    ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ (n : ℕ+) (z : K),
        ‖a n * (2 * π * I * ↑n) * cexp (2 * π * I * ↑n * z.1)‖ ≤ u n := by
  intro K hK_sub hK_compact
  by_cases hK_nonempty : K.Nonempty
  · obtain ⟨k_min, hk_min_mem, hk_min_le⟩ := hK_compact.exists_isMinOn hK_nonempty
      Complex.continuous_im.continuousOn
    have hy_min_pos : 0 < k_min.im := hK_sub hk_min_mem
    have hpos : 0 < 2 * π * k_min.im := by nlinarith [pi_pos]
    have h := Real.summable_pow_mul_exp_neg_nat_mul (k + 1) hpos
    have hconv : Summable (fun n : ℕ+ =>
        2 * π * ((n : ℕ) : ℝ)^(k + 1) * rexp (-(2 * π * k_min.im) * (n : ℕ))) := by
      have : Summable (fun n : ℕ+ =>
          ((n : ℕ) : ℝ)^(k + 1) * rexp (-(2 * π * k_min.im) * (n : ℕ))) := h.subtype _
      refine (this.mul_left (2 * π)).congr (fun n => ?_)
      ring
    use fun n => 2 * π * (n : ℝ)^(k + 1) * rexp (-2 * π * ↑n * k_min.im)
    constructor
    · apply hconv.of_nonneg_of_le
      · intro n; positivity
      · intro n
        have h1 : -2 * π * ↑↑n * k_min.im = -(2 * π * k_min.im) * ↑↑n := by ring
        simp only [h1]; exact le_refl _
    · intro n ⟨z, hz_mem⟩
      have hz_im : k_min.im ≤ z.im := hk_min_le hz_mem
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast n.pos
      have h_norm_2pin : ‖(2 : ℂ) * π * I * ↑↑n‖ = 2 * π * n := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
            Complex.norm_I, mul_one, Complex.norm_natCast, Real.norm_of_nonneg pi_pos.le]
      calc ‖a n * (2 * π * I * ↑↑n) * cexp (2 * π * I * ↑↑n * z)‖
          = ‖a n‖ * ‖(2 * π * I * ↑↑n)‖ * ‖cexp (2 * π * I * ↑↑n * z)‖ := by rw [norm_mul, norm_mul]
        _ ≤ (n : ℝ)^k * (2 * π * n) * rexp (-2 * π * n * z.im) := by
            rw [h_norm_2pin]
            have hexp : ‖cexp (2 * π * I * ↑↑n * z)‖ ≤ rexp (-2 * π * n * z.im) := by
              rw [Complex.norm_exp]
              have : (2 * π * I * ↑↑n * z).re = -2 * π * n * z.im := by
                have hrw : (2 * π * I * ↑↑n * z) = (↑(2 * π * (n : ℝ)) * I) * z := by
                  push_cast; ring
                rw [hrw, Complex.mul_re, Complex.mul_re]
                simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
                  Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero, zero_sub, add_zero]
                ring
              rw [this]
            gcongr; exact ha n
        _ ≤ (n : ℝ)^k * (2 * π * n) * rexp (-2 * π * n * k_min.im) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.exp_le_exp_of_le
            apply mul_le_mul_of_nonpos_left hz_im
            nlinarith [pi_pos, hn_pos]
        _ = 2 * π * (n : ℝ)^(k + 1) * rexp (-2 * π * n * k_min.im) := by ring
  · use fun _ => 0
    constructor
    · exact summable_zero
    · intro n ⟨z, hz_mem⟩
      exfalso; exact hK_nonempty ⟨z, hz_mem⟩
