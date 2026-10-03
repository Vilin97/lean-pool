/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Scalar bookkeeping for §2.2. The flow and interpolation lemmas below
are algebraic consequences of scalar estimates, not proofs of PDE/ODE estimates. -/

@[expose] public section

noncomputable section
open scoped BigOperators
open Finset
namespace AVenhance.Infra.Construction

/-- length scales lie in `(0,1]`. -/
theorem epsilon_le_one {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    AVenhance.epsilon β Λ m ≤ 1 := by
  have h := AVenhance.Infra.Ingredients.epsilon_le_lambda_pow hβ hβ' hΛ (m := m)
  have hbase : 1 ≤ (Λ : ℝ) := by exact_mod_cast (show 1 ≤ Λ by omega)
  exact h.trans (Real.rpow_le_one_of_one_le_of_nonpos hbase (by simp))

/-- Finite geometric sums are bounded by the full convergent geometric series. -/
theorem sum_geometric_le {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (n : ℕ) :
    ∑ j ∈ range n, r ^ j ≤ (1 - r)⁻¹ := by
  have ha : |r| < 1 := by rwa [abs_of_nonneg hr]
  have hsum := summable_geometric_of_abs_lt_one ha
  simpa only [tsum_geometric_of_abs_lt_one ha] using
    hsum.sum_le_tsum (range n) (fun j _ => pow_nonneg hr j)

/-- Backward geometric summation for increasing amplitudes. -/
theorem sum_le_last_mul_geometric (u : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hu : ∀ j, u j ≤ r * u (j + 1)) (m : ℕ) :
    ∑ j ∈ range (m + 1), u j ≤ u m * ∑ j ∈ range (m + 1), r ^ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsum : 0 ≤ ∑ j ∈ range (m + 1), r ^ j := sum_nonneg fun j _ => pow_nonneg hr j
    calc
      ∑ j ∈ range (m + 1 + 1), u j = (∑ j ∈ range (m + 1), u j) + u (m + 1) := sum_range_succ _ _
      _ ≤ u m * (∑ j ∈ range (m + 1), r ^ j) + u (m + 1) := add_le_add ih le_rfl
      _ ≤ (r * u (m + 1)) * (∑ j ∈ range (m + 1), r ^ j) + u (m + 1) :=
        add_le_add (mul_le_mul_of_nonneg_right (hu m) hsum) le_rfl
      _ = u (m + 1) * (∑ j ∈ range (m + 1 + 1), r ^ j) := by
        rw [geom_sum_succ (x := r) (n := m + 1)]
        ring

/-- Minimal separation reverses for the negative amplitude exponent. -/
theorem a_backward_step {β : ℝ} {Λ j : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    AVenhance.a β Λ j ≤ (Λ : ℝ) ^ (β - 2) * AVenhance.a β Λ (j + 1) := by
  have he := AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := j + 1)
  have hL : 0 < (Λ : ℝ) := by positivity
  have hs := AVenhance.Infra.Ingredients.epsilon_minsep hβ hβ' hΛ (m := j)
  have h := Real.rpow_le_rpow_of_nonpos (mul_pos hL he) hs (by linarith : β - 2 ≤ 0)
  simpa only [AVenhance.a, Real.mul_rpow hL.le he.le] using h

/-- The geometric-sum step in `e.Mmbound` for the actual amplitudes. -/
theorem a_sum_bounds {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (m : ℕ) :
    (∑ j ∈ range (m + 1), AVenhance.a β Λ j) ≤
      AVenhance.a β Λ m * (∑ j ∈ range (m + 1), ((Λ : ℝ) ^ (β - 2)) ^ j) ∧
    (∑ j ∈ range (m + 1), AVenhance.a β Λ j) ≤
      AVenhance.a β Λ m / (1 - (Λ : ℝ) ^ (β - 2)) := by
  have hL : 1 < (Λ : ℝ) := by exact_mod_cast (show 1 < Λ by omega)
  have hr : 0 ≤ (Λ : ℝ) ^ (β - 2) := Real.rpow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hL.le) _
  have hr' : (Λ : ℝ) ^ (β - 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)
  have hsum := sum_le_last_mul_geometric (AVenhance.a β Λ) hr (fun _ => a_backward_step hβ hβ' hΛ) m
  refine ⟨hsum, hsum.trans ?_⟩
  simpa only [div_eq_mul_inv, AVenhance.a] using mul_le_mul_of_nonneg_left (sum_geometric_le hr
      hr' (m + 1))
    (Real.rpow_nonneg (AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le _)

/-- The scalar numerical closure in source lines 1723–1730. -/
theorem M_numeric_closure :
    ((2 : ℝ) ^ 8 + 2 ^ 18) / (1 - (2 : ℝ) ^ (-(14 / 3 : ℝ))) ≤ 2 ^ 19 := by
  have he : -(14 / 3 : ℝ) ≤ -2 := by norm_num
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  norm_num at hp
  have hd : 0 < 1 - (2 : ℝ) ^ (-(14 / 3 : ℝ)) := by linarith
  apply (div_le_iff₀ hd).2
  norm_num at hp ⊢
  linarith only [hp]

/-- The exact comparison with the ratio printed in `e.Mmbound`. -/
theorem amplitude_ratio_bound {β : ℝ} {Λ : ℕ}
    (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    (Λ : ℝ) ^ (β - 2) ≤ (2 : ℝ) ^ (-(14 / 3 : ℝ)) := by
  have hL : (2 : ℝ) ^ 7 ≤ (Λ : ℝ) := by exact_mod_cast hΛ
  calc
    (Λ : ℝ) ^ (β - 2) ≤ ((2 : ℝ) ^ 7) ^ (β - 2) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by linarith)
    _ = (2 : ℝ) ^ (7 * (β - 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ ≤ (2 : ℝ) ^ (-(14 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- The final amplitude-sum closure, with no auxiliary recurrence assumptions. -/
theorem a_sum_closure {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (m : ℕ) :
    ((2 : ℝ) ^ 8 + 2 ^ 18) * (∑ j ∈ range (m + 1), AVenhance.a β Λ j) ≤
      2 ^ 19 * AVenhance.a β Λ m := by
  have hs := (a_sum_bounds hβ hβ' hΛ m).2
  have hr := amplitude_ratio_bound hβ' hΛ
  have ha : 0 ≤ AVenhance.a β Λ m :=
    Real.rpow_nonneg (AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le _
  have hd : 0 < 1 - (2 : ℝ) ^ (-(14 / 3 : ℝ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hfrac := div_le_div_of_nonneg_left ha hd (sub_le_sub_left hr 1)
  calc
    ((2 : ℝ) ^ 8 + 2 ^ 18) * (∑ j ∈ range (m + 1), AVenhance.a β Λ j) ≤
        (2 ^ 8 + 2 ^ 18) * (AVenhance.a β Λ m / (1 - (2 : ℝ) ^ (-(14 / 3 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hs.trans hfrac) (by norm_num)
    _ = (((2 : ℝ) ^ 8 + 2 ^ 18) / (1 - (2 : ℝ) ^ (-(14 / 3 : ℝ)))) * AVenhance.a β Λ m := by ring
    _ ≤ 2 ^ 19 * AVenhance.a β Λ m := mul_le_mul_of_nonneg_right M_numeric_closure ha

/-- Corrected upper bound, in inverse-amplitude form (stronger than 2⁻²⁴). -/
theorem tauPP_inverse_amplitude_bound {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    AVenhance.tauPP β Λ m ≤ (2 : ℝ) ^ (-25 : ℤ) *
      (AVenhance.a β Λ (m - 1))⁻¹ * AVenhance.epsilon β Λ (m - 1) ^ AVenhance.delta β := by
  have he := AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := m - 1)
  have he1 := epsilon_le_one hβ hβ' hΛ (m := m - 1)
  have hd := AVenhance.Infra.Ingredients.delta_pos hβ hβ'
  have hmono := Real.rpow_le_rpow_of_exponent_ge he he1
    (show AVenhance.delta β ≤ 2 * AVenhance.delta β by linarith)
  have heq : AVenhance.epsilon β Λ (m - 1) ^ (2 - β + 2 * AVenhance.delta β) =
      (AVenhance.a β Λ (m - 1))⁻¹ * AVenhance.epsilon β Λ (m - 1) ^ (2 * AVenhance.delta β) := by
    rw [AVenhance.a, ← Real.rpow_neg he.le, ← Real.rpow_add he]
    congr 1
    ring
  calc
    AVenhance.tauPP β Λ m ≤ (2 : ℝ) ^ (-25 : ℤ) *
        AVenhance.epsilon β Λ (m - 1) ^ (2 - β + 2 * AVenhance.delta β) :=
      (AVenhance.Infra.Ingredients.tauPP_bounds hβ hβ' hΛ hm).2
    _ = (2 : ℝ) ^ (-25 : ℤ) * (AVenhance.a β Λ (m - 1))⁻¹ *
        AVenhance.epsilon β Λ (m - 1) ^ (2 * AVenhance.delta β) := by rw [heq]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono
      (mul_nonneg (by norm_num) (inv_nonneg.mpr (Real.rpow_nonneg he.le _)))

/-- Abstract inverse-amplitude conversion used to close the flow time window. -/
theorem inverse_amplitude_window {A M E : ℝ} (hA : 0 < A) (hM : 0 < M)
    (hE : E ≤ 1) (hbound : M ≤ (2 : ℝ) ^ 19 * A) :
    (2 : ℝ) ^ (-24 : ℤ) * A⁻¹ * E ≤ (2 : ℝ) ^ (-5 : ℤ) * M⁻¹ := by
  have hfirst := mul_le_mul_of_nonneg_left hE
    (show 0 ≤ (2 : ℝ) ^ (-24 : ℤ) * A⁻¹ by positivity)
  have hsecond : (2 : ℝ) ^ (-24 : ℤ) * A⁻¹ ≤ (2 : ℝ) ^ (-5 : ℤ) * M⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hA hM).2
    norm_num at hbound ⊢
    linarith only [hbound]
  rw [mul_one] at hfirst
  exact hfirst.trans hsecond

/-- The actual time scale satisfies the inductive time-window condition. -/
theorem tauPP_induction_window {β M : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m)
    (hM : 0 < M) (hbound : M ≤ (2 : ℝ) ^ 19 * AVenhance.a β Λ (m - 1)) :
    AVenhance.tauPP β Λ m ≤ (2 : ℝ) ^ (-24 : ℤ) *
      (AVenhance.a β Λ (m - 1))⁻¹ * AVenhance.epsilon β Λ (m - 1) ^ AVenhance.delta β ∧
    AVenhance.tauPP β Λ m ≤ (2 : ℝ) ^ (-5 : ℤ) * M⁻¹ := by
  have he := AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := m - 1)
  have hd := AVenhance.Infra.Ingredients.delta_pos hβ hβ'
  have hE := Real.rpow_le_one he.le (epsilon_le_one hβ hβ' hΛ) hd.le
  have hA := Real.rpow_pos_of_pos he (β - 2)
  have hweak := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ^ (-25 : ℤ) ≤ 2 ^ (-24 : ℤ))
      (inv_nonneg.mpr hA.le)) (Real.rpow_nonneg he.le (AVenhance.delta β))
  have hfirst' := (tauPP_inverse_amplitude_bound hβ hβ' hΛ hm).trans hweak
  exact ⟨hfirst', hfirst'.trans (inverse_amplitude_window hA hM hE hbound)⟩

/-- Forward scale summation for a positive exponent. -/
theorem epsilon_power_sum {β p : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hp : 0 < p) (m : ℕ) :
    (∑ j ∈ range (m + 1), AVenhance.epsilon β Λ j ^ p) ≤
      (1 - (Λ : ℝ) ^ (-p))⁻¹ := by
  have hL : 1 < (Λ : ℝ) := by exact_mod_cast (show 1 < Λ by omega)
  have hbound : ∀ j, AVenhance.epsilon β Λ j ^ p ≤ ((Λ : ℝ) ^ (-p)) ^ j := by
    intro j
    calc
      AVenhance.epsilon β Λ j ^ p ≤ ((Λ : ℝ) ^ (-(j : ℝ))) ^ p :=
        Real.rpow_le_rpow (AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le
          (AVenhance.Infra.Ingredients.epsilon_le_lambda_pow hβ hβ' hΛ) hp.le
      _ = ((Λ : ℝ) ^ (-p)) ^ j := by
        rw [← Real.rpow_mul (by positivity : 0 ≤ (Λ : ℝ)), ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity : 0 ≤ (Λ : ℝ))]
        congr 1
        ring
  exact (sum_le_sum (fun j _ => hbound j)).trans
    (sum_geometric_le (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_lt_one_of_one_lt_of_neg hL (neg_neg_of_pos hp)) (m + 1))

/-- Zeroth-order telescoping scalar estimate, source 1805–1818. -/
theorem telescoping_zero {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (m : ℕ) :
    10 * (∑ j ∈ range (m + 1), AVenhance.epsilon β Λ j ^ β) ≤ 11 := by
  have hs := epsilon_power_sum hβ hβ' hΛ (by linarith : 0 < β) m
  have hL : 1 ≤ (Λ : ℝ) := by exact_mod_cast (show 1 ≤ Λ by omega)
  have hr := Real.rpow_le_rpow_of_exponent_le hL (show -β ≤ -1 by linarith)
  rw [Real.rpow_neg_one] at hr
  have hi : (Λ : ℝ)⁻¹ ≤ (128 : ℝ)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by norm_num)).2 (by exact_mod_cast hΛ)
  have hratio : (Λ : ℝ) ^ (-β) ≤ 1 / 128 := by norm_num at hi; exact hr.trans hi
  have hden : 0 < 1 - (Λ : ℝ) ^ (-β) := by linarith
  have hnum : 10 * (1 - (Λ : ℝ) ^ (-β))⁻¹ ≤ 11 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hden).2
    linarith only [hratio]
  exact (mul_le_mul_of_nonneg_left hs (by norm_num)).trans hnum

/-- Lambda has logarithm at least four, uniformly over the allowed range. -/
theorem four_le_log_lambda {Λ : ℕ} (hΛ : 2 ^ 7 ≤ Λ) : 4 ≤ Real.log (Λ : ℝ) := by
  have hL : 0 < (Λ : ℝ) := by positivity
  apply (Real.le_log_iff_exp_le hL).2
  have he : Real.exp (4 : ℝ) < 81 := by
    have h := pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num : (4 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  have hc : (81 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast (show 81 ≤ Λ by omega)
  exact he.le.trans hc

/-- The geometric denominator controlling the first-order telescoping sum. -/
theorem first_order_denominator {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    (5 / 3) * (β - 1) ≤ 1 - (Λ : ℝ) ^ (-(β - 1)) := by
  let s := β - 1
  have hs : 0 < s := by dsimp [s]; linarith
  have hs' : s ≤ 1 / 3 := by dsimp [s]; linarith
  have hlog := four_le_log_lambda hΛ
  have hlin : 1 + 4 * s ≤ Real.exp (s * Real.log (Λ : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hlog hs.le
    have he := Real.add_one_le_exp (s * Real.log (Λ : ℝ))
    linarith only [hm, he]
  have hpos : 0 < 1 + 4 * s := by linarith
  have hi := (inv_le_inv₀ (Real.exp_pos _) hpos).2 hlin
  have hr : (Λ : ℝ) ^ (-s) ≤ (1 + 4 * s)⁻¹ := by
    rw [Real.rpow_def_of_pos (by positivity : 0 < (Λ : ℝ))]
    have heq : Real.log (Λ : ℝ) * (-s) = -(s * Real.log (Λ : ℝ)) := by ring
    rw [heq, Real.exp_neg]
    exact hi
  have halg : (1 + 4 * s)⁻¹ ≤ 1 - (5 / 3) * s := by
    rw [← one_div]
    apply (div_le_iff₀ hpos).2
    nlinarith only [mul_nonneg hs.le (sub_nonneg.mpr hs'), hs.le]
  change (5 / 3) * s ≤ 1 - (Λ : ℝ) ^ (-s)
  linarith only [hr, halg]

/-- First-order telescoping scalar estimate, source 1805–1818. -/
theorem telescoping_one {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (m : ℕ) :
    5 * AVenhance.epsilon β Λ m * (∑ j ∈ range (m + 1), AVenhance.epsilon β Λ j ^ (β - 1)) ≤
      (3 / (β - 1)) * AVenhance.epsilon β Λ m := by
  have hs := epsilon_power_sum hβ hβ' hΛ (sub_pos.mpr hβ) m
  have hd := first_order_denominator hβ hβ' hΛ
  have hp : 0 < 1 - (Λ : ℝ) ^ (-(β - 1)) :=
    lt_of_lt_of_le (by positivity : 0 < (5 / 3) * (β - 1)) hd
  have hnum : 5 * (1 - (Λ : ℝ) ^ (-(β - 1)))⁻¹ ≤ 3 / (β - 1) := by
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ hp (sub_pos.mpr hβ)).2
    linarith only [hd]
  calc
    5 * AVenhance.epsilon β Λ m * (∑ j ∈ range (m + 1), AVenhance.epsilon β Λ j ^ (β - 1)) ≤
        5 * AVenhance.epsilon β Λ m * (1 - (Λ : ℝ) ^ (-(β - 1)))⁻¹ :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num) (AVenhance.Infra.Cutoff.epsilon_pos
          hβ hβ' hΛ).le)
    _ ≤ (3 / (β - 1)) * AVenhance.epsilon β Λ m := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hnum (AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le

/-- Real-power identity translating the interpolation estimate to epsilon. -/
theorem epsilon_beta_div {E β : ℝ} (hE : 0 < E) : E ^ β / E = E ^ (β - 1) := by
  rw [Real.rpow_sub hE, Real.rpow_one]

/-- Scalar closure for the normalized radius recurrence. -/
theorem radius_step_algebra {E F R : ℝ} (hE : 0 < E) (hR : 0 ≤ R)
    (hsep : F ≤ E / 128) (hprev : E * R ≤ 5 / 4) :
    F * ((9 / 4) * R + 128 * E⁻¹) ≤ 5 / 4 := by
  have hmul := mul_le_mul_of_nonneg_right hsep
    (show 0 ≤ (9 / 4) * R + 128 * E⁻¹ by positivity)
  have heq : E / 128 * ((9 / 4) * R + 128 * E⁻¹) = (9 / 512) * (E * R) + 1 := by
    field_simp
    ring
  rw [heq] at hmul
  linarith only [hmul, hprev]

/-- The 5/4 normalized-radius bound for the recurrence in source 1683. -/
theorem radius_recurrence_scaled {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (R : ℕ → ℝ)
    (hR₀ : R 0 = 1)
    (hR : ∀ j, R (j + 1) = (9 / 4) * R j + (2 : ℝ) ^ 7 * (AVenhance.epsilon β Λ (j + 1))⁻¹)
    (m : ℕ) : AVenhance.epsilon β Λ (m + 1) * R m ≤ 5 / 4 := by
  have hnonneg : ∀ j, 0 ≤ R j := by
    intro j
    induction j with
    | zero => rw [hR₀]; norm_num
    | succ j ih =>
      have he := AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := j + 1)
      rw [hR j]
      positivity
  have hsep : ∀ j, AVenhance.epsilon β Λ (j + 1) ≤ AVenhance.epsilon β Λ j / 128 := by
    intro j
    have hs := AVenhance.Infra.Ingredients.epsilon_minsep hβ hβ' hΛ (m := j)
    have hL : (128 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
    have hm := mul_le_mul_of_nonneg_right hL (AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := j
        + 1)).le
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 128)).2
    have hm' : AVenhance.epsilon β Λ (j + 1) * 128 ≤ (Λ : ℝ) * AVenhance.epsilon β Λ (j + 1) := by
      simpa only [mul_comm] using hm
    exact hm'.trans hs
  induction m with
  | zero =>
    rw [hR₀, mul_one]
    have hs := hsep 0
    have he : AVenhance.epsilon β Λ 0 = 1 := by simp only [AVenhance.epsilon, ↓reduceIte]
    rw [he] at hs
    linarith only [hs]
  | succ m ih =>
    rw [hR m]
    norm_num only [show (2 : ℝ) ^ 7 = 128 by norm_num]
    exact radius_step_algebra (AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ)
      (hnonneg m) (hsep (m + 1)) ih

/-- `e.Rmbound`: radius bounded by 131 epsilon⁻¹, directly from its recurrence. -/
theorem radius_recurrence_bound {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (R : ℕ → ℝ)
    (hR₀ : R 0 = 1)
    (hR : ∀ j, R (j + 1) = (9 / 4) * R j + (2 : ℝ) ^ 7 * (AVenhance.epsilon β Λ (j + 1))⁻¹)
    (hm : 1 ≤ m) : R m ≤ (3 + (2 : ℝ) ^ 7) * (AVenhance.epsilon β Λ m)⁻¹ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hs := radius_recurrence_scaled hβ hβ' hΛ R hR₀ hR j
  have he := AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := j + 1)
  rw [hR j]
  have halg {E S : ℝ} (hE : 0 < E) (hs : E * S ≤ 5 / 4) :
      (9 / 4) * S + 128 * E⁻¹ ≤ 131 * E⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    apply (le_div_iff₀ hE).2
    have heq : ((9 / 4) * S + 128 / E) * E = (9 / 4) * (E * S) + 128 := by
      field_simp
    rw [heq]
    linarith only [hs]
  norm_num only [show (2 : ℝ) ^ 7 = 128 by norm_num, show (3 : ℝ) + 128 = 131 by norm_num]
  exact halg he hs

/-- Summing the simplified scalar M recurrence. -/
theorem amplitude_recurrence_sum {β : ℝ} {Λ : ℕ}
    (M : ℕ → ℝ) (hM₀ : M 0 ≤ (2 : ℝ) ^ 8 + 2 ^ 18)
    (hstep : ∀ j, M (j + 1) ≤ M j + ((2 : ℝ) ^ 8 + 2 ^ 18) * AVenhance.a β Λ (j + 1))
    (m : ℕ) : M m ≤ ((2 : ℝ) ^ 8 + 2 ^ 18) * ∑ j ∈ range (m + 1), AVenhance.a β Λ j := by
  induction m with
  | zero => simpa [AVenhance.a, AVenhance.epsilon] using hM₀
  | succ m ih =>
    calc
      M (m + 1) ≤ M m + ((2 : ℝ) ^ 8 + 2 ^ 18) * AVenhance.a β Λ (m + 1) := hstep m
      _ ≤ ((2 : ℝ) ^ 8 + 2 ^ 18) * (∑ j ∈ range (m + 1), AVenhance.a β Λ j) +
          ((2 : ℝ) ^ 8 + 2 ^ 18) * AVenhance.a β Λ (m + 1) := add_le_add ih le_rfl
      _ = _ := by rw [sum_range_succ (n := m + 1), mul_add]

/-- `e.Mmbound` from the simplified recurrence, including its initial value. -/
theorem amplitude_recurrence_bound {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    (M : ℕ → ℝ) (hM₀ : M 0 ≤ (2 : ℝ) ^ 8 + 2 ^ 18)
    (hstep : ∀ j, M (j + 1) ≤ M j + ((2 : ℝ) ^ 8 + 2 ^ 18) * AVenhance.a β Λ (j + 1))
    (m : ℕ) : M m ≤ (2 : ℝ) ^ 19 * AVenhance.a β Λ m :=
  (amplitude_recurrence_sum M hM₀ hstep m).trans (a_sum_closure hβ hβ' hΛ m)

/-- Simplification of the full M increment using the normalized-radius bound. -/
theorem amplitude_step_algebra {A E R : ℝ} (hA : 0 ≤ A) (hER : 0 ≤ E * R)
    (hbound : E * R ≤ 5 / 4) :
    (2 : ℝ) ^ 7 * A * E ^ 2 * R ^ 2 + 2 ^ 18 * A ≤ (2 ^ 8 + 2 ^ 18) * A := by
  have hs : (E * R) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hER hbound 2
  have hm := mul_le_mul_of_nonneg_left hs hA
  nlinarith only [hm, hA]

/-- Full scalar recurrence closure for the source's M and R sequences. -/
theorem full_amplitude_recurrence_bound {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (R M : ℕ → ℝ)
    (hR₀ : R 0 = 1) (hM₀ : M 0 = 1)
    (hR : ∀ j, R (j + 1) = (9 / 4) * R j + (2 : ℝ) ^ 7 * (AVenhance.epsilon β Λ (j + 1))⁻¹)
    (hM : ∀ j, M (j + 1) = M j + (2 : ℝ) ^ 7 * AVenhance.a β Λ (j + 1) *
      AVenhance.epsilon β Λ (j + 1) ^ 2 * R j ^ 2 + 2 ^ 18 * AVenhance.a β Λ (j + 1))
    (m : ℕ) : M m ≤ (2 : ℝ) ^ 19 * AVenhance.a β Λ m := by
  have hnonneg : ∀ j, 0 ≤ R j := by
    intro j
    induction j with
    | zero => rw [hR₀]; norm_num
    | succ j ih =>
      have he := AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := j + 1)
      rw [hR j]
      positivity
  apply amplitude_recurrence_bound hβ hβ' hΛ M (by rw [hM₀]; norm_num) _ m
  intro j
  have hs := radius_recurrence_scaled hβ hβ' hΛ R hR₀ hR j
  have he := AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := j + 1)
  have ha : 0 ≤ AVenhance.a β Λ (j + 1) := Real.rpow_nonneg he.le _
  have hh := amplitude_step_algebra ha (mul_nonneg he.le (hnonneg j)) hs
  rw [hM j]
  have heq : M j + (2 : ℝ) ^ 7 * AVenhance.a β Λ (j + 1) *
      AVenhance.epsilon β Λ (j + 1) ^ 2 * R j ^ 2 + 2 ^ 18 * AVenhance.a β Λ (j + 1) =
      M j + ((2 : ℝ) ^ 7 * AVenhance.a β Λ (j + 1) *
      AVenhance.epsilon β Λ (j + 1) ^ 2 * R j ^ 2 + 2 ^ 18 * AVenhance.a β Λ (j + 1)) := by ring
  rw [heq]
  exact add_le_add le_rfl hh

end AVenhance.Infra.Construction
