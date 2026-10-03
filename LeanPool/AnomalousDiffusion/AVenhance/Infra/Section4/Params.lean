/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Numeric.Exponents
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Scalars
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermittedInterval
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KMat
public import Mathlib.Analysis.Matrix.Normed

/-! Scalar bridges for §4. Diffusivity results named `conditional` take the
applicable diffusivity-recursion conclusion explicitly. No draft theorem module is imported.
The top index never acquires an interior two-sided bound. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4
open scoped Matrix.Norms.Elementwise
open AVenhance
open AVenhance.Infra.Ingredients

/-- Multiplication by the preceding amplitude cancels the time-scale exponent. -/
theorem amplitude_time_power {β E p : ℝ} (hE : 0 < E) :
    E ^ (β - 2) * E ^ (2 - β + p) = E ^ p := by
  rw [← Real.rpow_add hE]
  congr 1
  ring

/-- Uniform bounds for the integer time-cell factor, with ceilings retained. -/
theorem time_cell_factor_bounds {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    4 * epsilon β Λ (m - 1) ^ (-delta β) ≤ tauCellFactor β Λ m ∧
      tauCellFactor β Λ m ≤ 9 * epsilon β Λ (m - 1) ^ (-delta β) := by
  have he := Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := m - 1)
  have he1 := Infra.Construction.epsilon_le_one hβ hβ' hΛ (m := m - 1)
  have hd := delta_pos hβ hβ'
  have hx : 1 ≤ epsilon β Λ (m - 1) ^ (-delta β) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos he he1 (neg_nonpos.mpr hd.le)
  have hlo := Nat.le_ceil (epsilon β Λ (m - 1) ^ (-delta β))
  have hhi : (⌈epsilon β Λ (m - 1) ^ (-delta β)⌉₊ : ℝ) <
      epsilon β Λ (m - 1) ^ (-delta β) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg he.le _)
  unfold tauCellFactor
  constructor <;> linarith only [hlo, hhi, hx]

/-- `a_(m−1) τ''_m ≍ ε_(m−1)^(2δ)`, with the corrected constants. -/
theorem amplitude_tauPP_bounds {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ (-26 : ℤ) * epsilon β Λ (m - 1) ^ (2 * delta β) ≤
      a β Λ (m - 1) * tauPP β Λ m ∧
    a β Λ (m - 1) * tauPP β Λ m ≤
      (2 : ℝ) ^ (-25 : ℤ) * epsilon β Λ (m - 1) ^ (2 * delta β) := by
  have he := Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := m - 1)
  have ha := Infra.Cutoff.a_pos hβ hβ' hΛ (m := m - 1)
  obtain ⟨hl, hu⟩ := tauPP_bounds hβ hβ' hΛ hm
  have hform (c : ℝ) : a β Λ (m - 1) *
      (c * epsilon β Λ (m - 1) ^ (2 - β + 2 * delta β)) =
      c * epsilon β Λ (m - 1) ^ (2 * delta β) := by
    rw [a, mul_left_comm, amplitude_time_power he]
  exact ⟨by simpa only [hform] using mul_le_mul_of_nonneg_left hl ha.le,
    by simpa only [hform] using mul_le_mul_of_nonneg_left hu ha.le⟩

/-- `a_(m−1) τ_m ≍ ε_(m−1)^(4δ)`. -/
theorem amplitude_tau_bounds {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ (-33 : ℤ) * epsilon β Λ (m - 1) ^ (4 * delta β) ≤
      a β Λ (m - 1) * tau β Λ m ∧
    a β Λ (m - 1) * tau β Λ m ≤
      (2 : ℝ) ^ (-28 : ℤ) * epsilon β Λ (m - 1) ^ (4 * delta β) := by
  have he := Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := m - 1)
  have ha := Infra.Cutoff.a_pos hβ hβ' hΛ (m := m - 1)
  obtain ⟨hl, hu⟩ := tau_bounds hβ hβ' hΛ hm
  have hform (c : ℝ) : a β Λ (m - 1) *
      (c * epsilon β Λ (m - 1) ^ (2 - β + 4 * delta β)) =
      c * epsilon β Λ (m - 1) ^ (4 * delta β) := by
    rw [a, mul_left_comm, amplitude_time_power he]
  exact ⟨by simpa only [hform] using mul_le_mul_of_nonneg_left hl ha.le,
    by simpa only [hform] using mul_le_mul_of_nonneg_left hu ha.le⟩

/-- The two time-scale ratios are exactly reciprocal cell factors. -/
theorem time_ratios_exact {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    tauP β Λ m / tau β Λ m = tauCellFactor β Λ m ∧
      tau β Λ m / tauP β Λ m = (tauCellFactor β Λ m)⁻¹ := by
  have ht := tau_pos hβ hβ' hΛ (m := m)
  have hF : 0 < tauCellFactor β Λ m := by unfold tauCellFactor; positivity
  rw [tauP_eq_cellFactor_mul_tau hm]
  constructor <;> field_simp [ht.ne', hF.ne']

/-- The separated fast times satisfy τ/τ' ≍ ε^δ. -/
theorem time_ratio_bounds {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    (1 / 9) * epsilon β Λ (m - 1) ^ delta β ≤ tau β Λ m / tauP β Λ m ∧
      tau β Λ m / tauP β Λ m ≤ (1 / 4) * epsilon β Λ (m - 1) ^ delta β := by
  have he := Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := m - 1)
  have hF : 0 < tauCellFactor β Λ m := by unfold tauCellFactor; positivity
  obtain ⟨hl, hu⟩ := time_cell_factor_bounds hβ hβ' hΛ (m := m)
  rw [(time_ratios_exact hβ hβ' hΛ hm).2]
  have hlo := (inv_le_inv₀ (by positivity : 0 < 9 * epsilon β Λ (m - 1) ^ (-delta β)) hF).2 hu
  have hhi := (inv_le_inv₀ hF (by positivity : 0 < 4 * epsilon β Λ (m - 1) ^ (-delta β))).2 hl
  simpa only [mul_inv_rev, Real.rpow_neg he.le, inv_inv, mul_comm, one_div] using And.intro hlo hhi

/-- The intermediate time scale satisfies a τ' ≍ ε^(3δ); the printed equality is approximate. -/
theorem amplitude_tauP_bounds {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    ((2 : ℝ) ^ (-26 : ℤ) / 9) * epsilon β Λ (m - 1) ^ (3 * delta β) ≤
      a β Λ (m - 1) * tauP β Λ m ∧
    a β Λ (m - 1) * tauP β Λ m ≤
      (2 : ℝ) ^ (-27 : ℤ) * epsilon β Λ (m - 1) ^ (3 * delta β) := by
  have he := Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := m - 1)
  have ha := Infra.Cutoff.a_pos hβ hβ' hΛ (m := m - 1)
  have hpp := Infra.Cutoff.tauPP_pos hβ hβ' hΛ (m := m)
  obtain ⟨hl, hu⟩ := amplitude_tauPP_bounds hβ hβ' hΛ hm
  have hF : 0 < tauCellFactor β Λ m := by unfold tauCellFactor; positivity
  have hform : a β Λ (m - 1) * tauP β Λ m =
      (a β Λ (m - 1) * tauPP β Λ m) * (tauCellFactor β Λ m)⁻¹ := by
    rw [tauPP_eq_cellFactor_mul_tauP hm]
    field_simp
  have hr := time_ratio_bounds hβ hβ' hΛ hm
  rw [(time_ratios_exact hβ hβ' hΛ hm).2] at hr
  have hl' := mul_le_mul hl hr.1 (by positivity) (mul_nonneg ha.le hpp.le)
  have hu' := mul_le_mul hu hr.2 (inv_nonneg.mpr hF.le) (by positivity)
  have heq : epsilon β Λ (m - 1) ^ (2 * delta β) *
      epsilon β Λ (m - 1) ^ delta β = epsilon β Λ (m - 1) ^ (3 * delta β) := by
    rw [← Real.rpow_add he]
    congr 1
    ring
  rw [hform]
  constructor
  · calc
      _ = ((2 : ℝ) ^ (-26 : ℤ) * epsilon β Λ (m - 1) ^ (2 * delta β)) *
          ((1 / 9) * epsilon β Λ (m - 1) ^ delta β) := by
        rw [mul_mul_mul_comm, heq]
        ring
      _ ≤ _ := hl'
  · have hc : (2 : ℝ) ^ (-25 : ℤ) * (1 / 4) = 2 ^ (-27 : ℤ) := by norm_num
    calc
      _ ≤ ((2 : ℝ) ^ (-25 : ℤ) * epsilon β Λ (m - 1) ^ (2 * delta β)) *
          ((1 / 4) * epsilon β Λ (m - 1) ^ delta β) := hu'
      _ = _ := by rw [mul_mul_mul_comm, heq, hc]

/-- The slow amplitude is bounded by the inverse intermediate time scale. -/
theorem amplitude_le_inverse_tauP {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    a β Λ (m - 1) ≤ (tauP β Λ m)⁻¹ := by
  have hp := Infra.Cutoff.tauP_pos hβ hβ' hΛ (m := m)
  have he := Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := m - 1)
  have hd := delta_pos hβ hβ'
  have hpow := Real.rpow_le_one he.le (Infra.Construction.epsilon_le_one hβ hβ' hΛ)
    (show 0 ≤ 3 * delta β by positivity)
  have hb := (amplitude_tauP_bounds hβ hβ' hΛ hm).2
  have hh := mul_le_mul_of_nonneg_left hpow (by norm_num : 0 ≤ (2 : ℝ) ^ (-27 : ℤ))
  rw [← one_div]
  apply (le_div_iff₀ hp).2
  exact hb.trans (hh.trans (by norm_num))

/-- Explicit budget for all three smallness bridges, independent of m and Lambda. -/
def smallnessBudget (C₁ C₂ C₃ : ℝ) : ℝ :=
  1 + 4 * C₁ ^ 2 + 2 * C₂ + ((320 / 9) * C₃ * (1 + C₂)) ^ 2

/-- Pure algebra: a squared smallness budget controls a linear loss. -/
theorem linear_smallness_of_square {t C D : ℝ} (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hD : 0 < D) (hbudget : 4 * C ^ 2 ≤ D) (hsmall : t ^ 2 ≤ D⁻¹) :
    C * t ≤ 1 / 2 := by
  have hmul := mul_le_mul_of_nonneg_left hsmall (sq_nonneg C)
  have hdiv : C ^ 2 * D⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hD).2
    linarith only [hbudget]
  have hs : (C * t) ^ 2 ≤ 1 / 4 := by
    calc
      (C * t) ^ 2 = C ^ 2 * t ^ 2 := by ring
      _ ≤ C ^ 2 * D⁻¹ := hmul
      _ ≤ 1 / 4 := hdiv
  have hp := mul_nonneg hC ht
  nlinarith only [hs, hp]

/-- The explicit power threshold for any desired coefficient and tolerance. -/
theorem power_smallness_of_threshold {E p C η : ℝ} (hE : 0 ≤ E) (hp : 0 < p)
    (hC : 0 < C) (hη : 0 ≤ η) (hsmall : E ≤ (η / C) ^ p⁻¹) :
    C * E ^ p ≤ η := by
  have h := Real.rpow_le_rpow hE hsmall hp.le
  rw [Real.rpow_inv_rpow (div_nonneg hη hC.le) hp.ne'] at h
  have hh := mul_le_mul_of_nonneg_left h hC.le
  simpa only [mul_div_cancel₀ _ hC.ne'] using hh

/-- The gamma and derivative budgets needed by Section 4, reusing the numeric layer. -/
theorem section4_exponent_budgets {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    4 * delta β ≤ gamma β ∧
      0 < q β - 1 - gamma β / 2 ∧
      8 * delta β + 4 * (q β - 1) * (β + gamma β) ≤ delta β * (Nstar β : ℝ) :=
  ⟨Infra.Numeric.gamma_ge_four_delta hβ hβ', Infra.Numeric.kill_half_gamma hβ hβ',
    Infra.Numeric.Nstar_exponent_budget hβ hβ'⟩

/-- The algebraic e.condition bridge; only an upper exprat bound is used. -/
theorem condition_of_exprat_upper {E K T r : ℝ} (hK : 0 < K) (hT : 0 < T)
    (hupper : E ^ 2 / (K * T) ≤ r) (hsmall : r ≤ 1 / 2) : E ^ 2 ≤ (1 / 2) * K * T := by
  have h := (div_le_iff₀ (mul_pos hK hT)).1 (hupper.trans hsmall)
  simpa only [mul_assoc] using h

/-- The epsilon scales tend to zero through positive values. -/
theorem epsilon_tendsto_zero {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    Filter.Tendsto (epsilon β Λ) Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  have hL : 1 < (Λ : ℝ) := by exact_mod_cast (show 1 < Λ by omega)
  have he : ∀ n, 0 ≤ epsilon β Λ n :=
    fun _ => (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le
  have hbound : ∀ n, epsilon β Λ n ≤ ((Λ : ℝ)⁻¹) ^ n := by
    intro n
    have hh := epsilon_le_lambda_pow hβ hβ' hΛ (m := n)
    rw [Real.rpow_neg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hL.le), Real.rpow_natCast, ← inv_pow]
        at hh
    exact hh
  have hzero := squeeze_zero he hbound
    (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (le_trans (by norm_num : (0 : ℝ) ≤ 1)
        hL.le))
      (inv_lt_one_of_one_lt₀ hL))
  exact tendsto_nhdsWithin_iff.mpr ⟨hzero, Filter.Eventually.of_forall
    (fun _ => Infra.Cutoff.epsilon_pos hβ hβ' hΛ)⟩

end AVenhance.Infra.Section4
