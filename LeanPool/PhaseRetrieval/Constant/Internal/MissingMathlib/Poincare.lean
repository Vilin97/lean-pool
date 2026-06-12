/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # Poincare.lean
  Weak Poincaré inequality on intervals — the ONLY missing Mathlib result.
  Scaffolding notes: MissingMathlib/missing_results.md

  Dependencies: Mathlib only

  Public API:
  - `poincare_interval` (M1: Poincaré inequality on [0, h])
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.Common
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Parity

/-! # Poincare -/


open MeasureTheory Real Set intervalIntegral Filter

noncomputable section

namespace FockSPR

namespace MissingMathlib

/-! ## Auxiliary lemmas -/

/-- FTC: `f x - f y = ∫_y^x f' t dt` for `x, y ∈ Icc 0 h`. -/
private lemma ftc_sub {h : ℝ} {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ Icc 0 h, HasDerivAt f (f' x) x)
    (hf'_cont : ContinuousOn f' (Icc 0 h))
    {x y : ℝ} (hx : x ∈ Icc 0 h) (hy : y ∈ Icc 0 h) :
    f x - f y = ∫ t in y..x, f' t := by
  have huIcc : uIcc y x ⊆ Icc 0 h := uIcc_subset_Icc hy hx
  rw [eq_comm]
  exact integral_eq_sub_of_hasDerivAt
    (fun z hz => hf z (huIcc hz))
    ((hf'_cont.mono huIcc).intervalIntegrable)

/-- For x, y ∈ [0, h], ‖f x - f y‖ ≤ ∫₀ʰ ‖f' t‖ dt. -/
private lemma diff_norm_le {h : ℝ} (hh : 0 < h) {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ Icc 0 h, HasDerivAt f (f' x) x)
    (hf'_cont : ContinuousOn f' (Icc 0 h))
    {x y : ℝ} (hx : x ∈ Icc 0 h) (hy : y ∈ Icc 0 h) :
    ‖f x - f y‖ ≤ ∫ t in (0 : ℝ)..h, ‖f' t‖ := by
  rw [ftc_sub hf hf'_cont hx hy]
  have hf'_norm_int : IntervalIntegrable (fun t => ‖f' t‖) volume 0 h :=
    hf'_cont.norm.intervalIntegrable_of_Icc hh.le
  have hf'_nn : 0 ≤ᵐ[volume.restrict (Ioc 0 h)] fun t => ‖f' t‖ :=
    ae_of_all _ (fun _ => norm_nonneg _)
  rcases le_or_gt y x with hyx | hyx
  · -- Case y ≤ x: ‖∫_y^x f'‖ ≤ ∫_y^x ‖f'‖ ≤ ∫_0^h ‖f'‖
    calc ‖∫ t in y..x, f' t‖
        ≤ ∫ t in y..x, ‖f' t‖ := norm_integral_le_integral_norm hyx
      _ ≤ ∫ t in (0 : ℝ)..h, ‖f' t‖ :=
          integral_mono_interval hy.1 hyx hx.2 hf'_nn hf'_norm_int
  · -- Case x < y: ‖∫_y^x f'‖ = ‖-∫_x^y f'‖ = ‖∫_x^y f'‖ ≤ ∫_x^y ‖f'‖ ≤ ∫_0^h ‖f'‖
    rw [integral_symm]
    rw [norm_neg]
    calc ‖∫ t in x..y, f' t‖
        ≤ ∫ t in x..y, ‖f' t‖ := norm_integral_le_integral_norm hyx.le
      _ ≤ ∫ t in (0 : ℝ)..h, ‖f' t‖ :=
          integral_mono_interval hx.1 hyx.le hy.2 hf'_nn hf'_norm_int

/-- Pointwise bound: `‖f x - f_bar‖ ≤ ∫₀ʰ ‖f' t‖ dt` for `x ∈ [0, h]`. -/
private lemma pointwise_bound {h : ℝ} (hh : 0 < h) {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ Icc 0 h, HasDerivAt f (f' x) x)
    (hf_cont : ContinuousOn f (Icc 0 h))
    (hf'_cont : ContinuousOn f' (Icc 0 h))
    {x : ℝ} (hx : x ∈ Icc 0 h) :
    ‖f x - (1 / h) • ∫ y in (0 : ℝ)..h, f y‖ ≤ ∫ t in (0 : ℝ)..h, ‖f' t‖ := by
  set M := ∫ t in (0 : ℝ)..h, ‖f' t‖
  have hbd : ∀ y ∈ Icc 0 h, ‖f x - f y‖ ≤ M := fun y hy => diff_norm_le hh hf hf'_cont hx hy
  have hh_ne : (h : ℝ) ≠ 0 := ne_of_gt hh
  have hf_int : IntervalIntegrable f volume 0 h := hf_cont.intervalIntegrable_of_Icc hh.le
  have hfx_sub_int : IntervalIntegrable (fun y => f x - f y) volume 0 h :=
    IntervalIntegrable.sub intervalIntegrable_const hf_int
  -- Convert (1/h) • I to ℂ multiplication
  set I := ∫ y in (0 : ℝ)..h, f y
  rw [show (1 / h : ℝ) • I = (↑(1 / h) : ℂ) * I from Complex.real_smul]
  -- ∫(f x - f y) dy = h • f x - I
  have hh_ne_C : (h : ℂ) ≠ 0 := by exact_mod_cast hh_ne
  have h_int_diff : (∫ y in (0 : ℝ)..h, (f x - f y)) = h • f x - I := by
    have := intervalIntegral.integral_sub (μ := volume) (a := (0 : ℝ)) (b := h)
      (f := fun _ => f x) (g := f)
      intervalIntegrable_const hf_int
    simp only [intervalIntegral.integral_const, sub_zero] at this
    exact this
  -- Rewrite: f x - (↑(1/h)) * I = (↑(1/h)) * (h • f x - I)
  have h_rewrite : f x - (↑(1 / h) : ℂ) * I = (↑(1 / h) : ℂ) * ∫ y in (0 : ℝ)..h, (f x - f y) := by
    rw [h_int_diff, Complex.real_smul, mul_sub]
    push_cast
    rw [one_div]
    congr 1
    rw [← mul_assoc, inv_mul_cancel₀ hh_ne_C, one_mul]
  rw [h_rewrite]
  -- ‖(↑(1/h)) * ∫(f x - f y)‖ = ‖↑(1/h)‖ * ‖∫(f x - f y)‖ = (1/h) * ‖∫(f x - f y)‖
  rw [norm_mul]
  -- ‖↑(1/h)‖ = 1/h since 1/h > 0
  have h_norm_coeff : ‖(↑(1 / h) : ℂ)‖ = 1 / h := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h)]
  rw [h_norm_coeff]
  -- Goal: 1/h * ‖∫(f x - f y)‖ ≤ M
  have h_norm_bound : ‖∫ y in (0 : ℝ)..h, (f x - f y)‖ ≤ h * M := by
    calc ‖∫ y in (0 : ℝ)..h, (f x - f y)‖
        ≤ ∫ y in (0 : ℝ)..h, ‖f x - f y‖ := norm_integral_le_integral_norm hh.le
      _ ≤ ∫ _ in (0 : ℝ)..h, M := by
          apply integral_mono_on hh.le
          · exact hfx_sub_int.norm
          · exact intervalIntegrable_const
          · exact hbd
      _ = h * M := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  calc 1 / h * ‖∫ y in (0 : ℝ)..h, (f x - f y)‖
      ≤ 1 / h * (h * M) := by
        exact mul_le_mul_of_nonneg_left h_norm_bound (by positivity)
    _ = M := by field_simp

-- to_mathlib: Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-- Cauchy-Schwarz for interval integrals:
  `(∫_a^b g)² ≤ (b - a) * ∫_a^b g²` for continuous `g`. -/
private lemma cauchy_schwarz_interval {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Icc a b)) :
    (∫ t in a..b, g t) ^ 2 ≤ (b - a) * ∫ t in a..b, g t ^ 2 := by
  by_cases hab' : a = b
  · subst hab'; simp
  have hab_lt : a < b := lt_of_le_of_ne hab hab'
  have hba_pos : 0 < b - a := sub_pos.mpr hab_lt
  set S := ∫ t in a..b, g t
  set c := S / (b - a) with hc_def
  -- Integrability facts
  have hg_int : IntervalIntegrable g volume a b :=
    hg_cont.intervalIntegrable_of_Icc hab
  have hg2_cont : ContinuousOn (fun t => g t ^ 2) (Icc a b) := hg_cont.pow 2
  have hg2_int : IntervalIntegrable (fun t => g t ^ 2) volume a b :=
    hg2_cont.intervalIntegrable_of_Icc hab
  -- Key identity: c * (b - a) = S
  have hcba : c * (b - a) = S := div_mul_cancel₀ _ (ne_of_gt hba_pos)
  -- Key: 0 ≤ ∫_a^b (g t - c)² dt
  have hvar : 0 ≤ ∫ t in a..b, (g t - c) ^ 2 :=
    integral_nonneg hab (fun u _ => sq_nonneg _)
  -- We show ∫(g-c)² = ∫g² - c²(b-a) by expanding and using c(b-a) = S
  -- First split: ∫(g-c)² = ∫g² + ∫(-2cg + c²)
  have hgc_sub_int : IntervalIntegrable (fun t => -2 * c * g t + c ^ 2) volume a b :=
    (hg_int.const_mul _).add intervalIntegrable_const
  have hexpand : ∫ t in a..b, (g t - c) ^ 2 =
      (∫ t in a..b, g t ^ 2) + (∫ t in a..b, (-2 * c * g t + c ^ 2)) := by
    have : (fun t => (g t - c) ^ 2) = (fun t => g t ^ 2 + (-2 * c * g t + c ^ 2)) := by
      ext t; ring
    rw [this, intervalIntegral.integral_add hg2_int hgc_sub_int]
  -- Compute ∫(-2cg + c²) = -2c·S + c²(b-a) = -2c²(b-a) + c²(b-a) = -c²(b-a)
  have hint_linear : ∫ t in a..b, (-2 * c * g t + c ^ 2) = -c ^ 2 * (b - a) := by
    rw [intervalIntegral.integral_add (hg_int.const_mul _) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    -- Goal: (-2 * c * ∫ g) + (b - a) * c ^ 2 = -c ^ 2 * (b - a)
    -- We know ∫ g = S = c * (b - a)
    have h_int_eq : ∫ x in a..b, g x = c * (b - a) := hcba.symm
    rw [h_int_eq]; ring
  rw [hexpand, hint_linear] at hvar
  -- Now hvar: 0 ≤ ∫g² + (-c²(b-a)) = ∫g² - c²(b-a)
  have h_ineq : c ^ 2 * (b - a) ≤ ∫ t in a..b, g t ^ 2 := by linarith
  -- And S² = c²·(b-a)², so S² ≤ (b-a)·∫g²
  calc S ^ 2 = (c * (b - a)) ^ 2 := by rw [hcba]
    _ = c ^ 2 * (b - a) * (b - a) := by ring
    _ ≤ (∫ t in a..b, g t ^ 2) * (b - a) := by
        exact mul_le_mul_of_nonneg_right h_ineq hba_pos.le
    _ = (b - a) * ∫ t in a..b, g t ^ 2 := by ring

/-! ## M1: Poincaré inequality on intervals (weak version) -/

/-- Weak Poincaré inequality on `[0, h]`: for an absolutely continuous function `f`,
  `∫_0^h ‖f(x) − f_bar‖² dx ≤ h² ∫_0^h ‖f'(x)‖² dx`
where `f_bar = (1/h) ∫_0^h f(x) dx`. -/
theorem poincare_interval {h : ℝ} (hh : 0 < h) {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ Icc 0 h, HasDerivAt f (f' x) x)
    (hf_cont : ContinuousOn f (Icc 0 h))
    (hf'_cont : ContinuousOn f' (Icc 0 h)) :
    let f_bar := (1 / h) • ∫ x in (0 : ℝ)..h, f x
    ∫ x in (0 : ℝ)..h, ‖f x - f_bar‖ ^ 2 ≤
      h ^ 2 * ∫ x in (0 : ℝ)..h, ‖f' x‖ ^ 2 := by
  intro f_bar
  -- Let M := ∫₀ʰ ‖f' t‖ dt
  set M := ∫ t in (0 : ℝ)..h, ‖f' t‖ with hM_def
  -- Step 1: Pointwise bound: ‖f x - f_bar‖² ≤ M² for x ∈ [0, h]
  have hpw : ∀ x ∈ Icc 0 h, ‖f x - f_bar‖ ^ 2 ≤ M ^ 2 := by
    intro x hx
    apply sq_le_sq'
    · linarith [norm_nonneg (f x - f_bar), pointwise_bound hh hf hf_cont hf'_cont hx]
    · exact pointwise_bound hh hf hf_cont hf'_cont hx
  -- Step 2: ∫₀ʰ ‖f x - f_bar‖² dx ≤ ∫₀ʰ M² dx = h * M²
  have hint_bound : ∫ x in (0 : ℝ)..h, ‖f x - f_bar‖ ^ 2 ≤ h * M ^ 2 := by
    have h1 : ∫ x in (0 : ℝ)..h, ‖f x - f_bar‖ ^ 2 ≤ ∫ _ in (0 : ℝ)..h, M ^ 2 := by
      apply integral_mono_on hh.le
      · exact ((hf_cont.sub continuousOn_const).norm.pow 2).intervalIntegrable_of_Icc hh.le
      · exact intervalIntegrable_const
      · exact hpw
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1
    exact h1
  -- Step 3: CS: M² ≤ h * ∫₀ʰ ‖f' t‖² dt
  have hCS : M ^ 2 ≤ h * ∫ t in (0 : ℝ)..h, ‖f' t‖ ^ 2 := by
    have := cauchy_schwarz_interval hh.le hf'_cont.norm
    simp only [sub_zero] at this
    exact this
  -- Step 4: Combine
  calc ∫ x in (0 : ℝ)..h, ‖f x - f_bar‖ ^ 2
      ≤ h * M ^ 2 := hint_bound
    _ ≤ h * (h * ∫ t in (0 : ℝ)..h, ‖f' t‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left hCS (le_of_lt hh)
    _ = h ^ 2 * ∫ t in (0 : ℝ)..h, ‖f' t‖ ^ 2 := by ring

end MissingMathlib

end FockSPR
