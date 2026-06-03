/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Probability.Moments.IntegrableExpMul
import LeanPool.OSforGFF.General.SchwartzTranslationDecay

/-!
# Quantitative Decay for Schwartz Bilinear Forms

This file proves that bilinear integrals of Schwartz functions against an
exponentially decaying kernel have polynomial decay at any rate.

## Main Result

`schwartz_bilinear_translation_decay_polynomial_proof`: For Schwartz functions f, g
and a kernel K with exponential decay |K(z)| ≤ C_K * exp(-m‖z‖), the bilinear
integral decays polynomially:

  |∫∫ f(x) · K(x - y) · g(y - a) dx dy| ≤ c * (1 + ‖a‖)^{-α}

for any α > 0.

## Proof Strategy

1. Define a PolynomialDecayBound structure to track decay constants
2. Show Schwartz functions have polynomial decay (via Mathlib seminorms)
3. Prove exponential decay implies polynomial decay at any rate
4. Prove split convolution lemma: conv of two polynomial-decay functions decays
5. Apply to the bilinear integral by decomposing K = K_sing + K_tail

## References

- Reed-Simon Vol. II, Ch. X (decay of correlations)
- Glimm-Jaffe "Quantum Physics" Sec. 6.2 (clustering bounds)
-/

open MeasureTheory Complex SchwartzMap Filter Set Function Metric
open scoped Real Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## Phase 1: Polynomial Decay Structure and Schwartz Bridge -/

/-- A function f has polynomial decay of order N with constant C if
    ‖f(x)‖ ≤ C / (1 + ‖x‖)^N for all x.
-/
structure PolynomialDecayBound {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (f : E → F) (N : ℝ) where
  /-- Positive constant controlling the polynomial decay bound. -/
  C : ℝ
  hC_pos : C > 0
  bound : ∀ x : E, ‖f x‖ ≤ C / (1 + ‖x‖)^N

/-- Schwartz functions have polynomial decay at any natural number rate.

This follows from SchwartzMap.one_add_le_sup_seminorm_apply:
  (1 + ‖x‖)^k * ‖D^n f(x)‖ ≤ 2^k * seminorm_{k,n} f

Taking n = 0 and rearranging gives ‖f(x)‖ ≤ C * (1 + ‖x‖)^{-k}.
-/
def schwartzHasPolynomialDecay (f : SchwartzMap E ℂ) (k : ℕ) :
    PolynomialDecayBound f (k : ℝ) := by
  -- Use SchwartzMap.one_add_le_sup_seminorm_apply with m = (k, 0)
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0))
    (le_refl k) (Nat.zero_le 0) f
  -- h : ∀ x, (1 + ‖x‖)^k * ‖iteratedFDeriv ℝ 0 f x‖ ≤ 2^k * sup_seminorm f
  set C := 2^k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f with hC_def
  have hC_nonneg : 0 ≤ C := by
    apply mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)
    exact apply_nonneg _ _
  refine ⟨C + 1, by linarith, ?_⟩
  intro x
  have h1 : 0 < 1 + ‖x‖ := by positivity
  have hx := h x
  -- Convert ‖iteratedFDeriv ℝ 0 f x‖ to ‖f x‖
  have h_norm_eq : ‖iteratedFDeriv ℝ 0 (⇑f) x‖ = ‖f x‖ := by
    simp only [iteratedFDeriv_zero_eq_comp]
    exact ContinuousMultilinearMap.norm_constOfIsEmpty ℝ (fun _ : Fin 0 => E) (f x)
  rw [h_norm_eq] at hx
  -- hx : (1 + ‖x‖)^k * ‖f x‖ ≤ C
  have h_rearrange : ‖f x‖ ≤ C / (1 + ‖x‖)^(k : ℝ) := by
    rw [Real.rpow_natCast]
    rw [le_div_iff₀ (pow_pos h1 k)]
    calc ‖f x‖ * (1 + ‖x‖) ^ k
        = (1 + ‖x‖) ^ k * ‖f x‖ := by ring
      _ ≤ C := hx
  calc ‖f x‖
      ≤ C / (1 + ‖x‖)^(k : ℝ) := h_rearrange
    _ ≤ (C + 1) / (1 + ‖x‖)^(k : ℝ) := by
        gcongr
        linarith

/-- Schwartz functions have polynomial decay at any real rate (via ceiling). -/
def schwartzHasPolynomialDecayReal (f : SchwartzMap E ℂ) (N : ℝ) (_hN : N > 0) :
    PolynomialDecayBound f N := by
  let _ := _hN
  -- Use the natural number version with k = ⌈N⌉
  obtain ⟨C, hC_pos, hbound⟩ := schwartzHasPolynomialDecay f (⌈N⌉₊)
  refine ⟨C, hC_pos, fun x => ?_⟩
  have h1 : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
  calc ‖f x‖
      ≤ C / (1 + ‖x‖)^(⌈N⌉₊ : ℝ) := hbound x
    _ ≤ C / (1 + ‖x‖)^N := by
        apply div_le_div_of_nonneg_left (le_of_lt hC_pos)
        · positivity
        exact Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil N)

/-! ## Phase 2: Exponential to Polynomial Conversion -/

/-- For any α > 0 and m > 0, exponential decay implies polynomial decay:
    exp(-mx) ≤ C * (1 + x)^{-α} for all x ≥ 0.

This uses the fact that x^α * exp(-mx) is bounded (it tends to 0 at infinity).
-/
lemma exp_decay_implies_polynomial_decay (m α : ℝ) (hm : m > 0) (hα : α > 0) :
    ∃ C : ℝ, C > 0 ∧ ∀ x : ℝ, x ≥ 0 → Real.exp (-m * x) ≤ C * (1 + x)^(-α) := by
  -- We show (1+x)^α * exp(-mx) is bounded using u^p ≤ (p/|t|)^p * exp(|t|u)
  -- Applied to u = 1 + x, we get a bound involving exp(m(1+x))
  use (α / m) ^ α * Real.exp m + 1
  constructor
  · -- Positivity of the constant
    positivity
  · intro x hx
    have h_one_plus_pos : 0 < 1 + x := by positivity
    -- Use ProbabilityTheory.rpow_abs_le_mul_exp_abs
    -- For u ≥ 0: u^α ≤ (α/t)^α * exp(t*u) for any t > 0
    have h_poly_exp : (1 + x) ^ α ≤ (α / m) ^ α * Real.exp (m * (1 + x)) := by
      have := ProbabilityTheory.rpow_abs_le_mul_exp_abs (1 + x) (p := α) hα.le (ne_of_gt hm)
      simp only [abs_of_nonneg (le_of_lt h_one_plus_pos), abs_of_pos hm] at this
      exact this
    -- Rearrange: (1+x)^α * exp(-mx) ≤ (α/m)^α * exp(m(1+x)) * exp(-mx)
    --                                = (α/m)^α * exp(m + mx - mx) = (α/m)^α * exp(m)
    have h_exp_combine : Real.exp (m * (1 + x)) * Real.exp (-m * x) = Real.exp m := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h_one_plus_nonneg : 0 ≤ 1 + x := h_one_plus_pos.le
    have h_rpow_cancel : (1 + x)^α * (1 + x)^(-α) = 1 := by
      rw [← Real.rpow_add h_one_plus_pos]; simp
    calc Real.exp (-m * x)
        = Real.exp (-m * x) * 1 := by ring
      _ = Real.exp (-m * x) * ((1 + x)^α * (1 + x)^(-α)) := by rw [h_rpow_cancel]
      _ = (1 + x)^α * Real.exp (-m * x) * (1 + x)^(-α) := by ring
      _ ≤ ((α / m)^α * Real.exp (m * (1 + x))) * Real.exp (-m * x) * (1 + x)^(-α) := by
          gcongr
      _ = (α / m)^α * (Real.exp (m * (1 + x)) * Real.exp (-m * x)) * (1 + x)^(-α) := by ring
      _ = (α / m)^α * Real.exp m * (1 + x)^(-α) := by rw [h_exp_combine]
      _ ≤ ((α / m)^α * Real.exp m + 1) * (1 + x)^(-α) := by
          have hrpow : (1 + x)^(-α) ≥ 0 := Real.rpow_nonneg h_one_plus_nonneg _
          nlinarith

/-- Exponential decay of norms implies polynomial decay bounds. -/
def normExpDecayImpliesPolynomialDecay {F : Type*} [NormedAddCommGroup F]
    (g : E → F) (m C_exp R₀ : ℝ) (hm : m > 0) (hC_exp : C_exp > 0) (hR₀ : R₀ > 0)
    (hg_decay : ∀ z : E, ‖z‖ ≥ R₀ → ‖g z‖ ≤ C_exp * Real.exp (-m * ‖z‖))
    (hg_bdd : ∃ M : ℝ, ∀ z : E, ‖g z‖ ≤ M)  -- g is globally bounded
    (α : ℝ) (hα : α > 0) :
    PolynomialDecayBound g α := by
  -- Use Classical.choose since PolynomialDecayBound is data, not Prop
  let M := Classical.choose hg_bdd
  have hM : ∀ z : E, ‖g z‖ ≤ M := Classical.choose_spec hg_bdd
  -- Get the polynomial bound from exp_decay_implies_polynomial_decay
  have h_exp := exp_decay_implies_polynomial_decay m α hm hα
  let C_poly := Classical.choose h_exp
  have hC_poly_spec := Classical.choose_spec h_exp
  have hC_poly_pos : C_poly > 0 := hC_poly_spec.1
  have hC_poly : ∀ x : ℝ, x ≥ 0 → Real.exp (-m * x) ≤ C_poly * (1 + x)^(-α) := hC_poly_spec.2
  -- For ‖z‖ ≥ R₀: ‖g z‖ ≤ C_exp * exp(-m‖z‖) ≤ C_exp * C_poly * (1+‖z‖)^{-α}
  -- For ‖z‖ < R₀: ‖g z‖ ≤ M ≤ M * (1+R₀)^α * (1+‖z‖)^{-α} since (1+‖z‖)^{-α} ≥ (1+R₀)^{-α}
  let C := max (C_exp * C_poly) (M * (1 + R₀)^α) + 1
  refine ⟨C, by positivity, ?_⟩
  intro z
  have h_one_plus_pos : 0 < 1 + ‖z‖ := by positivity
  by_cases hz : ‖z‖ ≥ R₀
  · -- Outside R₀: use exponential decay bound
    have h_rpow_eq : C * (1 + ‖z‖)^(-α) = C / (1 + ‖z‖)^α := by
      rw [Real.rpow_neg (le_of_lt h_one_plus_pos)]
      ring
    rw [← h_rpow_eq]
    calc ‖g z‖
        ≤ C_exp * Real.exp (-m * ‖z‖) := hg_decay z hz
      _ ≤ C_exp * (C_poly * (1 + ‖z‖)^(-α)) := by
          gcongr
          exact hC_poly ‖z‖ (norm_nonneg z)
      _ = (C_exp * C_poly) * (1 + ‖z‖)^(-α) := by ring
      _ ≤ C * (1 + ‖z‖)^(-α) := by
          gcongr
          calc C_exp * C_poly ≤ max (C_exp * C_poly) (M * (1 + R₀)^α) := le_max_left _ _
            _ ≤ C := by simp only [C]; linarith
  · -- Inside R₀: use global bound
    push Not at hz
    have h_one_plus_R₀_pos : 0 < 1 + R₀ := by linarith
    have h_rpow_mono : (1 + ‖z‖)^(-α) ≥ (1 + R₀)^(-α) := by
      have h1 : 1 + ‖z‖ ≤ 1 + R₀ := by linarith
      have h2 : (1 + ‖z‖)^α ≤ (1 + R₀)^α :=
        Real.rpow_le_rpow (by linarith) h1 hα.le
      rw [Real.rpow_neg (le_of_lt h_one_plus_pos), Real.rpow_neg (le_of_lt h_one_plus_R₀_pos)]
      rw [ge_iff_le, inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos h_one_plus_pos α) h2
    have h_rpow_eq : C * (1 + ‖z‖)^(-α) = C / (1 + ‖z‖)^α := by
      rw [Real.rpow_neg (le_of_lt h_one_plus_pos)]
      ring
    rw [← h_rpow_eq]
    have hM_nonneg : 0 ≤ M * (1 + R₀)^α := by
      apply mul_nonneg
      · -- M ≥ ‖g 0‖ ≥ 0 since ‖g 0‖ ≥ 0
        have := hM 0
        linarith [norm_nonneg (g 0)]
      · exact Real.rpow_nonneg (le_of_lt h_one_plus_R₀_pos) α
    calc ‖g z‖
        ≤ M := hM z
      _ = M * 1 := by ring
      _ = M * ((1 + R₀)^α * (1 + R₀)^(-α)) := by
          rw [← Real.rpow_add h_one_plus_R₀_pos]; simp
      _ = (M * (1 + R₀)^α) * (1 + R₀)^(-α) := by ring
      _ ≤ (M * (1 + R₀)^α) * (1 + ‖z‖)^(-α) := by
          gcongr
      _ ≤ C * (1 + ‖z‖)^(-α) := by
          gcongr
          calc M * (1 + R₀)^α ≤ max (C_exp * C_poly) (M * (1 + R₀)^α) := le_max_right _ _
            _ ≤ C := by simp only [C]; linarith

/-! ## Phase 3: Split Convolution Lemma -/

/-- Helper: (1 + x/2)^{-N} ≤ 2^N * (1 + x)^{-N} for x ≥ 0 and N > 0.

This follows from 1 + x ≤ 2 + x = 2(1 + x/2), so (1+x)^N ≤ 2^N(1+x/2)^N.
-/
lemma one_add_half_pow_le (x : ℝ) (hx : x ≥ 0) (N : ℝ) (hN : N > 0) :
    (1 + x/2)^(-N) ≤ (2:ℝ)^N * (1 + x)^(-N) := by
  have h1 : 0 < 1 + x/2 := by linarith
  have h2 : 0 < 1 + x := by positivity
  have h1_nonneg : 0 ≤ 1 + x/2 := h1.le
  have h2_nonneg : 0 ≤ 1 + x := h2.le
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  -- Key: 1 + x ≤ 2 * (1 + x/2) = 2 + x, so (1+x)^N ≤ (2*(1+x/2))^N = 2^N * (1+x/2)^N
  -- Therefore (1+x/2)^{-N} = 1/(1+x/2)^N ≤ 2^N/(1+x)^N = 2^N * (1+x)^{-N}
  have h_base : 1 + x ≤ 2 * (1 + x / 2) := by linarith
  have h_rpow_le : (1 + x)^N ≤ (2 * (1 + x / 2))^N :=
    Real.rpow_le_rpow h2_nonneg h_base hN.le
  have h_mul_rpow : (2 * (1 + x / 2))^N = 2^N * (1 + x/2)^N :=
    Real.mul_rpow (le_of_lt h2_pos) h1_nonneg
  rw [h_mul_rpow] at h_rpow_le
  -- Now: (1+x)^N ≤ 2^N * (1+x/2)^N
  -- We need: (1+x/2)^{-N} ≤ 2^N * (1+x)^{-N}
  -- i.e., 1/(1+x/2)^N ≤ 2^N / (1+x)^N
  rw [Real.rpow_neg h1_nonneg, Real.rpow_neg h2_nonneg]
  -- Goal: ((1 + x / 2) ^ N)⁻¹ ≤ 2 ^ N * ((1 + x) ^ N)⁻¹
  -- Equivalently: 1/(1+x/2)^N ≤ 2^N/(1+x)^N
  -- Multiply both sides by (1+x/2)^N and divide by (1+x)^{-N}:
  -- (1+x)^N ≤ 2^N * (1+x/2)^N, which is h_rpow_le
  have h1_rpow_pos : 0 < (1 + x / 2) ^ N := Real.rpow_pos_of_pos h1 N
  have h2_rpow_pos : 0 < (1 + x) ^ N := Real.rpow_pos_of_pos h2 N
  have h_two_rpow_pos : 0 < (2:ℝ) ^ N := Real.rpow_pos_of_pos h2_pos N
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div]
  rw [div_le_div_iff₀ h1_rpow_pos h2_rpow_pos]
  calc 1 * (1 + x) ^ N = (1 + x) ^ N := by ring
    _ ≤ (2:ℝ) ^ N * (1 + x / 2) ^ N := h_rpow_le

/-- Core lemma: If u, v both have polynomial decay of order N > dim(E),
    then their convolution also has polynomial decay of order N.

    The proof splits the integral at |y| = |x|/2:
    - Region A (|y| ≥ |x|/2): u(y) is small, v integrable
    - Region B (|y| < |x|/2): v(x-y) is small (since |x-y| ≥ |x|/2), u integrable
-/
private lemma convolution_polynomial_decay_exists
    {u v : E → ℂ} {N : ℝ} (hN_dim : N > Module.finrank ℝ E)
    (hu_decay : PolynomialDecayBound u N)
    (hv_decay : PolynomialDecayBound v N)
    (hu_int : Integrable u) (hv_int : Integrable v) :
    ∃ _result : PolynomialDecayBound (fun x => ∫ y, u y * v (x - y)) N, True := by
  refine ⟨?_, trivial⟩
  obtain ⟨C_u, hC_u_pos, hu_bound⟩ := hu_decay
  obtain ⟨C_v, hC_v_pos, hv_bound⟩ := hv_decay
  -- The L¹ norms
  let I_u := ∫ y, ‖u y‖
  let I_v := ∫ y, ‖v y‖
  have hI_u_nonneg : 0 ≤ I_u := integral_nonneg (fun _ => norm_nonneg _)
  have hI_v_nonneg : 0 ≤ I_v := integral_nonneg (fun _ => norm_nonneg _)
  -- Constant: combines the decay constants and L¹ norms
  -- Using the 2^N factor from one_add_half_pow_le
  let C := 2^N * (C_u * (I_v + 1) + C_v * (I_u + 1)) + 1
  refine ⟨C, by positivity, ?_⟩
  intro x
  have h_one_plus_pos : 0 < 1 + ‖x‖ := by positivity
  -- Split set: A = {y : ‖y‖ ≥ ‖x‖/2}
  let A : Set E := {y | ‖y‖ ≥ ‖x‖ / 2}
  have hA_meas : MeasurableSet A := measurableSet_le measurable_const measurable_norm
  -- Integrability of the integrand
  have hv_shift : Integrable (fun y => v (x - y)) volume := hv_int.comp_sub_left x
  have h_int : Integrable (fun y => u y * v (x - y)) volume := by
    -- Use that u is integrable and v(x - ·) is bounded
    refine Integrable.mul_bdd (c := C_v) hu_int hv_shift.aestronglyMeasurable ?_
    filter_upwards with y
    have hle : 1 ≤ 1 + ‖x - y‖ := le_add_of_nonneg_right (norm_nonneg _)
    have hN_pos : N > 0 := lt_of_le_of_lt (Nat.cast_nonneg _) hN_dim
    calc ‖v (x - y)‖ ≤ C_v / (1 + ‖x - y‖)^N := hv_bound (x - y)
      _ ≤ C_v / 1 := by
          apply div_le_div_of_nonneg_left (le_of_lt hC_v_pos) one_pos
          exact Real.one_le_rpow hle hN_pos.le
      _ = C_v := div_one _
  -- Integrability of ‖u‖ * ‖v(x - ·)‖
  have h_prod_int : Integrable (fun y => ‖u y‖ * ‖v (x - y)‖) volume := by
    have h_eq : (fun y => ‖u y‖ * ‖v (x - y)‖) = (fun y => ‖u y * v (x - y)‖) := by
      ext y; exact (norm_mul (u y) (v (x - y))).symm
    rw [h_eq]
    exact h_int.norm
  -- Bound on region A (‖y‖ ≥ ‖x‖/2): u is small
  have hA_bound : ∫ y in A, ‖u y‖ * ‖v (x - y)‖ ≤ C_u * 2^N / (1 + ‖x‖)^N * I_v := by
    let c_A := C_u / (1 + ‖x‖/2)^N
    have hc_A_pos : 0 < c_A := by positivity
    calc ∫ y in A, ‖u y‖ * ‖v (x - y)‖
        ≤ ∫ y in A, c_A * ‖v (x - y)‖ := by
          apply setIntegral_mono_on h_prod_int.integrableOn
            (hv_shift.norm.const_mul c_A).integrableOn hA_meas
          intro y hy
          gcongr
          calc ‖u y‖ ≤ C_u / (1 + ‖y‖)^N := hu_bound y
            _ ≤ c_A := by
              apply div_le_div_of_nonneg_left (le_of_lt hC_u_pos)
              · positivity
              · simp only [A, mem_setOf_eq] at hy
                exact Real.rpow_le_rpow (by positivity) (by linarith) (lt_of_le_of_lt
                  (Nat.cast_nonneg _) hN_dim).le
      _ = c_A * ∫ y in A, ‖v (x - y)‖ := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ c_A * ∫ y, ‖v (x - y)‖ := by
          have h_set_le := setIntegral_le_integral (s := A) hv_shift.norm
            (Eventually.of_forall fun _ => norm_nonneg _)
          exact mul_le_mul_of_nonneg_left h_set_le (le_of_lt hc_A_pos)
      _ = c_A * I_v := by
          congr 1
          exact MeasureTheory.integral_sub_left_eq_self (fun y => ‖v y‖) volume x
      _ ≤ (C_u * 2^N / (1 + ‖x‖)^N) * I_v := by
          gcongr
          -- c_A = C_u / (1 + ‖x‖/2)^N ≤ C_u * 2^N / (1 + ‖x‖)^N
          -- by one_add_half_pow_le: (1 + x/2)^{-N} ≤ 2^N * (1+x)^{-N}
          -- so C_u * (1 + x/2)^{-N} ≤ C_u * 2^N * (1+x)^{-N}
          have h_half := one_add_half_pow_le ‖x‖ (norm_nonneg x) N (by
            calc N > Module.finrank ℝ E := hN_dim
              _ ≥ 0 := Nat.cast_nonneg _)
          have h_half_pos : 0 < 1 + ‖x‖ / 2 := by positivity
          simp only [c_A]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          calc C_u * ((1 + ‖x‖ / 2) ^ N)⁻¹
              = C_u * (1 + ‖x‖ / 2)^(-N) := by rw [Real.rpow_neg (le_of_lt h_half_pos)]
            _ ≤ C_u * ((2:ℝ)^N * (1 + ‖x‖)^(-N)) := by gcongr
            _ = C_u * 2^N * (1 + ‖x‖)^(-N) := by ring
            _ = C_u * 2^N * ((1 + ‖x‖) ^ N)⁻¹ := by rw [Real.rpow_neg (le_of_lt h_one_plus_pos)]
  -- Bound on region Aᶜ (‖y‖ < ‖x‖/2): v(x-y) is small because ‖x-y‖ ≥ ‖x‖/2
  have hAc_bound : ∫ y in Aᶜ, ‖u y‖ * ‖v (x - y)‖ ≤ I_u * C_v * 2^N / (1 + ‖x‖)^N := by
    let c_Ac := C_v / (1 + ‖x‖/2)^N
    have hc_Ac_pos : 0 < c_Ac := by positivity
    calc ∫ y in Aᶜ, ‖u y‖ * ‖v (x - y)‖
        ≤ ∫ y in Aᶜ, ‖u y‖ * c_Ac := by
          apply setIntegral_mono_on h_prod_int.integrableOn
            (hu_int.norm.mul_const c_Ac).integrableOn hA_meas.compl
          intro y hy
          gcongr
          simp only [A, mem_compl_iff, mem_setOf_eq, not_le] at hy
          -- ‖x - y‖ ≥ ‖x‖ - ‖y‖ > ‖x‖ - ‖x‖/2 = ‖x‖/2
          have h_xy : ‖x - y‖ ≥ ‖x‖ / 2 := by
            have h1 : ‖x - y‖ ≥ ‖x‖ - ‖y‖ := norm_sub_norm_le x y
            have h2 : ‖x‖ - ‖y‖ > ‖x‖ - ‖x‖ / 2 := by linarith
            have h3 : ‖x‖ - ‖x‖ / 2 = ‖x‖ / 2 := by ring
            linarith
          have hN_pos : N > 0 := lt_of_le_of_lt (Nat.cast_nonneg _) hN_dim
          calc ‖v (x - y)‖ ≤ C_v / (1 + ‖x - y‖)^N := hv_bound (x - y)
            _ ≤ c_Ac := by
              apply div_le_div_of_nonneg_left (le_of_lt hC_v_pos)
              · positivity
              · exact Real.rpow_le_rpow (by positivity) (by linarith) hN_pos.le
      _ = (∫ y in Aᶜ, ‖u y‖) * c_Ac := by
          rw [MeasureTheory.integral_mul_const]
      _ ≤ I_u * c_Ac := by
          have h_set_le := setIntegral_le_integral (s := Aᶜ) hu_int.norm
            (Eventually.of_forall fun _ => norm_nonneg _)
          exact mul_le_mul_of_nonneg_right h_set_le (le_of_lt hc_Ac_pos)
      _ ≤ I_u * (C_v * 2^N / (1 + ‖x‖)^N) := by
          gcongr
          -- c_Ac = C_v / (1 + ‖x‖/2)^N ≤ C_v * 2^N / (1 + ‖x‖)^N
          have h_half := one_add_half_pow_le ‖x‖ (norm_nonneg x) N (by
            calc N > Module.finrank ℝ E := hN_dim
              _ ≥ 0 := Nat.cast_nonneg _)
          have h_half_pos : 0 < 1 + ‖x‖ / 2 := by positivity
          simp only [c_Ac]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          calc C_v * ((1 + ‖x‖ / 2) ^ N)⁻¹
              = C_v * (1 + ‖x‖ / 2)^(-N) := by rw [Real.rpow_neg (le_of_lt h_half_pos)]
            _ ≤ C_v * ((2:ℝ)^N * (1 + ‖x‖)^(-N)) := by gcongr
            _ = C_v * 2^N * (1 + ‖x‖)^(-N) := by ring
            _ = C_v * 2^N * ((1 + ‖x‖) ^ N)⁻¹ := by rw [Real.rpow_neg (le_of_lt h_one_plus_pos)]
      _ = I_u * C_v * 2^N / (1 + ‖x‖)^N := by ring
  -- Combine the bounds
  calc ‖∫ y, u y * v (x - y)‖
      ≤ ∫ y, ‖u y * v (x - y)‖ := norm_integral_le_integral_norm _
    _ = ∫ y, ‖u y‖ * ‖v (x - y)‖ := by congr 1; ext y; exact norm_mul _ _
    _ = (∫ y in A, ‖u y‖ * ‖v (x - y)‖) + (∫ y in Aᶜ, ‖u y‖ * ‖v (x - y)‖) :=
        (integral_add_compl hA_meas h_prod_int).symm
    _ ≤ C_u * 2^N / (1 + ‖x‖)^N * I_v + I_u * C_v * 2^N / (1 + ‖x‖)^N :=
        add_le_add hA_bound hAc_bound
    _ = 2^N * (C_u * I_v + C_v * I_u) / (1 + ‖x‖)^N := by ring
    _ ≤ 2^N * (C_u * (I_v + 1) + C_v * (I_u + 1)) / (1 + ‖x‖)^N := by
        gcongr
        · linarith
        · linarith
    _ = (2^N * (C_u * (I_v + 1) + C_v * (I_u + 1))) * (1 + ‖x‖)^(-N) := by
        rw [Real.rpow_neg (le_of_lt h_one_plus_pos)]
        ring
    _ ≤ C * (1 + ‖x‖)^(-N) := by
        gcongr
        simp only [C]
        linarith
    _ = C / (1 + ‖x‖)^N := by
        rw [Real.rpow_neg (le_of_lt h_one_plus_pos)]
        ring

/-- If two integrable functions have polynomial decay of order `N > dim E`, then their convolution
has polynomial decay of the same order. -/
def convolutionPolynomialDecay
    {u v : E → ℂ} {N : ℝ} (hN_dim : N > Module.finrank ℝ E)
    (hu_decay : PolynomialDecayBound u N)
    (hv_decay : PolynomialDecayBound v N)
    (hu_int : Integrable u) (hv_int : Integrable v) :
    PolynomialDecayBound (fun x => ∫ y, u y * v (x - y)) N :=
  (convolution_polynomial_decay_exists hN_dim hu_decay hv_decay hu_int hv_int).choose

/-! ## Phase 4: Kernel Decomposition Bounds -/

/-- The convolution of a Schwartz function with the singular part of the kernel
    (compactly supported) has polynomial decay.
-/
private lemma convolution_compactSupport_decay_exists (f : SchwartzMap E ℂ) (K : E → ℝ) (R₀ : ℝ)
    (hR₀ : R₀ > 0) (hK_loc : LocallyIntegrable K volume)
    (N : ℕ) (_hN : N > 0) :
    ∃ _result : PolynomialDecayBound
      (fun y => ∫ x, f x * (kernelSingular K R₀ (x - y) : ℂ)) (N : ℝ), True := by
  refine ⟨?_, trivial⟩
  let _ := _hN
  -- K_sing has support in closedBall 0 R₀
  -- (f ⋆ K_sing)(y) = ∫ f(x) K_sing(x-y) dx
  -- For |y| large, x-y ∈ supp(K_sing) implies x ∈ closedBall y R₀
  -- So only x near y contribute, and for large y, f(x) is small for all such x
  -- Use Schwartz decay
  obtain ⟨C_f, hC_f_pos, hf_bound⟩ := schwartzHasPolynomialDecay f N
  -- K_sing is integrable (compact support + locally integrable)
  have hK_sing_int : Integrable (kernelSingular K R₀) volume := by
    unfold kernelSingular
    have heq : (fun x => K x * (closedBall (0 : E) R₀).indicator (fun _ => (1 : ℝ)) x) =
               (closedBall (0 : E) R₀).indicator K := by
      ext x
      by_cases hx : x ∈ closedBall (0 : E) R₀
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
    rw [heq, integrable_indicator_iff isClosed_closedBall.measurableSet]
    exact hK_loc.integrableOn_isCompact (isCompact_closedBall 0 R₀)
  let I_Ksing := ∫ z, |kernelSingular K R₀ z|
  have hI_nonneg : 0 ≤ I_Ksing := integral_nonneg (fun _ => abs_nonneg _)
  -- Constant: C_f * (1 + R₀)^N * I_Ksing (with buffer for positivity)
  let C := C_f * (1 + R₀)^N * (I_Ksing + 1) + 1
  refine ⟨C, by positivity, ?_⟩
  intro y
  have h_one_plus_y_pos : 0 < 1 + ‖y‖ := by positivity
  have h_one_plus_R₀_pos : 0 < 1 + R₀ := by positivity
  -- Support property: kernelSingular K R₀ z = 0 unless ‖z‖ ≤ R₀
  have hK_sing_supp : ∀ z, kernelSingular K R₀ z ≠ 0 → ‖z‖ ≤ R₀ := by
    intro z hz
    unfold kernelSingular at hz
    by_contra h_not
    push Not at h_not
    have : z ∉ closedBall (0 : E) R₀ := by
      simp [mem_closedBall, dist_zero_right, not_le.mpr h_not]
    simp [indicator_of_notMem this] at hz
  -- Key step: Peetre's inequality
  -- If K_sing(x-y) ≠ 0, then ‖x-y‖ ≤ R₀, so:
  -- (1 + ‖y‖) ≤ (1 + ‖x‖) * (1 + ‖x-y‖) ≤ (1 + ‖x‖) * (1 + R₀)
  -- Therefore: 1/(1 + ‖x‖)^N ≤ (1 + R₀)^N / (1 + ‖y‖)^N
  have h_peetre : ∀ x, kernelSingular K R₀ (x - y) ≠ 0 →
      1 / (1 + ‖x‖)^(N : ℝ) ≤ (1 + R₀)^(N : ℝ) / (1 + ‖y‖)^(N : ℝ) := by
    intro x hx_supp
    have h_xy_le : ‖x - y‖ ≤ R₀ := hK_sing_supp (x - y) hx_supp
    have h_one_plus_x_pos : 0 < 1 + ‖x‖ := by positivity
    -- Peetre: 1 + ‖y‖ ≤ (1 + ‖x‖)(1 + ‖x - y‖) ≤ (1 + ‖x‖)(1 + R₀)
    have h_peetre_base : 1 + ‖y‖ ≤ (1 + ‖x‖) * (1 + R₀) := by
      have h1 : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
        calc ‖y‖ = ‖y - x + x‖ := by simp only [sub_add_cancel]
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
          _ = ‖x - y‖ + ‖x‖ := by rw [norm_sub_rev]
          _ = ‖x‖ + ‖x - y‖ := by ring
      calc 1 + ‖y‖ ≤ 1 + ‖x‖ + ‖x - y‖ := by linarith
        _ ≤ 1 + ‖x‖ + R₀ := by linarith
        _ ≤ (1 + ‖x‖) * (1 + R₀) := by nlinarith [norm_nonneg x]
    -- Raise to power N and rearrange
    have h_pow : (1 + ‖y‖)^(N : ℝ) ≤ ((1 + ‖x‖) * (1 + R₀))^(N : ℝ) := by
      apply Real.rpow_le_rpow (by linarith : 0 ≤ 1 + ‖y‖) h_peetre_base
      exact Nat.cast_nonneg N
    rw [Real.mul_rpow (le_of_lt h_one_plus_x_pos) (le_of_lt h_one_plus_R₀_pos)] at h_pow
    -- h_pow : (1 + ‖y‖)^N ≤ (1 + ‖x‖)^N * (1 + R₀)^N
    -- Goal: 1 / (1 + ‖x‖)^N ≤ (1 + R₀)^N / (1 + ‖y‖)^N
    -- Equivalently: (1 + ‖y‖)^N ≤ (1 + ‖x‖)^N * (1 + R₀)^N
    have h_x_rpow_pos : 0 < (1 + ‖x‖)^(N : ℝ) := Real.rpow_pos_of_pos h_one_plus_x_pos N
    have h_y_rpow_pos : 0 < (1 + ‖y‖)^(N : ℝ) := Real.rpow_pos_of_pos h_one_plus_y_pos N
    rw [div_le_div_iff₀ h_x_rpow_pos h_y_rpow_pos]
    calc 1 * (1 + ‖y‖) ^ (N : ℝ) = (1 + ‖y‖) ^ (N : ℝ) := by ring
      _ ≤ (1 + ‖x‖) ^ (N : ℝ) * (1 + R₀) ^ (N : ℝ) := h_pow
      _ = (1 + R₀) ^ (N : ℝ) * (1 + ‖x‖) ^ (N : ℝ) := by ring
  -- Shifted kernel integrability (needed in multiple places)
  have hK_shift_int : Integrable (fun x => |kernelSingular K R₀ (x - y)|) volume := by
    have h := hK_sing_int.comp_sub_right y
    exact h.abs
  -- Main calculation using Peetre inequality
  -- The integral bound follows from:
  -- 1. ‖f x‖ ≤ C_f / (1 + ‖x‖)^N (Schwartz decay)
  -- 2. On support of K_sing(x-y), Peetre gives: 1/(1+‖x‖)^N ≤ (1+R₀)^N/(1+‖y‖)^N
  -- 3. Change of variables: ∫ |K_sing(x-y)| dx = ∫ |K_sing(z)| dz = I_Ksing
  calc ‖∫ x, f x * (kernelSingular K R₀ (x - y) : ℂ)‖
      ≤ ∫ x, ‖f x * (kernelSingular K R₀ (x - y) : ℂ)‖ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖(kernelSingular K R₀ (x - y) : ℂ)‖ := by
        congr 1; ext x; exact norm_mul _ _
    _ ≤ ∫ x, (C_f / (1 + ‖x‖)^(N : ℝ)) * |kernelSingular K R₀ (x - y)| := by
        -- Use Schwartz decay and ‖(r : ℂ)‖ = |r|
        apply integral_mono_of_nonneg
        · exact Eventually.of_forall fun x => by positivity
        · -- Integrability: product of bounded function with shifted integrable function
          -- C_f / (1 + ‖x‖)^N ≤ C_f since (1 + ‖x‖)^N ≥ 1
          -- So integrand ≤ C_f * |K_sing(x - y)|, which is integrable
          have hbdd : ∀ x : E, C_f / (1 + ‖x‖)^(N : ℝ) ≤ C_f := fun x => by
            have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
            have h2 : 1 ≤ (1 + ‖x‖)^(N : ℝ) :=
              Real.one_le_rpow h1 (Nat.cast_nonneg N)
            calc C_f / (1 + ‖x‖)^(N : ℝ) ≤ C_f / 1 := by
                  apply div_le_div_of_nonneg_left (le_of_lt hC_f_pos) one_pos h2
              _ = C_f := by ring
          have hbnd_int := hK_shift_int.const_mul C_f
          -- Use Integrable.mono: if ‖f‖ ≤ g a.e. and g integrable, then f integrable
          refine Integrable.mono hbnd_int ?_ ?_
          · -- AEStronglyMeasurable: product of continuous and measurable
            have h_cont : Continuous (fun x : E => C_f / (1 + ‖x‖)^(N : ℝ)) := by
              apply Continuous.div continuous_const
              · refine Continuous.rpow_const ?_ (fun x => Or.inl ?_)
                · exact continuous_const.add continuous_norm
                · have := norm_nonneg x; linarith
              · intro x
                have hpos : 0 < 1 + ‖x‖ := by have := norm_nonneg x; linarith
                exact ne_of_gt (Real.rpow_pos_of_pos hpos N)
            exact h_cont.aestronglyMeasurable.mul hK_shift_int.aestronglyMeasurable
          · -- Bound: ‖(C_f / ...) * |...|‖ ≤ ‖C_f * |...|‖
            exact Eventually.of_forall fun x => by
              simp only [Real.norm_eq_abs, abs_mul, abs_abs]
              have h1 : |C_f / (1 + ‖x‖)^(N : ℝ)| = C_f / (1 + ‖x‖)^(N : ℝ) := by
                apply abs_of_nonneg; positivity
              have h2 : |C_f| = C_f := abs_of_pos hC_f_pos
              rw [h1, h2]
              exact mul_le_mul_of_nonneg_right (hbdd x) (abs_nonneg _)
        · apply Eventually.of_forall
          intro x
          simp only
          have hnorm : ‖(kernelSingular K R₀ (x - y) : ℂ)‖ = |kernelSingular K R₀ (x - y)| :=
            Complex.norm_real _
          rw [hnorm]
          apply mul_le_mul_of_nonneg_right (hf_bound x) (abs_nonneg _)
    _ ≤ ∫ x, (C_f * (1 + R₀)^(N : ℝ) / (1 + ‖y‖)^(N : ℝ)) * |kernelSingular K R₀ (x - y)| := by
        -- Key step: on support of K_sing(x-y), use Peetre to bound
        apply integral_mono_of_nonneg
        · exact Eventually.of_forall fun x => by positivity
        · -- Integrability: constant times shifted integrable function
          exact hK_shift_int.const_mul _
        · apply Eventually.of_forall
          intro x
          by_cases hx : kernelSingular K R₀ (x - y) = 0
          · simp only [hx, abs_zero, mul_zero, le_refl]
          · -- Use Peetre inequality
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            have hp := h_peetre x hx
            calc C_f / (1 + ‖x‖)^(N : ℝ)
                = C_f * (1 / (1 + ‖x‖)^(N : ℝ)) := by ring
              _ ≤ C_f * ((1 + R₀)^(N : ℝ) / (1 + ‖y‖)^(N : ℝ)) := by
                  apply mul_le_mul_of_nonneg_left hp (le_of_lt hC_f_pos)
              _ = C_f * (1 + R₀)^(N : ℝ) / (1 + ‖y‖)^(N : ℝ) := by ring
    _ = (C_f * (1 + R₀)^(N : ℝ) / (1 + ‖y‖)^(N : ℝ)) * ∫ x, |kernelSingular K R₀ (x - y)| := by
        -- Factor out the constant
        rw [MeasureTheory.integral_const_mul]
    _ = (C_f * (1 + R₀)^(N : ℝ) / (1 + ‖y‖)^(N : ℝ)) * I_Ksing := by
        congr 1
        -- Change of variables: z = x - y
        have hcov : ∫ x, |kernelSingular K R₀ (x - y)| = ∫ z, |kernelSingular K R₀ z| :=
          MeasureTheory.integral_sub_right_eq_self (fun z => |kernelSingular K R₀ z|) y
        exact hcov
    _ ≤ C / (1 + ‖y‖)^(N : ℝ) := by
        have h_rpow_pos : 0 < (1 + ‖y‖)^(N : ℝ) := Real.rpow_pos_of_pos h_one_plus_y_pos N
        -- Goal: C_f * (1 + R₀) ^ N / (1 + ‖y‖) ^ N * I_Ksing ≤ C / (1 + ‖y‖) ^ N
        -- Rewrite as: (C_f * (1 + R₀) ^ N * I_Ksing) / (1 + ‖y‖) ^ N ≤ C / (1 + ‖y‖) ^ N
        have heq : C_f * (1 + R₀) ^ (N : ℝ) / (1 + ‖y‖) ^ (N : ℝ) * I_Ksing =
            (C_f * (1 + R₀) ^ (N : ℝ) * I_Ksing) / (1 + ‖y‖) ^ (N : ℝ) := by ring
        rw [heq]
        apply div_le_div_of_nonneg_right _ (le_of_lt h_rpow_pos)
        calc C_f * (1 + R₀) ^ (N : ℝ) * I_Ksing
            ≤ C_f * (1 + R₀) ^ (N : ℝ) * (I_Ksing + 1) := by gcongr; linarith
          _ = C_f * (1 + R₀) ^ N * (I_Ksing + 1) := by rw [Real.rpow_natCast]
          _ ≤ C := by simp only [C]; linarith

/-- Convolution of a Schwartz function with the compactly supported singular kernel part has
polynomial decay. -/
def convolutionCompactSupportDecay (f : SchwartzMap E ℂ) (K : E → ℝ) (R₀ : ℝ)
    (hR₀ : R₀ > 0) (hK_loc : LocallyIntegrable K volume)
    (N : ℕ) (_hN : N > 0) :
    PolynomialDecayBound (fun y => ∫ x, f x * (kernelSingular K R₀ (x - y) : ℂ)) (N : ℝ) :=
  (convolution_compactSupport_decay_exists f K R₀ hR₀ hK_loc N _hN).choose

/-- The convolution of a Schwartz function with the tail part of the kernel
    (exponentially decaying) has polynomial decay at any rate.
-/
private lemma convolution_expDecay_polynomial_decay_exists (f : SchwartzMap E ℂ) (K : E → ℝ)
    (R₀ m C_K : ℝ) (hR₀ : R₀ > 0) (hm : m > 0) (hC_K : C_K > 0)
    (hK_loc : LocallyIntegrable K volume) -- For measurability
    (hK_decay : ∀ z : E, ‖z‖ ≥ R₀ → |K z| ≤ C_K * Real.exp (-m * ‖z‖))
    (hK_bdd : ∃ M : ℝ, ∀ z : E, |kernelTail K R₀ z| ≤ M)  -- K_tail is bounded
    (N : ℝ) (hN_dim : N > Module.finrank ℝ E) (hN : N > 0) :
    ∃ _result : PolynomialDecayBound
      (fun y => ∫ x, f x * (kernelTail K R₀ (x - y) : ℂ)) N, True := by
  refine ⟨?_, trivial⟩
  -- K_tail has exponential decay → polynomial decay (from exp_decay_implies_polynomial_decay)
  -- f has polynomial decay (Schwartz)
  -- Apply convolutionPolynomialDecay
  -- First show K_tail : E → ℂ (via ofReal) has polynomial decay
  have hK_tail_poly : PolynomialDecayBound (fun z => (kernelTail K R₀ z : ℂ)) N := by
    let M := Classical.choose hK_bdd
    have hM : ∀ z : E, |kernelTail K R₀ z| ≤ M := Classical.choose_spec hK_bdd
    apply normExpDecayImpliesPolynomialDecay (fun z => (kernelTail K R₀ z : ℂ))
      m C_K R₀ hm hC_K hR₀
    · intro z hz
      rw [Complex.norm_real]
      unfold kernelTail
      -- hz : ‖z‖ ≥ R₀. Either ‖z‖ > R₀ (in which case z ∈ complement) or ‖z‖ = R₀ (boundary)
      by_cases h_boundary : ‖z‖ = R₀
      · -- Boundary case: z ∈ closedBall, so kernelTail = 0
        have hmem : z ∈ closedBall (0 : E) R₀ := by
          simp [mem_closedBall, dist_zero_right]
          linarith
        have hnotmem : z ∉ (closedBall (0 : E) R₀)ᶜ := by simp [hmem]
        rw [indicator_of_notMem hnotmem]
        simp only [mul_zero, norm_zero, neg_mul, ge_iff_le]
        exact mul_nonneg hC_K.le (Real.exp_nonneg _)
      · -- Interior case: ‖z‖ > R₀
        have h_strict : ‖z‖ > R₀ := lt_of_le_of_ne hz (Ne.symm h_boundary)
        have hmem : z ∈ (closedBall (0 : E) R₀)ᶜ := by
          simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
          exact h_strict
        rw [indicator_of_mem hmem, mul_one]
        exact hK_decay z hz
    · exact ⟨M, fun z => by rw [Complex.norm_real]; exact hM z⟩
    · exact hN
  -- f has polynomial decay
  have hf_poly := schwartzHasPolynomialDecayReal f N hN
  -- Key observation: ∫ f(x) K_tail(x - y) dx = ∫ f(x) Ktilde(y - x) dx
  -- where Ktilde(z) = K_tail(-z). This is the standard convolution (f ⋆ Ktilde)(y).
  -- Define Ktilde (reflected K_tail)
  let K_refl : E → ℂ := fun z => (kernelTail K R₀ (-z) : ℂ)
  -- K_refl has the same polynomial decay as K_tail (since ‖-z‖ = ‖z‖)
  have hK_refl_poly : PolynomialDecayBound K_refl N := by
    obtain ⟨C, hC_pos, hbound⟩ := hK_tail_poly
    refine ⟨C, hC_pos, ?_⟩
    intro z
    simp only [K_refl]
    have h_neg : ‖(kernelTail K R₀ (-z) : ℂ)‖ = ‖(kernelTail K R₀ (-z) : ℂ)‖ := rfl
    calc ‖(kernelTail K R₀ (-z) : ℂ)‖
        ≤ C / (1 + ‖-z‖)^N := hbound (-z)
      _ = C / (1 + ‖z‖)^N := by rw [norm_neg]
  -- f is integrable (Schwartz)
  have hf_int : Integrable f volume := SchwartzMap.integrable f
  -- K_refl is integrable (from bounds + integrability machinery)
  have hK_refl_int : Integrable K_refl volume := by
    -- K_refl has polynomial decay with N > dim, so it's integrable
    -- For N > dim(E), ∫ C/(1+‖z‖)^N dz < ∞ (by integrable_one_add_norm)
    obtain ⟨C_poly, hC_poly_pos, hK_refl_bound⟩ := hK_refl_poly
    -- (1 + ‖z‖)^(-N) is integrable when N > dim
    have h_base_int : Integrable (fun z : E => (1 + ‖z‖)^(-N)) volume :=
      integrable_one_add_norm hN_dim
    -- K_refl is bounded by C_poly * (1 + ‖z‖)^(-N)
    have h_bound : ∀ z : E, ‖K_refl z‖ ≤ C_poly * (1 + ‖z‖)^(-N) := by
      intro z
      have hb := hK_refl_bound z
      rw [Real.rpow_neg (by linarith [norm_nonneg z] : 0 ≤ 1 + ‖z‖)]
      calc ‖K_refl z‖ ≤ C_poly / (1 + ‖z‖)^N := hb
        _ = C_poly * ((1 + ‖z‖)^N)⁻¹ := by ring
    -- Use Integrable.mono with bounding integrable function
    have h_bnd_int := h_base_int.const_mul C_poly
    refine Integrable.mono h_bnd_int ?_ ?_
    · -- AEStronglyMeasurable: K_refl z = (kernelTail K R₀ (-z) : ℂ)
      -- This follows from: K is locally integrable → K is AEStronglyMeasurable
      -- → kernelTail (indicator) is AEStronglyMeasurable
      -- → composition with negation preserves this
      -- → casting to ℂ preserves this
      haveI : ProperSpace E := FiniteDimensional.proper ℝ E
      haveI : SecondCountableTopology E := secondCountable_of_proper
      have h_K_aesm : AEStronglyMeasurable K volume :=
        LocallyIntegrable.aestronglyMeasurable hK_loc
      -- kernelTail K R₀ = K * indicator of complement of ball
      have h_Ktail_aesm : AEStronglyMeasurable (kernelTail K R₀) volume := by
        unfold kernelTail
        exact h_K_aesm.mul (aestronglyMeasurable_const.indicator measurableSet_closedBall.compl)
      have h_neg_aesm : AEStronglyMeasurable (fun z : E => kernelTail K R₀ (-z)) volume :=
        h_Ktail_aesm.comp_quasiMeasurePreserving (quasiMeasurePreserving_neg volume)
      exact continuous_ofReal.comp_aestronglyMeasurable h_neg_aesm
    · -- Bound: ‖K_refl z‖ ≤ ‖C_poly * (1 + ‖z‖)^(-N)‖
      exact Eventually.of_forall fun z => by
        have hb := h_bound z
        have h_nonneg : 0 ≤ C_poly * (1 + ‖z‖)^(-N) := by
          apply mul_nonneg (le_of_lt hC_poly_pos)
          exact Real.rpow_nonneg (by linarith [norm_nonneg z]) _
        rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
        exact hb
  -- The integral ∫ f(x) K_tail(x - y) dx equals (f ⋆ K_refl)(y)
  have h_conv_eq : ∀ y, ∫ x, f x * (kernelTail K R₀ (x - y) : ℂ) =
      ∫ x, f x * K_refl (y - x) := by
    intro y
    congr 1
    ext x
    simp only [K_refl]
    congr 1
    rw [neg_sub]
  -- Apply convolutionPolynomialDecay
  have h_conv := convolutionPolynomialDecay hN_dim hf_poly hK_refl_poly hf_int hK_refl_int
  -- Transfer the bound
  obtain ⟨C_conv, hC_conv_pos, h_conv_bound⟩ := h_conv
  refine ⟨C_conv, hC_conv_pos, ?_⟩
  intro y
  rw [h_conv_eq y]
  exact h_conv_bound y

/-- Convolution of a Schwartz function with the exponentially decaying kernel tail has polynomial
decay at any rate above the dimension. -/
def convolutionExpDecayPolynomialDecay (f : SchwartzMap E ℂ) (K : E → ℝ)
    (R₀ m C_K : ℝ) (hR₀ : R₀ > 0) (hm : m > 0) (hC_K : C_K > 0)
    (hK_loc : LocallyIntegrable K volume)
    (hK_decay : ∀ z : E, ‖z‖ ≥ R₀ → |K z| ≤ C_K * Real.exp (-m * ‖z‖))
    (hK_bdd : ∃ M : ℝ, ∀ z : E, |kernelTail K R₀ z| ≤ M)
    (N : ℝ) (hN_dim : N > Module.finrank ℝ E) (hN : N > 0) :
    PolynomialDecayBound (fun y => ∫ x, f x * (kernelTail K R₀ (x - y) : ℂ)) N :=
  (convolution_expDecay_polynomial_decay_exists f K R₀ m C_K hR₀ hm hC_K hK_loc
    hK_decay hK_bdd N hN_dim hN).choose

/-! ## Phase 5: Main Theorem Assembly -/

/-- **Quantitative polynomial decay for Schwartz bilinear forms** (proven theorem)

For Schwartz functions f, g and a kernel K with exponential decay
|K(z)| ≤ C_K · e^{-m‖z‖} (for large ‖z‖, from mass gap m > 0),
the bilinear integral decays polynomially at any rate α > 0:

  |∫∫ f(x) · K(x - y) · g(y - a) dx dy| ≤ c(f,g,α) · (1 + ‖a‖)^{-α}

The proof structure:
1. Decompose K = K_sing + K_tail
2. Show H(y) = ∫ f(x) K(x-y) dx = H_sing(y) + H_tail(y) has polynomial decay
3. The integral I(a) = ∫ H(y) g(y-a) dy = (H ⋆ gtilde)(a) where gtilde(z) = g(-z)
4. Apply convolutionPolynomialDecay to get the result
-/
theorem schwartz_bilinear_translation_decay_polynomial_proof
    (f g : SchwartzMap E ℂ)
    (K : E → ℝ)
    (hK_meas : Measurable K)
    (hK_loc : LocallyIntegrable K volume)
    (m : ℝ) (hm : m > 0)
    (C_K R₀ : ℝ) (hC_K : C_K > 0) (hR₀ : R₀ > 0)
    (_hK_cont : ContinuousOn K (closedBall (0 : E) R₀)ᶜ)
    (hK_decay : ∀ z : E, ‖z‖ ≥ R₀ → |K z| ≤ C_K * Real.exp (-m * ‖z‖))
    (α : ℝ) (hα : α > 0) :
    ∃ c : ℝ, c ≥ 0 ∧ ∀ a : E,
      ‖∫ x : E, ∫ y : E, f x * (K (x - y) : ℂ) * g (y - a)‖ ≤ c * (1 + ‖a‖)^(-α) := by
  -- Step 1: Decompose K = K_sing + K_tail
  let K_sing := kernelSingular K R₀
  let K_tail := kernelTail K R₀
  -- Step 2: Get dimension for the integrability condition
  let d := Module.finrank ℝ E
  -- Choose N > max(α, d) for integrability
  let N := max α d + 1
  have hN_pos : N > 0 := by simp only [N]; linarith [le_max_left α d, hα]
  have hN_gt_α : N > α := by simp only [N]; linarith [le_max_left α d]
  have hN_gt_d : N > d := by simp only [N]; linarith [le_max_right α d]
  -- Step 3: K_tail is bounded (from the decay bound on the complement)
  have hK_tail_bdd : ∃ M : ℝ, ∀ z : E, |kernelTail K R₀ z| ≤ M := by
    use max C_K 1
    intro z
    simp only [kernelTail]
    by_cases hz : z ∈ (closedBall (0 : E) R₀)ᶜ
    · rw [indicator_of_mem hz, mul_one]
      have hz' : ‖z‖ ≥ R₀ := by
        simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hz
        linarith
      calc |K z| ≤ C_K * Real.exp (-m * ‖z‖) := hK_decay z hz'
        _ ≤ C_K * Real.exp 0 := by gcongr; nlinarith [norm_nonneg z]
        _ = C_K := by simp
        _ ≤ max C_K 1 := le_max_left _ _
    · rw [indicator_of_notMem hz, mul_zero, abs_zero]
      exact le_of_lt (lt_max_of_lt_right one_pos)
  -- Step 4: Build H(y) = ∫ f(x) K(x-y) dx and show it has polynomial decay
  -- For the full proof, we need:
  -- 1. H_sing has polynomial decay (convolutionCompactSupportDecay)
  -- 2. H_tail has polynomial decay (convolutionExpDecayPolynomialDecay)
  -- 3. H = H_sing + H_tail has polynomial decay
  -- 4. The double integral = ∫ H(y) g(y-a) dy has polynomial decay (convolutionPolynomialDecay)
  -- Get the polynomial decay bounds
  have hf_poly := schwartzHasPolynomialDecayReal f N hN_pos
  have hg_poly := schwartzHasPolynomialDecayReal g N hN_pos
  -- Extract constants from the decay bounds
  obtain ⟨C_f, hC_f_pos, hf_bound⟩ := hf_poly
  obtain ⟨C_g, hC_g_pos, hg_bound⟩ := hg_poly
  -- Step 5: Build the inner function H(y) = ∫ f(x) K(x-y) dx and show polynomial decay
  -- We use kernel decomposition: K = K_sing + K_tail
  -- H = H_sing + H_tail where each has polynomial decay
  -- H_sing has polynomial decay (compactly supported kernel)
  have hH_sing := convolutionCompactSupportDecay f K R₀ hR₀ hK_loc
    (⌈N⌉₊) (Nat.ceil_pos.mpr hN_pos)
  -- H_tail has polynomial decay (exponentially decaying kernel)
  have hH_tail := convolutionExpDecayPolynomialDecay f K R₀ m C_K hR₀ hm hC_K hK_loc
    hK_decay hK_tail_bdd N hN_gt_d hN_pos
  -- Step 6: The double integral ∫∫ f(x) K(x-y) g(y-a) dx dy = ∫ H(y) g(y-a) dy
  -- where H(y) = ∫ f(x) K(x-y) dx = H_sing(y) + H_tail(y)
  -- For the bound, we use that H has polynomial decay and g has polynomial decay,
  -- so their convolution has polynomial decay.
  -- The full proof requires:
  -- 1. Showing H = H_sing + H_tail has polynomial decay
  -- 2. Showing the double integral equals ∫ H(y) g(y-a) dy
  -- 3. Applying convolutionPolynomialDecay to H and g
  -- 4. Converting from order N to order α (since N > α)
  -- Extract the decay bounds
  obtain ⟨C_Hsing, hC_Hsing_pos, hHsing_bound⟩ := hH_sing
  obtain ⟨C_Htail, hC_Htail_pos, hHtail_bound⟩ := hH_tail
  -- Schwartz integrability
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  haveI : SecondCountableTopology E := secondCountable_of_proper
  have hf_int : Integrable (⇑f) volume := f.integrable
  have hg_int : Integrable (⇑g) volume := g.integrable
  -- Combined H bound constant
  have hC_H : C_Hsing + C_Htail > 0 := by positivity
  -- ============================================================
  -- RESTRUCTURED: Build H and apply convolutionPolynomialDecay
  -- BEFORE introducing the existential constant
  -- ============================================================
  -- Define H(y) = ∫ f(x) K(x-y) dx
  let H : E → ℂ := fun y => ∫ x, f x * (K (x - y) : ℂ)
  -- Combine H_sing and H_tail bounds into H bound for all y
  have hH_combined : ∀ y : E, ‖H y‖ ≤ (C_Hsing + C_Htail) / (1 + ‖y‖)^N := fun y => by
    -- This proof is lengthy but self-contained - see below
    -- Use kernel decomposition: K = K_sing + K_tail
    have h_decomp : ∀ z, K z = kernelSingular K R₀ z + kernelTail K R₀ z := by
      intro z
      exact congrFun (kernel_decomposition K R₀) z
    -- Prove integrability of both terms
    have hK_sing_meas : Measurable (kernelSingular K R₀) := by
      unfold kernelSingular
      exact hK_meas.mul (measurable_const.indicator isClosed_closedBall.measurableSet)
    have hK_tail_meas : Measurable (kernelTail K R₀) := by
      unfold kernelTail
      exact hK_meas.mul (measurable_const.indicator isClosed_closedBall.measurableSet.compl)
    have hK_sing_int : Integrable (kernelSingular K R₀) volume := by
      unfold kernelSingular
      have heq : (fun x => K x * (closedBall (0 : E) R₀).indicator (fun _ => (1 : ℝ)) x) =
                 (closedBall (0 : E) R₀).indicator K := by
        ext x
        by_cases hx : x ∈ closedBall (0 : E) R₀
        · simp [indicator_of_mem hx]
        · simp [indicator_of_notMem hx]
      rw [heq, integrable_indicator_iff isClosed_closedBall.measurableSet]
      exact hK_loc.integrableOn_isCompact (isCompact_closedBall 0 R₀)
    obtain ⟨M_tail, hM_tail⟩ := hK_tail_bdd
    -- f is bounded by C_f (from Schwartz decay with denominator ≥ 1)
    have hf_bdd : ∀ x, ‖f x‖ ≤ C_f := fun x => by
      have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
      have h2 : 1 ≤ (1 + ‖x‖)^N := Real.one_le_rpow h1 hN_pos.le
      calc ‖f x‖ ≤ C_f / (1 + ‖x‖)^N := hf_bound x
        _ ≤ C_f / 1 := by
            apply div_le_div_of_nonneg_left (le_of_lt hC_f_pos) one_pos h2
        _ = C_f := by ring
    have hint1 : Integrable (fun x => f x * (kernelSingular K R₀ (x - y) : ℂ)) volume := by
      have hK_sing_shift : Integrable (fun x => kernelSingular K R₀ (x - y)) volume :=
        hK_sing_int.comp_sub_right y
      have hK_sing_shift_C : Integrable (fun x => (kernelSingular K R₀ (x - y) : ℂ)) volume :=
        hK_sing_shift.ofReal
      exact hK_sing_shift_C.bdd_mul (c := C_f) f.continuous.aestronglyMeasurable
        (Eventually.of_forall hf_bdd)
    have hint2 : Integrable (fun x => f x * (kernelTail K R₀ (x - y) : ℂ)) volume := by
      have hK_tail_shift_meas : Measurable (fun x => kernelTail K R₀ (x - y)) :=
        hK_tail_meas.comp (measurable_id.sub measurable_const)
      have hK_tail_shift_aesm : AEStronglyMeasurable
          (fun x => (kernelTail K R₀ (x - y) : ℂ)) volume :=
        hK_tail_shift_meas.complex_ofReal.aestronglyMeasurable
      have hK_tail_shift_bdd : ∀ x, ‖(kernelTail K R₀ (x - y) : ℂ)‖ ≤ M_tail := fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hM_tail (x - y)
      exact hf_int.mul_bdd (c := M_tail) hK_tail_shift_aesm
        (Eventually.of_forall hK_tail_shift_bdd)
    have hbound1 : ‖∫ x, f x * (kernelSingular K R₀ (x - y) : ℂ)‖ ≤ C_Hsing / (1 + ‖y‖)^N := by
      have h1 := hHsing_bound y
      have hle : N ≤ (⌈N⌉₊ : ℝ) := Nat.le_ceil N
      have hbase : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
      have hpow : (1 + ‖y‖)^N ≤ (1 + ‖y‖)^(⌈N⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase hle
      have hdenom_pos : 0 < (1 + ‖y‖)^N := by positivity
      calc ‖∫ x, f x * (kernelSingular K R₀ (x - y) : ℂ)‖ ≤ C_Hsing / (1 + ‖y‖)^(⌈N⌉₊ : ℝ) := h1
        _ ≤ C_Hsing / (1 + ‖y‖)^N :=
            div_le_div_of_nonneg_left (le_of_lt hC_Hsing_pos) hdenom_pos hpow
    have hbound2 : ‖∫ x, f x * (kernelTail K R₀ (x - y) : ℂ)‖ ≤ C_Htail / (1 + ‖y‖)^N :=
      hHtail_bound y
    have h_integrand : ∀ z, f z * (K (z - y) : ℂ) =
        f z * (kernelSingular K R₀ (z - y) : ℂ) + f z * (kernelTail K R₀ (z - y) : ℂ) := by
      intro z
      rw [h_decomp (z - y)]
      push_cast
      ring
    -- Unfold H to expose the integral, then rewrite
    change ‖∫ x, f x * (K (x - y) : ℂ)‖ ≤ (C_Hsing + C_Htail) / (1 + ‖y‖)^N
    simp_rw [h_integrand]
    let I₁ := ∫ x, f x * (kernelSingular K R₀ (x - y) : ℂ)
    let I₂ := ∫ x, f x * (kernelTail K R₀ (x - y) : ℂ)
    have hint_sum : ∫ x, (f x * (kernelSingular K R₀ (x - y) : ℂ) + f x * (kernelTail K R₀ (x - y)
      : ℂ)) = I₁ + I₂ :=
      integral_add hint1 hint2
    change ‖∫ x, f x * (kernelSingular K R₀ (x - y) : ℂ) + f x * (kernelTail K R₀ (x - y) : ℂ)‖ ≤
        (C_Hsing + C_Htail) / (1 + ‖y‖)^N
    rw [hint_sum]
    calc ‖I₁ + I₂‖ ≤ ‖I₁‖ + ‖I₂‖ := norm_add_le _ _
      _ ≤ C_Hsing / (1 + ‖y‖)^N + C_Htail / (1 + ‖y‖)^N := add_le_add hbound1 hbound2
      _ = (C_Hsing + C_Htail) / (1 + ‖y‖)^N := by ring
  -- H has polynomial decay of order N
  have hH_decay : PolynomialDecayBound H N :=
    ⟨C_Hsing + C_Htail, hC_H, hH_combined⟩
  -- g has polynomial decay of order N
  have hg_decay : PolynomialDecayBound (⇑g) N :=
    ⟨C_g, hC_g_pos, hg_bound⟩
  -- g_flip(x) = g(-x) also has polynomial decay of order N
  let g_flip : E → ℂ := fun x => g (-x)
  have hg_flip_decay : PolynomialDecayBound g_flip N := by
    refine ⟨C_g, hC_g_pos, fun x => ?_⟩
    calc ‖g (-x)‖ ≤ C_g / (1 + ‖-x‖)^N := hg_bound (-x)
      _ = C_g / (1 + ‖x‖)^N := by rw [norm_neg]
  have hg_flip_int : Integrable g_flip volume :=
    hg_int.comp_neg
  -- H is integrable: polynomial decay of order N > d implies integrability
  have hH_int : Integrable H volume := by
    have h_decay_int : Integrable (fun y : E => (1 + ‖y‖)^(-N)) volume :=
      integrable_one_add_norm hN_gt_d
    have h_bound_int : Integrable (fun y : E => (C_Hsing + C_Htail) * (1 + ‖y‖)^(-N)) volume :=
      h_decay_int.const_mul (C_Hsing + C_Htail)
    have hH_meas : AEStronglyMeasurable H volume := by
      -- Use StronglyMeasurable.integral_prod_right' to show H is strongly measurable
      -- The integrand F(y, x) = f(x) * K(x - y) : ℂ is strongly measurable
      have h1 : StronglyMeasurable (Function.uncurry (fun (y : E) (x : E) => f x * (K (x - y) :
        ℂ))) := by
        apply StronglyMeasurable.mul
        · exact (f.continuous.stronglyMeasurable.comp_measurable measurable_snd)
        · apply Measurable.stronglyMeasurable
          exact (hK_meas.comp (measurable_snd.sub measurable_fst)).complex_ofReal
      exact h1.integral_prod_right.aestronglyMeasurable
    have hH_bound_ae : ∀ᵐ y ∂volume, ‖H y‖ ≤ (C_Hsing + C_Htail) * (1 + ‖y‖)^(-N) := by
      apply Eventually.of_forall
      intro y
      have hbound := hH_combined y
      have h_eq : (C_Hsing + C_Htail) / (1 + ‖y‖)^N =
          (C_Hsing + C_Htail) * (1 + ‖y‖)^(-N) := by
        have h1plus_pos : 0 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
        rw [div_eq_mul_inv, Real.rpow_neg h1plus_pos]
      exact le_trans hbound (le_of_eq h_eq)
    exact Integrable.mono' h_bound_int hH_meas hH_bound_ae
  -- ============================================================
  -- Apply convolutionPolynomialDecay to get C_conv
  -- ============================================================
  have h_conv_decay := convolutionPolynomialDecay hN_gt_d hH_decay hg_flip_decay hH_int
    hg_flip_int
  obtain ⟨C_conv, hC_conv_pos, h_conv_bound⟩ := h_conv_decay
  -- ============================================================
  -- NOW introduce the existential with C_conv
  -- ============================================================
  use C_conv
  constructor
  · exact le_of_lt hC_conv_pos
  · intro a
    have h_one_plus_pos : 0 < 1 + ‖a‖ := by positivity
    have h_base_ge_one : 1 ≤ 1 + ‖a‖ := by linarith [norm_nonneg a]
    -- The bound from convolutionPolynomialDecay gives us:
    -- ‖∫ H(y) g_flip(a-y) dy‖ ≤ C_conv / (1 + ‖a‖)^N ≤ C_conv * (1 + ‖a‖)^(-α)
    have h_conv_to_goal : ‖∫ y, H y * g_flip (a - y)‖ ≤ C_conv * (1 + ‖a‖)^(-α) := by
      calc ‖∫ y, H y * g_flip (a - y)‖ ≤ C_conv / (1 + ‖a‖)^N := h_conv_bound a
        _ ≤ C_conv * (1 + ‖a‖)^(-α) := by
          rw [Real.rpow_neg (by linarith [norm_nonneg a] : 0 ≤ 1 + ‖a‖), div_eq_mul_inv]
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_conv_pos)
          rw [inv_le_inv₀ (by positivity) (by positivity)]
          exact Real.rpow_le_rpow_of_exponent_le h_base_ge_one (le_of_lt hN_gt_α)
    -- Step 1: Show product integrability using the textbook lemma
    have h_prod_int := schwartz_bilinear_prod_integrable f g K hK_meas hK_loc R₀ hR₀ hK_tail_bdd a
    -- Step 2: Apply Fubini to swap integration order
    have h_swap : ∫ x : E, ∫ y : E, f x * (K (x - y) : ℂ) * g (y - a) =
        ∫ y : E, ∫ x : E, f x * (K (x - y) : ℂ) * g (y - a) :=
      MeasureTheory.integral_integral_swap h_prod_int
    -- Step 3: Pull g(y-a) out of inner integral and relate to H
    have h_fubini : ∫ x : E, ∫ y : E, f x * (K (x - y) : ℂ) * g (y - a) =
        ∫ y : E, (∫ x : E, f x * (K (x - y) : ℂ)) * g (y - a) := by
      rw [h_swap]
      congr 1
      ext y
      show ∫ x : E, f x * (K (x - y) : ℂ) * g (y - a) =
          (∫ x : E, f x * (K (x - y) : ℂ)) * g (y - a)
      simp_rw [show ∀ x, f x * (K (x - y) : ℂ) * g (y - a) =
          (fun x => f x * (K (x - y) : ℂ)) x * g (y - a) from fun x => by ring]
      exact integral_mul_const (g (y - a)) (fun x => f x * (K (x - y) : ℂ))
    -- Final calc chain: relate double integral to convolution form
    calc ‖∫ x, ∫ y, f x * ↑(K (x - y)) * g (y - a)‖
        = ‖∫ y, (∫ x, f x * ↑(K (x - y))) * g (y - a)‖ := by rw [h_fubini]
      _ = ‖∫ y, H y * g (y - a)‖ := by rfl
      _ = ‖∫ y, H y * g_flip (a - y)‖ := by
          -- g(y-a) = g(-(a-y)) = g_flip(a-y)
          congr 1
          apply integral_congr_ae
          filter_upwards with y
          simp only [g_flip, neg_sub]
      _ ≤ C_conv * (1 + ‖a‖)^(-α) := h_conv_to_goal

end
