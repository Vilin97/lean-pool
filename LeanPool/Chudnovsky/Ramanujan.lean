/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# Ramanujan's derivative identities

This file proves Ramanujan's classical derivative identities for the level-one Eisenstein
series, using Mathlib's normalized derivative `D = (2πi)⁻¹ d/dτ`
(`Derivative.normalizedDerivOfComplex`) and Serre derivative `Derivative.serreDerivative`:

* `Chudnovsky.deriv_E2` : `D E₂ = (E₂² - E₄) / 12`;
* `Chudnovsky.deriv_E₄` : `D E₄ = (E₂·E₄ - E₆) / 3`;
* `Chudnovsky.deriv_E₆` : `D E₆ = (E₂·E₆ - E₄²) / 2`;
* `Chudnovsky.deriv_discriminant` : `D Δ = E₂·Δ` (from `logDeriv_eta_eq_E2`).

The proofs follow the classical finite-dimensionality argument (as in the
sphere-packing-lean project referenced by Mathlib's `ModularForms/Derivative.lean`):

1. For a weight-`k` level-one modular form `f`, the Serre derivative
   `∂ₖ f = D f - (k/12)·E₂·f` is a weight-`(k+2)` level-one modular form.  Slash-invariance
   is checked on the generators `S`, `T` of `SL(2, ℤ)` by differentiating the functional
   equations `f(-1/τ) = τᵏ f(τ)` and `E₂(-1/τ) = τ²E₂(τ) + 6τ/(πi)` (the latter is
   Mathlib's `E2_slash_action`); holomorphy is `serreDerivative_mdifferentiable`; and
   boundedness at `i∞` follows since `D f` *vanishes* at `i∞` (`D f = q·dF/dq` where `F`
   is the cusp function of `f`).
2. The spaces `M₄`, `M₆`, `M₈` of level-one modular forms are one-dimensional, spanned by
   `E₄`, `E₆`, `E₄²` (Mathlib's `LevelOne.DimensionFormula`), so each Serre derivative is a
   scalar multiple of the corresponding basis vector; the scalar is identified by comparing
   limits at `i∞` (`E₂, E₄, E₆ → 1` and `D f → 0`).

Byproducts stated for downstream use (Kummer/PicardFuchs and MainTheorem):

* `Chudnovsky.normalizedDeriv_eq_q_mul_deriv_cuspFunction` : `D f τ = q·F′(q)` with `F` the
  cusp function — the bridge from `τ`-derivatives to `q`-derivatives;
* `Chudnovsky.isZeroAtImInfty_normalizedDeriv`, `Chudnovsky.tendsto_E2_atImInfty`,
  `Chudnovsky.tendsto_E₄_atImInfty`, `Chudnovsky.tendsto_E₆_atImInfty`;
* pointwise raw-derivative forms `deriv_comp_ofComplex_E2`/`_E₄`/`_E₆`.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane hiding I
open Complex Filter Function ModularForm EisensteinSeries Derivative ModularGroup
  SlashInvariantForm

open scoped Real Topology MatrixGroups CongruenceSubgroup ModularForm Manifold

/-! ### Elementary helpers -/

private lemma pi_ne_zero' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero

private lemma pi_I_ne_zero : (π : ℂ) * I ≠ 0 := mul_ne_zero pi_ne_zero' I_ne_zero

private lemma two_pi_I_ne_zero' : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero

/-- Two functions agreeing on the (open) upper half-plane have the same derivative there. -/
lemma deriv_eqOn_upperHalfPlaneSet {F G : ℂ → ℂ} (h : Set.EqOn F G upperHalfPlaneSet)
    {z : ℂ} (hz : 0 < z.im) : deriv F z = deriv G z :=
  (Filter.eventuallyEq_of_mem (isOpen_upperHalfPlaneSet.mem_nhds hz) h).deriv_eq

/-- A `1`-translation-invariant function on `ℍ` extends to a `1`-periodic function on `ℂ`. -/
lemma periodic_comp_ofComplex_of_vadd {f : ℍ → ℂ} (hf : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ) :
    Periodic (f ∘ ofComplex) 1 := by
  intro w
  rcases lt_or_ge 0 w.im with hw | hw
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]
    have h := hf ⟨w, hw⟩
    convert h using 2
    ext
    simp [add_comm]
  · have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    simp only [comp_apply]
    rw [ofComplex_apply_eq_of_im_nonpos hw1 (by simpa using hw)]

/-! ### Transformation behaviour of `E₂` and of level-one modular forms under `T` and `S` -/

lemma E2_slash_T : E2 ∣[(2 : ℤ)] ModularGroup.T = E2 := by
  simp [E2_slash_action, D2_T]

private lemma denom_T (τ : ℍ) : denom ModularGroup.T τ = 1 := by
  simp [ModularGroup.denom_apply, ModularGroup.T]

/-- `E₂` is invariant under `τ ↦ τ + 1`. -/
lemma E2_vadd_one (τ : ℍ) : E2 ((1 : ℝ) +ᵥ τ) = E2 τ := by
  have h := congr_fun E2_slash_T τ
  rw [SL_slash_apply, denom_T, modular_T_smul] at h
  simpa using h

lemma E2_periodic_comp_ofComplex : Periodic (E2 ∘ ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd E2_vadd_one

/-- The `S`-transformation law of `E₂`, in a form using only the combination `π * I`:
`E₂(-1/τ) = τ²E₂(τ) + 6τ/(πi)`. -/
lemma E2_S_smul (τ : ℍ) :
    E2 (ModularGroup.S • τ) = ↑τ ^ 2 * E2 τ + 6 / (π * I) * ↑τ := by
  have h := congr_fun (E2_slash_action ModularGroup.S) τ
  rw [SL_slash_apply, ModularGroup.denom_S, Pi.sub_apply, Pi.smul_apply, D2_S,
    riemannZeta_two, smul_eq_mul] at h
  have hτ : (↑τ : ℂ) ≠ 0 := ne_zero τ
  have hπ : (π : ℂ) ≠ 0 := pi_ne_zero'
  have h2 : ((↑τ : ℂ) ^ (-2 : ℤ)) = ((↑τ : ℂ) ^ (2 : ℕ))⁻¹ := by
    rw [zpow_neg]; norm_cast
  rw [h2, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero 2 hτ)] at h
  have hkey : (6 : ℂ) / (π * I) = -(6 * I / π) := by
    rw [div_mul_eq_div_div, div_I]; ring
  rw [h, hkey]
  field_simp
  ring

/-- Any level-one modular form is invariant under `τ ↦ τ + 1`. -/
lemma modularForm_vadd_one {k : ℤ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) :
    f ((1 : ℝ) +ᵥ τ) = f τ :=
  SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f τ one_mem_strictPeriods_SL

/-- The `S`-transformation law of a level-one modular form: `f(-1/τ) = τᵏ·f(τ)`. -/
lemma modularForm_S_smul {k : ℤ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) :
    f (ModularGroup.S • τ) = ↑τ ^ k * f τ := by
  have h0 : (⇑f) ∣[k] ModularGroup.S = ⇑f :=
    f.slash_action_eq' _ (MonoidHom.mem_range.mpr ⟨ModularGroup.S, rfl⟩)
  have h := congr_fun h0 τ
  rw [SL_slash_apply, ModularGroup.denom_S, zpow_neg, ← div_eq_mul_inv,
    div_eq_iff (zpow_ne_zero k (ne_zero τ))] at h
  rw [h, mul_comm]

/-! ### Asymptotics of `E₂`, `E₄`, `E₆` at `i∞` -/

/-- The divisor-sum `q`-expansion of `E₂`, in `ℕ`-indexed form (cf. `E2_eq_tsum_cexp`). -/
private lemma E2_eq_one_sub_tsum (τ : ℍ) :
    E2 τ = 1 - 24 * ∑' n : ℕ, (ArithmeticFunction.sigma 1 (n + 1) : ℂ) * q τ ^ (n + 1) := by
  have h := EisensteinSeries.E2_eq_tsum_cexp τ
  rw [← q_eq] at h
  rw [tsum_pnat_eq_tsum_succ (f := fun n ↦ (ArithmeticFunction.sigma 1 n : ℂ) * q τ ^ n)] at h
  exact h

private lemma summable_sigma_one_norm_q (τ : ℍ) :
    Summable fun n : ℕ ↦ (ArithmeticFunction.sigma 1 n : ℝ) * ‖q τ‖ ^ n := by
  have hbase : Summable fun n : ℕ ↦ (n : ℝ) ^ 2 * ‖q τ‖ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 2
      (by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact norm_q_lt_one τ)
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hbase
  have hσ : (ArithmeticFunction.sigma 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 n
  exact mul_le_mul_of_nonneg_right hσ (by positivity)

/-- `E₂ → 1` as `Im τ → ∞`. -/
lemma tendsto_E2_atImInfty : Tendsto E2 atImInfty (𝓝 1) := by
  set r : ℝ := Real.exp (-(2 * π)) with hrdef
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff]
    have := Real.pi_pos; linarith
  -- the constant `C = ∑ (n+1)²·rⁿ`
  have hC : Summable fun n : ℕ ↦ ((n : ℝ) + 1) ^ 2 * r ^ n := by
    have h2 : Summable fun n : ℕ ↦ (n : ℝ) ^ 2 * r ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 2
        (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
    have h1 : Summable fun n : ℕ ↦ (n : ℝ) ^ 1 * r ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1
        (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
    have h0 : Summable fun n : ℕ ↦ r ^ n := summable_geometric_of_lt_one hr0.le hr1
    exact ((h2.add (h1.mul_left 2)).add h0).congr fun n ↦ by ring
  set C : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * r ^ n with hCdef
  -- the key pointwise bound on `Im τ ≥ 1`
  have key : ∀ τ : ℍ, 1 ≤ τ.im → ‖E2 τ - 1‖ ≤ 24 * C * ‖q τ‖ := by
    intro τ him
    have hx0 : (0 : ℝ) ≤ ‖q τ‖ := norm_nonneg _
    have hxr : ‖q τ‖ ≤ r := by
      rw [norm_q, hrdef, Real.exp_le_exp]
      have := Real.pi_pos; nlinarith
    have hE : E2 τ - 1 =
        -(24 * ∑' n : ℕ, (ArithmeticFunction.sigma 1 (n + 1) : ℂ) * q τ ^ (n + 1)) := by
      rw [E2_eq_one_sub_tsum τ]; ring
    have hsum1 : Summable fun n : ℕ ↦
        (ArithmeticFunction.sigma 1 (n + 1) : ℝ) * ‖q τ‖ ^ (n + 1) :=
      (summable_nat_add_iff 1).mpr (summable_sigma_one_norm_q τ)
    have hsumnorm : Summable fun n : ℕ ↦
        ‖(ArithmeticFunction.sigma 1 (n + 1) : ℂ) * q τ ^ (n + 1)‖ := by
      refine hsum1.congr fun n ↦ ?_
      rw [norm_mul, norm_pow, Complex.norm_natCast]
    have hsum2 : Summable fun n : ℕ ↦ ((n : ℝ) + 1) ^ 2 * r ^ n * ‖q τ‖ :=
      hC.mul_right _
    have hbound : ∑' n : ℕ, ‖(ArithmeticFunction.sigma 1 (n + 1) : ℂ) * q τ ^ (n + 1)‖
        ≤ C * ‖q τ‖ := by
      rw [hCdef, ← tsum_mul_right]
      refine Summable.tsum_mono hsumnorm hsum2 fun n ↦ ?_
      rw [norm_mul, norm_pow, Complex.norm_natCast, pow_succ]
      have hσ : (ArithmeticFunction.sigma 1 (n + 1) : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
        exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 (n + 1)
      have hpow : ‖q τ‖ ^ n ≤ r ^ n := pow_le_pow_left₀ hx0 hxr n
      calc (ArithmeticFunction.sigma 1 (n + 1) : ℝ) * (‖q τ‖ ^ n * ‖q τ‖)
          ≤ ((n : ℝ) + 1) ^ 2 * (r ^ n * ‖q τ‖) := by
            apply mul_le_mul hσ (by gcongr) (by positivity) (by positivity)
        _ = ((n : ℝ) + 1) ^ 2 * r ^ n * ‖q τ‖ := by ring
    rw [hE, norm_neg, norm_mul]
    calc ‖(24 : ℂ)‖ * ‖∑' n : ℕ, (ArithmeticFunction.sigma 1 (n + 1) : ℂ) * q τ ^ (n + 1)‖
        ≤ 24 * (C * ‖q τ‖) := by
          rw [Complex.norm_ofNat]
          exact mul_le_mul_of_nonneg_left
            ((norm_tsum_le_tsum_norm hsumnorm).trans hbound) (by norm_num)
      _ = 24 * C * ‖q τ‖ := by ring
  -- squeeze
  rw [← tendsto_sub_nhds_zero_iff]
  have hev : ∀ᶠ τ : ℍ in atImInfty, ‖E2 τ - 1‖ ≤ 24 * C * ‖q τ‖ := by
    rw [eventually_iff, atImInfty_mem]
    exact ⟨1, key⟩
  have hg : Tendsto (fun τ : ℍ ↦ 24 * C * ‖q τ‖) atImInfty (𝓝 0) := by
    have hq0 : Tendsto (fun τ : ℍ ↦ ‖q τ‖) atImInfty (𝓝 0) := by
      simpa [q] using (qParam_tendsto_atImInfty one_pos).norm
    simpa using hq0.const_mul (24 * C)
  exact squeeze_zero_norm' hev hg

lemma isBoundedAtImInfty_E2 : IsBoundedAtImInfty E2 :=
  tendsto_E2_atImInfty.isBigO_one ℝ

private instance : Fact (IsCusp OnePoint.infty 𝒮ℒ) :=
  ⟨(𝒮ℒ).isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods_SL⟩

/-- A `1`-periodic, holomorphic, bounded function on `ℍ` tends to its value at `i∞`. -/
lemma tendsto_valueAtInfty_atImInfty {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) :
    Tendsto f atImInfty (𝓝 (valueAtInfty f)) := by
  have h_hol : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ (f ∘ ofComplex) z :=
    eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
      fun z hz ↦ mdifferentiableAt_iff.mp (hhol ⟨z, hz⟩)
  have h_bd : BoundedAtFilter (comap Complex.im atTop) (f ∘ ofComplex) :=
    hbdd.comp_tendsto tendsto_comap_im_ofComplex
  have h1 := (Periodic.tendsto_at_I_inf one_pos hper h_hol h_bd).comp tendsto_coe_atImInfty
  have h2 : Tendsto f atImInfty (𝓝 (cuspFunction 1 f 0)) := by
    refine h1.congr fun τ ↦ ?_
    simp [Function.comp_def, ofComplex_apply]
  rwa [cuspFunction_apply_zero one_pos
    (analyticAt_cuspFunction_zero one_pos hper hhol hbdd) hper] at h2

/-- `E₄ → 1` as `Im τ → ∞`. -/
lemma tendsto_E₄_atImInfty : Tendsto (⇑E₄) atImInfty (𝓝 1) := by
  have hper : Periodic ((⇑E₄) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL
  have hhol : MDiff (⇑E₄) := ModularFormClass.holo E₄
  have hbdd : IsBoundedAtImInfty (⇑E₄) := ModularFormClass.bdd_at_infty E₄
  have h := tendsto_valueAtInfty_atImInfty hper hhol hbdd
  have hval : valueAtInfty (⇑E₄) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (analyticAt_cuspFunction_zero one_pos hper hhol hbdd) hper]
    exact E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  rwa [hval] at h

/-- `E₆ → 1` as `Im τ → ∞`. -/
lemma tendsto_E₆_atImInfty : Tendsto (⇑E₆) atImInfty (𝓝 1) := by
  have hper : Periodic ((⇑E₆) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex E₆ one_mem_strictPeriods_SL
  have hhol : MDiff (⇑E₆) := ModularFormClass.holo E₆
  have hbdd : IsBoundedAtImInfty (⇑E₆) := ModularFormClass.bdd_at_infty E₆
  have h := tendsto_valueAtInfty_atImInfty hper hhol hbdd
  have hval : valueAtInfty (⇑E₆) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (analyticAt_cuspFunction_zero one_pos hper hhol hbdd) hper]
    exact E_qExpansion_coeff_zero _ ⟨3, rfl⟩
  rwa [hval] at h

/-! ### The normalized derivative `D` via the cusp function

For a `1`-periodic, holomorphic, bounded function `f` on `ℍ` with cusp function `F`
(so `f(τ) = F(q)`), we have `D f τ = q·F′(q)`.  In particular `D f` vanishes at `i∞`.
-/

section NormalizedDeriv

variable {f : ℍ → ℂ}

/-- `D f τ = q · F′(q)` where `F = cuspFunction 1 f`.  This is the bridge between
`τ`-derivatives and `q`-derivatives, used throughout the `q`-expansion arguments. -/
lemma normalizedDeriv_eq_q_mul_deriv_cuspFunction (hper : Periodic (f ∘ ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) (τ : ℍ) :
    D f τ = q τ * deriv (cuspFunction 1 f) (q τ) := by
  have hcomp : f ∘ ofComplex = cuspFunction 1 f ∘ (fun w : ℂ ↦ Periodic.qParam 1 w) := by
    funext w
    exact (Periodic.eq_cuspFunction one_ne_zero hper w).symm
  have hq' : HasStrictDerivAt (Periodic.qParam 1) (Periodic.qParam 1 ↑τ * (2 * π * I / 1)) ↑τ := by
    simpa only [id_eq, mul_one] using!
      (((hasStrictDerivAt_id (↑τ : ℂ)).const_mul (2 * π * I)).div_const ((1 : ℝ) : ℂ)).cexp
  have hq : HasDerivAt (fun w : ℂ ↦ Periodic.qParam 1 w) (2 * π * I * q τ) ↑τ := by
    have h2 := hq'.hasDerivAt
    have hq_eq : Periodic.qParam 1 (↑τ : ℂ) = q τ := rfl
    rw [hq_eq] at h2
    simpa [mul_comm] using h2
  have hFq : DifferentiableAt ℂ (cuspFunction 1 f) (q τ) :=
    differentiableAt_cuspFunction one_pos hper hhol hbdd (norm_q_lt_one τ)
  have hd : deriv (f ∘ ofComplex) ↑τ = deriv (cuspFunction 1 f) (q τ) * (2 * π * I * q τ) := by
    rw [hcomp]
    exact (hFq.hasDerivAt.comp (↑τ : ℂ) hq).deriv
  change (2 * π * I)⁻¹ * deriv (f ∘ ofComplex) ↑τ = q τ * deriv (cuspFunction 1 f) (q τ)
  rw [hd]
  field_simp

/-- The normalized derivative of a `1`-periodic bounded holomorphic function vanishes
at `i∞`. -/
lemma isZeroAtImInfty_normalizedDeriv (hper : Periodic (f ∘ ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) :
    IsZeroAtImInfty (D f) := by
  have hana : AnalyticAt ℂ (cuspFunction 1 f) 0 :=
    analyticAt_cuspFunction_zero one_pos hper hhol hbdd
  have hc : ContinuousAt (deriv (cuspFunction 1 f)) 0 := hana.deriv.continuousAt
  have hq0 : Tendsto (fun τ : ℍ ↦ q τ) atImInfty (𝓝 0) := by
    simpa [q] using qParam_tendsto_atImInfty one_pos
  have h : Tendsto (fun τ : ℍ ↦ q τ * deriv (cuspFunction 1 f) (q τ)) atImInfty
      (𝓝 (0 * deriv (cuspFunction 1 f) 0)) :=
    hq0.mul ((hc.tendsto).comp hq0)
  rw [zero_mul] at h
  exact h.congr fun τ ↦ (normalizedDeriv_eq_q_mul_deriv_cuspFunction hper hhol hbdd τ).symm

/-- `D f` is invariant under `τ ↦ τ + 1` when `f` is `1`-periodic. -/
lemma normalizedDeriv_vadd_one (hper : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    D f ((1 : ℝ) +ᵥ τ) = D f τ := by
  have hcoe : ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) = ↑τ + 1 := by
    rw [coe_vadd]
    push_cast
    ring
  have hfun : (fun w : ℂ ↦ (f ∘ ofComplex) (w + 1)) = f ∘ ofComplex := by
    funext w
    simpa using hper w
  change (2 * π * I)⁻¹ * deriv (f ∘ ofComplex) ↑((1 : ℝ) +ᵥ τ) = _
  rw [hcoe, ← deriv_comp_add_const (f ∘ ofComplex) 1, hfun]
  rfl

/-! #### Behaviour of `D` under `S` -/

/-- Differentiating a functional equation along `S`: if `f` extends `Φ` along `w ↦ -w⁻¹`
on the upper half-plane, then `(f ∘ ofComplex)′(-1/τ) = τ² Φ′(τ)`. -/
lemma deriv_comp_ofComplex_S (hhol : MDiff f) {Φ : ℂ → ℂ}
    (heq : Set.EqOn ((f ∘ ofComplex) ∘ fun w ↦ -w⁻¹) Φ upperHalfPlaneSet) (τ : ℍ) :
    deriv (f ∘ ofComplex) (-(↑τ : ℂ)⁻¹) = (↑τ : ℂ) ^ 2 * deriv Φ ↑τ := by
  have hmem : 0 < (-(↑τ : ℂ)⁻¹).im := by
    have := τ.im_inv_neg_coe_pos
    rwa [inv_neg] at this
  have hdF : DifferentiableAt ℂ (f ∘ ofComplex) (-(↑τ : ℂ)⁻¹) := by
    have h1 : DifferentiableOn ℂ (f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
      mdifferentiable_iff.mp hhol
    exact (h1 _ hmem).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hmem)
  have h1 : HasDerivAt (fun w : ℂ ↦ -w⁻¹) (((↑τ : ℂ) ^ 2)⁻¹) ↑τ := by
    have h := (hasDerivAt_inv (ne_zero τ)).neg
    simp only [neg_neg] at h
    exact h
  have h2 : deriv ((f ∘ ofComplex) ∘ fun w : ℂ ↦ -w⁻¹) ↑τ =
      deriv (f ∘ ofComplex) (-(↑τ : ℂ)⁻¹) * (((↑τ : ℂ) ^ 2)⁻¹) :=
    (hdF.hasDerivAt.comp (↑τ : ℂ) h1).deriv
  have h3 : deriv ((f ∘ ofComplex) ∘ fun w : ℂ ↦ -w⁻¹) ↑τ = deriv Φ ↑τ :=
    deriv_eqOn_upperHalfPlaneSet heq τ.im_pos
  have hτ2 : ((↑τ : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (ne_zero τ)
  rw [← h3, h2, mul_comm (deriv (f ∘ ofComplex) (-(↑τ : ℂ)⁻¹)) _, ← mul_assoc,
    mul_inv_cancel₀ hτ2, one_mul]

private lemma coe_S_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -(↑τ : ℂ)⁻¹ := by
  rw [modular_S_smul]
  simp [inv_neg]

/-- How `D f` transforms under `S` for a function of weight `m + 1`:
if `f(-1/τ) = τ^(m+1)·f(τ)` then
`(D f)(-1/τ) = τ^(m+3)·D f(τ) + (m+1)·τ^(m+2)·f(τ)/(2πi)`. -/
lemma normalizedDeriv_S_smul_of_weight (hhol : MDiff f) {m : ℕ}
    (hfS : ∀ σ : ℍ, f (ModularGroup.S • σ) = ↑σ ^ (m + 1) * f σ) (τ : ℍ) :
    D f (ModularGroup.S • τ) =
      ↑τ ^ (m + 3) * D f τ + (m + 1) * ↑τ ^ (m + 2) * (2 * π * I)⁻¹ * f τ := by
  have hdF : DifferentiableAt ℂ (f ∘ ofComplex) ↑τ := mdifferentiableAt_iff.mp (hhol τ)
  -- the extension of the functional equation to `ℂ`
  have heq : Set.EqOn ((f ∘ ofComplex) ∘ fun w ↦ -w⁻¹)
      (fun w ↦ w ^ (m + 1) * (f ∘ ofComplex) w) upperHalfPlaneSet := by
    intro w hw
    have hmem : 0 < (-w⁻¹).im := by
      have := (⟨w, hw⟩ : ℍ).im_inv_neg_coe_pos
      rwa [inv_neg] at this
    have hofS : ofComplex (-w⁻¹) = ModularGroup.S • (⟨w, hw⟩ : ℍ) := by
      rw [ofComplex_apply_of_im_pos hmem]
      exact UpperHalfPlane.ext (by rw [coe_S_smul])
    simp only [comp_apply, hofS, hfS ⟨w, hw⟩, ofComplex_apply_of_im_pos hw]
  have hd := deriv_comp_ofComplex_S hhol heq τ
  -- compute the derivative of the right-hand side
  have hp : HasDerivAt (fun w : ℂ ↦ w ^ (m + 1)) ((((m + 1) : ℕ) : ℂ) * (↑τ : ℂ) ^ m) ↑τ := by
    simpa using hasDerivAt_pow (m + 1) (↑τ : ℂ)
  have hΦ : HasDerivAt (fun w : ℂ ↦ w ^ (m + 1) * (f ∘ ofComplex) w)
      ((((m + 1) : ℕ) : ℂ) * (↑τ : ℂ) ^ m * (f ∘ ofComplex) ↑τ +
        (↑τ : ℂ) ^ (m + 1) * deriv (f ∘ ofComplex) ↑τ) ↑τ :=
    hp.mul hdF.hasDerivAt
  rw [hΦ.deriv] at hd
  -- now unfold `D` and conclude by algebra
  have hcoe := coe_S_smul τ
  have hDτ : deriv (f ∘ ofComplex) ↑τ = 2 * π * I * D f τ := by
    change _ = 2 * π * I * ((2 * π * I)⁻¹ * deriv (f ∘ ofComplex) ↑τ)
    field_simp
  change (2 * π * I)⁻¹ * deriv (f ∘ ofComplex) ↑(ModularGroup.S • τ) = _
  rw [hcoe, hd, hDτ, comp_ofComplex]
  have h2πI : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero'
  push_cast
  field_simp
  ring

/-- How `D E₂` transforms under `S`:
`(D E₂)(-1/τ) = τ⁴·D E₂(τ) + τ³·E₂(τ)/(πi) + 3τ²/(πi)²`. -/
lemma normalizedDeriv_E2_S_smul (τ : ℍ) :
    D E2 (ModularGroup.S • τ) =
      ↑τ ^ 4 * D E2 τ + (π * I)⁻¹ * ↑τ ^ 3 * E2 τ + 3 * ((π * I) ^ 2)⁻¹ * ↑τ ^ 2 := by
  have hdF : DifferentiableAt ℂ (E2 ∘ ofComplex) ↑τ :=
    mdifferentiableAt_iff.mp (E2_mdifferentiable τ)
  have heq : Set.EqOn ((E2 ∘ ofComplex) ∘ fun w ↦ -w⁻¹)
      (fun w ↦ w ^ 2 * (E2 ∘ ofComplex) w + 6 / (π * I) * w) upperHalfPlaneSet := by
    intro w hw
    have hmem : 0 < (-w⁻¹).im := by
      have := (⟨w, hw⟩ : ℍ).im_inv_neg_coe_pos
      rwa [inv_neg] at this
    have hofS : ofComplex (-w⁻¹) = ModularGroup.S • (⟨w, hw⟩ : ℍ) := by
      rw [ofComplex_apply_of_im_pos hmem]
      exact UpperHalfPlane.ext (by rw [coe_S_smul])
    simp only [comp_apply, hofS, E2_S_smul ⟨w, hw⟩, ofComplex_apply_of_im_pos hw]
  have hd := deriv_comp_ofComplex_S E2_mdifferentiable heq τ
  have hp : HasDerivAt (fun w : ℂ ↦ w ^ 2) (2 * (↑τ : ℂ)) ↑τ := by
    simpa using hasDerivAt_pow 2 (↑τ : ℂ)
  have hlin : HasDerivAt (fun w : ℂ ↦ 6 / (π * I) * w) (6 / (π * I) * 1) ↑τ :=
    (hasDerivAt_id (↑τ : ℂ)).const_mul (6 / (π * I) : ℂ)
  have hΦ : HasDerivAt (fun w : ℂ ↦ w ^ 2 * (E2 ∘ ofComplex) w + 6 / (π * I) * w)
      (2 * (↑τ : ℂ) * (E2 ∘ ofComplex) ↑τ + (↑τ : ℂ) ^ 2 * deriv (E2 ∘ ofComplex) ↑τ +
        6 / (π * I) * 1) ↑τ :=
    (hp.mul hdF.hasDerivAt).add hlin
  rw [hΦ.deriv] at hd
  have hcoe := coe_S_smul τ
  have hDτ : deriv (E2 ∘ ofComplex) ↑τ = 2 * π * I * D E2 τ := by
    change _ = 2 * π * I * ((2 * π * I)⁻¹ * deriv (E2 ∘ ofComplex) ↑τ)
    field_simp
  change (2 * π * I)⁻¹ * deriv (E2 ∘ ofComplex) ↑(ModularGroup.S • τ) = _
  rw [hcoe, hd, hDτ, comp_ofComplex]
  have hπI : (π : ℂ) * I ≠ 0 := pi_I_ne_zero
  field_simp
  ring

end NormalizedDeriv

/-! ### The Serre derivatives of `E₂`, `E₄`, `E₆` as bundled modular forms -/

section SerreForms

/-- Slash-invariance of a Serre derivative under `T`, given translation-invariance of `f`. -/
private lemma serreDerivative_slash_T {kc : ℂ} {f : ℍ → ℂ} {w : ℤ}
    (hf : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ) :
    serreDerivative kc f ∣[w] ModularGroup.T = serreDerivative kc f := by
  ext τ
  rw [SL_slash_apply, denom_T, modular_T_smul]
  simp only [serreDerivative_apply]
  rw [normalizedDeriv_vadd_one (periodic_comp_ofComplex_of_vadd hf) τ, E2_vadd_one, hf]
  simp

/-- Boundedness at `i∞` of a Serre derivative. -/
private lemma isBoundedAtImInfty_serre {kc : ℂ} {f : ℍ → ℂ}
    (hf : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ) (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (serreDerivative kc f) := by
  have hD : IsBoundedAtImInfty (D f) :=
    (isZeroAtImInfty_normalizedDeriv (periodic_comp_ofComplex_of_vadd hf) hhol
      hbdd).isBoundedAtImInfty
  have hprod := (isBoundedAtImInfty_E2.mul hbdd).const_mul_left (kc * 12⁻¹)
  have h := hD.sub hprod
  have heq2 : serreDerivative kc f = fun x : ℍ ↦ D f x - kc * 12⁻¹ * (E2 * f) x := by
    rw [serreDerivative_eq]
    funext z
    simp only [Pi.mul_apply]
    ring
  rw [heq2]
  exact h

/-- The limit of a Serre derivative at `i∞`: if `f → a` then `∂ₖ f → -(k/12)·a`. -/
private lemma tendsto_serre_atImInfty {kc : ℂ} {f : ℍ → ℂ} {a : ℂ}
    (hf : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ) (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f)
    (hlim : Tendsto f atImInfty (𝓝 a)) :
    Tendsto (serreDerivative kc f) atImInfty (𝓝 (-(kc * 12⁻¹ * a))) := by
  have hD : Tendsto (D f) atImInfty (𝓝 0) :=
    isZeroAtImInfty_normalizedDeriv (periodic_comp_ofComplex_of_vadd hf) hhol hbdd
  have h2 : Tendsto (fun τ : ℍ ↦ kc * 12⁻¹ * E2 τ * f τ) atImInfty
      (𝓝 (kc * 12⁻¹ * 1 * a)) :=
    ((tendsto_const_nhds.mul tendsto_E2_atImInfty).mul hlim)
  have h := hD.sub h2
  rw [serreDerivative_eq]
  simpa using h

/-- Slash-invariance under `S` of `∂₄E₄` (weight 6). -/
private lemma serre_E₄_slash_S :
    serreDerivative 4 (⇑E₄) ∣[(6 : ℤ)] ModularGroup.S = serreDerivative 4 (⇑E₄) := by
  ext τ
  have hτ : (↑τ : ℂ) ≠ 0 := ne_zero τ
  have hπ : (π : ℂ) ≠ 0 := pi_ne_zero'
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hE₄S : ∀ σ : ℍ, (⇑E₄ : ℍ → ℂ) (ModularGroup.S • σ) = ↑σ ^ (3 + 1 : ℕ) * E₄ σ := by
    intro σ
    have h := modularForm_S_smul E₄ σ
    exact_mod_cast h
  rw [SL_slash_apply, ModularGroup.denom_S]
  simp only [serreDerivative_apply]
  rw [normalizedDeriv_S_smul_of_weight (ModularFormClass.holo E₄) hE₄S τ, E2_S_smul τ, hE₄S τ]
  have hz : ((↑τ : ℂ) ^ (-(6 : ℤ))) = ((↑τ : ℂ) ^ (6 : ℕ))⁻¹ := by
    rw [zpow_neg]; norm_cast
  rw [hz]
  push_cast
  field_simp
  ring

/-- Slash-invariance under `S` of `∂₆E₆` (weight 8). -/
private lemma serre_E₆_slash_S :
    serreDerivative 6 (⇑E₆) ∣[(8 : ℤ)] ModularGroup.S = serreDerivative 6 (⇑E₆) := by
  ext τ
  have hτ : (↑τ : ℂ) ≠ 0 := ne_zero τ
  have hπ : (π : ℂ) ≠ 0 := pi_ne_zero'
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hE₆S : ∀ σ : ℍ, (⇑E₆ : ℍ → ℂ) (ModularGroup.S • σ) = ↑σ ^ (5 + 1 : ℕ) * E₆ σ := by
    intro σ
    have h := modularForm_S_smul E₆ σ
    exact_mod_cast h
  rw [SL_slash_apply, ModularGroup.denom_S]
  simp only [serreDerivative_apply]
  rw [normalizedDeriv_S_smul_of_weight (ModularFormClass.holo E₆) hE₆S τ, E2_S_smul τ, hE₆S τ]
  have hz : ((↑τ : ℂ) ^ (-(8 : ℤ))) = ((↑τ : ℂ) ^ (8 : ℕ))⁻¹ := by
    rw [zpow_neg]; norm_cast
  rw [hz]
  push_cast
  field_simp
  ring

/-- Slash-invariance under `S` of `∂₁E₂ = D E₂ - E₂²/12` (weight 4): the quasimodularity
of `E₂` exactly cancels in the Serre derivative. -/
private lemma serre_E2_slash_S :
    serreDerivative 1 E2 ∣[(4 : ℤ)] ModularGroup.S = serreDerivative 1 E2 := by
  ext τ
  have hτ : (↑τ : ℂ) ≠ 0 := ne_zero τ
  have hπ : (π : ℂ) ≠ 0 := pi_ne_zero'
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  rw [SL_slash_apply, ModularGroup.denom_S]
  simp only [serreDerivative_apply]
  rw [normalizedDeriv_E2_S_smul τ, E2_S_smul τ]
  have hz : ((↑τ : ℂ) ^ (-(4 : ℤ))) = ((↑τ : ℂ) ^ (4 : ℕ))⁻¹ := by
    rw [zpow_neg]; norm_cast
  rw [hz]
  field_simp
  ring

/-- `∂₄E₄ = D E₄ - (1/3)·E₂·E₄`, as a modular form of weight 6 and level one. -/
private def serreE₄ : ModularForm 𝒮ℒ 6 where
  toFun := serreDerivative 4 (⇑E₄)
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact slash_action_generators_SL2Z serre_E₄_slash_S
      (serreDerivative_slash_T (modularForm_vadd_one E₄)) γ
  holo' := serreDerivative_mdifferentiable 4 (ModularFormClass.holo E₄)
  bdd_at_cusps' hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z serre_E₄_slash_S
      (serreDerivative_slash_T (modularForm_vadd_one E₄)) γ]
    exact isBoundedAtImInfty_serre (modularForm_vadd_one E₄) (ModularFormClass.holo E₄)
      (ModularFormClass.bdd_at_infty E₄)

/-- `∂₆E₆ = D E₆ - (1/2)·E₂·E₆`, as a modular form of weight 8 and level one. -/
private def serreE₆ : ModularForm 𝒮ℒ 8 where
  toFun := serreDerivative 6 (⇑E₆)
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact slash_action_generators_SL2Z serre_E₆_slash_S
      (serreDerivative_slash_T (modularForm_vadd_one E₆)) γ
  holo' := serreDerivative_mdifferentiable 6 (ModularFormClass.holo E₆)
  bdd_at_cusps' hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z serre_E₆_slash_S
      (serreDerivative_slash_T (modularForm_vadd_one E₆)) γ]
    exact isBoundedAtImInfty_serre (modularForm_vadd_one E₆) (ModularFormClass.holo E₆)
      (ModularFormClass.bdd_at_infty E₆)

/-- `∂₁E₂ = D E₂ - (1/12)·E₂²`, as a modular form of weight 4 and level one. -/
private def serreE2 : ModularForm 𝒮ℒ 4 where
  toFun := serreDerivative 1 E2
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact slash_action_generators_SL2Z serre_E2_slash_S
      (serreDerivative_slash_T E2_vadd_one) γ
  holo' := serreDerivative_mdifferentiable 1 E2_mdifferentiable
  bdd_at_cusps' hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z serre_E2_slash_S
      (serreDerivative_slash_T E2_vadd_one) γ]
    exact isBoundedAtImInfty_serre E2_vadd_one E2_mdifferentiable isBoundedAtImInfty_E2

end SerreForms

/-! ### The one-dimensionality arguments -/

section RankOne

/-- `E₄²` as a modular form of weight 8 (recast from weight `4 + 4`). -/
private def E₄sq : ModularForm 𝒮ℒ 8 := ModularForm.mcast (by norm_num) (E₄.mul E₄)

private lemma E₄sq_coe : (⇑E₄sq : ℍ → ℂ) = fun τ ↦ E₄ τ * E₄ τ := rfl

private lemma E₄sq_ne_zero : E₄sq ≠ 0 := by
  intro h
  have h4 : (qExpansion 1 (⇑E₄)).coeff 0 = 1 := E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  have hana : AnalyticAt ℂ (cuspFunction 1 (⇑E₄)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL
  have h0 : (qExpansion 1 (⇑E₄sq)).coeff 0 = 1 := by
    have hcoe : (⇑E₄sq : ℍ → ℂ) = (⇑E₄) * (⇑E₄) := by
      rw [E₄sq_coe]; rfl
    rw [hcoe, qExpansion_mul_coeff_zero hana.continuousAt hana.continuousAt, h4, mul_one]
  rw [(ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_SL E₄sq).mpr h] at h0
  simp at h0

private lemma tendsto_E₄sq_atImInfty : Tendsto (⇑E₄sq) atImInfty (𝓝 1) := by
  rw [E₄sq_coe]
  simpa using tendsto_E₄_atImInfty.mul tendsto_E₄_atImInfty

private lemma rank_eight : Module.rank ℂ (ModularForm 𝒮ℒ (8 : ℤ)) = 1 := by
  have h := ModularForm.dimension_level_one 8 (by decide)
  rw [if_neg (by decide)] at h
  simpa using h

/-- Extract the scalar from a rank-one comparison by taking limits at `i∞`. -/
private lemma smul_const_of_tendsto {k : ℤ} {e : ModularForm 𝒮ℒ k} {g : ℍ → ℂ} {c a b : ℂ}
    (h : (⇑(c • e) : ℍ → ℂ) = g) (he : Tendsto (⇑e) atImInfty (𝓝 a))
    (hg : Tendsto g atImInfty (𝓝 b)) : c * a = b := by
  have h1 : Tendsto (⇑(c • e)) atImInfty (𝓝 (c * a)) := by
    have hcoe : (⇑(c • e) : ℍ → ℂ) = fun τ ↦ c * e τ := by
      ext τ; simp
    rw [hcoe]
    exact tendsto_const_nhds.mul he
  rw [h] at h1
  exact tendsto_nhds_unique h1 hg

/-- The Serre-derivative form of Ramanujan's identity for `E₄`:
`D E₄ - (1/3)·E₂·E₄ = -(1/3)·E₆`. -/
theorem serreDerivative_E₄_eq : serreDerivative 4 (⇑E₄) = fun τ : ℍ ↦ -(3⁻¹) * E₆ τ := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' E₆ (E_ne_zero _ ⟨3, rfl⟩)).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_six_rank_one) serreE₄
  have hfun : (⇑(c • E₆) : ℍ → ℂ) = serreDerivative 4 (⇑E₄) :=
    congrArg (fun F : ModularForm 𝒮ℒ 6 ↦ (F : ℍ → ℂ)) hc
  have hval : c * 1 = -(4 * 12⁻¹ * 1) :=
    smul_const_of_tendsto hfun tendsto_E₆_atImInfty
      (tendsto_serre_atImInfty (modularForm_vadd_one E₄) (ModularFormClass.holo E₄)
        (ModularFormClass.bdd_at_infty E₄) tendsto_E₄_atImInfty)
  have hcval : c = -(3⁻¹) := by
    rw [mul_one] at hval
    rw [hval]; norm_num
  funext τ
  rw [← hfun, hcval]
  simp

/-- The Serre-derivative form of Ramanujan's identity for `E₆`:
`D E₆ - (1/2)·E₂·E₆ = -(1/2)·E₄²`. -/
theorem serreDerivative_E₆_eq :
    serreDerivative 6 (⇑E₆) = fun τ : ℍ ↦ -(2⁻¹) * (E₄ τ * E₄ τ) := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' E₄sq E₄sq_ne_zero).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp rank_eight) serreE₆
  have hfun : (⇑(c • E₄sq) : ℍ → ℂ) = serreDerivative 6 (⇑E₆) :=
    congrArg (fun F : ModularForm 𝒮ℒ 8 ↦ (F : ℍ → ℂ)) hc
  have hval : c * 1 = -(6 * 12⁻¹ * 1) :=
    smul_const_of_tendsto hfun tendsto_E₄sq_atImInfty
      (tendsto_serre_atImInfty (modularForm_vadd_one E₆) (ModularFormClass.holo E₆)
        (ModularFormClass.bdd_at_infty E₆) tendsto_E₆_atImInfty)
  have hcval : c = -(2⁻¹) := by
    rw [mul_one] at hval
    rw [hval]; norm_num
  funext τ
  have h := congr_fun hfun τ
  rw [← h, hcval]
  simp [E₄sq_coe]

/-- The Serre-derivative form of Ramanujan's identity for `E₂`:
`D E₂ - (1/12)·E₂² = -(1/12)·E₄`. -/
theorem serreDerivative_E2_eq : serreDerivative 1 E2 = fun τ : ℍ ↦ -(12⁻¹) * E₄ τ := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' E₄ (E_ne_zero _ ⟨2, rfl⟩)).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_four_rank_one) serreE2
  have hfun : (⇑(c • E₄) : ℍ → ℂ) = serreDerivative 1 E2 :=
    congrArg (fun F : ModularForm 𝒮ℒ 4 ↦ (F : ℍ → ℂ)) hc
  have hval : c * 1 = -(1 * 12⁻¹ * 1) :=
    smul_const_of_tendsto hfun tendsto_E₄_atImInfty
      (tendsto_serre_atImInfty E2_vadd_one E2_mdifferentiable isBoundedAtImInfty_E2
        tendsto_E2_atImInfty)
  have hcval : c = -(12⁻¹) := by
    rw [mul_one] at hval
    rw [hval]; norm_num
  funext τ
  rw [← hfun, hcval]
  simp

end RankOne

/-! ### Ramanujan's identities -/

/-- **Ramanujan's identity for `E₂`**: `D E₂ = (E₂² - E₄)/12`. -/
theorem deriv_E2 (τ : ℍ) : D E2 τ = (E2 τ ^ 2 - E₄ τ) / 12 := by
  have h := congr_fun serreDerivative_E2_eq τ
  rw [serreDerivative_apply] at h
  linear_combination h

/-- **Ramanujan's identity for `E₄`**: `D E₄ = (E₂·E₄ - E₆)/3`. -/
theorem deriv_E₄ (τ : ℍ) : D (⇑E₄) τ = (E2 τ * E₄ τ - E₆ τ) / 3 := by
  have h := congr_fun serreDerivative_E₄_eq τ
  rw [serreDerivative_apply] at h
  linear_combination h

/-- **Ramanujan's identity for `E₆`**: `D E₆ = (E₂·E₆ - E₄²)/2`. -/
theorem deriv_E₆ (τ : ℍ) : D (⇑E₆) τ = (E2 τ * E₆ τ - E₄ τ ^ 2) / 2 := by
  have h := congr_fun serreDerivative_E₆_eq τ
  rw [serreDerivative_apply] at h
  linear_combination h

/-! ### Raw-derivative corollaries

The identities in terms of `deriv (f ∘ ofComplex)`, i.e. `d/dτ = 2πi·D`, for direct use in
chain-rule computations. -/

private lemma deriv_eq_two_pi_I_mul_D (f : ℍ → ℂ) (τ : ℍ) :
    deriv (f ∘ ofComplex) ↑τ = 2 * π * I * D f τ := by
  change _ = 2 * π * I * ((2 * π * I)⁻¹ * deriv (f ∘ ofComplex) ↑τ)
  field_simp

theorem deriv_comp_ofComplex_E2 (τ : ℍ) :
    deriv (E2 ∘ ofComplex) ↑τ = π * I / 6 * (E2 τ ^ 2 - E₄ τ) := by
  rw [deriv_eq_two_pi_I_mul_D E2 τ, deriv_E2]
  ring

theorem deriv_comp_ofComplex_E₄ (τ : ℍ) :
    deriv ((⇑E₄) ∘ ofComplex) ↑τ = 2 * π * I / 3 * (E2 τ * E₄ τ - E₆ τ) := by
  rw [deriv_eq_two_pi_I_mul_D (⇑E₄) τ, deriv_E₄]
  ring

theorem deriv_comp_ofComplex_E₆ (τ : ℍ) :
    deriv ((⇑E₆) ∘ ofComplex) ↑τ = π * I * (E2 τ * E₆ τ - E₄ τ ^ 2) := by
  rw [deriv_eq_two_pi_I_mul_D (⇑E₆) τ, deriv_E₆]
  ring

/-! ### The discriminant: `D Δ = E₂·Δ` -/

/-- `D Δ = E₂·Δ`, from Mathlib's `logDeriv_eta_eq_E2` and `Δ = η²⁴`. -/
theorem deriv_discriminant (τ : ℍ) :
    D (ModularForm.discriminant) τ = E2 τ * ModularForm.discriminant τ := by
  have hmem : (↑τ : ℂ) ∈ upperHalfPlaneSet := τ.im_pos
  have hη : DifferentiableAt ℂ ModularForm.eta ↑τ :=
    ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hmem
  have hη0 : ModularForm.eta ↑τ ≠ 0 := ModularForm.eta_ne_zero hmem
  have heq : Set.EqOn (ModularForm.discriminant ∘ ofComplex)
      ((ModularForm.eta : ℂ → ℂ) ^ 24) upperHalfPlaneSet := by
    intro w hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hw]
    rfl
  have hd : deriv (ModularForm.discriminant ∘ ofComplex) (↑τ : ℂ) =
      deriv ((ModularForm.eta : ℂ → ℂ) ^ 24) (↑τ : ℂ) :=
    deriv_eqOn_upperHalfPlaneSet heq τ.im_pos
  have hpow := (hη.hasDerivAt.pow 24).deriv
  have hlog := logDeriv_eta_eq_E2 τ
  rw [logDeriv_apply, div_eq_iff hη0] at hlog
  have hΔ : ModularForm.discriminant τ = ModularForm.eta ↑τ ^ 24 := rfl
  change (2 * π * I)⁻¹ * deriv (ModularForm.discriminant ∘ ofComplex) ↑τ = _
  rw [hd, hpow, hlog, hΔ]
  have h2πI : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero'
  push_cast
  field_simp
  ring

end Chudnovsky
