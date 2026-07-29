/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.ExplicitFormula.ZeroCapture

/-!
# The prime side of the explicit formula  (SP2-vM)

Poitou's ultrametric side (p. 6-02) needs the Dirichlet series of the logarithmic
derivative: `−ζ_K'/ζ_K(s) = ∑_{𝔭,m} log(N𝔭)·N𝔭^{-ms}` on `Re s > 1`. This file
differentiates Chebotarev's prime-ideal Euler product through locally uniform
convergence (`logDeriv_tprod_eq_tsum`) to obtain the closed form
`−ζ_K'/ζ_K(s) = ∑_𝔭 log(N𝔭)·N𝔭^{-s}/(1 − N𝔭^{-s})`; the geometric `m`-expansion
is deferred to the Fubini step of Proposition 2.

## Main declarations
* `summable_primeIdeal_rpow`, `summable_primeIdeal_log_rpow` — prime-ideal Dirichlet
  convergence (with logarithmic weights, via exponent absorption);
* `logDeriv_euler_factor` — the single-factor computation;
* `euler_g_bound`, `euler_factor_ne_zero`, `euler_inv_norm_le_two` — uniform factor
  estimates on `Re ≥ σ₀ > 1`;
* `multipliableLocallyUniformlyOn_eulerFactors` — the Euler product converges locally
  uniformly on the half-plane;
* `neg_logDeriv_dedekindZeta_eq_tsum` — the prime-side series.

Route: `.mathlib-quality/decomposition-sp2.md`, leaf SP2-vM.
-/

@[expose] public section

namespace DedekindResidue

open MeasureTheory Complex NumberField
open scoped ENNReal NNReal

variable (K : Type*) [Field K] [NumberField K]

/-- The absolute norm of a nonzero prime ideal is nonzero (`absNorm I = 0 ↔ I = ⊥`, and the
ideal is nonzero). -/
theorem absNorm_ne_zero_of_prime {𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}} :
    Ideal.absNorm 𝔭.1 ≠ 0 :=
  fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)

/-- The absolute norm of a nonzero prime ideal is not `1` (`absNorm I = 1 ↔ I = ⊤`, and a
prime ideal is proper). -/
theorem absNorm_ne_one_of_prime {𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}} :
    Ideal.absNorm 𝔭.1 ≠ 1 :=
  fun h => 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)

/-- A nonzero prime ideal has absolute norm at least `2` (it is neither `0` nor `1`). This is
the arithmetic fact underlying every prime-power Dirichlet estimate in this file. -/
theorem two_le_absNorm_of_prime {𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}} :
    2 ≤ Ideal.absNorm 𝔭.1 := by
  have h0 : Ideal.absNorm 𝔭.1 ≠ 0 := absNorm_ne_zero_of_prime K
  have h1 : Ideal.absNorm 𝔭.1 ≠ 1 := absNorm_ne_one_of_prime K
  omega

/-- Real-cast form of `two_le_absNorm_of_prime`: `(2 : ℝ) ≤ N𝔭`. -/
theorem two_le_absNorm_of_prime_real {𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}} :
    (2 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
  exact_mod_cast two_le_absNorm_of_prime (K := K) (𝔭 := 𝔭)

/-- For a nonzero prime ideal and real exponent `σ > 1`, `2·N𝔭^{-σ} < 1`: the Euler-factor
smallness estimate that forces non-vanishing and the uniform inverse bound. -/
theorem two_mul_rpow_neg_lt_one {𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}} {σ : ℝ}
    (hσ : 1 < σ) : 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ) < 1 := by
  have hN2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := two_le_absNorm_of_prime_real K
  have hmono : 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ) ≤ 2 * (2 : ℝ) ^ (-σ) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_pos_of_pos (by norm_num) _)).mpr (Real.rpow_le_rpow (by norm_num) hN2 (by linarith))
  have h2s : (2 : ℝ) * (2 : ℝ) ^ (-σ) < 1 := by
    have hs2 : (2 : ℝ) ^ (-σ) < (2 : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at hs2
    norm_num at hs2
    linarith
  linarith

/-- Prime-ideal norm sums converge for real exponent `σ > 1` (comparison with the full
ideal Dirichlet series). -/
theorem summable_primeIdeal_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)) := by
  have hσsum : Summable (fun I : Chebotarev.NonzeroIdeal K =>
      (Ideal.absNorm I.1 : ℝ) ^ (-σ)) := by
    have h1 := (Chebotarev.hasSum_nonzeroIdeal_absNorm_cpow K
      (s := ((σ : ℝ) : ℂ)) (by simpa using hσ)).summable
    have h1' : Summable (fun I : Chebotarev.NonzeroIdeal K =>
        (((Ideal.absNorm I.1 : ℝ) ^ (-σ) : ℝ) : ℂ)) := by
      refine h1.congr (fun I => ?_)
      rw [show ((Ideal.absNorm I.1 : ℕ) : ℂ) = (((Ideal.absNorm I.1 : ℝ)) : ℂ) by
          push_cast; ring,
        show -(((σ : ℝ)) : ℂ) = (((-σ : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    exact Complex.summable_ofReal.mp h1'
  have hinj : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
        (⟨𝔭.1, 𝔭.2.2⟩ : Chebotarev.NonzeroIdeal K)) := by
    intro 𝔭 𝔮 h
    have h' : (⟨𝔭.1, 𝔭.2.2⟩ : Chebotarev.NonzeroIdeal K) = ⟨𝔮.1, 𝔮.2.2⟩ := h
    exact Subtype.ext (Subtype.mk_eq_mk.mp h')
  exact (hσsum.comp_injective hinj).congr (fun 𝔭 => rfl)

/-- Log-weighted prime-ideal norm sums converge for `σ > 1`: absorb the logarithm
into a slightly smaller exponent. -/
theorem summable_primeIdeal_log_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      Real.log (Ideal.absNorm 𝔭.1) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)) := by
  set δ : ℝ := (σ - 1)/2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hexp : 1 < σ - δ := by rw [hδ]; linarith
  refine Summable.of_nonneg_of_le (fun 𝔭 => ?_) (fun 𝔭 => ?_)
    ((summable_primeIdeal_rpow K hexp).mul_left (1/δ))
  · have hN : (1:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_ne_zero_of_prime K)
    have := Real.log_nonneg hN
    positivity
  · have hN : (1:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_ne_zero_of_prime K)
    have hNpos : (0:ℝ) < (Ideal.absNorm 𝔭.1 : ℝ) := by linarith
    -- log N ≤ N^δ/δ
    have hlog : Real.log (Ideal.absNorm 𝔭.1) ≤ (Ideal.absNorm 𝔭.1 : ℝ)^δ / δ := by
      have h1 : Real.log ((Ideal.absNorm 𝔭.1 : ℝ)^δ)
          ≤ (Ideal.absNorm 𝔭.1 : ℝ)^δ - 1 :=
        Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hNpos δ)
      rw [Real.log_rpow hNpos] at h1
      refine (le_div_iff₀ hδpos).mpr ?_
      have h3 : (0:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ)^δ := (Real.rpow_pos_of_pos hNpos δ).le
      nlinarith
    calc Real.log (Ideal.absNorm 𝔭.1) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)
        ≤ ((Ideal.absNorm 𝔭.1 : ℝ)^δ / δ) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hNpos.le _)
      _ = (1/δ) * ((Ideal.absNorm 𝔭.1 : ℝ)^δ * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)) := by
          ring
      _ = (1/δ) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(σ - δ)) := by
          rw [← Real.rpow_add hNpos, show δ + -σ = -(σ - δ) by ring]

/-- Logarithmic derivative of a single Euler factor:
`(d/dz) log (1 - c^{-z})⁻¹ = -(log c)·c^{-z}/(1 - c^{-z})`. -/
theorem logDeriv_euler_factor {c : ℂ} (hc : c ≠ 0) (z : ℂ) :
    logDeriv (fun w => (1 - c ^ (-w))⁻¹) z
      = -(Complex.log c * c ^ (-z) / (1 - c ^ (-z))) := by
  have hinner_deriv : HasDerivAt (fun w : ℂ => 1 - c ^ (-w))
      (Complex.log c * c ^ (-z)) z := by
    have h1 : HasDerivAt (fun w : ℂ => -w) (-1 : ℂ) z := (hasDerivAt_id z).neg
    have h2 := h1.const_cpow (c := c) (Or.inl hc)
    have h3 := h2.const_sub 1
    rw [show -(c ^ (-z) * Complex.log c * (-1)) = Complex.log c * c ^ (-z) by ring] at h3
    exact h3
  have hinner_diff : DifferentiableAt ℂ (fun w : ℂ => 1 - c ^ (-w)) z :=
    hinner_deriv.differentiableAt
  have hfun : (fun w : ℂ => (1 - c ^ (-w))⁻¹)
      = fun w : ℂ => (fun v : ℂ => 1 - c ^ (-v)) w ^ (-1 : ℤ) := by
    funext w
    rw [zpow_neg_one]
  rw [hfun, logDeriv_fun_zpow hinner_diff]
  have hld : logDeriv (fun w : ℂ => 1 - c ^ (-w)) z
      = Complex.log c * c ^ (-z) / (1 - c ^ (-z)) := by
    rw [logDeriv_apply, hinner_deriv.deriv]
  rw [hld]
  push_cast
  ring

/-- On a compact subset of the half-plane `Re > 1`, the real part attains a minimum
`σ₀ > 1`. -/
theorem exists_min_re_of_isCompact {S : Set ℂ} (hS : IsCompact S) (hne : S.Nonempty)
    (hsub : S ⊆ {z : ℂ | 1 < z.re}) :
    ∃ σ₀ : ℝ, 1 < σ₀ ∧ ∀ x ∈ S, σ₀ ≤ x.re := by
  obtain ⟨z₀, hz₀S, hz₀min⟩ := hS.exists_isMinOn hne
    (Complex.continuous_re.continuousOn)
  exact ⟨z₀.re, hsub hz₀S, fun x hx => hz₀min hx⟩

/-- Norm bound for the Euler-factor correction on `Re ≥ σ₀ > 1`. -/
theorem euler_g_bound (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) {x : ℂ} {σ₀ : ℝ}
    (h1 : 1 < σ₀) (h2 : σ₀ ≤ x.re) :
    ‖(1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x))⁻¹ - 1‖
      ≤ 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) := by
  have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := absNorm_ne_zero_of_prime K
  have hN2 : (2:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := two_le_absNorm_of_prime_real K
  have hnorm : ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-x)‖ = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-x.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have hle : ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-x)‖ ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) := by
    rw [hnorm]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hhalf : ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-x)‖ ≤ 1/2 := by
    refine le_trans hle ?_
    have hstep1 : (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) ≤ (2:ℝ) ^ (-σ₀) := by
      rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
      refine (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith) _)
        (Real.rpow_pos_of_pos (by norm_num) _)).mpr ?_
      exact Real.rpow_le_rpow (by norm_num) hN2 (by linarith)
    have hstep2 : (2:ℝ) ^ (-σ₀) ≤ (2:ℝ) ^ (-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hstep3 : (2:ℝ) ^ (-(1:ℝ)) = 1/2 := by
      rw [Real.rpow_neg_one]
      norm_num
    calc (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) ≤ (2:ℝ) ^ (-σ₀) := hstep1
      _ ≤ (2:ℝ) ^ (-(1:ℝ)) := hstep2
      _ = 1/2 := hstep3
  set w : ℂ := (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x) with hwdef
  have hfac_ne : (1 : ℂ) - w ≠ 0 := by
    intro h0
    have h1' : w = 1 := by linear_combination -h0
    rw [h1'] at hhalf
    norm_num at hhalf
  have hid : (1 - w)⁻¹ - 1 = w * (1 - w)⁻¹ := by
    field_simp
    ring
  rw [hid, norm_mul]
  have hlow : (1:ℝ)/2 ≤ ‖1 - w‖ := by
    have h1' : ‖(1:ℂ)‖ - ‖w‖ ≤ ‖1 - w‖ := norm_sub_norm_le _ _
    rw [norm_one] at h1'
    linarith
  have hinv : ‖(1 - w)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    rw [show (2:ℝ) = (1/2)⁻¹ by norm_num]
    refine (inv_le_inv₀ ?_ (by norm_num)).mpr hlow
    linarith
  calc ‖w‖ * ‖(1 - w)⁻¹‖ ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) * 2 :=
        mul_le_mul hle hinv (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
    _ = 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) := by ring

/-- The Euler product over prime ideals is locally uniformly multipliable on the
half-plane `Re > 1`. -/
theorem multipliableLocallyUniformlyOn_eulerFactors :
    MultipliableLocallyUniformlyOn
      (fun (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (z : ℂ) =>
        (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹)
      {z : ℂ | 1 < z.re} := by
  have hfun : (fun (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (z : ℂ) =>
      (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹)
      = fun 𝔭 z => 1 + ((1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹ - 1) := by
    funext 𝔭 z
    ring
  rw [hfun]
  refine ⟨fun z => ∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (1 + ((1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹ - 1)), ?_⟩
  refine hasProdLocallyUniformlyOn_of_forall_compact
    (isOpen_lt continuous_const Complex.continuous_re) ?_
  intro S hsub hcS
  rcases S.eq_empty_or_nonempty with hN | hN
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn, hN] using tendstoUniformlyOn_empty
  obtain ⟨σ₀, hσ₀, hσ₀min⟩ := exists_min_re_of_isCompact hcS hN hsub
  have hnonvan : ∀ (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}), ∀ x ∈ S,
      (1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x) ≠ 0 := by
    intro 𝔭 x hx h0
    have hb := euler_g_bound K 𝔭 hσ₀ (hσ₀min x hx)
    rw [h0] at hb
    simp only [inv_zero, zero_sub, norm_neg, norm_one] at hb
    linarith [two_mul_rpow_neg_lt_one K (𝔭 := 𝔭) hσ₀]
  have hsum_u : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀)) :=
    (summable_primeIdeal_rpow K hσ₀).mul_left 2
  refine hsum_u.hasProdUniformlyOn_one_add hcS ?_ ?_
  · refine Filter.Eventually.of_forall (fun 𝔭 x hx => ?_)
    exact euler_g_bound K 𝔭 hσ₀ (hσ₀min x hx)
  · intro 𝔭
    refine ContinuousOn.sub ?_ continuousOn_const
    refine ContinuousOn.inv₀ ?_ (fun x hx => hnonvan 𝔭 x hx)
    refine ContinuousOn.sub continuousOn_const ?_
    refine Continuous.continuousOn ?_
    refine Continuous.const_cpow continuous_neg ?_
    left
    intro h0
    have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := absNorm_ne_zero_of_prime K
    rw [show ((Ideal.absNorm 𝔭.1 : ℕ) : ℂ) = 0 ↔ Ideal.absNorm 𝔭.1 = 0 from
      Nat.cast_eq_zero] at h0
    exact hne0 h0

/-- Euler factors do not vanish on `Re > 1`. -/
theorem euler_factor_ne_zero (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) {x : ℂ}
    (hx : 1 < x.re) :
    (1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x) ≠ 0 := by
  intro h0
  have hb := euler_g_bound K 𝔭 hx (le_refl x.re)
  rw [h0] at hb
  simp only [inv_zero, zero_sub, norm_neg, norm_one] at hb
  linarith [two_mul_rpow_neg_lt_one K (𝔭 := 𝔭) hx]

/-- The inverse Euler factor has norm at most `2` on `Re > 1`. -/
theorem euler_inv_norm_le_two (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) {x : ℂ}
    (hx : 1 < x.re) :
    ‖((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x))⁻¹‖ ≤ 2 := by
  have hb := euler_g_bound K 𝔭 hx (le_refl x.re)
  have hsmall : 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-x.re) ≤ 1 :=
    (two_mul_rpow_neg_lt_one K (𝔭 := 𝔭) hx).le
  calc ‖((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x))⁻¹‖
      ≤ ‖((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x))⁻¹ - 1‖ + ‖(1:ℂ)‖ :=
        norm_le_norm_sub_add _ _
    _ ≤ 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-x.re) + 1 := by
        rw [norm_one]
        linarith [hb]
    _ ≤ 2 := by linarith

/-- **SP2-vM: the prime-side series** (Poitou p. 6-02): for `Re s > 1`,
`−ζ_K'/ζ_K(s) = ∑_𝔭 log(N𝔭)·N𝔭^{-s}/(1 − N𝔭^{-s})`, differentiating the Euler
product through the locally uniform convergence. -/
theorem neg_logDeriv_dedekindZeta_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    -(logDeriv (NumberField.dedekindZeta K) s)
      = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)
            / (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) := by
  have hUo : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ {z : ℂ | 1 < z.re} := hs
  have hNcast : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ((Ideal.absNorm 𝔭.1 : ℕ) : ℂ) ≠ 0 := by
    intro 𝔭 h0
    have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := absNorm_ne_zero_of_prime K
    exact hne0 (Nat.cast_eq_zero.mp h0)
  have hf_ne : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ ≠ 0 :=
    fun 𝔭 => inv_ne_zero (euler_factor_ne_zero K 𝔭 hs)
  have hd : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      DifferentiableOn ℂ (fun z => ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹)
        {z : ℂ | 1 < z.re} := by
    intro 𝔭 z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.inv ?_ (euler_factor_ne_zero K 𝔭 hz)
    refine DifferentiableAt.const_sub ?_ 1
    exact (differentiable_neg.differentiableAt).const_cpow (Or.inl (hNcast 𝔭))
  -- summability of the factor log-derivatives at s
  have hclosed_bound : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ‖-(Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)
        / (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)))‖
      ≤ 2 * (Real.log (Ideal.absNorm 𝔭.1) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re)) := by
    intro 𝔭
    have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := absNorm_ne_zero_of_prime K
    have hN1 : (1:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne0
    have hlogeq : ‖Complex.log (Ideal.absNorm 𝔭.1 : ℂ)‖ = Real.log (Ideal.absNorm 𝔭.1) := by
      rw [show ((Ideal.absNorm 𝔭.1 : ℕ) : ℂ) = (((Ideal.absNorm 𝔭.1 : ℝ)) : ℂ) by
          push_cast; ring,
        ← Complex.ofReal_log (by linarith), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg hN1)]
    have hweq : ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    rw [norm_neg, norm_div, norm_mul, hlogeq, hweq]
    rw [div_eq_mul_inv, ← norm_inv]
    calc Real.log (Ideal.absNorm 𝔭.1) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re)
        * ‖((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹‖
        ≤ Real.log (Ideal.absNorm 𝔭.1) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re) * 2 := by
          refine mul_le_mul_of_nonneg_left (euler_inv_norm_le_two K 𝔭 hs) ?_
          have := Real.log_nonneg hN1
          positivity
      _ = 2 * (Real.log (Ideal.absNorm 𝔭.1) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re)) := by
          ring
  have hclosed_sum : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      -(Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)
        / (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)))) := by
    refine Summable.of_norm_bounded ?_ hclosed_bound
    exact (summable_primeIdeal_log_rpow K hs).mul_left 2
  have hld_eq : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      logDeriv (fun z => ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹) s
        = -(Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)
            / (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))) :=
    fun 𝔭 => logDeriv_euler_factor (hNcast 𝔭) s
  have hm : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      logDeriv (fun z => ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹) s) :=
    hclosed_sum.congr (fun 𝔭 => (hld_eq 𝔭).symm)
  have hnez : (∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹) ≠ 0 := by
    rw [← Chebotarev.dedekindZeta_eq_tprod_primeIdeal K hs]
    exact dedekindZeta_ne_zero_of_one_lt_re K hs
  have hkey := logDeriv_tprod_eq_tsum hUo hsU hf_ne hd hm
    (multipliableLocallyUniformlyOn_eulerFactors K) hnez
  have hev : NumberField.dedekindZeta K =ᶠ[nhds s]
      (fun z => ∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹) := by
    filter_upwards [hUo.mem_nhds hsU] with z hz
    exact Chebotarev.dedekindZeta_eq_tprod_primeIdeal K hz
  have hζld : logDeriv (NumberField.dedekindZeta K) s
      = logDeriv (fun z => ∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  calc -(logDeriv (NumberField.dedekindZeta K) s)
      = -(∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          logDeriv (fun z => ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹) s) := by
        rw [hζld, hkey]
    _ = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          -(logDeriv (fun z => ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹) s) :=
        tsum_neg.symm
    _ = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)
            / (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) := by
        refine tsum_congr (fun 𝔭 => ?_)
        rw [hld_eq 𝔭, neg_neg]

/-- Summability of the prime-power family `log(N𝔭)·N𝔭^{-(k+1)σ}` for `σ > 1`. -/
theorem summable_primeIdeal_pow_log_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ)) := by
  have hfacts : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (2:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := fun 𝔭 => two_le_absNorm_of_prime_real K
  have hr : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (0:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ) ∧ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ) < 1 := by
    intro 𝔭
    constructor
    · positivity
    · rw [Real.rpow_neg (by linarith [hfacts 𝔭]), inv_lt_one_iff₀]
      right
      exact Real.one_lt_rpow_iff_of_pos (by linarith [hfacts 𝔭]) |>.mpr
        (Or.inl ⟨by linarith [hfacts 𝔭], by linarith⟩)
  have hnn : ∀ pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
      0 ≤ Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ) := by
    intro pk
    have h1 : (1:ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) := by linarith [hfacts pk.1]
    have := Real.log_nonneg h1
    positivity
  -- the exponent identity N^{-(k+1)σ} = (N^{-σ})^{k+1}
  have hexp : ∀ (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (k : ℕ),
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(((k+1 : ℕ)) : ℝ) * σ)
        = ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)) ^ (k+1) := by
    intro 𝔭 k
    rw [← Real.rpow_natCast ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)) (k+1),
      ← Real.rpow_mul (by linarith [hfacts 𝔭])]
    congr 1
    push_cast
    ring
  refine (summable_prod_of_nonneg hnn).mpr ⟨?_, ?_⟩
  · intro 𝔭
    exact (((summable_geometric_of_lt_one (hr 𝔭).1 (hr 𝔭).2).mul_left
        ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ))).mul_left (Real.log (Ideal.absNorm 𝔭.1))).congr
      (fun k => by rw [hexp 𝔭 k, pow_succ'])
  · -- the 𝔭-sums are dominated by a constant multiple of log(N𝔭)·N𝔭^{-σ}
    have hval : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (∑' k : ℕ, Real.log (Ideal.absNorm 𝔭.1)
          * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(((k+1 : ℕ)) : ℝ) * σ))
        ≤ (1 - (2:ℝ) ^ (-σ))⁻¹ * (Real.log (Ideal.absNorm 𝔭.1)
            * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)) := by
      intro 𝔭
      have h2σ : (2:ℝ) ^ (-σ) < 1 := by
        rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
        right
        exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr
          (Or.inl ⟨by norm_num, by linarith⟩)
      have hmono : (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ) ≤ (2:ℝ) ^ (-σ) := by
        rw [Real.rpow_neg (by linarith [hfacts 𝔭]), Real.rpow_neg (by norm_num)]
        refine (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith [hfacts 𝔭]) _)
          (Real.rpow_pos_of_pos (by norm_num) _)).mpr ?_
        exact Real.rpow_le_rpow (by norm_num) (hfacts 𝔭) (by linarith)
      have hsum : (∑' k : ℕ, Real.log (Ideal.absNorm 𝔭.1)
          * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(((k+1 : ℕ)) : ℝ) * σ))
          = Real.log (Ideal.absNorm 𝔭.1) * ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)
            * (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ))⁻¹) := by
        rw [show (fun k : ℕ => Real.log (Ideal.absNorm 𝔭.1)
            * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(((k+1 : ℕ)) : ℝ) * σ))
            = fun k : ℕ => Real.log (Ideal.absNorm 𝔭.1)
              * ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)
                * ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)) ^ k) from
          funext (fun k => by rw [hexp 𝔭 k, pow_succ'])]
        rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one (hr 𝔭).1 (hr 𝔭).2]
      rw [hsum]
      have hlognn : 0 ≤ Real.log (Ideal.absNorm 𝔭.1) :=
        Real.log_nonneg (by linarith [hfacts 𝔭])
      have hinv : (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ))⁻¹ ≤ (1 - (2:ℝ) ^ (-σ))⁻¹ := by
        refine (inv_le_inv₀ (by linarith [(hr 𝔭).2]) (by linarith [h2σ, hmono])).mpr ?_
        linarith
      calc Real.log (Ideal.absNorm 𝔭.1) * ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)
            * (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ))⁻¹)
          ≤ Real.log (Ideal.absNorm 𝔭.1) * ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)
            * (1 - (2:ℝ) ^ (-σ))⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ hlognn
            refine mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = (1 - (2:ℝ) ^ (-σ))⁻¹ * (Real.log (Ideal.absNorm 𝔭.1)
            * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)) := by ring
    refine Summable.of_nonneg_of_le (fun 𝔭 => ?_) hval
      ((summable_primeIdeal_log_rpow K hσ).mul_left _)
    exact tsum_nonneg (fun k => hnn (𝔭, k))

/-- **The prime-power expansion of `−ζ_K'/ζ_K`** (Poitou p. 6-02): for `Re s > 1`,
`−ζ_K'/ζ_K(s) = ∑_{𝔭,m≥1} log(N𝔭)·N𝔭^{-ms}`, expanding each Euler factor
geometrically. -/
theorem neg_logDeriv_dedekindZeta_eq_tsum_prod {s : ℂ} (hs : 1 < s.re) :
    -(logDeriv (NumberField.dedekindZeta K) s)
      = ∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
          Complex.log (Ideal.absNorm pk.1.1 : ℂ)
            * (Ideal.absNorm pk.1.1 : ℂ) ^ (-(((pk.2+1 : ℕ)) : ℂ) * s) := by
  have hfacts : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      2 ≤ Ideal.absNorm 𝔭.1 := fun 𝔭 => two_le_absNorm_of_prime K
  -- norm identities
  have hnorm : ∀ (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (k : ℕ),
      ‖Complex.log (Ideal.absNorm 𝔭.1 : ℂ)
        * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(((k+1 : ℕ)) : ℂ) * s)‖
      = Real.log (Ideal.absNorm 𝔭.1)
        * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(((k+1 : ℕ)) : ℝ) * s.re) := by
    intro 𝔭 k
    have h2 := hfacts 𝔭
    have hN1 : (1:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ Ideal.absNorm 𝔭.1)
    have hlogeq : ‖Complex.log (Ideal.absNorm 𝔭.1 : ℂ)‖ = Real.log (Ideal.absNorm 𝔭.1) := by
      rw [show ((Ideal.absNorm 𝔭.1 : ℕ) : ℂ) = (((Ideal.absNorm 𝔭.1 : ℝ)) : ℂ) by
          push_cast; ring,
        ← Complex.ofReal_log (by linarith), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg hN1)]
    rw [norm_mul, hlogeq, Complex.norm_natCast_cpow_of_pos (by omega)]
    congr 2
    rw [show (-(((k+1 : ℕ)) : ℂ) * s) = -((((k+1 : ℕ)) : ℝ) : ℂ) * s by push_cast; ring]
    rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
    ring
  -- summability of the double family
  have hsummable : Summable (fun pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      Complex.log (Ideal.absNorm pk.1.1 : ℂ)
        * (Ideal.absNorm pk.1.1 : ℂ) ^ (-(((pk.2+1 : ℕ)) : ℂ) * s)) := by
    refine Summable.of_norm ?_
    refine (summable_primeIdeal_pow_log_rpow K hs).congr (fun pk => ?_)
    exact (hnorm pk.1 pk.2).symm
  have hslice : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      Summable (fun k : ℕ => Complex.log (Ideal.absNorm 𝔭.1 : ℂ)
        * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(((k+1 : ℕ)) : ℂ) * s)) := by
    intro 𝔭
    refine Summable.of_norm ?_
    refine (((summable_primeIdeal_pow_log_rpow K hs).prod_factor 𝔭).congr (fun k => ?_))
    exact (hnorm 𝔭 k).symm
  rw [neg_logDeriv_dedekindZeta_eq_tsum K hs, hsummable.tsum_prod' hslice]
  refine tsum_congr (fun 𝔭 => ?_)
  -- per-prime geometric expansion
  set w : ℂ := (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s) with hw
  have hwlt : ‖w‖ < 1 := by
    rw [hw, Complex.norm_natCast_cpow_of_pos (by have := hfacts 𝔭; omega), Complex.neg_re]
    have hN2 : (2:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by exact_mod_cast hfacts 𝔭
    rw [Real.rpow_neg (by linarith), inv_lt_one_iff₀]
    right
    exact Real.one_lt_rpow_iff_of_pos (by linarith) |>.mpr
      (Or.inl ⟨by linarith, by linarith⟩)
  have hgeom : (∑' k : ℕ, w ^ (k+1)) = w / (1 - w) := by
    rw [show (fun k : ℕ => w ^ (k+1)) = fun k : ℕ => w * w ^ k from
      funext (fun k => pow_succ' w k), tsum_mul_left,
      tsum_geometric_of_norm_lt_one hwlt, div_eq_mul_inv]
  have hcpow : ∀ k : ℕ, (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(((k+1 : ℕ)) : ℂ) * s) = w ^ (k+1) := by
    intro k
    rw [hw, show (-(((k+1 : ℕ)) : ℂ) * s) = (((k+1 : ℕ)) : ℂ) * (-s) by ring,
      Complex.cpow_nat_mul]
  calc Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)
        / (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))
      = Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * (w / (1 - w)) := by
        rw [hw, mul_div_assoc]
    _ = Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * ∑' k : ℕ, w ^ (k+1) := by rw [hgeom]
    _ = ∑' k : ℕ, Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * w ^ (k+1) := tsum_mul_left.symm
    _ = ∑' k : ℕ, Complex.log (Ideal.absNorm 𝔭.1 : ℂ)
          * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(((k+1 : ℕ)) : ℂ) * s) := by
        refine tsum_congr (fun k => ?_)
        rw [hcpow k]

/-- The ideals of the ring of integers form a countable type: each ideal has finite
absolute norm and there are finitely many ideals of each norm. -/
instance countable_ideal_ringOfIntegers (K : Type*) [Field K] [NumberField K] :
    Countable (Ideal (𝓞 K)) := by
  have h0 : (Set.univ : Set (Ideal (𝓞 K))) = ⋃ n : ℕ, {I | Ideal.absNorm I = n} := by
    ext I
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨Ideal.absNorm I, rfl⟩
  have h1 : (Set.univ : Set (Ideal (𝓞 K))).Countable := by
    rw [h0]
    exact Set.countable_iUnion (fun n => (Ideal.finite_setOf_absNorm_eq n).countable)
  exact Set.countable_univ_iff.mp h1

/-- A pointwise `tsum` of integrable functions with summable `L¹` norms is
integrable (companion to `MeasureTheory.integral_tsum_of_summable_integral_norm`,
which computes its integral). -/
theorem integrable_tsum_of_summable_integral_norm {ι : Type*} [Countable ι]
    {F : ι → ℝ → ℂ} (hF_int : ∀ i, Integrable (F i) (volume : Measure ℝ))
    (hF_sum : Summable fun i => ∫ a : ℝ, ‖F i a‖) :
    Integrable (fun a : ℝ => ∑' i, F i a) (volume : Measure ℝ) := by
  refine ⟨AEStronglyMeasurable.tsum (fun i => (hF_int i).1), ?_⟩
  show ∫⁻ a, ‖∑' i, F i a‖ₑ ∂(volume : Measure ℝ) < ⊤
  have h0 : ∀ i : ι, ∫⁻ a, ‖F i a‖ₑ ∂(volume : Measure ℝ) = ‖∫ a : ℝ, ‖F i a‖‖ₑ := by
    intro i
    rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hF_int i),
      Real.enorm_eq_ofReal (integral_nonneg (fun a => norm_nonneg (F i a)))]
  calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂(volume : Measure ℝ)
      ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂(volume : Measure ℝ) :=
        lintegral_mono (fun a => enorm_tsum_le_tsum_enorm)
    _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂(volume : Measure ℝ) :=
        lintegral_tsum (fun i => (hF_int i).1.enorm)
    _ = ∑' i, ‖∫ a : ℝ, ‖F i a‖‖ₑ := tsum_congr h0
    _ < ⊤ := by
        have h1 : ∀ i : ι, ‖∫ a : ℝ, ‖F i a‖‖ₑ = ((‖∫ a : ℝ, ‖F i a‖‖₊ : ℝ≥0) : ℝ≥0∞) := by
          intro i
          rfl
        rw [tsum_congr h1]
        exact Ne.lt_top (ENNReal.tsum_coe_ne_top_iff_summable.2
          (NNReal.summable_coe.1 hF_sum.abs))

/-- **Translation identity**: multiplying a Fourier-type integral by `e^{-itβ}`
translates the integrand by `β`. -/
theorem integral_translate_cexp (G : ℝ → ℂ) (β t : ℝ) :
    (∫ x : ℝ, G x * Complex.exp ((t*x : ℝ) * Complex.I))
        * Complex.exp (((-(t*β)) : ℝ) * Complex.I)
      = ∫ u : ℝ, G (u + β) * Complex.exp ((t*u : ℝ) * Complex.I) := by
  have h2 := (measurePreserving_add_right (volume : Measure ℝ) β).integral_comp
    (Homeomorph.addRight β).isClosedEmbedding.measurableEmbedding
    (fun v : ℝ => G v * Complex.exp ((t*(v - β) : ℝ) * Complex.I))
  have h3 : (∫ u : ℝ, G (u + β) * Complex.exp ((t*u : ℝ) * Complex.I))
      = ∫ v : ℝ, G v * Complex.exp ((t*(v - β) : ℝ) * Complex.I) := by
    rw [← h2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    show G (u + β) * Complex.exp ((t*u : ℝ) * Complex.I)
        = G (u + β) * Complex.exp ((t*((u + β) - β) : ℝ) * Complex.I)
    rw [show (t*((u + β) - β) : ℝ) = (t*u : ℝ) by ring]
  rw [h3, ← MeasureTheory.integral_mul_const]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  show G v * Complex.exp ((t*v : ℝ) * Complex.I) * Complex.exp (((-(t*β)) : ℝ) * Complex.I)
      = G v * Complex.exp ((t*(v - β) : ℝ) * Complex.I)
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

variable (K : Type*) [Field K] [NumberField K]

/-- **Poitou's prime-side function `H`** (p. 6-02):
`H(u) = ∑_{𝔭,m≥1} log(N𝔭)·N𝔭^{-m(1+a)}·F_a(u + m·log N𝔭)`, where
`F_a(x) = F(x)·e^{(1/2+a)x}`. Its one-sided means at `0` are the limit of the
prime-side edge integral. -/
noncomputable def primeSideH (a : ℝ) (F : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
    ((Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
      * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
          * ((Real.exp ((1/2+a)
              * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ))

/-- Each prime-power term of `primeSideH` is integrable. -/
theorem integrable_primeSideH_term {a : ℝ} {F : ℝ → ℂ}
    (hFa : Integrable (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)))
    (pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ) :
    Integrable (fun u : ℝ =>
      ((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
        * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * ((Real.exp ((1/2+a)
                * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ)))
      (volume : Measure ℝ) := by
  refine Integrable.const_mul ?_ _
  exact hFa.comp_add_right _

/-- The `L¹` norms of the `primeSideH` terms are summable, with the geometric
values `log(N𝔭)·N𝔭^{-m(1+a)}·‖F_a‖₁`. -/
theorem summable_integral_norm_primeSideH {a : ℝ} (ha : 0 < a) (F : ℝ → ℂ) :
    Summable (fun pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      ∫ u : ℝ, ‖((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
        * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * ((Real.exp ((1/2+a)
                * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ))‖) := by
  have hval : ∀ pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
      (∫ u : ℝ, ‖((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
        * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * ((Real.exp ((1/2+a)
                * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ))‖)
      = (Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)))
        * ∫ x : ℝ, ‖F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)‖ := by
    intro pk
    have hne0 : Ideal.absNorm pk.1.1 ≠ 0 := absNorm_ne_zero_of_prime K
    have hN1 : (1:ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne0
    have hwnn : 0 ≤ Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) := by
      have := Real.log_nonneg hN1
      positivity
    rw [show (∫ u : ℝ, ‖((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
        * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * ((Real.exp ((1/2+a)
                * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ))‖)
        = ∫ u : ℝ, (Real.log (Ideal.absNorm pk.1.1)
            * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)))
          * ‖(fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ))
              (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))‖ from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      show ‖((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
        * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * ((Real.exp ((1/2+a)
                * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ))‖
        = (Real.log (Ideal.absNorm pk.1.1)
            * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)))
          * ‖F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
              * ((Real.exp ((1/2+a)
                  * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ)‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwnn]]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact (measurePreserving_add_right (volume : Measure ℝ)
        ((((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))).integral_comp
      (Homeomorph.addRight _).isClosedEmbedding.measurableEmbedding
      (fun x : ℝ => ‖F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)‖)
  refine Summable.congr ?_ (fun pk => (hval pk).symm)
  exact (summable_primeIdeal_pow_log_rpow K (by linarith : (1:ℝ) < 1+a)).mul_right _

/-- `primeSideH` is integrable. -/
theorem integrable_primeSideH {a : ℝ} (ha : 0 < a) {F : ℝ → ℂ}
    (hFa : Integrable (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ))) :
    Integrable (primeSideH K a F) (volume : Measure ℝ) :=
  integrable_tsum_of_summable_integral_norm
    (fun pk => integrable_primeSideH_term K hFa pk)
    (summable_integral_norm_primeSideH K ha F)

/-- **The fixed-`t` prime-side identity** (Poitou pp. 6-02/6-03, the "Calcul de la
partie ultramétrique"): on the edge `s = 1+a+it`,

`Φ(s)·(−ζ_K'/ζ_K(s)) = ∫ H(u)·e^{itu} du`,

expanding the Dirichlet series, translating each prime-power term, and summing
back under the integral. -/
theorem paperPhi_mul_neg_logDeriv_eq (K : Type*) [Field K] [NumberField K]
    {a : ℝ} (ha : 0 < a) {F : ℝ → ℂ}
    (hFa : Integrable (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)))
    (t : ℝ) :
    paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
        * (-(logDeriv (NumberField.dedekindZeta K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
      = ∫ u : ℝ, primeSideH K a F u * Complex.exp ((t*u : ℝ) * Complex.I) := by
  set s : ℂ := ((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I with hs_def
  have hs : 1 < s.re := by
    rw [hs_def, show ((((1+a : ℝ)):ℂ) + (t:ℂ)*Complex.I).re = 1+a from by simp]
    linarith
  set G : ℝ → ℂ := fun x => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ) with hG_def
  -- Step 1: the Φ-value on the edge
  have hφ : paperPhi F s = ∫ x : ℝ, G x * Complex.exp ((t*x : ℝ) * Complex.I) := by
    rw [paperPhi]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show F x * Complex.exp ((s - 1/2) * x)
        = F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ) * Complex.exp ((t*x : ℝ) * Complex.I)
    rw [show ((s - 1/2) * x) = (((1/2+a) * x : ℝ) : ℂ) + ((t*x : ℝ) : ℂ) * Complex.I from by
      rw [hs_def]
      push_cast
      ring]
    rw [Complex.exp_add, Complex.ofReal_exp]
    ring
  -- per-term data
  have hfacts : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      2 ≤ Ideal.absNorm 𝔭.1 := fun 𝔭 => two_le_absNorm_of_prime K
  -- Step 4 (per-term): Φ(s)·log(N𝔭)·N𝔭^{-(k+1)s} = ∫ H_pk(u)·e^{itu} du
  have hterm : ∀ pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
      paperPhi F s * (Complex.log (Ideal.absNorm pk.1.1 : ℂ)
          * (Ideal.absNorm pk.1.1 : ℂ) ^ (-(((pk.2+1 : ℕ)) : ℂ) * s))
      = ∫ u : ℝ, (((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
        * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * ((Real.exp ((1/2+a)
                * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ)))
          * Complex.exp ((t*u : ℝ) * Complex.I) := by
    intro pk
    have h2 := hfacts pk.1
    have hN0 : (0:ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) := by positivity
    have hN1 : (1:ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ Ideal.absNorm pk.1.1)
    have hNne : ((Ideal.absNorm pk.1.1 : ℕ) : ℂ) ≠ 0 := by
      rw [Ne, Nat.cast_eq_zero]
      omega
    set β : ℝ := (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) with hβ
    -- split the prime power along s = (1+a) + it
    have hsplit : (Ideal.absNorm pk.1.1 : ℂ) ^ (-(((pk.2+1 : ℕ)) : ℂ) * s)
        = (((Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
          * Complex.exp (((-(t*β)) : ℝ) * Complex.I) := by
      have h3 : (-(((pk.2+1 : ℕ)) : ℂ) * s)
          = ((-(((pk.2+1 : ℕ)) : ℝ) * (1+a) : ℝ) : ℂ)
            + ((-((((pk.2+1 : ℕ)) : ℝ) * t) : ℝ) : ℂ) * Complex.I := by
        rw [hs_def]
        push_cast
        ring
      rw [h3, Complex.cpow_add _ _ hNne]
      congr 1
      · rw [show ((Ideal.absNorm pk.1.1 : ℕ) : ℂ) = (((Ideal.absNorm pk.1.1 : ℝ)) : ℂ) by
            push_cast; ring,
          ← Complex.ofReal_cpow hN0]
      · rw [Complex.cpow_def_of_ne_zero hNne]
        congr 1
        rw [show ((Ideal.absNorm pk.1.1 : ℕ) : ℂ) = (((Ideal.absNorm pk.1.1 : ℝ)) : ℂ) by
            push_cast; ring,
          ← Complex.ofReal_log hN0, hβ]
        push_cast
        ring
    -- the complex log is the real log
    have hlog : Complex.log (Ideal.absNorm pk.1.1 : ℂ)
        = ((Real.log (Ideal.absNorm pk.1.1) : ℝ) : ℂ) := by
      rw [show ((Ideal.absNorm pk.1.1 : ℕ) : ℂ) = (((Ideal.absNorm pk.1.1 : ℝ)) : ℂ) by
          push_cast; ring,
        ← Complex.ofReal_log hN0]
    rw [hsplit, hlog, hφ]
    -- translate
    have htrans := integral_translate_cexp G β t
    calc (∫ x : ℝ, G x * Complex.exp ((t*x : ℝ) * Complex.I))
          * (((Real.log (Ideal.absNorm pk.1.1) : ℝ) : ℂ)
            * ((((Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
              * Complex.exp (((-(t*β)) : ℝ) * Complex.I)))
        = (((Real.log (Ideal.absNorm pk.1.1)
              * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ))
          * ((∫ x : ℝ, G x * Complex.exp ((t*x : ℝ) * Complex.I))
            * Complex.exp (((-(t*β)) : ℝ) * Complex.I)) := by
          push_cast
          ring
      _ = (((Real.log (Ideal.absNorm pk.1.1)
              * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ))
          * ∫ u : ℝ, G (u + β) * Complex.exp ((t*u : ℝ) * Complex.I) := by
          rw [htrans]
      _ = ∫ u : ℝ, (((Real.log (Ideal.absNorm pk.1.1)
              * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ))
          * (G (u + β) * Complex.exp ((t*u : ℝ) * Complex.I)) := by
          rw [MeasureTheory.integral_const_mul]
      _ = ∫ u : ℝ, (((Real.log (Ideal.absNorm pk.1.1)
              * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
            * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
              * ((Real.exp ((1/2+a)
                  * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ)))
            * Complex.exp ((t*u : ℝ) * Complex.I) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
          show (((Real.log (Ideal.absNorm pk.1.1)
              * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ))
            * (G (u + β) * Complex.exp ((t*u : ℝ) * Complex.I)) = _
          rw [hG_def, hβ]
          ring
  -- Step 2+3: expand the series and multiply in
  rw [neg_logDeriv_dedekindZeta_eq_tsum_prod K hs, ← tsum_mul_left]
  -- Step 5: sum the per-term identities and swap with the integral
  rw [tsum_congr hterm]
  -- integral_tsum in the ∑'∫ → ∫∑' direction
  have hint_pk : ∀ pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
      Integrable (fun u : ℝ =>
        (((Real.log (Ideal.absNorm pk.1.1)
            * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
          * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
              * ((Real.exp ((1/2+a)
                  * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ)))
            * Complex.exp ((t*u : ℝ) * Complex.I)) (volume : Measure ℝ) := by
    intro pk
    refine (integrable_primeSideH_term K hFa pk).mul_bdd (c := 1) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      refine Complex.continuous_exp.comp ?_
      exact (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
        continuous_const
    · filter_upwards [] with u
      rw [Complex.norm_exp_ofReal_mul_I]
  have hnorm_eq : ∀ pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
      (∫ u : ℝ, ‖(((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
        * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * ((Real.exp ((1/2+a)
                * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ)))
          * Complex.exp ((t*u : ℝ) * Complex.I)‖)
      = ∫ u : ℝ, ‖((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
        * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * ((Real.exp ((1/2+a)
                * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ))‖ := by
    intro pk
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    show ‖(((Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
      * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
          * ((Real.exp ((1/2+a)
              * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ)))
        * Complex.exp ((t*u : ℝ) * Complex.I)‖
      = ‖((Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
      * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
          * ((Real.exp ((1/2+a)
              * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ))‖
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [MeasureTheory.integral_tsum_of_summable_integral_norm hint_pk
    (by
      refine Summable.congr (summable_integral_norm_primeSideH K ha F) (fun pk => ?_)
      exact (hnorm_eq pk).symm)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  beta_reduce
  rw [show primeSideH K a F u
      = ∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
        ((Real.log (Ideal.absNorm pk.1.1)
            * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * (1+a)) : ℝ) : ℂ)
          * (F (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
              * ((Real.exp ((1/2+a)
                  * (u + (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1))) : ℝ) : ℂ))
      from rfl]
  exact tsum_mul_right

/-- Summability of the prime-power logarithmic series `∑ N𝔭^{-(m+1)σ}/(m+1)`
(dominated by the von Mangoldt series via `log N𝔭 ≥ log 2`). -/
theorem summable_primeIdeal_pow_div {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ) / ((pk.2+1 : ℕ) : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun pk => ?_) (fun pk => ?_)
    (((summable_primeIdeal_pow_log_rpow K hσ).mul_left (1/Real.log 2)))
  · positivity
  · have hfacts : (2:ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) := two_le_absNorm_of_prime_real K
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogN : Real.log 2 ≤ Real.log (Ideal.absNorm pk.1.1) :=
      Real.log_le_log (by norm_num) hfacts
    have hm1 : (1:ℝ) ≤ ((pk.2+1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero _)
    have hrpow : (0:ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ) := by
      positivity
    calc (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ) / ((pk.2+1 : ℕ) : ℝ)
        ≤ (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ) := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
      _ = (1/Real.log 2) * (Real.log 2
            * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ)) := by
          field_simp
      _ ≤ (1/Real.log 2) * (Real.log (Ideal.absNorm pk.1.1)
            * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hlogN hrpow

/-- **The Dedekind zeta function as an exponential** (log-Euler product, prime-ideal
form): `ζ_K(s) = exp(∑_𝔭 -log(1 - N𝔭^{-s}))` on `Re s > 1`. -/
theorem dedekindZeta_eq_exp_tsum {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s
      = Complex.exp (∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          -Complex.log (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))) := by
  have hsum : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) := by
    refine Summable.of_norm ?_
    refine (summable_primeIdeal_rpow K hs).congr (fun 𝔭 => ?_)
    have hpos : 0 < Ideal.absNorm 𝔭.1 := Nat.pos_of_ne_zero (absNorm_ne_zero_of_prime K)
    rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
  have hne : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (1:ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s) ≠ 0 :=
    fun 𝔭 => euler_factor_ne_zero K 𝔭 hs
  have H := (hsum.clog_one_sub.neg).hasSum.cexp.tprod_eq
  simp only [Function.comp_apply, Complex.exp_neg, Complex.exp_log (hne _)] at H
  rw [Chebotarev.dedekindZeta_eq_tprod_primeIdeal K hs]
  exact H

/-- **The Dedekind zeta function as an exponential of the prime-power series**:
`ζ_K(s) = exp(∑_{𝔭,m} N𝔭^{-(m+1)s}/(m+1))` on `Re s > 1`. -/
theorem dedekindZeta_eq_exp_tsum_prod {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s
      = Complex.exp (∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
          (Ideal.absNorm pk.1.1 : ℂ) ^ (-(((pk.2+1 : ℕ)) : ℂ) * s)
            / ((pk.2+1 : ℕ) : ℂ)) := by
  rw [dedekindZeta_eq_exp_tsum K hs]
  congr 1
  -- norms of the double-series terms
  have hnorm : ∀ pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
      ‖(Ideal.absNorm pk.1.1 : ℂ) ^ (-(((pk.2+1 : ℕ)) : ℂ) * s) / ((pk.2+1 : ℕ) : ℂ)‖
      = (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * s.re)
          / ((pk.2+1 : ℕ) : ℝ) := by
    intro pk
    have hpos : 0 < Ideal.absNorm pk.1.1 := Nat.pos_of_ne_zero (absNorm_ne_zero_of_prime K)
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hpos, Complex.norm_natCast]
    congr 2
    rw [show (-(((pk.2+1 : ℕ)) : ℂ) * s) = -((((pk.2+1 : ℕ)) : ℝ) : ℂ) * s by
        push_cast; ring]
    rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
    ring
  have hsummable : Summable (fun pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      (Ideal.absNorm pk.1.1 : ℂ) ^ (-(((pk.2+1 : ℕ)) : ℂ) * s)
        / ((pk.2+1 : ℕ) : ℂ)) := by
    refine Summable.of_norm ?_
    refine (summable_primeIdeal_pow_div K hs).congr (fun pk => ?_)
    exact (hnorm pk).symm
  have hslice : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      Summable (fun k : ℕ => (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(((k+1 : ℕ)) : ℂ) * s)
        / ((k+1 : ℕ) : ℂ)) := by
    intro 𝔭
    refine Summable.of_norm ?_
    refine ((summable_primeIdeal_pow_div K hs).prod_factor 𝔭).congr (fun k => ?_)
    exact (hnorm (𝔭, k)).symm
  rw [hsummable.tsum_prod' hslice]
  refine tsum_congr (fun 𝔭 => ?_)
  -- per-prime Taylor expansion of -log(1 - N^{-s})
  have hpos : 0 < Ideal.absNorm 𝔭.1 := Nat.pos_of_ne_zero (absNorm_ne_zero_of_prime K)
  have hfacts : (2:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := two_le_absNorm_of_prime_real K
  have hz : ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
    refine Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have h1 := Complex.hasSum_taylorSeries_neg_log hz
  have h2 : HasSum (fun m : ℕ =>
      ((Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) ^ (m+1) / ((m+1 : ℕ) : ℂ))
      (-Complex.log (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))) := by
    refine (hasSum_nat_add_iff (f := fun n : ℕ =>
      ((Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) ^ n / (n : ℂ)) 1).mpr ?_
    simpa using h1
  rw [← h2.tsum_eq]
  refine tsum_congr (fun m => ?_)
  rw [show (-(((m+1 : ℕ)) : ℂ) * s) = (((m+1 : ℕ)) : ℂ) * (-s) by push_cast; ring,
    Complex.cpow_nat_mul]

/-- On the real ray `σ > 1`, `ζ_K(σ)` is the coercion of the positive real number
`exp(∑_{𝔭,m} N𝔭^{-(m+1)σ}/(m+1))`. -/
theorem dedekindZeta_ofReal_eq {σ : ℝ} (hσ : 1 < σ) :
    NumberField.dedekindZeta K (σ : ℂ)
      = ((Real.exp (∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
          (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ)
            / ((pk.2+1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
  have hσ' : 1 < (σ : ℂ).re := by
    rw [Complex.ofReal_re]
    exact hσ
  rw [dedekindZeta_eq_exp_tsum_prod K hσ', Complex.ofReal_exp]
  congr 1
  rw [Complex.ofReal_tsum]
  refine tsum_congr (fun pk => ?_)
  have hpos : 0 ≤ (Ideal.absNorm pk.1.1 : ℝ) := Nat.cast_nonneg _
  rw [Complex.ofReal_div, Complex.ofReal_cpow hpos]
  push_cast
  ring_nf

/-- `ζ_K(σ) > 0` on the real ray, read on the real part. -/
theorem dedekindZeta_ofReal_re_pos {σ : ℝ} (hσ : 1 < σ) :
    0 < (NumberField.dedekindZeta K (σ : ℂ)).re := by
  rw [dedekindZeta_ofReal_eq K hσ, Complex.ofReal_re]
  exact Real.exp_pos _

/-- **The logarithmic Euler product on the real ray** (B–F eq. (4)):
`log ζ_K(σ) = ∑_{𝔭,m} N𝔭^{-(m+1)σ}/(m+1)` for `σ > 1`. -/
theorem real_log_dedekindZeta {σ : ℝ} (hσ : 1 < σ) :
    Real.log ((NumberField.dedekindZeta K (σ : ℂ)).re)
      = ∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
          (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ)
            / ((pk.2+1 : ℕ) : ℝ) := by
  rw [dedekindZeta_ofReal_eq K hσ, Complex.ofReal_re, Real.log_exp]

end DedekindResidue

end
