/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
/-
DedekindResidue: Belabas–Friedman Lemma 4 — the two-cutoff difference estimates.

Applying Lemma 3 at the two cutoffs `X` and `X' = X/e^a` and subtracting kills the
`T`-independent terms (`Φ(0)+Φ(1)`, `log Δ_K`, the Γ-constant), and the paper's four
estimates bound what remains: the sine difference by the mean value theorem
(`|sin(Tγ) − sin(T'γ)| ≤ a|γ|`, losing no `log X`), the cosine terms trivially, the
tail integrals by the exact antiderivative of the kernel, and the archimedean
integrals by monotonicity and the mean value theorem (the `β`-bound). Everything is
carried at real `σ > 1` with `h = σ − 1/2` explicit; the `σ → 1⁺` limit is taken in
the final inequality (never by analytic continuation of the identity), which
reproduces the paper's Lemma 4 (`Mostways`, eq. (Explicit2)) at `k = ℚ`.

Source: B–F 1305.0035, §3 (TeX lines 409–519); route: decomposition-t011.md.
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.Lemma3
public import LeanPool.Odlyzko.DedekindResidue.QSide

@[expose] public section

namespace DedekindResidue

open Complex NumberField Filter Real

variable (K : Type*) [Field K] [NumberField K]

/-! ### The sine-difference estimate (paper lines 446–456)

The mean value theorem gives `|sin(γT) − sin(γT')| ≤ |γ|(T − T')`, so the difference
of the sine series at two cutoffs loses the `1/γ` and is bounded by
`(T−T')·2h²·Σ_ρ m_ρ/(h²+γ_ρ²)` — no `log X` loss. -/

/-- Pointwise: `‖zeroSinTerm at X − zeroSinTerm at X'‖ ≤ 2h²(T−T')/(h²+γ²)`. -/
theorem norm_zeroSinTerm_sub_le {σ : ℝ} (hσ : 1/2 < σ) {X X' : ℝ} (hX' : 1 < X')
    (hXX : X' ≤ X) (γ : ℝ) :
    ‖zeroSinTerm (σ:ℂ) X γ - zeroSinTerm (σ:ℂ) X' γ‖
      ≤ 2*(σ - 1/2)^2 * (Real.log X - Real.log X') / ((σ - 1/2)^2 + γ^2) := by
  have hh : (0:ℝ) < σ - 1/2 := by linarith
  have hh2 : (0:ℝ) < (σ - 1/2)^2 := pow_pos hh 2
  have hT'0 : 0 < Real.log X' := Real.log_pos hX'
  have hTT : Real.log X' ≤ Real.log X := Real.log_le_log (by linarith) hXX
  have hD : (0:ℝ) < (σ - 1/2)^2 + γ^2 := by positivity
  by_cases hγ : γ = 0
  · -- plateau: the difference of the plateau values is `2(T − T')`
    subst hγ
    rw [zeroSinTerm, zeroSinTerm, if_pos rfl, if_pos rfl]
    have h1 : (2 * (Real.log X : ℂ)) - 2 * (Real.log X' : ℂ)
        = ((2*(Real.log X - Real.log X') : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [show (0:ℝ)^2 = 0 by norm_num, add_zero]
    rw [div_eq_mul_inv, show 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
        * ((σ - 1/2)^2)⁻¹ = 2*(Real.log X - Real.log X')
          * ((σ - 1/2)^2 * ((σ - 1/2)^2)⁻¹) by ring,
      mul_inv_cancel₀ hh2.ne', mul_one]
  · -- `γ ≠ 0`: MVT via `LipschitzWith 1 sin`
    have h1 : zeroSinTerm (σ:ℂ) X γ - zeroSinTerm (σ:ℂ) X' γ
        = ((2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*γ)
            * (Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ)) : ℝ) : ℂ) := by
      rw [zeroSinTerm, zeroSinTerm, if_neg hγ, if_neg hγ]
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    have hsin : |Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ)|
        ≤ (Real.log X - Real.log X') * |γ| := by
      have h2 := Real.lipschitzWith_sin.dist_le_mul (Real.log X * γ) (Real.log X' * γ)
      rw [Real.dist_eq, Real.dist_eq] at h2
      calc |Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ)|
          ≤ 1 * |Real.log X * γ - Real.log X' * γ| := by exact_mod_cast h2
        _ = |(Real.log X - Real.log X')| * |γ| := by
            rw [one_mul, show Real.log X * γ - Real.log X' * γ
              = (Real.log X - Real.log X') * γ by ring, abs_mul]
        _ = (Real.log X - Real.log X') * |γ| := by
            rw [abs_of_nonneg (by linarith)]
    have hγpos : (0:ℝ) < |γ| := abs_pos.mpr hγ
    calc |2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*γ)
          * (Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ))|
        = 2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*|γ|)
          * |Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ)| := by
          rw [abs_mul, abs_div, abs_mul, abs_two, abs_of_pos hh2, abs_mul,
            abs_of_pos hD]
      _ ≤ 2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*|γ|)
          * ((Real.log X - Real.log X') * |γ|) := by
          gcongr
      _ = 2*(σ - 1/2)^2 * (Real.log X - Real.log X') / ((σ - 1/2)^2 + γ^2) := by
          field_simp

/-- **The sine-difference estimate**: the two-cutoff difference of the sine series is
bounded by `2h²(T−T')·Σ_ρ m_ρ/(h²+γ_ρ²)`. -/
theorem norm_tsum_zeroSinTerm_sub_le {σ : ℝ} (hσ : 1/2 < σ) {X X' : ℝ} (hX' : 1 < X')
    (hXX : X' ≤ X) :
    ‖(∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im)
      - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im‖
      ≤ 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
          * ∑' ρ : ZetaZeros K,
              (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2) := by
  have hX : 1 < X := lt_of_lt_of_le hX' hXX
  have hsum : Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im) :=
    summable_zetaZeros_mul_of_norm_le K hσ (fun γ => norm_zeroSinTerm_le hσ hX γ)
  have hsum' : Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im) :=
    summable_zetaZeros_mul_of_norm_le K hσ (fun γ => norm_zeroSinTerm_le hσ hX' γ)
  rw [← Summable.tsum_sub hsum hsum']
  have hmaj : Summable (fun ρ : ZetaZeros K =>
      2*(σ - 1/2)^2 * (Real.log X - Real.log X')
        * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2))) :=
    (summable_zetaZeros_inv_sq K (σ - 1/2) (by linarith)).mul_left _
  have hpt : ∀ ρ : ZetaZeros K,
      ‖(zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im
        - (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im‖
      ≤ 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
          * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by
    intro ρ
    have hdnn : (0:ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
      exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
    rw [show (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im
        - (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im
        = (zetaZeroDivisor K ρ.1 : ℂ)
          * (zeroSinTerm (σ:ℂ) X ρ.1.im - zeroSinTerm (σ:ℂ) X' ρ.1.im) by ring,
      norm_mul, Complex.norm_intCast, abs_of_nonneg hdnn]
    calc (zetaZeroDivisor K ρ.1 : ℝ)
          * ‖zeroSinTerm (σ:ℂ) X ρ.1.im - zeroSinTerm (σ:ℂ) X' ρ.1.im‖
        ≤ (zetaZeroDivisor K ρ.1 : ℝ)
          * (2*(σ - 1/2)^2 * (Real.log X - Real.log X')
              / ((σ - 1/2)^2 + ρ.1.im^2)) :=
          mul_le_mul_of_nonneg_left (norm_zeroSinTerm_sub_le hσ hX' hXX _) hdnn
      _ = 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
            * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by ring
  rw [← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm ?_).trans
    (Summable.tsum_le_tsum (fun ρ => hpt ρ) ?_ hmaj)
  · exact hmaj.of_nonneg_of_le (fun ρ => norm_nonneg _) hpt
  · exact (hsum.sub hsum').norm

/-! ### The cosine and tail-integral estimates (paper lines 457–467)

The cosine terms are bounded trivially (`|cos| ≤ 1`) at each cutoff; the tail
integral is evaluated exactly by the kernel antiderivative
`d/dt(−e^{−ht}/t) = (h + 1/t)e^{−ht}/t`, giving the clean `1/T` bound with no
constants lost. -/

/-- Generic norm bound: a `c/(h²+γ²)`-bounded test function has divisor-weighted
series bounded by `c·Σ_ρ m_ρ/(h²+γ_ρ²)`. -/
theorem norm_tsum_zetaZeros_mul_le {σ : ℝ} (hσ : 1/2 < σ) {f : ℝ → ℂ} {c : ℝ}
    (hf : ∀ γ : ℝ, ‖f γ‖ ≤ c / ((σ - 1/2)^2 + γ^2)) :
    ‖∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * f ρ.1.im‖
      ≤ c * ∑' ρ : ZetaZeros K,
          (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2) := by
  have hmaj : Summable (fun ρ : ZetaZeros K =>
      c * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2))) :=
    (summable_zetaZeros_inv_sq K (σ - 1/2) (by linarith)).mul_left c
  have hpt : ∀ ρ : ZetaZeros K,
      ‖(zetaZeroDivisor K ρ.1 : ℂ) * f ρ.1.im‖
        ≤ c * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by
    intro ρ
    have hdnn : (0:ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
      exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hdnn]
    calc (zetaZeroDivisor K ρ.1 : ℝ) * ‖f ρ.1.im‖
        ≤ (zetaZeroDivisor K ρ.1 : ℝ) * (c / ((σ - 1/2)^2 + ρ.1.im^2)) :=
          mul_le_mul_of_nonneg_left (hf _) hdnn
      _ = c * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by ring
  rw [← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm ?_).trans
    (Summable.tsum_le_tsum (fun ρ => hpt ρ) ?_ hmaj)
  · exact hmaj.of_nonneg_of_le (fun ρ => norm_nonneg _) hpt
  · exact (summable_zetaZeros_mul_of_norm_le K hσ hf).norm

/-- **The cosine-terms estimate**: the two-cutoff difference of the cosine series is
bounded by `(2(h+1/T) + 2(h+1/T'))·Σ_ρ m_ρ/(h²+γ_ρ²)` (triangle inequality, `|cos|≤1`
at each cutoff). -/
theorem norm_tsum_zeroCosTerm_sub_le {σ : ℝ} (hσ : 1/2 < σ) {X X' : ℝ} (hX' : 1 < X')
    (hXX : X' ≤ X) :
    ‖(∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X ρ.1.im)
      - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X' ρ.1.im‖
      ≤ (2*((σ - 1/2) + 1/Real.log X) + 2*((σ - 1/2) + 1/Real.log X'))
          * ∑' ρ : ZetaZeros K,
              (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2) := by
  have hX : 1 < X := lt_of_lt_of_le hX' hXX
  refine (norm_sub_le _ _).trans ?_
  rw [add_mul]
  gcongr
  · exact norm_tsum_zetaZeros_mul_le K hσ (fun γ => norm_zeroCosTerm_le hσ hX γ)
  · exact norm_tsum_zetaZeros_mul_le K hσ (fun γ => norm_zeroCosTerm_le hσ hX' γ)

/-- The kernel `(h + 1/t)e^{−ht}/t` is integrable on `(T, ∞)`. -/
theorem integrableOn_kernel {h T : ℝ} (hh : 0 < h) (hT : 0 < T) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (h + 1/t) * Real.exp (-h*t) / t) (Set.Ioi T) := by
  refine MeasureTheory.Integrable.mono'
    (g := fun t : ℝ => (h + 1/T) / T * Real.exp (-h*t))
    ((exp_neg_integrableOn_Ioi T hh).const_mul _) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div ?_ continuousOn_id (fun t ht => (hT.trans ht).ne')
    refine ContinuousOn.mul ?_
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    exact continuousOn_const.add (continuousOn_const.div continuousOn_id
      (fun t ht => (hT.trans ht).ne'))
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := hT.trans ht
    have hTt : T ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (h + 1/t) * Real.exp (-h*t) / t
        ≤ (h + 1/T) * Real.exp (-h*t) / T := by
          gcongr
      _ = (h + 1/T) / T * Real.exp (-h*t) := by ring

/-- **The exact kernel integral** (paper eq:diffeq consequence, lines 460–467):
`∫_T^∞ (h + 1/t)·e^{−ht}/t · dt = e^{−hT}/T` — the antiderivative is `−e^{−ht}/t`. -/
theorem integral_Ioi_kernel_eval {h T : ℝ} (hh : 0 < h) (hT : 0 < T) :
    ∫ t in Set.Ioi T, (h + 1/t) * Real.exp (-h*t) / t = Real.exp (-h*T) / T := by
  have hderiv : ∀ t ∈ Set.Ioi T, HasDerivAt (fun u : ℝ => -(Real.exp (-h*u) / u))
      ((h + 1/t) * Real.exp (-h*t) / t) t := by
    intro t ht
    have ht0 : (0:ℝ) < t := hT.trans ht
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-h*u))
        (Real.exp (-h*t) * (-h * 1)) t :=
      ((hasDerivAt_id t).const_mul (-h)).exp
    have h2 := (h1.div (hasDerivAt_id t) ht0.ne').neg
    have h3 : (h + 1/t) * Real.exp (-h*t) / t
        = -((Real.exp (-h*t) * (-h*1) * t - Real.exp (-h*t) * 1) / t^2) := by
      field_simp
      ring
    exact h3 ▸ h2
  have hint := integrableOn_kernel hh hT
  have hlim : Tendsto (fun t : ℝ => -(Real.exp (-h*t) / t)) atTop (nhds 0) := by
    rw [show (0:ℝ) = -0 by norm_num]
    exact Tendsto.neg (Tendsto.div_atTop
      (Real.tendsto_exp_atBot.comp
        (Tendsto.const_mul_atTop_of_neg (by linarith : (-h:ℝ) < 0) tendsto_id))
      tendsto_id)
  have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun u : ℝ => -(Real.exp (-h*u) / u))
    (f' := fun t : ℝ => (h + 1/t) * Real.exp (-h*t) / t)
    (by
      refine ContinuousWithinAt.neg ?_
      refine ContinuousWithinAt.div ?_ continuousWithinAt_id hT.ne'
      exact (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).continuousWithinAt)
    hderiv hint hlim
  rw [hkey]
  ring

/-- **The refined integral-piece bound**: `‖zeroIntTerm‖ ≤ 4/(T·(h²+γ²))` — the
tail integral is at most `1/T` by the exact kernel antiderivative (no opaque
constant). -/
theorem norm_zeroIntTerm_le_refined {σ : ℝ} (hσ : 1/2 < σ) {X : ℝ} (hX : 1 < X)
    (γ : ℝ) :
    ‖zeroIntTerm (σ:ℂ) X γ‖
      ≤ 4 / (Real.log X * ((σ - 1/2)^2 + γ^2)) := by
  have hh : (0:ℝ) < σ - 1/2 := by linarith
  have hT0 : 0 < Real.log X := Real.log_pos hX
  have hD : (0:ℝ) < (σ - 1/2)^2 + γ^2 := by positivity
  have hDc : ((σ:ℂ) - 1/2)^2 + (γ:ℂ)^2 = (((σ - 1/2)^2 + γ^2 : ℝ) : ℂ) := by
    push_cast
    ring
  set T : ℝ := Real.log X with hT_def
  -- the tail integral is bounded by `1/T`
  have hIle : ‖∫ t in Set.Ioi T,
      ((Real.cos (t * γ) : ℝ) : ℂ) * auxF (σ:ℂ) X t * ((((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2)‖
      ≤ 1 / T := by
    have hmajint : MeasureTheory.IntegrableOn (fun t : ℝ =>
        Real.exp ((σ - 1/2)*T) * ((σ - 1/2 + 1/t) * Real.exp (-(σ - 1/2)*t) / t))
        (Set.Ioi T) := (integrableOn_kernel hh hT0).const_mul _
    have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi T)),
        ‖((Real.cos (t * γ) : ℝ) : ℂ) * auxF (σ:ℂ) X t
          * ((((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2)‖
        ≤ Real.exp ((σ - 1/2)*T) * ((σ - 1/2 + 1/t) * Real.exp (-(σ - 1/2)*t) / t) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := hT0.trans ht
      have hTt : T ≤ t := le_of_lt ht
      have habs : |t| = t := abs_of_pos ht0
      have hauxval : auxF (σ:ℂ) X t
          = ((T/t * Real.exp (-(σ - 1/2)*(t - T)) : ℝ) : ℂ) := by
        rw [auxF_ofReal, habs,
          if_neg (by simp only [← hT_def]; exact not_le.mpr ht), ← hT_def]
      have hqval : ((((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2)
          = ((((σ - 1/2)*t + 1)/t^2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hauxval, hqval, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      have h2 : |T/t * Real.exp (-(σ - 1/2)*(t - T))|
          = T/t * Real.exp (-(σ - 1/2)*(t - T)) := abs_of_nonneg (by positivity)
      have h3 : |((σ - 1/2)*t + 1)/t^2| = ((σ - 1/2)*t + 1)/t^2 :=
        abs_of_nonneg (by positivity)
      rw [h2, h3]
      calc |Real.cos (t*γ)| * (T/t * Real.exp (-(σ - 1/2)*(t - T)))
            * (((σ - 1/2)*t + 1)/t^2)
          ≤ 1 * (T/t * Real.exp (-(σ - 1/2)*(t - T))) * (((σ - 1/2)*t + 1)/t^2) := by
            gcongr
            · exact abs_cos_le_one _
        _ = Real.exp ((σ - 1/2)*T)
              * (Real.exp (-(σ - 1/2)*t) * (((σ - 1/2)*t + 1) * (T/t^3))) := by
            rw [show -(σ - 1/2)*(t - T) = -(σ - 1/2)*t + (σ - 1/2)*T by ring,
              Real.exp_add]
            field_simp
        _ ≤ Real.exp ((σ - 1/2)*T)
              * (Real.exp (-(σ - 1/2)*t) * (((σ - 1/2)*t + 1) * (1/t^2))) := by
            have h4 : T/t^3 ≤ 1/t^2 := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith
            gcongr
        _ = Real.exp ((σ - 1/2)*T) * ((σ - 1/2 + 1/t) * Real.exp (-(σ - 1/2)*t) / t) := by
            field_simp
    refine (MeasureTheory.norm_integral_le_of_norm_le hmajint hbound).trans ?_
    rw [MeasureTheory.integral_const_mul, integral_Ioi_kernel_eval hh hT0,
      ← mul_div_assoc, ← Real.exp_add,
      show (σ - 1/2)*T + -(σ - 1/2)*T = 0 by ring, Real.exp_zero]
  -- assemble
  rw [zeroIntTerm, norm_mul, norm_div, hDc, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hD, show ‖(4:ℂ)‖ = 4 by norm_num]
  calc 4 / ((σ - 1/2)^2 + γ^2) * ‖∫ t in Set.Ioi (Real.log X),
        ((Real.cos (t * γ) : ℝ) : ℂ) * auxF (σ:ℂ) X t
          * ((((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2)‖
      ≤ 4 / ((σ - 1/2)^2 + γ^2) * (1 / Real.log X) := by
        gcongr
    _ = 4 / (Real.log X * ((σ - 1/2)^2 + γ^2)) := by
        field_simp

/-- **The integral-terms estimate**: the two-cutoff difference of the tail-integral
series is bounded by `(4/T + 4/T')·Σ_ρ m_ρ/(h²+γ_ρ²)`. -/
theorem norm_tsum_zeroIntTerm_sub_le {σ : ℝ} (hσ : 1/2 < σ) {X X' : ℝ} (hX' : 1 < X')
    (hXX : X' ≤ X) :
    ‖(∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X ρ.1.im)
      - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X' ρ.1.im‖
      ≤ (4 / Real.log X + 4 / Real.log X')
          * ∑' ρ : ZetaZeros K,
              (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2) := by
  have hX : 1 < X := lt_of_lt_of_le hX' hXX
  refine (norm_sub_le _ _).trans ?_
  rw [add_mul]
  gcongr
  · refine norm_tsum_zetaZeros_mul_le K hσ (fun γ => ?_)
    have h1 := norm_zeroIntTerm_le_refined hσ hX γ
    rwa [show (4:ℝ) / (Real.log X * ((σ - 1/2)^2 + γ^2))
      = 4 / Real.log X / ((σ - 1/2)^2 + γ^2) by rw [div_div]] at h1
  · refine norm_tsum_zetaZeros_mul_le K hσ (fun γ => ?_)
    have h1 := norm_zeroIntTerm_le_refined hσ hX' γ
    rwa [show (4:ℝ) / (Real.log X' * ((σ - 1/2)^2 + γ^2))
      = 4 / Real.log X' / ((σ - 1/2)^2 + γ^2) by rw [div_div]] at h1

/-! ### The archimedean estimate: the `β`-kernel (paper lines 476–518)

The combined `sinh + cosh` archimedean kernel is
`L(U) = log((1+e^{−U})/(1−e^{−U})) = 2 artanh(e^{−U})`; the paper's `β`-bound rests
on `e^{U/2}·L(U)` being decreasing, which follows from `L(U) ≤ 1/sinh U`
(via `log(1+x) ≤ x` and `−log(1−x) ≤ x/(1−x)`). -/

/-- The combined archimedean log-kernel `L(U) = log(1+e^{−U}) − log(1−e^{−U})`. -/
noncomputable def archKernelL (U : ℝ) : ℝ :=
  Real.log (1 + Real.exp (-U)) - Real.log (1 - Real.exp (-U))

theorem exp_neg_lt_one {U : ℝ} (hU : 0 < U) : Real.exp (-U) < 1 :=
  Real.exp_lt_one_iff.mpr (by linarith)

theorem archKernelL_pos {U : ℝ} (hU : 0 < U) : 0 < archKernelL U := by
  have he1 : Real.exp (-U) < 1 := exp_neg_lt_one hU
  have he0 : 0 < Real.exp (-U) := Real.exp_pos _
  have h1 : Real.log (1 - Real.exp (-U)) < 0 :=
    Real.log_neg (by linarith) (by linarith)
  have h2 : 0 < Real.log (1 + Real.exp (-U)) :=
    Real.log_pos (by linarith)
  rw [archKernelL]
  linarith

/-- `sinh U = (1 − x²)/(2x)` for `x = e^{−U}`. -/
theorem sinh_eq_exp_neg {U : ℝ} :
    Real.sinh U = (1 - Real.exp (-U)^2) / (2*Real.exp (-U)) := by
  have hxU : Real.exp U = (Real.exp (-U))⁻¹ := by
    rw [← Real.exp_neg, neg_neg]
  rw [Real.sinh_eq, hxU]
  have hne : Real.exp (-U) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- **(A)** `L(U) ≤ 2/sinh U` (crude log bounds suffice for the factor 2). -/
theorem archKernelL_le_two_inv_sinh {U : ℝ} (hU : 0 < U) :
    archKernelL U ≤ 2 / Real.sinh U := by
  set x : ℝ := Real.exp (-U) with hx_def
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := exp_neg_lt_one hU
  have hx2 : (0:ℝ) < 1 - x^2 := by nlinarith
  rw [sinh_eq_exp_neg, ← hx_def, div_div_eq_mul_div]
  have hlog1 : Real.log (1 + x) ≤ x := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + x)
    linarith
  have hlog2 : -Real.log (1 - x) ≤ x / (1 - x) := by
    have h1 : Real.log (1 - x) = -Real.log (1/(1-x)) := by
      rw [Real.log_div one_ne_zero (by linarith : (1:ℝ) - x ≠ 0), Real.log_one]
      ring
    rw [h1, neg_neg]
    have h2 := Real.log_le_sub_one_of_pos
      (by positivity : (0:ℝ) < 1/(1-x))
    have h3 : 1/(1-x) - 1 = x/(1-x) := by
      rw [eq_div_iff (by linarith : (1:ℝ) - x ≠ 0), sub_mul, one_mul,
        div_mul_cancel₀ _ (by linarith : (1:ℝ) - x ≠ 0)]
      ring
    linarith
  rw [archKernelL, ← hx_def]
  have hL : x + x/(1-x) = x*(2-x)/(1-x) := by
    have hne : (1:ℝ) - x ≠ 0 := by linarith
    rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
    ring
  have hxx : x + x/(1-x) ≤ 2*(2*x)/(1-x^2) := by
    rw [hL, div_le_div_iff₀ (by linarith) hx2]
    nlinarith [mul_pos hx0 (by linarith : (0:ℝ) < 1 - x), sq_nonneg x,
      mul_pos (mul_pos hx0 hx0) (by linarith : (0:ℝ) < 1 - x)]
  linarith

/-- The derivative of the weighted kernel:
`d/dU (e^{U/2}·L(U)) = e^{U/2}·(L(U)/2 − 1/sinh U)`. -/
theorem hasDerivAt_exp_half_mul_archKernelL {U : ℝ} (hU : 0 < U) :
    HasDerivAt (fun U : ℝ => Real.exp (U/2) * archKernelL U)
      (Real.exp (U/2) * (archKernelL U / 2 - 1 / Real.sinh U)) U := by
  have he0 : 0 < Real.exp (-U) := Real.exp_pos _
  have he1 : Real.exp (-U) < 1 := exp_neg_lt_one hU
  have h1 : HasDerivAt (fun U : ℝ => Real.exp (U/2)) (Real.exp (U/2) * (1/2)) U := by
    have h0 := ((hasDerivAt_id U).div_const (2:ℝ)).exp
    simpa using h0
  have hexpneg : HasDerivAt (fun U : ℝ => Real.exp (-U)) (-Real.exp (-U)) U := by
    have h0 := ((hasDerivAt_id U).neg).exp
    simpa using h0
  have h2a : HasDerivAt (fun U : ℝ => Real.log (1 + Real.exp (-U)))
      (-Real.exp (-U)/(1 + Real.exp (-U))) U := by
    have h0 := ((hasDerivAt_const U (1:ℝ)).add hexpneg).log
      (by linarith : (1:ℝ) + Real.exp (-U) ≠ 0)
    simpa using h0
  have h2b : HasDerivAt (fun U : ℝ => Real.log (1 - Real.exp (-U)))
      (Real.exp (-U)/(1 - Real.exp (-U))) U := by
    have h0 := ((hasDerivAt_const U (1:ℝ)).sub hexpneg).log
      (by linarith : (1:ℝ) - Real.exp (-U) ≠ 0)
    rw [show Real.exp (-U)/(1 - Real.exp (-U))
      = (0 - -Real.exp (-U))/(1 - Real.exp (-U)) by ring]
    exact h0
  have h2 : HasDerivAt (fun U : ℝ =>
      Real.log (1 + Real.exp (-U)) - Real.log (1 - Real.exp (-U)))
      (-Real.exp (-U)/(1 + Real.exp (-U)) - Real.exp (-U)/(1 - Real.exp (-U))) U :=
    h2a.sub h2b
  have h3 := h1.mul h2
  have hLder : -Real.exp (-U)/(1 + Real.exp (-U)) - Real.exp (-U)/(1 - Real.exp (-U))
      = -(1 / Real.sinh U) := by
    rw [sinh_eq_exp_neg]
    have hx2 : (0:ℝ) < 1 - Real.exp (-U)^2 := by nlinarith
    have hne1 : (1:ℝ) + Real.exp (-U) ≠ 0 := by linarith
    have hne2 : (1:ℝ) - Real.exp (-U) ≠ 0 := by linarith
    have hne3 : (1:ℝ) - Real.exp (-U)^2 ≠ 0 := hx2.ne'
    field_simp
    ring
  have hval : Real.exp (U/2) * (archKernelL U / 2 - 1 / Real.sinh U)
      = Real.exp (U/2) * (1/2)
        * (Real.log (1 + Real.exp (-U)) - Real.log (1 - Real.exp (-U)))
        + Real.exp (U/2)
          * (-Real.exp (-U)/(1 + Real.exp (-U)) - Real.exp (-U)/(1 - Real.exp (-U))) := by
    rw [hLder]
    unfold archKernelL
    ring
  exact hval ▸ h3

/-- **(B)** `e^{U/2}·L(U)` is antitone on `(0, ∞)`. -/
theorem antitoneOn_exp_half_mul_archKernelL :
    AntitoneOn (fun U : ℝ => Real.exp (U/2) * archKernelL U) (Set.Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
  · intro U hU
    exact ((hasDerivAt_exp_half_mul_archKernelL hU).continuousAt).continuousWithinAt
  · rw [interior_Ioi]
    intro U hU
    exact ((hasDerivAt_exp_half_mul_archKernelL hU).differentiableAt).differentiableWithinAt
  · rw [interior_Ioi]
    intro U hU
    rw [(hasDerivAt_exp_half_mul_archKernelL hU).deriv]
    have hL := archKernelL_le_two_inv_sinh hU
    have hs : 0 < Real.sinh U := Real.sinh_pos_iff.mpr hU
    have h1 : archKernelL U / 2 - 1 / Real.sinh U ≤ 0 := by
      have h2 : (0:ℝ) < 1 / Real.sinh U := by positivity
      have h3 : archKernelL U ≤ 2 * (1 / Real.sinh U) := by
        rw [show (2:ℝ) * (1 / Real.sinh U) = 2 / Real.sinh U by ring]
        exact hL
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h1

/-! ### The cutoff-derivative representation (c4-C1)

For fixed `y > 0` the map `U ↦ F_{σ,e^U}(y)` is the plateau `1` for `U ≥ y` and the
smooth tail `(U/y)e^{−h(y−U)}` for `U ≤ y` (both branches agree at `U = y`), so the
two-cutoff difference is the interval integral of the `U`-derivative
`((1+hU)/y)e^{−h(y−U)}` cut off at `U = y`. -/

/-- The real auxiliary-function family in the log-cutoff `U`: `F_{σ,e^U}(y)` for
`y > 0`. -/
noncomputable def auxFCut (σ U y : ℝ) : ℝ :=
  if y ≤ U then 1 else U/y * Real.exp (-(σ - 1/2)*(y - U))

/-- On the real ray, `auxF` at cutoff `X` is the coercion of `auxFCut σ (log X)`. -/
theorem auxF_eq_auxFCut (σ : ℝ) (X : ℝ) {y : ℝ} (hy : 0 < y) :
    auxF (σ:ℂ) X y = ((auxFCut σ (Real.log X) y : ℝ) : ℂ) := by
  rw [auxF_ofReal, auxFCut, abs_of_pos hy]

/-- The tail branch extends continuously through the kink: for `U ≤ y`,
`auxFCut σ U y = (U/y)e^{−h(y−U)}`. -/
theorem auxFCut_eq_tail {σ U y : ℝ} (hy : 0 < y) (hU : U ≤ y) :
    auxFCut σ U y = U/y * Real.exp (-(σ - 1/2)*(y - U)) := by
  rw [auxFCut]
  by_cases hcase : y ≤ U
  · have hUy : U = y := le_antisymm hU hcase
    subst hUy
    rw [if_pos le_rfl, sub_self, mul_zero, Real.exp_zero,
      div_self hy.ne', one_mul]
  · rw [if_neg hcase]

/-- The `U`-derivative of the tail branch. -/
theorem hasDerivAt_auxFCut_tail {σ y : ℝ} (U : ℝ) :
    HasDerivAt (fun U : ℝ => U/y * Real.exp (-(σ - 1/2)*(y - U)))
      ((1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U))) U := by
  have h1 : HasDerivAt (fun U : ℝ => U/y) (1/y) U := (hasDerivAt_id U).div_const y
  have h2 : HasDerivAt (fun U : ℝ => Real.exp (-(σ - 1/2)*(y - U)))
      (Real.exp (-(σ - 1/2)*(y - U)) * (σ - 1/2)) U := by
    have h3 : HasDerivAt (fun U : ℝ => -(σ - 1/2)*(y - U)) (σ - 1/2) U := by
      have h4 := ((hasDerivAt_id U).const_sub y).const_mul (-(σ - 1/2))
      simpa using h4
    simpa using h3.exp
  have h5 := h1.mul h2
  have hval : (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U))
      = 1/y * Real.exp (-(σ - 1/2)*(y - U))
        + U/y * (Real.exp (-(σ - 1/2)*(y - U)) * (σ - 1/2)) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div,
      ← add_div]
    congr 1
    ring
  exact hval ▸ h5

/-- The cutoff-difference integrand: the `U`-derivative, cut off at `U = y`. -/
noncomputable def cutKernel (σ y U : ℝ) : ℝ :=
  if U < y then (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U)) else 0

theorem cutKernel_nonneg {σ y U : ℝ} (hσ : 1/2 < σ) (hy : 0 < y) (hU : 0 ≤ U) :
    0 ≤ cutKernel σ y U := by
  rw [cutKernel]
  by_cases hcase : U < y
  · rw [if_pos hcase]
    have h1 : (0:ℝ) ≤ 1 + (σ - 1/2)*U := by nlinarith
    positivity
  · rw [if_neg hcase]

theorem measurable_cutKernel (σ y : ℝ) : Measurable (cutKernel σ y) := by
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) ?_
    measurable_const
  fun_prop

theorem intervalIntegrable_cutKernel {σ y : ℝ} (hσ : 1/2 < σ) (hy : 0 < y)
    {T' T : ℝ} (hT' : 0 < T') (hTT : T' ≤ T) :
    IntervalIntegrable (cutKernel σ y) MeasureTheory.volume T' T := by
  refine IntervalIntegrable.mono_fun'
    (g := fun _ : ℝ => (1 + (σ - 1/2)*T)/y)
    (intervalIntegrable_const) ?_ ?_
  · exact (measurable_cutKernel σ y).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun U hU => ?_)
    rw [Set.uIoc_of_le hTT] at hU
    have hU0 : 0 < U := hT'.trans hU.1
    rw [Real.norm_eq_abs, abs_of_nonneg (cutKernel_nonneg hσ hy hU0.le), cutKernel]
    by_cases hcase : U < y
    · rw [if_pos hcase]
      have he : Real.exp (-(σ - 1/2)*(y - U)) ≤ 1 := by
        have h0 : (0:ℝ) ≤ (σ - 1/2)*(y - U) :=
          mul_nonneg (by linarith) (by linarith)
        calc Real.exp (-(σ - 1/2)*(y - U)) ≤ Real.exp 0 :=
              Real.exp_le_exp.mpr (by nlinarith [h0])
          _ = 1 := Real.exp_zero
      have h1 : (0:ℝ) ≤ 1 + (σ - 1/2)*U := by nlinarith
      calc (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U))
          ≤ (1 + (σ - 1/2)*U)/y * 1 :=
            mul_le_mul_of_nonneg_left he (by positivity)
        _ ≤ (1 + (σ - 1/2)*T)/y := by
            rw [mul_one]
            have h2 : (σ - 1/2)*U ≤ (σ - 1/2)*T :=
              mul_le_mul_of_nonneg_left hU.2 (by linarith)
            gcongr
    · rw [if_neg hcase]
      have h1 : (0:ℝ) ≤ 1 + (σ - 1/2)*T := by nlinarith
      positivity

/-- **(C1) The cutoff-difference representation**: for `0 < T' ≤ T` and `y > 0`,
`F_{σ,e^T}(y) − F_{σ,e^{T'}}(y) = ∫_{T'}^T cutKernel σ y U dU`. -/
theorem auxFCut_sub_eq_integral {σ : ℝ} (hσ : 1/2 < σ) {T' T y : ℝ} (hT' : 0 < T')
    (hTT : T' ≤ T) (hy : 0 < y) :
    auxFCut σ T y - auxFCut σ T' y = ∫ U in T'..T, cutKernel σ y U := by
  have hcont : Continuous (fun U : ℝ =>
      (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U))) := by fun_prop
  by_cases hyT' : y ≤ T'
  · -- plateau at both cutoffs; the kernel vanishes on `[T', T]`
    have h1 : auxFCut σ T y = 1 := by rw [auxFCut, if_pos (le_trans hyT' hTT)]
    have h2 : auxFCut σ T' y = 1 := by rw [auxFCut, if_pos hyT']
    rw [h1, h2, sub_self,
      intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun U hU => ?_),
      intervalIntegral.integral_zero]
    rw [Set.uIcc_of_le hTT] at hU
    rw [cutKernel, if_neg (not_lt.mpr (le_trans hyT' hU.1))]
  · rw [not_le] at hyT'
    by_cases hyT : T ≤ y
    · -- tail at both cutoffs: pure FTC on `[T', T] ⊆ (0, y]`
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun U : ℝ => U/y * Real.exp (-(σ - 1/2)*(y - U)))
        (f' := fun U : ℝ => (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U)))
        (fun U _ => hasDerivAt_auxFCut_tail U)
        (hcont.intervalIntegrable T' T)
      rw [auxFCut_eq_tail hy hyT, auxFCut_eq_tail hy (le_trans hTT hyT), ← hftc]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume y] with U hUy hUIoc
      rw [Set.uIoc_of_le hTT] at hUIoc
      have hUlt : U < y := lt_of_le_of_ne (le_trans hUIoc.2 hyT) hUy
      rw [cutKernel, if_pos hUlt]
    · -- straddling case `T' < y < T`: split at `y`
      rw [not_le] at hyT
      have hint1 := intervalIntegrable_cutKernel (T' := T') (T := y) hσ hy hT'
        (le_of_lt hyT')
      have hint2 := intervalIntegrable_cutKernel (T' := y) (T := T) hσ hy hy
        (le_of_lt hyT)
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
      -- the `[y, T]` piece vanishes pointwise
      have hzero : (∫ U in y..T, cutKernel σ y U) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun U hU => ?_),
          intervalIntegral.integral_zero]
        rw [Set.uIcc_of_le (le_of_lt hyT)] at hU
        rw [cutKernel, if_neg (not_lt.mpr hU.1)]
      rw [hzero, add_zero]
      -- the `[T', y]` piece: FTC ending exactly at the kink
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun U : ℝ => U/y * Real.exp (-(σ - 1/2)*(y - U)))
        (f' := fun U : ℝ => (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U)))
        (fun U _ => hasDerivAt_auxFCut_tail U)
        (hcont.intervalIntegrable T' y)
      have hplateau : auxFCut σ T y = 1 := by
        rw [auxFCut, if_pos (le_of_lt hyT)]
      have htailT' : auxFCut σ T' y
          = T'/y * Real.exp (-(σ - 1/2)*(y - T')) :=
        auxFCut_eq_tail hy (le_of_lt hyT')
      rw [hplateau, htailT']
      rw [show (∫ U in T'..y, cutKernel σ y U)
          = ∫ U in T'..y, (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U)) from ?_,
        hftc, sub_self, mul_zero, Real.exp_zero, mul_one, div_self hy.ne']
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume y] with U hUy hUIoc
      rw [Set.uIoc_of_le (le_of_lt hyT')] at hUIoc
      have hUlt : U < y := lt_of_le_of_ne hUIoc.2 hUy
      rw [cutKernel, if_pos hUlt]


/-! ### The closed-form archimedean tail integrals (c4-C2)

`∫_U^∞ dy/(e^y−1) = −log(1−e^{−U})` and `∫_U^∞ dy/(e^y+1) = log(1+e^{−U})` — the two
halves of the `archKernelL` closed form. -/

theorem integrableOn_inv_exp_sub_one {U : ℝ} (hU : 0 < U) :
    MeasureTheory.IntegrableOn (fun y : ℝ => 1/(Real.exp y - 1)) (Set.Ioi U) := by
  have hbound : ∀ y ∈ Set.Ioi U, ‖1/(Real.exp y - 1)‖
      ≤ (1 - Real.exp (-U))⁻¹ * Real.exp (-y) := by
    intro y hy
    have hyU : U < y := hy
    have he1 : Real.exp (-U) < 1 := exp_neg_lt_one hU
    have hey : 0 < Real.exp y := Real.exp_pos _
    have hgt : 1 < Real.exp y := by
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp y := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1/(Real.exp y - 1))]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.exp y - 1)]
    have hkey : Real.exp (-y) * (Real.exp y - 1) = 1 - Real.exp (-y) := by
      rw [mul_sub, ← Real.exp_add, mul_one]
      norm_num
    calc (1:ℝ) = (1 - Real.exp (-U))⁻¹ * (1 - Real.exp (-U)) := by
          rw [inv_mul_cancel₀ (by linarith : (1:ℝ) - Real.exp (-U) ≠ 0)]
      _ ≤ (1 - Real.exp (-U))⁻¹ * (1 - Real.exp (-y)) := by
          gcongr
      _ = (1 - Real.exp (-U))⁻¹ * Real.exp (-y) * (Real.exp y - 1) := by
          rw [mul_assoc, hkey]
  refine MeasureTheory.Integrable.mono'
    ((exp_neg_integrableOn_Ioi U one_pos).const_mul ((1 - Real.exp (-U))⁻¹)) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_exp.continuousOn.sub continuousOn_const) ?_
    intro y hy
    have hgt : 1 < Real.exp y := by
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp y := Real.exp_lt_exp.mpr (by linarith [hU.trans hy])
    linarith
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
    have h1 := hbound y hy
    calc ‖1/(Real.exp y - 1)‖ ≤ (1 - Real.exp (-U))⁻¹ * Real.exp (-y) := h1
      _ = (1 - Real.exp (-U))⁻¹ * Real.exp (-1*y) := by norm_num

theorem integral_Ioi_inv_exp_sub_one {U : ℝ} (hU : 0 < U) :
    ∫ y in Set.Ioi U, 1/(Real.exp y - 1) = -Real.log (1 - Real.exp (-U)) := by
  have hderiv : ∀ y ∈ Set.Ioi U, HasDerivAt (fun y : ℝ => Real.log (1 - Real.exp (-y)))
      (1/(Real.exp y - 1)) y := by
    intro y hy
    have hyU : U < y := hy
    have hy0 : 0 < y := hU.trans hyU
    have he1 : Real.exp (-y) < 1 := exp_neg_lt_one hy0
    have hexpneg : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
      have h0 := ((hasDerivAt_id y).neg).exp
      simpa using h0
    have h1 := ((hasDerivAt_const y (1:ℝ)).sub hexpneg).log
      (by linarith : (1:ℝ) - Real.exp (-y) ≠ 0)
    have hval : (0 - -Real.exp (-y))/(1 - Real.exp (-y)) = 1/(Real.exp y - 1) := by
      rw [zero_sub, neg_neg]
      rw [div_eq_div_iff (by linarith : (1:ℝ) - Real.exp (-y) ≠ 0)
        (by
          have hgt : 1 < Real.exp y := by
            calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
              _ < Real.exp y := Real.exp_lt_exp.mpr (by linarith)
          linarith : (Real.exp y - 1) ≠ 0)]
      rw [mul_sub, ← Real.exp_add, mul_one, neg_add_cancel, Real.exp_zero, one_mul]
    exact hval ▸ h1
  have hlim : Tendsto (fun y : ℝ => Real.log (1 - Real.exp (-y))) atTop (nhds 0) := by
    rw [show (0:ℝ) = Real.log (1 - 0) by norm_num]
    refine Tendsto.log ?_ (by norm_num)
    exact tendsto_const_nhds.sub
      (Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg
        (by norm_num : (-1:ℝ) < 0) tendsto_id) |>.congr (fun y => by norm_num))
  have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun y : ℝ => Real.log (1 - Real.exp (-y)))
    (f' := fun y : ℝ => 1/(Real.exp y - 1))
    (by
      have he1 : Real.exp (-U) < 1 := exp_neg_lt_one hU
      refine ContinuousWithinAt.log ?_ (by linarith)
      exact (continuous_const.sub (Real.continuous_exp.comp
        continuous_neg)).continuousWithinAt)
    hderiv (integrableOn_inv_exp_sub_one hU) hlim
  rw [hkey]
  ring

theorem integrableOn_inv_exp_add_one {U : ℝ} (hU : 0 < U) :
    MeasureTheory.IntegrableOn (fun y : ℝ => 1/(Real.exp y + 1)) (Set.Ioi U) := by
  refine (integrableOn_inv_exp_sub_one hU).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_exp.continuousOn.add continuousOn_const) ?_
    intro y _
    positivity
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
    have hgt : 1 < Real.exp y := by
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp y := Real.exp_lt_exp.mpr (by linarith [hU.trans hy])
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1/(Real.exp y + 1))]
    have h1 : (0:ℝ) < Real.exp y - 1 := by linarith
    have h2 : Real.exp y - 1 ≤ Real.exp y + 1 := by linarith
    exact one_div_le_one_div_of_le h1 h2

theorem integral_Ioi_inv_exp_add_one {U : ℝ} (hU : 0 < U) :
    ∫ y in Set.Ioi U, 1/(Real.exp y + 1) = Real.log (1 + Real.exp (-U)) := by
  have hderiv : ∀ y ∈ Set.Ioi U, HasDerivAt (fun y : ℝ => -Real.log (1 + Real.exp (-y)))
      (1/(Real.exp y + 1)) y := by
    intro y hy
    have hy0 : 0 < y := hU.trans hy
    have he0 : 0 < Real.exp (-y) := Real.exp_pos _
    have hexpneg : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
      have h0 := ((hasDerivAt_id y).neg).exp
      simpa using h0
    have h1 := (((hasDerivAt_const y (1:ℝ)).add hexpneg).log
      (by linarith : (1:ℝ) + Real.exp (-y) ≠ 0)).neg
    have hval : -((0 + -Real.exp (-y))/(1 + Real.exp (-y))) = 1/(Real.exp y + 1) := by
      rw [zero_add]
      rw [neg_div, neg_neg]
      rw [div_eq_div_iff (by linarith : (1:ℝ) + Real.exp (-y) ≠ 0)
        (by positivity : (Real.exp y + 1) ≠ 0)]
      rw [mul_add, ← Real.exp_add, mul_one, neg_add_cancel, Real.exp_zero, one_mul]
    exact hval ▸ h1
  have hlim : Tendsto (fun y : ℝ => -Real.log (1 + Real.exp (-y))) atTop (nhds 0) := by
    rw [show (0:ℝ) = -Real.log (1 + 0) by norm_num]
    refine Tendsto.neg (Tendsto.log ?_ (by norm_num))
    exact tendsto_const_nhds.add
      (Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg
        (by norm_num : (-1:ℝ) < 0) tendsto_id) |>.congr (fun y => by norm_num))
  have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun y : ℝ => -Real.log (1 + Real.exp (-y)))
    (f' := fun y : ℝ => 1/(Real.exp y + 1))
    (by
      refine ContinuousWithinAt.neg ?_
      refine ContinuousWithinAt.log ?_ (by positivity)
      exact (continuous_const.add (Real.continuous_exp.comp
        continuous_neg)).continuousWithinAt)
    hderiv (integrableOn_inv_exp_add_one hU) hlim
  rw [hkey]
  ring


/-! ### The inner archimedean bound (c4-C2b)

For `y > U` the cut kernel is at most `(h+1/U)e^{−h(y−U)}`, the combined weights are
`1/(2sinh(y/2)) + 1/(2cosh(y/2)) = e^{y/2}(1/(e^y−1) + 1/(e^y+1))`, and for
`h ≥ 1/2` the exponentials collapse to the `h`-free `e^{U/2}`, leaving exactly the
closed-form tails of `archKernelL U`. -/

theorem two_sinh_half_eq {y : ℝ} : 2 * Real.sinh (y/2)
    = Real.exp (-(y/2)) * (Real.exp y - 1) := by
  have h1 : Real.exp (-(y/2)) * Real.exp y = Real.exp (y/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.sinh_eq, mul_sub, mul_one, h1]
  ring

theorem two_cosh_half_eq {y : ℝ} : 2 * Real.cosh (y/2)
    = Real.exp (-(y/2)) * (Real.exp y + 1) := by
  have h1 : Real.exp (-(y/2)) * Real.exp y = Real.exp (y/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.cosh_eq, mul_add, mul_one, h1]
  ring

/-- Pointwise: `(w₁+w₂)(y)·cutKernel σ y U ≤ (h+1/U)e^{U/2}·(1/(e^y−1)+1/(e^y+1))`
for `1 ≤ σ` and `0 < U < y`. -/
theorem weight_mul_cutKernel_le {σ : ℝ} (hσ1 : 1 ≤ σ) {U y : ℝ} (hU : 0 < U)
    (hyU : U < y) :
    (1/(2*Real.sinh (y/2)) + 1/(2*Real.cosh (y/2))) * cutKernel σ y U
      ≤ (σ - 1/2 + 1/U) * Real.exp (U/2)
          * (1/(Real.exp y - 1) + 1/(Real.exp y + 1)) := by
  have hh : (1:ℝ)/2 ≤ σ - 1/2 := by linarith
  have hy0 : 0 < y := hU.trans hyU
  have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
  have hc : 0 < Real.cosh (y/2) := Real.cosh_pos _
  have hey : 1 < Real.exp y := by
    calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp y := Real.exp_lt_exp.mpr hy0
  have hkernel : cutKernel σ y U
      ≤ (σ - 1/2 + 1/U) * Real.exp (-(σ - 1/2)*(y - U)) := by
    rw [cutKernel, if_pos hyU]
    have h1 : (1 + (σ - 1/2)*U)/y ≤ (1 + (σ - 1/2)*U)/U := by
      gcongr
    have h2 : (1 + (σ - 1/2)*U)/U = σ - 1/2 + 1/U := by
      field_simp
      ring
    calc (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U))
        ≤ (1 + (σ - 1/2)*U)/U * Real.exp (-(σ - 1/2)*(y - U)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = (σ - 1/2 + 1/U) * Real.exp (-(σ - 1/2)*(y - U)) := by rw [h2]
  have hwsum : 1/(2*Real.sinh (y/2)) + 1/(2*Real.cosh (y/2))
      = Real.exp (y/2) * (1/(Real.exp y - 1) + 1/(Real.exp y + 1)) := by
    rw [two_sinh_half_eq, two_cosh_half_eq, one_div, one_div, mul_inv, mul_inv,
      Real.exp_neg, inv_inv, mul_add, one_div, one_div]
  have hwpos : 0 ≤ 1/(Real.exp y - 1) + 1/(Real.exp y + 1) := by positivity
  have hexp_collapse : Real.exp (y/2) * Real.exp (-(σ - 1/2)*(y - U))
      ≤ Real.exp (U/2) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h7 : (1/2)*(y - U) ≤ (σ - 1/2)*(y - U) :=
      mul_le_mul_of_nonneg_right hh (by linarith)
    linarith
  calc (1/(2*Real.sinh (y/2)) + 1/(2*Real.cosh (y/2))) * cutKernel σ y U
      ≤ (1/(2*Real.sinh (y/2)) + 1/(2*Real.cosh (y/2)))
          * ((σ - 1/2 + 1/U) * Real.exp (-(σ - 1/2)*(y - U))) :=
        mul_le_mul_of_nonneg_left hkernel (by positivity)
    _ = (σ - 1/2 + 1/U) * (Real.exp (y/2) * Real.exp (-(σ - 1/2)*(y - U)))
          * (1/(Real.exp y - 1) + 1/(Real.exp y + 1)) := by
        rw [hwsum]
        ring
    _ ≤ (σ - 1/2 + 1/U) * Real.exp (U/2)
          * (1/(Real.exp y - 1) + 1/(Real.exp y + 1)) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp_collapse (by positivity)) hwpos

/-- **(C2b) The inner bound**: for `1 ≤ σ` and `U > 0`,
`∫_{y>U} (1/(2sinh(y/2)) + 1/(2cosh(y/2)))·cutKernel σ y U dy
  ≤ (h + 1/U)·e^{U/2}·L(U)`. -/
theorem inner_arch_bound {σ : ℝ} (hσ1 : 1 ≤ σ) {U : ℝ} (hU : 0 < U) :
    ∫ y in Set.Ioi U,
      (1/(2*Real.sinh (y/2)) + 1/(2*Real.cosh (y/2))) * cutKernel σ y U
      ≤ (σ - 1/2 + 1/U) * Real.exp (U/2) * archKernelL U := by
  have hh : (1:ℝ)/2 ≤ σ - 1/2 := by linarith
  have hh0 : (0:ℝ) < σ - 1/2 := by linarith
  have hσ2 : (1:ℝ)/2 < σ := by linarith
  have hmajint : MeasureTheory.IntegrableOn (fun y : ℝ =>
      (σ - 1/2 + 1/U) * Real.exp (U/2) * (1/(Real.exp y - 1) + 1/(Real.exp y + 1)))
      (Set.Ioi U) :=
    (((integrableOn_inv_exp_sub_one hU).add
      (integrableOn_inv_exp_add_one hU)).const_mul _)
  have hwcont : ContinuousOn (fun y : ℝ =>
      1/(2*Real.sinh (y/2)) + 1/(2*Real.cosh (y/2))) (Set.Ioi U) := by
    refine ContinuousOn.add ?_ ?_
    · refine continuousOn_const.div (by fun_prop) (fun y hy => ?_)
      have hs : 0 < Real.sinh (y/2) :=
        Real.sinh_pos_iff.mpr (by linarith [hU.trans hy])
      positivity
    · refine continuousOn_const.div (by fun_prop) (fun y _ => ?_)
      have hc : 0 < Real.cosh (y/2) := Real.cosh_pos _
      positivity
  have hmeasK : Measurable (fun y : ℝ => cutKernel σ y U) := by
    unfold cutKernel
    refine Measurable.ite (measurableSet_lt measurable_const measurable_id) ?_
      measurable_const
    fun_prop
  have hptnn : ∀ y ∈ Set.Ioi U,
      0 ≤ (1/(2*Real.sinh (y/2)) + 1/(2*Real.cosh (y/2))) * cutKernel σ y U := by
    intro y hy
    have hy0 : 0 < y := hU.trans hy
    have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
    have hc : 0 < Real.cosh (y/2) := Real.cosh_pos _
    exact mul_nonneg (by positivity) (cutKernel_nonneg hσ2 hy0 hU.le)
  have hptbound : ∀ y ∈ Set.Ioi U,
      (1/(2*Real.sinh (y/2)) + 1/(2*Real.cosh (y/2))) * cutKernel σ y U
      ≤ (σ - 1/2 + 1/U) * Real.exp (U/2)
          * (1/(Real.exp y - 1) + 1/(Real.exp y + 1)) :=
    fun y hy => weight_mul_cutKernel_le hσ1 hU hy
  have hint : MeasureTheory.IntegrableOn (fun y : ℝ =>
      (1/(2*Real.sinh (y/2)) + 1/(2*Real.cosh (y/2))) * cutKernel σ y U)
      (Set.Ioi U) := by
    refine MeasureTheory.Integrable.mono' hmajint
      ((hwcont.aestronglyMeasurable measurableSet_Ioi).mul
        hmeasK.aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (hptnn y hy)]
    exact hptbound y hy
  calc ∫ y in Set.Ioi U,
        (1/(2*Real.sinh (y/2)) + 1/(2*Real.cosh (y/2))) * cutKernel σ y U
      ≤ ∫ y in Set.Ioi U, (σ - 1/2 + 1/U) * Real.exp (U/2)
          * (1/(Real.exp y - 1) + 1/(Real.exp y + 1)) :=
        MeasureTheory.setIntegral_mono_on hint hmajint measurableSet_Ioi hptbound
    _ = (σ - 1/2 + 1/U) * Real.exp (U/2) * archKernelL U := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (integrableOn_inv_exp_sub_one hU)
            (integrableOn_inv_exp_add_one hU),
          integral_Ioi_inv_exp_sub_one hU, integral_Ioi_inv_exp_add_one hU,
          archKernelL]
        ring

/-! ### The Tonelli swap and the final archimedean estimate (c4-C2c/C3) -/

/-- The combined weight, as a global (junk-at-0) function. -/
noncomputable def archWeight (y : ℝ) : ℝ :=
  1/(2*Real.sinh (y/2)) + 1/(2*Real.cosh (y/2))

theorem measurable_archWeight : Measurable archWeight := by
  unfold archWeight
  fun_prop

theorem archWeight_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ archWeight y := by
  have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
  have hc : 0 < Real.cosh (y/2) := Real.cosh_pos _
  unfold archWeight
  positivity

/-- The weighted cut kernel is integrable on `(0, ∞)` in `y` (it vanishes on
`(0, U]` and is dominated beyond). -/
theorem integrableOn_archWeight_mul_cutKernel {σ : ℝ} (hσ1 : 1 ≤ σ) {U : ℝ}
    (hU : 0 < U) :
    MeasureTheory.IntegrableOn (fun y : ℝ => archWeight y * cutKernel σ y U)
      (Set.Ioi 0) := by
  have hh0 : (0:ℝ) < σ - 1/2 := by linarith
  have hσ2 : (1:ℝ)/2 < σ := by linarith
  -- on `(0, U]` the integrand vanishes; on `(U, ∞)` use the C2b majorant
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 U ∪ Set.Ioi U := by
    rw [Set.Ioc_union_Ioi_eq_Ioi hU.le]
  rw [hsplit]
  refine MeasureTheory.IntegrableOn.union ?_ ?_
  · refine MeasureTheory.integrableOn_zero.congr_fun (fun y hy => ?_) measurableSet_Ioc
    rw [cutKernel, if_neg (not_lt.mpr hy.2), mul_zero]
  · have hmajint : MeasureTheory.IntegrableOn (fun y : ℝ =>
        (σ - 1/2 + 1/U) * Real.exp (U/2)
          * (1/(Real.exp y - 1) + 1/(Real.exp y + 1))) (Set.Ioi U) :=
      (((integrableOn_inv_exp_sub_one hU).add
        (integrableOn_inv_exp_add_one hU)).const_mul _)
    refine MeasureTheory.Integrable.mono' hmajint
      ((measurable_archWeight.mul (by
        unfold cutKernel
        refine Measurable.ite (measurableSet_lt measurable_const measurable_id) ?_
          measurable_const
        fun_prop)).aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hU.trans hy
    have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
    have hc : 0 < Real.cosh (y/2) := Real.cosh_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (archWeight_nonneg hy0) (cutKernel_nonneg hσ2 hy0 hU.le))]
    exact weight_mul_cutKernel_le hσ1 hU hy

/-- Extending the inner integral to `(0, ∞)` costs nothing: the cut kernel vanishes
below the cutoff. -/
theorem integral_archWeight_mul_cutKernel_Ioi_zero {σ : ℝ} (hσ1 : 1 ≤ σ) {U : ℝ}
    (hU : 0 < U) :
    ∫ y in Set.Ioi 0, archWeight y * cutKernel σ y U
      = ∫ y in Set.Ioi U, archWeight y * cutKernel σ y U := by
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 U ∪ Set.Ioi U := by
    rw [Set.Ioc_union_Ioi_eq_Ioi hU.le]
  have hzero : ∀ y ∈ Set.Ioc (0:ℝ) U, archWeight y * cutKernel σ y U = 0 := by
    intro y hy
    rw [cutKernel, if_neg (not_lt.mpr hy.2), mul_zero]
  rw [hsplit, MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi
    (MeasureTheory.integrableOn_zero.congr_fun (fun y hy => (hzero y hy).symm)
      measurableSet_Ioc)
    ((integrableOn_archWeight_mul_cutKernel hσ1 hU).mono_set
      (Set.Ioi_subset_Ioi hU.le)),
    MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero hzero, zero_add]

/-- The inner bound with the packaged weight. -/
theorem inner_arch_bound' {σ : ℝ} (hσ1 : 1 ≤ σ) {U : ℝ} (hU : 0 < U) :
    ∫ y in Set.Ioi 0, archWeight y * cutKernel σ y U
      ≤ (σ - 1/2 + 1/U) * Real.exp (U/2) * archKernelL U := by
  rw [integral_archWeight_mul_cutKernel_Ioi_zero hσ1 hU]
  have h1 := inner_arch_bound hσ1 hU
  simpa [archWeight] using h1

/-- **(c4) The archimedean difference estimate**: for `1 ≤ σ`, `0 < T' ≤ T`,
`∫_{y>0} (w₁+w₂)(y)·(F_{σ,e^T}(y) − F_{σ,e^{T'}}(y)) dy
  ≤ (T−T')·(h+1/T')·e^{T'/2}·L(T')` — the paper's `β`-bound with no constant
loss. -/
theorem arch_sum_diff_le {σ : ℝ} (hσ1 : 1 ≤ σ) {T' T : ℝ} (hT' : 0 < T')
    (hTT : T' ≤ T) :
    ∫ y in Set.Ioi 0, archWeight y * (auxFCut σ T y - auxFCut σ T' y)
      ≤ (T - T') * ((σ - 1/2 + 1/T') * Real.exp (T'/2) * archKernelL T') := by
  have hσ2 : (1:ℝ)/2 < σ := by linarith
  have hc₀nn : 0 ≤ (σ - 1/2 + 1/T') * Real.exp (T'/2) * archKernelL T' := by
    have hL := archKernelL_pos hT'
    have h1 : (0:ℝ) < 1/T' := by positivity
    positivity
  have hbound_nonneg : 0 ≤ (T - T')
      * ((σ - 1/2 + 1/T') * Real.exp (T'/2) * archKernelL T') :=
    mul_nonneg (by linarith) hc₀nn
  have hFmeas : Measurable (fun y : ℝ =>
      archWeight y * (auxFCut σ T y - auxFCut σ T' y)) := by
    refine measurable_archWeight.mul (Measurable.sub ?_ ?_) <;>
    · unfold auxFCut
      refine Measurable.ite (measurableSet_le measurable_id measurable_const)
        measurable_const ?_
      fun_prop
  have hFnn : ∀ y ∈ Set.Ioi (0:ℝ),
      0 ≤ archWeight y * (auxFCut σ T y - auxFCut σ T' y) := by
    intro y hy
    refine mul_nonneg (archWeight_nonneg hy) ?_
    rw [auxFCut_sub_eq_integral hσ2 hT' hTT hy, intervalIntegral.integral_of_le hTT]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun U hU => ?_)
    exact cutKernel_nonneg hσ2 hy (le_of_lt (lt_of_lt_of_le hT' hU.1.le))
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall hFnn))
    hFmeas.aestronglyMeasurable.restrict]
  refine ENNReal.toReal_le_of_le_ofReal hbound_nonneg ?_
  have hstep1 : ∫⁻ y in Set.Ioi 0,
      ENNReal.ofReal (archWeight y * (auxFCut σ T y - auxFCut σ T' y))
      = ∫⁻ y in Set.Ioi 0, ∫⁻ U in Set.Ioc T' T,
          ENNReal.ofReal (archWeight y * cutKernel σ y U) := by
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    rw [auxFCut_sub_eq_integral hσ2 hT' hTT hy, intervalIntegral.integral_of_le hTT,
      ← MeasureTheory.integral_const_mul,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · exact (((intervalIntegrable_cutKernel hσ2 hy hT' hTT).1).const_mul _)
    · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun U hU => ?_)
      exact mul_nonneg (archWeight_nonneg hy)
        (cutKernel_nonneg hσ2 hy (le_of_lt (lt_of_lt_of_le hT' hU.1.le)))
  rw [hstep1]
  have huncurry : AEMeasurable
      (Function.uncurry fun y U => ENNReal.ofReal (archWeight y * cutKernel σ y U))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioc T' T))) := by
    refine Measurable.aemeasurable ?_
    have h1 : (Function.uncurry fun y U =>
        ENNReal.ofReal (archWeight y * cutKernel σ y U))
        = fun p : ℝ × ℝ => ENNReal.ofReal (archWeight p.1 * cutKernel σ p.1 p.2) :=
      rfl
    rw [h1]
    refine ENNReal.measurable_ofReal.comp ?_
    refine (measurable_archWeight.comp measurable_fst).mul ?_
    unfold cutKernel
    refine Measurable.ite (measurableSet_lt measurable_snd measurable_fst) ?_
      measurable_const
    fun_prop
  rw [MeasureTheory.lintegral_lintegral_swap huncurry]
  have hinner : ∀ U ∈ Set.Ioc T' T,
      (∫⁻ y in Set.Ioi 0, ENNReal.ofReal (archWeight y * cutKernel σ y U))
      ≤ ENNReal.ofReal ((σ - 1/2 + 1/T') * Real.exp (T'/2) * archKernelL T') := by
    intro U hU
    have hU0 : 0 < U := lt_of_lt_of_le hT' hU.1.le
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (integrableOn_archWeight_mul_cutKernel hσ1 hU0)
      (by
        rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
        refine Filter.Eventually.of_forall (fun y hy => ?_)
        exact mul_nonneg (archWeight_nonneg hy)
          (cutKernel_nonneg hσ2 hy hU0.le))]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (inner_arch_bound' hσ1 hU0).trans ?_
    have hmono := antitoneOn_exp_half_mul_archKernelL
      (Set.mem_Ioi.mpr hT') (Set.mem_Ioi.mpr hU0) hU.1.le
    have hfac : σ - 1/2 + 1/U ≤ σ - 1/2 + 1/T' := by
      have h1 : 1/U ≤ 1/T' := one_div_le_one_div_of_le hT' hU.1.le
      linarith
    have hULnn : 0 ≤ Real.exp (U/2) * archKernelL U :=
      mul_nonneg (Real.exp_pos _).le (archKernelL_pos hU0).le
    have hfacnn : (0:ℝ) ≤ σ - 1/2 + 1/T' := by
      have : (0:ℝ) < 1/T' := by positivity
      linarith
    calc (σ - 1/2 + 1/U) * Real.exp (U/2) * archKernelL U
        = (σ - 1/2 + 1/U) * (Real.exp (U/2) * archKernelL U) := by ring
      _ ≤ (σ - 1/2 + 1/T') * (Real.exp (T'/2) * archKernelL T') :=
          mul_le_mul hfac hmono hULnn hfacnn
      _ = (σ - 1/2 + 1/T') * Real.exp (T'/2) * archKernelL T' := by ring
  refine le_trans (MeasureTheory.lintegral_mono_ae
    ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall hinner))) ?_
  rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc,
    ← ENNReal.ofReal_mul hc₀nn]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (mul_comm _ _))


/-! ### The relative display (L4-a): `K` minus `ℚ`

Subtracting the `ℚ`-instance of the Lemma-3 display kills the field-independent
`Φ(0) + Φ(1)` (the test function is the same), `log Δ_ℚ = 0`, and shifts the
archimedean coefficients by one (`n_ℚ = r_ℚ = 1`). -/

theorem lemma4_relative_display (hGRH : GeneralizedRiemannHypothesis K)
    (hRH : RiemannHypothesis)
    {σ X : ℝ} (hσ : 1 < σ) (hX : 1 < X) {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1/4)
    (has : a < σ - 1) :
    2 * ((Real.log X * Real.exp ((σ - 1/2) * Real.log X)
        * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
          - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)) : ℝ) : ℂ)
      = ((Real.log |NumberField.discr K| : ℝ) : ℂ)
        + (((-((((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
            + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ)) - 1)
              * (Real.eulerMascheroniConstant + Real.log (8*π))
            + ((NumberField.InfinitePlace.nrRealPlaces K : ℝ) - 1) * (π/2)) : ℝ)) : ℂ)
        + ((((NumberField.InfinitePlace.nrRealPlaces K
            + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ) - 1)
            * (∫ y in Set.Ioi (0:ℝ),
              ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (1 - auxF (σ:ℂ) X y))
        + (((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ) - 1)
            * (∫ y in Set.Ioi (0:ℝ),
              ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (1 - auxF (σ:ℂ) X y))
        - 2 * ((∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
            (if (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
              then Real.log (Ideal.absNorm pk.1.1)
                * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
                * (1 - Real.log X
                    / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
                    * Real.exp (-(σ - 1/2)
                        * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1)
                          - Real.log X)))
              else 0) : ℝ) : ℂ)
        + 2 * ((∑' pk : {𝔭 : Ideal (𝓞 ℚ) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
            (if (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
              then Real.log (Ideal.absNorm pk.1.1)
                * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
                * (1 - Real.log X
                    / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
                    * Real.exp (-(σ - 1/2)
                        * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1)
                          - Real.log X)))
              else 0) : ℝ) : ℂ)
        - ((∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im)
          - ∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im)
        - ((∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X ρ.1.im)
          - ∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X ρ.1.im)
        + ((∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X ρ.1.im)
          - ∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X ρ.1.im) := by
  have hK := lemma3_display K hGRH hσ hX ha ha' has
  have hQ := lemma3_display ℚ (generalizedRiemannHypothesis_rat hRH) hσ hX ha ha' has
  rw [Rat.numberField_discr,
    NumberField.InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one
      (Module.finrank_self ℚ),
    NumberField.InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one
      (Module.finrank_self ℚ)] at hQ
  simp only [abs_one, Int.cast_one, Real.log_one, Nat.cast_one, Nat.cast_zero,
    mul_zero, add_zero, one_mul, Complex.ofReal_zero] at hQ
  push_cast at hK hQ ⊢
  linear_combination hK - hQ


/-! ### The two-cutoff difference (L4-b)

Subtracting the relative display at cutoffs `X` and `X'` kills the remaining
cutoff-free terms (`log Δ_K` and the Γ-constant), leaving only differences that the
four estimates (c1–c4) control — with no `log X` loss. -/

/-- The plateau (prime-side defect) sum, abbreviated. -/
noncomputable def plateauSum (K : Type*) [Field K] [NumberField K] (σ X : ℝ) : ℝ :=
  ∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
    (if (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
      then Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
        * (1 - Real.log X
            / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * Real.exp (-(σ - 1/2)
                * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1)
                  - Real.log X)))
      else 0)

/-- **The two-cutoff difference of the relative display** (L4-b): all cutoff-free
terms cancel. -/
theorem lemma4_diff_display (hGRH : GeneralizedRiemannHypothesis K)
    (hRH : RiemannHypothesis)
    {σ : ℝ} (hσ : 1 < σ) {X' X : ℝ} (hX' : 1 < X') (hXX : X' ≤ X)
    {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1/4) (has : a < σ - 1) :
    2 * ((Real.log X * Real.exp ((σ - 1/2) * Real.log X)
        * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
          - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)) : ℝ) : ℂ)
      - 2 * ((Real.log X' * Real.exp ((σ - 1/2) * Real.log X')
        * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
          - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)) : ℝ) : ℂ)
      = ((((NumberField.InfinitePlace.nrRealPlaces K
            + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ) - 1)
            * ((∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (1 - auxF (σ:ℂ) X y))
              - ∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (1 - auxF (σ:ℂ) X' y))
        + (((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ) - 1)
            * ((∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (1 - auxF (σ:ℂ) X y))
              - ∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (1 - auxF (σ:ℂ) X' y))
        - 2 * (((plateauSum K σ X : ℝ) : ℂ) - ((plateauSum K σ X' : ℝ) : ℂ))
        + 2 * (((plateauSum ℚ σ X : ℝ) : ℂ) - ((plateauSum ℚ σ X' : ℝ) : ℂ))
        - (((∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im)
            - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im)
          - ((∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im)
            - ∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im))
        - (((∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X ρ.1.im)
            - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X' ρ.1.im)
          - ((∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X ρ.1.im)
            - ∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X' ρ.1.im))
        + (((∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X ρ.1.im)
            - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X' ρ.1.im)
          - ((∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X ρ.1.im)
            - ∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X' ρ.1.im)) := by
  have hX : 1 < X := lt_of_lt_of_le hX' hXX
  have h1 := lemma4_relative_display K hGRH hRH hσ hX ha ha' has
  have h2 := lemma4_relative_display K hGRH hRH hσ hX' ha ha' has
  unfold plateauSum
  push_cast at h1 h2 ⊢
  linear_combination h1 - h2


/-! ### Realifying the archimedean display integrals (L4-c-i) -/

/-- The display's archimedean integrals are coercions of their real avatars. -/
theorem arch_display_integral_eq (σ X : ℝ) (w : ℝ → ℝ) :
    (∫ y in Set.Ioi (0:ℝ), ((w y : ℝ) : ℂ) * (1 - auxF (σ:ℂ) X y))
      = ((∫ y in Set.Ioi (0:ℝ), w y * (1 - auxFCut σ (Real.log X) y) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  rw [auxF_eq_auxFCut σ X hy]
  push_cast
  ring

theorem measurable_one_sub_auxFCut (σ T : ℝ) :
    Measurable (fun y : ℝ => 1 - auxFCut σ T y) := by
  refine measurable_const.sub ?_
  unfold auxFCut
  refine Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const ?_
  fun_prop

/-- `0 ≤ 1 − F_{σ,e^T}(y) ≤ 1` for `y, T > 0`, `σ > 1/2`. -/
theorem one_sub_auxFCut_mem {σ T y : ℝ} (hσ : 1/2 < σ) (hT : 0 < T) (hy : 0 < y) :
    0 ≤ 1 - auxFCut σ T y ∧ 1 - auxFCut σ T y ≤ 1 := by
  rw [auxFCut]
  by_cases hcase : y ≤ T
  · rw [if_pos hcase]
    norm_num
  · rw [if_neg hcase]
    rw [not_le] at hcase
    constructor
    · have h1 : T/y ≤ 1 := by
        rw [div_le_one hy]
        linarith
      have h2 : Real.exp (-(σ - 1/2)*(y - T)) ≤ 1 := by
        have h2a : (0:ℝ) ≤ σ - 1/2 := by linarith
        have h2b : (0:ℝ) ≤ y - T := by linarith
        have h2c : (0:ℝ) ≤ (σ - 1/2)*(y - T) := mul_nonneg h2a h2b
        calc Real.exp (-(σ - 1/2)*(y - T)) ≤ Real.exp 0 :=
              Real.exp_le_exp.mpr (by nlinarith)
          _ = 1 := Real.exp_zero
      have h3 : T/y * Real.exp (-(σ - 1/2)*(y - T)) ≤ 1 := by
        calc T/y * Real.exp (-(σ - 1/2)*(y - T)) ≤ 1 * 1 :=
              mul_le_mul h1 h2 (Real.exp_pos _).le one_pos.le
          _ = 1 := by norm_num
      linarith
    · have h4 : 0 ≤ T/y * Real.exp (-(σ - 1/2)*(y - T)) := by positivity
      linarith

/-- `2 sinh(y/2) = e^{y/2}(1 − e^{−y})`. -/
theorem two_sinh_half_eq' {y : ℝ} : 2 * Real.sinh (y/2)
    = Real.exp (y/2) * (1 - Real.exp (-y)) := by
  have h1 : Real.exp (y/2) * Real.exp (-y) = Real.exp (-(y/2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.sinh_eq, mul_sub, mul_one, h1]
  ring

/-- The sinh-weighted `(1 − F)`-integrand is integrable on `(0, ∞)`. -/
theorem integrableOn_sinh_weight_one_sub {σ T : ℝ} (hσ : 1/2 < σ) (hT : 0 < T) :
    MeasureTheory.IntegrableOn
      (fun y : ℝ => 1/(2*Real.sinh (y/2)) * (1 - auxFCut σ T y)) (Set.Ioi 0) := by
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 T ∪ Set.Ioi T := by
    rw [Set.Ioc_union_Ioi_eq_Ioi hT.le]
  rw [hsplit]
  refine MeasureTheory.IntegrableOn.union ?_ ?_
  · refine MeasureTheory.integrableOn_zero.congr_fun (fun y hy => ?_) measurableSet_Ioc
    rw [auxFCut, if_pos hy.2]
    norm_num
  · have hmaj : MeasureTheory.IntegrableOn (fun y : ℝ =>
        (1 - Real.exp (-T))⁻¹ * Real.exp (-(1/2) * y)) (Set.Ioi T) :=
      (exp_neg_integrableOn_Ioi T (by norm_num : (0:ℝ) < 1/2)).const_mul _
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · refine MeasureTheory.AEStronglyMeasurable.mul ?_
        (measurable_one_sub_auxFCut σ T).aestronglyMeasurable
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine continuousOn_const.div (by fun_prop) (fun y hy => ?_)
      have hs : 0 < Real.sinh (y/2) :=
        Real.sinh_pos_iff.mpr (by linarith [hT.trans hy])
      positivity
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
      have hyT : T < y := hy
      have hy0 : 0 < y := hT.trans hyT
      have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
      have hmem := one_sub_auxFCut_mem hσ hT hy0
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hmem.1)]
      have hpos1 : (0:ℝ) < 1 - Real.exp (-T) := by
        linarith [exp_neg_lt_one hT]
      have hwval : 1/(2*Real.sinh (y/2))
          ≤ (1 - Real.exp (-T))⁻¹ * Real.exp (-(1/2)*y) := by
        have hTy : 1 - Real.exp (-T) ≤ 1 - Real.exp (-y) := by
          have h5 : Real.exp (-y) ≤ Real.exp (-T) :=
            Real.exp_le_exp.mpr (by linarith)
          linarith
        have hexphalf : Real.exp (-(1/2)*y) = (Real.exp (y/2))⁻¹ := by
          rw [← Real.exp_neg]
          congr 1
          ring
        rw [two_sinh_half_eq', one_div, mul_inv, hexphalf,
          mul_comm ((1 - Real.exp (-T))⁻¹)]
        gcongr
      calc 1/(2*Real.sinh (y/2)) * (1 - auxFCut σ T y)
          ≤ 1/(2*Real.sinh (y/2)) * 1 :=
            mul_le_mul_of_nonneg_left hmem.2 (by positivity)
        _ = 1/(2*Real.sinh (y/2)) := mul_one _
        _ ≤ (1 - Real.exp (-T))⁻¹ * Real.exp (-(1/2)*y) := hwval

/-- The cosh-weighted `(1 − F)`-integrand is integrable on `(0, ∞)`. -/
theorem integrableOn_cosh_weight_one_sub {σ T : ℝ} (hσ : 1/2 < σ) (hT : 0 < T) :
    MeasureTheory.IntegrableOn
      (fun y : ℝ => 1/(2*Real.cosh (y/2)) * (1 - auxFCut σ T y)) (Set.Ioi 0) := by
  refine (integrableOn_sinh_weight_one_sub hσ hT).mono' ?_ ?_
  · refine MeasureTheory.AEStronglyMeasurable.mul ?_
      (measurable_one_sub_auxFCut σ T).aestronglyMeasurable
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine continuousOn_const.div (by fun_prop) (fun y _ => ?_)
    have hc : 0 < Real.cosh (y/2) := Real.cosh_pos _
    positivity
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
    have hc : 0 < Real.cosh (y/2) := Real.cosh_pos _
    have hmem := one_sub_auxFCut_mem hσ hT hy0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hmem.1)]
    have hsc : Real.sinh (y/2) < Real.cosh (y/2) := Real.sinh_lt_cosh _
    have hw12 : 1/(2*Real.cosh (y/2)) ≤ 1/(2*Real.sinh (y/2)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_right hw12 hmem.1


/-! ### The archimedean difference, realified and bounded (L4-c-ii) -/

/-- `arch_display_integral_eq` at the sinh weight. -/
theorem arch_display_sinh_eq (σ X : ℝ) :
    (∫ y in Set.Ioi (0:ℝ), ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (1 - auxF (σ:ℂ) X y))
      = ((∫ y in Set.Ioi (0:ℝ),
          1/(2 * Real.sinh (y/2)) * (1 - auxFCut σ (Real.log X) y) : ℝ) : ℂ) :=
  arch_display_integral_eq σ X _

/-- `arch_display_integral_eq` at the cosh weight. -/
theorem arch_display_cosh_eq (σ X : ℝ) :
    (∫ y in Set.Ioi (0:ℝ), ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (1 - auxF (σ:ℂ) X y))
      = ((∫ y in Set.Ioi (0:ℝ),
          1/(2 * Real.cosh (y/2)) * (1 - auxFCut σ (Real.log X) y) : ℝ) : ℂ) :=
  arch_display_integral_eq σ X _

/-- Raising the cutoff raises the test function: `F_{σ,e^{T'}} ≤ F_{σ,e^T}` pointwise. -/
theorem auxFCut_sub_nonneg {σ : ℝ} (hσ : 1/2 < σ) {T' T y : ℝ} (hT' : 0 < T')
    (hTT : T' ≤ T) (hy : 0 < y) :
    0 ≤ auxFCut σ T y - auxFCut σ T' y := by
  rw [auxFCut_sub_eq_integral hσ hT' hTT hy, intervalIntegral.integral_of_le hTT]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc
    (fun U hU => cutKernel_nonneg hσ hy (hT'.trans hU.1).le)

/-- The sinh-weighted cutoff difference is integrable on `(0, ∞)`. -/
theorem integrableOn_sinh_weight_sub {σ : ℝ} (hσ : 1/2 < σ) {T' T : ℝ} (hT' : 0 < T')
    (hT : 0 < T) :
    MeasureTheory.IntegrableOn
      (fun y : ℝ => 1/(2*Real.sinh (y/2)) * (auxFCut σ T y - auxFCut σ T' y))
      (Set.Ioi 0) :=
  ((integrableOn_sinh_weight_one_sub hσ hT').sub
    (integrableOn_sinh_weight_one_sub hσ hT)).congr_fun
    (fun y _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi

/-- The cosh-weighted cutoff difference is integrable on `(0, ∞)`. -/
theorem integrableOn_cosh_weight_sub {σ : ℝ} (hσ : 1/2 < σ) {T' T : ℝ} (hT' : 0 < T')
    (hT : 0 < T) :
    MeasureTheory.IntegrableOn
      (fun y : ℝ => 1/(2*Real.cosh (y/2)) * (auxFCut σ T y - auxFCut σ T' y))
      (Set.Ioi 0) :=
  ((integrableOn_cosh_weight_one_sub hσ hT').sub
    (integrableOn_cosh_weight_one_sub hσ hT)).congr_fun
    (fun y _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi

/-- The difference of sinh-weighted `(1−F)`-integrals is minus the cutoff-difference
integral. -/
theorem sinh_integral_diff_eq {σ : ℝ} (hσ : 1/2 < σ) {T' T : ℝ} (hT' : 0 < T')
    (hT : 0 < T) :
    (∫ y in Set.Ioi (0:ℝ), 1/(2 * Real.sinh (y/2)) * (1 - auxFCut σ T y))
      - ∫ y in Set.Ioi (0:ℝ), 1/(2 * Real.sinh (y/2)) * (1 - auxFCut σ T' y)
      = - ∫ y in Set.Ioi (0:ℝ),
          1/(2 * Real.sinh (y/2)) * (auxFCut σ T y - auxFCut σ T' y) := by
  rw [← MeasureTheory.integral_sub (integrableOn_sinh_weight_one_sub hσ hT)
    (integrableOn_sinh_weight_one_sub hσ hT'), ← MeasureTheory.integral_neg]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => by ring)

/-- The difference of cosh-weighted `(1−F)`-integrals is minus the cutoff-difference
integral. -/
theorem cosh_integral_diff_eq {σ : ℝ} (hσ : 1/2 < σ) {T' T : ℝ} (hT' : 0 < T')
    (hT : 0 < T) :
    (∫ y in Set.Ioi (0:ℝ), 1/(2 * Real.cosh (y/2)) * (1 - auxFCut σ T y))
      - ∫ y in Set.Ioi (0:ℝ), 1/(2 * Real.cosh (y/2)) * (1 - auxFCut σ T' y)
      = - ∫ y in Set.Ioi (0:ℝ),
          1/(2 * Real.cosh (y/2)) * (auxFCut σ T y - auxFCut σ T' y) := by
  rw [← MeasureTheory.integral_sub (integrableOn_cosh_weight_one_sub hσ hT)
    (integrableOn_cosh_weight_one_sub hσ hT'), ← MeasureTheory.integral_neg]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => by ring)

/-- The sinh cutoff-difference integral is nonnegative. -/
theorem integral_sinh_weight_sub_nonneg {σ : ℝ} (hσ : 1/2 < σ) {T' T : ℝ}
    (hT' : 0 < T') (hTT : T' ≤ T) :
    0 ≤ ∫ y in Set.Ioi (0:ℝ),
        1/(2 * Real.sinh (y/2)) * (auxFCut σ T y - auxFCut σ T' y) := by
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun y hy => ?_)
  have hy0 : 0 < y := hy
  have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
  exact mul_nonneg (by positivity) (auxFCut_sub_nonneg hσ hT' hTT hy0)

/-- The cosh cutoff-difference integral is nonnegative. -/
theorem integral_cosh_weight_sub_nonneg {σ : ℝ} (hσ : 1/2 < σ) {T' T : ℝ}
    (hT' : 0 < T') (hTT : T' ≤ T) :
    0 ≤ ∫ y in Set.Ioi (0:ℝ),
        1/(2 * Real.cosh (y/2)) * (auxFCut σ T y - auxFCut σ T' y) := by
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun y hy => ?_)
  have hy0 : 0 < y := hy
  have hc : 0 < Real.cosh (y/2) := Real.cosh_pos _
  exact mul_nonneg (by positivity) (auxFCut_sub_nonneg hσ hT' hTT hy0)

/-- The combined-weight cutoff-difference integral splits into its sinh and cosh
parts. -/
theorem integral_archWeight_sub_split {σ : ℝ} (hσ : 1/2 < σ) {T' T : ℝ}
    (hT' : 0 < T') (hT : 0 < T) :
    ∫ y in Set.Ioi (0:ℝ), archWeight y * (auxFCut σ T y - auxFCut σ T' y)
      = (∫ y in Set.Ioi (0:ℝ),
          1/(2 * Real.sinh (y/2)) * (auxFCut σ T y - auxFCut σ T' y))
        + ∫ y in Set.Ioi (0:ℝ),
          1/(2 * Real.cosh (y/2)) * (auxFCut σ T y - auxFCut σ T' y) := by
  rw [← MeasureTheory.integral_add (integrableOn_sinh_weight_sub hσ hT' hT)
    (integrableOn_cosh_weight_sub hσ hT' hT)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  unfold archWeight
  ring

/-- **The place-count combination bound**: for `n = r₁ + 2r₂ ≥ 2` and `D₁, D₂ ≥ 0`,
`|(n−1)·D₁ + (r₁−1)·D₂| ≤ (n−1)·(D₁+D₂)` — the paper's `|r_K − r_k| ≤ n_K − n_k`
step (B–F lines 497–501) at `k = ℚ`. -/
theorem abs_place_combination_le (hn : 1 < Module.finrank ℚ K) {D₁ D₂ : ℝ}
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) :
    |((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
        + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ) - 1) * D₁
      + ((NumberField.InfinitePlace.nrRealPlaces K : ℝ) - 1) * D₂|
      ≤ ((Module.finrank ℚ K : ℝ) - 1) * (D₁ + D₂) := by
  have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcardR : (NumberField.InfinitePlace.nrRealPlaces K : ℝ)
      + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ)
      = (Module.finrank ℚ K : ℝ) := by
    rw [← hcard]
    push_cast
    ring
  have hnR : (1:ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast hn
  have hn2R : (2:ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    have : (2:ℕ) ≤ Module.finrank ℚ K := hn
    exact_mod_cast this
  have hr2nn : (0:ℝ) ≤ (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) :=
    Nat.cast_nonneg _
  have hr1nn : (0:ℝ) ≤ (NumberField.InfinitePlace.nrRealPlaces K : ℝ) :=
    Nat.cast_nonneg _
  have habs1 : |(NumberField.InfinitePlace.nrRealPlaces K : ℝ)
      + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ) - 1|
      = (Module.finrank ℚ K : ℝ) - 1 := by
    rw [abs_of_nonneg (by linarith), hcardR]
  have habs2 : |(NumberField.InfinitePlace.nrRealPlaces K : ℝ) - 1|
      ≤ (Module.finrank ℚ K : ℝ) - 1 := by
    rw [abs_le]
    constructor <;> linarith
  calc |((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
        + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ) - 1) * D₁
      + ((NumberField.InfinitePlace.nrRealPlaces K : ℝ) - 1) * D₂|
      ≤ |((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
          + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ) - 1) * D₁|
        + |((NumberField.InfinitePlace.nrRealPlaces K : ℝ) - 1) * D₂| := abs_add_le _ _
    _ = |(NumberField.InfinitePlace.nrRealPlaces K : ℝ)
          + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ) - 1| * D₁
        + |(NumberField.InfinitePlace.nrRealPlaces K : ℝ) - 1| * D₂ := by
        rw [abs_mul, abs_mul, abs_of_nonneg hD₁, abs_of_nonneg hD₂]
    _ ≤ ((Module.finrank ℚ K : ℝ) - 1) * D₁
        + ((Module.finrank ℚ K : ℝ) - 1) * D₂ := by
        rw [habs1]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right habs2 hD₂)
    _ = ((Module.finrank ℚ K : ℝ) - 1) * (D₁ + D₂) := by ring

/-- Triangle inequality for the display's arch + zero-side combination. -/
theorem norm_arch_zero_comb_le {A SK SQ CK CQ IK IQ : ℂ} {b sk sq ck cq ik iq : ℝ}
    (hA : ‖A‖ ≤ b) (hSK : ‖SK‖ ≤ sk) (hSQ : ‖SQ‖ ≤ sq) (hCK : ‖CK‖ ≤ ck)
    (hCQ : ‖CQ‖ ≤ cq) (hIK : ‖IK‖ ≤ ik) (hIQ : ‖IQ‖ ≤ iq) :
    ‖A - (SK - SQ) - (CK - CQ) + (IK - IQ)‖
      ≤ b + (sk + sq) + (ck + cq) + (ik + iq) := by
  calc ‖A - (SK - SQ) - (CK - CQ) + (IK - IQ)‖
      ≤ ‖A - (SK - SQ) - (CK - CQ)‖ + ‖IK - IQ‖ := norm_add_le _ _
    _ ≤ (‖A - (SK - SQ)‖ + ‖CK - CQ‖) + ‖IK - IQ‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖A‖ + ‖SK - SQ‖) + ‖CK - CQ‖) + ‖IK - IQ‖ :=
        add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ ((b + (‖SK‖ + ‖SQ‖)) + (‖CK‖ + ‖CQ‖)) + (‖IK‖ + ‖IQ‖) :=
        add_le_add (add_le_add (add_le_add hA (norm_sub_le _ _)) (norm_sub_le _ _))
          (norm_sub_le _ _)
    _ ≤ ((b + (sk + sq)) + (ck + cq)) + (ik + iq) :=
        add_le_add (add_le_add (add_le_add le_rfl (add_le_add hSK hSQ))
          (add_le_add hCK hCQ)) (add_le_add hIK hIQ)
    _ = b + (sk + sq) + (ck + cq) + (ik + iq) := by ring

/-- The per-`σ` zero sum `Σ_ρ m_ρ/(h² + γ_ρ²)` (`h = σ − 1/2`) appearing in every
zero-side estimate; under GRH and `σ → 1⁺` it converges to the paper's
`Σ_ρ 1/(¼ + γ_ρ²)`. -/
noncomputable def zeroSumSigma (K : Type*) [Field K] [NumberField K] (σ : ℝ) : ℝ :=
  ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)

/-- **The σ-tracked Explicit2 estimate (L4-c)** — the quantitative core of B–F
Lemma 4 (`Mostways`, eq. Explicit2) at real `σ > 1`, `k = ℚ`, cutoffs
`X' ≤ X`: moving the plateau sums to the left, the two-cutoff difference of the
relative display is bounded by the archimedean term
`(n−1)(T−T')(h+1/T')e^{T'/2}L(T')` plus the coefficient
`2h²(T−T') + 2(h+1/T) + 2(h+1/T') + 4/T + 4/T'` times the two fields' zero sums
(`T = log X`, `T' = log X'`, `h = σ−1/2`). `σ → 1⁺` (L4-d) turns this into the
paper's `Explicit2` with `c_{a,T}`. -/
theorem lemma4_sigma_estimate (hGRH : GeneralizedRiemannHypothesis K)
    (hRH : RiemannHypothesis) (hn : 1 < Module.finrank ℚ K)
    {σ : ℝ} (hσ : 1 < σ) {X' X : ℝ} (hX' : 1 < X') (hXX : X' ≤ X)
    {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1/4) (has : a < σ - 1) :
    |2 * (Real.log X * Real.exp ((σ - 1/2) * Real.log X)
          * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
            - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)))
      - 2 * (Real.log X' * Real.exp ((σ - 1/2) * Real.log X')
          * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
            - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)))
      + 2 * (plateauSum K σ X - plateauSum K σ X')
      - 2 * (plateauSum ℚ σ X - plateauSum ℚ σ X')|
      ≤ ((Module.finrank ℚ K : ℝ) - 1)
          * ((Real.log X - Real.log X')
            * ((σ - 1/2 + 1/Real.log X') * Real.exp (Real.log X'/2)
              * archKernelL (Real.log X')))
        + (2*(σ - 1/2)^2 * (Real.log X - Real.log X')
            + (2*((σ - 1/2) + 1/Real.log X) + 2*((σ - 1/2) + 1/Real.log X'))
            + (4 / Real.log X + 4 / Real.log X'))
          * (zeroSumSigma K σ + zeroSumSigma ℚ σ) := by
  have hX : 1 < X := lt_of_lt_of_le hX' hXX
  have hT : 0 < Real.log X := Real.log_pos hX
  have hT' : 0 < Real.log X' := Real.log_pos hX'
  have hTT : Real.log X' ≤ Real.log X := Real.log_le_log (by linarith) hXX
  have hσ2 : (1:ℝ)/2 < σ := by linarith
  -- the difference display with realified archimedean integrals
  have hd := lemma4_diff_display K hGRH hRH hσ hX' hXX ha ha' has
  rw [arch_display_sinh_eq σ X, arch_display_sinh_eq σ X',
    arch_display_cosh_eq σ X, arch_display_cosh_eq σ X'] at hd
  push_cast at hd
  -- the key identity: the real left side is the real arch part plus the zero sums
  have key : ((2 * (Real.log X * Real.exp ((σ - 1/2) * Real.log X)
          * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
            - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)))
        - 2 * (Real.log X' * Real.exp ((σ - 1/2) * Real.log X')
          * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
            - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)))
        + 2 * (plateauSum K σ X - plateauSum K σ X')
        - 2 * (plateauSum ℚ σ X - plateauSum ℚ σ X') : ℝ) : ℂ)
      = ((((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
            + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ) - 1)
            * ((∫ y in Set.Ioi (0:ℝ),
                1/(2 * Real.sinh (y/2)) * (1 - auxFCut σ (Real.log X) y))
              - ∫ y in Set.Ioi (0:ℝ),
                1/(2 * Real.sinh (y/2)) * (1 - auxFCut σ (Real.log X') y))
          + ((NumberField.InfinitePlace.nrRealPlaces K : ℝ) - 1)
            * ((∫ y in Set.Ioi (0:ℝ),
                1/(2 * Real.cosh (y/2)) * (1 - auxFCut σ (Real.log X) y))
              - ∫ y in Set.Ioi (0:ℝ),
                1/(2 * Real.cosh (y/2)) * (1 - auxFCut σ (Real.log X') y)) : ℝ) : ℂ)
        - (((∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im)
            - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im)
          - ((∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im)
            - ∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im))
        - (((∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X ρ.1.im)
            - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X' ρ.1.im)
          - ((∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X ρ.1.im)
            - ∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X' ρ.1.im))
        + (((∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X ρ.1.im)
            - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X' ρ.1.im)
          - ((∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X ρ.1.im)
            - ∑' ρ : ZetaZeros ℚ, (zetaZeroDivisor ℚ ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X' ρ.1.im)) := by
    push_cast
    linear_combination hd
  -- the archimedean bound
  have hDs := integral_sinh_weight_sub_nonneg hσ2 hT' hTT
  have hDc := integral_cosh_weight_sub_nonneg hσ2 hT' hTT
  have hsd := sinh_integral_diff_eq hσ2 hT' hT
  have hcd := cosh_integral_diff_eq hσ2 hT' hT
  have habsneg : ∀ c d e f : ℝ, |c * -d + e * -f| = |c * d + e * f| := fun c d e f => by
    rw [show c * -d + e * -f = -(c * d + e * f) by ring, abs_neg]
  have hnR : (1:ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast hn
  have harch : ‖((((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
        + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ) - 1)
        * ((∫ y in Set.Ioi (0:ℝ),
            1/(2 * Real.sinh (y/2)) * (1 - auxFCut σ (Real.log X) y))
          - ∫ y in Set.Ioi (0:ℝ),
            1/(2 * Real.sinh (y/2)) * (1 - auxFCut σ (Real.log X') y))
      + ((NumberField.InfinitePlace.nrRealPlaces K : ℝ) - 1)
        * ((∫ y in Set.Ioi (0:ℝ),
            1/(2 * Real.cosh (y/2)) * (1 - auxFCut σ (Real.log X) y))
          - ∫ y in Set.Ioi (0:ℝ),
            1/(2 * Real.cosh (y/2)) * (1 - auxFCut σ (Real.log X') y)) : ℝ) : ℂ)‖
      ≤ ((Module.finrank ℚ K : ℝ) - 1)
          * ((Real.log X - Real.log X')
            * ((σ - 1/2 + 1/Real.log X') * Real.exp (Real.log X'/2)
              * archKernelL (Real.log X'))) := by
    rw [Complex.norm_real, Real.norm_eq_abs, hsd, hcd, habsneg]
    refine (abs_place_combination_le K hn hDs hDc).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [← integral_archWeight_sub_split hσ2 hT' hT]
    exact arch_sum_diff_le hσ.le hT' hTT
  -- the zero-sum bounds (c1–c3) at `K` and at `ℚ`
  have hc1K := norm_tsum_zeroSinTerm_sub_le K hσ2 hX' hXX
  have hc1Q := norm_tsum_zeroSinTerm_sub_le ℚ hσ2 hX' hXX
  have hc2K := norm_tsum_zeroCosTerm_sub_le K hσ2 hX' hXX
  have hc2Q := norm_tsum_zeroCosTerm_sub_le ℚ hσ2 hX' hXX
  have hc3K := norm_tsum_zeroIntTerm_sub_le K hσ2 hX' hXX
  have hc3Q := norm_tsum_zeroIntTerm_sub_le ℚ hσ2 hX' hXX
  -- assemble
  calc |2 * (Real.log X * Real.exp ((σ - 1/2) * Real.log X)
          * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
            - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)))
      - 2 * (Real.log X' * Real.exp ((σ - 1/2) * Real.log X')
          * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
            - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)))
      + 2 * (plateauSum K σ X - plateauSum K σ X')
      - 2 * (plateauSum ℚ σ X - plateauSum ℚ σ X')|
      = ‖((2 * (Real.log X * Real.exp ((σ - 1/2) * Real.log X)
          * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
            - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)))
        - 2 * (Real.log X' * Real.exp ((σ - 1/2) * Real.log X')
          * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
            - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)))
        + 2 * (plateauSum K σ X - plateauSum K σ X')
        - 2 * (plateauSum ℚ σ X - plateauSum ℚ σ X') : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ((Module.finrank ℚ K : ℝ) - 1)
          * ((Real.log X - Real.log X')
            * ((σ - 1/2 + 1/Real.log X') * Real.exp (Real.log X'/2)
              * archKernelL (Real.log X')))
        + (2*(σ - 1/2)^2 * (Real.log X - Real.log X')
              * ∑' ρ : ZetaZeros K,
                  (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)
            + 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
              * ∑' ρ : ZetaZeros ℚ,
                  (zetaZeroDivisor ℚ ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2))
        + ((2*((σ - 1/2) + 1/Real.log X) + 2*((σ - 1/2) + 1/Real.log X'))
              * ∑' ρ : ZetaZeros K,
                  (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)
            + (2*((σ - 1/2) + 1/Real.log X) + 2*((σ - 1/2) + 1/Real.log X'))
              * ∑' ρ : ZetaZeros ℚ,
                  (zetaZeroDivisor ℚ ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2))
        + ((4 / Real.log X + 4 / Real.log X')
              * ∑' ρ : ZetaZeros K,
                  (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)
            + (4 / Real.log X + 4 / Real.log X')
              * ∑' ρ : ZetaZeros ℚ,
                  (zetaZeroDivisor ℚ ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by
        rw [key]
        exact norm_arch_zero_comb_le harch hc1K hc1Q hc2K hc2Q hc3K hc3Q
    _ = ((Module.finrank ℚ K : ℝ) - 1)
          * ((Real.log X - Real.log X')
            * ((σ - 1/2 + 1/Real.log X') * Real.exp (Real.log X'/2)
              * archKernelL (Real.log X')))
        + (2*(σ - 1/2)^2 * (Real.log X - Real.log X')
            + (2*((σ - 1/2) + 1/Real.log X) + 2*((σ - 1/2) + 1/Real.log X'))
            + (4 / Real.log X + 4 / Real.log X'))
          * (zeroSumSigma K σ + zeroSumSigma ℚ σ) := by
        unfold zeroSumSigma
        ring


/-! ### The `σ → 1⁺` limit (L4-d): Explicit2 at the residue

Every quantity in `lemma4_sigma_estimate` is continuous in `σ` at `1` — except the
log-ratio, whose limit is `log κ_K − log κ_ℚ` (the divergences of `log ζ_K` and
`log ζ_ℚ` cancel), and the zero sums, which we bound by their `σ = 1` values
(termwise antitone in `σ`). Taking `σ → 1⁺` in the inequality yields the paper's
`Explicit2` (in our ×2 normalisation) with `h = 1/2` pinned. -/

theorem zeroSumSigma_nonneg (σ : ℝ) : 0 ≤ zeroSumSigma K σ :=
  tsum_nonneg fun ρ => div_nonneg
    (by exact_mod_cast zetaZeroDivisor_nonneg K ρ.1) (by positivity)

/-- The zero sum is antitone in `σ` past the critical line: each term
`m_ρ/((σ−1/2)² + γ²)` decreases as `σ` grows. -/
theorem zeroSumSigma_anti {σ' σ : ℝ} (hσ' : 1/2 < σ') (hσσ : σ' ≤ σ) :
    zeroSumSigma K σ ≤ zeroSumSigma K σ' := by
  refine Summable.tsum_le_tsum (fun ρ => ?_)
    (summable_zetaZeros_inv_sq K (σ - 1/2) (by linarith))
    (summable_zetaZeros_inv_sq K (σ' - 1/2) (by linarith))
  have hm : (0:ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
    exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
  have hB : (0:ℝ) < (σ' - 1/2)^2 + ρ.1.im^2 :=
    add_pos_of_pos_of_nonneg (pow_pos (by linarith) 2) (sq_nonneg _)
  have hA : (0:ℝ) < (σ - 1/2)^2 + ρ.1.im^2 :=
    add_pos_of_pos_of_nonneg (pow_pos (by linarith) 2) (sq_nonneg _)
  rw [div_le_div_iff₀ hA hB]
  have hsq : (σ' - 1/2)^2 ≤ (σ - 1/2)^2 := by nlinarith
  nlinarith

/-- The plateau sum is the finite sum over the plateau support. -/
theorem plateauSum_eq_sum {X : ℝ} (hX : 1 < X) (σ : ℝ) :
    plateauSum K σ X = ∑ pk ∈ (finite_plateau_support K hX).toFinset,
      (if (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
        then Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
          * (1 - Real.log X
              / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
              * Real.exp (-(σ - 1/2)
                  * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1)
                    - Real.log X)))
        else 0) := by
  unfold plateauSum
  refine tsum_eq_sum (fun pk hpk => ?_)
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hpk
  exact if_neg hpk

set_option maxHeartbeats 800000 in
/-- The plateau sum is continuous in `σ` (its support is finite and
`σ`-independent, and each term is an exponential in `σ`). -/
theorem tendsto_plateauSum {X : ℝ} (hX : 1 < X) :
    Filter.Tendsto (fun σ : ℝ => plateauSum K σ X) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (plateauSum K 1 X)) := by
  have hs : Filter.Tendsto (fun σ : ℝ =>
      ∑ pk ∈ (finite_plateau_support K hX).toFinset,
        (if (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
          then Real.log (Ideal.absNorm pk.1.1)
            * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
            * (1 - Real.log X
                / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
                * Real.exp (-(σ - 1/2)
                    * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1)
                      - Real.log X)))
          else 0)) (nhds 1)
      (nhds (∑ pk ∈ (finite_plateau_support K hX).toFinset,
        (if (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
          then Real.log (Ideal.absNorm pk.1.1)
            * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
            * (1 - Real.log X
                / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
                * Real.exp (-((1:ℝ) - 1/2)
                    * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1)
                      - Real.log X)))
          else 0))) := by
    refine tendsto_finsetSum _ (fun pk _ => ?_)
    by_cases hc : (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
    · simp only [if_pos hc]
      exact Continuous.tendsto (by fun_prop) 1
    · simp only [if_neg hc]
      exact tendsto_const_nhds
  refine Filter.Tendsto.congr (fun σ => (plateauSum_eq_sum K hX σ).symm) ?_
  rw [plateauSum_eq_sum K hX 1]
  exact hs.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))

/-- The real-part class number formula: `(σ−1)·ζ_K(σ).re → κ_K` as `σ → 1⁺`. -/
theorem tendsto_sub_one_mul_dedekindZeta_re :
    Filter.Tendsto (fun σ : ℝ => (σ - 1) * (NumberField.dedekindZeta K (σ:ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (NumberField.dedekindZeta_residue K)) := by
  have h1 := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have h2 := (Complex.continuous_re.tendsto _).comp h1
  have h3 : Filter.Tendsto
      (Complex.re ∘ fun s : ℝ => ((s : ℂ) - 1) * NumberField.dedekindZeta K (s:ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (NumberField.dedekindZeta_residue K)) := by
    simpa using h2
  refine h3.congr (fun σ => ?_)
  simp only [Function.comp_apply]
  rw [show ((σ:ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-- `log((σ−1)·ζ_K(σ).re) → log κ_K` as `σ → 1⁺`. -/
theorem tendsto_log_sub_one_mul_dedekindZeta :
    Filter.Tendsto (fun σ : ℝ =>
        Real.log ((σ - 1) * (NumberField.dedekindZeta K (σ:ℂ)).re))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (Real.log (NumberField.dedekindZeta_residue K))) :=
  ((Real.continuousAt_log
    (NumberField.dedekindZeta_residue_pos K).ne').tendsto).comp
    (tendsto_sub_one_mul_dedekindZeta_re K)

/-- **The relative log-residue limit**: as `σ → 1⁺`,
`log ζ_K(σ) − log ζ_ℚ(σ) → log κ_K − log κ_ℚ` — the individual divergences cancel
against the shared `log(σ−1)`. -/
theorem tendsto_log_dedekindZeta_ratio :
    Filter.Tendsto (fun σ : ℝ => Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
        - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (Real.log (NumberField.dedekindZeta_residue K)
        - Real.log (NumberField.dedekindZeta_residue ℚ))) := by
  refine ((tendsto_log_sub_one_mul_dedekindZeta K).sub
    (tendsto_log_sub_one_mul_dedekindZeta ℚ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have h1 : (1:ℝ) < σ := hσ
  rw [Real.log_mul (by linarith) (dedekindZeta_ofReal_re_pos K h1).ne',
    Real.log_mul (by linarith) (dedekindZeta_ofReal_re_pos ℚ h1).ne']
  ring

/-- The cutoff weight `T·e^{(σ−1/2)T}` tends to `T·√X` (`T = log X`). -/
theorem tendsto_cutoff_weight {X : ℝ} (hX : 1 < X) :
    Filter.Tendsto (fun σ : ℝ => Real.log X * Real.exp ((σ - 1/2) * Real.log X))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log X * Real.sqrt X)) := by
  have hc : Continuous fun σ : ℝ => Real.log X * Real.exp ((σ - 1/2) * Real.log X) := by
    fun_prop
  have h1 : Filter.Tendsto (fun σ : ℝ => Real.log X * Real.exp ((σ - 1/2) * Real.log X))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (Real.log X * Real.exp (((1:ℝ) - 1/2) * Real.log X))) :=
    (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  convert h1 using 2
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith : (0:ℝ) < X)]
  congr 1
  ring

/-- **The Explicit2 inequality at the residue (L4-d)** — B–F Lemma 4 (`Mostways`,
eq. Explicit2) at `k = ℚ` in our ×2 normalisation, `h = 1/2` pinned by `σ → 1⁺`:
for cutoffs `1 < X' ≤ X` (`T = log X`, `T' = log X'`),
`|2(T√X − T'√X')·log(κ_K/κ_ℚ) + 2ΔP_K − 2ΔP_ℚ|` is at most
`(n−1)(T−T')(1/2+1/T')e^{T'/2}L(T') + [2·(1/2)²(T−T') + 2(1/2+1/T) + 2(1/2+1/T')
+ 4/T + 4/T']·(Σ_K + Σ_ℚ)` with `Σ = Σ_ρ m_ρ/(1/4+γ_ρ²)`. Dividing by 2 recovers
the paper's `a/4 + 1 + 3/T + 3/T' ≤ c_{a,T}` and `a·e^{−T'/2}β(T')`. -/
theorem lemma4_explicit2 (hGRH : GeneralizedRiemannHypothesis K)
    (hRH : RiemannHypothesis) (hn : 1 < Module.finrank ℚ K)
    {X' X : ℝ} (hX' : 1 < X') (hXX : X' ≤ X) :
    |2 * (Real.log X * Real.sqrt X
          * (Real.log (NumberField.dedekindZeta_residue K)
            - Real.log (NumberField.dedekindZeta_residue ℚ)))
      - 2 * (Real.log X' * Real.sqrt X'
          * (Real.log (NumberField.dedekindZeta_residue K)
            - Real.log (NumberField.dedekindZeta_residue ℚ)))
      + 2 * (plateauSum K 1 X - plateauSum K 1 X')
      - 2 * (plateauSum ℚ 1 X - plateauSum ℚ 1 X')|
      ≤ ((Module.finrank ℚ K : ℝ) - 1)
          * ((Real.log X - Real.log X')
            * ((1/2 + 1/Real.log X') * Real.exp (Real.log X'/2)
              * archKernelL (Real.log X')))
        + (2*(1/2:ℝ)^2 * (Real.log X - Real.log X')
            + (2*((1/2:ℝ) + 1/Real.log X) + 2*((1/2:ℝ) + 1/Real.log X'))
            + (4 / Real.log X + 4 / Real.log X'))
          * (zeroSumSigma K 1 + zeroSumSigma ℚ 1) := by
  have hX : 1 < X := lt_of_lt_of_le hX' hXX
  have hT : 0 < Real.log X := Real.log_pos hX
  have hT' : 0 < Real.log X' := Real.log_pos hX'
  have hTT : Real.log X' ≤ Real.log X := Real.log_le_log (by linarith) hXX
  -- the left side converges
  have hL := tendsto_log_dedekindZeta_ratio K
  have hwX := tendsto_cutoff_weight hX
  have hwX' := tendsto_cutoff_weight hX'
  have hPKX := tendsto_plateauSum K hX
  have hPKX' := tendsto_plateauSum K hX'
  have hPQX := tendsto_plateauSum ℚ hX
  have hPQX' := tendsto_plateauSum ℚ hX'
  have hf : Filter.Tendsto (fun σ : ℝ =>
      |2 * (Real.log X * Real.exp ((σ - 1/2) * Real.log X)
          * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
            - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)))
        - 2 * (Real.log X' * Real.exp ((σ - 1/2) * Real.log X')
          * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
            - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)))
        + 2 * (plateauSum K σ X - plateauSum K σ X')
        - 2 * (plateauSum ℚ σ X - plateauSum ℚ σ X')|)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (|2 * (Real.log X * Real.sqrt X
          * (Real.log (NumberField.dedekindZeta_residue K)
            - Real.log (NumberField.dedekindZeta_residue ℚ)))
        - 2 * (Real.log X' * Real.sqrt X'
          * (Real.log (NumberField.dedekindZeta_residue K)
            - Real.log (NumberField.dedekindZeta_residue ℚ)))
        + 2 * (plateauSum K 1 X - plateauSum K 1 X')
        - 2 * (plateauSum ℚ 1 X - plateauSum ℚ 1 X')|)) := by
    refine Filter.Tendsto.abs ?_
    exact ((((tendsto_const_nhds.mul (hwX.mul hL)).sub
      (tendsto_const_nhds.mul (hwX'.mul hL))).add
      (tendsto_const_nhds.mul (hPKX.sub hPKX'))).sub
      (tendsto_const_nhds.mul (hPQX.sub hPQX')))
  -- the right side converges
  have hg : Filter.Tendsto (fun σ : ℝ =>
      ((Module.finrank ℚ K : ℝ) - 1)
          * ((Real.log X - Real.log X')
            * ((σ - 1/2 + 1/Real.log X') * Real.exp (Real.log X'/2)
              * archKernelL (Real.log X')))
        + (2*(σ - 1/2)^2 * (Real.log X - Real.log X')
            + (2*((σ - 1/2) + 1/Real.log X) + 2*((σ - 1/2) + 1/Real.log X'))
            + (4 / Real.log X + 4 / Real.log X'))
          * (zeroSumSigma K 1 + zeroSumSigma ℚ 1))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (((Module.finrank ℚ K : ℝ) - 1)
          * ((Real.log X - Real.log X')
            * ((1/2 + 1/Real.log X') * Real.exp (Real.log X'/2)
              * archKernelL (Real.log X')))
        + (2*(1/2:ℝ)^2 * (Real.log X - Real.log X')
            + (2*((1/2:ℝ) + 1/Real.log X) + 2*((1/2:ℝ) + 1/Real.log X'))
            + (4 / Real.log X + 4 / Real.log X'))
          * (zeroSumSigma K 1 + zeroSumSigma ℚ 1))) := by
    have hc : Continuous (fun σ : ℝ =>
        ((Module.finrank ℚ K : ℝ) - 1)
            * ((Real.log X - Real.log X')
              * ((σ - 1/2 + 1/Real.log X') * Real.exp (Real.log X'/2)
                * archKernelL (Real.log X')))
          + (2*(σ - 1/2)^2 * (Real.log X - Real.log X')
              + (2*((σ - 1/2) + 1/Real.log X) + 2*((σ - 1/2) + 1/Real.log X'))
              + (4 / Real.log X + 4 / Real.log X'))
            * (zeroSumSigma K 1 + zeroSumSigma ℚ 1)) := by fun_prop
    have h1 := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    convert h1 using 2
    norm_num
  -- the σ-estimate, relaxed to the σ = 1 zero sums, holds on `(1, ∞)`
  have hle : ∀ᶠ σ in nhdsWithin 1 (Set.Ioi 1),
      |2 * (Real.log X * Real.exp ((σ - 1/2) * Real.log X)
          * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
            - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)))
        - 2 * (Real.log X' * Real.exp ((σ - 1/2) * Real.log X')
          * (Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re)
            - Real.log ((NumberField.dedekindZeta ℚ (σ:ℂ)).re)))
        + 2 * (plateauSum K σ X - plateauSum K σ X')
        - 2 * (plateauSum ℚ σ X - plateauSum ℚ σ X')|
      ≤ ((Module.finrank ℚ K : ℝ) - 1)
          * ((Real.log X - Real.log X')
            * ((σ - 1/2 + 1/Real.log X') * Real.exp (Real.log X'/2)
              * archKernelL (Real.log X')))
        + (2*(σ - 1/2)^2 * (Real.log X - Real.log X')
            + (2*((σ - 1/2) + 1/Real.log X) + 2*((σ - 1/2) + 1/Real.log X'))
            + (4 / Real.log X + 4 / Real.log X'))
          * (zeroSumSigma K 1 + zeroSumSigma ℚ 1) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : (1:ℝ) < σ := hσ
    -- instantiate the phantom `a`
    have hest := lemma4_sigma_estimate K hGRH hRH hn hσ1 hX' hXX
      (a := min (1/4) ((σ - 1)/2))
      (lt_min (by norm_num) (by linarith))
      (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (by linarith))
    refine hest.trans (add_le_add le_rfl ?_)
    -- relax the zero sums to σ = 1
    have hcoeff : (0:ℝ) ≤ 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
        + (2*((σ - 1/2) + 1/Real.log X) + 2*((σ - 1/2) + 1/Real.log X'))
        + (4 / Real.log X + 4 / Real.log X') := by
      have h1 : (0:ℝ) ≤ 2*(σ - 1/2)^2 * (Real.log X - Real.log X') :=
        mul_nonneg (by positivity) (by linarith)
      have h2 : (0:ℝ) < 1/Real.log X := by positivity
      have h3 : (0:ℝ) < 1/Real.log X' := by positivity
      have h4 : (0:ℝ) < 4/Real.log X := by positivity
      have h5 : (0:ℝ) < 4/Real.log X' := by positivity
      linarith
    refine mul_le_mul_of_nonneg_left ?_ hcoeff
    exact add_le_add (zeroSumSigma_anti K (by norm_num) hσ1.le)
      (zeroSumSigma_anti ℚ (by norm_num) hσ1.le)
  exact le_of_tendsto_of_tendsto hf hg hle


end DedekindResidue

end
