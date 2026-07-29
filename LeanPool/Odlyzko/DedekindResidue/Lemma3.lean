/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
/-
DedekindResidue: Belabas–Friedman Lemma 3 — the explicit formula at `F_{s,X}` as an
absolutely convergent sum over the critical-line zeros.

Under GRH the window sums of `weil_explicit_formula_auxF` converge (b5,
`tendsto_finsum_window_zetaZeros`) to the absolutely summable series
`∑'_ρ m_ρ · Φ_{F_{s,X}}(ρ)` over the full zero index: absolute convergence comes from
the quadratic Fourier decay `‖F̂_{s,X}(γ)‖ = O(1/γ²)` (Lemma 2's closed form) glued to
the band bound on `|γ| ≤ γ₀`, against the Landau-type summability
`∑_ρ m_ρ/(1+γ_ρ²) < ∞`. Uniqueness of limits then upgrades the explicit formula from
a limit statement along good heights to the honest `∑'` identity — the shape of
Belabas–Friedman's Lemma 3 (eq. (13)) sums.
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.ExplicitFormula.WeilAssembly
public import LeanPool.Odlyzko.DedekindResidue.ExplicitFormula.GRHZeros

@[expose] public section

namespace DedekindResidue

open Complex NumberField Filter Real

variable (K : Type*) [Field K] [NumberField K]

/-- **Absolute convergence of the zero side at the auxiliary function** (`Re s > 1`):
under GRH every zero is `ρ = 1/2 + iγ_ρ`, where `Φ_{F_{s,X}}(ρ) = F̂_{s,X}(γ_ρ)` decays
like `1/γ_ρ²` (Lemma 2), so the divisor-weighted series over the zero index converges
absolutely by the Landau-type bound `∑_ρ m_ρ/(1+γ_ρ²) < ∞`. -/
theorem summable_zetaZeros_paperPhi_auxF (hGRH : GeneralizedRiemannHypothesis K)
    (s : ℂ) {X : ℝ} (hX : 1 < X) (hs : 1 < s.re) :
    Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (auxF s X) ρ.1) := by
  have hs2 : 1/2 < s.re := by linarith
  obtain ⟨C, γ₀, hC, hγ₀, hφ⟩ := exists_norm_fourier_auxF_le s hX hs2
  set a : ℝ := (s.re - 1)/2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have has : a < s.re - 1 := by rw [ha_def]; linarith
  obtain ⟨M, hM0, hMb⟩ := exists_band_bound_paperPhi_auxF s hX ha has
  set C' : ℝ := max (2*C) (M*(1+γ₀^2)) with hC'_def
  have hbound : ∀ ρ : ZetaZeros K,
      ‖(zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (auxF s X) ρ.1‖
        ≤ C' * ((zetaZeroDivisor K ρ.1 : ℝ) / (1^2 + ρ.1.im^2)) := by
    intro ρ
    have hre := ZetaZeros_re_eq_half K hGRH ρ
    set γ : ℝ := ρ.1.im with hγ_def
    have hρ_eq : ρ.1 = ((1/2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I := by
      apply Complex.ext
      · simpa using hre
      · simp [hγ_def]
    have hden : (0:ℝ) < 1 + γ^2 := by positivity
    -- the uniform bound `‖Φ(1/2+iγ)‖ ≤ C'/(1+γ²)`
    have hΦbound : ‖paperPhi (auxF s X) ρ.1‖ ≤ C' / (1 + γ^2) := by
      by_cases hcase : γ₀ ≤ |γ|
      · -- tail regime: the quadratic Fourier decay
        have h12 : ((1/2 : ℝ) : ℂ) = (1/2 : ℂ) := by norm_num
        have hval : paperPhi (auxF s X) ρ.1 = paperFourierIntegral (auxF s X) γ := by
          rw [hρ_eq, h12, paperPhi_half_add_mul_I]
        rw [hval]
        refine (hφ γ hcase).trans ?_
        have hγ1 : (1:ℝ) ≤ |γ| := le_trans hγ₀ hcase
        have hγsq : (1:ℝ) ≤ γ^2 := by
          have := sq_abs γ
          nlinarith
        have h1 : C/γ^2 ≤ 2*C/(1+γ^2) := by
          rw [div_le_div_iff₀ (by positivity) hden]
          nlinarith
        refine h1.trans ?_
        gcongr
        exact le_max_left _ _
      · -- compact regime: the band bound at `σ = 1/2`
        have hcase' : |γ| < γ₀ := not_le.mp hcase
        have hb := hMb (1/2) γ (by linarith) (by linarith)
        rw [← hρ_eq] at hb
        refine hb.trans ?_
        have h1 : M / max |γ| 1 ≤ M := by
          refine div_le_self hM0 (le_max_right _ _)
        refine h1.trans ?_
        have hγsq : γ^2 ≤ γ₀^2 := by
          have h2 : |γ| ≤ γ₀ := le_of_lt hcase'
          have := sq_abs γ
          nlinarith [abs_nonneg γ]
        rw [le_div_iff₀ hden]
        have hMC : M * (1+γ₀^2) ≤ C' := le_max_right _ _
        nlinarith
    -- assemble the product bound
    have hdnn : (0:ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
      exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
    rw [norm_mul]
    have hnormd : ‖((zetaZeroDivisor K ρ.1 : ℤ) : ℂ)‖ = (zetaZeroDivisor K ρ.1 : ℝ) := by
      rw [Complex.norm_intCast, abs_of_nonneg]
      exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
    rw [hnormd]
    calc (zetaZeroDivisor K ρ.1 : ℝ) * ‖paperPhi (auxF s X) ρ.1‖
        ≤ (zetaZeroDivisor K ρ.1 : ℝ) * (C' / (1 + γ^2)) :=
          mul_le_mul_of_nonneg_left hΦbound hdnn
      _ = C' * ((zetaZeroDivisor K ρ.1 : ℝ) / (1^2 + γ^2)) := by
          rw [one_pow]
          ring
  have hmaj : Summable (fun ρ : ZetaZeros K =>
      C' * ((zetaZeroDivisor K ρ.1 : ℝ) / (1^2 + ρ.1.im^2))) :=
    (summable_zetaZeros_inv_sq K 1 one_pos).mul_left C'
  exact Summable.of_norm_bounded hmaj hbound

/-- **The explicit formula as an absolutely convergent zero sum** (the b6 bridge to
Belabas–Friedman Lemma 3): under GRH, for `1 < X` and `0 < a ≤ 1/4` with
`a < Re s − 1`, the divisor-weighted sum of `Φ_{F_{s,X}}` over the full zero index
equals Poitou's right-hand side of the explicit formula at `F_{s,X}`. This removes
the `T → ∞` limit from `weil_explicit_formula_auxF` (uniqueness of limits against
`tendsto_finsum_window_zetaZeros`). -/
theorem tsum_zetaZeros_paperPhi_auxF_eq (hGRH : GeneralizedRiemannHypothesis K)
    (s : ℂ) {X : ℝ} (hX : 1 < X) {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1/4)
    (has : a < s.re - 1) :
    ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (auxF s X) ρ.1
      = (paperPhi (auxF s X) 0 + paperPhi (auxF s X) 1)
          + ((Real.log |NumberField.discr K| : ℝ) : ℂ) * auxF s X 0
          + (((-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
              + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
                * (Real.eulerMascheroniConstant + Real.log (8*π))
              + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)) : ℝ)) : ℂ)
              * auxF s X 0
          + (((NumberField.InfinitePlace.nrRealPlaces K
              + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ)
              * (∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (auxF s X 0 - auxF s X y))
          + ((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ)
              * (∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (auxF s X 0 - auxF s X y))
          - (primeSideH K a (auxF s X) 0 + primeSideH K a (auxF s X) 0) := by
  have hs : 1 < s.re := by linarith
  obtain ⟨T, hTtop, hTlim⟩ := weil_explicit_formula_auxF K s hX ha ha' has
  exact tendsto_nhds_unique
    (tendsto_finsum_window_zetaZeros K hGRH
      (summable_zetaZeros_paperPhi_auxF K hGRH s hX hs) ha hTtop)
    hTlim

/-! ### The three pieces of the Fourier closed form (Lemma 2, eq. (8))

`F̂_{s,X}(γ)` splits into a sine piece, a cosine piece and a tail-integral piece; the
sine piece carries the removable singularity at `γ = 0` (plateau value `2·log X`),
matching the `γ = 0` companion `fourier_auxF_zero`. These are the three zero-sums of
Belabas–Friedman's Lemma 3 display (eq. (13)). -/

/-- The sine piece `2h²·sin(Tγ)/((h²+γ²)γ)` of eq. (8), with its plateau value `2T`
at `γ = 0` (`h := s − 1/2`, `T := log X`). -/
noncomputable def zeroSinTerm (s : ℂ) (X : ℝ) (γ : ℝ) : ℂ :=
  if γ = 0 then 2 * (Real.log X : ℂ)
  else 2 * (s - 1/2)^2 / (((s - 1/2)^2 + (γ:ℂ)^2) * γ)
    * ((Real.sin (Real.log X * γ) : ℝ) : ℂ)

/-- The cosine piece `2(h + 1/T)·cos(Tγ)/(h²+γ²)` of eq. (8). -/
noncomputable def zeroCosTerm (s : ℂ) (X : ℝ) (γ : ℝ) : ℂ :=
  2 * ((s - 1/2) + 1/(Real.log X : ℂ)) / ((s - 1/2)^2 + (γ:ℂ)^2)
    * ((Real.cos (Real.log X * γ) : ℝ) : ℂ)

/-- The tail-integral piece `4/(h²+γ²)·∫_T^∞ cos(tγ)·F_{s,X}(t)·(ht+1)/t² dt` of
eq. (8). -/
noncomputable def zeroIntTerm (s : ℂ) (X : ℝ) (γ : ℝ) : ℂ :=
  4 / ((s - 1/2)^2 + (γ:ℂ)^2)
    * ∫ t in Set.Ioi (Real.log X),
        ((Real.cos (t * γ) : ℝ) : ℂ) * auxF s X t * (((s - 1/2)*t + 1)/t^2)

/-- **The three-piece split of the Fourier transform of the auxiliary function**:
Lemma 2's closed form (eq. (8)) and its `γ = 0` companion, packaged as one total
identity `F̂_{s,X}(γ) = sin-piece + cos-piece − integral-piece`. -/
theorem paperFourierIntegral_auxF_split (s : ℂ) {X : ℝ} (hX : 1 < X)
    (hs : 1/2 < s.re) (γ : ℝ) :
    paperFourierIntegral (auxF s X) γ
      = zeroSinTerm s X γ + zeroCosTerm s X γ - zeroIntTerm s X γ := by
  by_cases hγ : γ = 0
  · subst hγ
    rw [fourier_auxF_zero s hX hs, zeroSinTerm, zeroCosTerm, zeroIntTerm, if_pos rfl]
    have h2 : ((Real.cos (Real.log X * 0) : ℝ) : ℂ) = 1 := by
      rw [mul_zero, Real.cos_zero, Complex.ofReal_one]
    have h3 : (∫ t in Set.Ioi (Real.log X),
        ((Real.cos (t * 0) : ℝ) : ℂ) * auxF s X t * (((s - 1/2)*t + 1)/t^2))
        = ∫ t in Set.Ioi (Real.log X), auxF s X t * (((s - 1/2)*t + 1)/t^2) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      dsimp only
      rw [mul_zero, Real.cos_zero, Complex.ofReal_one, one_mul]
    rw [h2, h3]
    push_cast
    ring
  · rw [fourier_auxF s hX hs hγ, zeroSinTerm, if_neg hγ, zeroCosTerm, zeroIntTerm]

/-- The eq-(8) tail integrand is integrable on `(T, ∞)`: on the tail `F_{s,X}` is the
exponential kernel `T·e^{hT}·e^{−ht}/t`, and the cofactor `cos(tγ)·(ht+1)/t²` is
continuous and bounded there. -/
theorem integrableOn_auxF_tail_kernel (s : ℂ) {X : ℝ} (hX : 1 < X) (hs : 1/2 < s.re)
    (γ : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
        ((Real.cos (t * γ) : ℝ) : ℂ) * auxF s X t * (((s - 1/2)*t + 1)/t^2))
      (Set.Ioi (Real.log X)) := by
  have hT0 : 0 < Real.log X := Real.log_pos hX
  have hh : 0 < (s - 1/2 : ℂ).re := by
    have h1 : (s - 1/2 : ℂ).re = s.re - 1/2 := by
      simp [Complex.sub_re]
    rw [h1]
    linarith
  set T : ℝ := Real.log X with hT_def
  set cT : ℂ := (T : ℂ) * Complex.exp ((s - 1/2) * (T:ℂ)) with hcT_def
  have hbdd : ∀ t ∈ Set.Ioi T, ‖((Real.cos (t * γ) : ℝ) : ℂ) * cT
      * (((s - 1/2)*t + 1)/(t:ℂ)^2)‖ ≤ ‖cT‖ * (‖(s - 1/2 : ℂ)‖/T + 1/T^2) := by
    intro t ht
    have htpos : 0 < t := hT0.trans ht
    have hTt : T ≤ t := le_of_lt ht
    rw [norm_mul, norm_mul]
    have hc : ‖((Real.cos (t*γ) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_cos_le_one _
    have hq : ‖(((s - 1/2)*t + 1)/(t:ℂ)^2 : ℂ)‖ ≤ ‖(s - 1/2 : ℂ)‖/T + 1/T^2 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
      have hnum : ‖((s - 1/2)*(t:ℂ) + 1 : ℂ)‖ ≤ ‖(s - 1/2 : ℂ)‖ * t + 1 := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, norm_one]
      refine (div_le_div_of_nonneg_right hnum (by positivity)).trans ?_
      rw [div_le_iff₀ (by positivity : (0:ℝ) < t^2), add_mul]
      have hhn : (0:ℝ) ≤ ‖(s - 1/2 : ℂ)‖ := norm_nonneg _
      have e1 : ‖(s - 1/2 : ℂ)‖ * t ≤ ‖(s - 1/2 : ℂ)‖/T * t^2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hT0]
        have := mul_le_mul_of_nonneg_left hTt (mul_nonneg hhn htpos.le)
        nlinarith
      have e2 : (1:ℝ) ≤ 1/T^2 * t^2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < T^2)]
        nlinarith
      linarith
    calc ‖((Real.cos (t*γ) : ℝ) : ℂ)‖ * ‖cT‖ * ‖(((s - 1/2)*t + 1)/(t:ℂ)^2 : ℂ)‖
        ≤ 1 * ‖cT‖ * (‖(s - 1/2 : ℂ)‖/T + 1/T^2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hq
            (norm_nonneg _) (by positivity)
      _ = ‖cT‖ * (‖(s - 1/2 : ℂ)‖/T + 1/T^2) := by ring
  refine ((integrableOn_bounded_mul_exp_div hh hT0
      (φ := fun t : ℝ => ((Real.cos (t * γ) : ℝ) : ℂ) * cT * (((s - 1/2)*t + 1)/(t:ℂ)^2))
      ?_ hbdd)).congr_fun (fun t ht => ?_) measurableSet_Ioi
  · refine ContinuousOn.mul (ContinuousOn.mul ?_ continuousOn_const) ?_
    · exact (Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (continuous_id.mul continuous_const))).continuousOn
    · refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
      intro t ht
      have htpos : (0:ℝ) < t := hT0.trans ht
      exact_mod_cast pow_ne_zero 2 (by exact_mod_cast htpos.ne' : (t:ℂ) ≠ 0)
  · rw [auxF_tail_form s hX t ht]
    ring

/-! ### Norm bounds at real `σ` and summability of the three zero-series -/

/-- Generic summability wrapper: any test function with a `c/(h²+γ²)` bound
(`h := σ − 1/2 > 0`) is divisor-summable over the zero index (Landau). -/
theorem summable_zetaZeros_mul_of_norm_le {σ : ℝ} (hσ : 1/2 < σ) {f : ℝ → ℂ} {c : ℝ}
    (hf : ∀ γ : ℝ, ‖f γ‖ ≤ c / ((σ - 1/2)^2 + γ^2)) :
    Summable (fun ρ : ZetaZeros K => (zetaZeroDivisor K ρ.1 : ℂ) * f ρ.1.im) := by
  have hh : (0:ℝ) < σ - 1/2 := by linarith
  refine Summable.of_norm_bounded
    ((summable_zetaZeros_inv_sq K (σ - 1/2) hh).mul_left c) (fun ρ => ?_)
  rw [norm_mul]
  have hdnn : (0:ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
    exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
  have hnormd : ‖((zetaZeroDivisor K ρ.1 : ℤ) : ℂ)‖ = (zetaZeroDivisor K ρ.1 : ℝ) := by
    rw [Complex.norm_intCast, abs_of_nonneg]
    exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
  rw [hnormd]
  calc (zetaZeroDivisor K ρ.1 : ℝ) * ‖f ρ.1.im‖
      ≤ (zetaZeroDivisor K ρ.1 : ℝ) * (c / ((σ - 1/2)^2 + ρ.1.im^2)) :=
        mul_le_mul_of_nonneg_left (hf _) hdnn
    _ = c * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by ring

/-- **Sine-piece bound**: `‖zeroSinTerm‖ ≤ 2h²T/(h²+γ²)` — `|sin(Tγ)| ≤ T|γ|` kills
the `1/γ`, uniformly through the plateau at `γ = 0`. -/
theorem norm_zeroSinTerm_le {σ : ℝ} (hσ : 1/2 < σ) {X : ℝ} (hX : 1 < X) (γ : ℝ) :
    ‖zeroSinTerm (σ:ℂ) X γ‖
      ≤ 2*(σ - 1/2)^2 * Real.log X / ((σ - 1/2)^2 + γ^2) := by
  have hh : (0:ℝ) < σ - 1/2 := by linarith
  have hh2 : (0:ℝ) < (σ - 1/2)^2 := pow_pos hh 2
  have hT0 : 0 < Real.log X := Real.log_pos hX
  by_cases hγ : γ = 0
  · subst hγ
    rw [zeroSinTerm, if_pos rfl]
    have h1 : (2 * (Real.log X : ℂ)) = ((2*Real.log X : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h2 : 2*(σ - 1/2)^2 * Real.log X / ((σ - 1/2)^2 + 0^2) = 2*Real.log X := by
      rw [show (0:ℝ)^2 = 0 by norm_num, add_zero,
        show 2*(σ - 1/2)^2*Real.log X = 2*Real.log X * (σ - 1/2)^2 by ring,
        mul_div_assoc, div_self hh2.ne', mul_one]
    rw [h2]
  · have h1 : zeroSinTerm (σ:ℂ) X γ
        = ((2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*γ)
            * Real.sin (Real.log X * γ) : ℝ) : ℂ) := by
      rw [zeroSinTerm, if_neg hγ]
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    have hD : (0:ℝ) < (σ - 1/2)^2 + γ^2 := by positivity
    have habs : |2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*γ) * Real.sin (Real.log X * γ)|
        = 2*(σ - 1/2)^2 * |Real.sin (Real.log X * γ)|
          / (((σ - 1/2)^2 + γ^2) * |γ|) := by
      rw [abs_mul, abs_div, abs_mul, abs_mul, abs_two, abs_of_pos hh2, abs_of_pos hD]
      ring
    have hsin : |Real.sin (Real.log X * γ)| ≤ Real.log X * |γ| := by
      have h2 := Real.abs_sin_le_abs (x := Real.log X * γ)
      rwa [abs_mul, abs_of_pos hT0] at h2
    have hγ' : |γ| ≠ 0 := abs_ne_zero.mpr hγ
    have hγpos : (0:ℝ) < |γ| := abs_pos.mpr hγ
    rw [habs]
    calc 2*(σ - 1/2)^2 * |Real.sin (Real.log X * γ)| / (((σ - 1/2)^2 + γ^2) * |γ|)
        ≤ 2*(σ - 1/2)^2 * (Real.log X * |γ|) / (((σ - 1/2)^2 + γ^2) * |γ|) := by
          gcongr
      _ = 2*(σ - 1/2)^2 * Real.log X / ((σ - 1/2)^2 + γ^2) := by
          rw [show 2*(σ - 1/2)^2 * (Real.log X * |γ|)
              = 2*(σ - 1/2)^2 * Real.log X * |γ| by ring,
            mul_div_mul_right _ _ hγ']

/-- **Cosine-piece bound**: `‖zeroCosTerm‖ ≤ 2(h + 1/T)/(h²+γ²)`. -/
theorem norm_zeroCosTerm_le {σ : ℝ} (hσ : 1/2 < σ) {X : ℝ} (hX : 1 < X) (γ : ℝ) :
    ‖zeroCosTerm (σ:ℂ) X γ‖
      ≤ 2*((σ - 1/2) + 1/Real.log X) / ((σ - 1/2)^2 + γ^2) := by
  have hh : (0:ℝ) < σ - 1/2 := by linarith
  have hT0 : 0 < Real.log X := Real.log_pos hX
  have hD : (0:ℝ) < (σ - 1/2)^2 + γ^2 := by positivity
  have h1 : zeroCosTerm (σ:ℂ) X γ
      = ((2*((σ - 1/2) + 1/Real.log X) / ((σ - 1/2)^2 + γ^2)
          * Real.cos (Real.log X * γ) : ℝ) : ℂ) := by
    rw [zeroCosTerm]
    push_cast
    ring
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_pos (by positivity : (0:ℝ) < 2*((σ - 1/2) + 1/Real.log X)),
    abs_of_pos hD]
  calc 2*((σ - 1/2) + 1/Real.log X) / ((σ - 1/2)^2 + γ^2) * |Real.cos (Real.log X * γ)|
      ≤ 2*((σ - 1/2) + 1/Real.log X) / ((σ - 1/2)^2 + γ^2) * 1 := by
        gcongr
        exact abs_cos_le_one _
    _ = 2*((σ - 1/2) + 1/Real.log X) / ((σ - 1/2)^2 + γ^2) := mul_one _

/-- The uniform (γ-free) majorant of the tail integral: the integrated norm of the
`γ = 0` integrand. -/
noncomputable def auxFTailNormBound (σ X : ℝ) : ℝ :=
  ∫ t in Set.Ioi (Real.log X), ‖auxF (σ:ℂ) X t * ((((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2)‖

/-- **Integral-piece bound**: `‖zeroIntTerm‖ ≤ 4·M₀/(h²+γ²)` with the γ-free tail
constant `M₀ = ∫‖F_{s,X}·(ht+1)/t²‖`. -/
theorem norm_zeroIntTerm_le {σ : ℝ} (hσ : 1/2 < σ) {X : ℝ} (hX : 1 < X) (γ : ℝ) :
    ‖zeroIntTerm (σ:ℂ) X γ‖
      ≤ 4 * auxFTailNormBound σ X / ((σ - 1/2)^2 + γ^2) := by
  have hh : (0:ℝ) < σ - 1/2 := by linarith
  have hs2 : 1/2 < ((σ:ℂ)).re := by rw [Complex.ofReal_re]; linarith
  have hD : (0:ℝ) < (σ - 1/2)^2 + γ^2 := by positivity
  have hDc : ((σ:ℂ) - 1/2)^2 + (γ:ℂ)^2 = (((σ - 1/2)^2 + γ^2 : ℝ) : ℂ) := by
    push_cast
    ring
  -- integrability of the γ = 0 majorant
  have hint0 : MeasureTheory.IntegrableOn (fun t : ℝ =>
      auxF (σ:ℂ) X t * ((((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2)) (Set.Ioi (Real.log X)) := by
    refine (integrableOn_auxF_tail_kernel (σ:ℂ) hX hs2 0).congr_fun (fun t ht => ?_)
      measurableSet_Ioi
    dsimp only
    rw [mul_zero, Real.cos_zero, Complex.ofReal_one, one_mul]
  rw [zeroIntTerm, norm_mul, norm_div, hDc, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hD]
  have h4 : ‖(4:ℂ)‖ = 4 := by norm_num
  rw [h4]
  have hIle : ‖∫ t in Set.Ioi (Real.log X),
      ((Real.cos (t * γ) : ℝ) : ℂ) * auxF (σ:ℂ) X t * ((((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2)‖
      ≤ auxFTailNormBound σ X := by
    rw [auxFTailNormBound]
    refine MeasureTheory.norm_integral_le_of_norm_le hint0.norm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t _
    rw [norm_mul, norm_mul, norm_mul]
    have hc : ‖((Real.cos (t*γ) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_cos_le_one _
    calc ‖((Real.cos (t*γ) : ℝ) : ℂ)‖ * ‖auxF (σ:ℂ) X t‖ * ‖(((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2‖
        ≤ 1 * ‖auxF (σ:ℂ) X t‖ * ‖(((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2‖ := by
          gcongr
      _ = ‖auxF (σ:ℂ) X t‖ * ‖(((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2‖ := by ring
  calc 4 / ((σ - 1/2)^2 + γ^2) * ‖∫ t in Set.Ioi (Real.log X),
        ((Real.cos (t * γ) : ℝ) : ℂ) * auxF (σ:ℂ) X t * ((((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2)‖
      ≤ 4 / ((σ - 1/2)^2 + γ^2) * auxFTailNormBound σ X := by
        gcongr
    _ = 4 * auxFTailNormBound σ X / ((σ - 1/2)^2 + γ^2) := by ring

/-- **The three-series split of the zero side** (the Lemma 3 display's zero sums):
under GRH at real `σ > 1`, the absolutely convergent zero sum of the explicit formula
splits into the sine, cosine and tail-integral series, each absolutely convergent. -/
theorem tsum_zetaZeros_paperPhi_auxF_split (hGRH : GeneralizedRiemannHypothesis K)
    {σ X : ℝ} (hσ : 1 < σ) (hX : 1 < X) :
    ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (auxF (σ:ℂ) X) ρ.1
      = (∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im)
        + (∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X ρ.1.im)
        - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X ρ.1.im := by
  have hσ2 : (1:ℝ)/2 < σ := by linarith
  have hs2 : 1/2 < ((σ:ℂ)).re := by rw [Complex.ofReal_re]; linarith
  have hsin : Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im) :=
    summable_zetaZeros_mul_of_norm_le K hσ2 (fun γ => norm_zeroSinTerm_le hσ2 hX γ)
  have hcos : Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X ρ.1.im) :=
    summable_zetaZeros_mul_of_norm_le K hσ2 (fun γ => norm_zeroCosTerm_le hσ2 hX γ)
  have hint : Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X ρ.1.im) :=
    summable_zetaZeros_mul_of_norm_le K hσ2 (fun γ => norm_zeroIntTerm_le hσ2 hX γ)
  have hpoint : ∀ ρ : ZetaZeros K,
      (zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (auxF (σ:ℂ) X) ρ.1
        = ((zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im
            + (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X ρ.1.im)
          - (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X ρ.1.im := by
    intro ρ
    have hre := ZetaZeros_re_eq_half K hGRH ρ
    have hρ_eq : ρ.1 = ((1/2 : ℝ) : ℂ) + (ρ.1.im : ℂ) * Complex.I := by
      apply Complex.ext
      · simpa using hre
      · simp
    have h12 : ((1/2 : ℝ) : ℂ) = (1/2 : ℂ) := by norm_num
    rw [show paperPhi (auxF (σ:ℂ) X) ρ.1 = paperFourierIntegral (auxF (σ:ℂ) X) ρ.1.im by
      conv_lhs => rw [hρ_eq, h12]
      rw [paperPhi_half_add_mul_I],
      paperFourierIntegral_auxF_split (σ:ℂ) hX hs2 ρ.1.im]
    ring
  rw [tsum_congr hpoint, Summable.tsum_sub (hsin.add hcos) hint,
    Summable.tsum_add hsin hcos]

/-! ### The prime side at the origin: plateau defect + `T·e^{hT}·log ζ_K(σ)`

Belabas–Friedman's Lemma 3 bookkeeping (proof of eq. (13)): since
`f_{σ,X}(t) = g_σ(t)/g_σ(T)` with `g_σ(t) = e^{−ht}/t`, the pure-kernel prime sum
collapses to `(1/g_σ(T))·log ζ_K(σ) = T·e^{hT}·log ζ_K(σ)` by the logarithmic Euler
product, and `H(0)` differs from it by the finitely-supported plateau defect
`∑_{N𝔭^m ≤ X} (log N𝔭/N𝔭^{m/2})·(1 − f_{σ,X}(m log N𝔭))`. -/

/-- On the real ray the auxiliary function is the coercion of its real avatar. -/
theorem auxF_ofReal (σ X t : ℝ) :
    auxF (σ:ℂ) X t
      = ((if |t| ≤ Real.log X then 1
          else Real.log X/|t| * Real.exp (-(σ - 1/2)*(|t| - Real.log X)) : ℝ) : ℂ) := by
  rw [auxF]
  by_cases ht : |t| ≤ Real.log X
  · rw [if_pos ht, if_pos ht, Complex.ofReal_one]
  · rw [if_neg ht, if_neg ht, Complex.ofReal_mul, Complex.ofReal_exp]
    congr 1
    push_cast
    ring

/-- **The pure-kernel prime sum is the logarithm** (B–F eq. (4) folded into the
`f_{σ,X}` weights): `∑_{𝔭,m} (log N𝔭/N𝔭^{m/2})·f_{σ,X}(m log N𝔭)
= T·e^{hT}·log ζ_K(σ)` for real `σ > 1`. -/
theorem tsum_kernel_eq_log_zeta {σ : ℝ} (hσ : 1 < σ) (X : ℝ) :
    ∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
      Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
        * (Real.log X / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * Real.exp (-(σ - 1/2)
                * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1) - Real.log X)))
      = Real.log X * Real.exp ((σ - 1/2) * Real.log X)
          * Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re) := by
  rw [real_log_dedekindZeta K hσ, ← tsum_mul_left]
  refine tsum_congr (fun pk => ?_)
  have hN2 : (2:ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) := two_le_absNorm_of_prime_real K
  have hN0 : (0:ℝ) < (Ideal.absNorm pk.1.1 : ℝ) := by linarith
  have hL0 : 0 < Real.log (Ideal.absNorm pk.1.1 : ℝ) :=
    Real.log_pos (by linarith)
  have hm0 : (0:ℝ) < ((pk.2+1 : ℕ) : ℝ) := by positivity
  -- collapse the exponentials: `N^{-m/2}·e^{-h(mL-T)} = e^{hT}·N^{-mσ}`
  have hexp : (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
      * Real.exp (-(σ - 1/2)
          * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1) - Real.log X))
      = Real.exp ((σ - 1/2) * Real.log X)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ) := by
    rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos hN0, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
        * (Real.log X / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * Real.exp (-(σ - 1/2)
                * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1) - Real.log X)))
      = (Real.log X / ((pk.2+1 : ℕ) : ℝ))
          * ((Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
            * Real.exp (-(σ - 1/2)
                * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1) - Real.log X))) := by
        field_simp
    _ = (Real.log X / ((pk.2+1 : ℕ) : ℝ))
          * (Real.exp ((σ - 1/2) * Real.log X)
            * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ)) := by rw [hexp]
    _ = Real.log X * Real.exp ((σ - 1/2) * Real.log X)
          * ((Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ)
            / ((pk.2+1 : ℕ) : ℝ)) := by ring

/-- **Finiteness of the plateau**: only finitely many prime powers satisfy
`m·log N𝔭 ≤ log X`. -/
theorem finite_plateau_support {X : ℝ} (hX : 1 < X) :
    {pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ |
      (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X}.Finite := by
  have hX0 : (0:ℝ) < X := by linarith
  refine Set.Finite.of_finite_image (f := fun pk => (pk.1.1, pk.2)) ?_ ?_
  · refine Set.Finite.subset
      ((Ideal.finite_setOf_absNorm_le (S := 𝓞 K) ⌊X⌋₊).prod
        (Set.finite_Iic ⌊Real.log X / Real.log 2⌋₊)) ?_
    rintro ⟨I, m⟩ ⟨pk, hpk, hIm⟩
    simp only [Prod.mk.injEq] at hIm
    obtain ⟨rfl, rfl⟩ : pk.1.1 = I ∧ pk.2 = m := ⟨hIm.1, hIm.2⟩
    have hN2 : (2:ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) := two_le_absNorm_of_prime_real K
    have hL2 : Real.log 2 ≤ Real.log (Ideal.absNorm pk.1.1 : ℝ) :=
      Real.log_le_log (by norm_num) hN2
    have hL0 : 0 < Real.log (Ideal.absNorm pk.1.1 : ℝ) :=
      Real.log_pos (by linarith)
    have hm1 : (1:ℝ) ≤ ((pk.2+1 : ℕ) : ℝ) := by
      have h1 : (1:ℕ) ≤ pk.2+1 := by lia
      exact_mod_cast h1
    constructor
    · -- `absNorm ≤ ⌊X⌋₊`: `log N ≤ m·log N ≤ log X`
      have h1 : Real.log (Ideal.absNorm pk.1.1 : ℝ) ≤ Real.log X := by
        calc Real.log (Ideal.absNorm pk.1.1 : ℝ)
            ≤ (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) := by
              nlinarith
          _ ≤ Real.log X := hpk
      have h2 : (Ideal.absNorm pk.1.1 : ℝ) ≤ X :=
        (Real.log_le_log_iff (by linarith) hX0).mp h1
      exact Nat.le_floor h2
    · -- `m ≤ ⌊log X/log 2⌋₊`: `(m+1)·log 2 ≤ (m+1)·log N ≤ log X`
      have h1 : (((pk.2+1 : ℕ)) : ℝ) * Real.log 2 ≤ Real.log X := by
        calc (((pk.2+1 : ℕ)) : ℝ) * Real.log 2
            ≤ (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) := by
              nlinarith
          _ ≤ Real.log X := hpk
      have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have h2 : ((pk.2 : ℕ) : ℝ) ≤ Real.log X / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        have h3 : ((pk.2 : ℕ) : ℝ) ≤ (((pk.2+1 : ℕ)) : ℝ) := by push_cast; linarith
        nlinarith
      exact Set.mem_Iic.mpr (Nat.le_floor h2)
  · intro pk _ pk' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) h.2

/-- **Summability of the kernel-weighted prime series** (its terms are
`T·e^{hT}·N^{-mσ}/m`, cf. `tsum_kernel_eq_log_zeta`). -/
theorem summable_kernel {σ : ℝ} (hσ : 1 < σ) (X : ℝ) :
    Summable (fun pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
        * (Real.log X / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
            * Real.exp (-(σ - 1/2)
                * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1) - Real.log X)))) := by
  have hsum := (summable_primeIdeal_pow_div K hσ).mul_left
    (Real.log X * Real.exp ((σ - 1/2) * Real.log X))
  refine hsum.congr (fun pk => ?_)
  have hN2 : (2:ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) := two_le_absNorm_of_prime_real K
  have hN0 : (0:ℝ) < (Ideal.absNorm pk.1.1 : ℝ) := by linarith
  have hL0 : 0 < Real.log (Ideal.absNorm pk.1.1 : ℝ) :=
    Real.log_pos (by linarith)
  have hm0 : (0:ℝ) < ((pk.2+1 : ℕ) : ℝ) := by positivity
  have hexp : (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
      * Real.exp (-(σ - 1/2)
          * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1) - Real.log X))
      = Real.exp ((σ - 1/2) * Real.log X)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * σ) := by
    rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos hN0, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h1 : Real.log (Ideal.absNorm pk.1.1)
      * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
      * (Real.log X / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
          * Real.exp (-(σ - 1/2)
              * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1) - Real.log X)))
      = (Real.log X / ((pk.2+1 : ℕ) : ℝ))
        * ((Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
          * Real.exp (-(σ - 1/2)
              * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1) - Real.log X))) := by
    field_simp
  rw [h1, hexp]
  ring

/-- **The prime side at the origin splits** (real `σ > 1`): the finitely-supported
plateau defect plus `T·e^{hT}·log ζ_K(σ)` — the bookkeeping step of Belabas–Friedman's
Lemma 3 that makes `log ζ_K` appear in the explicit formula. -/
theorem primeSideH_auxF_zero_split (a : ℝ) {σ X : ℝ} (hσ : 1 < σ) (hX : 1 < X) :
    primeSideH K a (auxF (σ:ℂ) X) 0
      = ((∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
          (if (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
            then Real.log (Ideal.absNorm pk.1.1)
              * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
              * (1 - Real.log X / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
                  * Real.exp (-(σ - 1/2)
                      * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1)
                        - Real.log X)))
            else 0) : ℝ) : ℂ)
        + ((Real.log X * Real.exp ((σ - 1/2) * Real.log X)
            * Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re) : ℝ) : ℂ) := by
  have hplateau : Summable (fun pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      (if (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
        then Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
          * (1 - Real.log X / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
              * Real.exp (-(σ - 1/2)
                  * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1) - Real.log X)))
        else 0)) := by
    refine summable_of_ne_finset_zero (s := (finite_plateau_support K hX).toFinset)
      (fun pk hpk => ?_)
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hpk
    exact if_neg hpk
  calc primeSideH K a (auxF (σ:ℂ) X) 0
      = ∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
          ((Real.log (Ideal.absNorm pk.1.1)
              * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2) : ℝ) : ℂ)
            * auxF (σ:ℂ) X ((((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1)) :=
        primeSideH_auxF_zero_eq K a _
    _ = ((∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
          Real.log (Ideal.absNorm pk.1.1)
            * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
            * (if |(((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1)| ≤ Real.log X
                then 1
                else Real.log X/|(((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1)|
                  * Real.exp (-(σ - 1/2)
                      * (|(((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1)|
                        - Real.log X))) : ℝ) : ℂ) := by
        rw [Complex.ofReal_tsum]
        exact tsum_congr (fun pk => by
          rw [auxF_ofReal, ← Complex.ofReal_mul])
    _ = ((∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
          ((if (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
            then Real.log (Ideal.absNorm pk.1.1)
              * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
              * (1 - Real.log X / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
                  * Real.exp (-(σ - 1/2)
                      * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1)
                        - Real.log X)))
            else 0)
          + Real.log (Ideal.absNorm pk.1.1)
              * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
              * (Real.log X / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
                  * Real.exp (-(σ - 1/2)
                      * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1)
                        - Real.log X)))) : ℝ) : ℂ) := by
        congr 1
        refine tsum_congr (fun pk => ?_)
        have hN2 : (2:ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) := two_le_absNorm_of_prime_real K
        have hL0 : 0 < Real.log (Ideal.absNorm pk.1.1 : ℝ) :=
          Real.log_pos (by linarith)
        have hm0 : (0:ℝ) < ((pk.2+1 : ℕ) : ℝ) := by positivity
        have hmL0 : 0 < (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) := by
          positivity
        rw [abs_of_pos hmL0]
        by_cases hg : (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
        · rw [if_pos hg, if_pos hg]
          ring
        · rw [if_neg hg, if_neg hg]
          ring
    _ = _ := by
        rw [show (∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
            ((if (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
              then Real.log (Ideal.absNorm pk.1.1)
                * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
                * (1 - Real.log X / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
                    * Real.exp (-(σ - 1/2)
                        * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1)
                          - Real.log X)))
              else 0)
            + Real.log (Ideal.absNorm pk.1.1)
                * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
                * (Real.log X / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
                    * Real.exp (-(σ - 1/2)
                        * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1)
                          - Real.log X)))))
            = (∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
              (if (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) ≤ Real.log X
                then Real.log (Ideal.absNorm pk.1.1)
                  * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
                  * (1 - Real.log X
                      / (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1))
                      * Real.exp (-(σ - 1/2)
                          * (((pk.2+1 : ℕ) : ℝ) * Real.log (Ideal.absNorm pk.1.1)
                            - Real.log X)))
                else 0))
              + (Real.log X * Real.exp ((σ - 1/2) * Real.log X)
                  * Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re))
          from by rw [Summable.tsum_add hplateau (summable_kernel K hσ X),
            tsum_kernel_eq_log_zeta (K := K) hσ X],
          Complex.ofReal_add]

/-! ### Lemma 3: the assembled display

Combining the tsum form of the explicit formula, the three-series split of the zero
side, and the plateau/log split of the prime side, and clearing `F_{σ,X}(0) = 1`,
gives Belabas–Friedman's Lemma 3 in the canonical rearrangement: the logarithm term
`2·T·e^{hT}·log ζ_K(σ)` equals the archimedean side minus the plateau defect minus
the three zero-series. (The paper's eq. (13) is this identity divided by
`2/g_σ(T) = 2·T·e^{hT}`.) -/

/-- **Belabas–Friedman Lemma 3** (canonical rearrangement, real `σ > 1`): under GRH,
$$ 2\,T e^{hT} \log ζ_K(σ) = Φ(0) + Φ(1) + \log Δ_K + c_Γ
  + n_K ∫\frac{1-F}{2\sinh(y/2)} + r_1 ∫\frac{1-F}{2\cosh(y/2)}
  - 2\!\!\sum_{mL ≤ T}\frac{\log N}{N^{m/2}}(1 - f_{σ,X}(mL))
  - S_{\sin} - S_{\cos} + S_{\mathrm{int}}, $$
where `S_sin`, `S_cos`, `S_int` are the three absolutely convergent zero-series of
eq. (13) and `c_Γ = -(n_K(γ_E + \log 8π) + r_1 π/2)`. -/
theorem lemma3_display (hGRH : GeneralizedRiemannHypothesis K)
    {σ X : ℝ} (hσ : 1 < σ) (hX : 1 < X) {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1/4)
    (has : a < σ - 1) :
    2 * ((Real.log X * Real.exp ((σ - 1/2) * Real.log X)
        * Real.log ((NumberField.dedekindZeta K (σ:ℂ)).re) : ℝ) : ℂ)
      = (paperPhi (auxF (σ:ℂ) X) 0 + paperPhi (auxF (σ:ℂ) X) 1)
        + ((Real.log |NumberField.discr K| : ℝ) : ℂ)
        + (((-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
            + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
              * (Real.eulerMascheroniConstant + Real.log (8*π))
            + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)) : ℝ)) : ℂ)
        + (((NumberField.InfinitePlace.nrRealPlaces K
            + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ)
            * (∫ y in Set.Ioi (0:ℝ),
              ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (1 - auxF (σ:ℂ) X y))
        + ((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ)
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
        - (∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im)
        - (∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X ρ.1.im)
        + ∑' ρ : ZetaZeros K,
            (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X ρ.1.im := by
  have hsre : a < ((σ:ℂ)).re - 1 := by rw [Complex.ofReal_re]; linarith
  have hmain := tsum_zetaZeros_paperPhi_auxF_eq K hGRH (σ:ℂ) hX ha ha' hsre
  rw [tsum_zetaZeros_paperPhi_auxF_split K hGRH hσ hX,
    primeSideH_auxF_zero_split K a hσ hX, auxF_zero (σ:ℂ) hX.le] at hmain
  simp only [mul_one] at hmain
  linear_combination hmain

end DedekindResidue

end
