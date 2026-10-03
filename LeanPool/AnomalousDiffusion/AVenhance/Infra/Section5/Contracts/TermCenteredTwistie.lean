/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredPT
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredCombine

/-! # Per-time centered bounds for `twistie4`, `twistie5`

In the corrected form, both slots are pure divergences of smooth periodic fluxes
    (`twistie4_eq_neg_div_flux`),
so the centered `HDot⁻¹` bound is flux-only. The bounds for the earlier bodies `twistie4ND`,
`twistie5ND` are kept as `sd_tw4ND_time_bound`, `sd_tw5ND_time_bound`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff ENNReal

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Ergodic

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Common real-variable assembly: nondivergence bound + flux bound, with the square root of the
three slice energies split into a sum of square roots. -/
theorem sd_assemble_time_bound {Nd1 cf g₀ g₁ g₂ k₀ k₁ E2 Q : ℝ}
    (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁) (h₀ : 0 ≤ g₀) (h₁ : 0 ≤ g₁) (h₂ : 0 ≤ g₂)
    (hNd1 : 0 ≤ Nd1) (hE2 : 0 ≤ E2) (hQ : Q ≤ cf * Real.sqrt g₀)
    (hQ0 : 0 ≤ Q) :
    ENNReal.ofReal (Nd1 * Real.sqrt (k₀ ^ 2 * g₀ + k₁ ^ 2 * (g₁ + g₂)) + E2) +
      ENNReal.ofReal Q ≤
    ENNReal.ofReal ((Nd1 * k₀ + cf) * Real.sqrt g₀ + Nd1 * k₁ * Real.sqrt g₁ +
      Nd1 * k₁ * Real.sqrt g₂ + E2) := by
  have hs := sd_sqrt_comb_le hk₀ hk₁ h₀ h₁ h₂
  have hsn : 0 ≤ Real.sqrt (k₀ ^ 2 * g₀ + k₁ ^ 2 * (g₁ + g₂)) := Real.sqrt_nonneg _
  rw [← ENNReal.ofReal_add (by positivity) hQ0]
  apply ENNReal.ofReal_le_ofReal
  have := mul_le_mul_of_nonneg_left hs hNd1
  nlinarith [this]

/-- **Per-time centered bound for `twistie4`** (corrected form): `twistie4 = -div (flux)` is a pure
divergence, so its centered `HDot⁻¹` norm is at most the `L²` norm of the flux. -/
theorem sd_tw4_time_bound (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t))
    (hTp : IsZ2Periodic (T t)) {cf : ℝ} {V₀ : Vec 2 → Vec 2} (h₀ : Continuous V₀)
    (hflux : ∀ x, vecNormSq (twistie4Flux I hΦ m κm T t x) ≤ cf ^ 2 * vecNormSq (V₀ x)) :
    hMinusOneNorm (Integration.centerCell (twistie4 I hΦ m κm T t)) ≤
      ENNReal.ofReal (|cf| * Real.sqrt (gradNormSq V₀)) := by
  have hF := twistie4Flux_smooth_periodic I hΦ hm κm T hTt hTp
  refine (sd_centered_div_bound hF.1 hF.2 (twistie4_eq_neg_div_flux I hΦ m κm T t)).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hg := sd_gradNormSq_le hF.1.continuous h₀ hflux
  calc _ ≤ Real.sqrt (cf ^ 2 * gradNormSq V₀) := Real.sqrt_le_sqrt hg
    _ = |cf| * Real.sqrt (gradNormSq V₀) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- **Per-time centered bound for `twistie5`** (corrected form): `twistie5 = -div (flux)`. -/
theorem sd_tw5_time_bound (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t))
    (hTp : IsZ2Periodic (T t)) {cf : ℝ} {V₀ : Vec 2 → Vec 2} (h₀ : Continuous V₀)
    (hflux : ∀ x, vecNormSq (twistie5Flux I hΦ m κm T t x) ≤ cf ^ 2 * vecNormSq (V₀ x)) :
    hMinusOneNorm (Integration.centerCell (twistie5 I hΦ m κm T t)) ≤
      ENNReal.ofReal (|cf| * Real.sqrt (gradNormSq V₀)) := by
  have hF := twistie5Flux_smooth_periodic I hΦ hm κm T hTt hTp
  refine (sd_centered_div_bound hF.1 hF.2 (twistie5_eq_neg_div_flux I hΦ m κm T t)).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hg := sd_gradNormSq_le hF.1.continuous h₀ hflux
  calc _ ≤ Real.sqrt (cf ^ 2 * gradNormSq V₀) := Real.sqrt_le_sqrt hg
    _ = |cf| * Real.sqrt (gradNormSq V₀) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- Per-time centered bound for the earlier body `twistie4ND` (nondivergence part by the ergodic
lemma, divergence part by its flux). Kept for reference. -/
theorem sd_tw4ND_time_bound (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκm : 0 < κm) (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t))
    (hTp : IsZ2Periodic (T t)) {Cf r k₀ k₁ cf : ℝ} (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁)
    {V₀ V₁ V₂ : Vec 2 → Vec 2}
    (h₀ : Continuous V₀) (h₁ : Continuous V₁) (h₂ : Continuous V₂)
    (hpt : ∀ (k : ℤ) (a j : Fin 2) (x : Vec 2), section5SlowChoice2 I hΦ m κm T k t a j x ^ 2 ≤
      k₀ ^ 2 * vecNormSq (V₀ x) + k₁ ^ 2 * (vecNormSq (V₁ x) + vecNormSq (V₂ x)))
    (hflux : ∀ x, vecNormSq (twistie4Flux I hΦ m κm T t x) ≤ cf ^ 2 * vecNormSq (V₀ x))
    (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hder : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 → ∀ a j : Fin 2,
      HasCoordinateAnalyticL2Bounds (fun x =>
        ((section5SlowChoice2 I hΦ m κm T k.1 t a j (I.xFlow hΦ m (lIdx β I.Λ m k.1) t x) : ℝ) : ℂ))
        Cf r)
    (hnear : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 →
      FlowDerivativeNearIdentity (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k.1) t))
    (hNr : 2 ≤ r * (ergodicFrequency β I.Λ m : ℝ)) :
    hMinusOneNorm (Integration.centerCell (twistie4ND I hΦ m κm T t)) ≤
      ENNReal.ofReal
        ((144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ)) *
            (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) * k₀ + |cf|) * Real.sqrt (gradNormSq V₀) +
          144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ)) *
            (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) * k₁ * Real.sqrt (gradNormSq V₁) +
          144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ)) *
            (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) * k₁ * Real.sqrt (gradNormSq V₂) +
          144 * sdCd * Cf * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) *
            Real.exp (-r * (ergodicFrequency β I.Λ m : ℝ) / 4096)) := by
  have hm1 : 1 ≤ m := by omega
  have hnd := sd_nd4_centered_bound I hΦ hm hκm T hTt hTp h₀ h₁ h₂ hpt hCf hr hder hnear hNr
  have hsplit := sd_centered_split_bound
    (twistie4Nd_continuous I hΦ hm1 κm T hTt)
    (twistie4Flux_smooth_periodic I hΦ hm1 κm T hTt hTp).1
    (twistie4Flux_smooth_periodic I hΦ hm1 κm T hTt hTp).2
    (twistie4ND_split I hΦ hm1 κm T hTt)
  have hFc : Continuous (twistie4Flux I hΦ m κm T t) :=
    (twistie4Flux_smooth_periodic I hΦ hm1 κm T hTt hTp).1.continuous
  have hg := sd_gradNormSq_le hFc h₀ hflux
  have hQ : Real.sqrt (gradNormSq (twistie4Flux I hΦ m κm T t)) ≤
      |cf| * Real.sqrt (gradNormSq V₀) := by
    calc _ ≤ Real.sqrt (cf ^ 2 * gradNormSq V₀) := Real.sqrt_le_sqrt hg
      _ = |cf| * Real.sqrt (gradNormSq V₀) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hN : 0 < (ergodicFrequency β I.Λ m : ℝ) := by
    exact_mod_cast ergodicFrequency_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hA : 0 ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 / κm :=
    div_nonneg (mul_nonneg (Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
      (sq_nonneg _)) hκm.le
  refine (add_le_add hnd le_rfl |>.trans' hsplit).trans ?_
  have := sd_assemble_time_bound (Nd1 := 144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ)) *
    (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) (cf := |cf|) (g₀ := gradNormSq V₀)
    (g₁ := gradNormSq V₁) (g₂ := gradNormSq V₂) (k₀ := k₀) (k₁ := k₁)
    (E2 := 144 * sdCd * Cf * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) *
      Real.exp (-r * (ergodicFrequency β I.Λ m : ℝ) / 4096))
    (Q := Real.sqrt (gradNormSq (twistie4Flux I hΦ m κm T t))) hk₀ hk₁
    (sa_gradNormSq_nonneg _) (sa_gradNormSq_nonneg _) (sa_gradNormSq_nonneg _)
    (by have := sdCd_pos; positivity) (by have := sdCd_pos; positivity) hQ (Real.sqrt_nonneg _)
  convert this using 2
  ring_nf

/-- Per-time centered bound for the earlier body `twistie5ND` (choice 3). Kept for reference. -/
theorem sd_tw5ND_time_bound (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκm : 0 < κm) (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t))
    (hTp : IsZ2Periodic (T t)) {Cf r k₀ k₁ cf : ℝ} (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁)
    {V₀ V₁ V₂ : Vec 2 → Vec 2}
    (h₀ : Continuous V₀) (h₁ : Continuous V₁) (h₂ : Continuous V₂)
    (hpt : ∀ (k : ℤ) (a j : Fin 2) (x : Vec 2), section5SlowChoice3 I hΦ m T k t a j x ^ 2 ≤
      k₀ ^ 2 * vecNormSq (V₀ x) + k₁ ^ 2 * (vecNormSq (V₁ x) + vecNormSq (V₂ x)))
    (hflux : ∀ x, vecNormSq (twistie5Flux I hΦ m κm T t x) ≤ cf ^ 2 * vecNormSq (V₀ x))
    (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hder : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 → ∀ a j : Fin 2,
      HasCoordinateAnalyticL2Bounds (fun x =>
        ((section5SlowChoice3 I hΦ m T k.1 t a j (I.xFlow hΦ m (lIdx β I.Λ m k.1) t x) : ℝ) : ℂ))
        Cf r)
    (hnear : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 →
      FlowDerivativeNearIdentity (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k.1) t))
    (hNr : 2 ≤ r * (ergodicFrequency β I.Λ m : ℝ)) :
    hMinusOneNorm (Integration.centerCell (twistie5ND I hΦ m κm T t)) ≤
      ENNReal.ofReal
        ((144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ)) *
            (2 * (a β I.Λ m * epsilon β I.Λ m ^ 2)) * k₀ + |cf|) * Real.sqrt (gradNormSq V₀) +
          144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ)) *
            (2 * (a β I.Λ m * epsilon β I.Λ m ^ 2)) * k₁ * Real.sqrt (gradNormSq V₁) +
          144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ)) *
            (2 * (a β I.Λ m * epsilon β I.Λ m ^ 2)) * k₁ * Real.sqrt (gradNormSq V₂) +
          144 * sdCd * Cf * (2 * (a β I.Λ m * epsilon β I.Λ m ^ 2)) *
            Real.exp (-r * (ergodicFrequency β I.Λ m : ℝ) / 4096)) := by
  have hm1 : 1 ≤ m := by omega
  have hnd := sd_nd5_centered_bound I hΦ hm hκm T hTt hTp h₀ h₁ h₂ hpt hCf hr hder hnear hNr
  have hsplit := sd_centered_split_bound
    (twistie5Nd_continuous I hΦ hm1 κm T hTt)
    (twistie5Flux_smooth_periodic I hΦ hm1 κm T hTt hTp).1
    (twistie5Flux_smooth_periodic I hΦ hm1 κm T hTt hTp).2
    (twistie5ND_split I hΦ hm1 κm T hTt)
  have hFc : Continuous (twistie5Flux I hΦ m κm T t) :=
    (twistie5Flux_smooth_periodic I hΦ hm1 κm T hTt hTp).1.continuous
  have hg := sd_gradNormSq_le hFc h₀ hflux
  have hQ : Real.sqrt (gradNormSq (twistie5Flux I hΦ m κm T t)) ≤
      |cf| * Real.sqrt (gradNormSq V₀) := by
    calc _ ≤ Real.sqrt (cf ^ 2 * gradNormSq V₀) := Real.sqrt_le_sqrt hg
      _ = |cf| * Real.sqrt (gradNormSq V₀) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hN : 0 < (ergodicFrequency β I.Λ m : ℝ) := by
    exact_mod_cast ergodicFrequency_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hA : 0 ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 :=
    mul_nonneg (Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le (sq_nonneg _)
  refine (add_le_add hnd le_rfl |>.trans' hsplit).trans ?_
  have := sd_assemble_time_bound (Nd1 := 144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ)) *
    (2 * (a β I.Λ m * epsilon β I.Λ m ^ 2))) (cf := |cf|) (g₀ := gradNormSq V₀)
    (g₁ := gradNormSq V₁) (g₂ := gradNormSq V₂) (k₀ := k₀) (k₁ := k₁)
    (E2 := 144 * sdCd * Cf * (2 * (a β I.Λ m * epsilon β I.Λ m ^ 2)) *
      Real.exp (-r * (ergodicFrequency β I.Λ m : ℝ) / 4096))
    (Q := Real.sqrt (gradNormSq (twistie5Flux I hΦ m κm T t))) hk₀ hk₁
    (sa_gradNormSq_nonneg _) (sa_gradNormSq_nonneg _) (sa_gradNormSq_nonneg _)
    (by have := sdCd_pos; positivity) (by have := sdCd_pos; positivity) hQ (Real.sqrt_nonneg _)
  convert this using 2
  ring_nf

end AVenhance.Infra.Section5.Contracts
end
