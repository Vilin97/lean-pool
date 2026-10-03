/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredNormie3Analytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredNd
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredPT
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredCombine

/-! # Per-time centered bound for `normie3`

`normie3 = Σ_k Σ_{p,j} n3Fast_{kpj}(Y_k x) · n3Slow_{kpj}(x)` is a locally finite sum of fast-slow
products with mean-zero fast factors, so the generic centered ergodic bound
`sd_nd_centered_bound` applies directly (there is no divergence part).  The fast factors are
bounded by `G = 4ψ(1 + ψ/κ)`, `ψ = a_m ε_m²`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff ENNReal

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Ergodic

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- **Per-time centered bound of `normie3`.** -/
theorem n3_time_bound (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκm : 0 < κm) (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t))
    (hTp : IsZ2Periodic (T t)) {Cf r k₀ k₁ : ℝ} (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁)
    {V₀ V₁ V₂ : Vec 2 → Vec 2}
    (h₀ : Continuous V₀) (h₁ : Continuous V₁) (h₂ : Continuous V₂)
    (hpt : ∀ (k : ℤ) (p j : Fin 2) (x : Vec 2), n3Slow I hΦ m T k t p j x ^ 2 ≤
      k₀ ^ 2 * vecNormSq (V₀ x) + k₁ ^ 2 * (vecNormSq (V₁ x) + vecNormSq (V₂ x)))
    (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hder : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 → ∀ p j : Fin 2,
      HasCoordinateAnalyticL2Bounds (fun x =>
        ((n3Slow I hΦ m T k.1 t p j (I.xFlow hΦ m (lIdx β I.Λ m k.1) t x) : ℝ) : ℂ)) Cf r)
    (hnear : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 →
      FlowDerivativeNearIdentity (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k.1) t))
    (hNr : 2 ≤ r * (ergodicFrequency β I.Λ m : ℝ)) :
    hMinusOneNorm (Integration.centerCell (normie3 I hΦ m κm T t)) ≤
      ENNReal.ofReal
        ((144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ)) *
            (4 * (a β I.Λ m * epsilon β I.Λ m ^ 2) *
              (1 + a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) * k₀) * Real.sqrt (gradNormSq V₀) +
          (144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ)) *
            (4 * (a β I.Λ m * epsilon β I.Λ m ^ 2) *
              (1 + a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) * k₁) * Real.sqrt (gradNormSq V₁) +
          (144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ)) *
            (4 * (a β I.Λ m * epsilon β I.Λ m ^ 2) *
              (1 + a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) * k₁) * Real.sqrt (gradNormSq V₂) +
          144 * sdCd * Cf *
            (4 * (a β I.Λ m * epsilon β I.Λ m ^ 2) *
              (1 + a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) *
            Real.exp (-r * (ergodicFrequency β I.Λ m : ℝ) / 4096)) := by
  have hm1 : 1 ≤ m := by omega
  have hNpos : 0 < ergodicFrequency β I.Λ m :=
    ergodicFrequency_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hN : (0 : ℝ) < (ergodicFrequency β I.Λ m : ℝ) := by exact_mod_cast hNpos
  have hψ0 : 0 ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 := scf_P_nonneg I
  set G : ℝ := 4 * (a β I.Λ m * epsilon β I.Λ m ^ 2) *
    (1 + a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) with hG
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hnd := sd_nd_centered_bound I hΦ t (fun k p j => n3Fast I κm m k.1 t p j)
    (fun k p j => n3Slow I hΦ m T k.1 t p j) (normie3 I hΦ m κm T t)
    (fun S hS x => normie3_eq_sum I hΦ m κm T t S hS x)
    (fun k p j hk => n3Slow_zero I hΦ m T k.1 t p j hk)
    (fun k p j => n3Slow_smooth_periodic I hΦ m T hTt hTp k.1 p j)
    (fun k p j => n3Fast_continuous I κm k.2 t p j)
    (fun k p j => n3Fast_isFastPeriodic I hm1 κm k.1 t p j)
    (fun k p j => n3Fast_cellAverage I hm1 κm k.2 t p j)
    (Gm := G) (fun k p j y => n3Fast_abs_le I hm1 hκm k.1 t p j y)
    (fun k p j hk => hder k hk p j) hnear hCf hr hNpos hNr
    (F2sq := k₀ ^ 2 * gradNormSq V₀ + k₁ ^ 2 * (gradNormSq V₁ + gradNormSq V₂)) ?_
  · refine hnd.trans (ENNReal.ofReal_le_ofReal ?_)
    have hs := sd_sqrt_comb_le hk₀ hk₁ (sa_gradNormSq_nonneg V₀) (sa_gradNormSq_nonneg V₁)
      (sa_gradNormSq_nonneg V₂)
    have hcd := sdCd_pos
    have hc : 0 ≤ 144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ)) * G := by positivity
    have := mul_le_mul_of_nonneg_left hs hc
    nlinarith [this]
  · intro k p j _
    exact sd_cellAverage_sq_le (n3Slow_smooth_periodic I hΦ m T hTt hTp k.1 p j).1.continuous
      h₀ h₁ h₂ (hpt k.1 p j)

end AVenhance.Infra.Section5.Contracts
end
