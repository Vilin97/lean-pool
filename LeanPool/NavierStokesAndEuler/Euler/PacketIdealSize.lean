/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof

@[expose] public section

/-!
Uniform comparison of ideal primary sizes before target.  This follows
from the actual scalar equation's prefix and weighted monotonicity.
-/

noncomputable section


namespace EulerPacketMovingFrame

open Set EulerPacketGrowth

def idealPrimarySize (σ : ℝ) (Z : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (1+(σ^2*t^2)^2)*Z t

theorem quadratic_weight_sqrt {p : ℝ} (hp : 0 ≤ p) :
    Real.sqrt (1+p^2) ≤ 1+p ∧ 1+p ≤ 2*Real.sqrt (1+p^2) := by
  constructor
  · exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith only [hp]⟩
  · have h1 : 1 ≤ Real.sqrt (1+p^2) := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg p])
    have hp' : p ≤ Real.sqrt (1+p^2) := Real.le_sqrt_of_sq_le (by linarith)
    linarith only [h1, hp']

theorem equation30_polynomial_size_monotone {σ : ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) :
    MonotoneOn (fun t => (1+σ^2*t^2)*Z t) (Ici 0) := by
  have hpos := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0
  have hpre := equation30_prefix_monotone hσ hσsmall hZ hfluxZ hZ0 hZ₁0
  have hpost := equation30_weighted_monotone hσ hσsmall hZ hfluxZ hZ0 hZ₁0
  have hcut : 0 < 1/σ := by positivity
  have hpreW : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1/σ → (1+σ^2*s^2)*Z s ≤ (1+σ^2*t^2)*Z t := by
    intro s t hs hst ht
    have ht0 := hs.trans hst
    have hz := hpre ⟨hs, hst.trans ht⟩ ⟨ht0, ht⟩ hst
    have hpow : s^2 ≤ t^2 := (sq_le_sq₀ hs ht0).mpr hst
    have hcoef : 1+σ^2*s^2 ≤ 1+σ^2*t^2 := by
      nlinarith only [mul_le_mul_of_nonneg_left hpow (sq_nonneg σ)]
    exact (mul_le_mul_of_nonneg_left hz (by positivity)).trans
      (mul_le_mul_of_nonneg_right hcoef (hpos t ht0).le)
  have hpostW : ∀ s t, 1/σ ≤ s → s ≤ t → (1+σ^2*s^2)*Z s ≤ (1+σ^2*t^2)*Z t := by
    intro s t hs hst
    have hs0 := hcut.trans_le hs
    have ht := hs.trans hst
    have ht0 := hs0.le.trans hst
    have hz := hpost hs ht hst
    have hss : 1 ≤ σ*s := by have hh := (div_le_iff₀ hσ).mp hs; nlinarith only [hh]
    have hst' : 1 ≤ σ*t := by have hh := (div_le_iff₀ hσ).mp ht; nlinarith only [hh]
    have hproduct : 1 ≤ (σ*s)*(σ*t) := by
      simpa only [one_mul] using mul_le_mul hss hst' zero_le_one (le_trans zero_le_one hss)
    have hpositive : 0 ≤ (t-s)*(σ^2*s*t-1) :=
      mul_nonneg (sub_nonneg.mpr hst) (by nlinarith only [hproduct])
    have hcoef : t*(1+σ^2*s^2) ≤ s*(1+σ^2*t^2) := by nlinarith only [hpositive]
    have h1 := mul_le_mul_of_nonneg_left hz (show 0 ≤ 1+σ^2*s^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (hpos t ht0).le
    apply (mul_le_mul_iff_right₀ hs0).mp
    nlinarith only [h1, h2]
  intro s hs t _ht hst
  by_cases htpre : t ≤ 1/σ
  · exact hpreW s t hs hst htpre
  · have htpost : 1/σ ≤ t := le_of_not_ge htpre
    by_cases hspre : s ≤ 1/σ
    · exact (hpreW s (1/σ) hs hspre le_rfl).trans (hpostW (1/σ) t le_rfl htpost)
    · exact hpostW s t (le_of_not_ge hspre) hst

/-- The ideal physical primary size is bounded by twice its later size,
uniformly in the initial nonnegative scalar slope. -/
theorem equation30_ideal_size_comparison {σ s t : ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) (hs : 0 ≤ s) (hst : s ≤ t) :
    idealPrimarySize σ Z s ≤ 2*idealPrimarySize σ Z t := by
  have hpos := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0
  have hmono := equation30_polynomial_size_monotone hσ hσsmall hZ hfluxZ hZ0 hZ₁0 hs (hs.trans hst)
    hst
  have hws := (quadratic_weight_sqrt (show 0 ≤ σ^2*s^2 by positivity)).1
  have hwt := (quadratic_weight_sqrt (show 0 ≤ σ^2*t^2 by positivity)).2
  have h1 := mul_le_mul_of_nonneg_right hws (hpos s hs).le
  have h2 := mul_le_mul_of_nonneg_right hwt (hpos t (hs.trans hst)).le
  unfold idealPrimarySize
  nlinarith only [h1, hmono, h2]

end EulerPacketMovingFrame
