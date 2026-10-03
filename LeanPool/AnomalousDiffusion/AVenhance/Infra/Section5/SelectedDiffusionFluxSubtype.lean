/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.OddSupportTsum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SelectedDiffusionFlux

/-! Selected diffusion flux decomposition on the odd-subtype support. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

/-- Reindex the selected spatial-gradient decomposition from integer
cutoff support to the finite odd-subtype support used by the named terms. -/
theorem frozen_ansatz_diffusion_flux_decomposition_odd_support
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (hT : ∀ y, HasFDerivAt (T t) (fderiv ℝ (T t) y) y)
    (hH : ∀ y, HasFDerivAt (I.Hm hΦ m κ T t)
      (fderiv ℝ (I.Hm hΦ m κ T t) y) y)
    (hχ : ∀ k ∈ (I.xiMK_support_finite m t).toFinset, ∀ y,
      HasFDerivAt (I.chiTilde hΦ m κ k t)
        (fderiv ℝ (I.chiTilde hΦ m κ k t) y) y)
    (hG : ∀ k ∈ (I.xiMK_support_finite m t).toFinset, ∀ y,
      HasFDerivAt (fun z => G I hΦ m T (lIdx β I.Λ m k) t z)
        (fderiv ℝ (fun z => G I hΦ m T (lIdx β I.Λ m k) t z) y) y)
    (y : Vec 2) :
    (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (I.ansatz hΦ m κ T t) y) =
      (∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t •
          (correctorFlux I hΦ m κ q.1 t y).mulVec
            (G I hΦ m T (lIdx β I.Λ m q.1) t y)) +
      (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (T t) y -
          ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
            I.xiMK m q.1 t •
              G I hΦ m T (lIdx β I.Λ m q.1) t y) +
      (∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t •
          (diffusionMatrix I hΦ m κ t y).mulVec
            (chiGradG I hΦ m κ T q.1 t y)) +
      (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (I.Hm hΦ m κ T t) y) := by
  have hbase := frozen_ansatz_diffusion_flux_decomposition I hΦ m hm κ T t
    hT hH hχ hG y
  let U := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have hcorrector := xiMK_odd_integer_support_sum_eq_subtype_sum I m hm t
    (fun k => (correctorFlux I hΦ m κ k t y).mulVec
      (G I hΦ m T (lIdx β I.Λ m k) t y))
  have hgradient := xiMK_odd_integer_support_sum_eq_subtype_sum I m hm t
    (fun k => G I hΦ m T (lIdx β I.Λ m k) t y)
  have hchi := xiMK_odd_integer_support_sum_eq_subtype_sum I m hm t
    (fun k => (diffusionMatrix I hΦ m κ t y).mulVec
      (chiGradG I hΦ m κ T k t y))
  rw [hcorrector, hgradient, hchi] at hbase
  simpa [U] using hbase

end AVenhance.Infra.Section5

end
