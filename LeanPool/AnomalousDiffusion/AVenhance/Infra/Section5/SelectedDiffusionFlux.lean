/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SelectedAnsatzSpatial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorLocalization

/-! Rewrite the diffusion flux of the ansatz using the selected
corrector fluxes, the selected-gradient mismatch, the pulled-gradient term,
and the `H_m` gradient. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

/-- Pointwise selected-flow decomposition of the ansatz diffusion
flux. The local derivative hypotheses are those used by the already proved
selected spatial-gradient identity. -/
theorem frozen_ansatz_diffusion_flux_decomposition
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
      (∑ k ∈ ((I.xiMK_support_finite m t).toFinset.filter Odd),
        I.xiMK m k t •
          (correctorFlux I hΦ m κ k t y).mulVec
            (G I hΦ m T (lIdx β I.Λ m k) t y)) +
      (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (T t) y -
          ∑ k ∈ ((I.xiMK_support_finite m t).toFinset.filter Odd),
            I.xiMK m k t • G I hΦ m T (lIdx β I.Λ m k) t y) +
      (∑ k ∈ ((I.xiMK_support_finite m t).toFinset.filter Odd),
        I.xiMK m k t •
          (diffusionMatrix I hΦ m κ t y).mulVec
            (chiGradG I hΦ m κ T k t y)) +
      (diffusionMatrix I hΦ m κ t y).mulVec
        (spaceGrad (I.Hm hΦ m κ T t) y) := by
  let S₀ := (I.xiMK_support_finite m t).toFinset
  let S := S₀.filter Odd
  have hgrad (i : Fin 2) := ansatz_spaceGrad_selected I hΦ m κ T t y
    (fun k => fderiv ℝ (I.chiTilde hΦ m κ k t) y)
    (fun k => fderiv ℝ (fun z => G I hΦ m T (lIdx β I.Λ m k) t z) y)
    (hT y) (hH y) (by intro k hk; exact hχ k hk y)
    (by intro k hk; exact hG k hk y) i
  have hselected :
      spaceGrad (I.ansatz hΦ m κ T t) y =
        (∑ k ∈ S, I.xiMK m k t •
          ((gradMatrix (I.chiTilde hΦ m κ k t) y).mulVec
              (G I hΦ m T (lIdx β I.Λ m k) t y) +
            G I hΦ m T (lIdx β I.Λ m k) t y)) +
        (spaceGrad (T t) y -
          ∑ k ∈ S, I.xiMK m k t •
            G I hΦ m T (lIdx β I.Λ m k) t y) +
        (∑ k ∈ S, I.xiMK m k t • chiGradG I hΦ m κ T k t y) +
        spaceGrad (I.Hm hΦ m κ T t) y := by
    ext i
    have hi := hgrad i
    fin_cases i <;>
      simpa [S, S₀, chiGradG, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        gradG, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply,
        Pi.add_apply, Pi.sub_apply, mul_add] using hi
  have hlocal (k : ℤ) (hk : k ∈ S) (z : Vec 2) :
      diffusionMatrix I hΦ m κ t z *
          (1 + gradChiTilde I hΦ m κ k t z) =
        correctorFlux I hΦ m κ k t z := by
    have hkodd : Odd k := (Finset.mem_filter.mp hk).2
    have hkS₀ : k ∈ S₀ := (Finset.mem_filter.mp hk).1
    have hxi : I.xiMK m k t ≠ 0 := by
      exact (I.xiMK_support_finite m t).mem_toFinset.mp hkS₀
    simpa [gradChiTilde] using congrFun
      (diffusionMatrix_mul_one_plus_gradChi_eq_correctorFlux
        I hΦ m hm κ k t hkodd hxi) z
  have hfirst :
      (diffusionMatrix I hΦ m κ t y).mulVec
          (∑ k ∈ S, I.xiMK m k t •
            ((gradMatrix (I.chiTilde hΦ m κ k t) y).mulVec
                (G I hΦ m T (lIdx β I.Λ m k) t y) +
              G I hΦ m T (lIdx β I.Λ m k) t y)) =
      ∑ k ∈ S, I.xiMK m k t •
          (correctorFlux I hΦ m κ k t y).mulVec
            (G I hΦ m T (lIdx β I.Λ m k) t y) := by
    rw [Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul]
    apply Finset.sum_congr rfl
    intro k hk
    have hvec :
        (gradMatrix (I.chiTilde hΦ m κ k t) y).mulVec
            (G I hΦ m T (lIdx β I.Λ m k) t y) +
          G I hΦ m T (lIdx β I.Λ m k) t y =
        (1 + gradMatrix (I.chiTilde hΦ m κ k t) y).mulVec
            (G I hΦ m T (lIdx β I.Λ m k) t y) := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec]
      abel
    have hcore :
        (diffusionMatrix I hΦ m κ t y).mulVec
          ((gradMatrix (I.chiTilde hΦ m κ k t) y).mulVec
              (G I hΦ m T (lIdx β I.Λ m k) t y) +
            G I hΦ m T (lIdx β I.Λ m k) t y) =
          (correctorFlux I hΦ m κ k t y).mulVec
            (G I hΦ m T (lIdx β I.Λ m k) t y) := by
      calc
        _ = (diffusionMatrix I hΦ m κ t y).mulVec
            ((1 + gradMatrix (I.chiTilde hΦ m κ k t) y).mulVec
              (G I hΦ m T (lIdx β I.Λ m k) t y)) := by rw [hvec]
        _ = (diffusionMatrix I hΦ m κ t y *
            (1 + gradMatrix (I.chiTilde hΦ m κ k t) y)).mulVec
              (G I hΦ m T (lIdx β I.Λ m k) t y) := by
                rw [Matrix.mulVec_mulVec]
        _ = (correctorFlux I hΦ m κ k t y).mulVec
              (G I hΦ m T (lIdx β I.Λ m k) t y) := by
                simpa [gradChiTilde] using congrArg
                  (fun B : Matrix (Fin 2) (Fin 2) ℝ =>
                    B.mulVec (G I hΦ m T (lIdx β I.Λ m k) t y))
                  (hlocal k hk y)
    exact congrArg (fun v : Vec 2 => I.xiMK m k t • v) hcore
  rw [hselected]
  rw [Matrix.mulVec_add]
  rw [Matrix.mulVec_add]
  rw [Matrix.mulVec_add]
  rw [hfirst]
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_smul,
    S, S₀]

end AVenhance.Infra.Section5

end
