/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFlowCoefficientProfile

/-! # Iterates Forcing Profiles From Flow

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- The two actual forcing coefficient profiles are derived from active flow
jets, the K bound, and the mean comparison. Positive flow jets need not carry
the small distortion prefactor before radius inflation. -/
theorem iterate_TForcing_profiles_from_flow {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    {κm κprev K Cflow Cmean r₀ ρ : ℝ} (hκ : 0 ≤ κprev)
    (hK : 0 ≤ K) (hCf : 0 ≤ Cflow) (hCm : 0 ≤ Cmean)
    (hr : 0 ≤ r₀) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hflow : ∀ t l, ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t))
    (hKm : ∀ t j k, |I.Kmat κm m t j k| ≤ K * κprev)
    (hmean : ∀ j k, |(timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
      κprev * Cmean * ρ)
    (hzero : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ j k,
      |(I.flowGrad hΦ m l t x - 1) j k| ≤ Cflow * ρ)
    (hpositive : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ p : List (Fin 2), 1 ≤ p.length → ∀ j k,
      |iterateSpatialWord p (fun y => (I.flowGrad hΦ m l t y - 1) j k) x| ≤
        Cflow * (p.length.factorial : ℝ) * r₀ ^ p.length)
    (hκscale : |κm| ≤ κprev) (hrad1 : 1 ≤ r₀ / ρ) :
    (∀ t x p j k, |iterateMatrixWord
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t y) p x j
          k| ≤
      κprev * (K + 1 + Cmean + (2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1))) *
          (p.length.factorial : ℝ) * (2 * (r₀ / ρ)) ^ p.length) ∧
    (∀ t x p j k, |iterateMatrixWord
      (fun y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm
          t y) p x j k| ≤
      κprev * (K + 1 + Cmean + (2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1))) * ρ *
          (p.length.factorial : ℝ) * (2 * (r₀ / ρ)) ^ p.length) := by
  have hs := iterate_sMat_small_profile_of_flow I hΦ hm κm κprev K Cflow r₀ ρ
    hK hCf hr hρ hρ1 hflow hKm hzero hpositive hκ hκscale hrad1
  have hrad : 0 ≤ 2 * (r₀ / ρ) := by positivity
  have hSM (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (I.sMat hΦ m κm t) :=
    AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm κm t (hflow t)
  have hsmall t p x j k : |iterateMatrixWord (I.sMat hΦ m κm t) p x j k| ≤
      κprev * ((2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1))) * ρ * (p.length.factorial : ℝ)
          * (2 * (r₀ / ρ)) ^ p.length := by
    exact hs t x p j k
  have hfullsmall t p x j k : |iterateMatrixWord (I.sMat hΦ m κm t) p x j k| ≤
      κprev * ((2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1))) * 1 * (p.length.factorial : ℝ)
          * (2 * (r₀ / ρ)) ^ p.length := by
    have hb := mul_le_mul_of_nonneg_left hρ1
      (show 0 ≤ κprev * ((2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1))) *
          (p.length.factorial : ℝ) * (2 * (r₀ / ρ)) ^ p.length by positivity)
    have hp := hsmall t p x j k
    nlinarith only [hb, hp]
  have hKcenter t j k : |(I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
      κprev * (K + 1) * 1 := by
    have hi : |(1 : Matrix (Fin 2) (Fin 2) ℝ) j k| ≤ 1 := by
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num
    have hb := mul_le_mul_of_nonneg_left hi hκ
    have ht := abs_sub (I.Kmat κm m t j k) (κprev * (1 : Matrix (Fin 2) (Fin 2) ℝ) j k)
    change |I.Kmat κm m t j k - κprev * (1 : Matrix (Fin 2) (Fin 2) ℝ) j k| ≤ _
    rw [abs_mul, abs_of_nonneg hκ] at ht
    nlinarith only [ht, hb, hKm t j k]
  constructor
  · intro t x p j k
    have hb := iterate_constant_plus_small_matrix_profile (hSM t) _ hκ
      (by positivity : 0 ≤ (2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1))) (by positivity : 0
          ≤ K + 1)
      (by norm_num : (0 : ℝ) ≤ 1) hrad (hKcenter t) (hfullsmall t) p x j k
    have hc := mul_nonneg (mul_nonneg (mul_nonneg hκ hCm)
      (Nat.cast_nonneg p.length.factorial)) (pow_nonneg hrad p.length)
    nlinarith only [hb, hc]
  · intro t x p j k
    have hb := iterate_constant_plus_small_matrix_profile (hSM t) _ hκ
      (by positivity : 0 ≤ (2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1))) hCm hρ.le hrad
          hmean (hsmall t) p x j k
    have hc := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hκ
      (by positivity : 0 ≤ K + 1)) hρ.le) (Nat.cast_nonneg p.length.factorial))
      (pow_nonneg hrad p.length)
    nlinarith only [hb, hc]

end AVenhance.Infra.Section4
