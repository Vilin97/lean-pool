/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Profile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoefficientWords
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingCoefficients
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesRadiusInflation

/-! # Iterates Flow Coefficient Profile

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- Actual coefficient jets follow from the finite cutoff average and the
active flow jets. The small zeroth flow jet and positive analytic jets use the
inflated radius; no sMat coefficient estimate is a premise. -/
theorem iterate_sMat_small_profile_of_flow {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    (κm κprev K Cflow r₀ ρ : ℝ) (_hK : 0 ≤ K) (hCf : 0 ≤ Cflow)
    (hr : 0 ≤ r₀) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hflow : ∀ t l, ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t))
    (hKm : ∀ t j k, |I.Kmat κm m t j k| ≤ K * κprev)
    (hzero : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ j k,
      |(I.flowGrad hΦ m l t x - 1) j k| ≤ Cflow * ρ)
    (hpositive : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ p : List (Fin 2), 1 ≤ p.length → ∀ j k,
      |iterateSpatialWord p (fun y => (I.flowGrad hΦ m l t y - 1) j k) x| ≤
        Cflow * (p.length.factorial : ℝ) * r₀ ^ p.length)
    (hκprev : 0 ≤ κprev) (hκscale : |κm| ≤ κprev) (hrad : 1 ≤ r₀ / ρ) :
    ∀ t x p j k, |iterateMatrixWord (I.sMat hΦ m κm t) p x j k| ≤
      κprev * (2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1)) * ρ *
        (p.length.factorial : ℝ) * (2 * (r₀ / ρ)) ^ p.length := by
  intro t x p j k
  have hs := (sMat_coarseCoeffForm I hΦ m κm).small_profile_of_flow hm
    (mul_nonneg _hK hκprev) hCf hr hρ hρ1 hflow hKm hzero hpositive t x p j k
  rw [max_eq_right hrad] at hs
  have hA : Cflow * ρ ≤ Cflow := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hρ1 hCf
  have hcoeff : 2 * (K * κprev) * (Cflow * ρ) +
      4 * (K * κprev + |κm|) * (Cflow * ρ) * (Cflow * ρ + 1) ≤
      κprev * (2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1)) * ρ := by
    have hq : 4 * (K * κprev + |κm|) * (Cflow * ρ) * (Cflow * ρ + 1) ≤
        4 * (K * κprev + κprev) * (Cflow * ρ) * (Cflow + 1) := by
      gcongr
    nlinarith only [hq]
  exact hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)) (pow_nonneg (by positivity) _))

/-- Adding a spatially constant coefficient preserves the positive small
jets, and its zeroth bound adds to the small sMat coefficient. -/
theorem iterate_constant_plus_small_matrix_profile
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (B : Matrix (Fin 2) (Fin 2) ℝ) {κ Csmall Cbase ρ r : ℝ}
    (hκ : 0 ≤ κ) (_hCs : 0 ≤ Csmall) (hCb : 0 ≤ Cbase) (hρ : 0 ≤ ρ) (hr : 0 ≤ r)
    (hB : ∀ j k, |B j k| ≤ κ * Cbase * ρ)
    (hsmall : ∀ p x j k, |iterateMatrixWord A p x j k| ≤
      κ * Csmall * ρ * (p.length.factorial : ℝ) * r ^ p.length) :
    ∀ p x j k, |iterateMatrixWord (fun y => B + A y) p x j k| ≤
      κ * (Cbase + Csmall) * ρ * (p.length.factorial : ℝ) * r ^ p.length := by
  intro p x j k
  rw [iterateMatrixWord_constant_add hA B p x]
  by_cases hp : p = []
  · subst p
    simp only [ite_true, Matrix.add_apply]
    have hb := hB j k
    have hs := hsmall [] x j k
    simp only [List.length_nil, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one] at hs ⊢
    have ht := abs_add_le (B j k) (iterateMatrixWord A [] x j k)
    nlinarith only [hb, hs, ht]
  · simp only [hp, ite_false, zero_add]
    have hs := hsmall p x j k
    have hc := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hκ hCb) hρ)
      (Nat.cast_nonneg p.length.factorial)) (pow_nonneg hr p.length)
    nlinarith only [hs, hc]

end AVenhance.Infra.Section4
