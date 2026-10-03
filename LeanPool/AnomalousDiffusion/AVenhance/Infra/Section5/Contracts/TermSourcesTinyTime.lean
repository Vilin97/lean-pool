/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyTransfer

/-! # Time assembly for the `tiny` source contract

Abstract measure-theoretic step: if the slices of the negative norm are dominated by a divergence
part `√‖F‖²` (with `‖F‖² ≤ 2‖d‖² + 2‖e‖²`) and a nondivergence part `(2π)⁻¹ √‖n‖²`, if the
`d`-energy is controlled in `L²_t` by the contract and the remaining energy
`4‖e‖² + 2 (2π)⁻² ‖n‖²` by its lower integral, then the time negative norm is bounded by
`2 b_d + √S`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

theorem sc_ofReal_sqrt_sq {g : ℝ} (hg : 0 ≤ g) :
    ENNReal.ofReal (Real.sqrt g) ^ 2 = ENNReal.ofReal g := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hg]

/-- The pointwise-in-time estimate `X² ≤ ofReal (4 Gd) + ofReal (4 Ge + 2 (2π)⁻² N)`. -/
theorem sc_sq_le_of_slices {X : ENNReal} {GF Gd Ge N : ℝ} (hGd : 0 ≤ Gd) (hGe : 0 ≤ Ge)
    (hN : 0 ≤ N) (hGF0 : 0 ≤ GF) (hGF : GF ≤ 2 * Gd + 2 * Ge)
    (hX : X ≤ ENNReal.ofReal (Real.sqrt GF) +
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.sqrt N)) :
    X ^ 2 ≤ ENNReal.ofReal (4 * Gd) +
      ENNReal.ofReal (4 * Ge + 2 * ((2 * Real.pi)⁻¹) ^ 2 * N) := by
  have hpi : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  set A : ℝ := Real.sqrt GF with hA
  set B : ℝ := (2 * Real.pi)⁻¹ * Real.sqrt N with hB
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := mul_nonneg hpi (Real.sqrt_nonneg _)
  have hA2 : A ^ 2 = GF := Real.sq_sqrt hGF0
  have hB2 : B ^ 2 = ((2 * Real.pi)⁻¹) ^ 2 * N := by
    rw [hB, mul_pow, Real.sq_sqrt hN]
  have h1 : X ^ 2 ≤ (ENNReal.ofReal A + ENNReal.ofReal B) ^ 2 := pow_le_pow_left' hX 2
  rw [← ENNReal.ofReal_add hA0 hB0, ← ENNReal.ofReal_pow (add_nonneg hA0 hB0)] at h1
  refine h1.trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by nlinarith [sq_nonneg (A - B)]
  rw [hA2, hB2] at this
  have hq : 0 ≤ ((2 * Real.pi)⁻¹) ^ 2 * N := by positivity
  nlinarith

/-- **Time assembly.** -/
theorem sc_time_norm_le {X : ℝ → ENNReal} {GF Gd Ge N : ℝ → ℝ} {bd S : ℝ} (hbd : 0 ≤ bd)
    (hS : 0 ≤ S)
    (hGd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ Gd t) (hGe : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ Ge t)
    (hN : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ N t) (hGF0 : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ GF t)
    (hGF : ∀ t ∈ Set.Ioo (0 : ℝ) 1, GF t ≤ 2 * Gd t + 2 * Ge t)
    (hX : ∀ t ∈ Set.Ioo (0 : ℝ) 1, X t ≤ ENNReal.ofReal (Real.sqrt (GF t)) +
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.sqrt (N t)))
    (hmeas : AEMeasurable (fun t => ENNReal.ofReal (Gd t)) (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (hd : (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (Gd t)) ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal bd)
    (hrest : ∫⁻ t in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (4 * Ge t + 2 * ((2 * Real.pi)⁻¹) ^ 2 * N t) ≤ ENNReal.ofReal S) :
    (∫⁻ t in Set.Ioo (0 : ℝ) 1, X t ^ 2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (2 * bd + Real.sqrt S) := by
  have h1 : ∫⁻ t in Set.Ioo (0 : ℝ) 1, X t ^ 2 ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1,
      (ENNReal.ofReal (4 * Gd t) +
        ENNReal.ofReal (4 * Ge t + 2 * ((2 * Real.pi)⁻¹) ^ 2 * N t)) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact sc_sq_le_of_slices (hGd t ht) (hGe t ht) (hN t ht) (hGF0 t ht) (hGF t ht) (hX t ht)
  have hmeas4 : AEMeasurable (fun t => ENNReal.ofReal (4 * Gd t))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    have : (fun t => ENNReal.ofReal (4 * Gd t)) = fun t => 4 * ENNReal.ofReal (Gd t) := by
      funext t
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [this]
    exact hmeas.const_mul 4
  rw [lintegral_add_left' hmeas4] at h1
  have h2 : ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (4 * Gd t) ≤ ENNReal.ofReal (4 * bd ^ 2) := by
    have e1 : ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (4 * Gd t) =
        4 * ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (Gd t) := by
      have : (fun t => ENNReal.ofReal (4 * Gd t)) = fun t => 4 * ENNReal.ofReal (Gd t) := by
        funext t
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      rw [this, lintegral_const_mul'' _ hmeas]
    have e2 : ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (Gd t) =
        ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (Gd t)) ^ 2 := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      exact (sc_ofReal_sqrt_sq (hGd t ht)).symm
    have e3 : ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (Gd t)) ^ 2 ≤
        ENNReal.ofReal bd ^ 2 := by
      have := ENNReal.rpow_le_rpow hd (by norm_num : (0 : ℝ) ≤ 2)
      rwa [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.rpow_two] at this
    rw [e1, e2]
    calc 4 * ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (Gd t)) ^ 2
        ≤ 4 * ENNReal.ofReal bd ^ 2 := by gcongr
      _ = ENNReal.ofReal (4 * bd ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hbd]
        norm_num
  have h3 : ∫⁻ t in Set.Ioo (0 : ℝ) 1, X t ^ 2 ≤ ENNReal.ofReal (4 * bd ^ 2 + S) := by
    rw [ENNReal.ofReal_add (by positivity) hS]
    exact h1.trans (add_le_add h2 hrest)
  calc _ ≤ (ENNReal.ofReal (4 * bd ^ 2 + S)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h3 (by norm_num)
    _ = ENNReal.ofReal ((4 * bd ^ 2 + S) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.sqrt_eq_rpow]
        apply Real.sqrt_le_iff.2
        refine ⟨by positivity, ?_⟩
        have hs := Real.sq_sqrt hS
        nlinarith [Real.sqrt_nonneg S, mul_nonneg hbd (Real.sqrt_nonneg S)]

end AVenhance.Infra.Section5.Contracts
