/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrders
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicPartDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalConstants
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds

/-!
# Harmonic Part Bounds Helpers

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

/-! Summation, normalization and localization helpers for the all-order
harmonic pressure estimate: derivative bounds for finite sums of potentials and
the annulus power normalizations used at each order. -/

theorem norm_iteratedFDeriv_sum_le
    {ι : Type*} {s : Finset ι} {P : ι → Vec3 → ℝ} {U : Set Vec3}
    {k : ℕ} (hU : IsOpen U)
    (hP : ∀ i ∈ s, ContDiffOn ℝ (k : ℕ) (P i) U)
    {x : Vec3} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ k (∑ i ∈ s, P i) x‖ ≤
      ∑ i ∈ s, ‖iteratedFDeriv ℝ k (P i) x‖ := by
  rw [iteratedFDeriv_sum_apply]
  · exact norm_sum_le _ _
  intro i hi
  exact (hP i hi x hx).contDiffAt (hU.mem_nhds hx)

theorem norm_iteratedFDeriv_fin3_sum_le
    {P : Fin 3 → Vec3 → ℝ} {U : Set Vec3} {k : ℕ}
    (hU : IsOpen U) (hP : ∀ i, ContDiffOn ℝ (k : ℕ) (P i) U)
    {x : Vec3} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ k (∑ i : Fin 3, P i) x‖ ≤
      ∑ i : Fin 3, ‖iteratedFDeriv ℝ k (P i) x‖ := by
  simpa only [Fin.sum_univ_three] using
    (norm_iteratedFDeriv_sum_le (s := (Finset.univ : Finset (Fin 3))) hU
      (fun i hi => hP i) hx)

theorem annulus_power_normalize_potential {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    ((3 * ρ / 20) ^ (1 + k))⁻¹ * (ρ ^ (2 : ℕ))⁻¹ * ρ =
      (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) * ρ ^ (-(2 + k : ℝ)) := by
  rw [inv_pow_eq_rpow_neg (by positivity) (1 + k),
    inv_pow_eq_rpow_neg hρ 2]
  have hsplit : 3 * ρ / 20 = (3 / 20 : ℝ) * ρ := by ring
  rw [hsplit, Real.mul_rpow (by positivity) hρ.le]
  have hrpow : ρ ^ (-(1 + k : ℝ)) * ρ ^ (-(2 : ℝ)) * ρ =
      ρ ^ (-(2 + k : ℝ)) := by
    calc
      ρ ^ (-(1 + k : ℝ)) * ρ ^ (-(2 : ℝ)) * ρ =
          ρ ^ (-(1 + k : ℝ)) * ρ ^ (-(2 : ℝ)) * ρ ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = ρ ^ (-(1 + k : ℝ) + -(2 : ℝ)) * ρ ^ (1 : ℝ) := by
            rw [← Real.rpow_add hρ]
      _ = ρ ^ (-(1 + k : ℝ) + -(2 : ℝ) + 1) := by
            rw [← Real.rpow_add hρ]
      _ = _ := by congr 1; ring_nf
  have hk : -((1 + k : ℕ) : ℝ) = -(1 + k : ℝ) := by
    push_cast
    ring_nf
  rw [hk]
  calc
    (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) * ρ ^ (-(1 + k : ℝ)) *
        ρ ^ (-(2 : ℝ)) * ρ =
        (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) *
          (ρ ^ (-(1 + k : ℝ)) * ρ ^ (-(2 : ℝ)) * ρ) := by ring_nf
    _ = _ := by rw [hrpow]

theorem annulus_power_normalize_derivative {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    ((3 * ρ / 20) ^ (2 + k))⁻¹ * (ρ ^ (1 : ℕ))⁻¹ * ρ =
      (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) * ρ ^ (-(2 + k : ℝ)) := by
  rw [inv_pow_eq_rpow_neg (by positivity) (2 + k),
    inv_pow_eq_rpow_neg hρ 1]
  have hsplit : 3 * ρ / 20 = (3 / 20 : ℝ) * ρ := by ring
  rw [hsplit, Real.mul_rpow (by positivity) hρ.le]
  have hrpow : ρ ^ (-(2 + k : ℝ)) * ρ ^ (-(1 : ℝ)) * ρ =
      ρ ^ (-(2 + k : ℝ)) := by
    calc
      ρ ^ (-(2 + k : ℝ)) * ρ ^ (-(1 : ℝ)) * ρ =
          ρ ^ (-(2 + k : ℝ)) * ρ ^ (-(1 : ℝ)) * ρ ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = ρ ^ (-(2 + k : ℝ) + -(1 : ℝ)) * ρ ^ (1 : ℝ) := by
            rw [← Real.rpow_add hρ]
      _ = ρ ^ (-(2 + k : ℝ) + -(1 : ℝ) + 1) := by
            rw [← Real.rpow_add hρ]
      _ = _ := by congr 1; ring_nf
  have hk : -((2 + k : ℕ) : ℝ) = -(2 + k : ℝ) := by
    push_cast
    ring_nf
  rw [hk]
  calc
    (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) * ρ ^ (-(2 + k : ℝ)) *
        ρ ^ (-((1 : ℕ) : ℝ)) * ρ =
        (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
          (ρ ^ (-(2 + k : ℝ)) * ρ ^ (-(1 : ℝ)) * ρ) := by ring_nf
    _ = _ := by rw [hrpow]

theorem integral_abs_mul_le_ball_indicator
    {a b N : Vec3 → ℝ} {A B : Set Vec3} {K : ℝ}
    (hInt : Integrable (fun y => a y * b y) volume)
    (hN : Integrable N (volume.restrict B))
    (hN0 : ∀ y, 0 ≤ N y) (hK : 0 ≤ K) (hB : MeasurableSet B)
    (hsub : A ⊆ B)
    (hA : ∀ y, a y * b y ≠ 0 → y ∈ A)
    (ha : ∀ y, |a y| ≤ K) (hb : ∀ y, |b y| ≤ N y) :
    ∫ y, |a y * b y| ≤ K * ∫ y in B, N y := by
  have hNi : Integrable (B.indicator N) volume :=
    (show IntegrableOn N B volume from hN).integrable_indicator hB
  have hmono := integral_mono hInt.norm (hNi.const_mul K) (fun y => by
    have hle : |a y * b y| ≤ K * B.indicator N y := by
      by_cases hzero : a y * b y = 0
      · rw [hzero, abs_zero]
        by_cases hy : y ∈ B
        · simp only [Set.indicator_of_mem hy]
          exact mul_nonneg hK (hN0 y)
        · simp only [Set.indicator_of_notMem hy, mul_zero]
          norm_num
      · have hyA := hA y hzero
        have hyB := hsub hyA
        rw [Set.indicator_of_mem hyB, abs_mul]
        exact mul_le_mul (ha y) (hb y) (abs_nonneg _) hK
    simpa only [Real.norm_eq_abs] using hle)
  calc
    ∫ y, |a y * b y| ≤ ∫ y, K * B.indicator N y := hmono
    _ = K * ∫ y in B, N y := by
      rw [integral_const_mul, integral_indicator hB]

theorem norm_iteratedFDeriv_add_le
    {f g : Vec3 → ℝ} {k : ℕ} {x : Vec3}
    (hf : ContDiffAt ℝ (k : ℕ) f x) (hg : ContDiffAt ℝ (k : ℕ) g x) :
    ‖iteratedFDeriv ℝ k (f + g) x‖ ≤
      ‖iteratedFDeriv ℝ k f x‖ + ‖iteratedFDeriv ℝ k g x‖ := by
  rw [iteratedFDeriv_add_apply hf hg]
  exact norm_add_le _ _


end CKN
