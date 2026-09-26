/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.PowerSum
public import LeanPool.MarkoffModP.BGS.HasseWeil.ZetaTrace

/-!
# Spectral bounds from even power-sum asymptotics

This file formalizes the elementary Corvaja--Zannier/Tao step that turns an
even-extension point-count asymptotic into the Riemann-hypothesis bound for
each Frobenius parameter.

Repeated squared parameters must first be grouped.  Their coefficients are
the positive cardinalities of their fibers, so the weighted power-sum lemma
from `BGS.HasseWeil.PowerSum` applies without an injectivity assumption on the
original family of parameters.
-/

@[expose] public section

namespace BGS.HasseWeil

open Filter Asymptotics
open scoped BigOperators

noncomputable section

/-- The finite set of distinct squared values occurring in `alpha`. -/
def squaredBaseSet {N : ℕ} (alpha : Fin N → ℂ) : Finset ℂ :=
  Finset.univ.image fun i ↦ alpha i ^ 2

/-- The complex-valued multiplicity of a squared value occurring in `alpha`. -/
def squaredBaseMultiplicity {N : ℕ} (alpha : Fin N → ℂ) (z : ℂ) : ℂ :=
  ((Finset.univ.filter fun i ↦ alpha i ^ 2 = z).card : ℂ)

/-- Every squared value in `squaredBaseSet alpha` has positive, hence nonzero,
multiplicity. -/
lemma squaredBaseMultiplicity_ne_zero_of_mem
    {N : ℕ} {alpha : Fin N → ℂ} {z : ℂ} (hz : z ∈ squaredBaseSet alpha) :
    squaredBaseMultiplicity alpha z ≠ 0 := by
  classical
  rw [squaredBaseSet, Finset.mem_image] at hz
  rcases hz with ⟨i, hi, rfl⟩
  rw [squaredBaseMultiplicity]
  have hmem : i ∈ Finset.univ.filter (fun j : Fin N ↦ alpha j ^ 2 = alpha i ^ 2) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩
  have hcard :
      (Finset.univ.filter (fun j : Fin N ↦ alpha j ^ 2 = alpha i ^ 2)).card ≠ 0 :=
    Finset.card_ne_zero.mpr ⟨i, hmem⟩
  exact_mod_cast hcard

/-- Grouping repeated squared values with their multiplicities recovers the
original even power sum. -/
lemma weightedPowerSum_squaredBaseMultiplicity
    {N : ℕ} (alpha : Fin N → ℂ) (n : ℕ) :
    weightedPowerSum (squaredBaseSet alpha) (squaredBaseMultiplicity alpha) n =
      ∑ i, alpha i ^ (2 * n) := by
  classical
  rw [weightedPowerSum, squaredBaseSet]
  calc
    ∑ z ∈ Finset.univ.image (fun i ↦ alpha i ^ 2),
        squaredBaseMultiplicity alpha z * z ^ n =
      ∑ z ∈ Finset.univ.image (fun i ↦ alpha i ^ 2),
        ∑ i ∈ Finset.univ with alpha i ^ 2 = z, (alpha i ^ 2) ^ n := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [squaredBaseMultiplicity]
          calc
            ((Finset.univ.filter fun i ↦ alpha i ^ 2 = z).card : ℂ) * z ^ n =
                ∑ _i ∈ Finset.univ.filter (fun i ↦ alpha i ^ 2 = z), z ^ n := by simp
            _ = ∑ i ∈ Finset.univ with alpha i ^ 2 = z, (alpha i ^ 2) ^ n := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i, (alpha i ^ 2) ^ n :=
      Finset.sum_fiberwise_of_maps_to
        (fun i hi ↦ Finset.mem_image.mpr ⟨i, hi, rfl⟩) (fun i ↦ (alpha i ^ 2) ^ n)
    _ = ∑ i, alpha i ^ (2 * n) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_mul]

/-- An `O(q ^ n)` bound for all even power sums forces every spectral
parameter to have norm at most `sqrt q`.

The `IsBigO` hypothesis already allows an arbitrary fixed multiplicative
constant. -/
theorem spectral_norm_le_sqrt_of_evenPowerSum_isBigO
    {N : ℕ} {q : ℝ} (alpha : Fin N → ℂ)
    (hq : 0 ≤ q)
    (hO : (fun n : ℕ ↦ ∑ i, alpha i ^ (2 * n)) =O[atTop]
      fun n : ℕ ↦ q ^ n) :
    ∀ i, ‖alpha i‖ ≤ Real.sqrt q := by
  classical
  have hgrouped :
      weightedPowerSum (squaredBaseSet alpha) (squaredBaseMultiplicity alpha) =O[atTop]
        fun n : ℕ ↦ q ^ n :=
    hO.congr_left fun n ↦ (weightedPowerSum_squaredBaseMultiplicity alpha n).symm
  have hall := weightedPowerSum_base_norm_le hq
    (fun z hz ↦ squaredBaseMultiplicity_ne_zero_of_mem hz) hgrouped
  intro i
  have hmem : alpha i ^ 2 ∈ squaredBaseSet alpha := by
    rw [squaredBaseSet]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hsquare : ‖alpha i ^ 2‖ ≤ q := hall (alpha i ^ 2) hmem
  have hnormSquare : ‖alpha i‖ ^ 2 ≤ q := by
    simpa only [norm_pow] using hsquare
  exact (Real.le_sqrt (norm_nonneg _) hq).2 hnormSquare

/-- It is enough to control the even power sums along any fixed positive
divisible subsequence. -/
theorem spectral_norm_le_sqrt_of_divisibleEvenPowerSum_isBigO
    {N δ : ℕ} {q : ℝ} (alpha : Fin N → ℂ)
    (hq : 0 < q) (hδ : 0 < δ)
    (hO : (fun n : ℕ ↦ ∑ i, alpha i ^ (2 * δ * n)) =O[atTop]
      fun n : ℕ ↦ (q ^ δ) ^ n) :
    ∀ i, ‖alpha i‖ ≤ Real.sqrt q := by
  classical
  have hO' :
      (fun n : ℕ ↦ ∑ i, (alpha i ^ δ) ^ (2 * n)) =O[atTop]
        fun n : ℕ ↦ (q ^ δ) ^ n :=
    hO.congr_left fun n ↦ by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        alpha i ^ (2 * δ * n) = alpha i ^ (δ * (2 * n)) := by
          congr 1
          ac_rfl
        _ = (alpha i ^ δ) ^ (2 * n) := by rw [pow_mul]
  have hpowered := spectral_norm_le_sqrt_of_evenPowerSum_isBigO
    (fun i ↦ alpha i ^ δ) (pow_nonneg hq.le δ) hO'
  intro i
  have hsquared :
      ‖alpha i ^ δ‖ ^ 2 ≤ (Real.sqrt (q ^ δ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hpowered i) 2
  have hpow : (‖alpha i‖ ^ 2) ^ δ ≤ q ^ δ := by
    calc
      (‖alpha i‖ ^ 2) ^ δ = ‖alpha i‖ ^ (2 * δ) := by rw [pow_mul]
      _ = ‖alpha i‖ ^ (δ * 2) := by
        congr 1
        ac_rfl
      _ = (‖alpha i‖ ^ δ) ^ 2 := by rw [pow_mul]
      _ = ‖alpha i ^ δ‖ ^ 2 := by rw [norm_pow]
      _ ≤ (Real.sqrt (q ^ δ)) ^ 2 := hsquared
      _ = q ^ δ := Real.sq_sqrt (pow_nonneg hq.le δ)
  have hnormSquare : ‖alpha i‖ ^ 2 ≤ q :=
    le_of_pow_le_pow_left₀ hδ.ne' hq.le hpow
  exact (Real.le_sqrt (norm_nonneg _) hq.le).2 hnormSquare

/-- The Hasse point-count inequality obtained from a spectral point-count
formula and the even-power-sum asymptotic. -/
theorem abs_pointCount_sub_card_sub_one_le_of_evenPowerSum_isBigO
    (q g pointCount : ℕ) (alpha : Fin (2 * g) → ℂ)
    (hformula : HasPointCountSpectralFormula q g pointCount alpha)
    (hO : (fun n : ℕ ↦ ∑ i, alpha i ^ (2 * n)) =O[atTop]
      fun n : ℕ ↦ (q : ℝ) ^ n) :
    |(pointCount : ℝ) - q - 1| ≤ (2 * g : ℝ) * Real.sqrt q := by
  apply abs_pointCount_sub_card_sub_one_le_of_spectralFormula q g pointCount alpha hformula
  exact spectral_norm_le_sqrt_of_evenPowerSum_isBigO alpha (by positivity) hO

/-- The degree-one Hasse bound follows from a power-sum estimate on any fixed
positive divisible-even subsequence. -/
theorem abs_pointCount_sub_card_sub_one_le_of_divisibleEvenPowerSum_isBigO
    (q g pointCount δ : ℕ) (alpha : Fin (2 * g) → ℂ)
    (hq : 0 < q) (hδ : 0 < δ)
    (hformula : HasPointCountSpectralFormula q g pointCount alpha)
    (hO : (fun n : ℕ ↦ ∑ i, alpha i ^ (2 * δ * n)) =O[atTop]
      fun n : ℕ ↦ ((q : ℝ) ^ δ) ^ n) :
    |(pointCount : ℝ) - q - 1| ≤ (2 * g : ℝ) * Real.sqrt q := by
  apply abs_pointCount_sub_card_sub_one_le_of_spectralFormula q g pointCount alpha hformula
  exact spectral_norm_le_sqrt_of_divisibleEvenPowerSum_isBigO alpha
    (by exact_mod_cast hq) hδ hO

end

end BGS.HasseWeil
