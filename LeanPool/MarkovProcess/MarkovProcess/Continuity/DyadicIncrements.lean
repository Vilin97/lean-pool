/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Time.FiniteGridIncrement
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli


/-!
# Dyadic increment bounds for the Kolmogorov--Chentsov argument

This file merges the following former modules, one section each:

* `DyadicIncrementSummability`: Geometric summability for dyadic increment bounds
* `DyadicBorelCantelli`: Borel--Cantelli for dyadic increment events
* `DyadicIncrementControl`: Almost-sure control of adjacent dyadic increments
* `DyadicThresholdTail`: Geometric tails of dyadic increment thresholds
-/

@[expose] public section

namespace MarkovProcess

section DyadicIncrementSummability

open scoped ENNReal NNReal


/-- The geometric ratio in the dyadic Kolmogorov--Chentsov estimate. -/
noncomputable def dyadicIncrementDecayRatio (p q γ : ℝ) : ℝ≥0 :=
  (2 : ℝ≥0) ^ (1 - q + p * γ)

/-- The admissible Hölder-exponent inequality makes the dyadic ratio strictly less than one. -/
theorem dyadicIncrementDecayRatio_lt_one {p q γ : ℝ} (hp : 0 < p)
    (hγ : γ < (q - 1) / p) : dyadicIncrementDecayRatio p q γ < 1 := by
  have hmul : p * γ < q - 1 := by
    simpa only [mul_comm] using (lt_div_iff₀ hp).mp hγ
  have hexp : 1 - q + p * γ < 0 := by
    linarith only [hmul]
  exact NNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp

/-- The geometric majorant for the dyadic bad-event probabilities is summable. -/
theorem summable_dyadicIncrementDecayRatio {p q γ : ℝ} (M : ℝ≥0) (hp : 0 < p)
    (hγ : γ < (q - 1) / p) :
    Summable (fun n : ℕ ↦ M * dyadicIncrementDecayRatio p q γ ^ n) :=
  (NNReal.summable_geometric (dyadicIncrementDecayRatio_lt_one hp hγ)).mul_left M

/-- The same geometric majorant has finite `ENNReal` total mass, as needed by the first
Borel--Cantelli lemma. -/
theorem tsum_coe_dyadicIncrementDecayRatio_ne_top {p q γ : ℝ} (M : ℝ≥0)
    (hp : 0 < p) (hγ : γ < (q - 1) / p) :
    (∑' n : ℕ, ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞)) ≠ ∞ := by
  rw [ENNReal.tsum_coe_ne_top_iff_summable]
  exact summable_dyadicIncrementDecayRatio M hp hγ

end DyadicIncrementSummability

section DyadicBorelCantelli

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- The level-`n` increment threshold used in the dyadic Kolmogorov--Chentsov argument. -/
noncomputable def dyadicIncrementThreshold (γ : ℝ) (n : ℕ) : ℝ≥0∞ :=
  (((2 : ℝ≥0∞) ^ n)⁻¹) ^ γ

theorem dyadicIncrementThreshold_ne_zero {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    dyadicIncrementThreshold γ n ≠ 0 := by
  unfold dyadicIncrementThreshold
  exact (ENNReal.rpow_eq_zero_iff_of_pos hγ).not.mpr (by simp)

theorem dyadicIncrementThreshold_ne_top {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    dyadicIncrementThreshold γ n ≠ ∞ := by
  unfold dyadicIncrementThreshold
  exact (ENNReal.rpow_eq_top_iff_of_pos hγ).not.mpr (by simp)

/-- Normalization of the level-`n` dyadic union bound: the product of the number of cells with
the Kolmogorov quotient at the level's threshold is exactly `M` times the `n`-th power of the
geometric decay ratio. -/
theorem dyadic_bound_normalization (p q γ : ℝ) (M : ℝ≥0) (n : ℕ) :
    (2 : ℝ≥0∞) ^ n *
        ((M : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ n)⁻¹) ^ q /
          dyadicIncrementThreshold γ n ^ p) =
      ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞) := by
  have hl : (2 : ℝ≥0∞) ^ n *
        ((M : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ n)⁻¹) ^ q /
          dyadicIncrementThreshold γ n ^ p) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · simp
    apply ENNReal.div_ne_top
    · apply ENNReal.mul_ne_top
      · simp
      exact ENNReal.rpow_ne_top_of_ne_zero (by simp) (by simp)
    exact ENNReal.rpow_eq_zero_iff.not.mpr (by
      unfold dyadicIncrementThreshold
      simp)
  have hr : ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞) ≠ ∞ := by
    finiteness
  apply (ENNReal.toReal_eq_toReal_iff' hl hr).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_div, ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_rpow,
    dyadicIncrementThreshold, dyadicIncrementDecayRatio]
  rw [← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  simp? [← Real.rpow_natCast, ← Real.rpow_mul]
  rw [← Real.rpow_neg (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity), div_eq_mul_inv,
    ← Real.rpow_neg (by positivity), ← Real.rpow_mul (by positivity)]
  calc
    2 ^ (n : ℝ) * ((M : ℝ) * 2 ^ (-(n : ℝ) * q) * 2 ^ (-(n : ℝ) * -(γ * p))) =
        (M : ℝ) * (2 ^ (n : ℝ) * 2 ^ (-(n : ℝ) * q) *
          2 ^ (-(n : ℝ) * -(γ * p))) := by ring_nf
    _ = (M : ℝ) * 2 ^ ((n : ℝ) + (-(n : ℝ) * q) + (-(n : ℝ) * -(γ * p))) := by
      rw [Real.rpow_add (by positivity), Real.rpow_add (by positivity)]
    _ = (M : ℝ) * 2 ^ ((1 - q + p * γ) * (n : ℝ)) := by
      congr 1
      ring_nf

/-- The dyadic bad-increment event has a summable geometric majorant. -/
theorem IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_threshold_le
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ) (n : ℕ) :
    P (finiteGridBadIncrement X (unitDyadicGrid n) p (dyadicIncrementThreshold γ n)) ≤
      ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞) := by
  rw [← dyadic_bound_normalization]
  exact IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_le hX n _
    (dyadicIncrementThreshold_ne_zero hγ n) (dyadicIncrementThreshold_ne_top hγ n)

/-- The measures of the dyadic bad-increment events have finite total mass. -/
theorem IsKolmogorovProcess.tsum_measure_unitDyadicGridBadIncrement_threshold_ne_top
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    (∑' n : ℕ,
      P (finiteGridBadIncrement X (unitDyadicGrid n) p (dyadicIncrementThreshold γ n))) ≠ ∞ := by
  exact ne_top_of_le_ne_top
    (tsum_coe_dyadicIncrementDecayRatio_ne_top M hX.p_pos hγq)
    (ENNReal.tsum_le_tsum fun n ↦
      IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_threshold_le hX hγ n)

/-- Almost surely, all sufficiently fine unit dyadic grids avoid the bad-increment event. -/
theorem IsKolmogorovProcess.ae_eventually_notMem_unitDyadicGridBadIncrement_threshold
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in Filter.atTop,
      ω ∉ finiteGridBadIncrement X (unitDyadicGrid n) p (dyadicIncrementThreshold γ n) :=
  MeasureTheory.ae_eventually_notMem
    (IsKolmogorovProcess.tsum_measure_unitDyadicGridBadIncrement_threshold_ne_top
      hX hγ hγq)

end DyadicBorelCantelli

section DyadicIncrementControl

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- Outside the finite-grid bad event, every adjacent increment is strictly below the
specified threshold. -/
theorem edist_adjacent_lt_of_notMem_finiteGridBadIncrement
    {N : ℕ} {T : Type*} {X : T → Ω → E} {grid : Fin (N + 1) → T}
    {p : ℝ} (hp : 0 < p) {ε : ℝ≥0∞} {ω : Ω}
    (hω : ω ∉ finiteGridBadIncrement X grid p ε) (i : Fin N) :
    edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) < ε := by
  rw [← ENNReal.rpow_lt_rpow_iff hp]
  exact lt_of_not_ge fun hi ↦ hω (Set.mem_iUnion.mpr ⟨i, hi⟩)

/-- Almost surely, every adjacent increment on every sufficiently fine unit dyadic grid is
strictly below the level's Kolmogorov--Chentsov threshold. -/
theorem IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_adjacent_lt_threshold
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in Filter.atTop, ∀ i : Fin (2 ^ n),
      edist (X (unitDyadicGrid n i.castSucc) ω)
          (X (unitDyadicGrid n i.succ) ω) < dyadicIncrementThreshold γ n := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_notMem_unitDyadicGridBadIncrement_threshold
      hX hγ hγq] with ω hω
  filter_upwards [hω] with n hn
  intro i
  exact edist_adjacent_lt_of_notMem_finiteGridBadIncrement hX.p_pos hn i

end DyadicIncrementControl

section DyadicThresholdTail

open scoped ENNReal NNReal


/-- The ratio between consecutive dyadic increment thresholds. -/
noncomputable def dyadicIncrementThresholdRatio (γ : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (-γ)

/-- The level-`n` threshold is the `n`th power of the one-level decay ratio. -/
theorem dyadicIncrementThreshold_eq_ratio_pow (γ : ℝ) (n : ℕ) :
    dyadicIncrementThreshold γ n = dyadicIncrementThresholdRatio γ ^ n := by
  unfold dyadicIncrementThreshold dyadicIncrementThresholdRatio
  rw [ENNReal.inv_rpow, ← ENNReal.rpow_natCast_mul, ← ENNReal.rpow_neg,
    ← ENNReal.rpow_mul_natCast]
  congr 2
  ring

/-- Positive exponents make the one-level threshold ratio strictly smaller than one. -/
theorem dyadicIncrementThresholdRatio_lt_one {γ : ℝ} (hγ : 0 < γ) :
    dyadicIncrementThresholdRatio γ < 1 := by
  unfold dyadicIncrementThresholdRatio
  exact ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hγ)

/-- The infinite tail beginning at level `n` has the exact geometric-series value. -/
theorem tsum_dyadicIncrementThreshold_add (γ : ℝ) (n : ℕ) :
    (∑' k : ℕ, dyadicIncrementThreshold γ (n + k)) =
      dyadicIncrementThreshold γ n * (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
  simp_rw [dyadicIncrementThreshold_eq_ratio_pow, pow_add]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- For a positive exponent, every infinite threshold tail has finite `ENNReal` mass. -/
theorem tsum_dyadicIncrementThreshold_add_ne_top {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    (∑' k : ℕ, dyadicIncrementThreshold γ (n + k)) ≠ ∞ := by
  rw [tsum_dyadicIncrementThreshold_add]
  apply ENNReal.mul_ne_top
  · exact dyadicIncrementThreshold_ne_top hγ n
  · exact ENNReal.inv_ne_top.mpr
      (tsub_pos_iff_lt.mpr (dyadicIncrementThresholdRatio_lt_one hγ)).ne'

/-- Every finite tail segment is bounded by the corresponding infinite geometric tail. -/
theorem sum_dyadicIncrementThreshold_add_le (γ : ℝ) (n N : ℕ) :
    ∑ k ∈ Finset.range N, dyadicIncrementThreshold γ (n + k) ≤
      dyadicIncrementThreshold γ n * (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
  calc
    ∑ k ∈ Finset.range N, dyadicIncrementThreshold γ (n + k) ≤
        ∑' k : ℕ, dyadicIncrementThreshold γ (n + k) :=
      ENNReal.sum_le_tsum (Finset.range N)
    _ = dyadicIncrementThreshold γ n *
        (1 - dyadicIncrementThresholdRatio γ)⁻¹ :=
      tsum_dyadicIncrementThreshold_add γ n

end DyadicThresholdTail

end MarkovProcess
