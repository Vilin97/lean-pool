/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LocallyUniform
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.PowerSeriesConvergence.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt.Hull

/-!
# Analytic sums on power-series convergence domains

Arbitrary Banach-valued coefficient families converge locally uniformly on the interior of their
absolute-convergence set, and their sum is analytic there. Absolute-convergence sets are
geometrically convex in moduli even at zero coordinates and boundary points. Reference:
[Korevaar–Wiegerinck][KorevaarWiegerinck2017] (2017), Theorem 2.4.2.

## Main results

`powerSeriesSum` is the sum of a Banach-valued power series on its convergence domain.
`hasSumLocallyUniformlyOn_powerSeries` is locally uniform convergence there.
`analyticOnNhd_powerSeriesSum` is analyticity of the sum.
`hasGeometricallyConvexModuli_powerSeriesConvergenceDomain` is geometric convexity of the moduli,
including zero coordinates.

## References

* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
-/

public noncomputable section

open Set Filter
open scoped NNReal Topology BigOperators

namespace SeveralComplexVariables

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]

/-- Nonnegative monomials commute with weighted geometric interpolation, including zeros. -/
theorem prod_geometricCombination_pow (r s : ι → ℝ≥0) (m : ι →₀ ℕ) (a b : ℝ) :
    (∏ i, geometricCombination a b r s i ^ m i) =
      (∏ i, r i ^ m i) ^ a * (∏ i, s i ^ m i) ^ b := by
  simp only [geometricCombination, mul_pow, Finset.prod_mul_distrib]
  congr 1
  · rw [← NNReal.finsetProd_rpow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← NNReal.rpow_mul_natCast, mul_comm, NNReal.rpow_natCast_mul]
  · rw [← NNReal.finsetProd_rpow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← NNReal.rpow_mul_natCast, mul_comm, NNReal.rpow_natCast_mul]

/-- Weighted arithmetic–geometric mean bounds a coefficient times an interpolated monomial. -/
theorem geometric_monomial_le (k : ℝ≥0) (r s : ι → ℝ≥0) (m : ι →₀ ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (k : ℝ) * (∏ i, (geometricCombination a b r s i : ℝ) ^ m i) ≤
      a * ((k : ℝ) * ∏ i, (r i : ℝ) ^ m i) +
      b * ((k : ℝ) * ∏ i, (s i : ℝ) ^ m i) := by
  have he : k * (∏ i, geometricCombination a b r s i ^ m i) =
      (k * ∏ i, r i ^ m i) ^ a * (k * ∏ i, s i ^ m i) ^ b := by
    rw [prod_geometricCombination_pow, NNReal.mul_rpow, NNReal.mul_rpow]
    have hk : k ^ a * k ^ b = k := by
      rw [← NNReal.rpow_add_of_nonneg k ha hb, hab, NNReal.rpow_one]
    calc
      _ = (k ^ a * k ^ b) * ((∏ i, r i ^ m i) ^ a * (∏ i, s i ^ m i) ^ b) := by rw [hk]
      _ = _ := by ring
  have h := NNReal.geom_mean_le_arith_mean2_weighted ⟨a, ha⟩ ⟨b, hb⟩
    (k * ∏ i, r i ^ m i) (k * ∏ i, s i ^ m i) (by ext; exact hab)
  change (k * ∏ i, r i ^ m i) ^ a * (k * ∏ i, s i ^ m i) ^ b ≤ _ at h
  rw [← he] at h
  exact_mod_cast h

/-- The absolute-convergence set has geometrically convex moduli, including boundary points and
points on coordinate hyperplanes. No completeness of the coefficient space is needed. -/
theorem hasGeometricallyConvexModuli_powerSeriesAbsConvergenceSet (c : MvPowerSeries ι F) :
    HasGeometricallyConvexModuli (powerSeriesAbsConvergenceSet c) := by
  rintro r ⟨z, hz, rfl⟩ s ⟨w, hw, rfl⟩ a b ha hb hab
  apply (isCompleteReinhardt_powerSeriesAbsConvergenceSet c).isReinhardt.mem_modulusTrace_iff.mpr
  change Summable (fun m : ι →₀ ℕ => ‖c m‖ *
    ∏ i, ‖(geometricCombination a b (fun i => ‖z i‖₊) (fun i => ‖w i‖₊) i : ℂ)‖ ^ m i)
  apply ((hz.mul_left a).add (hw.mul_left b)).of_nonneg_of_le (fun _ => by positivity)
  intro m
  simpa only [Complex.norm_of_nonneg (NNReal.coe_nonneg _), coe_nnnorm] using
    geometric_monomial_le ‖c m‖₊ (fun i => ‖z i‖₊) (fun i => ‖w i‖₊) m ha hb hab

/-- The convergence domain satisfies the zero-inclusive logarithmic convexity property. -/
theorem hasGeometricallyConvexModuli_powerSeriesConvergenceDomain (c : MvPowerSeries ι F) :
    HasGeometricallyConvexModuli (powerSeriesConvergenceDomain c) :=
  (isLogarithmicallyConvex_powerSeriesConvergenceDomain c).hasGeometricallyConvexModuli
    (isOpen_powerSeriesConvergenceDomain c) (isCompleteReinhardt_powerSeriesConvergenceDomain c)

variable [NormedSpace ℂ F] [CompleteSpace F]

/-- The sum of a coefficient power series; its analytic domain is treated separately. -/
@[expose] def powerSeriesSum (c : MvPowerSeries ι F) (z : ι → ℂ) : F :=
  ∑' m : ι →₀ ℕ, (∏ i, z i ^ m i) • c m

/-- An arbitrary coefficient series converges locally uniformly on its convergence domain. -/
theorem hasSumLocallyUniformlyOn_powerSeries (c : MvPowerSeries ι F) :
    HasSumLocallyUniformlyOn (fun (m : ι →₀ ℕ) z => (∏ i, z i ^ m i) • c m)
      (powerSeriesSum c) (powerSeriesConvergenceDomain c) := by
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z hz
  obtain ⟨r, hr, hzr⟩ := (isReinhardt_powerSeriesConvergenceDomain c).exists_strict_modulus_majorant
    (isOpen_powerSeriesConvergenceDomain c) hz
  let W : Set (ι → ℂ) := {w | ∀ i, ‖w i‖ < (r i : ℝ)}
  have hW : IsOpen W := by
    simpa only [W, ofPred_forall] using
      (isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm
        (continuous_const (y := (r i : ℝ))))
  refine ⟨W, nhdsWithin_le_nhds (hW.mem_nhds (fun i => hzr i)), ?_⟩
  apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
  apply tendstoUniformlyOn_tsum (powerSeriesConvergenceDomain_subset c hr)
  intro m w hw
  simp only [norm_smul, norm_prod, norm_pow]
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
  intro i _
  apply pow_le_pow_left₀ (norm_nonneg _) _
  simpa only [Complex.norm_of_nonneg (NNReal.coe_nonneg _)] using (hw i).le

/-- Compact subsets of the convergence domain have uniform convergence of finite subsums. -/
theorem hasSumUniformlyOn_powerSeries (c : MvPowerSeries ι F)
    {K : Set (ι → ℂ)} (hK : IsCompact K) (hKD : K ⊆ powerSeriesConvergenceDomain c) :
    HasSumUniformlyOn (fun (m : ι →₀ ℕ) z => (∏ i, z i ^ m i) • c m)
      (powerSeriesSum c) K :=
  hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      ((hasSumLocallyUniformlyOn_powerSeries c).mono hKD))

/-- The sum of an arbitrary Banach-valued power series is analytic on its convergence domain. -/
theorem analyticOnNhd_powerSeriesSum (c : MvPowerSeries ι F) :
    AnalyticOnNhd ℂ (powerSeriesSum c) (powerSeriesConvergenceDomain c) := by
  classical
  apply (hasSumLocallyUniformlyOn_powerSeries c).analyticOnNhd_pi _
    (isOpen_powerSeriesConvergenceDomain c)
  intro m z _
  exact (Finset.analyticAt_fun_prod Finset.univ (fun i _ =>
    ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z).pow (m i))).smul analyticAt_const

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
