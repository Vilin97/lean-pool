/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.UrysohnsLemma

/-!
# Vague convergence to a probability measure is weak convergence

On a locally compact Polish space, a family of probability measures whose integrals of every
compactly supported continuous test converge to those of a probability measure also converges
against every bounded continuous test.  The reason is that no mass escapes: the limit is a
probability measure, so it is tight, and a compactly supported cutoff with values in `[0, 1]`
captures all but `epsilon` of its mass; convergence of the cutoff integral then forces the
approximating measures to keep all but `epsilon` of their mass on the same compact set, and the
truncation error of a bounded continuous test is at most its norm times the discarded mass.

Main results: `tendsto_integral_boundedContinuous_of_tendsto_compactlySupported`.

Nothing is asserted for families that are not probability measures: for sub-probability measures
the conclusion is false, since mass may escape to infinity.
-/

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction CompactlySupported

namespace MarkovProcess

variable {X : Type*} [MeasurableSpace X]

/-- Tightness in integral form: on a locally compact Polish space, a probability measure has all
but `eps` of its mass captured by the integral of a compactly supported continuous cutoff with
values in `[0, 1]`. -/
theorem exists_compactlySupported_one_sub_lt_integral [PseudoEMetricSpace X]
    [CompleteSpace X] [SecondCountableTopology X] [BorelSpace X] [LocallyCompactSpace X]
    [T2Space X] (mu : Measure X) [IsProbabilityMeasure mu] {eps : ℝ} (heps : 0 < eps) :
    ∃ g : C_c(X, ℝ), (∀ y, g y ∈ Set.Icc (0 : ℝ) 1) ∧ 1 - eps < ∫ y, g y ∂mu := by
  have htight : IsTightMeasureSet ({mu} : Set (Measure X)) := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  obtain ⟨K, hK, hKmu⟩ := htight (ENNReal.ofReal (eps / 2)) (by positivity)
  simp only [Set.mem_singleton_iff, forall_eq] at hKmu
  obtain ⟨g, hgK, -, hgsupp, hg01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  refine ⟨⟨g, hgsupp⟩, hg01, ?_⟩
  show (1 : ℝ) - eps < ∫ y, g y ∂mu
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hKcompl : mu.real Kᶜ ≤ eps / 2 := by
    have h := ENNReal.toReal_mono (by simp) hKmu
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  have hint : Integrable (fun y ↦ g y) mu :=
    g.continuous.integrable_of_hasCompactSupport hgsupp
  have hlow : mu.real K ≤ ∫ y, g y ∂mu := by
    rw [← integral_indicator_one hKmeas]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hKmeas) hint fun y ↦ ?_
    by_cases hy : y ∈ K
    · simp only [Set.indicator_of_mem hy, Pi.one_apply]
      exact le_of_eq (hgK hy).symm
    · simp only [Set.indicator_of_notMem hy]
      exact (hg01 y).1
  have huniv : mu.real K + mu.real Kᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hKmeas, probReal_univ]
  linarith

/-- Truncation error: cutting a bounded continuous `f` down to `f * g` by a cutoff `g` with
values in `[0, 1]` costs at most `‖f‖` times the mass `1 - ∫ g` that the cutoff discards. -/
theorem abs_integral_sub_integral_smul_le [TopologicalSpace X] [OpensMeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (f : X →ᵇ ℝ) (g : C_c(X, ℝ))
    (hg01 : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1) :
    |(∫ y, f y ∂mu) - ∫ y, (f • g) y ∂mu| ≤ ‖f‖ * (1 - ∫ y, g y ∂mu) := by
  have hf : Integrable (fun y ↦ f y) mu := f.integrable mu
  have hg : Integrable (fun y ↦ g y) mu :=
    (map_continuous g).integrable_of_hasCompactSupport g.hasCompactSupport
  have hfg : Integrable (fun y ↦ (f • g) y) mu :=
    (map_continuous (f • g)).integrable_of_hasCompactSupport
      (f • g : C_c(X, ℝ)).hasCompactSupport
  have hbound : ∀ y, ‖f y - (f • g) y‖ ≤ ‖f‖ * (1 - g y) := by
    intro y
    have hy1 : g y ≤ 1 := (hg01 y).2
    have hsub : f y - (f • g) y = f y * (1 - g y) := by
      simp only [CompactlySupportedContinuousMap.smulc_apply, smul_eq_mul]
      ring
    rw [hsub, norm_mul, Real.norm_eq_abs (1 - g y), abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm y) (by linarith)
  have hmaj : Integrable (fun y ↦ ‖f‖ * (1 - g y)) mu :=
    ((integrable_const (1 : ℝ)).sub hg).const_mul ‖f‖
  rw [← integral_sub hf hfg, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hmaj (Eventually.of_forall hbound)).trans_eq ?_
  rw [integral_const_mul, integral_sub (integrable_const (1 : ℝ)) hg, integral_const,
    probReal_univ, smul_eq_mul, mul_one]

/-- **Vague convergence to a probability measure is weak convergence.**  If the integrals of every
compactly supported continuous test against a family of probability measures converge to those
against a probability measure, then the same holds for every bounded continuous test. -/
theorem tendsto_integral_boundedContinuous_of_tendsto_compactlySupported
    [PseudoEMetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [BorelSpace X]
    [LocallyCompactSpace X] [T2Space X] {iota : Type*} {l : Filter iota}
    (mu : iota → Measure X) (nu : Measure X)
    [∀ i, IsProbabilityMeasure (mu i)] [IsProbabilityMeasure nu]
    (h : ∀ g : C_c(X, ℝ), Tendsto (fun i ↦ ∫ y, g y ∂mu i) l (nhds (∫ y, g y ∂nu)))
    (f : X →ᵇ ℝ) : Tendsto (fun i ↦ ∫ y, f y ∂mu i) l (nhds (∫ y, f y ∂nu)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have hnorm : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  have hdpos : 0 < eps / (3 * (‖f‖ + 1)) := by positivity
  obtain ⟨g, hg01, hgint⟩ := exists_compactlySupported_one_sub_lt_integral nu hdpos
  have hsmall : ‖f‖ * (eps / (3 * (‖f‖ + 1))) ≤ eps / 3 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
    have hexpand : eps * (3 * (‖f‖ + 1)) - ‖f‖ * eps * 3 = 3 * eps := by ring
    linarith only [hexpand, heps]
  have htrunc : ∀ᶠ i in l,
      |(∫ y, (f • g) y ∂mu i) - ∫ y, (f • g) y ∂nu| < eps / 3 := by
    have hstep := Metric.tendsto_nhds.mp (h (f • g)) (eps / 3) (by positivity)
    simpa only [Real.dist_eq] using hstep
  have hmass : ∀ᶠ i in l, 1 - (∫ y, g y ∂mu i) < eps / (3 * (‖f‖ + 1)) :=
    Tendsto.eventually_lt_const (by linarith only [hgint])
      (tendsto_const_nhds.sub (h g))
  filter_upwards [htrunc, hmass] with i hitrunc himass
  rw [Real.dist_eq]
  have hkey := abs_integral_sub_integral_smul_le (mu i) f g hg01
  have hkey0 := abs_integral_sub_integral_smul_le nu f g hg01
  have hbound : ‖f‖ * (1 - ∫ y, g y ∂mu i) ≤ ‖f‖ * (eps / (3 * (‖f‖ + 1))) :=
    mul_le_mul_of_nonneg_left himass.le hnorm
  have hbound0 : ‖f‖ * (1 - ∫ y, g y ∂nu) ≤ ‖f‖ * (eps / (3 * (‖f‖ + 1))) :=
    mul_le_mul_of_nonneg_left (by linarith only [hgint]) hnorm
  have htri := abs_sub_le (∫ y, f y ∂mu i) (∫ y, (f • g) y ∂mu i) (∫ y, f y ∂nu)
  have htri0 := abs_sub_le (∫ y, (f • g) y ∂mu i) (∫ y, (f • g) y ∂nu) (∫ y, f y ∂nu)
  have hcomm := abs_sub_comm (∫ y, (f • g) y ∂nu) (∫ y, f y ∂nu)
  linarith only [hkey, hkey0, hitrunc, hbound, hbound0, hsmall, htri, htri0, hcomm]

end MarkovProcess
