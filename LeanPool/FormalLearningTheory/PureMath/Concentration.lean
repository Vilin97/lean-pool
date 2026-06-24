/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance

/-!
# Concentration Inequalities

Pure mathematical infrastructure for concentration inequalities.
No learning-theory types.

## Main definitions

- `BoundedRandomVariable` : typeclass for random variables bounded in [a, b] a.e.
- `chebyshev_majority_bound` : Chebyshev-based majority bound for independent events

## Main results

- `chebyshev_majority_bound`: if k ≥ 9/δ independent events each have probability ≥ 2 / 3,
  then the probability that strictly more than k/2 of them hold is ≥ 1-δ.

## References

- Boucheron, Lugosi, Massart, "Concentration Inequalities", Chapter 2
-/

open MeasureTheory

/-- A random variable f : Ω → ℝ is bounded in [a, b] almost everywhere. -/
class BoundedRandomVariable {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (a b : ℝ) : Prop where
  ae_mem_Icc : ∀ᵐ ω ∂μ, f ω ∈ Set.Icc a b
  measurable : Measurable f

section ClassicalInstances

attribute [local instance] Classical.propDecidable

/-- Chebyshev majority bound: if k ≥ 9/δ independent events each have probability ≥ 2 / 3,
    then the probability that strictly more than k/2 of them hold is ≥ 1-δ.
    Uses indicator random variables, Popoviciu's variance bound, independence for
    variance of sums, and Chebyshev's inequality. -/
lemma chebyshev_majority_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {k : ℕ} {δ : ℝ} (h_delta_pos : 0 < δ)
    (hk : (9 : ℝ) / δ ≤ k)
    (events : Fin k → Set Ω)
    (hevents_meas : ∀ j, MeasurableSet (events j))
    (hindep : ProbabilityTheory.iIndepSet (fun j => events j) μ)
    (hprob : ∀ j, μ (events j) ≥ ENNReal.ofReal (2 / 3)) :
    μ {ω | k < 2 * (Finset.univ.filter (fun j => ω ∈ events j)).card} ≥
      ENNReal.ofReal (1 - δ) := by
  classical
  open MeasureTheory ProbabilityTheory Finset in
  set X : Fin k → Ω → ℝ := fun j => (events j).indicator (fun _ => (1 : ℝ))
  set S : Ω → ℝ := fun ω => ∑ j : Fin k, X j ω
  have hS_count : ∀ ω, S ω = ((univ.filter (fun j => ω ∈ events j)).card : ℝ) := by
    intro ω; simp only [S, X, Set.indicator_apply]
    conv_lhs => arg 2; ext j; rw [show (if ω ∈ events j then (1 : ℝ) else 0) =
      (if ω ∈ events j then 1 else 0 : ℕ) from by split_ifs <;> simp]
    rw [← Nat.cast_sum, Finset.sum_boole]; rfl
  have hindep_fun : iIndepFun (m := fun _ => inferInstance)
      (fun j => (events j).indicator (fun _ => (1 : ℝ))) μ :=
    hindep.iIndepFun_indicator
  have hX_bound : ∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro j; apply Filter.Eventually.of_forall; intro ω
    simp only [X, Set.indicator_apply, Set.mem_Icc]
    split_ifs <;> constructor <;> norm_num
  have hX_meas : ∀ j, AEMeasurable (X j) μ := by
    intro j
    exact (stronglyMeasurable_one.indicator (hevents_meas j)).aestronglyMeasurable.aemeasurable
  have hX_memLp : ∀ j, MemLp (X j) 2 μ := by
    intro j
    exact memLp_of_bounded (hX_bound j)
      (stronglyMeasurable_one.indicator (hevents_meas j)).aestronglyMeasurable 2
  have hvar_bound : ∀ j, ProbabilityTheory.variance (X j) μ ≤ 1 / 4 := by
    intro j
    calc ProbabilityTheory.variance (X j) μ
        ≤ ((1 - 0) / 2) ^ 2 := variance_le_sq_of_bounded (hX_bound j) (hX_meas j)
      _ = 1 / 4 := by norm_num
  have hpairwise : Set.Pairwise (↑(univ : Finset (Fin k)))
      (fun i j => (X i) ⟂ᵢ[μ] (X j)) := by
    intro i _ j _ hij; exact hindep_fun.indepFun hij
  have hvar_S : ProbabilityTheory.variance (∑ j : Fin k, X j) μ ≤ k / 4 := by
    rw [IndepFun.variance_sum (fun i _ => hX_memLp i) hpairwise]
    calc ∑ j : Fin k, ProbabilityTheory.variance (X j) μ
        ≤ ∑ _j : Fin k, (1 : ℝ) / 4 := sum_le_sum (fun j _ => hvar_bound j)
      _ = k * (1 / 4) := by rw [sum_const]; simp [nsmul_eq_mul]
      _ = k / 4 := by ring
  have hk_pos : (0 : ℝ) < ↑k := lt_of_lt_of_le (by positivity : (0 : ℝ) < 9 / δ) hk
  have hX_int : ∀ j, Integrable (X j) μ := fun j => (hX_memLp j).integrable one_le_two
  have hS_memLp : MemLp S 2 μ :=
    memLp_finsetSum univ (fun j (_ : j ∈ univ) => hX_memLp j)
  have hvar_S_fn : ProbabilityTheory.variance S μ ≤ ↑k / 4 := by
    have heq : ProbabilityTheory.variance S μ =
        ProbabilityTheory.variance (∑ j : Fin k, X j) μ := by
      congr 1; ext ω; simp [S, Finset.sum_apply]
    rw [heq]; exact hvar_S
  have hk6_pos : (0 : ℝ) < ↑k / 6 := by positivity
  have hcheb := meas_ge_le_variance_div_sq hS_memLp hk6_pos
  have hcheb_bound : ProbabilityTheory.variance S μ / ((↑k / 6) ^ 2) ≤ δ := by
    calc ProbabilityTheory.variance S μ / ((↑k / 6) ^ 2)
        ≤ (↑k / 4) / ((↑k / 6) ^ 2) :=
          div_le_div_of_nonneg_right hvar_S_fn (sq_nonneg _)
      _ = 9 / ↑k := by field_simp; ring
      _ ≤ δ := by
          rw [div_le_iff₀ hk_pos]
          have h9 : 9 / δ * δ = 9 := div_mul_cancel₀ 9 (ne_of_gt h_delta_pos)
          nlinarith [hk]
  have hbad_le : μ {ω | ↑k / 6 ≤ |S ω - ∫ ω, S ω ∂μ|} ≤ ENNReal.ofReal δ :=
    le_trans hcheb (ENNReal.ofReal_le_ofReal hcheb_bound)
  have hES : ∫ ω, S ω ∂μ ≥ 2 * ↑k / 3 := by
    change ∫ ω, (∑ j : Fin k, X j ω) ∂μ ≥ _
    rw [integral_finsetSum univ (fun j _ => hX_int j)]
    have hEX : ∀ j, ∫ ω, X j ω ∂μ ≥ 2 / 3 := by
      intro j; simp only [X]
      rw [integral_indicator_const (1 : ℝ) (hevents_meas j), smul_eq_mul, mul_one,
        ge_iff_le, ← ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2 / 3)]
      exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one)
        (hprob j).le
    calc ∑ j : Fin k, ∫ ω, X j ω ∂μ
        ≥ ∑ _j : Fin k, (2 : ℝ) / 3 := sum_le_sum (fun j _ => hEX j)
      _ = ↑k * (2 / 3) := by rw [sum_const]; simp [nsmul_eq_mul]
      _ = 2 * ↑k / 3 := by ring
  have hcompl_sub : {ω | ↑k / 2 < S ω}ᶜ ⊆
      {ω | ↑k / 6 ≤ |S ω - ∫ ω, S ω ∂μ|} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω
    simp only [Set.mem_setOf_eq]
    calc ↑k / 6 ≤ ∫ ω, S ω ∂μ - S ω := by linarith
      _ ≤ |S ω - ∫ ω, S ω ∂μ| := by rw [abs_sub_comm]; exact le_abs_self _
  have hcompl_le : μ {ω | ↑k / 2 < S ω}ᶜ ≤ ENNReal.ofReal δ :=
    le_trans (μ.mono hcompl_sub) hbad_le
  have hS_meas : Measurable S := by
    change Measurable (fun ω => ∑ j : Fin k, X j ω)
    exact Finset.measurable_sum _ (fun j _ =>
      (stronglyMeasurable_one.indicator (hevents_meas j)).measurable)
  have hmeas : MeasurableSet {ω | ↑k / 2 < S ω} :=
    measurableSet_lt measurable_const hS_meas
  have hgood : μ {ω | ↑k / 2 < S ω} ≥ ENNReal.ofReal (1 - δ) := by
    rw [ge_iff_le, ENNReal.ofReal_sub _ h_delta_pos.le, ENNReal.ofReal_one,
      ← measure_univ (μ := μ), ← measure_add_measure_compl hmeas,
      tsub_le_iff_right]
    exact add_le_add (le_refl _) hcompl_le
  apply le_trans hgood
  apply μ.mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [hS_count ω] at hω
  have : (↑k : ℝ) < 2 * ↑(univ.filter (fun j => ω ∈ events j)).card := by linarith
  exact_mod_cast this

end ClassicalInstances
