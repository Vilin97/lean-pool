/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import Mathlib.Probability.Moments.Variance
import LeanPool.LinearModel.Ols.QuadForm

/-!
# Convergence in probability

This file introduces the notion of convergence in probability and a few simple
results concerning it.  `TendstoInProbability P f T` says the random sequence `fₙ`
converges to the deterministic sequence `Tₙ` in probability: for every `ε > 0`,
`P {ω | ε < |fₙ ω − Tₙ|} → 0`.

A variant of Mathlib's `TendstoInMeasure`, allowing more familiar statistical
convergence statements, e.g. convergence to a moving sequence (meaning the
difference goes to zero), and standard ways of proving convergence in
statistics (e.g. Chebyshev, Markov).

The main results are the following:

· `TendstoInProbability.of_variance` - via Chebyshev's inequality: mean-zero `L²`
  sequences with vanishing variance tend to `0` in probability
· `TendstoInProbability.of_integral_abs_le` - via Markov's inequality: `L¹` sequences
  with `E|fₙ| ≤ bₙ → 0` tend to `0` in probability
· `TendstoInProbability.normSq'_of_entry` - scalarisation: if `Mₙ → Tₙ`
  entrywise in probability then `aᵀMₙa → aᵀTₙa`.
-/

open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology

namespace LeanPool.LinearModel

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section Results

variable (P : Measure Ω)

/-- `fₙ → Tₙ` in probability (`fₙ →ₚ Tₙ`): for every `ε > 0`, `P {ω | ε < |fₙ ω − Tₙ|} → 0`. -/
def TendstoInProbability (f : (n : ℕ) → Ω → ℝ) (T : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P {ω | ε < |f n ω - T n|}) atTop (𝓝 0)

variable {P}

/-- If `fₙ →ₚ Tₙ` and `gₙ = fₙ` pointwise then `gₙ →ₚ Tₙ`. -/
lemma TendstoInProbability.congr {f g : (n : ℕ) → Ω → ℝ} {T : ℕ → ℝ}
    (h : TendstoInProbability P f T) (hfg : ∀ n ω, f n ω = g n ω) :
    TendstoInProbability P g T := by
  intro ε hε
  have hset : ∀ n, {ω | ε < |g n ω - T n|} = {ω | ε < |f n ω - T n|} := by
    intro n
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hfg n ω]
  simpa only [hset] using h ε hε

/-- If `fₙ →ₚ Tₙ` then `fₙ - Tₙ →ₚ 0`. -/
lemma tendstoInProbability_iff_sub {f : (n : ℕ) → Ω → ℝ} {T : ℕ → ℝ} :
    TendstoInProbability P f T ↔
      TendstoInProbability P (fun n ω => f n ω - T n) (fun _ => 0) := by
  constructor
  · intro h ε hε
    simpa only [sub_zero] using h ε hε
  · intro h ε hε
    simpa only [sub_zero] using h ε hε

/-- If `fₙ →ₚ 0` and `gₙ →ₚ 0` then `fₙ + gₙ →ₚ 0`. -/
lemma TendstoInProbability.add {f g : (n : ℕ) → Ω → ℝ}
    (hf : TendstoInProbability P f (fun _ => 0))
    (hg : TendstoInProbability P g (fun _ => 0)) :
    TendstoInProbability P (fun n ω => f n ω + g n ω) (fun _ => 0) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hsub : ∀ n, {ω | ε < |f n ω + g n ω - 0|} ⊆
      {ω | ε / 2 < |f n ω - 0|} ∪ {ω | ε / 2 < |g n ω - 0|} := by
    intro n ω hω
    rw [Set.mem_ofPred_eq, sub_zero] at hω
    rw [Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq, sub_zero, sub_zero]
    by_contra hcon
    push Not at hcon
    have habs := abs_add_le (f n ω) (g n ω)
    have h1 := hcon.1
    have h2 := hcon.2
    linarith
  have hsum : Tendsto (fun n => P {ω | ε / 2 < |f n ω - 0|}
      + P {ω | ε / 2 < |g n ω - 0|}) atTop (𝓝 0) := by
    simpa using (hf (ε / 2) hε2).add (hg (ε / 2) hε2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => zero_le) (fun n => ?_)
  exact le_trans (measure_mono (hsub n)) (measure_union_le _ _)

/-- If `|fₙ| ≤ |gₙ|` pointwise and `gₙ →ₚ 0` then `fₙ →ₚ 0`. -/
lemma TendstoInProbability.of_abs_le {f g : (n : ℕ) → Ω → ℝ}
    (hle : ∀ n ω, |f n ω| ≤ |g n ω|)
    (hg : TendstoInProbability P g (fun _ => 0)) :
    TendstoInProbability P f (fun _ => 0) := by
  intro ε hε
  have hsub : ∀ n, {ω | ε < |f n ω - 0|} ⊆ {ω | ε < |g n ω - 0|} := by
    intro n ω hω
    rw [Set.mem_ofPred_eq, sub_zero] at hω
    rw [Set.mem_ofPred_eq, sub_zero]
    exact lt_of_lt_of_le hω (hle n ω)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg ε hε)
    (fun n => zero_le) (fun n => measure_mono (hsub n))

/-- If `fₙ →ₚ 0` and `c ∈ ℝ` then `cfₙ →ₚ 0`. -/
lemma TendstoInProbability.const_mul {f : (n : ℕ) → Ω → ℝ} (c : ℝ)
    (hf : TendstoInProbability P f (fun _ => 0)) :
    TendstoInProbability P (fun n ω => c * f n ω) (fun _ => 0) := by
  intro ε hε
  have hc1 : (0 : ℝ) < |c| + 1 := by positivity
  have hε' : (0 : ℝ) < ε / (|c| + 1) := by positivity
  have hsub : ∀ n, {ω | ε < |c * f n ω - 0|} ⊆
      {ω | ε / (|c| + 1) < |f n ω - 0|} := by
    intro n ω hω
    rw [Set.mem_ofPred_eq, sub_zero, abs_mul] at hω
    rw [Set.mem_ofPred_eq, sub_zero, div_lt_iff₀ hc1]
    calc ε < |c| * |f n ω| := hω
      _ ≤ (|c| + 1) * |f n ω| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = |f n ω| * (|c| + 1) := by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hf (ε / (|c| + 1)) hε') (fun n => zero_le) (fun n => measure_mono (hsub n))

/-- A finite sum of sequences tending to `0` in probability tends to `0`. -/
lemma TendstoInProbability.finsetSum {ι : Type*} (s : Finset ι)
    {F : ι → (n : ℕ) → Ω → ℝ}
    (h : ∀ j ∈ s, TendstoInProbability P (F j) (fun _ => 0)) :
    TendstoInProbability P (fun n ω => ∑ j ∈ s, F j n ω) (fun _ => 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro ε hε
      have hset : ∀ n, {ω : Ω | ε < |(∑ j ∈ (∅ : Finset ι), F j n ω) - 0|} = ∅ := by
        intro n
        ext ω
        simp [not_lt, hε.le]
      simp only [hset, measure_empty]
      exact tendsto_const_nhds
  | insert a s ha ih =>
      have hadd := TendstoInProbability.add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      exact hadd.congr fun n ω =>
        (Finset.sum_insert (f := fun i => F i n ω) ha).symm

variable [IsProbabilityMeasure P]

/-- (Chebyshev) If `fₙ` is a sequence of mean-zero, `L²` functions with vanishing variance
then `fₙ →ₚ 0`. -/
lemma TendstoInProbability.of_variance {f : (n : ℕ) → Ω → ℝ}
    (hf_MemL2 : ∀ n, MemLp (f n) 2 P)
    (hmean : ∀ n, P[f n] = 0)
    (hvar : Tendsto (fun n => Var[f n; P]) atTop (𝓝 0)) :
    TendstoInProbability P f (fun _ => 0) := by
  intro ε hε
  have hbound : ∀ n, P {ω | ε < |f n ω - 0|}
      ≤ ENNReal.ofReal (Var[f n; P] / ε ^ 2) := by
    intro n
    have hcheb := meas_ge_le_variance_div_sq (hf_MemL2 n) hε
    rw [hmean n] at hcheb
    refine le_trans (measure_mono fun ω hω => ?_) hcheb
    rw [Set.mem_ofPred_eq, sub_zero] at hω
    rw [Set.mem_ofPred_eq, sub_zero]
    exact le_of_lt hω
  have hdiv : Tendsto (fun n => Var[f n; P] / ε ^ 2) atTop (𝓝 0) := by
    have h := hvar.div_const (ε ^ 2)
    rwa [zero_div] at h
  have hlim : Tendsto (fun n => ENNReal.ofReal (Var[f n; P] / ε ^ 2)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hdiv
    rwa [ENNReal.ofReal_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => zero_le) hbound

/-- (Markov) If `fₙ` is a sequence of `L¹` functions with `E|fₙ| ≤ bₙ → 0`
then `fₙ →ₚ 0`. -/
lemma TendstoInProbability.of_integral_abs_le {f : (n : ℕ) → Ω → ℝ} {b : ℕ → ℝ}
    (hf_int : ∀ n, MemLp (f n) 1 P)
    (habs_f_ub : ∀ n, ∫ ω, |f n ω| ∂P ≤ b n)
    (hb0 : Tendsto b atTop (𝓝 0)) :
    TendstoInProbability P f (fun _ => 0) := by
  intro ε hε
  have hbound : ∀ n, P {ω | ε < |f n ω - 0|} ≤ ENNReal.ofReal (b n / ε) := by
    intro n
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (ae_of_all P fun ω => abs_nonneg (f n ω)) ((hf_int n).integrable le_rfl).abs ε
    have hreal : P.real {ω | ε ≤ |f n ω|} ≤ b n / ε := by
      rw [le_div_iff₀ hε]
      calc P.real {ω | ε ≤ |f n ω|} * ε
          = ε * P.real {ω | ε ≤ |f n ω|} := by ring
        _ ≤ ∫ ω, |f n ω| ∂P := hmarkov
        _ ≤ b n := habs_f_ub n
    have hsub : {ω | ε < |f n ω - 0|} ⊆ {ω | ε ≤ |f n ω|} := by
      intro ω hω
      rw [Set.mem_ofPred_eq, sub_zero] at hω
      exact le_of_lt hω
    calc P {ω | ε < |f n ω - 0|} ≤ P {ω | ε ≤ |f n ω|} := measure_mono hsub
      _ = ENNReal.ofReal (P.real {ω | ε ≤ |f n ω|}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
      _ ≤ ENNReal.ofReal (b n / ε) := ENNReal.ofReal_le_ofReal hreal
  have hdiv : Tendsto (fun n => b n / ε) atTop (𝓝 0) := by
    have h := hb0.div_const ε
    rwa [zero_div] at h
  have hlim : Tendsto (fun n => ENNReal.ofReal (b n / ε)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hdiv
    rwa [ENNReal.ofReal_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => zero_le) hbound

omit [IsProbabilityMeasure P] in
/-- If `Mₙ →ₚ Tₙ` entrywise then for any `a`, `aᵀMₙa →ₚ aᵀTa`. -/
lemma TendstoInProbability.normSq'_of_entry {p : ℕ}
    {M : (n : ℕ) → Ω → Matrix (Fin p) (Fin p) ℝ}
    {T : (n : ℕ) → Matrix (Fin p) (Fin p) ℝ} (a : Fin p → ℝ)
    (h : ∀ i j, TendstoInProbability P (fun n ω => M n ω i j)
      (fun n => T n i j)) :
    TendstoInProbability P (fun n ω => normSq' (M n ω) a)
      (fun n => normSq' (T n) a) := by
  classical
  rw [tendstoInProbability_iff_sub]
  have hterm : ∀ i j : Fin p, TendstoInProbability P
      (fun n ω => a i * (M n ω i j - T n i j) * a j) (fun _ => 0) := by
    intro k ℓ
    have h1 := (tendstoInProbability_iff_sub.mp (h k ℓ)).const_mul (a k * a ℓ)
    exact h1.congr fun n ω => by ring
  have hsum : TendstoInProbability P
      (fun n ω => ∑ k, ∑ ℓ, a k * (M n ω k ℓ - T n k ℓ) * a ℓ)
      (fun _ => 0) := by
    refine TendstoInProbability.finsetSum Finset.univ fun k _ => ?_
    exact TendstoInProbability.finsetSum Finset.univ fun ℓ _ => hterm k ℓ
  refine hsum.congr fun n ω => ?_
  simp only [normSq']
  rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ℓ _ => by ring


end Results

end
end LinearModel
end LeanPool
