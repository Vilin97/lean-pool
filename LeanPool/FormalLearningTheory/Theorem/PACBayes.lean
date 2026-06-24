/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.Generalization
import LeanPool.FormalLearningTheory.Complexity.Symmetrization
import LeanPool.FormalLearningTheory.PureMath.KLDivergence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# PAC-Bayes Bounds

McAllester's PAC-Bayes bound for finite hypothesis classes.
The Gibbs learner draws h ~ Q (posterior) and classifies with h.
The bound relates the Gibbs learner's true error to its empirical error
plus a complexity term involving KL(Q‖P).

## Main results

- `pac_bayes_per_hypothesis`: per-hypothesis Hoeffding with prior-weighted tail
- `pac_bayes_all_hypotheses`: simultaneous bound for all h via union bound
- `pac_bayes_finite`: the PAC-Bayes bound (Jensen over Q)

## References

- McAllester, "PAC-Bayesian Model Averaging", COLT 1999
- McAllester, "Simplified PAC-Bayesian Margin Bounds", COLT 2003
-/

universe u

open MeasureTheory Finset

-- ============================================================================
-- Definitions: PAC-Bayes quantities (FinitePMF, klDiv, etc. in MathLib.KLDivergence)
-- ============================================================================

/-- The Gibbs error: expected true error under posterior Q.
    E_{h~Q}[D{x | h(x) ≠ c(x)}]. -/
noncomputable def gibbsError {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H]
    (Q : FinitePMF H) (hs : H → Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X) : ℝ :=
  expectFinitePMF Q (fun h => TrueErrorReal X (hs h) c D)

/-- Empirical Gibbs error: expected empirical error under Q.
    E_{h~Q}[EmpErr(h, S)]. -/
noncomputable def gibbsEmpError {X : Type u}
    {H : Type*} [Fintype H]
    (Q : FinitePMF H) (hs : H → Concept X Bool) (c : Concept X Bool)
    {m : ℕ} (S : Fin m → X) : ℝ :=
  expectFinitePMF Q (fun h =>
    EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool))

-- ============================================================================
-- Phase 2: Per-hypothesis Hoeffding with prior-weighted tail
-- ============================================================================

/-- Per-hypothesis Hoeffding with prior-weighted tail.
    For each h with prior weight P(h), the probability that
    TrueErr(h) exceeds EmpErr(h,S) + √(log(1/(P(h)·δ))/(2m))
    is at most P(h)·δ.

    This is Hoeffding's inequality with t = √(log(1/(P(h)·δ))/(2m)).

    We require the bound parameter t ≤ 1 for Hoeffding's applicability. -/
theorem pac_bayes_per_hypothesis {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hs : H → Concept X Bool) (hhs_meas : ∀ h, Measurable (hs h))
    (P : FinitePMF H) (hP_pos : ∀ h, 0 < P.prob h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h₀ : H)
    (hbound_le_one : Real.sqrt (Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m)) ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { S : Fin m → X |
        TrueErrorReal X (hs h₀) c D >
          EmpiricalError X Bool (hs h₀) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
          Real.sqrt (Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m)) }
      ≤ ENNReal.ofReal (P.prob h₀ * δ) := by
  -- Set up abbreviations
  set t := Real.sqrt (Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m))
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
  -- Positivity facts
  have hPδ_pos : 0 < P.prob h₀ * δ := mul_pos (hP_pos h₀) hδ
  have h_inv_pos : 0 < 1 / (P.prob h₀ * δ) := div_pos one_pos hPδ_pos
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
  have h_denom_pos : 0 < 2 * (↑m : ℝ) := by positivity
  have h_log_nonneg : 0 ≤ Real.log (1 / (P.prob h₀ * δ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hPδ_pos]; simp only [one_mul]
    have h1 : P.prob h₀ ≤ 1 := by
      have := P.prob_sum_one
      calc P.prob h₀ ≤ ∑ h : H, P.prob h :=
            Finset.single_le_sum (fun i _ => P.prob_nonneg i) (Finset.mem_univ h₀)
        _ = 1 := P.prob_sum_one
    nlinarith
  have h_quot_nonneg : 0 ≤ Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m) :=
    div_nonneg h_log_nonneg (le_of_lt h_denom_pos)
  have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
  -- Handle the t = 0 case vs t > 0 case
  by_cases ht_pos_case : t = 0
  case pos =>
    have h_Pδ_ge_one : P.prob h₀ * δ ≥ 1 := by
      have ht_sq_zero : Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m) = 0 := by
        rwa [Real.sqrt_eq_zero h_quot_nonneg] at ht_pos_case
      have h_log_zero : Real.log (1 / (P.prob h₀ * δ)) = 0 := by
        by_contra h_ne
        exact absurd (div_ne_zero h_ne (ne_of_gt h_denom_pos)) (not_not.mpr ht_sq_zero)
      have h_le : 1 / (P.prob h₀ * δ) ≤ 1 := by
        by_contra h_not_le
        push Not at h_not_le
        linarith [Real.log_pos h_not_le]
      have h_ge : 1 ≤ 1 / (P.prob h₀ * δ) := by
        by_contra h_not_ge
        push Not at h_not_ge
        have := Real.log_neg (by linarith [h_inv_pos]) h_not_ge
        linarith [h_log_nonneg]
      have h_inv_eq_one : 1 / (P.prob h₀ * δ) = 1 := le_antisymm h_le h_ge
      rw [div_eq_one_iff_eq (ne_of_gt hPδ_pos)] at h_inv_eq_one; linarith
    calc μ { S | TrueErrorReal X (hs h₀) c D >
            EmpiricalError X Bool (hs h₀) (fun i => (S i, c (S i)))
              (zeroOneLoss Bool) + t }
        ≤ μ Set.univ := μ.mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (P.prob h₀ * δ) := ENNReal.ofReal_le_ofReal h_Pδ_ge_one
  case neg =>
    -- t > 0 case: use Hoeffding
    have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht_pos_case)
    -- The event {TrueErr > EmpErr + t} ⊆ {EmpErr ≤ TrueErr - t}
    have h_sub : { S : Fin m → X |
        TrueErrorReal X (hs h₀) c D >
          EmpiricalError X Bool (hs h₀) (fun i => (S i, c (S i))) (zeroOneLoss Bool) + t }
      ⊆ { xs : Fin m → X | EmpiricalError X Bool (hs h₀) (fun i => (xs i, c (xs i)))
          (zeroOneLoss Bool) ≤ TrueErrorReal X (hs h₀) c D - t } := by
      intro xs hxs
      simp only [Set.mem_setOf_eq] at hxs ⊢
      linarith
    -- Measurability for Hoeffding
    have hmeas : MeasurableSet {x : X | hs h₀ x ≠ c x} :=
      (measurableSet_eq_fun (hhs_meas h₀) hc_meas).compl
    -- Apply hoeffding_one_sided
    have h_hoeff := hoeffding_one_sided D (hs h₀) c m hm t ht_pos hbound_le_one hmeas
    -- Key calculation: exp(-2·m·t²) = P(h₀)·δ
    have h_tsq : t ^ 2 = Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m) := by
      rw [sq, ← Real.sqrt_mul h_quot_nonneg, Real.sqrt_mul_self h_quot_nonneg]
    have h_exp_eq : Real.exp (-2 * ↑m * t ^ 2) = P.prob h₀ * δ := by
      rw [h_tsq]
      rw [show -2 * ↑m * (Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m)) =
            -Real.log (1 / (P.prob h₀ * δ)) from by field_simp]
      rw [Real.exp_neg, Real.exp_log h_inv_pos]
      field_simp
    calc μ { S | TrueErrorReal X (hs h₀) c D >
            EmpiricalError X Bool (hs h₀) (fun i => (S i, c (S i)))
              (zeroOneLoss Bool) + t }
        ≤ μ { xs | EmpiricalError X Bool (hs h₀) (fun i => (xs i, c (xs i)))
            (zeroOneLoss Bool) ≤ TrueErrorReal X (hs h₀) c D - t } := μ.mono h_sub
      _ ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := h_hoeff
      _ = ENNReal.ofReal (P.prob h₀ * δ) := by rw [h_exp_eq]

-- ============================================================================
-- Phase 3: Simultaneous bound via union bound
-- ============================================================================

/-- For a probability measure, μ(S) ≥ 1 - μ(Sᶜ), and hence μ(S) ≥ 1 - δ if μ(Sᶜ) ≤ δ. -/
private lemma prob_ge_one_sub_compl' {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (S : Set Ω) (δ : ENNReal)
    (h : μ Sᶜ ≤ δ) :
    μ S ≥ 1 - δ := by
  rw [ge_iff_le, tsub_le_iff_right]
  calc (1 : ENNReal)
      = μ Set.univ := (MeasureTheory.IsProbabilityMeasure.measure_univ).symm
    _ = μ (S ∪ Sᶜ) := by rw [Set.union_compl_self]
    _ ≤ μ S + μ Sᶜ := MeasureTheory.measure_union_le S Sᶜ
    _ ≤ μ S + δ := add_le_add_right h (μ S)

/-- Simultaneous PAC-Bayes bound: with probability ≥ 1-δ,
    ALL hypotheses h simultaneously satisfy
    TrueErr(h) ≤ EmpErr(h,S) + √(log(1/(P(h)·δ))/(2m)). -/
theorem pac_bayes_all_hypotheses {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H] [Nonempty H]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hs : H → Concept X Bool) (hhs_meas : ∀ h, Measurable (hs h))
    (P : FinitePMF H) (hP_pos : ∀ h, 0 < P.prob h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { S : Fin m → X |
        ∀ h : H,
          TrueErrorReal X (hs h) c D ≤
            EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
            Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) }
      ≥ ENNReal.ofReal (1 - δ) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
  set Good := { S : Fin m → X |
    ∀ h : H,
      TrueErrorReal X (hs h) c D ≤
        EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
        Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) }
  -- Goodᶜ ⊆ ⋃ h, {bad for h}
  have h_compl_sub : Goodᶜ ⊆ ⋃ h : H, { S : Fin m → X |
      TrueErrorReal X (hs h) c D >
        EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
        Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) } := by
    intro S hS
    simp only [Set.mem_compl_iff, Good, Set.mem_setOf_eq, not_forall] at hS
    obtain ⟨h, hh⟩ := hS
    push Not at hh
    exact Set.mem_iUnion.mpr ⟨h, by simp only [Set.mem_setOf_eq]; linarith⟩
  -- Per-hypothesis bounds
  have h_per : ∀ h : H, μ { S : Fin m → X |
      TrueErrorReal X (hs h) c D >
        EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
        Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) }
      ≤ ENNReal.ofReal (P.prob h * δ) := by
    intro h
    set t := Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m))
    by_cases ht1 : t ≤ 1
    · -- Normal case: t ≤ 1, apply per-hypothesis Hoeffding
      exact pac_bayes_per_hypothesis D c hc_meas hs hhs_meas P hP_pos m hm δ hδ hδ1 h ht1
    · -- t > 1 case: bad event is empty (gap ≤ 1 < t)
      push Not at ht1
      have h_empty : { S : Fin m → X |
          TrueErrorReal X (hs h) c D >
            EmpiricalError X Bool (hs h) (fun i => (S i, c (S i)))
              (zeroOneLoss Bool) + t } = ∅ := by
        ext S
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        -- TrueErrorReal ≤ 1 (probability measure)
        have h_true_le_one : TrueErrorReal X (hs h) c D ≤ 1 := by
          simp only [TrueErrorReal, TrueError]
          have h_le : D {x | hs h x ≠ c x} ≤ 1 := by
            calc D {x | hs h x ≠ c x} ≤ D Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
              _ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
          exact ENNReal.toReal_le_of_le_ofReal one_pos.le
            (by rw [ENNReal.ofReal_one]; exact h_le)
        -- EmpiricalError ≥ 0
        have h_emp_nonneg : 0 ≤ EmpiricalError X Bool (hs h)
            (fun i => (S i, c (S i))) (zeroOneLoss Bool) := by
          simp only [EmpiricalError]
          split
          · exact le_refl 0
          · apply div_nonneg
            · apply Finset.sum_nonneg; intro i _
              simp only [zeroOneLoss]; split <;> linarith
            · positivity
        -- gap ≤ 1 ≤ 1 + emp ≤ emp + t (since t > 1 and emp ≥ 0)
        linarith
      rw [h_empty]
      simp only [MeasureTheory.measure_empty]
      exact zero_le
  -- Union bound + ∑ P(h)·δ = δ
  have h_compl_bound : μ Goodᶜ ≤ ENNReal.ofReal δ := by
    calc μ Goodᶜ
        ≤ μ (⋃ h : H, { S | TrueErrorReal X (hs h) c D >
            EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
            Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) }) :=
          μ.mono h_compl_sub
      _ ≤ ∑ h : H, μ { S | TrueErrorReal X (hs h) c D >
            EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
            Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) } :=
          MeasureTheory.measure_iUnion_fintype_le μ _
      _ ≤ ∑ h : H, ENNReal.ofReal (P.prob h * δ) :=
          Finset.sum_le_sum (fun h _ => h_per h)
      _ ≤ ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_sum_of_nonneg
            (fun h _ => le_of_lt (mul_pos (hP_pos h) hδ)),
            ← Finset.sum_mul, P.prob_sum_one, one_mul]
  have h_result := prob_ge_one_sub_compl' μ Good (ENNReal.ofReal δ) h_compl_bound
  rw [ge_iff_le, ENNReal.ofReal_sub _ hδ.le, ENNReal.ofReal_one]
  rwa [ge_iff_le] at h_result

-- ============================================================================
-- Phase 4: The PAC-Bayes bound (Jensen)
-- ============================================================================

/-- Jensen's inequality for √ over a finite PMF: ∑ q_h · √(f_h) ≤ √(∑ q_h · f_h).
    Proof via Cauchy-Schwarz: (∑ q_h √f_h)² ≤ (∑ q_h)(∑ q_h f_h) = ∑ q_h f_h. -/
private lemma jensen_sqrt_finpmf {H : Type*} [Fintype H]
    (Q : FinitePMF H) (f : H → ℝ) (hf : ∀ h, 0 ≤ f h) :
    ∑ h : H, Q.prob h * Real.sqrt (f h) ≤
    Real.sqrt (∑ h : H, Q.prob h * f h) := by
  -- Via the variance identity ∑ q_h (√f_h - c)² ≥ 0 with c = ∑ q_h √f_h,
  -- which expands to c² ≤ ∑ q_h f_h (Cauchy-Schwarz).
  have h_sum_nonneg : 0 ≤ ∑ h : H, Q.prob h * Real.sqrt (f h) := by
    apply Finset.sum_nonneg; intro h _
    exact mul_nonneg (Q.prob_nonneg h) (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq h_sum_nonneg]
  apply Real.sqrt_le_sqrt
  set c := ∑ h : H, Q.prob h * Real.sqrt (f h)
  have h_var_nonneg : 0 ≤ ∑ h : H, Q.prob h * (Real.sqrt (f h) - c) ^ 2 :=
    Finset.sum_nonneg (fun h _ => mul_nonneg (Q.prob_nonneg h) (sq_nonneg _))
  suffices h_sq_le : c ^ 2 ≤ ∑ h : H, Q.prob h * f h by
    linarith
  have h_expand_term : ∀ h : H, Q.prob h * (Real.sqrt (f h) - c) ^ 2 =
      Q.prob h * f h - 2 * Q.prob h * Real.sqrt (f h) * c + Q.prob h * c ^ 2 := by
    intro h
    have hsq : Real.sqrt (f h) * Real.sqrt (f h) = f h := Real.mul_self_sqrt (hf h)
    nlinarith [sq_nonneg (Real.sqrt (f h) - c), Q.prob_nonneg h, sq_nonneg c, hsq]
  have h_sum_qf : ∑ h : H, Q.prob h * (Real.sqrt (f h) - c) ^ 2 =
      ∑ h : H, (Q.prob h * f h - 2 * Q.prob h * Real.sqrt (f h) * c + Q.prob h * c ^ 2) := by
    congr 1; ext h; exact h_expand_term h
  rw [h_sum_qf, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h_var_nonneg
  -- ∑ 2 * Q.prob h * √(f h) * c = 2 * c * c
  have h_sum_mid : ∑ h : H, 2 * Q.prob h * Real.sqrt (f h) * c = 2 * c * c := by
    simp_rw [show ∀ h : H, 2 * Q.prob h * Real.sqrt (f h) * c =
      c * (Q.prob h * Real.sqrt (f h)) * 2 from fun h => by ring]
    rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  -- ∑ Q.prob h * c² = c²
  have h_sum_tail : ∑ h : H, Q.prob h * c ^ 2 = c ^ 2 := by
    simp_rw [show ∀ h : H, Q.prob h * c ^ 2 = c ^ 2 * Q.prob h from fun h => by ring]
    rw [← Finset.mul_sum, Q.prob_sum_one, mul_one]
  rw [h_sum_mid, h_sum_tail] at h_var_nonneg
  linarith [sq_nonneg c]

/-- Auxiliary: on the good event from pac_bayes_all_hypotheses, the Gibbs bound holds
    for any posterior Q. This is the deterministic core of the PAC-Bayes bound. -/
private lemma gibbs_bound_of_pointwise {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H]
    (hs : H → Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X)
    (P : FinitePMF H) (hP_pos : ∀ h, 0 < P.prob h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (S : Fin m → X)
    (hgood : ∀ h : H,
      TrueErrorReal X (hs h) c D ≤
        EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
        Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)))
    (Q : FinitePMF H) :
    gibbsError Q hs c D ≤
      gibbsEmpError Q hs c S +
      Real.sqrt ((crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m)) := by
  unfold gibbsError gibbsEmpError expectFinitePMF
  set g := fun h : H => Real.log (1 / (P.prob h * δ)) / (2 * ↑m)
  have h_step1 : ∑ h : H, Q.prob h * TrueErrorReal X (hs h) c D ≤
      ∑ h : H, Q.prob h * EmpiricalError X Bool (hs h)
        (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
      ∑ h : H, Q.prob h * Real.sqrt (g h) := by
    have : ∀ h : H, Q.prob h * TrueErrorReal X (hs h) c D ≤
        Q.prob h * EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
        Q.prob h * Real.sqrt (g h) := by
      intro h; rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (hgood h) (Q.prob_nonneg h)
    calc ∑ h : H, Q.prob h * TrueErrorReal X (hs h) c D
        ≤ ∑ h : H, (Q.prob h * EmpiricalError X Bool (hs h) (fun i => (S i, c (S i)))
            (zeroOneLoss Bool) + Q.prob h * Real.sqrt (g h)) :=
          Finset.sum_le_sum (fun h _ => this h)
      _ = _ := Finset.sum_add_distrib
  have hg_nonneg : ∀ h : H, 0 ≤ g h := by
    intro h; apply div_nonneg _ (by positivity)
    apply Real.log_nonneg; rw [le_div_iff₀ (mul_pos (hP_pos h) hδ)]
    simp only [one_mul]
    have : P.prob h ≤ 1 :=
      le_trans (Finset.single_le_sum (fun i _ => P.prob_nonneg i) (Finset.mem_univ h))
        (le_of_eq P.prob_sum_one)
    nlinarith
  have h_jensen := jensen_sqrt_finpmf Q g hg_nonneg
  have h_sum_g : ∑ h : H, Q.prob h * g h =
      (crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m) := by
    simp only [g]
    simp_rw [mul_div_assoc']
    rw [← Finset.sum_div]
    congr 1
    unfold crossEntropyFinitePMF
    have h_split : ∀ h : H, Q.prob h * Real.log (1 / (P.prob h * δ)) =
        (if Q.prob h = 0 then 0 else Q.prob h * Real.log (1 / P.prob h)) +
        Q.prob h * Real.log (1 / δ) := by
      intro h
      by_cases hq : Q.prob h = 0
      · simp [hq]
      · simp only [hq, ↓reduceIte]
        rw [show (1 : ℝ) / (P.prob h * δ) = (1 / P.prob h) * (1 / δ) from by ring]
        rw [Real.log_mul (ne_of_gt (div_pos one_pos (hP_pos h)))
          (ne_of_gt (div_pos one_pos hδ))]
        ring
    simp_rw [h_split, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_mul, Q.prob_sum_one, one_mul]
  have h_sqrt_eq : Real.sqrt (∑ h : H, Q.prob h * g h) =
      Real.sqrt ((crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m)) := by
    rw [h_sum_g]
  calc ∑ h : H, Q.prob h * TrueErrorReal X (hs h) c D
      ≤ ∑ h : H, Q.prob h * EmpiricalError X Bool (hs h) (fun i => (S i, c (S i)))
          (zeroOneLoss Bool) +
        ∑ h : H, Q.prob h * Real.sqrt (g h) := h_step1
    _ ≤ ∑ h : H, Q.prob h * EmpiricalError X Bool (hs h) (fun i => (S i, c (S i)))
          (zeroOneLoss Bool) +
        Real.sqrt (∑ h : H, Q.prob h * g h) := by linarith [h_jensen]
    _ = ∑ h : H, Q.prob h * EmpiricalError X Bool (hs h) (fun i => (S i, c (S i)))
          (zeroOneLoss Bool) +
        Real.sqrt ((crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m)) := by
        rw [h_sqrt_eq]

/-- McAllester's PAC-Bayes bound (finite hypothesis class, union-bound version).

    With probability ≥ 1-δ over the sample S of size m, for ALL posteriors Q:

      E_{h~Q}[TrueErr(h)] ≤ E_{h~Q}[EmpErr(h,S)]
        + √((crossEntropyFinitePMF Q P + log(1/δ)) / (2m))

    where crossEntropyFinitePMF Q P = ∑_h Q(h)·log(1/P(h)) = KL(Q‖P) + H(Q).

    This is the union-bound version. The tight change-of-measure version
    replaces crossEntropyFinitePMF with klDivFinitePMF and adds log(m).

    The tighter change-of-measure version (Catoni 2007) is not included here:
      E_Q[TrueErr] ≤ E_Q[EmpErr] + √((KL(Q‖P) + log(2√m/δ))/(2m))

    Reference: McAllester, COLT 1999. -/
theorem pac_bayes_finite {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H] [Nonempty H]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hs : H → Concept X Bool) (hhs_meas : ∀ h, Measurable (hs h))
    (P : FinitePMF H) (hP_pos : ∀ h, 0 < P.prob h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { S : Fin m → X |
        ∀ (Q : FinitePMF H),
          gibbsError Q hs c D ≤
            gibbsEmpError Q hs c S +
            Real.sqrt ((crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m)) }
      ≥ ENNReal.ofReal (1 - δ) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
  set AllHyp := { S : Fin m → X |
    ∀ h : H,
      TrueErrorReal X (hs h) c D ≤
        EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
        Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) }
  set PBEvent := { S : Fin m → X |
    ∀ (Q : FinitePMF H),
      gibbsError Q hs c D ≤
        gibbsEmpError Q hs c S +
        Real.sqrt ((crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m)) }
  -- AllHyp ⊆ PBEvent (deterministic implication)
  have h_sub : AllHyp ⊆ PBEvent := by
    intro S hS Q
    exact gibbs_bound_of_pointwise hs c D P hP_pos m hm δ hδ hδ1 S hS Q
  calc μ PBEvent
      ≥ μ AllHyp := μ.mono h_sub
    _ ≥ ENNReal.ofReal (1 - δ) :=
        pac_bayes_all_hypotheses D c hc_meas hs hhs_meas P hP_pos m hm δ hδ hδ1
