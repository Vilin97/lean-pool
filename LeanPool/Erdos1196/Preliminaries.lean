/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc
-/
import LeanPool.Erdos1196.Basic
import LeanPool.Erdos1196.PreliminariesMertens
import LeanPool.Erdos1196.PreliminariesTailAux
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.AbelSummation

/-!
# Tail estimates for primitive sets above `x`

This file proves the logarithmic tail estimate used later in the Markov-chain arguments.
It combines the arithmetic input from `PrimitiveSetsAboveX.PreliminariesMertens`,
Abel summation, and explicit calculus on the model kernel `1 / log (mt)^2`.
The arithmetic input for the Mertens partial sums lives in
`PrimitiveSetsAboveX.PreliminariesMertens`.

## Main statements

* `tailEstimate`
-/

open scoped ArithmeticFunction BigOperators Topology
open Filter MeasureTheory

namespace PrimitiveSetsAboveX

/-- The kernel `t ↦ 1 / log (m t)^2` that appears in the tail estimate. -/
private noncomputable def tailKernel (m : ℕ) (t : ℝ) : ℝ :=
  (Real.log ((m : ℝ) * t) ^ 2)⁻¹

/-- The truncated coefficients used to start Abel summation at `y`. -/
private noncomputable def tailCutoffCoeff (y q : ℕ) : ℝ :=
  if y ≤ q then Λ q / (q : ℝ) else 0

/-- The `0`-term in `mertensPartialSum` vanishes, so the same sum may start at `0`. -/
private lemma mertensPartialSum_eq_sum_Icc_zero (n : ℕ) :
    mertensPartialSum n = (Finset.Icc 0 n).sum (fun q => Λ q / (q : ℝ)) := by
  have hI : Finset.Ioc 0 n = Finset.Icc 1 n := by
    rfl
  rw [mertensPartialSum, ← Finset.add_sum_Ioc_eq_sum_Icc
    (f := fun q => Λ q / (q : ℝ)) (Nat.zero_le n)]
  simp [hI]

/-- The cutoff coefficients sum to a difference of Mertens partial sums. -/
private lemma tailCutoffCoeff_partialSum {y n : ℕ} (hy0 : 1 ≤ y) (hy : y ≤ n) :
    (Finset.Icc 0 n).sum (tailCutoffCoeff y) =
      mertensPartialSum n - mertensPartialSum (y - 1) := by
  have hfilter :
      (Finset.Icc 0 n).filter (fun q => y ≤ q) = Finset.Icc y n := by
    ext q
    simp
    omega
  have hunion : Finset.Icc 0 n = Finset.Icc 0 (y - 1) ∪ Finset.Icc y n := by
    ext q
    simp
    omega
  have hdisj : Disjoint (Finset.Icc 0 (y - 1)) (Finset.Icc y n) := by
    refine Finset.disjoint_left.mpr ?_
    intro q hq0 hqy
    rcases Finset.mem_Icc.mp hq0 with ⟨_, hq0u⟩
    rcases Finset.mem_Icc.mp hqy with ⟨hqyl, _⟩
    omega
  calc
    (Finset.Icc 0 n).sum (tailCutoffCoeff y)
        = ((Finset.Icc 0 n).filter (fun q => y ≤ q)).sum (fun q => Λ q / (q : ℝ)) := by
            simpa [tailCutoffCoeff] using
              (Finset.sum_filter (s := Finset.Icc 0 n) (p := fun q => y ≤ q)
                (f := fun q => Λ q / (q : ℝ))).symm
    _ = (Finset.Icc y n).sum (fun q => Λ q / (q : ℝ)) := by rw [hfilter]
    _ = (Finset.Icc 0 n).sum (fun q => Λ q / (q : ℝ)) -
          (Finset.Icc 0 (y - 1)).sum (fun q => Λ q / (q : ℝ)) := by
            rw [hunion, Finset.sum_union hdisj]
            ring
    _ = mertensPartialSum n - mertensPartialSum (y - 1) := by
          rw [← mertensPartialSum_eq_sum_Icc_zero, ← mertensPartialSum_eq_sum_Icc_zero]

/-- The cutoff coefficients vanish before the cutoff point. -/
private lemma tailCutoffCoeff_partialSum_floor {y : ℕ} {t : ℝ}
    (hy : 2 ≤ y) (ht : (y : ℝ) ≤ t) :
    (Finset.Icc 0 ⌊t⌋₊).sum (tailCutoffCoeff y) =
      mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1) := by
  refine tailCutoffCoeff_partialSum (by omega) ?_
  exact Nat.le_floor ht

/-- The cutoff coefficients are zero at `0`. -/
private lemma tailCutoffCoeff_zero (y : ℕ) : tailCutoffCoeff y 0 = 0 := by
  by_cases hy : y ≤ 0
  · simp [tailCutoffCoeff, hy]
  · simp [tailCutoffCoeff, hy]

/-- The cutoff coefficients are zero at `1` once `y ≥ 2`. -/
private lemma tailCutoffCoeff_one {y : ℕ} (hy : 2 ≤ y) : tailCutoffCoeff y 1 = 0 := by
  have hy1 : ¬ y ≤ 1 := by omega
  simp [tailCutoffCoeff, hy1]

/-- The kernel is differentiable on the domain relevant to the tail estimate. -/
private lemma hasDerivAt_tailKernel {m : ℕ} {t : ℝ} (hmt : 1 < (m : ℝ) * t) :
    HasDerivAt (tailKernel m) (-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) t := by
  have hm : 0 < (m : ℝ) := by
    by_contra hm
    have hm0 : (m : ℝ) = 0 := by linarith
    rw [hm0, zero_mul] at hmt
    linarith
  convert hasDerivAt_inv_log_sq_mul (c := (m : ℝ)) (t := t) hm hmt using 1
  · funext u
    rw [tailKernel]
    exact (inv_pow (Real.log ((m : ℝ) * u)) 2).symm
  · ring_nf

/-- The derivative formula for the tail kernel. -/
private lemma deriv_tailKernel {m : ℕ} {t : ℝ} (hmt : 1 < (m : ℝ) * t) :
    deriv (tailKernel m) t = -2 / (t * Real.log ((m : ℝ) * t) ^ 3) :=
  (hasDerivAt_tailKernel hmt).deriv

/-- The explicit derivative factor for `tailKernel` is continuous on admissible closed tails. -/
private lemma continuousOn_tailKernelDerivFactor_Ici {m y : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y) :
    ContinuousOn
      (fun t : ℝ => -2 / (t * Real.log ((m : ℝ) * t) ^ 3))
      (Set.Ici (y : ℝ)) := by
  intro t ht
  have ht_pos : 0 < t := by
    have hy0 : (0 : ℝ) < y := by positivity
    exact lt_of_lt_of_le hy0 ht
  have hmt : 1 < (m : ℝ) * t := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hy1 : (1 : ℝ) < y := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hy)
    have ht1 : 1 < t := lt_of_lt_of_le hy1 ht
    nlinarith
  have hlog_ne : Real.log ((m : ℝ) * t) ≠ 0 := (Real.log_pos hmt).ne'
  refine ContinuousWithinAt.div ?_ ?_ ?_
  · exact continuousWithinAt_const.neg
  · have hmul : ContinuousWithinAt (fun x : ℝ => (m : ℝ) * x) (Set.Ici (y : ℝ)) t := by
      simpa [mul_comm] using continuousWithinAt_id.const_mul (m : ℝ)
    exact continuousWithinAt_id.mul
      ((ContinuousWithinAt.log hmul
        (mul_ne_zero
          (by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)))
          ht_pos.ne')).pow 3)
  · exact mul_ne_zero ht_pos.ne' (pow_ne_zero 3 hlog_ne)

/-- The tail kernel is nonnegative. -/
private lemma tailKernel_nonneg (m : ℕ) (t : ℝ) : 0 ≤ tailKernel m t := by
  unfold tailKernel
  positivity

/-- The floor/log discrepancy on a unit interval is bounded by `log 2`. -/
private lemma abs_log_floor_sub_log_le_log_two {t : ℝ} (ht : 2 ≤ t) :
    |Real.log ((⌊t⌋₊ : ℕ) : ℝ) - Real.log t| ≤ Real.log 2 := by
  have hfloor_pos : 0 < ((⌊t⌋₊ : ℕ) : ℝ) := by
    have hfloor_one : (1 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le one_lt_two (Nat.le_floor ht)
    linarith
  have ht_pos : 0 < t := by linarith
  have hfloor_le : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht_pos.le
  have htwo : t ≤ ((⌊t⌋₊ : ℕ) : ℝ) * 2 := by
    have hlt : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
    grind only
  have hsub_nonneg : 0 ≤ Real.log t - Real.log ((⌊t⌋₊ : ℕ) : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hfloor_pos hfloor_le)
  have habs : Real.log ((⌊t⌋₊ : ℕ) : ℝ) - Real.log t ≤ 0 := by linarith
  rw [abs_of_nonpos habs, neg_sub, ← Real.log_div
    (show t ≠ 0 by linarith) (show (((⌊t⌋₊ : ℕ) : ℝ) ≠ 0) by positivity)]
  have hratio_pos : 0 < t / (((⌊t⌋₊ : ℕ) : ℝ)) := by positivity
  refine Real.log_le_log hratio_pos ?_
  exact (div_le_iff₀' hfloor_pos).mpr htwo

/-- The cutoff partial sums vanish below the cutoff. -/
private lemma tailCutoffCoeff_partialSum_eq_zero_of_lt {y : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t < y) :
    (Finset.Icc 0 ⌊t⌋₊).sum (tailCutoffCoeff y) = 0 := by
  have hfloor : ⌊t⌋₊ < y := (Nat.floor_lt ht0).2 ht
  refine Finset.sum_eq_zero ?_
  intro q hq
  have hqle : q ≤ ⌊t⌋₊ := (Finset.mem_Icc.mp hq).2
  have hyq : ¬ y ≤ q := by omega
  simp [tailCutoffCoeff, hyq]

/-- Abel summation for the finite truncations of the tail sum. -/
private lemma tailPartialSum_abel {m y n : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y) (hyn : y ≤ n) :
    (Finset.Icc 0 n).sum (fun q => tailKernel m q * tailCutoffCoeff y q) =
      tailKernel m n * (mertensPartialSum n - mertensPartialSum (y - 1)) -
        ∫ t in (y : ℝ)..n, deriv (tailKernel m) t *
          (mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1)) := by
  have hmn : (2 : ℝ) ≤ n := by exact_mod_cast (le_trans hy hyn)
  have hmy : (y : ℝ) ≤ n := by exact_mod_cast hyn
  have hmt : ∀ {t : ℝ}, t ∈ Set.Icc (2 : ℝ) n → 1 < (m : ℝ) * t := by
    intro t ht
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [ht.1, hm']
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) n, DifferentiableAt ℝ (tailKernel m) t := by
    intro t ht
    exact (hasDerivAt_tailKernel (hmt ht)).differentiableAt
  have hcont :
      ContinuousOn (fun t : ℝ => -2 / (t * Real.log ((m : ℝ) * t) ^ 3))
        (Set.Icc (2 : ℝ) n) := by
    exact (continuousOn_tailKernelDerivFactor_Ici hm (by decide : 2 ≤ 2)).mono
      Set.Icc_subset_Ici_self
  have hcontDeriv : ContinuousOn (deriv (tailKernel m)) (Set.Icc (2 : ℝ) n) := by
    refine ContinuousOn.congr hcont ?_
    intro t ht
    rw [deriv_tailKernel (hmt ht)]
  have hint : MeasureTheory.IntegrableOn (deriv (tailKernel m)) (Set.Icc (2 : ℝ) n) :=
    ContinuousOn.integrableOn_Icc hcontDeriv
  have habel0 := sum_mul_eq_sub_integral_mul₁ (c := tailCutoffCoeff y) (f := tailKernel m)
    (tailCutoffCoeff_zero y) (tailCutoffCoeff_one hy) n hdiff hint
  rw [← intervalIntegral.integral_of_le hmn] at habel0
  have habel := by simpa [Nat.floor_natCast] using habel0
  have hprod_int : MeasureTheory.IntegrableOn
      (fun t => deriv (tailKernel m) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tailCutoffCoeff y k)
      (Set.Icc (2 : ℝ) n) :=
    integrableOn_mul_sum_Icc (c := tailCutoffCoeff y) (m := 0) (a := (2 : ℝ))
      (b := n) (ha := by norm_num) hint
  have hprod_2y : IntervalIntegrable
      (fun t => deriv (tailKernel m) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tailCutoffCoeff y k)
      MeasureTheory.volume (2 : ℝ) y := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (show (2 : ℝ) ≤ y by exact_mod_cast hy)]
    exact hprod_int.mono_set (Set.Icc_subset_Icc_right hmy)
  have hprod_yn : IntervalIntegrable
      (fun t => deriv (tailKernel m) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tailCutoffCoeff y k)
      MeasureTheory.volume (y : ℝ) n := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hmy]
    exact hprod_int.mono_set (Set.Icc_subset_Icc_left (show (2 : ℝ) ≤ y by exact_mod_cast hy))
  rw [← intervalIntegral.integral_add_adjacent_intervals hprod_2y hprod_yn] at habel
  have hzero :
      ∫ t in (2 : ℝ)..y, deriv (tailKernel m) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tailCutoffCoeff y k =
        0 := by
    rw [intervalIntegral.integral_congr_ae (μ := MeasureTheory.volume)
      (g := fun _ => (0 : ℝ))]
    · simp
    · filter_upwards
        [MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume) (a := (2 : ℝ)) (b := y)]
        with t hEq ht
      have htIoc : t ∈ Set.Ioc (2 : ℝ) y := by
        simpa [Set.uIoc_of_le (show (2 : ℝ) ≤ y by exact_mod_cast hy)] using ht
      have hmem : t ∈ Set.Ioo (2 : ℝ) y := hEq.symm.mp htIoc
      rw [tailCutoffCoeff_partialSum_eq_zero_of_lt (by linarith [hmem.1.le]) hmem.2, mul_zero]
  have hyrewrite :
      ∫ t in (y : ℝ)..n, deriv (tailKernel m) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tailCutoffCoeff y k =
        ∫ t in (y : ℝ)..n, deriv (tailKernel m) t *
          (mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1)) := by
    rw [intervalIntegral.integral_congr_ae (μ := MeasureTheory.volume)]
    exact Filter.Eventually.of_forall fun t ht => by
      have hmem : t ∈ Set.Ioc (y : ℝ) n := by
        simpa [Set.uIoc_of_le hmy] using ht
      rw [tailCutoffCoeff_partialSum_floor hy hmem.1.le]
  rw [tailCutoffCoeff_partialSum (by omega) hyn, hzero, hyrewrite] at habel
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using habel

/-- The Mertens error at `⌊t⌋` differs from the continuous `log t` error by at most `log 2`. -/
private lemma abs_mertensPartialSum_floor_sub_log_le {C : ℝ} {t : ℝ}
    (hC : ∀ ⦃u : ℕ⦄, 2 ≤ u →
      |mertensPartialSum u - Real.log (u : ℝ)| ≤ C)
    (ht : 2 ≤ t) :
    |mertensPartialSum ⌊t⌋₊ - Real.log t| ≤ C + Real.log 2 := by
  have hfloor : 2 ≤ ⌊t⌋₊ := Nat.le_floor ht
  calc
    |mertensPartialSum ⌊t⌋₊ - Real.log t|
      ≤ |mertensPartialSum ⌊t⌋₊ - Real.log ((⌊t⌋₊ : ℕ) : ℝ)| +
          |Real.log ((⌊t⌋₊ : ℕ) : ℝ) - Real.log t| := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              abs_sub_le (mertensPartialSum ⌊t⌋₊) (Real.log ((⌊t⌋₊ : ℕ) : ℝ)) (Real.log t)
    _ ≤ C + Real.log 2 := add_le_add (hC hfloor) (abs_log_floor_sub_log_le_log_two ht)

/-- Consecutive logarithms differ by at most `log 2` once the index is at least `2`. -/
private lemma abs_log_natPred_sub_log_le_log_two {y : ℕ} (hy : 2 ≤ y) :
    |Real.log ((y - 1 : ℕ) : ℝ) - Real.log (y : ℝ)| ≤ Real.log 2 := by
  by_cases hy2 : y = 2
  · subst hy2
    have hlog2_nonneg : 0 ≤ Real.log 2 := by positivity
    simp [abs_of_nonneg hlog2_nonneg]
  · have hy3 : 3 ≤ y := by omega
    have hpred_pos_nat : 0 < y - 1 := by omega
    have hpred_pos : 0 < ((y - 1 : ℕ) : ℝ) := by exact_mod_cast hpred_pos_nat
    have hy_pos : 0 < (y : ℝ) := by positivity
    have hy_le : ((y - 1 : ℕ) : ℝ) ≤ y := by
      exact_mod_cast Nat.sub_le y 1
    have hratio : (y : ℝ) / ((y - 1 : ℕ) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hpred_pos]
      have hmul : y ≤ 2 * (y - 1) := by omega
      exact_mod_cast hmul
    have hlog_ratio :
        Real.log ((y : ℝ) / ((y - 1 : ℕ) : ℝ)) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) hratio
    have hlog_le : Real.log (y : ℝ) - Real.log ((y - 1 : ℕ) : ℝ) ≤ Real.log 2 := by
      rwa [Real.log_div (show (y : ℝ) ≠ 0 by positivity)
        (show (((y - 1 : ℕ) : ℝ) ≠ 0) by positivity), sub_eq_add_neg] at hlog_ratio
    have hneg : Real.log ((y - 1 : ℕ) : ℝ) - Real.log (y : ℝ) ≤ 0 := by
      exact sub_nonpos.mpr (Real.log_le_log hpred_pos hy_le)
    rw [abs_of_nonpos hneg, neg_sub]
    exact hlog_le

/-- The predecessor cutoff carries the same uniform Mertens error up to `log 2`. -/
private lemma abs_mertensPartialSum_pred_sub_log_le {C : ℝ}
    (hC : ∀ ⦃u : ℕ⦄, 2 ≤ u →
      |mertensPartialSum u - Real.log (u : ℝ)| ≤ C)
    {y : ℕ} (hy : 2 ≤ y) :
    |mertensPartialSum (y - 1) - Real.log (y : ℝ)| ≤ C + Real.log 2 := by
  by_cases hy2 : y = 2
  · subst hy2
    have hCnonneg : 0 ≤ C := by
      have h₂ := hC (u := 2) (by decide : 2 ≤ 2)
      exact le_trans (abs_nonneg (mertensPartialSum 2 - Real.log (2 : ℝ))) h₂
    have hlog2_pos : 0 < Real.log 2 := by positivity
    have hlog2_nonneg : 0 ≤ Real.log 2 := by positivity
    have h₁ : mertensPartialSum 1 = 0 := by
      simp [mertensPartialSum]
    rw [show (2 - 1 : ℕ) = 1 by decide, h₁, zero_sub]
    norm_num
    rw [abs_of_nonneg hlog2_nonneg]
    linarith
  · have hpred : 2 ≤ y - 1 := by omega
    calc
      |mertensPartialSum (y - 1) - Real.log (y : ℝ)|
        ≤ |mertensPartialSum (y - 1) - Real.log ((y - 1 : ℕ) : ℝ)| +
            |Real.log ((y - 1 : ℕ) : ℝ) - Real.log (y : ℝ)| := by
              exact abs_sub_le (mertensPartialSum (y - 1)) (Real.log ↑(y - 1)) (Real.log ↑y)
      _ ≤ C + Real.log 2 := by
            gcongr
            · exact hC hpred
            · exact abs_log_natPred_sub_log_le_log_two hy

/-- The tail kernel decays to `0` along the naturals. -/
private lemma tendsto_tailKernel_natZero {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => tailKernel m n) atTop (𝓝 0) := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hmul : Tendsto (fun n : ℕ => (m : ℝ) * n) atTop atTop := by
    simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop hm_pos
  have hlog : Tendsto (fun n : ℕ => Real.log ((m : ℝ) * n)) atTop atTop := by
    exact Real.tendsto_log_atTop.comp hmul
  have hinv : Tendsto (fun n : ℕ => (Real.log ((m : ℝ) * n))⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp hlog
  simpa [tailKernel] using hinv.pow 2

/-- The boundary contribution coming from the continuous Mertens error vanishes at infinity. -/
private lemma tendsto_tailKernel_mul_mertensError_zero {m : ℕ} (hm : 1 ≤ m) {C : ℝ}
    (hC : ∀ ⦃u : ℕ⦄, 2 ≤ u →
      |mertensPartialSum u - Real.log (u : ℝ)| ≤ C) :
    Tendsto
      (fun n : ℕ => tailKernel m n * (mertensPartialSum n - Real.log (n : ℝ)))
      atTop (𝓝 0) := by
  have hkernel : Tendsto (fun n : ℕ => C * tailKernel m n) atTop (𝓝 0) := by
    simpa using (tendsto_tailKernel_natZero hm).const_mul C
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        |tailKernel m n * (mertensPartialSum n - Real.log (n : ℝ))| ≤ C * tailKernel m n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hkernel_nonneg : 0 ≤ tailKernel m n := tailKernel_nonneg m n
    rw [abs_mul, abs_of_nonneg hkernel_nonneg]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hC hn) hkernel_nonneg
  have habs :
      Tendsto (fun n : ℕ =>
        |tailKernel m n * (mertensPartialSum n - Real.log (n : ℝ))|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound hkernel
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa using habs

/-- On the admissible tail `t ≥ y`, the logarithmic difference `log t - log y` is nonnegative and
bounded by `log (m t)`. -/
private lemma log_sub_log_bounds {m y : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y) {t : ℝ}
    (ht : (y : ℝ) ≤ t) :
    0 ≤ Real.log t - Real.log (y : ℝ) ∧
      Real.log t - Real.log (y : ℝ) ≤ Real.log ((m : ℝ) * t) := by
  have ht_pos : 0 < t := by
    have hy0 : (0 : ℝ) < y := by positivity
    linarith
  have hy_pos : 0 < (y : ℝ) := by positivity
  constructor
  · exact sub_nonneg.mpr <| Real.log_le_log hy_pos ht
  · have hlog_le : Real.log t ≤ Real.log ((m : ℝ) * t) := by
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hle : t ≤ (m : ℝ) * t := by
        have := mul_le_mul_of_nonneg_right hm1 ht_pos.le
        simpa using this
      exact Real.log_le_log ht_pos hle
    have : Real.log t - Real.log (y : ℝ) ≤ Real.log t := by
      have hy1 : (1 : ℝ) ≤ y := by
        exact_mod_cast (le_trans (by decide : 1 ≤ 2) hy)
      linarith [Real.log_nonneg hy1]
    exact le_trans this hlog_le

/-- The logarithmic boundary term vanishes along the real tail. -/
private lemma tendsto_tailKernel_mul_log_sub_log_zero_aux {m y : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y) :
    Tendsto (fun t : ℝ => tailKernel m t * (Real.log t - Real.log (y : ℝ))) atTop (𝓝 0) := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hmul : Tendsto (fun t : ℝ => (m : ℝ) * t) atTop atTop := by
    simpa [mul_comm] using tendsto_id.const_mul_atTop' hm_pos
  have hlog : Tendsto (fun t : ℝ => Real.log ((m : ℝ) * t)) atTop atTop :=
    Real.tendsto_log_atTop.comp hmul
  have hinv : Tendsto (fun t : ℝ => (Real.log ((m : ℝ) * t))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hbound :
      ∀ᶠ t : ℝ in atTop,
        |tailKernel m t * (Real.log t - Real.log (y : ℝ))| ≤
          (Real.log ((m : ℝ) * t))⁻¹ := by
    filter_upwards [eventually_ge_atTop (max y 2 : ℝ)] with t ht
    have hty : (y : ℝ) ≤ t := le_trans (by exact_mod_cast le_max_left y 2) ht
    have ht2 : (2 : ℝ) ≤ t := le_trans (by exact_mod_cast le_max_right y 2) ht
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmt : 1 < (m : ℝ) * t := by
      nlinarith
    have hkernel_nonneg : 0 ≤ tailKernel m t := tailKernel_nonneg m t
    have hdiff := log_sub_log_bounds hm hy hty
    have hdiff_nonneg : 0 ≤ Real.log t - Real.log (y : ℝ) := hdiff.1
    have hdiff_le : Real.log t - Real.log (y : ℝ) ≤ Real.log ((m : ℝ) * t) := hdiff.2
    rw [abs_of_nonneg (mul_nonneg hkernel_nonneg hdiff_nonneg)]
    calc
      tailKernel m t * (Real.log t - Real.log (y : ℝ))
        ≤ tailKernel m t * Real.log ((m : ℝ) * t) := by
            exact mul_le_mul_of_nonneg_left hdiff_le hkernel_nonneg
      _ = (Real.log ((m : ℝ) * t))⁻¹ := by
            have hlog_ne : Real.log ((m : ℝ) * t) ≠ 0 := by
              exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hmt)
            unfold tailKernel
            field_simp [hlog_ne]
  have habs :
      Tendsto (fun t : ℝ =>
        |tailKernel m t * (Real.log t - Real.log (y : ℝ))|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound hinv
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa using habs

/-- The full boundary term in Abel summation vanishes at infinity. -/
private lemma tendsto_tailKernel_mul_mertensTail_zero {m y : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y)
    {C : ℝ} (hC : ∀ ⦃u : ℕ⦄, 2 ≤ u →
      |mertensPartialSum u - Real.log (u : ℝ)| ≤ C) :
    Tendsto (fun n : ℕ => tailKernel m n * (mertensPartialSum n - mertensPartialSum (y - 1)))
      atTop (𝓝 0) := by
  have h₁ := tendsto_tailKernel_mul_mertensError_zero hm hC
  have h₂ :
      Tendsto (fun n : ℕ => tailKernel m n * (Real.log (n : ℝ) - Real.log (y : ℝ)))
        atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_tailKernel_mul_log_sub_log_zero_aux hm hy).comp tendsto_natCast_atTop_atTop
  have h₃ : Tendsto (fun n : ℕ => tailKernel m n * (Real.log (y : ℝ) - mertensPartialSum (y - 1)))
      atTop (𝓝 0) := by
    simpa [mul_comm] using (tendsto_tailKernel_natZero hm).const_mul
      (Real.log (y : ℝ) - mertensPartialSum (y - 1))
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, Pi.add_apply] using
    (h₁.add h₂).add h₃

/-- On the admissible tail, the logarithm in the kernel is always positive. -/
private lemma one_lt_mul_of_mem_Ioi {m y : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y) {t : ℝ}
    (ht : t ∈ Set.Ioi (y : ℝ)) :
    1 < (m : ℝ) * t := by
  have hy1 : (1 : ℝ) < y := by
    exact_mod_cast lt_of_lt_of_le one_lt_two hy
  have ht1 : 1 < t := lt_trans hy1 ht
  have hm1 : (1 : ℝ) ≤ m := by
    exact_mod_cast hm
  exact one_lt_mul hm1 ht1

/-- Points in the admissible tail are positive. -/
private lemma zero_lt_of_mem_Ioi {y : ℕ} (hy : 2 ≤ y) {t : ℝ} (ht : t ∈ Set.Ioi (y : ℝ)) :
    0 < t := by
  have hy0 : (0 : ℝ) < y := by positivity
  exact lt_trans hy0 ht

/-- The Abel-summation error after subtracting the logarithmic main term is uniformly bounded. -/
private lemma abs_mertensTail_floor_error_le {C : ℝ}
    (hC : ∀ ⦃u : ℕ⦄, 2 ≤ u →
      |mertensPartialSum u - Real.log (u : ℝ)| ≤ C)
    {y : ℕ} (hy : 2 ≤ y) {t : ℝ} (ht : (y : ℝ) ≤ t) :
    |(mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1)) -
        (Real.log t - Real.log (y : ℝ))| ≤ 2 * (C + Real.log 2) := by
  have ht2 : 2 ≤ t :=
    le_trans (by exact_mod_cast hy) ht
  have hfloor := abs_mertensPartialSum_floor_sub_log_le hC ht2
  have hpred := abs_mertensPartialSum_pred_sub_log_le hC hy
  calc
    |(mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1)) -
        (Real.log t - Real.log (y : ℝ))|
      = |(mertensPartialSum ⌊t⌋₊ - Real.log t) -
          (mertensPartialSum (y - 1) - Real.log (y : ℝ))| := by ring_nf
    _ ≤ |mertensPartialSum ⌊t⌋₊ - Real.log t| +
          |mertensPartialSum (y - 1) - Real.log (y : ℝ)| :=
            abs_sub (mertensPartialSum ⌊t⌋₊ - Real.log t)
                  (mertensPartialSum (y - 1) - Real.log ↑y)
    _ ≤ 2 * (C + Real.log 2) := by
          linarith

/--
The explicit derivative factor in the tail kernel is strongly measurable on the admissible tail.
-/
private lemma aestronglyMeasurable_tailKernelDerivFactor {m y : ℕ}
    (hm : 1 ≤ m) (hy : 2 ≤ y) :
    AEStronglyMeasurable
      (fun t : ℝ => -2 / (t * Real.log ((m : ℝ) * t) ^ 3))
      (MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))) := by
  have hcont :
      ContinuousOn
        (fun t : ℝ => -2 / (t * Real.log ((m : ℝ) * t) ^ 3))
        (Set.Ioi (y : ℝ)) :=
    (continuousOn_tailKernelDerivFactor_Ici hm hy).mono Set.Ioi_subset_Ici_self
  exact hcont.aestronglyMeasurable measurableSet_Ioi

/-- The logarithmic main-term integrand is integrable on the tail. -/
private lemma integrableOn_Ioi_deriv_tailKernel_mul_log_sub_log {m y : ℕ}
    (hm : 1 ≤ m) (hy : 2 ≤ y) :
    IntegrableOn
      (fun t => deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)))
      (Set.Ioi (y : ℝ)) := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hmy : 1 < (m : ℝ) * y := by
    have hmy_nat : 2 ≤ m * y := by
      have := Nat.mul_le_mul hm hy
      simpa using this
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hmy_nat)
  have hdom :
      (fun t => deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ))) =ᵐ[
        MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))]
      (fun t =>
        (-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * (Real.log t - Real.log (y : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hmt : 1 < (m : ℝ) * t := one_lt_mul_of_mem_Ioi hm hy ht
    rw [deriv_tailKernel hmt]
  have hmajor :
      IntegrableOn (fun t : ℝ => 2 / (t * Real.log ((m : ℝ) * t) ^ 2)) (Set.Ioi (y : ℝ)) := by
    rw [IntegrableOn]
    simpa [two_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (integrableOn_Ioi_inv_log_sq hm_pos hmy).const_mul (2 : ℝ)
  have hmeas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          (-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * (Real.log t - Real.log (y : ℝ)))
        (MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))) := by
    refine (aestronglyMeasurable_tailKernelDerivFactor hm hy).mul ?_
    refine (show ContinuousOn
      (fun t : ℝ => Real.log t - Real.log (y : ℝ))
      (Set.Ioi (y : ℝ)) from ?_).aestronglyMeasurable measurableSet_Ioi
    intro t ht
    exact ((Real.continuousAt_log (zero_lt_of_mem_Ioi hy ht).ne').sub
      continuousAt_const).continuousWithinAt
  have hbound :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))),
        ‖(-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * (Real.log t - Real.log (y : ℝ))‖ ≤
          2 / (t * Real.log ((m : ℝ) * t) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_of_mem_Ioi hy ht
    have hmt : 1 < (m : ℝ) * t := one_lt_mul_of_mem_Ioi hm hy ht
    have hlog_pos : 0 < Real.log ((m : ℝ) * t) := Real.log_pos hmt
    have hdiff := log_sub_log_bounds hm hy ht.le
    have hdiff_nonneg : 0 ≤ Real.log t - Real.log (y : ℝ) := hdiff.1
    have hdiff_le : Real.log t - Real.log (y : ℝ) ≤ Real.log ((m : ℝ) * t) := hdiff.2
    have hfactor_nonneg : 0 ≤ 2 / (t * Real.log ((m : ℝ) * t) ^ 3) := by
      positivity
    calc
      ‖(-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * (Real.log t - Real.log (y : ℝ))‖
        = (2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * (Real.log t - Real.log (y : ℝ)) := by
            have habs_factor :
                |(-2 / (t * Real.log ((m : ℝ) * t) ^ 3))| =
                  2 / (t * Real.log ((m : ℝ) * t) ^ 3) := by
              have hneg :
                  -2 / (t * Real.log ((m : ℝ) * t) ^ 3) =
                    -(2 / (t * Real.log ((m : ℝ) * t) ^ 3)) := by ring
              rw [hneg, abs_neg, abs_of_nonneg hfactor_nonneg]
            rw [Real.norm_eq_abs, abs_mul, habs_factor, abs_of_nonneg hdiff_nonneg]
      _ ≤ (2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * Real.log ((m : ℝ) * t) :=
            mul_le_mul_of_nonneg_left hdiff_le hfactor_nonneg
      _ = 2 / (t * Real.log ((m : ℝ) * t) ^ 2) := by
            have ht_ne : t ≠ 0 := ht_pos.ne'
            have hlog_ne : Real.log ((m : ℝ) * t) ≠ 0 := hlog_pos.ne'
            field_simp [ht_ne, hlog_ne]
  rw [IntegrableOn]
  refine (Integrable.mono' hmajor hmeas hbound).congr hdom.symm

/-- The logarithmic main term is exactly `1 / log (my)`. -/
private lemma integral_tailKernel_mainTerm {m y : ℕ} (hm : 1 ≤ m) (hy : 2 ≤ y) :
    -∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)) =
      1 / Real.log ((m * y : ℕ) : ℝ) := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hmy : 1 < (m : ℝ) * y := by
    have hmy_nat : 2 ≤ m * y := by
      have := Nat.mul_le_mul hm hy
      simpa using this
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hmy_nat)
  have hu :
      ∀ x ∈ Set.Ioi (y : ℝ),
        HasDerivAt (tailKernel m) (-2 / (x * Real.log ((m : ℝ) * x) ^ 3)) x := by
    intro x hx
    exact hasDerivAt_tailKernel (one_lt_mul_of_mem_Ioi hm hy hx)
  have hv :
      ∀ x ∈ Set.Ioi (y : ℝ),
        HasDerivAt (fun t : ℝ => Real.log t - Real.log (y : ℝ)) (1 / x) x := by
    intro x hx
    rw [one_div]
    exact (Real.hasDerivAt_log (show x ≠ 0 by exact (zero_lt_of_mem_Ioi hy hx).ne')).sub_const
      (Real.log (y : ℝ))
  have huv' :
      IntegrableOn
        ((tailKernel m) * fun t : ℝ => 1 / t)
        (Set.Ioi (y : ℝ)) := by
    simpa [tailKernel, Pi.mul_def, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      integrableOn_Ioi_inv_log_sq hm_pos hmy
  have hu'v :
      IntegrableOn
        ((fun x : ℝ => -2 / (x * Real.log ((m : ℝ) * x) ^ 3)) *
          fun t : ℝ => Real.log t - Real.log (y : ℝ))
        (Set.Ioi (y : ℝ)) := by
    refine (integrableOn_Ioi_deriv_tailKernel_mul_log_sub_log hm hy).congr_fun_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Pi.mul_apply, deriv_tailKernel (one_lt_mul_of_mem_Ioi hm hy ht)]
  have h_zero :
      Tendsto
        ((tailKernel m) * fun t : ℝ => Real.log t - Real.log (y : ℝ))
        (𝓝[>] (y : ℝ)) (𝓝 0) := by
    have hy_pos : 0 < (y : ℝ) := by positivity
    simpa [Pi.mul_def] using
      (tendsto_nhdsWithin_of_tendsto_nhds (hasDerivAt_tailKernel hmy).continuousAt.tendsto).mul
        (tendsto_sub_nhds_zero_iff.mpr <|
          tendsto_nhdsWithin_of_tendsto_nhds (Real.continuousAt_log hy_pos.ne').tendsto)
  have h_inf :
      Tendsto
        ((tailKernel m) * fun t : ℝ => Real.log t - Real.log (y : ℝ))
        atTop (𝓝 0) := by
    simpa [Pi.mul_def] using tendsto_tailKernel_mul_log_sub_log_zero_aux hm hy
  have hparts :
      -∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)) =
        ∫ t in Set.Ioi (y : ℝ), tailKernel m t * (1 / t) := by
    calc
      -∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ))
        = -∫ t in Set.Ioi (y : ℝ), (-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) *
            (Real.log t - Real.log (y : ℝ)) := by
            refine congrArg Neg.neg ?_
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            rw [deriv_tailKernel (one_lt_mul_of_mem_Ioi hm hy ht)]
      _ = ∫ t in Set.Ioi (y : ℝ), tailKernel m t * (1 / t) := by
            simpa [sub_eq_add_neg, Pi.mul_def] using
              (MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_inf).symm
  have hkernel_eq :
      ∫ t in Set.Ioi (y : ℝ), tailKernel m t * (1 / t) =
        ∫ t in Set.Ioi (y : ℝ), (1 : ℝ) / (t * Real.log ((m : ℝ) * t) ^ 2) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_of_mem_Ioi hy ht
    have hmt : 1 < (m : ℝ) * t := one_lt_mul_of_mem_Ioi hm hy ht
    have hlog_ne : Real.log ((m : ℝ) * t) ≠ 0 := (Real.log_pos hmt).ne'
    unfold tailKernel
    field_simp [ht_pos.ne', hlog_ne]
  calc
    -∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ))
      = ∫ t in Set.Ioi (y : ℝ), tailKernel m t * (1 / t) := hparts
    _ = 1 / Real.log ((m * y : ℕ) : ℝ) := by
          rw [hkernel_eq]
          simpa [Nat.cast_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            integral_Ioi_inv_log_sq hm_pos hmy

/-- The logarithmic tail sum satisfies
`tailSum m y = 1 / log (my) + O(log(my)⁻²)` uniformly for `m ≥ 1` and `y ≥ 2`. -/
lemma tailEstimate :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃m y : ℕ⦄, 1 ≤ m → 2 ≤ y →
        |tailSum m y - 1 / Real.log ((m * y : ℕ) : ℝ)| ≤
          C / (Real.log ((m * y : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := mertensEstimate
  refine ⟨2 * (C₀ + Real.log 2), by positivity, ?_⟩
  intro m y hm hy
  let coeff : ℕ → ℝ := fun q => tailKernel m q * tailCutoffCoeff y q
  let partialS : ℕ → ℝ := fun n => ∑ q ∈ Finset.Icc 0 n, coeff q
  let A : ℝ → ℝ := fun t =>
    deriv (tailKernel m) t * (mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1))
  let E : ℝ → ℝ := fun t =>
    (mertensPartialSum ⌊t⌋₊ - mertensPartialSum (y - 1)) -
      (Real.log t - Real.log (y : ℝ))
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hmy : 1 < (m : ℝ) * y := by
    have hmy_nat : 2 ≤ m * y := by
      have := Nat.mul_le_mul hm hy
      simpa using this
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hmy_nat)
  have hcoeff_nonneg : ∀ q : ℕ, 0 ≤ coeff q := by
    intro q
    by_cases hyq : y ≤ q
    · have hmq_nat : 2 ≤ m * q := by
        have := Nat.mul_le_mul hm hyq
        exact le_trans (by omega) this
      have hmq : 1 < ((m * q : ℕ) : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hmq_nat)
      have hkernel_nonneg : 0 ≤ tailKernel m q := tailKernel_nonneg m q
      have hcutoff_nonneg : 0 ≤ tailCutoffCoeff y q := by
        have hq_pos_nat : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) (le_trans hy hyq)
        have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq_pos_nat
        have hΛ_nonneg : 0 ≤ Λ q := ArithmeticFunction.vonMangoldt_nonneg
        rw [tailCutoffCoeff, if_pos hyq]
        exact div_nonneg hΛ_nonneg hq_pos.le
      exact mul_nonneg hkernel_nonneg hcutoff_nonneg
    · simp [coeff, tailCutoffCoeff, hyq]
  have hAeq :
      A =
        (fun t =>
          deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)) +
            deriv (tailKernel m) t * E t) := by
    funext t
    simp [A, E]
    ring
  have hEbound :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))),
        |E t| ≤ 2 * (C₀ + Real.log 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact abs_mertensTail_floor_error_le hC₀ hy ht.le
  have hmain_int :
      IntegrableOn
        (fun t => deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)))
        (Set.Ioi (y : ℝ)) :=
    integrableOn_Ioi_deriv_tailKernel_mul_log_sub_log hm hy
  have hmajor :
      IntegrableOn
        (fun t : ℝ => (2 * (C₀ + Real.log 2)) * (2 / (t * Real.log ((m : ℝ) * t) ^ 3)))
        (Set.Ioi (y : ℝ)) := by
    rw [IntegrableOn]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (integrableOn_Ioi_two_inv_log_cube hm_pos hmy).const_mul (2 * (C₀ + Real.log 2))
  have hderivE_dom :
      (fun t => deriv (tailKernel m) t * E t) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))]
        (fun t => (-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * E t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hmt : 1 < (m : ℝ) * t := one_lt_mul_of_mem_Ioi hm hy ht
    rw [deriv_tailKernel hmt]
  have hderivE_bound :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))),
        ‖deriv (tailKernel m) t * E t‖ ≤
          (2 * (C₀ + Real.log 2)) * (2 / (t * Real.log ((m : ℝ) * t) ^ 3)) := by
    filter_upwards [hEbound, ae_restrict_mem measurableSet_Ioi] with t htE ht
    have hmt : 1 < (m : ℝ) * t := one_lt_mul_of_mem_Ioi hm hy ht
    have hfactor_nonneg : 0 ≤ 2 / (t * Real.log ((m : ℝ) * t) ^ 3) := by
      have ht_pos : 0 < t := zero_lt_of_mem_Ioi hy ht
      have hlog_pos : 0 < Real.log ((m : ℝ) * t) := Real.log_pos hmt
      positivity
    calc
      ‖deriv (tailKernel m) t * E t‖
        = ‖(-2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * E t‖ := by
            rw [deriv_tailKernel hmt]
      _ = |(-2 / (t * Real.log ((m : ℝ) * t) ^ 3))| * |E t| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ (2 / (t * Real.log ((m : ℝ) * t) ^ 3)) * (2 * (C₀ + Real.log 2)) := by
            have hneg :
                -2 / (t * Real.log ((m : ℝ) * t) ^ 3) =
                  -(2 / (t * Real.log ((m : ℝ) * t) ^ 3)) := by ring
            rw [hneg, abs_neg, abs_of_nonneg hfactor_nonneg]
            exact mul_le_mul_of_nonneg_left htE hfactor_nonneg
      _ = (2 * (C₀ + Real.log 2)) * (2 / (t * Real.log ((m : ℝ) * t) ^ 3)) := by ring
  have herr_int :
      IntegrableOn (fun t => deriv (tailKernel m) t * E t) (Set.Ioi (y : ℝ)) := by
    have hmeas :
        AEStronglyMeasurable (fun t => deriv (tailKernel m) t * E t)
          (MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))) := by
      have hE_meas :
          AEStronglyMeasurable E (MeasureTheory.volume.restrict (Set.Ioi (y : ℝ))) := by
        measurability
      exact ((aestronglyMeasurable_tailKernelDerivFactor hm hy).mul hE_meas).congr hderivE_dom.symm
    rw [IntegrableOn] at hmajor ⊢
    exact Integrable.mono' hmajor hmeas hderivE_bound
  have hA_int : IntegrableOn A (Set.Ioi (y : ℝ)) := by
    rw [IntegrableOn, hAeq]
    change Integrable
      ((fun t : ℝ => deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ))) +
        fun t : ℝ => deriv (tailKernel m) t * E t) _
    rw [IntegrableOn] at hmain_int herr_int
    exact hmain_int.add herr_int
  have hpartial :
      Tendsto partialS atTop (𝓝 (-∫ t in Set.Ioi (y : ℝ), A t)) := by
    refine Tendsto.congr' ?_ (by
      simpa using
        (tendsto_tailKernel_mul_mertensTail_zero hm hy hC₀).sub
          (intervalIntegral_tendsto_integral_Ioi
            (y : ℝ) hA_int tendsto_natCast_atTop_atTop))
    filter_upwards [eventually_ge_atTop y] with n hn
    simp [partialS, coeff, A, tailPartialSum_abel hm hy hn]
  have hcoeff_sum :
      HasSum coeff (-∫ t in Set.Ioi (y : ℝ), A t) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg hcoeff_nonneg _).2 ?_
    refine Tendsto.congr' ?_ (hpartial.comp (tendsto_sub_atTop_nat 1))
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [partialS, Nat.range_eq_Icc_zero_sub_one n (by omega)]
  have htail :
      tailSum m y = -∫ t in Set.Ioi (y : ℝ), A t := by
    have hcoeff_eq :
        coeff = fun q : ℕ =>
          if y ≤ q then
            Λ q / ((q : ℝ) * Real.log ((m * q : ℕ) : ℝ) ^ 2)
          else 0 := by
      funext q
      unfold coeff
      by_cases hyq : y ≤ q
      · have hcast : ((m : ℝ) * q) = ((m * q : ℕ) : ℝ) := by
          norm_num [Nat.cast_mul]
        rw [if_pos hyq, tailCutoffCoeff, if_pos hyq]
        unfold tailKernel
        rw [hcast]
        field_simp
      · simp [tailCutoffCoeff, hyq]
    calc
      tailSum m y = ∑' q : ℕ, coeff q := by simp [tailSum, hcoeff_eq]
      _ = -∫ t in Set.Ioi (y : ℝ), A t := hcoeff_sum.tsum_eq
  have hmain :
      -∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)) =
        1 / Real.log ((m * y : ℕ) : ℝ) :=
    integral_tailKernel_mainTerm hm hy
  have htail_split :
      tailSum m y - 1 / Real.log ((m * y : ℕ) : ℝ) =
        -∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * E t := by
    have hmain' :
        ∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * (Real.log t - Real.log (y : ℝ)) =
          -(1 / Real.log ((m * y : ℕ) : ℝ)) := by
      linarith [hmain]
    rw [htail, hAeq, integral_add hmain_int herr_int, hmain']
    ring
  calc
    |tailSum m y - 1 / Real.log ((m * y : ℕ) : ℝ)|
      = |∫ t in Set.Ioi (y : ℝ), deriv (tailKernel m) t * E t| := by
          rw [htail_split, abs_neg]
    _ ≤ ∫ t in Set.Ioi (y : ℝ), ‖deriv (tailKernel m) t * E t‖ := by
          simpa using
            (norm_integral_le_integral_norm
              (μ := MeasureTheory.volume.restrict (Set.Ioi (y : ℝ)))
              (fun t : ℝ => deriv (tailKernel m) t * E t))
    _ ≤
        ∫ t in Set.Ioi (y : ℝ),
          (2 * (C₀ + Real.log 2)) * (2 / (t * Real.log ((m : ℝ) * t) ^ 3)) := by
          exact setIntegral_mono_ae_restrict herr_int.norm hmajor hderivE_bound
    _ = (2 * (C₀ + Real.log 2)) * (1 / Real.log ((m * y : ℕ) : ℝ)) ^ 2 := by
          rw [integral_const_mul]
          simpa [Nat.cast_mul] using congrArg (fun z => (2 * (C₀ + Real.log 2)) * z)
            (integral_Ioi_two_inv_log_cube hm_pos hmy)
    _ = (2 * (C₀ + Real.log 2)) / (Real.log ((m * y : ℕ) : ℝ)) ^ 2 := by
          field_simp

end PrimitiveSetsAboveX
