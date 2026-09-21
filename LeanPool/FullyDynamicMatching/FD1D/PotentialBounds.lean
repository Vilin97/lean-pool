/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Convex.Jensen
import LeanPool.FullyDynamicMatching.FD1D.Potential
import LeanPool.FullyDynamicMatching.FD1D.Parameters

/-! # Potential Bounds -/

namespace FD1D

noncomputable section

open Set intervalIntegral
open scoped BigOperators

/-! ## Bounds for the harmonic potential -/

/-- The node potential is nonnegative when the regularization is positive. -/
theorem harmonicPotential_nonneg {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 ≤ harmonicPotential a k := by
  unfold harmonicPotential
  apply Finset.sum_nonneg
  intro j hj
  simp only [Finset.mem_Icc] at hj
  positivity

/--
The shifted harmonic sum is bounded by its integral:
`sum_{j=1}^k 1 / (a+j) ≤ log (1+k/a)`.
-/
theorem harmonicPotential_le_log_one_add {a : ℝ} (ha : 0 < a) (k : ℕ) :
    harmonicPotential a k ≤ Real.log (1 + (k : ℝ) / a) := by
  have hanti :
      AntitoneOn (fun x : ℝ => (a + x)⁻¹)
        (Icc 0 ((0 : ℝ) + (k : ℝ))) := by
    intro x hx y hy hxy
    exact (inv_le_inv₀ (add_pos_of_pos_of_nonneg ha hy.1)
      (add_pos_of_pos_of_nonneg ha hx.1)).2 (by linarith)
  have hsum :
      (∑ i ∈ Finset.range k, (a + (i + 1 : ℕ))⁻¹) ≤
        ∫ x in (0 : ℝ)..(k : ℝ), (a + x)⁻¹ := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      hanti.sum_le_integral (x₀ := (0 : ℝ)) (a := k)
  have hpot :
      harmonicPotential a k =
        ∑ i ∈ Finset.range k, (a + (i + 1 : ℕ))⁻¹ := by
    clear hanti hsum
    induction k with
    | zero => simp
    | succ k ih =>
        rw [harmonicPotential_succ, Finset.sum_range_succ, ih]
        congr 1
        simp only [Nat.cast_add, Nat.cast_one]
        ring
  have hint :
      (∫ x in (0 : ℝ)..(k : ℝ), (a + x)⁻¹) =
        Real.log (1 + (k : ℝ) / a) := by
    calc
      (∫ x in (0 : ℝ)..(k : ℝ), (a + x)⁻¹) =
          ∫ x in a..a + k, x⁻¹ := by
            simpa only [add_zero] using
              (integral_comp_add_left (fun x : ℝ => x⁻¹) a :
                (∫ x in (0 : ℝ)..(k : ℝ), (a + x)⁻¹) =
                  ∫ x in a + 0..a + k, x⁻¹)
      _ = Real.log ((a + k) / a) :=
        integral_inv_of_pos ha (by positivity)
      _ = Real.log (1 + (k : ℝ) / a) := by
        congr 1
        field_simp
  rw [hpot]
  exact hsum.trans_eq hint

/-! ## Global potential bounds -/

/-- Every global harmonic potential is nonnegative. -/
theorem globalHarmonicPotential_nonneg
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    (ha : 0 < a) :
    0 ≤ globalHarmonicPotential L a N := by
  unfold globalHarmonicPotential
  apply Finset.sum_nonneg
  intro d hd
  apply Finset.sum_nonneg
  intro v hv
  exact mul_nonneg (sq_nonneg _) (harmonicPotential_nonneg ha _)

/--
If all node counts are at most `m`, then the global potential is at most
`log (1 + m/a)`.
-/
theorem globalHarmonicPotential_le_log_one_add
    {L m : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    (ha : 0 < a) (hN : ∀ d v, N d v ≤ m) :
    globalHarmonicPotential L a N ≤
      Real.log (1 + (m : ℝ) / a) := by
  have hquot : 0 ≤ (m : ℝ) / a :=
    div_nonneg (Nat.cast_nonneg m) ha.le
  have harg : (1 : ℝ) ≤ 1 + (m : ℝ) / a := by linarith
  have hlog : 0 ≤ Real.log (1 + (m : ℝ) / a) :=
    Real.log_nonneg harg
  have hnode (d : ℕ) (v : DyadicNode d) :
      harmonicPotential a (N d v) ≤ Real.log (1 + (m : ℝ) / a) := by
    calc
      harmonicPotential a (N d v) ≤
          Real.log (1 + (N d v : ℝ) / a) :=
        harmonicPotential_le_log_one_add ha _
      _ ≤ Real.log (1 + (m : ℝ) / a) := by
        apply Real.strictMonoOn_log.monotoneOn
        · exact Set.mem_Ioi.mpr (by positivity)
        · exact Set.mem_Ioi.mpr (by positivity)
        · have hcast : (N d v : ℝ) ≤ (m : ℝ) :=
            Nat.cast_le.mpr (hN d v)
          simpa [add_comm] using
            add_le_add_left
              (div_le_div_of_nonneg_right hcast ha.le) 1
  calc
    globalHarmonicPotential L a N ≤
        nonrootMassSqSum L * Real.log (1 + (m : ℝ) / a) := by
      unfold globalHarmonicPotential nonrootMassSqSum
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_left (hnode _ _) (sq_nonneg _)
    _ ≤ Real.log (1 + (m : ℝ) / a) := by
      rw [sum_nonroot_nodeMass_sq]
      have hpow : 0 < (2 : ℝ) ^ L := by positivity
      nlinarith [one_div_pos.mpr hpow]

/-- The two-sided global potential estimate used in the transient argument. -/
theorem globalHarmonicPotential_bounds
    {L m : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    (ha : 0 < a) (hN : ∀ d v, N d v ≤ m) :
    0 ≤ globalHarmonicPotential L a N ∧
      globalHarmonicPotential L a N ≤
        Real.log (1 + (m : ℝ) / a) :=
  ⟨globalHarmonicPotential_nonneg ha,
    globalHarmonicPotential_le_log_one_add ha hN⟩

/-! ## The logarithmic budget for the chosen parameter -/

/-- The chosen parameter dominates `200 * log (1 + m/a)`. -/
theorem two_hundred_mul_log_one_add_le_parameterA
    {m : ℕ} (hm : 1 ≤ m) :
    200 * Real.log
        (1 + (m : ℝ) / (parameterA m : ℝ)) ≤ parameterA m := by
  have ha : 0 < (parameterA m : ℝ) := parameterA_cast_pos hm
  have hratio : (m : ℝ) / parameterA m ≤ m := by
    have haone : (1 : ℝ) ≤ parameterA m := by
      exact_mod_cast (parameterA_pos hm)
    calc
      (m : ℝ) / parameterA m ≤ (m : ℝ) / 1 :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg m) zero_lt_one haone
      _ = m := by ring
  have hlog_m :
      Real.log (1 + (m : ℝ) / parameterA m) ≤
        Real.log ((m + 1 : ℕ) : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by positivity)
    · norm_num at hratio ⊢
      linarith
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlog_nat_nonneg :
      0 ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 1 by omega))
  have hlog_le_logb :
      Real.log ((m + 1 : ℕ) : ℝ) ≤
        Real.logb 2 ((m + 1 : ℕ) : ℝ) := by
    rw [← Real.log_div_log]
    apply (le_div_iff₀ hlog_two_pos).2
    nlinarith
  have hlogb_le_clog :
      Real.logb 2 ((m + 1 : ℕ) : ℝ) ≤
        (Nat.clog 2 (m + 1) : ℝ) := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.le_ceil _
  calc
    200 * Real.log
          (1 + (m : ℝ) / (parameterA m : ℝ)) ≤
        200 * (Nat.clog 2 (m + 1) : ℝ) := by
      gcongr
      exact hlog_m.trans (hlog_le_logb.trans hlogb_le_clog)
    _ = parameterA m := by
      simp [parameterA]

/-- Divided form of the logarithmic budget appearing in Section 5. -/
theorem two_hundred_mul_log_one_add_div_parameterA_le_one
    {m : ℕ} (hm : 1 ≤ m) :
    200 * Real.log
        (1 + (m : ℝ) / (parameterA m : ℝ)) /
        (parameterA m : ℝ) ≤ 1 := by
  apply (div_le_iff₀ (parameterA_cast_pos hm)).2
  simpa using two_hundred_mul_log_one_add_le_parameterA hm

/-! ## Finite Jensen helper -/

/-- Jensen's inequality for the square root of a nonnegative finite average. -/
theorem finite_average_sqrt_le_sqrt_average
    {T : ℕ} (hT : 0 < T) (f : ℕ → ℝ)
    (hf : ∀ t < T, 0 ≤ f t) :
    (∑ t ∈ Finset.range T, Real.sqrt (f t)) / T ≤
      Real.sqrt ((∑ t ∈ Finset.range T, f t) / T) := by
  let w : ℕ → ℝ := fun _ => 1 / (T : ℝ)
  have hw0 : ∀ t ∈ Finset.range T, 0 ≤ w t := by
    intro t ht
    dsimp [w]
    positivity
  have hw1 : ∑ t ∈ Finset.range T, w t = 1 := by
    simp [w, hT.ne']
  have hmem : ∀ t ∈ Finset.range T, f t ∈ Ici (0 : ℝ) := by
    intro t ht
    exact hf t (Finset.mem_range.mp ht)
  have hjensen :=
    Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
      hw0 hw1 hmem
  calc
    (∑ t ∈ Finset.range T, Real.sqrt (f t)) / T =
        ∑ t ∈ Finset.range T, w t * Real.sqrt (f t) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [w, div_eq_mul_inv, one_mul]
      ring
    _ ≤ Real.sqrt (∑ t ∈ Finset.range T, w t * f t) := by
      simpa only [smul_eq_mul, Function.comp_apply] using hjensen
    _ = Real.sqrt ((∑ t ∈ Finset.range T, f t) / T) := by
      congr 1
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [w, div_eq_mul_inv, one_mul]
      ring

end

end FD1D
