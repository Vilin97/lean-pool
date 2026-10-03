/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.HermiteIntegrals
public import LeanPool.Zeta5Irrational.Zeta5
public import LeanPool.Zeta5Irrational.Construction
import LeanPool.Zeta5Irrational.HermiteIBP
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # Hermite's formula at `s = 5` for integer arguments

`∫₀^∞ w(y) / (y² + j²) dy = j⁴ (ζ(5) - H_j^{(5)}) - 1/4 + 1/(2j)` for `j ≥ 1`,
i.e. the pole moments (2.3) of the paper (Proposition 2.2).
-/

public section

open Filter Topology Set MeasureTheory Finset

namespace Zeta5Irrational

/-- `∫₀^∞ y/(y² + a²)² dy = 1/(2a²)`. -/
lemma integral_y_div_sq_sq {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi 0, y / (y ^ 2 + a ^ 2) ^ 2 = 1 / (2 * a ^ 2) := by
  have hd :
    ∀ y : ℝ, HasDerivAt (fun y : ℝ => -1 / (2 * (y ^ 2 + a ^ 2))) (y / (y ^ 2 + a ^ 2) ^ 2) y := by
    intro y
    have hne : 2 * (y ^ 2 + a ^ 2) ≠ 0 := by positivity
    have :=
      (hasDerivAt_const y (-1 : ℝ)).div (((hasDerivAt_pow 2 y).add_const (a ^ 2)).const_mul 2) hne
    refine this.congr_deriv ?_
    field_simp
    ring
  have hint : IntegrableOn (fun y : ℝ => y / (y ^ 2 + a ^ 2) ^ 2) (Ioi 0) := by
    refine
      integrableOn_of_le_inv_sq ha (C := 1 / (2 * a))
        ((by fun_prop : Continuous fun y : ℝ => y).div (by fun_prop)
            (fun y => by positivity)).aestronglyMeasurable
        (fun y hy => ?_)
    rw [abs_of_nonneg (by positivity)]
    have h2 : y / (y ^ 2 + a ^ 2) ≤ 1 / (2 * a) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_nonneg (y - a)]
    calc
      y / (y ^ 2 + a ^ 2) ^ 2 = (y / (y ^ 2 + a ^ 2)) * (1 / (y ^ 2 + a ^ 2)) := by field_simp
      _ ≤ (1 / (2 * a)) * (1 / (y ^ 2 + a ^ 2)) := by gcongr
      _ = 1 / (2 * a) / (y ^ 2 + a ^ 2) := by ring
  have hlim : Tendsto (fun y : ℝ => -1 / (2 * (y ^ 2 + a ^ 2))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact ((tendsto_pow_atTop two_ne_zero).atTop_add tendsto_const_nhds).const_mul_atTop two_pos
  have := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun y _ => hd y) hint hlim
  rw [this]
  field_simp
  ring

/-- `∫₀^∞ |k4 a n| ≤ 5a / n²`. -/
lemma integral_abs_k4_le {a n : ℝ} (ha : 0 < a) (hn : 0 < n) :
    ∫ y in Ioi 0, |k4 a n y| ≤ 5 * a / n ^ 2 := by
  have hint1 : IntegrableOn (fun y => |k4 a n y|) (Ioi 0) := (integrableOn_k4 ha hn).abs
  have hbase : IntegrableOn (fun y : ℝ => y / (y ^ 2 + a ^ 2) ^ 2) (Ioi 0) := by
    refine
      integrableOn_of_le_inv_sq ha (C := 1 / (2 * a))
        ((by fun_prop : Continuous fun y : ℝ => y).div (by fun_prop)
            (fun y => by positivity)).aestronglyMeasurable
        (fun y hy => ?_)
    rw [abs_of_nonneg (by positivity)]
    have h2 : y / (y ^ 2 + a ^ 2) ≤ 1 / (2 * a) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_nonneg (y - a)]
    calc
      y / (y ^ 2 + a ^ 2) ^ 2 = (y / (y ^ 2 + a ^ 2)) * (1 / (y ^ 2 + a ^ 2)) := by field_simp
      _ ≤ (1 / (2 * a)) * (1 / (y ^ 2 + a ^ 2)) := by gcongr
      _ = 1 / (2 * a) / (y ^ 2 + a ^ 2) := by ring
  have hint2 :
    IntegrableOn (fun y : ℝ => 10 * a ^ 3 / n ^ 2 * (y / (y ^ 2 + a ^ 2) ^ 2)) (Ioi 0) :=
    hbase.const_mul _
  calc
    ∫ y in Ioi 0, |k4 a n y| ≤ ∫ y in Ioi 0, 10 * a ^ 3 / n ^ 2 * (y / (y ^ 2 + a ^ 2) ^ 2) := by
      refine setIntegral_mono_on hint1 hint2 measurableSet_Ioi fun y hy => ?_
      have hy : 0 < y := hy
      unfold k4
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ y / (y ^ 2 + n ^ 2))]
      have h1 := abs_g4_le ha hy.le
      have h2 : y / (y ^ 2 + n ^ 2) ≤ y / n ^ 2 := by gcongr; nlinarith [sq_nonneg y]
      calc
        |g4 a y| * (y / (y ^ 2 + n ^ 2)) ≤ 10 * a ^ 3 / (y ^ 2 + a ^ 2) ^ 2 * (y / n ^ 2) := by
          gcongr
        _ = 10 * a ^ 3 / n ^ 2 * (y / (y ^ 2 + a ^ 2) ^ 2) := by ring
    _ = 10 * a ^ 3 / n ^ 2 * (1 / (2 * a ^ 2)) := by
      rw [integral_const_mul, integral_y_div_sq_sq ha]
    _ = 5 * a / n ^ 2 := by field_simp; ring

/-- `∑_{n ≥ 0} 1/(n + j + 1)⁵ = ζ(5) - H_j^{(5)}`. -/
lemma tsum_tail_eq (j : ℕ) : ∑' n : ℕ, 1 / ((j : ℝ) + ((n : ℝ) + 1)) ^ 5 = zeta5 - (H5 j : ℝ) := by
  have hz : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 5) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h := hz.sum_add_tsum_nat_add (j + 1)
  have hH : ∑ i ∈ range (j + 1), 1 / ((i : ℝ)) ^ 5 = (H5 j : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      add_zero]
    unfold H5
    push_cast
    have e1 : Finset.Icc 1 j = Finset.Ico 1 (j + 1) := by
      ext x;
      simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e1, Finset.sum_Ico_eq_sum_range, show j + 1 - 1 = j by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  have htail :
    ∑' n : ℕ, 1 / ((j : ℝ) + ((n : ℝ) + 1)) ^ 5 = ∑' n : ℕ, 1 / ((n + (j + 1) : ℕ) : ℝ) ^ 5 := by
    refine tsum_congr fun n => ?_
    push_cast; ring_nf
  rw [htail, ← hH]
  unfold zeta5
  linarith

/-- **Hermite's formula at `s = 5`** (the pole moments (2.3) of the paper). -/
theorem hermite_pole (j : ℕ) (hj : 1 ≤ j) :
    ∫ y in Ioi 0, w y / (y ^ 2 + (j : ℝ) ^ 2) =
      (j : ℝ) ^ 4 * (zeta5 - (H5 j : ℝ)) - 1 / 4 + 1 / (2 * (j : ℝ)) := by
  set a : ℝ := (j : ℝ) with ha_def
  have ha : 0 < a := by
    rw [ha_def];
    exact_mod_cast
      hj
        -- Step 1: `w / (y² + a²) = g₀ · F₄`
  have h1 : ∫ y in Ioi 0, w y / (y ^ 2 + a ^ 2) = ∫ y in Ioi 0, g0 a y * F4 y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy : 0 < y := hy
    have hne : y ^ 2 + a ^ 2 ≠ 0 := by positivity
    rw [w_eq_F4 hy]; unfold g0; field_simp;
    try
      ring
        -- Step 2: integrate by parts four times
  rw [h1, integral_g0F4_eq ha]
    -- Step 3: the pointwise decomposition of `g₄ F₀`
  have hdec :
    ∀ y,
      0 < y →
        g4 a y * F0 y =
          -(1 / 2) * g4 a y + 1 / (2 * Real.pi) * h4 a y +
            1 / Real.pi * ∑' n : ℕ, k4 a ((n : ℝ) + 1) y := by
    intro y hy
    rw [F0_series hy, ← g4_div_eq_h4 a hy.ne']
    simp only [k4]
    rw [tsum_mul_left]
    have hy' : y ≠ 0 := hy.ne'
    field_simp
    try
      ring
        -- Step 4: integrability of the pieces
  have hA : IntegrableOn (fun y => -(1 / 2) * g4 a y) (Ioi 0) := (integrableOn_g4 ha).const_mul _
  have hB : IntegrableOn (fun y => 1 / (2 * Real.pi) * h4 a y) (Ioi 0) :=
    (integrableOn_h4 ha).const_mul _
  have hprod : IntegrableOn (fun y => g4 a y * F0 y) (Ioi 0) :=
    integrableOn_of_prod_bound ha ((continuous_g4 a ha).continuousOn.mul continuousOn_F0)
      (fun y hy => abs_g4F0_le ha hy)
  have hC : IntegrableOn (fun y => 1 / Real.pi * ∑' n : ℕ, k4 a ((n : ℝ) + 1) y) (Ioi 0) := by
    have := (hprod.sub hA).sub hB
    refine this.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy : 0 < y := hy
    simp only [Pi.sub_apply]
    rw [hdec y hy];
    ring
      -- Step 5: the series of integrals
  have hnorm : Summable fun n : ℕ => ∫ y in Ioi 0, ‖k4 a ((n : ℝ) + 1) y‖ := by
    have hs : Summable fun n : ℕ => 5 * a / ((n : ℝ) + 1) ^ 2 := by
      have :=
        (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
      refine (this.mul_left (5 * a)).congr fun n => ?_
      push_cast; ring
    refine
      Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) (fun n => ?_) hs
    simp only [Real.norm_eq_abs]
    exact integral_abs_k4_le ha (by positivity)
  have hsum :
    ∫ y in Ioi 0, ∑' n : ℕ, k4 a ((n : ℝ) + 1) y = ∑' n : ℕ, ∫ y in Ioi 0, k4 a ((n : ℝ) + 1) y :=
    (integral_tsum_of_summable_integral_norm (fun n => integrableOn_k4 ha (by positivity))
        hnorm).symm
  have hval :
    ∀ n : ℕ, ∫ y in Ioi 0, k4 a ((n : ℝ) + 1) y = Real.pi * a ^ 4 / (a + ((n : ℝ) + 1)) ^ 5 :=
    fun n =>
    integral_k4 ha
      (by positivity)
        -- Step 6: assemble
  have hAB : IntegrableOn (fun y => -(1 / 2) * g4 a y + 1 / (2 * Real.pi) * h4 a y) (Ioi 0) :=
    hA.add hB
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => hdec y hy), integral_add hAB hC,
    integral_add hA hB, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_g4 ha, integral_h4 ha, hsum, tsum_congr hval]
  have htail :
    ∑' n : ℕ, Real.pi * a ^ 4 / (a + ((n : ℝ) + 1)) ^ 5 =
      Real.pi * a ^ 4 * (zeta5 - (H5 j : ℝ)) := by
    rw [← tsum_tail_eq j, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [ha_def]; ring
  rw [htail]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

end Zeta5Irrational
