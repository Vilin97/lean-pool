/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisProfile
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic.GCongr

@[expose] public section

/-!
# Convergent series for the leading natural axis profile

This module concerns the leading scaled linear equation of Proposition 5.1,
not the nonlinear perturbation or the claimed uniform remainder estimates.
-/

noncomputable section

namespace NavierStokes.AxisSeries

open scoped BigOperators Topology
open Filter Set

/-- Terms of a family of entire factorial-denominator series. -/
def term (k n : ℕ) (t : ℝ) : ℝ :=
  (-t) ^ n / ((n.factorial : ℝ) * ((n + k).factorial : ℝ))

/-- The generalized leading series; the axis profile uses `k=1`. -/
def bessel (k : ℕ) (t : ℝ) : ℝ := ∑' n : ℕ, term k n t

theorem term_norm_le (k n : ℕ) (t R : ℝ) (hR : 0 ≤ R) (ht : |t| ≤ R) :
    ‖term k n t‖ ≤ R ^ n / (n.factorial : ℝ) := by
  have hf : (1 : ℝ) ≤ ((n + k).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_pos (n + k))
  have hn : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  calc
    ‖term k n t‖ = |t| ^ n /
        ((n.factorial : ℝ) * ((n + k).factorial : ℝ)) := by
      simp [term, Real.norm_eq_abs]
    _ ≤ R ^ n / ((n.factorial : ℝ) * ((n + k).factorial : ℝ)) := by
      gcongr
    _ ≤ R ^ n / (n.factorial : ℝ) := by
      apply div_le_div_of_nonneg_left (pow_nonneg hR _) hn
      nlinarith

/-- Absolute summability, proved by comparison with the exponential series. -/
theorem summable_term (k : ℕ) (t : ℝ) : Summable (fun n : ℕ => term k n t) := by
  exact Summable.of_norm_bounded
    (Real.summable_pow_div_factorial |t|)
    (fun n => term_norm_le k n t |t| (abs_nonneg t) le_rfl)

theorem summable_norm_term (k : ℕ) (t : ℝ) :
    Summable (fun n : ℕ => ‖term k n t‖) := by
  apply Summable.of_norm_bounded
    (Real.summable_pow_div_factorial |t|)
  intro n
  simpa only [norm_norm] using term_norm_le k n t |t| (abs_nonneg t) le_rfl

theorem summable_term_tail (k j : ℕ) (t : ℝ) :
    Summable (fun n : ℕ => term k (n + j) t) :=
  (summable_nat_add_iff j).mpr (summable_term k t)

/-- Differentiating a successor-index term cancels one factorial factor. -/
theorem hasDerivAt_term_succ (k n : ℕ) (t : ℝ) :
    HasDerivAt (term k (n + 1)) (-term (k + 1) n t) t := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hk : ((n + (k + 1)).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  convert! (((hasDerivAt_id t).fun_neg.fun_pow (n + 1)).div_const
    ((Nat.factorial (n + 1) : ℝ) * (Nat.factorial (n + 1 + k) : ℝ))) using 1
  simp only [term, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, id_eq]
  rw [show n + 1 + k = n + (k + 1) by omega]
  field_simp

theorem bessel_eq_constant_add_tail (k : ℕ) (t : ℝ) :
    bessel k t = 1 / (k.factorial : ℝ) + ∑' n : ℕ, term k (n + 1) t := by
  simpa [bessel, term] using (summable_term k t).tsum_eq_zero_add

/-- Differentiation of the convergent infinite series on every real point. -/
theorem hasDerivAt_bessel (k : ℕ) (t : ℝ) :
    HasDerivAt (bessel k) (-bessel (k + 1) t) t := by
  let R : ℝ := |t| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have ht : t ∈ Ioo (-R) R := by
    dsimp [R]
    constructor
    · linarith [neg_abs_le t]
    · linarith [le_abs_self t]
  have htail : HasDerivAt (fun x : ℝ => ∑' n : ℕ, term k (n + 1) x)
      (∑' n : ℕ, -term (k + 1) n t) t := by
    apply hasDerivAt_tsum_of_isPreconnected
      (u := fun n : ℕ => R ^ n / (n.factorial : ℝ))
      (g := fun n y => term k (n + 1) y)
      (g' := fun n y => -term (k + 1) n y)
      (t := Ioo (-R) R) (y₀ := t)
      (Real.summable_pow_div_factorial R) isOpen_Ioo isPreconnected_Ioo
    · intro n y _
      exact hasDerivAt_term_succ k n y
    · intro n y hy
      rw [norm_neg]
      exact term_norm_le (k + 1) n y R hR.le
        (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
    · exact ht
    · exact summable_term_tail k 1 t
    · exact ht
  have hfun : bessel k = fun x : ℝ =>
      1 / (k.factorial : ℝ) + ∑' n : ℕ, term k (n + 1) x := by
    funext x
    exact bessel_eq_constant_add_tail k x
  rw [hfun]
  simpa only [tsum_neg, bessel] using htail.const_add (1 / (k.factorial : ℝ))

theorem deriv_bessel (k : ℕ) :
    deriv (bessel k) = fun t : ℝ => -bessel (k + 1) t := by
  funext t
  exact (hasDerivAt_bessel k t).deriv

/-- A termwise contiguous relation, with the constant term removed. -/
theorem term_contiguous (k n : ℕ) (t : ℝ) :
    term k (n + 1) t = ((k : ℝ) + 1) * term (k + 1) (n + 1) t -
      t * term (k + 2) n t := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hnk : (n : ℝ) + k + 1 ≠ 0 := by positivity
  have hnk' : (n : ℝ) + k + 1 + 1 ≠ 0 := by positivity
  have hfn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfk : ((n + k).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [term, show n + 1 + k = (n + k) + 1 by omega,
    show n + 1 + (k + 1) = (n + k) + 1 + 1 by omega,
    show n + (k + 2) = (n + k) + 1 + 1 by omega,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp; ring

theorem factorial_reciprocal (k : ℕ) :
    1 / (k.factorial : ℝ) = ((k : ℝ) + 1) * (1 / ((k + 1).factorial : ℝ)) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

/-- The convergent sums satisfy the contiguous relation underlying the ODE. -/
theorem bessel_contiguous (k : ℕ) (t : ℝ) :
    bessel k t = ((k : ℝ) + 1) * bessel (k + 1) t - t * bessel (k + 2) t := by
  have htail : (∑' n : ℕ, term k (n + 1) t) =
      ((k : ℝ) + 1) * (∑' n : ℕ, term (k + 1) (n + 1) t) -
      t * (∑' n : ℕ, term (k + 2) n t) := by
    calc
      _ = ∑' n : ℕ, (((k : ℝ) + 1) * term (k + 1) (n + 1) t -
          t * term (k + 2) n t) := tsum_congr (fun n => term_contiguous k n t)
      _ = _ := by
        rw [((summable_term_tail (k + 1) 1 t).mul_left ((k : ℝ) + 1)).tsum_sub
          ((summable_term (k + 2) t).mul_left t), tsum_mul_left, tsum_mul_left]
  rw [bessel_eq_constant_add_tail k t, bessel_eq_constant_add_tail (k + 1) t,
    htail, factorial_reciprocal k]
  unfold bessel
  ring

theorem second_deriv_bessel (k : ℕ) (t : ℝ) :
    deriv (deriv (bessel k)) t = bessel (k + 2) t := by
  rw [deriv_bessel]
  simpa only [neg_neg, Nat.add_assoc] using (hasDerivAt_bessel (k + 1) t).fun_neg.deriv

/-- An actual differential equation for the infinite function. -/
theorem bessel_ode (k : ℕ) (t : ℝ) :
    t * deriv (deriv (bessel k)) t + ((k : ℝ) + 1) * deriv (bessel k) t +
      bessel k t = 0 := by
  rw [second_deriv_bessel, deriv_bessel, bessel_contiguous k t]
  ring

theorem bessel_zero (k : ℕ) : bessel k 0 = 1 / (k.factorial : ℝ) := by
  rw [bessel_eq_constant_add_tail]
  simp [term]

/-- The leading regular angular profile in the manuscript's scaled radius. -/
def profile (χ Y : ℝ) : ℝ := bessel 1 ((χ / 2) * Y)

theorem profile_eq_tsum (χ Y : ℝ) :
    profile χ Y = ∑' n : ℕ, (-χ * Y / 2) ^ n /
      ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
  unfold profile bessel term
  apply tsum_congr
  intro n
  congr 2
  ring

theorem profile_zero (χ : ℝ) : profile χ 0 = 1 := by
  simp [profile, bessel_zero]

theorem hasDerivAt_profile (χ Y : ℝ) :
    HasDerivAt (profile χ) (-(χ / 2) * bessel 2 ((χ / 2) * Y)) Y := by
  convert! (hasDerivAt_bessel 1 ((χ / 2) * Y)).comp Y
    ((hasDerivAt_id Y).const_mul (χ / 2)) using 1
  simp only [mul_one]
  ring

theorem deriv_profile (χ : ℝ) :
    deriv (profile χ) = fun Y : ℝ => -(χ / 2) * bessel 2 ((χ / 2) * Y) := by
  funext Y
  exact (hasDerivAt_profile χ Y).deriv

theorem second_deriv_profile (χ Y : ℝ) :
    deriv (deriv (profile χ)) Y = (χ / 2) ^ 2 * bessel 3 ((χ / 2) * Y) := by
  rw [deriv_profile]
  have h := ((hasDerivAt_bessel 2 ((χ / 2) * Y)).comp Y
    ((hasDerivAt_id Y).const_mul (χ / 2))).const_mul (-(χ / 2))
  convert! h.deriv using 1
  simp only [mul_one]
  ring

/-- The leading regular equation `2(YΦ''+2Φ') = -χΦ`, for the actual sum. -/
theorem profile_scaled_ode (χ Y : ℝ) :
    2 * (Y * deriv (deriv (profile χ)) Y + 2 * deriv (profile χ) Y) =
      -χ * profile χ Y := by
  rw [second_deriv_profile, deriv_profile]
  unfold profile
  rw [bessel_contiguous 1 ((χ / 2) * Y)]
  norm_num
  ring

/-- The exact successive-term ratio, including its sign. -/
theorem term_succ_ratio (k n : ℕ) (t : ℝ) :
    term k (n + 1) t =
      (-t) / (((n : ℝ) + 1) * ((n : ℝ) + k + 1)) * term k n t := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hnk : (n : ℝ) + k + 1 ≠ 0 := by positivity
  have hfn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfk : ((n + k).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [term, show n + 1 + k = (n + k) + 1 by omega,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

theorem term_sign (k n : ℕ) (t : ℝ) :
    term k n t = (-1 : ℝ) ^ n * term k n (-t) := by
  simp only [term, neg_neg]
  rw [show -t = (-1 : ℝ) * t by ring, mul_pow]
  ring

/-- Once at least the zeroth term is removed, the remaining magnitudes
decrease on `0 ≤ t ≤ 4`, for every nonnegative factorial offset. -/
theorem magnitude_tail_antitone (k j : ℕ) (hj : 1 ≤ j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 4) :
    Antitone (fun n : ℕ => term k (n + j) (-t)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [show n + 1 + j = (n + j) + 1 by omega, term_succ_ratio]
  simp only [neg_neg]
  have hm : 0 ≤ term k (n + j) (-t) := by
    unfold term
    simp only [neg_neg]
    positivity
  have hd : 0 < (((n + j : ℕ) : ℝ) + 1) * (((n + j : ℕ) : ℝ) + k + 1) := by
    positivity
  apply mul_le_of_le_one_left hm
  apply (div_le_one hd).mpr
  have hnj : (1 : ℝ) ≤ ((n + j : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ n + j by omega)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hleft : (2 : ℝ) ≤ ((n + j : ℕ) : ℝ) + 1 := by linarith
  have hright : (2 : ℝ) ≤ ((n + j : ℕ) : ℝ) + k + 1 := by linarith
  have hprod := mul_le_mul hleft hright (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : 0 ≤ ((n + j : ℕ) : ℝ) + 1)
  linarith

/-- The cubic tail is an instance of the preceding magnitude estimate. -/
theorem cubic_tail_antitone (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 41 / 20) :
    Antitone (fun n : ℕ => term 1 (n + 4) (-t)) :=
  magnitude_tail_antitone 1 4 (by norm_num) t ht0 (by linarith)

/-- The infinite alternating tail following the cubic has nonnegative sum. -/
theorem cubic_tail_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 41 / 20) :
    0 ≤ ∑' n : ℕ, term 1 (n + 4) t := by
  have hsign : (fun n : ℕ => term 1 (n + 4) t) =
      fun n : ℕ => (-1 : ℝ) ^ n * term 1 (n + 4) (-t) := by
    funext n
    rw [term_sign, pow_add]
    norm_num
  have hs := (summable_term_tail 1 4 t).hasSum
  rw [hsign] at hs
  have hb := Antitone.alternating_series_le_tendsto hs.tendsto_sum_nat
    (cubic_tail_antitone t ht0 ht) 0
  simpa only [hsign, mul_zero, Finset.range_zero, Finset.sum_empty] using hb

theorem cubic_lower_le_bessel (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 41 / 20) :
    AxisProfile.cubicLower t ≤ bessel 1 t := by
  have hpoly : (∑ n ∈ Finset.range 4, term 1 n t) = AxisProfile.cubicLower t := by
    norm_num [Finset.sum_range_succ, term, AxisProfile.cubicLower, Nat.factorial_succ]
    ring
  have hs := (summable_term 1 t).sum_add_tsum_nat_add 4
  rw [hpoly] at hs
  have ht' := cubic_tail_nonneg t ht0 ht
  unfold bessel
  linarith

/-- A uniform positive lower bound for the actual infinite leading series. -/
theorem bessel_one_gt_quarter (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 41 / 20) :
    1 / 4 < bessel 1 t :=
  lt_of_lt_of_le (AxisProfile.cubicLower_gt_quarter t ht)
    (cubic_lower_le_bessel t ht0 ht)

/-- Positivity on the entire axis interval requested in Proposition 5.1,
for the leading profile rather than its nonlinear perturbation. -/
theorem profile_gt_quarter (χ Y : ℝ) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 41 / 10) : 1 / 4 < profile χ Y := by
  apply bessel_one_gt_quarter
  · positivity
  · nlinarith [mul_nonneg (sub_nonneg.mpr hχ1) hY0]

theorem profile_pos (χ Y : ℝ) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 41 / 10) : 0 < profile χ Y := by
  have h := profile_gt_quarter χ Y hχ0 hχ1 hY0 hY1
  linarith

/-- A convergent alternating tail beginning with its positive sign has
nonnegative total, for every offset starting after at least one term. -/
theorem alternating_tail_nonneg (k j : ℕ) (hj : 1 ≤ j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 4) :
    0 ≤ ∑' n : ℕ, (-1 : ℝ) ^ n * term k (n + j) (-t) := by
  have hs : Summable (fun n : ℕ => (-1 : ℝ) ^ n * term k (n + j) (-t)) := by
    apply Summable.of_norm_bounded
      ((summable_nat_add_iff j).mpr (summable_norm_term k (-t)))
    intro n
    simp
  have hb := Antitone.alternating_series_le_tendsto hs.hasSum.tendsto_sum_nat
    (magnitude_tail_antitone k j hj t ht0 ht) 0
  simpa using hb

/-- Every odd-length truncation with at least one term is an upper bound
on the actual series on this interval. -/
theorem bessel_le_odd_partial_sum (k j : ℕ) (hj : 1 ≤ j) (hodd : Odd j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 4) :
    bessel k t ≤ ∑ n ∈ Finset.range j, term k n t := by
  have hsign : ∀ n : ℕ, term k (n + j) t =
      -((-1 : ℝ) ^ n * term k (n + j) (-t)) := by
    intro n
    rw [term_sign, pow_add, hodd.neg_one_pow]
    ring
  have htail : (∑' n : ℕ, term k (n + j) t) =
      -(∑' n : ℕ, (-1 : ℝ) ^ n * term k (n + j) (-t)) := by
    simp_rw [hsign]
    rw [tsum_neg]
  have hs := (summable_term k t).sum_add_tsum_nat_add j
  have hnonneg := alternating_tail_nonneg k j hj t ht0 ht
  rw [htail] at hs
  unfold bessel
  linarith

theorem bessel_one_le_one (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 4) :
    bessel 1 t ≤ 1 := by
  have h := bessel_le_odd_partial_sum 1 1 (by norm_num) (by norm_num) t ht0 ht
  simpa [Finset.sum_range_succ, term] using h

/-- The quartic upper bound controls the actual factorial-square series. -/
theorem bessel_zero_lt_neg_eighteen_hundredths
    (t : ℝ) (ht0 : 99 / 50 ≤ t) (ht1 : t ≤ 2) :
    bessel 0 t < -(18 / 100) := by
  have h := bessel_le_odd_partial_sum 0 5 (by norm_num) ⟨2, by norm_num⟩ t
    (by linarith) (by linarith)
  have hpoly : (∑ n ∈ Finset.range 5, term 0 n t) = AxisProfile.quarticUpper t := by
    norm_num [Finset.sum_range_succ, term, AxisProfile.quarticUpper, Nat.factorial_succ]
    ring
  rw [hpoly] at h
  exact lt_of_le_of_lt h (AxisProfile.quarticUpper_lt_neg_eighteen_hundredths t ht0 ht1)

/-- The derivative combination used in the manuscript's sign test is now
an identity of differentiable infinite functions. -/
theorem bessel_one_add_mul_deriv (t : ℝ) :
    bessel 1 t + t * deriv (bessel 1) t = bessel 0 t := by
  rw [deriv_bessel, bessel_contiguous 0 t]
  norm_num
  ring

theorem bessel_one_log_slope_gt (t : ℝ) (ht0 : 99 / 50 ≤ t) (ht1 : t ≤ 2) :
    236 / 100 < -2 * t * deriv (bessel 1) t / bessel 1 t := by
  have hpos : 0 < bessel 1 t := by
    have h := bessel_one_gt_quarter t (by linarith) (by linarith)
    linarith
  have hupper := bessel_one_le_one t (by linarith) (by linarith)
  have hsign := bessel_zero_lt_neg_eighteen_hundredths t ht0 ht1
  rw [← bessel_one_add_mul_deriv t] at hsign
  apply (lt_div_iff₀ hpos).mpr
  nlinarith

/-- The exact leading profile has the stated `2.36` slope margin at `Y=4`
when `χ≥0.99`. No perturbation estimate is asserted. -/
theorem profile_log_slope_at_four (χ : ℝ) (hχ0 : 99 / 100 ≤ χ) (hχ1 : χ ≤ 1) :
    236 / 100 < -8 * deriv (profile χ) 4 / profile χ 4 := by
  have h := bessel_one_log_slope_gt ((χ / 2) * 4) (by linarith) (by linarith)
  rw [deriv_bessel] at h
  rw [deriv_profile]
  unfold profile
  convert! h using 1
  ring

end NavierStokes.AxisSeries

end
