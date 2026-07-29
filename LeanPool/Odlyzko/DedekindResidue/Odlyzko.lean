/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import LeanPool.Odlyzko.DedekindResidue.Lemma5
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Odlyzko's root-discriminant bound

An unconditional three-exponential explicit-formula certificate for totally
complex number fields of degree at least eighteen.
-/

@[expose] public section

namespace DedekindResidue

open Complex Filter MeasureTheory NumberField Real
open scoped ENNReal NNReal

variable (K : Type*) [Field K] [NumberField K]

/-- The zero-window bridge does not require GRH when the contour contains the
whole critical strip. -/
theorem tendsto_finsum_window_zetaZeros_unconditional {φ : ℂ → ℂ}
    (hsum : Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * φ ρ.1))
    {a : ℝ} (ha : 0 < a) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun n : ℕ => ∑ᶠ z, ((MeromorphicOn.divisor
        (completedDedekindZetaEntire K)
        (Set.Ioo (-a) (1 + a) ×ℂ Set.Ioo (-(T n)) (T n))) z : ℂ) * φ z)
      atTop
      (nhds (∑' ρ : ZetaZeros K,
        (zetaZeroDivisor K ρ.1 : ℂ) * φ ρ.1)) := by
  classical
  have hWb : ∀ n : ℕ,
      Bornology.IsBounded (Set.Ioo (-a) (1 + a) ×ℂ Set.Ioo (-(T n)) (T n)) :=
    fun n => isBounded_Ioo_reProdIm (-a) (1 + a) (-(T n)) (T n)
  set S : ℕ → Finset (ZetaZeros K) :=
    fun n => (finite_zetaZeros_mem_of_isBounded K (hWb n)).toFinset with hSdef
  have hSmem : ∀ (n : ℕ) (ρ : ZetaZeros K),
      ρ ∈ S n ↔ ρ.1 ∈ Set.Ioo (-a) (1 + a) ×ℂ Set.Ioo (-(T n)) (T n) :=
    fun n ρ => by
      rw [hSdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hStop : Tendsto S atTop atTop := by
    rw [tendsto_atTop]
    intro b
    obtain ⟨B, hB⟩ :=
      (b.finite_toSet.image (fun ρ : ZetaZeros K => |ρ.1.im|)).bddAbove
    filter_upwards [hT.eventually_ge_atTop (B + 1)] with n hn
    rw [Finset.le_iff_subset]
    intro ρ hρb
    rw [hSmem]
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have hre := re_mem_of_completedDedekindZetaEntire_eq_zero K
          ((zetaZeroDivisor_ne_zero_iff K).mp ρ.2)
      exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    · have him : |ρ.1.im| ≤ B :=
        hB (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hρb))
      obtain ⟨h1, h2⟩ := abs_le.mp him
      exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  refine (hsum.hasSum.comp hStop).congr (fun n => ?_)
  exact (finsum_divisor_mul_eq_sum_zetaZeros K φ (hWb n)).symm

/-- Absolute convergence of the exponential test's zero series, without GRH. -/
theorem summable_zetaZeros_paperPhi_expTest_unconditional {h : ℝ} (hh : 1 / 2 < h) :
    Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (expTest h) ρ.1) := by
  have hbase := summable_zetaZeros_inv_sq K (h - 1 / 2) (by linarith)
  refine Summable.of_norm_bounded (hbase.mul_left (2*h)) (fun ρ => ?_)
  have hre := re_mem_of_completedDedekindZetaEntire_eq_zero K
    ((zetaZeroDivisor_ne_zero_iff K).mp ρ.2)
  have hband : |ρ.1.re - 1 / 2| < h := by
    rw [abs_lt]
    constructor <;> linarith
  have hdenpos : 0 < (h - 1 / 2)^2 + ρ.1.im^2 := by positivity
  have hreal : ((h : ℂ)^2 - (ρ.1 - 1 / 2)^2).re
      = h^2 - (ρ.1.re - 1 / 2)^2 + ρ.1.im^2 := by
    norm_num [pow_two, Complex.sub_re, Complex.mul_re, Complex.div_re,
      Complex.div_im]
    ring
  have hdenlower : (h - 1 / 2)^2 + ρ.1.im^2
      ≤ ‖(h : ℂ)^2 - (ρ.1 - 1 / 2)^2‖ := by
    calc
      (h - 1 / 2)^2 + ρ.1.im^2
          ≤ h^2 - (ρ.1.re - 1 / 2)^2 + ρ.1.im^2 := by
            have ha : (ρ.1.re - 1 / 2)^2 ≤ (1 / 2)^2 := by
              nlinarith [sq_nonneg ρ.1.re, sq_nonneg (ρ.1.re - 1)]
            nlinarith
      _ = ((h : ℂ)^2 - (ρ.1 - 1 / 2)^2).re := hreal.symm
      _ ≤ ‖(h : ℂ)^2 - (ρ.1 - 1 / 2)^2‖ :=
        Complex.re_le_norm _
  have hdenne : (h : ℂ)^2 - (ρ.1 - 1 / 2)^2 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hdenlower
    linarith
  have hform : 1 / ((h : ℂ) - (ρ.1 - 1 / 2))
        + 1 / ((h : ℂ) + (ρ.1 - 1 / 2))
      = (2*h : ℂ) / ((h : ℂ)^2 - (ρ.1 - 1 / 2)^2) := by
    have hminus : (h : ℂ) - (ρ.1 - 1 / 2) ≠ 0 := by
      intro hz
      apply hdenne
      calc
        (h : ℂ)^2 - (ρ.1 - 1 / 2)^2
            = ((h : ℂ) - (ρ.1 - 1 / 2)) * ((h : ℂ) + (ρ.1 - 1 / 2)) := by ring
        _ = 0 := by rw [hz, zero_mul]
    have hplus : (h : ℂ) + (ρ.1 - 1 / 2) ≠ 0 := by
      intro hz
      apply hdenne
      calc
        (h : ℂ)^2 - (ρ.1 - 1 / 2)^2
            = ((h : ℂ) - (ρ.1 - 1 / 2)) * ((h : ℂ) + (ρ.1 - 1 / 2)) := by ring
        _ = 0 := by rw [hz, mul_zero]
    rw [one_div_add_one_div hminus hplus]
    congr 1 <;> ring
  rw [norm_mul, Complex.norm_intCast]
  have hdnn : (0 : ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
    exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
  rw [abs_of_nonneg hdnn, paperPhi_expTest hband, hform, norm_div]
  have hnum : ‖(2*h : ℂ)‖ = 2*h := by
    rw [show (2*h : ℂ) = ((2*h : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 2*h)]
  rw [hnum]
  calc
    (zetaZeroDivisor K ρ.1 : ℝ) *
          (2*h / ‖(h : ℂ)^2 - (ρ.1 - 1 / 2)^2‖)
        ≤ (zetaZeroDivisor K ρ.1 : ℝ) *
          (2*h / ((h - 1 / 2)^2 + ρ.1.im^2)) := by
            gcongr
    _ = 2*h * ((zetaZeroDivisor K ρ.1 : ℝ) /
          ((h - 1 / 2)^2 + ρ.1.im^2)) := by ring

/-- The archimedean integral for a two-sided exponential test. -/
noncomputable def sinhIntegral (h : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ),
    1 / (2 * Real.sinh (y/2)) * (1 - Real.exp (-h*y))

/-- The unconditional explicit formula at an exponential test for a totally
complex field. -/
theorem expTest_identity_totallyComplex [IsTotallyComplex K] {h : ℝ} (hh : 1 / 2 < h) :
    (∑' ρ : ZetaZeros K,
      (zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (expTest h) ρ.1)
      = ((4*h/(h^2 - 1 / 4) + Real.log |NumberField.discr K|
          - (Module.finrank ℚ K : ℝ)
            * (Real.eulerMascheroniConstant + Real.log (8*π))
          + (Module.finrank ℚ K : ℝ) * sinhIntegral h
          - 2 * vonMangoldtSum K (h + 1 / 2) : ℝ) : ℂ) := by
  set a : ℝ := min (1 / 4) ((h - 1 / 2)/2) with ha_def
  have ha : 0 < a := lt_min (by norm_num) (by linarith)
  have ha' : a ≤ 1 / 4 := min_le_left _ _
  have hah : 1 / 2 + a < h := by
    have h1 : a ≤ (h - 1 / 2)/2 := min_le_right _ _
    linarith
  obtain ⟨T, hT, hlim⟩ := weil_explicit_formula_expTest K ha ha' hah
  have hsum := summable_zetaZeros_paperPhi_expTest_unconditional K hh
  have hbridge := tendsto_finsum_window_zetaZeros_unconditional K hsum ha hT
  have hkey := tendsto_nhds_unique hbridge hlim
  have hpoles := paperPhi_expTest_zero_add_one hh
  have hprime := primeSideH_expTest_zero_eq K a (by linarith : 0 < h)
  have harch := arch_expTest_integral_eq h
    (fun y => 1/(2 * Real.sinh (y/2)))
  have hr1 := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K
  have hdegree :=
    NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hr1, zero_add] at hdegree
  rw [hpoles, hprime, harch, expTest_zero, hr1] at hkey
  simp only [Nat.cast_zero, zero_mul, zero_add, add_zero] at hkey
  have hdegree_real :
      2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ)
        = (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast hdegree
  rw [hdegree_real] at hkey
  have hdegree_complex :
      (((2 * NumberField.InfinitePlace.nrComplexPlaces K : ℕ) : ℂ))
        = ((Module.finrank ℚ K : ℕ) : ℂ) := by
    exact_mod_cast hdegree
  rw [hdegree_complex] at hkey
  have hpole_value :
      2/(h + 1 / 2) + 2/(h - 1 / 2) = 4*h/(h^2 - 1 / 4) := by
    have h1 : h + 1 / 2 ≠ 0 := by linarith
    have h2 : h - 1 / 2 ≠ 0 := by linarith
    rw [div_add_div (2 : ℝ) 2 h1 h2]
    congr 1 <;> ring
  rw [hpole_value] at hkey
  have harch_value :
      (∫ y in Set.Ioi (0 : ℝ),
        1 / (2 * Real.sinh (y / 2)) * (1 - Real.exp (-h * y)))
        = sinhIntegral h := rfl
  rw [harch_value] at hkey
  rw [hkey]
  push_cast
  ring

/-- Evaluation of the exponential test's archimedean integral by Gauss's
digamma formula. -/
theorem ofReal_sinhIntegral_eq_digamma {h : ℝ} (hh : 0 < h) :
    ((sinhIntegral h : ℝ) : ℂ)
      = Complex.digamma ((h + 1 / 2 : ℝ) : ℂ)
        - Complex.digamma ((1 / 2 : ℝ) : ℂ) := by
  have hw : 0 < (((h + 1 / 2 : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith
  rw [digamma_sub_digamma_eq_integral (show (0 : ℝ) < 1 / 2 by norm_num) hw]
  rw [sinhIntegral, ← integral_complex_ofReal]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  rw [Set.mem_Ioi] at hu
  have hden : 1 - Real.exp (-u) ≠ 0 := by
    have he := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
    rw [Real.exp_zero] at he
    linarith
  have hkernel := exp_half_div_one_sub_exp_neg hu
  rw [show (-((1 / 2 : ℝ) : ℂ) * (u : ℂ)) = ((-(u/2) : ℝ) : ℂ) by
      push_cast; ring,
    show (-((h + 1 / 2 : ℝ) : ℂ) * (u : ℂ))
        = ((-(h + 1 / 2)*u : ℝ) : ℂ) by push_cast; ring,
    show (-(u : ℂ)) = ((-u : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  norm_cast
  have hexp : -(h + 1 / 2)*u = -(u/2) + (-h*u) := by ring
  rw [hexp, Real.exp_add]
  symm
  calc
    (Real.exp (-(u/2)) - Real.exp (-(u/2)) * Real.exp (-h*u))
          / (1 - Real.exp (-u))
        = (Real.exp (-(u/2)) / (1 - Real.exp (-u)))
            * (1 - Real.exp (-h*u)) := by field_simp
    _ = 1 / (2 * Real.sinh (u/2)) * (1 - Real.exp (-h*u)) := by
      rw [hkernel]

/-- Exact archimedean contribution of the three-exponential Odlyzko test. -/
theorem weighted_sinhIntegral :
    7 * sinhIntegral (5 / 4)
        - (48 / 5) * sinhIntegral (7 / 4)
        + (18 / 5) * sinhIntegral (9 / 4)
      = (101 / 10)*π - Real.log 2 - 15692 / 525 := by
  have hI5 := ofReal_sinhIntegral_eq_digamma (show (0 : ℝ) < 5 / 4 by norm_num)
  have hI7 := ofReal_sinhIntegral_eq_digamma (show (0 : ℝ) < 7 / 4 by norm_num)
  have hI9 := ofReal_sinhIntegral_eq_digamma (show (0 : ℝ) < 9 / 4 by norm_num)
  norm_num only [show (5 / 4 : ℝ) + 1 / 2 = 7 / 4 by norm_num,
    show (7 / 4 : ℝ) + 1 / 2 = 9 / 4 by norm_num,
    show (9 / 4 : ℝ) + 1 / 2 = 11 / 4 by norm_num] at hI5 hI7 hI9
  have h34 := Complex.digamma_apply_add_one ((3 / 4 : ℝ) : ℂ)
    (by
      intro m hm
      have hm' := congrArg Complex.re hm
      norm_num at hm'
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
  have h14 := Complex.digamma_apply_add_one ((1 / 4 : ℝ) : ℂ)
    (by
      intro m hm
      have hm' := congrArg Complex.re hm
      norm_num at hm'
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
  have h54 := Complex.digamma_apply_add_one ((5 / 4 : ℝ) : ℂ)
    (by
      intro m hm
      have hm' := congrArg Complex.re hm
      norm_num at hm'
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
  have h74 := Complex.digamma_apply_add_one ((7 / 4 : ℝ) : ℂ)
    (by
      intro m hm
      have hm' := congrArg Complex.re hm
      norm_num at hm'
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
  norm_num at h34 h14 h54 h74
  have hquarter := digamma_three_quarter_sub_quarter
  have hhalf := digamma_half_sub_quarter
  norm_num at hI5 hI7 hI9 hquarter hhalf
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hlog] at hhalf
  have hresult :
      (((7 * sinhIntegral (5 / 4)
          - (48 / 5) * sinhIntegral (7 / 4)
          + (18 / 5) * sinhIntegral (9 / 4) : ℝ)) : ℂ)
        = ((((101 / 10)*π - Real.log 2 - 15692 / 525 : ℝ)) : ℂ) := by
    push_cast
    linear_combination
      7 * hI5 - (48 / 5) * hI7 + (18 / 5) * hI9
        - (48 / 5) * h54 - (48 / 5) * h14
        + (18 / 5) * h74 + (53 / 5) * h34
        + (53 / 5) * hquarter - hhalf
  exact_mod_cast hresult

/-- The Poitou transform of the three-exponential Odlyzko test. -/
noncomputable def odlyzkoTransform (z : ℂ) : ℂ :=
  7 * paperPhi (expTest (5 / 4)) z
    - (48 / 5) * paperPhi (expTest (7 / 4)) z
    + (18 / 5) * paperPhi (expTest (9 / 4)) z

/-- The real part of the Odlyzko transform on either boundary of the critical
strip. -/
theorem odlyzkoTransform_re_boundary {z : ℂ} (hz : z.re = 0 ∨ z.re = 1) :
    (odlyzkoTransform z).re =
      8 * (65536*z.im^8 - 3112960*z.im^6 + 35213824*z.im^4
          + 109758720*z.im^2 + 320987205) /
        (5 * (16*z.im^2 + 9) * (16*z.im^2 + 25) * (16*z.im^2 + 49)
          * (16*z.im^2 + 81) * (16*z.im^2 + 121)) := by
  have hzband : |z.re - 1 / 2| < (5 / 4 : ℝ) := by
    rcases hz with hz | hz <;> rw [hz] <;> norm_num
  rw [odlyzkoTransform, paperPhi_expTest hzband,
    paperPhi_expTest (lt_trans hzband (by norm_num : (5 / 4 : ℝ) < 7 / 4)),
    paperPhi_expTest (lt_trans hzband (by norm_num : (5 / 4 : ℝ) < 9 / 4))]
  rcases hz with hz | hz <;>
    norm_num [Complex.div_re, Complex.normSq, Complex.sub_re, Complex.sub_im,
      hz, pow_succ] <;> field_simp <;> ring

/-- Positivity of the Odlyzko transform on the critical-strip boundary. -/
theorem odlyzkoTransform_re_nonneg_boundary {z : ℂ}
    (hz : z.re = 0 ∨ z.re = 1) :
    0 ≤ (odlyzkoTransform z).re := by
  rw [odlyzkoTransform_re_boundary hz]
  have hq : 0 <
      65536*z.im^8 - 3112960*z.im^6 + 35213824*z.im^4
        + 109758720*z.im^2 + 320987205 := by
    have hsq1 : 0 ≤ (256*z.im^4 - 6080*z.im^2 - 9000)^2 := sq_nonneg _
    have hsq2 : 0 ≤ (z.im^2 + 415 / 7436)^2 := sq_nonneg _
    nlinarith
  positivity

/-- The three-exponential transform is nonnegative throughout the critical
strip. -/
theorem odlyzkoTransform_re_nonneg {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    0 ≤ (odlyzkoTransform z).re := by
  let g : ℂ → ℂ := fun w => Complex.exp (-odlyzkoTransform w)
  have hclosed : IsClosed (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1) :=
    isClosed_Icc.preimage Complex.continuous_re
  have hclosure :
      closure (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1)
        ⊆ Complex.re ⁻¹' Set.Icc (0 : ℝ) 1 :=
    closure_minimal (fun w hw => ⟨hw.1.le, hw.2.le⟩) hclosed
  have hdiffPhi (h : ℝ) (hh : (3 / 4 : ℝ) < h) :
      DifferentiableOn ℂ (paperPhi (expTest h))
        (closure (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1)) := by
    intro w hw
    have hw' := hclosure hw
    exact (differentiableAt_paperPhi_expTest (h := h) (a := 1 / 4)
      (show (0 : ℝ) < 1 / 4 by norm_num) (by linarith)
      w (by linarith [hw'.1]) (by linarith [hw'.2])).differentiableWithinAt
  have hdiffT : DifferentiableOn ℂ odlyzkoTransform
      (closure (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1)) := by
    unfold odlyzkoTransform
    exact (((hdiffPhi (5 / 4) (by norm_num)).const_mul (7 : ℂ)).sub
      ((hdiffPhi (7 / 4) (by norm_num)).const_mul (48 / 5 : ℂ))).add
      ((hdiffPhi (9 / 4) (by norm_num)).const_mul (18 / 5 : ℂ))
  have hdiffg : DifferentiableOn ℂ g
      (closure (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1)) := by
    exact hdiffT.neg.cexp
  have hgdc : DiffContOnCl ℂ g
      (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1) :=
    hdiffg.diffContOnCl
  obtain ⟨M5, hM50, hM5⟩ := exists_band_bound_paperPhi_expTest
    (show (0 : ℝ) < 5 / 4 by norm_num) (show (0 : ℝ) < 1 / 4 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 4 < 5 / 4 by norm_num)
  obtain ⟨M7, hM70, hM7⟩ := exists_band_bound_paperPhi_expTest
    (show (0 : ℝ) < 7 / 4 by norm_num) (show (0 : ℝ) < 1 / 4 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 4 < 7 / 4 by norm_num)
  obtain ⟨M9, hM90, hM9⟩ := exists_band_bound_paperPhi_expTest
    (show (0 : ℝ) < 9 / 4 by norm_num) (show (0 : ℝ) < 1 / 4 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 4 < 9 / 4 by norm_num)
  have hB : BddAbove ((norm ∘ g) ''
      Complex.HadamardThreeLines.verticalClosedStrip (0 : ℝ) 1) := by
    rw [bddAbove_def]
    refine ⟨Real.exp (7*M5 + (48 / 5)*M7 + (18 / 5)*M9), ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have hwre : 0 ≤ w.re ∧ w.re ≤ 1 := hw
    have hwrepr : ((w.re : ℂ) + (w.im : ℂ)*Complex.I) = w := by
      apply Complex.ext <;> simp
    have hmax : 1 ≤ max |w.im| 1 := le_max_right _ _
    have hb (h M : ℝ) (hM0 : 0 ≤ M)
        (hM : ∀ σ t : ℝ, -(1 / 4 : ℝ) ≤ σ → σ ≤ 1 + 1 / 4 →
          ‖paperPhi (expTest h) ((σ:ℂ) + (t : ℂ)*Complex.I)‖
            ≤ M / max |t| 1) :
        ‖paperPhi (expTest h) w‖ ≤ M := by
      rw [← hwrepr]
      exact (hM w.re w.im (by linarith) (by linarith)).trans
        (div_le_self hM0 hmax)
    have hb5 := hb (5 / 4) M5 hM50 hM5
    have hb7 := hb (7 / 4) M7 hM70 hM7
    have hb9 := hb (9 / 4) M9 hM90 hM9
    have hT : ‖odlyzkoTransform w‖
        ≤ 7*M5 + (48 / 5)*M7 + (18 / 5)*M9 := by
      rw [odlyzkoTransform]
      calc
        ‖7 * paperPhi (expTest (5 / 4)) w
            - (48 / 5) * paperPhi (expTest (7 / 4)) w
            + (18 / 5) * paperPhi (expTest (9 / 4)) w‖
            ≤ 7 * ‖paperPhi (expTest (5 / 4)) w‖
              + (48 / 5) * ‖paperPhi (expTest (7 / 4)) w‖
              + (18 / 5) * ‖paperPhi (expTest (9 / 4)) w‖ := by
                norm_num [norm_add_le, norm_sub_le]
                grw [norm_add_le, norm_sub_le]
                norm_num
        _ ≤ 7*M5 + (48 / 5)*M7 + (18 / 5)*M9 := by gcongr
    change ‖Complex.exp (-odlyzkoTransform w)‖ ≤ _
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self (-odlyzkoTransform w).re).trans
      ((Complex.abs_re_le_norm _).trans ((norm_neg _).trans_le hT))
  have hg :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := g) (z := z) (a := 1) (b := 1) (l := 0) (u := 1)
      (by norm_num) ⟨hz0, hz1⟩ hgdc hB
      (fun w hw => by
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
        change ‖Complex.exp (-odlyzkoTransform w)‖ ≤ 1
        rw [Complex.norm_exp, Real.exp_le_one_iff]
        exact neg_nonpos.mpr (odlyzkoTransform_re_nonneg_boundary (Or.inl hw)))
      (fun w hw => by
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
        change ‖Complex.exp (-odlyzkoTransform w)‖ ≤ 1
        rw [Complex.norm_exp, Real.exp_le_one_iff]
        exact neg_nonpos.mpr (odlyzkoTransform_re_nonneg_boundary (Or.inr hw)))
  simp only [one_rpow, one_mul] at hg
  change ‖Complex.exp (-odlyzkoTransform z)‖ ≤ 1 at hg
  rw [Complex.norm_exp, Real.exp_le_one_iff] at hg
  exact neg_nonpos.mp hg

/-- The prime-ideal contribution of the three-exponential test is
nonnegative. -/
theorem odlyzko_vonMangoldt_nonneg :
    0 ≤ 7 * vonMangoldtSum K (7 / 4)
      - (48 / 5) * vonMangoldtSum K (9 / 4)
      + (18 / 5) * vonMangoldtSum K (11 / 4) := by
  let f (σ : ℝ) (pk :
      {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ) : ℝ :=
    Real.log (Ideal.absNorm pk.1.1)
      * (Ideal.absNorm pk.1.1 : ℝ) ^
        (-(((pk.2 + 1 : ℕ)) : ℝ) * σ)
  have h7 : Summable (f (7 / 4)) :=
    summable_primeIdeal_pow_log_rpow K (by norm_num)
  have h9 : Summable (f (9 / 4)) :=
    summable_primeIdeal_pow_log_rpow K (by norm_num)
  have h11 : Summable (f (11 / 4)) :=
    summable_primeIdeal_pow_log_rpow K (by norm_num)
  rw [vonMangoldtSum, vonMangoldtSum, vonMangoldtSum]
  change 0 ≤ 7 * ∑' pk, f (7 / 4) pk
    - (48 / 5) * ∑' pk, f (9 / 4) pk
    + (18 / 5) * ∑' pk, f (11 / 4) pk
  rw [← h7.tsum_mul_left, ← h9.tsum_mul_left, ← h11.tsum_mul_left,
    ← (h7.mul_left 7).tsum_sub (h9.mul_left (48 / 5)),
    ← ((h7.mul_left 7).sub (h9.mul_left (48 / 5))).tsum_add
      (h11.mul_left (18 / 5))]
  apply tsum_nonneg
  intro pk
  let N : ℝ := Ideal.absNorm pk.1.1
  let m : ℝ := ((pk.2 + 1 : ℕ) : ℝ)
  let x : ℝ := N ^ (-m/4)
  have hN : 1 ≤ N := by
    dsimp only [N]
    linarith [two_le_absNorm_of_prime_real (K := K) (𝔭 := pk.1)]
  have hm : 0 < m := by
    dsimp only [m]
    positivity
  have hx0 : 0 ≤ x := Real.rpow_nonneg (by linarith [hN]) _
  have hx1 : x ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hN (by
      dsimp only [m]
      nlinarith [hm])
  have hrpow (j : ℕ) :
      N ^ (-m * ((j : ℕ) : ℝ) / 4) = x^j := by
    rw [show -m * (j : ℝ) / 4 = (-m/4) * j by ring,
      Real.rpow_mul (by linarith [hN]), Real.rpow_natCast]
  have hpoly : 0 ≤ 35 - 48*x^2 + 18*x^4 := by
    have hx2 : x^2 ≤ 1 := by nlinarith [sq_nonneg x]
    have hfac : 0 ≤ (1-x^2) * (30-18*x^2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  change 0 ≤ 7 * (Real.log N * N ^ (-m * (7 / 4)))
    - (48 / 5) * (Real.log N * N ^ (-m * (9 / 4)))
    + (18 / 5) * (Real.log N * N ^ (-m * (11 / 4)))
  have hp7 := hrpow 7
  have hp9 := hrpow 9
  have hp11 := hrpow 11
  norm_num at hp7 hp9 hp11
  have hp7' : N ^ (-m * (7 / 4)) = x^7 := by
    convert hp7 using 1
    all_goals ring
  have hp9' : N ^ (-m * (9 / 4)) = x^9 := by
    convert hp9 using 1
    all_goals ring
  have hp11' : N ^ (-m * (11 / 4)) = x^11 := by
    convert hp11 using 1
    all_goals ring
  rw [hp7', hp9', hp11']
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  nlinarith [mul_nonneg (mul_nonneg hlog (pow_nonneg hx0 7)) hpoly]

/-- A rational lower bound for the Euler--Mascheroni constant used in the
final numerical certificate. -/
theorem eulerMascheroni_gt_fifty_seven_hundredths :
    (57 / 100 : ℝ) < Real.eulerMascheroniConstant := by
  apply lt_trans (b := Real.eulerMascheroniSeq 127)
  · rw [Real.eulerMascheroniSeq]
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    have hlog := Real.log_two_lt_d9
    rw [show (128 : ℝ) = 2^7 by norm_num, Real.log_pow]
    norm_num [harmonic]
    linarith
  · exact Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 127

/-- The logarithmic part of the numerical Odlyzko certificate. -/
theorem nine_fifths_lt_log_sixty_four_pi_div_thirty_three :
    (9 / 5 : ℝ) < Real.log (64*π/33) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have hsmall := Real.exp_le_two_add_div_two_sub
    (show (0 : ℝ) ≤ 1 / 5 by norm_num) (show (1 / 5 : ℝ) < 2 by norm_num)
  norm_num at hsmall
  have hsplit : Real.exp (9 / 5) = Real.exp 1 * (Real.exp (1 / 5))^4 := by
    rw [show (9 / 5 : ℝ) = 1 + 4*(1 / 5) by norm_num, Real.exp_add]
    congr 1
    convert Real.exp_nat_mul (1 / 5) 4 using 1
    all_goals norm_num
  rw [hsplit]
  calc
    Real.exp 1 * Real.exp (1 / 5)^4
        < 2.7182818286 * (11 / 9)^4 := by calc
          _ < 2.7182818286 * Real.exp (1 / 5)^4 :=
            mul_lt_mul_of_pos_right Real.exp_one_lt_d9
              (pow_pos (Real.exp_pos _) _)
          _ ≤ 2.7182818286 * (11 / 9)^4 := by gcongr
    _ < 64*π/33 := by nlinarith [Real.pi_gt_d2]

/-- The exact numerical inequality supplied by the three-exponential
certificate. -/
theorem odlyzko_numerical_certificate :
    Real.log (33 / 4)
      < Real.eulerMascheroniConstant + Real.log (8*π)
        - ((101 / 10)*π - Real.log 2 - 15692 / 525)
        - (54896 / 5775)/18 := by
  have hγ := eulerMascheroni_gt_fifty_seven_hundredths
  have hlog := nine_fifths_lt_log_sixty_four_pi_div_thirty_three
  have hπ := Real.pi_lt_d4
  have hlog8 : Real.log (8*π) + Real.log 2 - Real.log (33 / 4)
      = Real.log (64*π/33) := by
    calc
      _ = Real.log ((8*π)*2) - Real.log (33 / 4) := by
        rw [Real.log_mul (by positivity : (8*π:ℝ) ≠ 0)
          (by norm_num : (2 : ℝ) ≠ 0)]
      _ = Real.log (((8*π)*2)/(33 / 4)) := by
        rw [Real.log_div (by positivity : ((8*π)*2 : ℝ) ≠ 0)
          (by norm_num : (33 / 4 : ℝ) ≠ 0)]
      _ = _ := by congr 1; ring
  norm_num at *
  nlinarith [hlog8]

/-- The explicit formula and the three-exponential certificate give the
required logarithmic discriminant estimate. -/
theorem odlyzko_log_discr_bound [IsTotallyComplex K] :
    (Module.finrank ℚ K : ℝ)
        * (Real.eulerMascheroniConstant + Real.log (8*π)
          - ((101 / 10)*π - Real.log 2 - 15692 / 525))
      - 54896 / 5775
        ≤ Real.log |NumberField.discr K| := by
  let term (h : ℝ) (ρ : ZetaZeros K) : ℂ :=
    (zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (expTest h) ρ.1
  have hs5 : Summable (term (5 / 4)) :=
    summable_zetaZeros_paperPhi_expTest_unconditional K (by norm_num)
  have hs7 : Summable (term (7 / 4)) :=
    summable_zetaZeros_paperPhi_expTest_unconditional K (by norm_num)
  have hs9 : Summable (term (9 / 4)) :=
    summable_zetaZeros_paperPhi_expTest_unconditional K (by norm_num)
  have hslinear : Summable (fun ρ =>
      7 * term (5 / 4) ρ - (48 / 5) * term (7 / 4) ρ
        + (18 / 5) * term (9 / 4) ρ) :=
    ((hs5.mul_left 7).sub (hs7.mul_left (48 / 5))).add
      (hs9.mul_left (18 / 5))
  have hsT : Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * odlyzkoTransform ρ.1) := by
    refine hslinear.congr (fun ρ => ?_)
    dsimp only [term]
    rw [odlyzkoTransform]
    ring
  have hsum_expand :
      (∑' ρ : ZetaZeros K,
          (zetaZeroDivisor K ρ.1 : ℂ) * odlyzkoTransform ρ.1)
        = 7 * ∑' ρ, term (5 / 4) ρ
          - (48 / 5) * ∑' ρ, term (7 / 4) ρ
          + (18 / 5) * ∑' ρ, term (9 / 4) ρ := by
    calc
      _ = ∑' ρ, (7 * term (5 / 4) ρ - (48 / 5) * term (7 / 4) ρ
          + (18 / 5) * term (9 / 4) ρ) := by
            apply tsum_congr
            intro ρ
            dsimp only [term]
            rw [odlyzkoTransform]
            ring
      _ = _ := by
        rw [((hs5.mul_left 7).sub (hs7.mul_left (48 / 5))).tsum_add
            (hs9.mul_left (18 / 5)),
          (hs5.mul_left 7).tsum_sub (hs7.mul_left (48 / 5)),
          hs5.tsum_mul_left, hs7.tsum_mul_left, hs9.tsum_mul_left]
  have h5 := expTest_identity_totallyComplex K
    (show (1 / 2 : ℝ) < 5 / 4 by norm_num)
  have h7 := expTest_identity_totallyComplex K
    (show (1 / 2 : ℝ) < 7 / 4 by norm_num)
  have h9 := expTest_identity_totallyComplex K
    (show (1 / 2 : ℝ) < 9 / 4 by norm_num)
  change (∑' ρ, term (5 / 4) ρ) = _ at h5
  change (∑' ρ, term (7 / 4) ρ) = _ at h7
  change (∑' ρ, term (9 / 4) ρ) = _ at h9
  have hidentity :
      (∑' ρ : ZetaZeros K,
          (zetaZeroDivisor K ρ.1 : ℂ) * odlyzkoTransform ρ.1)
        = ((54896 / 5775 + Real.log |NumberField.discr K|
            - (Module.finrank ℚ K : ℝ)
              * (Real.eulerMascheroniConstant + Real.log (8*π))
            + (Module.finrank ℚ K : ℝ)
              * ((101 / 10)*π - Real.log 2 - 15692 / 525)
            - 2 * (7 * vonMangoldtSum K (7 / 4)
              - (48 / 5) * vonMangoldtSum K (9 / 4)
              + (18 / 5) * vonMangoldtSum K (11 / 4)) : ℝ) : ℂ) := by
    rw [hsum_expand, h5, h7, h9]
    have harch := congrArg (fun x : ℝ => (x : ℂ)) weighted_sinhIntegral
    push_cast at harch ⊢
    norm_num at harch ⊢
    linear_combination (Module.finrank ℚ K : ℂ) * harch
  have hzero : 0 ≤ (∑' ρ : ZetaZeros K,
      (zetaZeroDivisor K ρ.1 : ℂ) * odlyzkoTransform ρ.1).re := by
    rw [Complex.re_tsum hsT]
    apply tsum_nonneg
    intro ρ
    have hre := re_mem_of_completedDedekindZetaEntire_eq_zero K
      ((zetaZeroDivisor_ne_zero_iff K).mp ρ.2)
    rw [Complex.mul_re]
    norm_num
    exact mul_nonneg
      (by exact_mod_cast zetaZeroDivisor_nonneg K ρ.1)
      (odlyzkoTransform_re_nonneg hre.1 hre.2)
  have hreal := congrArg Complex.re hidentity
  simp only [Complex.ofReal_re] at hreal
  have hprime := odlyzko_vonMangoldt_nonneg K
  linarith

/-- Odlyzko's root-discriminant bound in degree at least eighteen. -/
theorem abs_discr_ge [IsTotallyComplex K]
    (hdim : Module.finrank ℚ K ≥ 18) :
    |(NumberField.discr K : ℝ)|
      ≥ 8.25 ^ Module.finrank ℚ K := by
  let n : ℕ := Module.finrank ℚ K
  let A : ℝ := Real.eulerMascheroniConstant + Real.log (8*π)
    - ((101 / 10)*π - Real.log 2 - 15692 / 525)
  have hn : (18 : ℝ) ≤ n := by exact_mod_cast hdim
  have hcert : Real.log (33 / 4) < A - (54896 / 5775)/18 := by
    exact odlyzko_numerical_certificate
  have hscaled : (n : ℝ) * Real.log (33 / 4)
      ≤ (n : ℝ) * A - 54896 / 5775 := by
    have hn0 : (0 : ℝ) < n := by linarith
    have hmul := mul_lt_mul_of_pos_left hcert hn0
    have hcompare :
        (n : ℝ) * (A - (54896 / 5775)/18)
          ≤ (n : ℝ) * A - 54896 / 5775 := by
      nlinarith
    exact hmul.le.trans hcompare
  have hlog : (n : ℝ) * Real.log (33 / 4)
      ≤ Real.log |NumberField.discr K| :=
    hscaled.trans (odlyzko_log_discr_bound K)
  have habspos : 0 < |(NumberField.discr K : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast NumberField.discr_ne_zero K
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_nat_mul (Real.log (33 / 4)) n,
    Real.exp_log (by norm_num : (0 : ℝ) < 33 / 4),
    Real.exp_log habspos] at hexp
  norm_num at hexp ⊢
  exact hexp

end DedekindResidue

end
