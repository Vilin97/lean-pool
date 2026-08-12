/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Gauss Digamma Eq Digamma

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

/-- A gauss digamma integrand used in the Odlyzko-bound argument. -/
noncomputable def gaussDigammaIntegrand (s : ℂ) (x : ℝ) : ℂ :=
  (Complex.exp (-x) - Complex.exp (-s * x)) /
    (1 - Complex.exp (-x))

theorem integral_cexp_neg_mul_Ioi {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ in Ioi 0, Complex.exp (-s * x)) = 1 / s := by
  have hneg : (-s).re < 0 := by simpa using hs
  rw [integral_exp_mul_complex_Ioi hneg 0]
  simp

end NumberField.Odlyzko

end

section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

theorem half_mul_le_one_sub_exp_neg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have hexp : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have hpos : 0 < x + 1 := by linarith
  have hinv : (Real.exp x)⁻¹ ≤ (x + 1)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) hpos).mpr hexp
  have hrec : (x + 1)⁻¹ ≤ 1 - x / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  rw [Real.exp_neg]
  linarith

theorem norm_gaussDigammaIntegrand_le_local
    (s : ℂ) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hsx : ‖s - 1‖ * x ≤ 1) :
    ‖gaussDigammaIntegrand s x‖ ≤ 4 * ‖s - 1‖ := by
  have hdenPos : 0 < 1 - Real.exp (-x) := by simp_all
  have hden :
      ‖(1 : ℂ) - Complex.exp (-x)‖ =
        1 - Real.exp (-x) := by
    rw [show Complex.exp (-x) = (Real.exp (-x) : ℝ) by
      simp]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdenPos]
  have hfactor :
      Complex.exp (-x) - Complex.exp (-s * x) =
        Complex.exp (-x) *
          (1 - Complex.exp (-(s - 1) * x)) := by
    have hexp :
        Complex.exp (-s * x) =
          Complex.exp (-x) * Complex.exp (-(s - 1) * x) := by
      rw [← Complex.exp_add]
      ring_nf
    grind
  have hz : ‖-(s - 1) * (x : ℂ)‖ ≤ 1 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx0]
    grind
  have hnum :
      ‖Complex.exp (-x) - Complex.exp (-s * x)‖ ≤
        2 * ‖s - 1‖ * x := by
    rw [hfactor, norm_mul]
    have hexpnorm : ‖Complex.exp (-x)‖ = Real.exp (-x) := by
      rw [Complex.norm_exp]
      simp
    rw [hexpnorm]
    have hsub :
        ‖1 - Complex.exp (-(s - 1) * x)‖ ≤
          2 * ‖s - 1‖ * x := by
      rw [← norm_neg, neg_sub]
      calc
        ‖Complex.exp (-(s - 1) * x) - 1‖ ≤
            2 * ‖-(s - 1) * (x : ℂ)‖ :=
          Complex.norm_exp_sub_one_le hz
        _ = 2 * ‖s - 1‖ * x := by
          rw [norm_mul, norm_neg, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hx0]
          ring
    calc
      Real.exp (-x) * ‖1 - Complex.exp (-(s - 1) * x)‖ ≤
          1 * (2 * ‖s - 1‖ * x) := by
        gcongr
        grind
      _ = _ := by ring
  rw [gaussDigammaIntegrand, norm_div, hden]
  have hlower : x / 2 ≤ 1 - Real.exp (-x) :=
    half_mul_le_one_sub_exp_neg hx0.le hx1
  apply (div_le_iff₀ hdenPos).mpr
  calc
    ‖Complex.exp (-x) - Complex.exp (-s * x)‖ ≤
        2 * ‖s - 1‖ * x := hnum
    _ ≤ (4 * ‖s - 1‖) * (1 - Real.exp (-x)) := by
      nlinarith [norm_nonneg (s - 1)]

theorem norm_gaussDigammaIntegrand_le_tail
    {s : ℂ} (_hs : 0 < s.re) {x : ℝ} (hx : 1 ≤ x) :
    ‖gaussDigammaIntegrand s x‖ ≤
      (1 - Real.exp (-1))⁻¹ *
        (Real.exp (-x) + Real.exp (-s.re * x)) := by
  have hdenPos : 0 < 1 - Real.exp (-x) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hdenOnePos : 0 < 1 - Real.exp (-1) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hden :
      ‖(1 : ℂ) - Complex.exp (-x)‖ =
        1 - Real.exp (-x) := by
    rw [show Complex.exp (-x) = (Real.exp (-x) : ℝ) by
      simp]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdenPos]
  have hdenLower : 1 - Real.exp (-1) ≤ 1 - Real.exp (-x) := by
    gcongr
  have hnum :
      ‖Complex.exp (-x) - Complex.exp (-s * x)‖ ≤
        Real.exp (-x) + Real.exp (-s.re * x) := by
    calc
      ‖Complex.exp (-x) - Complex.exp (-s * x)‖ ≤
          ‖Complex.exp (-x)‖ + ‖Complex.exp (-s * x)‖ :=
        norm_sub_le _ _
      _ = Real.exp (-x) + Real.exp (-s.re * x) := by
        rw [Complex.norm_exp, Complex.norm_exp]
        simp
  rw [gaussDigammaIntegrand, norm_div, hden]
  calc
    ‖Complex.exp (-x) - Complex.exp (-s * x)‖ /
          (1 - Real.exp (-x)) ≤
        (Real.exp (-x) + Real.exp (-s.re * x)) /
          (1 - Real.exp (-x)) := by
      exact div_le_div_of_nonneg_right hnum hdenPos.le
    _ ≤ (Real.exp (-x) + Real.exp (-s.re * x)) /
          (1 - Real.exp (-1)) := by
      exact div_le_div_of_nonneg_left
        (by positivity) hdenOnePos hdenLower
    _ = _ := by grind

theorem gaussDigammaIntegrand_integrableOn_Ioi_one
    {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn (gaussDigammaIntegrand s)
      (Set.Ioi (1 : ℝ)) := by
  let C : ℝ := (1 - Real.exp (-1))⁻¹
  let majorant : ℝ → ℝ := fun x ↦
    C * (Real.exp (-x) + Real.exp (-s.re * x))
  have hfirst :
      MeasureTheory.IntegrableOn (fun x : ℝ ↦ Real.exp (-x))
        (Set.Ioi (1 : ℝ)) := by
    simpa only [neg_mul, one_mul] using
      (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 1)
  have hsecond :
      MeasureTheory.IntegrableOn
        (fun x : ℝ ↦ Real.exp (-s.re * x))
        (Set.Ioi (1 : ℝ)) :=
    integrableOn_exp_mul_Ioi (by linarith) 1
  have hmajorant :
      MeasureTheory.IntegrableOn majorant (Set.Ioi (1 : ℝ)) :=
    (hfirst.add hsecond).const_mul C
  have hmeas :
      AEStronglyMeasurable (gaussDigammaIntegrand s)
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have hcont : ContinuousOn (gaussDigammaIntegrand s) (Set.Ioi (1 : ℝ)) := by
      intro x hx
      unfold gaussDigammaIntegrand
      apply ContinuousWithinAt.div
      · fun_prop
      · fun_prop
      · have hx0 : 0 < x := zero_lt_one.trans hx
        intro h
        have hexp : Complex.exp (-(x : ℂ)) = 1 :=
          sub_eq_zero.mp h |>.symm
        have hnorm := congrArg norm hexp
        have hre : Real.exp (-x) = Real.exp 0 := by
          simpa [Complex.norm_exp] using hnorm
        simp_all
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  apply Integrable.mono' hmajorant hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_gaussDigammaIntegrand_le_tail hs hx.le

/-- A gauss digamma local radius used in the Odlyzko-bound argument. -/
noncomputable def gaussDigammaLocalRadius (s : ℂ) : ℝ :=
  min 1 (1 / (1 + ‖s - 1‖))

theorem norm_mul_gaussDigammaLocalRadius_le_one (s : ℂ) :
    ‖s - 1‖ * gaussDigammaLocalRadius s ≤ 1 := by
  have hr :
      gaussDigammaLocalRadius s ≤ 1 / (1 + ‖s - 1‖) :=
    min_le_right _ _
  calc
    ‖s - 1‖ * gaussDigammaLocalRadius s ≤
        ‖s - 1‖ * (1 / (1 + ‖s - 1‖)) := by gcongr
    _ ≤ 1 := by
      have hp : 0 < 1 + ‖s - 1‖ := by positivity
      rw [one_div, ← div_eq_mul_inv]
      exact (div_le_one hp).mpr (by linarith)

theorem gaussDigammaIntegrand_integrableOn_Ioc_zero_localRadius
    (s : ℂ) :
    IntegrableOn (gaussDigammaIntegrand s)
      (Ioc 0 (gaussDigammaLocalRadius s)) := by
  let r := gaussDigammaLocalRadius s
  have hr1 : r ≤ 1 := min_le_left _ _
  have hmajor :
      IntegrableOn (fun _ : ℝ ↦ 4 * ‖s - 1‖)
        (Ioc 0 r) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmeas :
      AEStronglyMeasurable (gaussDigammaIntegrand s)
        (volume.restrict (Ioc 0 r)) := by
    have hcont : ContinuousOn (gaussDigammaIntegrand s) (Ioc 0 r) := by
      intro x hx
      unfold gaussDigammaIntegrand
      apply ContinuousWithinAt.div
      · fun_prop
      · fun_prop
      · intro h
        have hexp : Complex.exp (-(x : ℂ)) = 1 :=
          sub_eq_zero.mp h |>.symm
        have hnorm := congrArg norm hexp
        have hre : Real.exp (-x) = Real.exp 0 := by
          simpa [Complex.norm_exp] using hnorm
        simp_all
    exact hcont.aestronglyMeasurable measurableSet_Ioc
  apply Integrable.mono' hmajor hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  apply norm_gaussDigammaIntegrand_le_local s hx.1
    (hx.2.trans hr1)
  calc
    ‖s - 1‖ * x ≤ ‖s - 1‖ * r := by gcongr; simp_all
    _ ≤ 1 := norm_mul_gaussDigammaLocalRadius_le_one s

theorem gaussDigammaIntegrand_integrableOn_Ioi
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (gaussDigammaIntegrand s) (Ioi 0) := by
  let r := gaussDigammaLocalRadius s
  have hr0 : 0 < r := by
    dsimp only [r, gaussDigammaLocalRadius]
    positivity
  have hlocal :=
    gaussDigammaIntegrand_integrableOn_Ioc_zero_localRadius s
  have hmiddle : IntegrableOn (gaussDigammaIntegrand s) (Ioc r 1) := by
    have hcont : ContinuousOn (gaussDigammaIntegrand s) (Icc r 1) := by
      intro x hx
      unfold gaussDigammaIntegrand
      apply ContinuousWithinAt.div
      · fun_prop
      · fun_prop
      · intro h
        have hexp : Complex.exp (-(x : ℂ)) = 1 :=
          sub_eq_zero.mp h |>.symm
        have hnorm := congrArg norm hexp
        have hre : Real.exp (-x) = Real.exp 0 := by
          simpa [Complex.norm_exp] using hnorm
        have : -x = 0 := Real.exp_injective hre
        grind
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have htail := gaussDigammaIntegrand_integrableOn_Ioi_one hs
  rw [show Ioi (0 : ℝ) = Ioc 0 r ∪ Ioc r 1 ∪ Ioi 1 by
    grind]
  exact (hlocal.union hmiddle).union htail

end NumberField.Odlyzko

end

section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

/-- A gauss digamma used in the Odlyzko-bound argument. -/
noncomputable def gaussDigamma (s : ℂ) : ℂ :=
  -Real.eulerMascheroniConstant +
    ∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x

end NumberField.Odlyzko

end

section

open Complex Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A gauss digamma partial integrand used in the Odlyzko-bound argument. -/
noncomputable def gaussDigammaPartialIntegrand (s : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n,
    (Complex.exp (-(k + 1 : ℂ) * x) -
      Complex.exp (-(s + k) * x))

/-- A gauss digamma partial sum used in the Odlyzko-bound argument. -/
noncomputable def gaussDigammaPartialSum (s : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℂ)⁻¹ - (s + k)⁻¹)

theorem gaussDigammaPartialIntegrand_eq
    (s : ℂ) (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    gaussDigammaPartialIntegrand s n x =
      (1 - Complex.exp (-n * x)) * gaussDigammaIntegrand s x := by
  induction n with
  | zero =>
      simp [gaussDigammaPartialIntegrand]
  | succ n ih =>
      rw [gaussDigammaPartialIntegrand, Finset.sum_range_succ]
      change
        gaussDigammaPartialIntegrand s n x +
            (Complex.exp (-(n + 1 : ℂ) * x) -
              Complex.exp (-(s + n) * x)) =
          (1 - Complex.exp (-(n + 1 : ℕ) * x)) *
            gaussDigammaIntegrand s x
      rw [ih]
      have hden : 1 - Complex.exp (-x) ≠ 0 := by
        intro h
        have hexp : Complex.exp (-(x : ℂ)) = 1 :=
          sub_eq_zero.mp h |>.symm
        have hnorm := congrArg norm hexp
        have hre : Real.exp (-x) = Real.exp 0 := by
          simpa [Complex.norm_exp] using hnorm
        simp_all
      have hpow_n :
          Complex.exp (-(n : ℂ) * x) =
            Complex.exp (-x) ^ n := by
        rw [← Complex.exp_nat_mul]
        simp
      have hpow_s :
          Complex.exp (-(s + n) * x) =
            Complex.exp (-s * x) * Complex.exp (-x) ^ n := by
        rw [← hpow_n, ← Complex.exp_add]
        grind
      have hterm_succ :
          Complex.exp (-(n + 1 : ℂ) * x) =
            Complex.exp (-x) * Complex.exp (-x) ^ n := by
        rw [← hpow_n, ← Complex.exp_add]
        grind
      have hfactor_succ :
          Complex.exp (-(n + 1 : ℕ) * x) =
            Complex.exp (-x) * Complex.exp (-x) ^ n := by simp_all
      rw [gaussDigammaIntegrand, hpow_n, hpow_s, hterm_succ,
        hfactor_succ]
      grind

theorem integral_gaussDigammaPartialIntegrand
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ x : ℝ in Ioi 0, gaussDigammaPartialIntegrand s n x) =
      gaussDigammaPartialSum s n := by
  unfold gaussDigammaPartialIntegrand gaussDigammaPartialSum
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    have hfirst :
        IntegrableOn
          (fun x : ℝ ↦ Complex.exp (-(k + 1 : ℂ) * x)) (Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (a := -(k + 1 : ℂ))
        (by
          simp only [neg_re, add_re, natCast_re, one_re]
          grind) 0
    have hsecond :
        IntegrableOn
          (fun x : ℝ ↦ Complex.exp (-(s + k) * x)) (Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (a := -(s + k))
        (by
          simp only [neg_re, add_re, natCast_re]
          grind) 0
    rw [integral_sub]
    · rw [integral_cexp_neg_mul_Ioi, integral_cexp_neg_mul_Ioi]
      · simp only [Nat.cast_add, Nat.cast_one, one_div]
      · simp only [add_re, natCast_re]
        grind
      · simp only [add_re, natCast_re, one_re]
        grind
    · exact hfirst
    · exact hsecond
  · intro k hk
    exact
      (integrableOn_exp_mul_complex_Ioi (a := -(k + 1 : ℂ))
        (by
          simp only [neg_re, add_re, natCast_re, one_re]
          grind) 0).sub
      (integrableOn_exp_mul_complex_Ioi (a := -(s + k))
        (by
          simp only [neg_re, add_re, natCast_re]
          grind) 0)

theorem tendsto_integral_gaussDigammaPartialIntegrand
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ ↦
        ∫ x : ℝ in Ioi 0, gaussDigammaPartialIntegrand s n x)
      atTop
      (𝓝 (∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x)) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let bound : ℝ → ℝ := fun x ↦ 2 * ‖gaussDigammaIntegrand s x‖
  have hint :
      Integrable (gaussDigammaIntegrand s) μ :=
    gaussDigammaIntegrand_integrableOn_Ioi hs
  apply tendsto_integral_of_dominated_convergence bound
  · intro n
    have hfactorMeas :
        AEStronglyMeasurable
          (fun x : ℝ ↦
            (1 - Complex.exp (-n * x)) *
              gaussDigammaIntegrand s x) μ :=
      (by fun_prop : Continuous
          (fun x : ℝ ↦ (1 - Complex.exp (-n * x)))).aestronglyMeasurable.mul
        hint.aestronglyMeasurable
    apply hfactorMeas.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (gaussDigammaPartialIntegrand_eq s n hx.ne').symm
  · simpa [bound] using hint.norm.const_mul 2
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [gaussDigammaPartialIntegrand_eq s n hx.ne', norm_mul]
    have hexpNorm :
        ‖Complex.exp (-n * x)‖ ≤ 1 := by
      rw [Complex.norm_exp]
      simp_all
    have hfactorNorm :
        ‖1 - Complex.exp (-n * x)‖ ≤ 2 := by
      calc
        ‖1 - Complex.exp (-n * x)‖ ≤
            ‖(1 : ℂ)‖ + ‖Complex.exp (-n * x)‖ :=
          norm_sub_le _ _
        _ ≤ 1 + 1 := by
          simpa using add_le_add_right hexpNorm 1
        _ = 2 := by norm_num
    calc
      ‖1 - Complex.exp (-n * x)‖ *
            ‖gaussDigammaIntegrand s x‖ ≤
          2 * ‖gaussDigammaIntegrand s x‖ := by
        exact mul_le_mul_of_nonneg_right hfactorNorm (norm_nonneg _)
      _ = bound x := by simp [bound]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hq :
        ‖Complex.exp (-x)‖ < 1 := by
      rw [Complex.norm_exp]
      simp_all
    have hp :
        Tendsto (fun n : ℕ ↦ Complex.exp (-x) ^ n)
          atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
    have hfactor :
        Tendsto
          (fun n : ℕ ↦
            (1 - Complex.exp (-x) ^ n) *
              gaussDigammaIntegrand s x)
          atTop
          (𝓝 (gaussDigammaIntegrand s x)) := by
      have hone :
          Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (𝓝 1) :=
        tendsto_const_nhds
      simpa using (hone.sub hp).mul_const (gaussDigammaIntegrand s x)
    apply hfactor.congr'
    filter_upwards [] with n
    rw [gaussDigammaPartialIntegrand_eq s n hx.ne']
    rw [← Complex.exp_nat_mul]
    simp

theorem tendsto_gaussDigammaPartialSum
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (gaussDigammaPartialSum s) atTop
      (𝓝 (∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x)) := by
  apply
    (tendsto_integral_gaussDigammaPartialIntegrand hs).congr'
  filter_upwards [] with n
  exact integral_gaussDigammaPartialIntegrand hs n

end NumberField.Odlyzko

end

section

open Complex

namespace NumberField.Odlyzko

theorem logDeriv_natCast_cpow
    {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    logDeriv (fun z : ℂ ↦ (n : ℂ) ^ z) s =
      Complex.log (n : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hderiv :=
    (hasDerivAt_id s).const_cpow (c := (n : ℂ)) (Or.inl hnC)
  have hderiv' :
      HasDerivAt (fun z : ℂ ↦ (n : ℂ) ^ z)
        ((n : ℂ) ^ s * Complex.log (n : ℂ)) s := by grind
  rw [logDeriv_apply, hderiv'.deriv]
  simp_all

private theorem logDeriv_add_nat (s : ℂ) (j : ℕ) :
    logDeriv (fun z : ℂ ↦ z + j) s = (s + j)⁻¹ := by
  rw [logDeriv_apply, deriv_add_const]
  simp only [deriv_id'', one_div]

theorem logDeriv_GammaSeq
    {s : ℂ} {n : ℕ} (hn : n ≠ 0)
    (hs : ∀ j ∈ Finset.range (n + 1), s + j ≠ 0) :
    logDeriv (fun z : ℂ ↦ Complex.GammaSeq z n) s =
      Complex.log (n : ℂ) -
        ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹ := by
  let numerator : ℂ → ℂ := fun z ↦ (n : ℂ) ^ z * (n.factorial : ℂ)
  let denominator : ℂ → ℂ := fun z ↦
    ∏ j ∈ Finset.range (n + 1), (z + j)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    norm_cast
    exact Nat.factorial_ne_zero n
  have hnum : numerator s ≠ 0 := by
    unfold numerator
    simp_all
  have hden : denominator s ≠ 0 := by
    unfold denominator
    exact Finset.prod_ne_zero_iff.mpr hs
  have hdnum : DifferentiableAt ℂ numerator s := by
    unfold numerator
    exact
      ((hasDerivAt_id s).const_cpow (c := (n : ℂ)) (Or.inl hnC))
        |>.differentiableAt.mul (differentiableAt_const _)
  have hdden : DifferentiableAt ℂ denominator s := by
    unfold denominator
    fun_prop
  change logDeriv (fun z : ℂ ↦ numerator z / denominator z) s = _
  rw [logDeriv_div s hnum hden hdnum hdden]
  have hnumFormula :
      logDeriv numerator s = Complex.log (n : ℂ) := by
    unfold numerator
    rw [logDeriv_mul_const s (n.factorial : ℂ) hfac]
    exact logDeriv_natCast_cpow hn s
  have hdenFormula :
      logDeriv denominator s =
        ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹ := by
    unfold denominator
    rw [logDeriv_prod hs]
    · apply Finset.sum_congr rfl
      intro j hj
      exact logDeriv_add_nat s j
    · simp
  simp_all

end NumberField.Odlyzko

end

section

open Complex Filter Real
open scoped Topology

namespace NumberField.Odlyzko

private theorem sum_range_natCast_inv_eq_harmonic (n : ℕ) :
    (∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℂ)⁻¹)) =
      (harmonic n : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      simp

theorem logDeriv_GammaSeq_succ_eq
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    logDeriv (fun z : ℂ ↦ Complex.GammaSeq z (n + 1)) s =
      gaussDigammaPartialSum s (n + 1) -
        (Real.eulerMascheroniSeq' (n + 1) : ℂ) -
          (s + (n + 1 : ℕ))⁻¹ := by
  have hnonzero :
      ∀ j ∈ Finset.range ((n + 1) + 1), s + j ≠ 0 := by
    intro j hj h
    have hre := congrArg Complex.re h
    simp only [add_re, natCast_re, zero_re] at hre
    grind
  rw [logDeriv_GammaSeq (Nat.succ_ne_zero n) hnonzero]
  rw [Finset.sum_range_succ]
  unfold gaussDigammaPartialSum
  have hharm :
      (∑ k ∈ Finset.range (n + 1),
          (((k + 1 : ℕ) : ℂ)⁻¹)) =
        (harmonic (n + 1) : ℂ) :=
    sum_range_natCast_inv_eq_harmonic (n + 1)
  rw [Real.eulerMascheroniSeq', ite_eq_right (Nat.succ_ne_zero n)]
  rw [Finset.sum_sub_distrib, hharm]
  push_cast
  have hlog :
      Complex.log ((n : ℂ) + 1) =
        (Real.log ((n : ℝ) + 1) : ℂ) := by
    simpa using
      (Complex.ofReal_log
        (show 0 ≤ (n : ℝ) + 1 by positivity)).symm
  grind

end NumberField.Odlyzko

end

section

open Complex Filter Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A gauss digamma series term used in the Odlyzko-bound argument. -/
noncomputable def gaussDigammaSeriesTerm (k : ℕ) (s : ℂ) : ℂ :=
  (((k + 1 : ℕ) : ℂ)⁻¹ - (s + k)⁻¹)

private theorem gaussDigammaPartialSum_eq_sum_seriesTerm (s : ℂ) (n : ℕ) :
    gaussDigammaPartialSum s n =
      ∑ k ∈ Finset.range n, gaussDigammaSeriesTerm k s :=
  rfl

theorem gaussDigammaSeriesTerm_eq_div
    {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    gaussDigammaSeriesTerm k s =
      (s - 1) / (((k + 1 : ℕ) : ℂ) * (s + k)) := by
  have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have hsk : s + k ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, natCast_re, zero_re] at hre
    grind
  unfold gaussDigammaSeriesTerm
  grind

theorem norm_gaussDigammaSeriesTerm_le
    {M : ℝ} {s : ℂ} (hs : 0 < s.re) (hsM : ‖s - 1‖ ≤ M)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖gaussDigammaSeriesTerm k s‖ ≤ M / (k : ℝ) ^ 2 := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hk)
  have hM : 0 ≤ M := (norm_nonneg _).trans hsM
  have hsk :
      (k : ℝ) ≤ ‖s + k‖ := by
    calc
      (k : ℝ) ≤ s.re + k := by linarith
      _ = (s + k).re := by simp
      _ ≤ ‖s + k‖ := Complex.re_le_norm _
  have hk1norm :
      ‖(((k + 1 : ℕ) : ℂ))‖ = (k + 1 : ℕ) := by
    change ‖(((k + 1 : ℕ) : ℝ) : ℂ)‖ = ((k + 1 : ℕ) : ℝ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    grind
  rw [gaussDigammaSeriesTerm_eq_div hs, norm_div, norm_mul,
    hk1norm]
  have hden :
      (k : ℝ) ^ 2 ≤
        (k + 1 : ℕ) * ‖s + k‖ := by
    rw [pow_two]
    calc
      (k : ℝ) * k ≤ (k + 1 : ℕ) * k := by simp_all
      _ ≤ (k + 1 : ℕ) * ‖s + k‖ := by
        gcongr
  exact div_le_div₀ hM hsM (sq_pos_of_pos hkR) hden

theorem tendstoUniformlyOn_gaussDigammaPartialSum
    (M : ℝ) :
    TendstoUniformlyOn
      (fun n s ↦ gaussDigammaPartialSum s n)
      (fun s ↦ ∑' k, gaussDigammaSeriesTerm k s)
      atTop {s : ℂ | 0 < s.re ∧ ‖s - 1‖ ≤ M} := by
  have hu :
      Summable (fun k : ℕ ↦ M / (k : ℝ) ^ 2) := by
    have h :=
      (Real.summable_one_div_nat_pow.mpr
        (show 1 < (2 : ℕ) by norm_num)).mul_left M
    grind
  rw [show (fun n s ↦ gaussDigammaPartialSum s n) =
      (fun n s ↦ ∑ k ∈ Finset.range n,
        gaussDigammaSeriesTerm k s) by
    funext n s
    exact gaussDigammaPartialSum_eq_sum_seriesTerm s n]
  apply tendstoUniformlyOn_tsum_nat_eventually hu
  filter_upwards [eventually_ge_atTop 1] with k hk s hs
  exact norm_gaussDigammaSeriesTerm_le hs.1 hs.2 hk

theorem tsum_gaussDigammaSeriesTerm_eq_integral
    {s : ℂ} (hs : 0 < s.re) :
    (∑' k, gaussDigammaSeriesTerm k s) =
      ∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x := by
  exact tendsto_nhds_unique
    ((tendstoUniformlyOn_gaussDigammaPartialSum ‖s - 1‖).tendsto_at
      ⟨hs, le_rfl⟩)
    (tendsto_gaussDigammaPartialSum hs)

theorem tendstoLocallyUniformlyOn_gaussDigammaPartialSum :
    TendstoLocallyUniformlyOn
      (fun n s ↦ gaussDigammaPartialSum s n)
      (fun s ↦ ∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x)
      atTop {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen]
  intro K hKsub hK
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.mp hK.isBounded
  have hsubset :
      K ⊆ {s : ℂ | 0 < s.re ∧ ‖s - 1‖ ≤ C + 1} := by
    intro s hsK
    refine ⟨hKsub hsK, ?_⟩
    exact (norm_sub_le s 1).trans
      (by simpa using add_le_add_right (hC s hsK) 1)
  have huniform :=
    (tendstoUniformlyOn_gaussDigammaPartialSum (C + 1)).mono hsubset
  apply huniform.congr_right
  intro s hsK
  exact tsum_gaussDigammaSeriesTerm_eq_integral (hKsub hsK)

end NumberField.Odlyzko

end

section

open Complex Filter Real Set
open scoped Topology

namespace NumberField.Odlyzko

theorem norm_inv_add_natCast_le
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖(s + (n : ℂ))⁻¹‖ ≤ 1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hnorm :
      (n : ℝ) ≤ ‖s + (n : ℂ)‖ := by
    calc
      (n : ℝ) ≤ s.re + n := by linarith
      _ = (s + (n : ℂ)).re := by simp
      _ ≤ ‖s + (n : ℂ)‖ := Complex.re_le_norm _
  rw [norm_inv, one_div]
  exact inv_anti₀ hnR hnorm

theorem tendstoUniformlyOn_inv_add_natCast_succ :
    TendstoUniformlyOn
      (fun n (s : ℂ) ↦ (s + (n + 1 : ℕ))⁻¹)
      (fun _ ↦ 0)
      atTop {s : ℂ | 0 < s.re} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hscalar :
      Tendsto (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hscalar ε hε
  filter_upwards [eventually_ge_atTop N] with n hn s hs
  simp only [dist_zero_left]
  exact
    (norm_inv_add_natCast_le hs
      (Nat.succ_le_succ (Nat.zero_le n))).trans_lt
        (by
          have hnonneg : 0 ≤ (n : ℝ) + 1 := by positivity
          have hinvnonneg : 0 ≤ ((n : ℝ) + 1)⁻¹ :=
            inv_nonneg.mpr hnonneg
          simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg,
            abs_of_nonneg hinvnonneg, one_div, Nat.cast_add,
            Nat.cast_succ, Nat.cast_one] using hN n hn)

theorem tendstoLocallyUniformlyOn_logDeriv_GammaSeq_succ :
    TendstoLocallyUniformlyOn
      (fun n s ↦ logDeriv (fun z : ℂ ↦ Complex.GammaSeq z (n + 1)) s)
      gaussDigamma
      atTop {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen]
  intro K hKsub hK
  have hpartialBase :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).mp
      tendstoLocallyUniformlyOn_gaussDigammaPartialSum K hKsub hK
  have hpartial :=
    show TendstoUniformlyOn
      (fun n s ↦ gaussDigammaPartialSum s (n + 1))
      (fun s ↦ ∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x)
      atTop K by
      rw [Metric.tendstoUniformlyOn_iff] at hpartialBase ⊢
      intro ε hε
      exact (Filter.tendsto_add_atTop_nat 1).eventually
        (hpartialBase ε hε)
  have heulerReal :=
    Real.tendsto_eulerMascheroniSeq'.comp
      (Filter.tendsto_add_atTop_nat 1)
  have heuler :
      Tendsto
        (fun n : ℕ ↦
          (Real.eulerMascheroniSeq' (n + 1) : ℂ))
        atTop
        (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp heulerReal
  have heulerUniform :=
    heuler.tendstoUniformlyOn_const K
  have htail :=
    tendstoUniformlyOn_inv_add_natCast_succ.mono hKsub
  have hcombined :=
    (hpartial.sub heulerUniform).sub htail
  have hlimit :
      (fun s : ℂ ↦
          (∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x) -
            (Real.eulerMascheroniConstant : ℂ) - 0) =
        gaussDigamma := by
    funext s
    unfold gaussDigamma
    ring
  rw [← hlimit]
  apply hcombined.congr
  filter_upwards [] with n s hs
  exact (logDeriv_GammaSeq_succ_eq (hKsub hs) n).symm

end NumberField.Odlyzko

end

section

open Complex Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A gamma seq approx integrand used in the Odlyzko-bound argument. -/
noncomputable def gammaSeqApproxIntegrand (n : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  (Ioc 0 (n : ℝ)).indicator
    (fun x ↦ ((1 - x / n) ^ n : ℝ) * (x : ℂ) ^ (s - 1)) x

/-- A gamma integral integrand used in the Odlyzko-bound argument. -/
noncomputable def gammaIntegralIntegrand (s : ℂ) (x : ℝ) : ℂ :=
  (Ioi 0).indicator
    (fun x ↦ (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)) x

/-- A gamma vertical majorant used in the Odlyzko-bound argument. -/
noncomputable def gammaVerticalMajorant (a b : ℝ) (x : ℝ) : ℝ :=
  (Ioi 0).indicator
    (fun x ↦ Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1))) x

theorem integral_gammaSeqApproxIntegrand
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    (∫ x : ℝ, gammaSeqApproxIntegrand n s x) =
      Complex.GammaSeq s n := by
  rw [Complex.GammaSeq_eq_approx_Gamma_integral hs hn]
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  rfl

theorem integral_gammaIntegralIntegrand
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ, gammaIntegralIntegrand s x) = Complex.Gamma s := by
  rw [show gammaIntegralIntegrand s =
      (Ioi 0).indicator
        (fun x ↦ (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)) by rfl]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi,
    show (∫ x : ℝ in Ioi 0,
      (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)) =
      Complex.GammaIntegral s by rfl]
  exact (Complex.Gamma_eq_integral hs).symm

theorem rpow_re_sub_one_le_endpoint_sum
    {a b x : ℝ} {s : ℂ}
    (hx : 0 < x) (ha : a ≤ s.re) (hb : s.re ≤ b) :
    x ^ (s.re - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
  rcases le_total x 1 with hx1 | hx1
  · have hpow :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1
        (show a - 1 ≤ s.re - 1 by linarith)
    exact hpow.trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
  · have hpow :=
      Real.rpow_le_rpow_of_exponent_le hx1
        (show s.re - 1 ≤ b - 1 by linarith)
    exact hpow.trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))

end NumberField.Odlyzko

end

section

open Complex Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A gamma seq scalar kernel used in the Odlyzko-bound argument. -/
noncomputable def gammaSeqScalarKernel (n : ℕ) (x : ℝ) : ℝ :=
  (Ioc 0 (n : ℝ)).indicator (fun x ↦ (1 - x / n) ^ n) x

/-- A gamma scalar kernel used in the Odlyzko-bound argument. -/
noncomputable def gammaScalarKernel (x : ℝ) : ℝ :=
  (Ioi 0).indicator (fun x ↦ Real.exp (-x)) x

/-- A gamma seq integral error used in the Odlyzko-bound argument. -/
noncomputable def gammaSeqIntegralError (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  |gammaSeqScalarKernel n x - gammaScalarKernel x| *
    (Ioi 0).indicator (fun x ↦ x ^ (a - 1) + x ^ (b - 1)) x

theorem integrable_gammaVerticalMajorant
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (gammaVerticalMajorant a b) := by
  change Integrable
    ((Ioi 0).indicator
      (fun x : ℝ ↦ Real.exp (-x) *
        (x ^ (a - 1) + x ^ (b - 1))))
  rw [integrable_indicator_iff measurableSet_Ioi]
  convert
    (Real.GammaIntegral_convergent ha).add
      (Real.GammaIntegral_convergent hb) using 1
  ext x
  simp only [Pi.add_apply]
  ring

private theorem gammaSeqScalarKernel_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ gammaSeqScalarKernel n x := by
  by_cases hx : x ∈ Ioc 0 (n : ℝ)
  · rw [gammaSeqScalarKernel, indicator_of_mem hx]
    exact pow_nonneg
      (sub_nonneg.mpr
        (div_le_one_of_le₀ hx.2 (Nat.cast_nonneg n))) n
  · rw [gammaSeqScalarKernel, indicator_of_notMem hx]

private theorem gammaScalarKernel_nonneg (x : ℝ) :
    0 ≤ gammaScalarKernel x := by
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [gammaScalarKernel, indicator_of_mem hx]
    exact (Real.exp_pos _).le
  · rw [gammaScalarKernel, indicator_of_notMem hx]

theorem gammaSeqScalarKernel_le (n : ℕ) (x : ℝ) :
    gammaSeqScalarKernel n x ≤ gammaScalarKernel x := by
  by_cases hx : x ∈ Ioc 0 (n : ℝ)
  · have hxpos : x ∈ Ioi (0 : ℝ) := hx.1
    rw [gammaSeqScalarKernel, indicator_of_mem hx,
      gammaScalarKernel, indicator_of_mem hxpos]
    exact one_sub_div_pow_le_exp_neg hx.2
  · rw [gammaSeqScalarKernel, indicator_of_notMem hx]
    exact gammaScalarKernel_nonneg x

theorem tendsto_gammaSeqScalarKernel (x : ℝ) :
    Tendsto (fun n : ℕ ↦ gammaSeqScalarKernel n x)
      atTop (𝓝 (gammaScalarKernel x)) := by
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · apply Tendsto.congr'
    · filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
      have hxn : x ≤ (n : ℝ) := by simp_all
      rw [gammaSeqScalarKernel,
        indicator_of_mem (show x ∈ Ioc 0 (n : ℝ) from ⟨hx, hxn⟩)]
    · rw [show gammaScalarKernel x = Real.exp (-x) by
        rw [gammaScalarKernel, indicator_of_mem hx]]
      convert Real.tendsto_one_add_div_pow_exp (-x) using 1
      grind
  · have hxnot : ∀ n : ℕ, x ∉ Ioc 0 (n : ℝ) :=
      fun _ h ↦ hx h.1
    simpa only [gammaSeqScalarKernel, gammaScalarKernel,
      indicator_of_notMem hx, indicator_of_notMem (hxnot _)] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

theorem tendsto_gammaSeqIntegralError (a b x : ℝ) :
    Tendsto (fun n : ℕ ↦ gammaSeqIntegralError a b n x)
      atTop (𝓝 0) := by
  unfold gammaSeqIntegralError
  have hsub :
      Tendsto
        (fun n : ℕ ↦ gammaSeqScalarKernel n x - gammaScalarKernel x)
        atTop (𝓝 0) := by
    simpa using
      (tendsto_gammaSeqScalarKernel x).sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ gammaScalarKernel x)
            atTop (𝓝 (gammaScalarKernel x)))
  simpa using
    (hsub.abs.mul_const
      ((Ioi 0).indicator
        (fun x ↦ x ^ (a - 1) + x ^ (b - 1)) x))

theorem gammaSeqIntegralError_le_majorant
    (a b : ℝ) (n : ℕ) (x : ℝ) :
    gammaSeqIntegralError a b n x ≤ gammaVerticalMajorant a b x := by
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [gammaSeqIntegralError, gammaVerticalMajorant,
      indicator_of_mem hx, indicator_of_mem hx]
    have hnonneg :=
      gammaSeqScalarKernel_nonneg n x
    have hle :=
      gammaSeqScalarKernel_le n x
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    have hfactor :
        0 ≤ x ^ (a - 1) + x ^ (b - 1) :=
      add_nonneg (Real.rpow_nonneg hx.le _)
        (Real.rpow_nonneg hx.le _)
    exact mul_le_mul_of_nonneg_right
      (by
        rw [gammaScalarKernel, indicator_of_mem hx]
        linarith)
      hfactor
  · rw [gammaSeqIntegralError, gammaVerticalMajorant,
      indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

theorem gammaSeqIntegralError_nonneg
    (a b : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ gammaSeqIntegralError a b n x := by
  unfold gammaSeqIntegralError
  apply mul_nonneg (abs_nonneg _)
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hx]
    exact add_nonneg (Real.rpow_nonneg hx.le _)
      (Real.rpow_nonneg hx.le _)
  · simp_all

private theorem measurable_gammaSeqScalarKernel (n : ℕ) :
    Measurable (gammaSeqScalarKernel n) := by
  unfold gammaSeqScalarKernel
  apply Measurable.indicator _ measurableSet_Ioc
  fun_prop

private theorem measurable_gammaScalarKernel :
    Measurable gammaScalarKernel := by
  unfold gammaScalarKernel
  apply Measurable.indicator _ measurableSet_Ioi
  fun_prop

theorem aestronglyMeasurable_gammaSeqIntegralError
    (a b : ℝ) (n : ℕ) :
    AEStronglyMeasurable (gammaSeqIntegralError a b n) := by
  unfold gammaSeqIntegralError
  apply AEStronglyMeasurable.mul
  · exact
      (continuous_abs.measurable.comp
        ((measurable_gammaSeqScalarKernel n).sub
          measurable_gammaScalarKernel)).aestronglyMeasurable
  · rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi]
    exact
      ((continuousOn_id.rpow_const
          (fun x hx ↦ Or.inl hx.ne')).add
        (continuousOn_id.rpow_const
          (fun x hx ↦ Or.inl hx.ne'))).aestronglyMeasurable
        measurableSet_Ioi

theorem integrable_gammaSeqIntegralError
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Integrable (gammaSeqIntegralError a b n) := by
  apply (integrable_gammaVerticalMajorant ha hb).mono'
    (aestronglyMeasurable_gammaSeqIntegralError a b n)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,
    abs_of_nonneg (gammaSeqIntegralError_nonneg a b n x)]
  exact gammaSeqIntegralError_le_majorant a b n x

theorem tendsto_integral_gammaSeqIntegralError
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦ ∫ x : ℝ, gammaSeqIntegralError a b n x)
      atTop (𝓝 0) := by
  have h :=
    tendsto_integral_of_dominated_convergence
      (gammaVerticalMajorant a b)
      (fun n ↦
        aestronglyMeasurable_gammaSeqIntegralError a b n)
      (integrable_gammaVerticalMajorant ha hb)
      (fun n ↦ ?_)
      (ae_of_all _ fun x ↦ tendsto_gammaSeqIntegralError a b x)
  · simpa using h
  · filter_upwards [] with x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (gammaSeqIntegralError_nonneg a b n x)]
    exact gammaSeqIntegralError_le_majorant a b n x

theorem integrable_gammaSeqApproxIntegrand
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Integrable (gammaSeqApproxIntegrand n s) := by
  change Integrable
    ((Ioc 0 (n : ℝ)).indicator
      (fun x ↦ ((1 - x / n) ^ n : ℝ) *
        (x : ℂ) ^ (s - 1)))
  rw [integrable_indicator_iff measurableSet_Ioc]
  change IntegrableOn
    (fun x ↦ ((1 - x / n) ^ n : ℝ) *
      (x : ℂ) ^ (s - 1)) (Ioc 0 (n : ℝ))
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le
    (Nat.cast_nonneg n)]
  apply IntervalIntegrable.continuousOn_mul
  · refine intervalIntegral.intervalIntegrable_cpow' ?_
    simp_all
  · fun_prop

theorem integrable_gammaIntegralIntegrand
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (gammaIntegralIntegrand s) := by
  change Integrable
    ((Ioi 0).indicator
      (fun x ↦ (Real.exp (-x) : ℂ) *
        (x : ℂ) ^ (s - 1)))
  rw [integrable_indicator_iff measurableSet_Ioi]
  exact Complex.GammaIntegral_convergent hs

theorem norm_gammaSeqApproxIntegrand_sub_le_error
    {a b : ℝ} {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b)
    (n : ℕ) (x : ℝ) :
    ‖gammaSeqApproxIntegrand n s x -
        gammaIntegralIntegrand s x‖ ≤
      gammaSeqIntegralError a b n x := by
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · have happ :
        gammaSeqApproxIntegrand n s x =
          (gammaSeqScalarKernel n x : ℂ) *
            (x : ℂ) ^ (s - 1) := by
      by_cases hxn : x ∈ Ioc 0 (n : ℝ)
      · rw [gammaSeqApproxIntegrand, indicator_of_mem hxn,
          gammaSeqScalarKernel, indicator_of_mem hxn]
      · rw [gammaSeqApproxIntegrand, indicator_of_notMem hxn,
          gammaSeqScalarKernel, indicator_of_notMem hxn,
          ofReal_zero, zero_mul]
    have hlim :
        gammaIntegralIntegrand s x =
          (gammaScalarKernel x : ℂ) *
            (x : ℂ) ^ (s - 1) := by
      rw [gammaIntegralIntegrand, indicator_of_mem hx,
        gammaScalarKernel, indicator_of_mem hx]
    rw [happ, hlim, ← sub_mul, norm_mul, ← ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx,
      sub_re, one_re, gammaSeqIntegralError,
      indicator_of_mem hx]
    exact mul_le_mul_of_nonneg_left
      (rpow_re_sub_one_le_endpoint_sum hx ha hb)
      (abs_nonneg _)
  · have hxIoc : ∀ n : ℕ, x ∉ Ioc 0 (n : ℝ) :=
      fun _ h ↦ hx h.1
    rw [gammaSeqApproxIntegrand,
      indicator_of_notMem (hxIoc n),
      gammaIntegralIntegrand, indicator_of_notMem hx,
      sub_zero, norm_zero, gammaSeqIntegralError,
      indicator_of_notMem hx, mul_zero]

theorem norm_integral_gammaSeqApproxIntegrand_sub_le
    {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b)
    (n : ℕ) :
    ‖(∫ x : ℝ, gammaSeqApproxIntegrand n s x) -
        ∫ x : ℝ, gammaIntegralIntegrand s x‖ ≤
      ∫ x : ℝ, gammaSeqIntegralError a b n x := by
  have hs : 0 < s.re := ha0.trans_le ha
  rw [← integral_sub
    (integrable_gammaSeqApproxIntegrand hs n)
    (integrable_gammaIntegralIntegrand hs)]
  exact norm_integral_le_of_norm_le
    (integrable_gammaSeqIntegralError ha0 hb0 n)
    (ae_of_all _ fun x ↦
      norm_gammaSeqApproxIntegrand_sub_le_error ha hb n x)

theorem tendstoUniformlyOn_integral_gammaSeqApproxIntegrand
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn
      (fun n s ↦ ∫ x : ℝ, gammaSeqApproxIntegrand n s x)
      (fun s ↦ ∫ x : ℝ, gammaIntegralIntegrand s x)
      atTop {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
  have hb : 0 < b := ha.trans_le hab
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.1
      (tendsto_integral_gammaSeqIntegralError ha hb) ε hε
  filter_upwards [eventually_ge_atTop N] with n hn s hs
  rw [dist_eq_norm, norm_sub_rev]
  refine
    (norm_integral_gammaSeqApproxIntegrand_sub_le
      ha hb hs.1 hs.2 n).trans_lt ?_
  have hnonneg :
      0 ≤ ∫ x : ℝ, gammaSeqIntegralError a b n x :=
    integral_nonneg
      (fun x ↦ gammaSeqIntegralError_nonneg a b n x)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
    hN n hn

theorem tendstoUniformlyOn_GammaSeq
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn
      (fun n s ↦ Complex.GammaSeq s n)
      Complex.Gamma
      atTop {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
  have h :=
    tendstoUniformlyOn_integral_gammaSeqApproxIntegrand ha hab
  have h' := h.congr (by
    filter_upwards [eventually_ne_atTop 0] with n hn s hs
    exact integral_gammaSeqApproxIntegrand
      (ha.trans_le hs.1) hn)
  exact h'.congr_right fun s hs ↦
    integral_gammaIntegralIntegrand (ha.trans_le hs.1)

theorem tendstoLocallyUniformlyOn_GammaSeq :
    TendstoLocallyUniformlyOn
      (fun n s ↦ Complex.GammaSeq s n)
      Complex.Gamma
      atTop {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen]
  intro K hKsub hK
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  · obtain ⟨smin, hsminK, hsmin⟩ :=
      hK.exists_isMinOn hKne continuous_re.continuousOn
    obtain ⟨smax, hsmaxK, hsmax⟩ :=
      hK.exists_isMaxOn hKne continuous_re.continuousOn
    have hamin : 0 < smin.re := hKsub hsminK
    have hab : smin.re ≤ smax.re :=
      isMinOn_iff.mp hsmin smax hsmaxK
    apply
      (tendstoUniformlyOn_GammaSeq hamin hab).mono
    intro s hsK
    exact
      ⟨isMinOn_iff.mp hsmin s hsK,
        isMaxOn_iff.mp hsmax s hsK⟩

end NumberField.Odlyzko

end

section

open Complex Filter Set
open scoped Topology

namespace NumberField.Odlyzko

theorem tendstoLocallyUniformlyOn_GammaSeq_succ :
    TendstoLocallyUniformlyOn
      (fun n s ↦ Complex.GammaSeq s (n + 1))
      Complex.Gamma
      atTop {s : ℂ | 0 < s.re} := by
  intro u hu s hs
  obtain ⟨t, ht, hEventually⟩ :=
    tendstoLocallyUniformlyOn_GammaSeq u hu s hs
  exact
    ⟨t, ht,
      (Filter.tendsto_add_atTop_nat 1).eventually hEventually⟩

theorem differentiableOn_GammaSeq_succ (n : ℕ) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ Complex.GammaSeq s (n + 1))
      {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  unfold Complex.GammaSeq
  apply DifferentiableAt.differentiableWithinAt
  have hnC : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hnum :
      DifferentiableAt ℂ
        (fun z : ℂ ↦
          ((n + 1 : ℕ) : ℂ) ^ z *
            ((n + 1).factorial : ℂ)) s :=
    ((hasDerivAt_id s).const_cpow
      (c := ((n + 1 : ℕ) : ℂ)) (Or.inl hnC))
      |>.differentiableAt.mul (differentiableAt_const _)
  have hden :
      DifferentiableAt ℂ
        (fun z : ℂ ↦
          ∏ j ∈ Finset.range (n + 1 + 1), (z + j)) s := by
    fun_prop
  apply hnum.div hden
  exact Finset.prod_ne_zero_iff.mpr fun j hj hzero ↦ by
    have hre := congrArg Complex.re hzero
    simp only [add_re, natCast_re, zero_re] at hre
    grind

theorem gaussDigamma_eq_digamma
    {s : ℂ} (hs : 0 < s.re) :
    gaussDigamma s = Complex.digamma s := by
  have hGauss :=
    tendstoLocallyUniformlyOn_logDeriv_GammaSeq_succ.tendsto_at hs
  have hMathlib :=
    Complex.logDeriv_tendsto
      (continuous_re.isOpen_preimage _ isOpen_Ioi)
      hs
      tendstoLocallyUniformlyOn_GammaSeq_succ
      (Eventually.of_forall differentiableOn_GammaSeq_succ)
      (Complex.Gamma_ne_zero_of_re_pos hs)
  exact tendsto_nhds_unique hGauss hMathlib

end NumberField.Odlyzko

end
