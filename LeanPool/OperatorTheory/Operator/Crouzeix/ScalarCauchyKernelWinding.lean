/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCauchyKernelConstancy
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanSupport
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Winding normalization from oriented convex geometry

For a consistently oriented point `c` of a smooth strictly convex carrier,
the logarithmic derivative

`gamma'(t) / (gamma(t) - c)`

has strictly positive imaginary part.  Its interval integral is therefore a
strictly increasing argument lift.  Solving the associated exponential ODE
and using periodicity shows that the lift changes by a positive natural
multiple of `2 * pi` over one period.

There cannot be two turns: the intermediate value theorem would then give a
second boundary point on the same positive ray from `c` as the initial one.
Convexity puts the nearer of two such frontier points in the open carrier,
unless the points coincide; fundamental-interval injectivity excludes that
last possibility.  Thus the winding is exactly one.

## Main declarations

* `crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier_point` -- oriented
  convex geometry normalizes the kernel at the selected carrier point;
* `crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier` -- the normalization
  propagates throughout the carrier.
-/

open Complex Filter MeasureTheory Set
open scoped Interval Real

private theorem boundaryLogDeriv_im_pos
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    (t : ℝ) :
    0 < (deriv Omega.boundaryParam t /
      (Omega.boundaryParam t - c)).im := by
  let D := deriv Omega.boundaryParam t
  let d := Omega.boundaryParam t - c
  have hd : d ≠ 0 := by
    intro hzero
    have heq : Omega.boundaryParam t = c := sub_eq_zero.mp hzero
    have hfrontier : c ∈ frontier Omega.carrier := by
      rw [← heq, ← Omega.boundaryParam_range]
      exact mem_range_self t
    have hempty : c ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hc, hfrontier⟩
    exact hempty
  have hnormal :
      ((starRingEnd ℂ) (-I * D) * (-d)).re < 0 := by
    have hstrict :=
      (Omega.closure_support_and_carrier_strict_of_support_at_mem_carrier
        c hc t (hcside t)).2 c hc
    simpa only [D, d, neg_sub] using hstrict
  have hnum : 0 < D.im * d.re - D.re * d.im := by
    have hid : ((starRingEnd ℂ) (-I * D) * (-d)).re =
        -(D.im * d.re - D.re * d.im) := by
      simp only [map_mul, map_neg, Complex.conj_I, Complex.mul_re,
        Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
        Complex.I_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [hid] at hnormal
    linarith
  rw [Complex.div_im, ← sub_div]
  exact div_pos hnum (Complex.normSq_pos.mpr hd)

private theorem frontier_same_positive_ray_eq
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    {x y : ℂ} (hx : x ∈ frontier Omega.carrier)
    (hy : y ∈ frontier Omega.carrier) {a : ℝ} (ha : 0 < a)
    (hxy : y - c = (a : ℂ) * (x - c)) : x = y := by
  by_cases haone : a = 1
  · subst a
    simpa only [ofReal_one, one_mul, sub_left_inj] using hxy.symm
  have hcint : c ∈ interior Omega.carrier := by
    rwa [Omega.isOpen_carrier.interior_eq]
  rcases lt_or_gt_of_ne haone with halt | haalt
  · have hcombo : y = (1 - a) • c + a • x := by
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      linear_combination hxy
    have hyint : y ∈ interior Omega.carrier := by
      rw [hcombo]
      exact Omega.strictConvex_carrier.convex.combo_interior_closure_mem_interior
        hcint (frontier_subset_closure hx) (sub_pos.mpr halt) ha.le (by ring)
    have hycarrier : y ∈ Omega.carrier := by
      rwa [Omega.isOpen_carrier.interior_eq] at hyint
    have hempty : y ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hycarrier, hy⟩
    simp only [Set.mem_empty_iff_false] at hempty
  · have hainv : 0 < a⁻¹ := inv_pos.mpr ha
    have hainvlt : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ haalt
    have hratio : x - c = ((a : ℂ))⁻¹ * (y - c) := by
      rw [hxy]
      field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt ha)]
    have hcombo : x = (1 - a⁻¹) • c + a⁻¹ • y := by
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      linear_combination hratio
    have hxint : x ∈ interior Omega.carrier := by
      rw [hcombo]
      exact Omega.strictConvex_carrier.convex.combo_interior_closure_mem_interior
        hcint (frontier_subset_closure hy) (sub_pos.mpr hainvlt)
          hainv.le (by ring)
    have hxcarrier : x ∈ Omega.carrier := by
      rwa [Omega.isOpen_carrier.interior_eq] at hxint
    have hempty : x ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hxcarrier, hx⟩
    simp only [Set.mem_empty_iff_false] at hempty

/-- A consistently oriented carrier point has normalized scalar winding one.
The proof obtains the total argument change from the logarithmic-derivative
ODE and uses convexity to exclude every positive integer other than one. -/
theorem crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier_point
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    crouzeixScalarCauchyKernel Omega c = 1 := by
  classical
  let gamma := Omega.boundaryParam
  let T := 2 * Real.pi
  let q : ℝ → ℂ := fun t => gamma t - c
  let r : ℝ → ℂ := fun t => deriv gamma t / q t
  let L : ℝ → ℂ := fun t => ∫ x in (0 : ℝ)..t, r x
  let theta : ℝ → ℝ := fun t => (L t).im
  let F : ℝ → ℂ := q * fun t => Complex.exp (-L t)
  have hT : 0 < T := Real.two_pi_pos
  have hqne : ∀ t : ℝ, q t ≠ 0 := by
    intro t hzero
    have heq : gamma t = c := sub_eq_zero.mp hzero
    have hfrontier : c ∈ frontier Omega.carrier := by
      rw [← heq, ← Omega.boundaryParam_range]
      exact mem_range_self t
    have hempty : c ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hc, hfrontier⟩
    exact hempty
  have hrcont : Continuous r := by
    apply Continuous.div
    · exact Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)
    · exact Omega.boundaryParam_contDiff.continuous.sub continuous_const
    · exact hqne
  have hLDeriv : ∀ t : ℝ, HasDerivAt L (r t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hrcont.intervalIntegrable 0 t)
      (hrcont.stronglyMeasurableAtFilter volume (nhds t))
      hrcont.continuousAt
  have hthetaDeriv : ∀ t : ℝ, HasDerivAt theta (r t).im t := by
    intro t
    convert!
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hLDeriv t) using 1
  have hrim : ∀ t : ℝ, 0 < (r t).im := by
    intro t
    exact boundaryLogDeriv_im_pos Omega c hc hcside t
  have hthetaStrict : StrictMono theta :=
    strictMono_of_hasDerivAt_pos hthetaDeriv hrim
  have hqDeriv : ∀ t : ℝ, HasDerivAt q (deriv gamma t) t := by
    intro t
    exact
      (Omega.boundaryParam_contDiff.differentiable (by norm_num) t).hasDerivAt.sub_const c
  have hFDeriv : ∀ t : ℝ, HasDerivAt F 0 t := by
    intro t
    have hprod := (hqDeriv t).mul ((hLDeriv t).neg.cexp)
    have hrel : deriv gamma t = r t * q t := by
      dsimp only [r]
      field_simp [hqne t]
    have hzero :
        deriv gamma t * Complex.exp ((-L) t) +
          q t * (Complex.exp ((-L) t) * -r t) = 0 := by
      rw [hrel]
      ring
    simpa only [F, Pi.neg_apply] using
      hprod.congr_deriv hzero
  have hFconst : ∀ t : ℝ, F t = F 0 := by
    intro t
    exact is_const_of_deriv_eq_zero
      (fun x => (hFDeriv x).differentiableAt)
      (fun x => (hFDeriv x).deriv) t 0
  have hLzero : L 0 = 0 := by
    simp only [L, intervalIntegral.integral_same]
  have hqexp : ∀ t : ℝ, q t = q 0 * Complex.exp (L t) := by
    intro t
    calc
      q t = (q t * Complex.exp (-L t)) * Complex.exp (L t) := by
        rw [mul_assoc, ← Complex.exp_add]
        simp only [neg_add_cancel, Complex.exp_zero, mul_one]
      _ = F t * Complex.exp (L t) := rfl
      _ = F 0 * Complex.exp (L t) := by rw [hFconst t]
      _ = (q 0 * Complex.exp (-L 0)) * Complex.exp (L t) := rfl
      _ = q 0 * Complex.exp (L t) := by
        rw [hLzero]
        simp only [neg_zero, Complex.exp_zero, mul_one]
  have hqperiod : q T = q 0 := by
    simpa only [q, gamma, T, zero_add] using
      congrArg (fun z : ℂ => z - c) (Omega.boundaryParam_periodic 0)
  have hexpPeriod : Complex.exp (L T) = 1 := by
    have hmuleq : q 0 * Complex.exp (L T) = q 0 * 1 := by
      rw [← hqexp T, hqperiod, mul_one]
    exact mul_left_cancel₀ (hqne 0) hmuleq
  have hthetaZero : theta 0 = 0 := by
    simp only [theta, hLzero, zero_im]
  have hthetaPeriodPos : 0 < theta T := by
    rw [← hthetaZero]
    exact hthetaStrict hT
  have himPeriodNonneg : 0 ≤ (L T).im := hthetaPeriodPos.le
  obtain ⟨n, hn⟩ :=
    (Complex.exp_eq_one_iff_of_im_nonneg himPeriodNonneg).mp hexpPeriod
  have hthetaPeriod : theta T = (n : ℝ) * (2 * Real.pi) := by
    have him := congrArg Complex.im hn
    dsimp only [theta]
    norm_num [Complex.mul_im] at him ⊢
    exact him
  have hnne : n ≠ 0 := by
    intro hnzero
    subst n
    norm_num at hthetaPeriod
    linarith
  have hnpos : 0 < n := Nat.pos_of_ne_zero hnne
  have hthetaCont : Continuous theta :=
    continuous_iff_continuousAt.mpr fun t => (hthetaDeriv t).continuousAt
  have hnle : n ≤ 1 := by
    by_contra hnnot
    have htwo : 2 ≤ n := by omega
    have htwoReal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast htwo
    have htargetLt : 2 * Real.pi < theta T := by
      rw [hthetaPeriod]
      nlinarith only [htwoReal, Real.pi_pos]
    have htargetMem :
        2 * Real.pi ∈ Icc (theta 0) (theta T) := by
      rw [hthetaZero]
      exact ⟨Real.two_pi_pos.le, htargetLt.le⟩
    obtain ⟨t, _, htvalue⟩ :=
      intermediate_value_Icc hT.le hthetaCont.continuousOn htargetMem
    have htpos : 0 < t := by
      apply hthetaStrict.lt_iff_lt.mp
      rw [hthetaZero, htvalue]
      exact Real.two_pi_pos
    have htT : t < T := by
      apply hthetaStrict.lt_iff_lt.mp
      rw [htvalue]
      exact htargetLt
    have hLim : (L t).im = 2 * Real.pi := by
      simpa only [theta] using htvalue
    have hLdecomp :
        L t = ((L t).re : ℂ) + (2 * (Real.pi : ℂ)) * I := by
      calc
        L t = ((L t).re : ℂ) + ((L t).im : ℂ) * I :=
          (Complex.re_add_im (L t)).symm
        _ = ((L t).re : ℂ) + (2 * (Real.pi : ℂ)) * I := by
          rw [hLim]
          norm_num
    have hexpt :
        Complex.exp (L t) = (Real.exp (L t).re : ℂ) := by
      calc
        Complex.exp (L t) =
            Complex.exp
              (((L t).re : ℂ) + 2 * (Real.pi : ℂ) * I) :=
          congrArg Complex.exp hLdecomp
        _ = Complex.exp ((L t).re : ℂ) *
              Complex.exp (2 * (Real.pi : ℂ) * I) :=
          Complex.exp_add _ _
        _ = Complex.exp ((L t).re : ℂ) := by
          rw [Complex.exp_two_pi_mul_I, mul_one]
        _ = (Real.exp (L t).re : ℂ) :=
          (Complex.ofReal_exp (L t).re).symm
    let a : ℝ := Real.exp (L t).re
    have ha : 0 < a := Real.exp_pos _
    have hchord : gamma t - c = (a : ℂ) * (gamma 0 - c) := by
      have hqt := hqexp t
      rw [hexpt] at hqt
      simpa only [q, a, mul_comm] using hqt
    have hfront0 : gamma 0 ∈ frontier Omega.carrier := by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self 0
    have hfrontt : gamma t ∈ frontier Omega.carrier := by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self t
    have hboundaryEq : gamma 0 = gamma t :=
      frontier_same_positive_ray_eq Omega c hc hfront0 hfrontt ha hchord
    have hzeroMem : (0 : ℝ) ∈ Ico (0 : ℝ) T :=
      ⟨le_rfl, hT⟩
    have htMem : t ∈ Ico (0 : ℝ) T := ⟨htpos.le, htT⟩
    have hzeroEqT : (0 : ℝ) = t := by
      apply Omega.boundaryParam_injOn
      · simpa only [T] using hzeroMem
      · simpa only [T] using htMem
      · simpa only [gamma] using hboundaryEq
    exact (ne_of_lt htpos) hzeroEqT
  have hnOne : n = 1 := by omega
  have hLPeriod : L T = 2 * (Real.pi : ℂ) * I := by
    rw [hnOne] at hn
    simpa only [Nat.cast_one, one_mul] using hn
  have hcontour :
      contourIntegral (fun sigma : ℂ => (sigma - c)⁻¹)
        Omega.boundaryParam = L T := by
    simp only [contourIntegral, L, r, q, gamma, T, smul_eq_mul,
      div_eq_mul_inv]
  unfold crouzeixScalarCauchyKernel
  rw [hcontour, hLPeriod]
  field_simp [Real.pi_ne_zero, I_ne_zero]

/-- Consistent orientation at one carrier point forces winding normalization
at every point of the strictly convex carrier. -/
theorem crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1 := by
  exact crouzeixScalarCauchyKernel_eq_one_of_basepoint Omega c hc
    (crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier_point
      Omega c hc hcside)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
