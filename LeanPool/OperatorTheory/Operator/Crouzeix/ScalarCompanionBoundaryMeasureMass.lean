/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Automatic mass of the boundary double-layer density

For an oriented smooth convex Jordan boundary, the double-layer density

`rho_xi(t) = Im (gamma'(t) / (gamma(t) - xi)) / pi`

has mass one at every frontier point.  The proof chooses a parameter `s` for
`xi`, divides the boundary chord by `gamma'(s)`, and rotates it by `-I`.
Convex support puts this normalized chord in `Complex.slitPlane`.  Its
principal argument therefore lifts continuously from `0` to `pi` during one
period, and its derivative is exactly `pi * rho_xi`.  Positivity makes the
lift monotone, which supplies derivative integrability; the improper
fundamental theorem then gives the mass identity.

## Main declarations

* `crouzeixBoundaryDoubleLayerDensity_periodic` -- the density is periodic;
* `canonicalNormal_support_all_of_Ioc` -- oriented support on one fundamental
  interval propagates to every parameter;
* `integral_crouzeixBoundaryDoubleLayerDensity_eq_one_of_oriented_carrier_point`
  -- one consistently oriented carrier point forces unit mass at every
  frontier basepoint;
* `crouzeixBoundaryPhaseContractive_of_oriented_carrier_point` -- the same
  geometry gives sharp boundary-phase contractivity for every polynomial.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionBoundaryMeasure
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanSupport
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open Complex Filter MeasureTheory Set
open scoped Interval Real

private theorem periodic_deriv_boundaryParam (Omega : SmoothJordanDomain) :
    Function.Periodic (deriv Omega.boundaryParam) (2 * Real.pi) := by
  intro t
  have hfun : (fun x : ℝ => Omega.boundaryParam (x + 2 * Real.pi)) =
      Omega.boundaryParam := by
    funext x
    exact Omega.boundaryParam_periodic x
  have h := congrArg (fun f : ℝ → ℂ => deriv f t) hfun
  rwa [deriv_comp_add_const] at h

/-- The explicit boundary double-layer density has the same period as the
boundary trace. -/
theorem crouzeixBoundaryDoubleLayerDensity_periodic
    (Omega : SmoothJordanDomain) (xi : ℂ) :
    Function.Periodic
      (crouzeixBoundaryDoubleLayerDensity Omega xi) (2 * Real.pi) := by
  intro t
  unfold crouzeixBoundaryDoubleLayerDensity
  rw [periodic_deriv_boundaryParam Omega t,
    Omega.boundaryParam_periodic t]

/-- An oriented support inequality verified on the standard half-open
fundamental interval holds at every real parameter. -/
theorem canonicalNormal_support_all_of_Ioc
    (Omega : SmoothJordanDomain) (c : ℂ)
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0 := by
  let f : ℝ → ℝ := fun t =>
    ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
      (c - Omega.boundaryParam t)).re
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro t
    dsimp only [f]
    rw [periodic_deriv_boundaryParam Omega t,
      Omega.boundaryParam_periodic t]
  intro t
  obtain ⟨u, hu, htu⟩ :=
    hf.exists_mem_Ioc Real.two_pi_pos t 0
  change f t ≤ 0
  rw [htu]
  exact hsupport u (by simpa only [zero_add] using hu)

private theorem boundaryParam_ne_of_mem_Ioo_period
    (Omega : SmoothJordanDomain) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Ioo s (s + 2 * Real.pi)) :
    Omega.boundaryParam t ≠ Omega.boundaryParam s := by
  intro heq
  by_cases htT : t < 2 * Real.pi
  · exact ht.1.ne (Omega.boundaryParam_injOn
      ⟨hs.1, hs.2⟩ ⟨le_trans hs.1 ht.1.le, htT⟩ heq.symm)
  · have htTle : 2 * Real.pi ≤ t := le_of_not_gt htT
    let u := t - 2 * Real.pi
    have hu0 : 0 ≤ u := sub_nonneg.mpr htTle
    have hus : u < s := by
      dsimp only [u]
      linarith [ht.2]
    have huT : u < 2 * Real.pi := hus.trans_le hs.2.le
    have hperiod : Omega.boundaryParam u = Omega.boundaryParam t := by
      have hp := Omega.boundaryParam_periodic u
      rw [show u + 2 * Real.pi = t by dsimp only [u]; ring] at hp
      exact hp.symm
    exact hus.ne (Omega.boundaryParam_injOn
      ⟨hu0, huT⟩ hs (hperiod.trans heq))

/-- If one point of the open carrier lies consistently on the inward side of
the canonical oriented tangent line, then the boundary double-layer density
based at every frontier point has interval-integral mass one. -/
theorem
    integral_crouzeixBoundaryDoubleLayerDensity_eq_one_of_oriented_carrier_point
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    (xi : ℂ) (hxi : xi ∈ frontier Omega.carrier) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1 := by
  classical
  let gamma := Omega.boundaryParam
  let T := 2 * Real.pi
  rw [← Omega.boundaryParam_range] at hxi
  obtain ⟨r, rfl⟩ := hxi
  obtain ⟨s, hs, hrs⟩ :=
    Omega.boundaryParam_periodic.exists_mem_Ico₀ Real.two_pi_pos r
  have hrep : gamma s = gamma r := hrs.symm
  let D0 := deriv gamma s
  let b := s + T
  let q : ℝ → ℂ := fun t => (gamma t - gamma r) / D0
  let w : ℝ → ℂ := fun t => -I * q t
  have hT : 0 < T := Real.two_pi_pos
  have hsb : s < b := by dsimp only [b]; linarith
  have hD0 : D0 ≠ 0 := Omega.boundaryParam_regular s
  have hgammaB : gamma b = gamma r := by
    simpa only [gamma, b, T] using
      (Omega.boundaryParam_periodic s).trans hrep
  have hboundary : ∀ t z, z ∈ frontier Omega.carrier →
      ((starRingEnd ℂ) (-I * deriv gamma t) *
        (z - gamma t)).re ≤ 0 := by
    intro t z hz
    exact
      (Omega.closure_support_and_carrier_strict_of_support_at_mem_carrier
        c hc t (hcside t)).1 z (frontier_subset_closure hz)
  have hqne : ∀ t ∈ Ioo s b, q t ≠ 0 := by
    intro t ht hzero
    have hchord : gamma t = gamma s := by
      apply sub_eq_zero.mp
      have : gamma t - gamma r = 0 := by
        apply (div_eq_zero_iff.mp hzero).resolve_right hD0
      simpa only [hrep] using this
    exact boundaryParam_ne_of_mem_Ioo_period Omega hs ht hchord
  have hqim : ∀ t ∈ Ioo s b, 0 ≤ (q t).im := by
    intro t ht
    have hfrontierT : gamma t ∈ frontier Omega.carrier := by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self t
    have hnormal := hboundary s (gamma t) hfrontierT
    have hnormSq : 0 < Complex.normSq D0 :=
      Complex.normSq_pos.mpr hD0
    dsimp only [q]
    rw [Complex.div_im]
    have hnormal' :
        D0.im * (gamma t - gamma r).re -
          D0.re * (gamma t - gamma r).im ≤ 0 := by
      rw [← hrep]
      simpa [D0, map_mul, map_neg, Complex.conj_I,
        Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
        using hnormal
    have hnum :
        0 ≤ (gamma t - gamma r).im * D0.re -
          (gamma t - gamma r).re * D0.im := by
      linarith [hnormal']
    rw [← sub_div]
    exact div_nonneg hnum hnormSq.le
  have hwslit : ∀ t ∈ Ioo s b, w t ∈ Complex.slitPlane := by
    intro t ht
    have hq0 := hqne t ht
    have hqim0 := hqim t ht
    have hw0 : w t ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hq0
    rw [Complex.mem_slitPlane_iff]
    by_cases hpos : 0 < (w t).re
    · exact Or.inl hpos
    · right
      have hwre_nonneg : 0 ≤ (w t).re := by
        have hwre_eq : (w t).re = (q t).im := by
          simp only [neg_mul, neg_re, mul_re, I_re, zero_mul, I_im, one_mul,
            zero_sub, neg_neg, w]
        rwa [hwre_eq]
      have hwre : (w t).re = 0 :=
        le_antisymm (le_of_not_gt hpos) hwre_nonneg
      intro hwim
      apply hw0
      exact Complex.ext hwre hwim
  let rawTheta : ℝ → ℝ := fun t => Complex.arg (w t) + Real.pi / 2
  let theta : ℝ → ℝ :=
    Function.update (Function.update rawTheta s 0) b Real.pi
  have htheta_eq : ∀ t ∈ Ioo s b, theta t = rawTheta t := by
    intro t ht
    simp only [ne_eq, ht.2.ne, not_false_eq_true, Function.update_of_ne,
      ht.1.ne', theta]
  have hthetaS : theta s = 0 := by
    simp only [ne_eq, hsb.ne, not_false_eq_true, Function.update_of_ne,
      Function.update_self, theta]
  have hthetaB : theta b = Real.pi := by
    simp only [theta, Function.update_self]
  have hthetaDeriv : ∀ t ∈ Ioo s b,
      HasDerivAt theta
        (Real.pi * crouzeixBoundaryDoubleLayerDensity Omega (gamma r) t) t := by
    intro t ht
    have hgammaDeriv : HasDerivAt gamma (deriv gamma t) t :=
      (Omega.boundaryParam_contDiff.differentiable (by norm_num) t).hasDerivAt
    have hqDeriv : HasDerivAt q (deriv gamma t / D0) t := by
      simpa only [q] using (hgammaDeriv.sub_const (gamma r)).div_const D0
    have hwDeriv : HasDerivAt w (-I * (deriv gamma t / D0)) t := by
      simpa only [w] using hqDeriv.const_mul (-I)
    have hlogDeriv := hwDeriv.clog_real (hwslit t ht)
    have himLogDeriv :
        HasDerivAt (fun x => (Complex.log (w x)).im)
          ((-I * (deriv gamma t / D0)) / w t).im t := by
      convert!
        Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlogDeriv using 1
    have hrawDeriv :
        HasDerivAt rawTheta
          ((-I * (deriv gamma t / D0)) / w t).im t := by
      simpa only [rawTheta, Complex.log_im] using
        himLogDeriv.add_const (Real.pi / 2)
    have hchord : gamma t - gamma r ≠ 0 := by
      intro hzero
      apply hqne t ht
      simp only [q, hzero, zero_div]
    have hratio :
        (-I * (deriv gamma t / D0)) / w t =
          deriv gamma t / (gamma t - gamma r) := by
      dsimp only [w, q]
      field_simp [hD0, hchord, I_ne_zero]
    have hrho :
        (deriv gamma t / (gamma t - gamma r)).im =
          Real.pi *
            crouzeixBoundaryDoubleLayerDensity Omega (gamma r) t := by
      unfold crouzeixBoundaryDoubleLayerDensity
      simp only [gamma, div_eq_mul_inv]
      field_simp [Real.pi_ne_zero]
    have hev : theta =ᶠ[nhds t] rawTheta := by
      filter_upwards [eventually_ne_nhds ht.1.ne',
        eventually_ne_nhds ht.2.ne] with x hxs hxb
      simp only [ne_eq, hxb, not_false_eq_true, Function.update_of_ne, hxs,
        theta]
    exact (hrawDeriv.congr_of_eventuallyEq hev).congr_deriv (by
      rw [hratio, hrho])
  have hthetaBounds : ∀ t ∈ Ioo s b, theta t ∈ Icc (0 : ℝ) Real.pi := by
    intro t ht
    have hwre : 0 ≤ (w t).re := by
      have hwre_eq : (w t).re = (q t).im := by
        simp only [neg_mul, neg_re, mul_re, I_re, zero_mul, I_im, one_mul,
          zero_sub, neg_neg, w]
      rw [hwre_eq]
      exact hqim t ht
    have harg := Complex.abs_arg_le_pi_div_two_iff.mpr hwre
    rw [abs_le] at harg
    rw [htheta_eq t ht]
    dsimp only [rawTheta]
    constructor <;> linarith
  have hrhoNonneg : ∀ t ∈ Ioo s b,
      0 ≤ crouzeixBoundaryDoubleLayerDensity Omega (gamma r) t := by
    intro t _
    apply crouzeixBoundaryDoubleLayerDensity_nonneg_of_support
    apply hboundary
    rw [← Omega.boundaryParam_range]
    exact mem_range_self r
  have hthetaMonoInterior : MonotoneOn theta (Ioo s b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo s b)
    · intro t ht
      exact (hthetaDeriv t ht).continuousAt.continuousWithinAt
    · intro t ht
      apply (hthetaDeriv t ?_).hasDerivWithinAt
      simpa only [interior_Ioo] using ht
    · intro t ht
      have ht' : t ∈ Ioo s b := by
        simpa only [interior_Ioo] using ht
      exact mul_nonneg Real.pi_pos.le (hrhoNonneg t ht')
  have hthetaMono : MonotoneOn theta (Icc s b) := by
    intro x hx y hy hxy
    by_cases hxs : x = s
    · subst x
      by_cases hys : y = s
      · subst y
        exact le_rfl
      · rw [hthetaS]
        by_cases hyb : y = b
        · subst y
          rw [hthetaB]
          exact Real.pi_pos.le
        · have hyoo : y ∈ Ioo s b := by
            exact ⟨lt_of_le_of_ne hy.1 (Ne.symm hys),
              lt_of_le_of_ne hy.2 hyb⟩
          exact (hthetaBounds y hyoo).1
    · by_cases hyb : y = b
      · subst y
        by_cases hxb : x = b
        · subst x
          exact le_rfl
        · rw [hthetaB]
          have hxoo : x ∈ Ioo s b := by
            exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxs),
              lt_of_le_of_ne hx.2 hxb⟩
          exact (hthetaBounds x hxoo).2
      · have hxoo : x ∈ Ioo s b := by
          refine ⟨lt_of_le_of_ne hx.1 (Ne.symm hxs), ?_⟩
          exact lt_of_le_of_lt hxy (lt_of_le_of_ne hy.2 hyb)
        have hyoo : y ∈ Ioo s b := by
          refine ⟨lt_of_lt_of_le hxoo.1 hxy, ?_⟩
          exact lt_of_le_of_ne hy.2 hyb
        exact hthetaMonoInterior hxoo hyoo hxy
  have hthetaMonoU : MonotoneOn theta [[s, b]] := by
    simpa [uIcc_of_le hsb.le] using hthetaMono
  have hintDeriv : IntervalIntegrable (deriv theta) volume s b :=
    hthetaMonoU.intervalIntegrable_deriv
  have hderivEq : EqOn (deriv theta)
      (fun t => Real.pi *
        crouzeixBoundaryDoubleLayerDensity Omega (gamma r) t) (uIoo s b) := by
    intro t ht
    have ht' : t ∈ Ioo s b := by
      simpa [uIoo_of_le hsb.le] using ht
    exact (hthetaDeriv t ht').deriv
  have hintScaled : IntervalIntegrable
      (fun t => Real.pi *
        crouzeixBoundaryDoubleLayerDensity Omega (gamma r) t)
      volume s b :=
    hintDeriv.congr_uIoo hderivEq
  let vS : ℝ → ℂ := fun t => -I * (dslope gamma s t / D0)
  have hvSVal : vS s = -I := by
    simp only [neg_mul, dslope_same, ne_eq, hD0, not_false_eq_true, div_self,
      mul_one, vS, D0]
  have hvSContinuous : ContinuousAt vS s := by
    dsimp only [vS]
    exact continuousAt_const.mul
      ((continuousAt_dslope_same.mpr
        (Omega.boundaryParam_contDiff.differentiable
          (by norm_num) s)).div_const D0)
  have hwFactorS : ∀ t : ℝ, w t = (t - s) * vS t := by
    intro t
    dsimp only [w, q, vS]
    rw [← hrep, ← sub_smul_dslope gamma s t]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hthetaStartEq : ∀ t, s < t → t < b →
      theta t = Complex.arg (vS t) + Real.pi / 2 := by
    intro t hst htb
    rw [htheta_eq t ⟨hst, htb⟩]
    dsimp only [rawTheta]
    rw [hwFactorS t, ← Complex.ofReal_sub,
      Complex.arg_real_mul (vS t) (sub_pos.mpr hst)]
  have hvSTend : Tendsto vS (nhds s) (nhds (-I)) := by
    rw [← hvSVal]
    exact hvSContinuous
  have hminusISlit : (-I : ℂ) ∈ Complex.slitPlane := by
    simp only [Complex.mem_slitPlane_iff, neg_re, I_re, neg_zero,
      lt_self_iff_false, neg_im, I_im, ne_eq, neg_eq_zero, one_ne_zero,
      not_false_eq_true, or_true]
  have hargSTend : Tendsto (fun t => Complex.arg (vS t))
      (nhds s) (nhds (Complex.arg (-I))) :=
    Filter.Tendsto.comp (Complex.continuousAt_arg hminusISlit) hvSTend
  have hangleSTend : Tendsto
      (fun t => Complex.arg (vS t) + Real.pi / 2)
      (nhds s) (nhds 0) := by
    convert hargSTend.add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.pi / 2)
        (nhds s) (nhds (Real.pi / 2))) using 1
    rw [Complex.arg_neg_I]
    ring_nf
  have hthetaStart : Tendsto theta (nhdsWithin s (Ioi s)) (nhds 0) := by
    apply Tendsto.congr' ?_
      (hangleSTend.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hsb)] with t hst htb
    exact (hthetaStartEq t hst htb).symm
  have hDB : deriv gamma b = D0 := by
    dsimp only [gamma, b, T, D0]
    exact periodic_deriv_boundaryParam Omega s
  let vB : ℝ → ℂ := fun t => I * (dslope gamma b t / D0)
  have hvBVal : vB b = I := by
    simp only [dslope_same, hDB, ne_eq, hD0, not_false_eq_true, div_self,
      mul_one, vB]
  have hvBContinuous : ContinuousAt vB b := by
    dsimp only [vB]
    exact continuousAt_const.mul
      ((continuousAt_dslope_same.mpr
        (Omega.boundaryParam_contDiff.differentiable
          (by norm_num) b)).div_const D0)
  have hwFactorB : ∀ t : ℝ, w t = (b - t) * vB t := by
    intro t
    dsimp only [w, q, vB]
    rw [← hgammaB, ← sub_smul_dslope gamma b t]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hthetaEndEq : ∀ t, s < t → t < b →
      theta t = Complex.arg (vB t) + Real.pi / 2 := by
    intro t hst htb
    rw [htheta_eq t ⟨hst, htb⟩]
    dsimp only [rawTheta]
    rw [hwFactorB t, ← Complex.ofReal_sub,
      Complex.arg_real_mul (vB t) (sub_pos.mpr htb)]
  have hvBTend : Tendsto vB (nhds b) (nhds I) := by
    rw [← hvBVal]
    exact hvBContinuous
  have hISlit : (I : ℂ) ∈ Complex.slitPlane := by
    simp only [Complex.mem_slitPlane_iff, I_re, lt_self_iff_false, I_im,
      ne_eq, one_ne_zero, not_false_eq_true, or_true]
  have hargBTend : Tendsto (fun t => Complex.arg (vB t))
      (nhds b) (nhds (Complex.arg I)) :=
    Filter.Tendsto.comp (Complex.continuousAt_arg hISlit) hvBTend
  have hangleBTend : Tendsto
      (fun t => Complex.arg (vB t) + Real.pi / 2)
      (nhds b) (nhds Real.pi) := by
    convert hargBTend.add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.pi / 2)
        (nhds b) (nhds (Real.pi / 2))) using 1
    rw [Complex.arg_I]
    ring_nf
  have hthetaEnd : Tendsto theta (nhdsWithin b (Iio b))
      (nhds Real.pi) := by
    apply Tendsto.congr' ?_
      (hangleBTend.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hsb)] with t htb hst
    exact (hthetaEndEq t hst htb).symm
  have hscaledIntegral :
      (∫ t in s..b, Real.pi *
        crouzeixBoundaryDoubleLayerDensity Omega (gamma r) t) =
        Real.pi := by
    simpa only [sub_zero] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
        hsb hthetaDeriv hintScaled hthetaStart hthetaEnd)
  have hunitSB :
      (∫ t in s..b,
        crouzeixBoundaryDoubleLayerDensity Omega (gamma r) t) = 1 := by
    rw [intervalIntegral.integral_const_mul] at hscaledIntegral
    apply mul_left_cancel₀ Real.pi_ne_zero
    simpa only [mul_one] using hscaledIntegral
  calc
    (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega (gamma r) t) =
        ∫ t in s..b,
          crouzeixBoundaryDoubleLayerDensity Omega (gamma r) t := by
      simpa only [b, T, zero_add] using
        ((crouzeixBoundaryDoubleLayerDensity_periodic Omega (gamma r)).intervalIntegral_add_eq
          s 0).symm
    _ = 1 := hunitSB

/-- A consistently oriented point of the carrier makes every polynomial
boundary phase contractive. -/
theorem crouzeixBoundaryPhaseContractive_of_oriented_carrier_point
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    (p : Polynomial ℂ) :
    CrouzeixBoundaryPhaseContractive Omega p := by
  apply
    crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_mass_support
      Omega p
  · intro xi hxi
    exact
      integral_crouzeixBoundaryDoubleLayerDensity_eq_one_of_oriented_carrier_point
        Omega c hc hcside xi hxi
  · intro xi hxi t _
    exact
      (Omega.closure_support_and_carrier_strict_of_support_at_mem_carrier
        c hc t (hcside t)).1 xi (frontier_subset_closure hxi)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
