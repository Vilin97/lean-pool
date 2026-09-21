/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Polynomial approximation from smooth-Jordan Cauchy formulas

This file converts a normalized scalar Cauchy formula on a compact smooth
convex Jordan carrier into uniform polynomial approximation on its closure.
Strict radial contraction moves the evaluation point into the carrier and
turns each boundary kernel into one whose pole lies strictly outside the
closed carrier.  `ConvexRungeIntegral` approximates each radialized function,
and a diagonal selection removes the radial contraction.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ConvexRungeIntegral
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanCauchyFormula
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanExhaustion
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

open Complex Filter Metric Set
open scoped Interval Real Topology

/-- The strict radial contraction of `z` toward `c`. -/
noncomputable def smoothJordanRadialPoint (c z : ℂ) (r : ℝ) : ℂ :=
  (1 - r) • c + r • z

/-- The point beyond `xi` on the ray from `c`, reciprocal to the radial
contraction factor. -/
noncomputable def smoothJordanOutwardPoint (c xi : ℂ) (r : ℝ) : ℂ :=
  c + r⁻¹ • (xi - c)

private noncomputable def smoothMergelyanRadialFactor (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) / ((n : ℝ) + 2)

private theorem smoothMergelyanRadialFactor_pos (n : ℕ) :
    0 < smoothMergelyanRadialFactor n := by
  unfold smoothMergelyanRadialFactor
  positivity

private theorem smoothMergelyanRadialFactor_lt_one (n : ℕ) :
    smoothMergelyanRadialFactor n < 1 := by
  unfold smoothMergelyanRadialFactor
  rw [div_lt_one]
  · linarith
  · positivity

private theorem one_sub_smoothMergelyanRadialFactor (n : ℕ) :
    1 - smoothMergelyanRadialFactor n = 1 / ((n : ℝ) + 2) := by
  unfold smoothMergelyanRadialFactor
  have hn : (n : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hn]
  ring

/-- A boundary point pushed outward by the reciprocal of a strict radial
contraction lies outside the closed convex carrier. -/
theorem SmoothJordanDomain.smoothJordanOutwardPoint_not_mem_closure
    (Omega : SmoothJordanDomain) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    smoothJordanOutwardPoint c xi r ∉ closure Omega.carrier := by
  intro hout
  have hcint : c ∈ interior Omega.carrier := by
    rwa [Omega.isOpen_carrier.interior_eq]
  have hcombo :
      (1 - r) • c + r • smoothJordanOutwardPoint c xi r = xi := by
    unfold smoothJordanOutwardPoint
    rw [smul_add, smul_smul, mul_inv_cancel₀ hr.1.ne', one_smul]
    module
  have hxiint : xi ∈ interior Omega.carrier := by
    rw [← hcombo]
    exact
      Omega.strictConvex_carrier.convex.combo_interior_closure_mem_interior
        hcint hout (sub_pos.mpr hr.2) hr.1.le (by ring)
  have hxicarrier : xi ∈ Omega.carrier := by
    rwa [Omega.isOpen_carrier.interior_eq] at hxiint
  have hempty : xi ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hxicarrier, hxi⟩
  exact hempty

/-- Strict radial contractions of points in the closed carrier lie in its
open interior. -/
theorem SmoothJordanDomain.smoothJordanRadialPoint_mem_carrier
    (Omega : SmoothJordanDomain) {c z : ℂ}
    (hc : c ∈ Omega.carrier) (hz : z ∈ closure Omega.carrier)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    smoothJordanRadialPoint c z r ∈ Omega.carrier := by
  have hcint : c ∈ interior Omega.carrier := by
    rwa [Omega.isOpen_carrier.interior_eq]
  have hmem : smoothJordanRadialPoint c z r ∈ interior Omega.carrier := by
    unfold smoothJordanRadialPoint
    exact
      Omega.strictConvex_carrier.convex.combo_interior_closure_mem_interior
        hcint hz (sub_pos.mpr hr.2) hr.1.le (by ring)
  exact interior_subset hmem

private theorem tendstoUniformlyOn_smoothJordanRadialPoint
    (K : Set ℂ) (hK : IsCompact K) (c : ℂ) :
    TendstoUniformlyOn
      (fun n z ↦ smoothJordanRadialPoint c z
        (smoothMergelyanRadialFactor n))
      id atTop K := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall c
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hbase : Tendsto
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
  have hzero : Tendsto
      (fun n : ℕ => (1 / ((n : ℝ) + 2)) * R) atTop (𝓝 0) := by
    have heq :
        (fun n : ℕ => (1 / ((n : ℝ) + 2)) * R) =
          fun n : ℕ => (1 / (((n + 1 : ℕ) : ℝ) + 1)) * R := by
      funext n
      congr 2
      norm_num
      ring
    rw [heq]
    simpa only [zero_mul] using hbase.mul_const R
  have hevent := hzero.eventually (gt_mem_nhds hε)
  filter_upwards [hevent] with n hn z hz
  have hzR : ‖z - c‖ ≤ R := by
    have := hR hz
    simpa only [Metric.mem_closedBall, dist_eq_norm] using this
  have hsub : z - smoothJordanRadialPoint c z
      (smoothMergelyanRadialFactor n) =
        (1 - smoothMergelyanRadialFactor n) • (z - c) := by
    unfold smoothJordanRadialPoint
    module
  rw [id_eq, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by
      rw [one_sub_smoothMergelyanRadialFactor]
      positivity), one_sub_smoothMergelyanRadialFactor]
  exact (mul_le_mul_of_nonneg_left hzR (by positivity)).trans_lt hn

private theorem inv_sub_smoothJordanRadialPoint
    (c xi z : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (xi - smoothJordanRadialPoint c z r)⁻¹ =
      ((r : ℂ))⁻¹ * (smoothJordanOutwardPoint c xi r - z)⁻¹ := by
  have hfactor : xi - smoothJordanRadialPoint c z r =
      (r : ℂ) * (smoothJordanOutwardPoint c xi r - z) := by
    unfold smoothJordanRadialPoint smoothJordanOutwardPoint
    simp only [Complex.real_smul, Complex.ofReal_inv]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr]
    ring
  rw [hfactor, mul_inv_rev]
  ring

private theorem exists_polynomial_tendstoUniformlyOn_smoothJordanRadialPoint
    (Omega : SmoothJordanDomain) (f : ℂ → ℂ)
    (hf : DiffContOnCl ℂ f Omega.carrier)
    (hcompact : IsCompact (closure Omega.carrier))
    (hCauchy : ∀ z ∈ Omega.carrier,
      f z = ∫ t in (0 : ℝ)..(2 * Real.pi),
        (2 * (Real.pi : ℂ) * I)⁻¹ * deriv Omega.boundaryParam t *
          f (Omega.boundaryParam t) *
            (Omega.boundaryParam t - z)⁻¹)
    {c : ℂ} (hc : c ∈ Omega.carrier) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn
        (fun n z ↦ Polynomial.eval z (q n))
        (fun z ↦ f (smoothJordanRadialPoint c z r)) atTop
        (closure Omega.carrier) := by
  let coeff : ℝ → ℂ := fun t =>
    (2 * (Real.pi : ℂ) * I)⁻¹ * deriv Omega.boundaryParam t *
      f (Omega.boundaryParam t) * (r : ℂ)⁻¹
  let pole : ℝ → ℂ := fun t =>
    smoothJordanOutwardPoint c (Omega.boundaryParam t) r
  have hfBoundary : Continuous (fun t => f (Omega.boundaryParam t)) :=
    hf.continuousOn.comp_continuous
      Omega.boundaryParam_contDiff.continuous (fun t =>
        frontier_subset_closure (by
          rw [← Omega.boundaryParam_range]
          exact mem_range_self t))
  have hcoeff : Continuous coeff := by
    dsimp only [coeff]
    exact (((continuous_const.mul
      (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num))).mul
        hfBoundary).mul continuous_const)
  have hpole_cont : Continuous pole := by
    dsimp only [pole, smoothJordanOutwardPoint]
    have hscale : Continuous (fun _ : ℝ => (r⁻¹ : ℝ)) := continuous_const
    have hdiff : Continuous (fun t : ℝ => Omega.boundaryParam t - c) :=
      Omega.boundaryParam_contDiff.continuous.sub continuous_const
    exact continuous_const.add (hscale.smul hdiff)
  have hpole : ∀ t, pole t ∉ closure Omega.carrier := by
    intro t
    apply Omega.smoothJordanOutwardPoint_not_mem_closure hc
    · rw [← Omega.boundaryParam_range]
      exact mem_range_self t
    · exact hr
  obtain ⟨q, hq⟩ :=
    exists_polynomial_tendstoUniformlyOn_intervalIntegral_mul_inv_sub_of_isCompact_convex
      (closure Omega.carrier) hcompact
      Omega.strictConvex_carrier.convex.closure coeff pole hcoeff
      hpole_cont hpole Real.two_pi_pos
  refine ⟨q, hq.congr_right ?_⟩
  intro z hz
  change (∫ t in (0 : ℝ)..(2 * Real.pi),
    coeff t * (pole t - z)⁻¹) = f (smoothJordanRadialPoint c z r)
  rw [hCauchy (smoothJordanRadialPoint c z r)
    (Omega.smoothJordanRadialPoint_mem_carrier hc hz hr)]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only [coeff, pole]
  rw [inv_sub_smoothJordanRadialPoint c (Omega.boundaryParam t) z hr.1.ne']
  ring

private theorem exists_polynomial_tendstoUniformlyOn_of_iterated_polynomial_limits
    (K : Set ℂ) (f : ℂ → ℂ) (g : ℕ → ℂ → ℂ)
    (hg : TendstoUniformlyOn g f atTop K)
    (hpoly : ∀ n, ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun j z => Polynomial.eval z (q j))
        (g n) atTop K) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z => Polynomial.eval z (q n))
        f atTop K := by
  choose q hq using hpoly
  have hevent : ∀ n : ℕ, ∀ᶠ j in atTop,
      ∀ z ∈ K, dist (g n z) (Polynomial.eval z (q n j)) <
        1 / ((n : ℝ) + 1) := by
    intro n
    apply (Metric.tendstoUniformlyOn_iff.mp (hq n))
    positivity
  choose N hN using fun n => eventually_atTop.1 (hevent n)
  refine ⟨fun n => q n (N n), ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hg_event : ∀ᶠ n in atTop,
      ∀ z ∈ K, dist (f z) (g n z) < ε / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp hg) (ε / 2) (by positivity)
  have hrate : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hrate_event : ∀ᶠ (n : ℕ) in atTop,
      1 / ((n : ℝ) + 1) < ε / 2 :=
    hrate.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hg_event, hrate_event] with n hgn hn z hz
  calc
    dist (f z) (Polynomial.eval z (q n (N n))) ≤
        dist (f z) (g n z) +
          dist (g n z) (Polynomial.eval z (q n (N n))) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add (hgn z hz) ((hN n (N n) le_rfl z hz).trans hn)
    _ = ε := by ring

/-- A normalized interval Cauchy formula on a compact smooth convex Jordan
carrier implies the full polynomial approximation property. -/
theorem SmoothJordanDomain.hasMergelyanPolynomialApproximation_of_intervalCauchyFormula
    (Omega : SmoothJordanDomain)
    (hcompact : IsCompact (closure Omega.carrier))
    (hCauchy : ∀ (f : ℂ → ℂ), DiffContOnCl ℂ f Omega.carrier →
      ∀ z ∈ Omega.carrier,
        f z = ∫ t in (0 : ℝ)..(2 * Real.pi),
          (2 * (Real.pi : ℂ) * I)⁻¹ * deriv Omega.boundaryParam t *
            f (Omega.boundaryParam t) *
              (Omega.boundaryParam t - z)⁻¹) :
    Omega.HasMergelyanPolynomialApproximation := by
  intro f hf
  obtain ⟨c, hc⟩ := Omega.carrier_nonempty
  let g : ℕ → ℂ → ℂ := fun n z =>
    f (smoothJordanRadialPoint c z (smoothMergelyanRadialFactor n))
  have hradial : TendstoUniformlyOn g f atTop
      (closure Omega.carrier) := by
    have huc : UniformContinuousOn f (closure Omega.carrier) :=
      hcompact.uniformContinuousOn_of_continuous hf.continuousOn
    simpa only [g, id_eq] using
      huc.comp_tendstoUniformlyOn_eventually
        (Eventually.of_forall fun n z hz =>
          subset_closure (Omega.smoothJordanRadialPoint_mem_carrier hc hz
            ⟨smoothMergelyanRadialFactor_pos n,
              smoothMergelyanRadialFactor_lt_one n⟩))
        (fun _z hz => hz)
        (tendstoUniformlyOn_smoothJordanRadialPoint
          (closure Omega.carrier) hcompact c)
  apply
    exists_polynomial_tendstoUniformlyOn_of_iterated_polynomial_limits
      (closure Omega.carrier) f g hradial
  intro n
  exact exists_polynomial_tendstoUniformlyOn_smoothJordanRadialPoint
    Omega f hf hcompact (hCauchy f hf) hc
      ⟨smoothMergelyanRadialFactor_pos n,
        smoothMergelyanRadialFactor_lt_one n⟩

/-- The contour form of the normalized Cauchy formula implies the same
polynomial approximation property. -/
theorem SmoothJordanDomain.hasMergelyanPolynomialApproximation_of_cauchyFormula
    (Omega : SmoothJordanDomain)
    (hcompact : IsCompact (closure Omega.carrier))
    (hCauchy : ∀ (f : ℂ → ℂ), DiffContOnCl ℂ f Omega.carrier →
      ∀ z ∈ Omega.carrier,
        f z = (2 * (Real.pi : ℂ) * I)⁻¹ *
          contourIntegral (fun xi => f xi * (xi - z)⁻¹)
            Omega.boundaryParam) :
    Omega.HasMergelyanPolynomialApproximation := by
  apply Omega.hasMergelyanPolynomialApproximation_of_intervalCauchyFormula
    hcompact
  intro f hf z hz
  rw [hCauchy f hf z hz]
  unfold contourIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [smul_eq_mul]
  ring

/-- Every smooth strictly convex Jordan domain has the polynomial
approximation property on its closed carrier. -/
theorem SmoothJordanDomain.hasMergelyanPolynomialApproximation
    (Omega : SmoothJordanDomain) :
    Omega.HasMergelyanPolynomialApproximation := by
  let Psi := Omega.canonicalOrientation
  have hPsi : Psi.HasMergelyanPolynomialApproximation := by
    obtain ⟨c, hc, hc0⟩ := Omega.exists_oriented_point_canonicalOrientation
    have hcside : ∀ t : ℝ,
        ((starRingEnd ℂ) (-I * deriv Psi.boundaryParam t) *
          (c - Psi.boundaryParam t)).re ≤ 0 :=
      Psi.canonicalNormal_support_all_of_support_at c hc 0 hc0
    have hkernel : ∀ z ∈ Psi.carrier,
        crouzeixScalarCauchyKernel Psi z = 1 :=
      crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
        Psi c hc hcside
    have hcompact : IsCompact (closure Psi.carrier) :=
      Psi.isCompact_closure_of_cauchyKernel_eq_one hkernel
    apply Psi.hasMergelyanPolynomialApproximation_of_cauchyFormula hcompact
    intro f hf z hz
    have hfOmega : DiffContOnCl ℂ f Omega.carrier := by
      simpa only [Psi, SmoothJordanDomain.canonicalOrientation_carrier] using hf
    have hzOmega : z ∈ Omega.carrier := by
      simpa only [Psi, SmoothJordanDomain.canonicalOrientation_carrier] using hz
    change f z = (2 * (Real.pi : ℂ) * I)⁻¹ *
      contourIntegral (fun xi => f xi * (xi - z)⁻¹) Psi.boundaryParam
    exact cauchyFormula_canonicalOrientation Omega hfOmega hzOmega
  exact
    (SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
      Omega).mp hPsi

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
