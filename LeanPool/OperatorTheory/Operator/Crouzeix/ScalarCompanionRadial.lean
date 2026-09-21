/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionPlemeljBound
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology

/-!
# Inward-chord control for the scalar companion

Full Plemelj continuity at an arbitrary smooth frontier is delicate.  Along
an inward chord of a convex domain, however, an interior ball gives a uniform
geometric denominator estimate.  If

`z_r = (1-r) xi + r c`,

where `c` is interior and `xi` is on the frontier, then every frontier point
`sigma` satisfies `r * delta ≤ ‖sigma - z_r‖` for one fixed `delta > 0`.
The factor `r` exactly cancels the size of `z_r - xi`; this is the domination
needed to pass the cancelled scalar Cauchy contour to its radial boundary
value.

## Main declarations

* `continuous_eval_divByMonic_X_sub_C` -- joint continuity of the polynomial
  divided difference in its base and evaluation points;
* `exists_uniform_norm_eval_divByMonic_X_sub_C_frontier_le` -- one bound for
  all pairs of frontier points;
* `ae_boundaryParam_ne_of_mem_frontier` -- a frontier point is attained only
  on a null set of integration parameters;
* `smoothJordanInwardPoint` -- the inward real convex combination;
* `smoothJordanInwardPoint_mem_carrier` -- it lies in the carrier for
  `0 < r ≤ 1`;
* `exists_inward_coordinates` -- every point of a bounded carrier lies on
  such a chord from any fixed interior center;
* `exists_uniform_inward_boundary_denominator_bound` -- one interior-ball
  separation constant for every pair of frontier points;
* `exists_inward_boundary_denominator_bound` -- the uniform frontier
  separation supplied by an interior ball;
* `exists_uniform_inward_boundary_cross_bound` -- the cancellation-ready
  estimate with constants uniform in the chord endpoint;
* `exists_inward_boundary_cross_bound` -- the cancellation-ready multiplied
  form of that estimate.
* `exists_uniform_norm_inward_regularized_integrand_sub_le_deriv` -- one
  continuous majorant for all endpoints of chords from a fixed center.
* `exists_norm_inward_regularized_integrand_sub_le` -- an integrable-form
  domination bound for the difference from the regularized self-kernel.
* `tendsto_crouzeixPolynomialScalarCompanionRegularized_inward` -- dominated
  convergence of the regularized companion along every inward chord.
* `tendsto_crouzeixPolynomialScalarCompanion_inward` -- the corresponding
  full Plemelj limit when the scalar winding kernel is normalized.
* `tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_sub_self_joint`
  -- the Plemelj error tends uniformly locally to zero as its endpoint moves.
* `continuousOn_crouzeixPolynomialScalarCompanionRegularized_self` -- the
  moving regularized boundary value is continuous on the frontier.
* `tendsto_crouzeixPolynomialScalarCompanion_inward_joint` -- joint radial
  convergence of the full companion with moving endpoint.
* `tendsto_crouzeixPolynomialScalarCompanionRegularized_of_inward_coordinates`
  -- an inward-coordinate chart yields unrestricted regularized convergence.
* `exists_inward_coordinate_functions` -- global radial coordinates converge
  to `(0, xi)` near every frontier point.
* `SmoothJordanDomain.isBounded_carrier_of_cauchyKernel_eq_one` -- winding
  normalization and exterior decay force the carrier to be bounded.
* `tendsto_crouzeixPolynomialScalarCompanion_of_cauchyKernel_eq_one` --
  unrestricted full Plemelj convergence under winding normalization alone.
* `continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_cauchyKernel_eq_one`
  -- the resulting canonical closed extension is continuous.
* `norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform_radial`
  -- the sharp phase inequality controls that extension on the closure.
-/

open Complex Filter MeasureTheory Set
open scoped Interval Real

/-- If the scalar winding kernel is normalized to one throughout the carrier,
then exterior Cauchy-transform decay forces that carrier to be bounded. -/
theorem SmoothJordanDomain.isBounded_carrier_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    Bornology.IsBounded Omega.carrier := by
  have hdecay :=
    tendsto_crouzeixPolynomialScalarCompanion_cocompact
      Omega (Polynomial.C 1)
  have hsmall : ∀ᶠ z : ℂ in cocompact ℂ,
      dist (crouzeixPolynomialScalarCompanion
        Omega (Polynomial.C 1) z) 0 < 1 / 2 :=
    Metric.tendsto_nhds.mp hdecay (1 / 2) (by norm_num)
  rw [Filter.eventually_iff] at hsmall
  obtain ⟨K, hKcompact, hKsub⟩ := Filter.mem_cocompact.mp hsmall
  apply hKcompact.isBounded.subset
  intro z hz
  by_contra hzK
  have hzsmall := hKsub hzK
  have hcompanion :
      crouzeixPolynomialScalarCompanion Omega (Polynomial.C 1) z = 1 := by
    simpa only [crouzeixPolynomialScalarCompanion,
      crouzeixScalarCauchyKernel, Polynomial.eval_C, star_one, one_mul] using
      hkernel z hz
  change dist (crouzeixPolynomialScalarCompanion
    Omega (Polynomial.C 1) z) 0 < 1 / 2 at hzsmall
  rw [hcompanion, dist_zero_right, norm_one] at hzsmall
  norm_num at hzsmall

/-- The closure of a winding-normalized smooth Jordan carrier is compact. -/
theorem SmoothJordanDomain.isCompact_closure_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    IsCompact (closure Omega.carrier) :=
  (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel).isCompact_closure

/-- The value of the polynomial divided difference
`p /ₘ (X - C xi)` at `sigma` depends jointly continuously on `xi` and
`sigma`. -/
theorem continuous_eval_divByMonic_X_sub_C (p : Polynomial ℂ) :
    Continuous (fun x : ℂ × ℂ =>
      Polynomial.eval x.2 (p /ₘ (Polynomial.X - Polynomial.C x.1))) := by
  have hfun :
      (fun x : ℂ × ℂ =>
        Polynomial.eval x.2 (p /ₘ (Polynomial.X - Polynomial.C x.1))) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1),
        (∑ j ∈ Finset.Icc (i + 1) p.natDegree,
          x.1 ^ (j - (i + 1)) * p.coeff j) * x.2 ^ i := by
    funext x
    rw [Polynomial.eval_eq_sum_range' (n := p.natDegree + 1)]
    · apply Finset.sum_congr rfl
      intro i _hi
      rw [Polynomial.coeff_divByMonic_X_sub_C]
    · rw [Polynomial.natDegree_divByMonic p
        (Polynomial.monic_X_sub_C x.1), Polynomial.natDegree_X_sub_C]
      omega
  rw [hfun]
  fun_prop

/-- On the compact frontier, the values of all frontier-based divided
differences of one polynomial admit a single nonnegative bound. -/
theorem exists_uniform_norm_eval_divByMonic_X_sub_C_frontier_le
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ xi ∈ frontier Omega.carrier,
      ∀ sigma ∈ frontier Omega.carrier,
        ‖Polynomial.eval sigma
          (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤ Q := by
  let f : ℂ × ℂ → ℝ := fun x =>
    ‖Polynomial.eval x.2
      (p /ₘ (Polynomial.X - Polynomial.C x.1))‖
  have hf : Continuous f :=
    (continuous_eval_divByMonic_X_sub_C p).norm
  have hnonempty :
      (frontier Omega.carrier ×ˢ frontier Omega.carrier).Nonempty := by
    refine ⟨(Omega.boundaryParam 0, Omega.boundaryParam 0), ?_, ?_⟩ <;>
      rw [← Omega.boundaryParam_range] <;> exact mem_range_self 0
  obtain ⟨x, hx, hmax⟩ :=
    (Omega.isCompact_frontier.prod Omega.isCompact_frontier).exists_isMaxOn
      hnonempty hf.continuousOn
  refine ⟨f x, norm_nonneg _, ?_⟩
  intro xi hxi sigma hsigma
  have hpair : (xi, sigma) ∈
      frontier Omega.carrier ×ˢ frontier Omega.carrier := ⟨hxi, hsigma⟩
  exact hmax hpair

/-- On one fundamental integration interval, a Jordan boundary
parametrization takes any prescribed frontier value only on a null set. -/
theorem ae_boundaryParam_ne_of_mem_frontier
    (Omega : SmoothJordanDomain) {xi : ℂ}
    (hxi : xi ∈ frontier Omega.carrier) :
    ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Ι (0 : ℝ) (2 * Real.pi) → Omega.boundaryParam t ≠ xi := by
  rw [← Omega.boundaryParam_range] at hxi
  obtain ⟨s, rfl⟩ := hxi
  obtain ⟨t0, ht0, hrep⟩ :=
    Function.Periodic.exists_mem_Ico₀ Omega.boundaryParam_periodic
      Real.two_pi_pos s
  have ht0ae : ∀ᵐ t ∂MeasureTheory.volume, t ≠ t0 :=
    MeasureTheory.volume.ae_ne t0
  have hendae : ∀ᵐ t ∂MeasureTheory.volume,
      t ≠ 2 * Real.pi := MeasureTheory.volume.ae_ne (2 * Real.pi)
  filter_upwards [ht0ae, hendae] with t hne0 hneEnd
  intro ht heq
  have ht' := uIoc_subset_uIcc ht
  rw [uIcc_of_le Real.two_pi_pos.le] at ht'
  have htIco : t ∈ Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨ht'.1, lt_of_le_of_ne ht'.2 hneEnd⟩
  apply hne0
  exact Omega.boundaryParam_injOn htIco ht0 (heq.trans hrep)

/-- The point at proportion `r` along the inward chord from a frontier point
`xi` to an interior center `c`. -/
noncomputable def smoothJordanInwardPoint (c xi : ℂ) (r : ℝ) : ℂ :=
  (1 - r) • xi + r • c

/-- Every strict inward convex combination of a frontier point and an
interior point lies in the open convex carrier. -/
theorem smoothJordanInwardPoint_mem_carrier
    (Omega : SmoothJordanDomain) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier)
    {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    smoothJordanInwardPoint c xi r ∈ Omega.carrier := by
  have hcint : c ∈ interior Omega.carrier := by
    rwa [Omega.isOpen_carrier.interior_eq]
  have hcombo :=
    Omega.strictConvex_carrier.convex.combo_closure_interior_mem_interior
      (frontier_subset_closure hxi) hcint
      (sub_nonneg.mpr hr.2) hr.1 (by ring)
  exact interior_subset (by
    simpa only [smoothJordanInwardPoint] using hcombo)

/-- In a bounded smooth Jordan carrier, every interior point is an inward
chord point from any fixed interior center to some frontier endpoint. -/
theorem exists_inward_coordinates
    (Omega : SmoothJordanDomain)
    (hbounded : Bornology.IsBounded Omega.carrier)
    {c z : ℂ} (hc : c ∈ Omega.carrier) (hz : z ∈ Omega.carrier) :
    ∃ r ∈ Ioc (0 : ℝ) 1, ∃ eta ∈ frontier Omega.carrier,
      smoothJordanInwardPoint c eta r = z := by
  by_cases hzc : z = c
  · refine ⟨1, ⟨zero_lt_one, le_rfl⟩, Omega.boundaryParam 0, ?_, ?_⟩
    · rw [← Omega.boundaryParam_range]
      exact mem_range_self 0
    · rw [hzc]
      simp only [smoothJordanInwardPoint, sub_self, zero_smul, one_smul,
        zero_add]
  let f : ℝ → ℂ := fun t => c + t • (z - c)
  let S : Set ℝ := {t | f t ∈ Omega.carrier}
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hSopen : IsOpen S := Omega.isOpen_carrier.preimage hf
  have h0 : (0 : ℝ) ∈ S := by
    simpa only [S, mem_ofPred_eq, f, zero_smul, add_zero] using hc
  have h1 : (1 : ℝ) ∈ S := by
    simpa only [S, mem_ofPred_eq, f, one_smul, add_sub_cancel] using hz
  have hSne : S.Nonempty := ⟨0, h0⟩
  obtain ⟨R, _hRpos, hR⟩ := hbounded.subset_ball_lt 0 c
  have hvpos : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzc)
  have hSbdd : BddAbove S := by
    refine ⟨R / ‖z - c‖, ?_⟩
    intro t ht
    have hmem := hR ht
    rw [Metric.mem_ball, dist_eq_norm] at hmem
    have heq : f t - c = t • (z - c) := by
      dsimp only [f]
      module
    rw [heq, norm_smul, Real.norm_eq_abs] at hmem
    have habs : |t| < R / ‖z - c‖ :=
      (lt_div_iff₀ hvpos).2 hmem
    exact (le_abs_self t).trans habs.le
  let T := sSup S
  obtain ⟨eps, heps, hepsSub⟩ := Metric.isOpen_iff.mp hSopen 1 h1
  let a := 1 + eps / 2
  have haBall : a ∈ Metric.ball (1 : ℝ) eps := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp only [a]
    rw [add_sub_cancel_left, abs_of_pos (half_pos heps)]
    linarith
  have ha : a ∈ S := hepsSub haBall
  have haT : a ≤ T := le_csSup hSbdd ha
  have hT : 1 < T := by
    apply lt_of_lt_of_le _ haT
    dsimp only [a]
    linarith
  have hTclosure : T ∈ closure S := csSup_mem_closure hSne hSbdd
  have hetaClosure : f T ∈ closure Omega.carrier := by
    have himage : f T ∈ f '' closure S := ⟨T, hTclosure, rfl⟩
    have hclosureImage : f '' closure S ⊆ closure (f '' S) :=
      image_closure_subset_closure_image hf
    apply closure_mono _ (hclosureImage himage)
    rintro _ ⟨t, ht, rfl⟩
    exact ht
  have hTnot : T ∉ S := by
    intro hTS
    obtain ⟨eps, heps, hepsSub⟩ := Metric.isOpen_iff.mp hSopen T hTS
    let b := T + eps / 2
    have hbBall : b ∈ Metric.ball T eps := by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp only [b]
      rw [add_sub_cancel_left, abs_of_pos (half_pos heps)]
      linarith
    have hb : b ∈ S := hepsSub hbBall
    have hbT : b ≤ T := le_csSup hSbdd hb
    dsimp only [b] at hbT
    linarith
  have heta : f T ∈ frontier Omega.carrier := by
    rw [frontier, Omega.isOpen_carrier.interior_eq]
    exact ⟨hetaClosure, hTnot⟩
  let r := 1 - T⁻¹
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hrpos : 0 < r := by
    dsimp only [r]
    rw [sub_pos]
    exact (inv_lt_one₀ hTpos).2 hT
  have hrle : r ≤ 1 := by
    dsimp only [r]
    exact sub_le_self 1 (inv_nonneg.mpr hTpos.le)
  refine ⟨r, ⟨hrpos, hrle⟩, f T, heta, ?_⟩
  unfold smoothJordanInwardPoint
  dsimp only [r, f]
  rw [show 1 - (1 - T⁻¹) = T⁻¹ by ring, smul_add, smul_smul,
    inv_mul_cancel₀ hTpos.ne', one_smul]
  module

/-- Under winding normalization, every carrier point has inward coordinates
without a separate boundedness hypothesis. -/
theorem exists_inward_coordinates_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain)
    (hkernel : ∀ w ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega w = 1)
    {c z : ℂ} (hc : c ∈ Omega.carrier) (hz : z ∈ Omega.carrier) :
    ∃ r ∈ Ioc (0 : ℝ) 1, ∃ eta ∈ frontier Omega.carrier,
      smoothJordanInwardPoint c eta r = z := by
  exact exists_inward_coordinates Omega
    (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel) hc hz

/-- One ball about an interior center gives the same linear-in-`r`
separation estimate simultaneously for every chord endpoint and every test
point on the frontier. -/
theorem exists_uniform_inward_boundary_denominator_bound
    (Omega : SmoothJordanDomain) {c : ℂ} (hc : c ∈ Omega.carrier) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ xi ∈ frontier Omega.carrier,
        ∀ r ∈ Ioc (0 : ℝ) 1, ∀ sigma ∈ frontier Omega.carrier,
          r * delta ≤ ‖sigma - smoothJordanInwardPoint c xi r‖ := by
  obtain ⟨delta, hdelta, hball⟩ :=
    Metric.isOpen_iff.mp Omega.isOpen_carrier c hc
  refine ⟨delta, hdelta, ?_⟩
  intro xi hxi r hr sigma hsigma
  apply le_of_not_gt
  intro hlt
  let z := smoothJordanInwardPoint c xi r
  let y : ℂ := c + r⁻¹ • (sigma - z)
  have hyball : y ∈ Metric.ball c delta := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖y - c‖ = r⁻¹ * ‖sigma - z‖ := by
      simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr.1)]
    rw [hnorm]
    calc
      r⁻¹ * ‖sigma - z‖ < r⁻¹ * (r * delta) :=
        mul_lt_mul_of_pos_left hlt (inv_pos.mpr hr.1)
      _ = delta := by
        rw [← mul_assoc, inv_mul_cancel₀ hr.1.ne', one_mul]
  have hy : y ∈ Omega.carrier := hball hyball
  have hyint : y ∈ interior Omega.carrier := by
    rwa [Omega.isOpen_carrier.interior_eq]
  have hcombo : (1 - r) • xi + r • y = sigma := by
    simp only [y, z, smoothJordanInwardPoint, smul_add, smul_smul,
      mul_inv_cancel₀ hr.1.ne', one_smul]
    module
  have hsigmaInt : sigma ∈ interior Omega.carrier := by
    rw [← hcombo]
    exact
      Omega.strictConvex_carrier.convex.combo_closure_interior_mem_interior
        (frontier_subset_closure hxi) hyint
        (sub_nonneg.mpr hr.2) hr.1 (by ring)
  have hsigmaCarrier : sigma ∈ Omega.carrier := interior_subset hsigmaInt
  have hempty : sigma ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hsigmaCarrier, hsigma⟩
  exact hempty

/-- An interior ball gives a linear-in-`r` lower bound on the distance from
the inward chord point to every frontier point. -/
theorem exists_inward_boundary_denominator_bound
    (Omega : SmoothJordanDomain) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ sigma ∈ frontier Omega.carrier,
        r * delta ≤ ‖sigma - smoothJordanInwardPoint c xi r‖ := by
  obtain ⟨delta, hdelta, hbound⟩ :=
    exists_uniform_inward_boundary_denominator_bound Omega hc
  refine ⟨delta, hdelta, ?_⟩
  intro r hr sigma hsigma
  exact hbound xi hxi r hr sigma hsigma

/-- For a fixed interior center, compactness of the frontier also bounds the
chord lengths.  Consequently the multiplied cancellation estimate has
constants independent of both frontier points. -/
theorem exists_uniform_inward_boundary_cross_bound
    (Omega : SmoothJordanDomain) {c : ℂ} (hc : c ∈ Omega.carrier) :
    ∃ delta R : ℝ, 0 < delta ∧ 0 ≤ R ∧
      ∀ xi ∈ frontier Omega.carrier,
        ∀ r ∈ Ioc (0 : ℝ) 1, ∀ sigma ∈ frontier Omega.carrier,
          delta * ‖smoothJordanInwardPoint c xi r - xi‖ ≤
            R * ‖sigma - smoothJordanInwardPoint c xi r‖ := by
  obtain ⟨delta, hdelta, hbound⟩ :=
    exists_uniform_inward_boundary_denominator_bound Omega hc
  let f : ℂ → ℝ := fun xi => ‖c - xi‖
  have hf : Continuous f := continuous_const.sub continuous_id |>.norm
  have hnonempty : (frontier Omega.carrier).Nonempty := by
    refine ⟨Omega.boundaryParam 0, ?_⟩
    rw [← Omega.boundaryParam_range]
    exact mem_range_self 0
  obtain ⟨xiMax, hxiMax, hmax⟩ :=
    Omega.isCompact_frontier.exists_isMaxOn hnonempty hf.continuousOn
  refine ⟨delta, f xiMax, hdelta, norm_nonneg _, ?_⟩
  intro xi hxi r hr sigma hsigma
  have hdisplacement :
      ‖smoothJordanInwardPoint c xi r - xi‖ = r * ‖c - xi‖ := by
    have heq : smoothJordanInwardPoint c xi r - xi = r • (c - xi) := by
      simp only [smoothJordanInwardPoint]
      module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
  rw [hdisplacement]
  calc
    delta * (r * ‖c - xi‖) = ‖c - xi‖ * (r * delta) := by ring
    _ ≤ ‖c - xi‖ * ‖sigma - smoothJordanInwardPoint c xi r‖ :=
      mul_le_mul_of_nonneg_left (hbound xi hxi r hr sigma hsigma)
        (norm_nonneg _)
    _ ≤ f xiMax * ‖sigma - smoothJordanInwardPoint c xi r‖ :=
      mul_le_mul_of_nonneg_right (hmax hxi) (norm_nonneg _)

/-- The preceding denominator bound in the multiplied form used after the
resolvent identity.  The chord displacement contributes exactly the same
factor `r` as the boundary separation, leaving a uniform domination
constant. -/
theorem exists_inward_boundary_cross_bound
    (Omega : SmoothJordanDomain) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ sigma ∈ frontier Omega.carrier,
        delta * ‖smoothJordanInwardPoint c xi r - xi‖ ≤
          ‖c - xi‖ * ‖sigma - smoothJordanInwardPoint c xi r‖ := by
  obtain ⟨delta, hdelta, hbound⟩ :=
    exists_inward_boundary_denominator_bound Omega hc hxi
  refine ⟨delta, hdelta, ?_⟩
  intro r hr sigma hsigma
  have hdisplacement :
      ‖smoothJordanInwardPoint c xi r - xi‖ = r * ‖c - xi‖ := by
    have heq : smoothJordanInwardPoint c xi r - xi = r • (c - xi) := by
      simp only [smoothJordanInwardPoint]
      module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
  rw [hdisplacement]
  calc
    delta * (r * ‖c - xi‖) = ‖c - xi‖ * (r * delta) := by ring
    _ ≤ ‖c - xi‖ * ‖sigma - smoothJordanInwardPoint c xi r‖ :=
      mul_le_mul_of_nonneg_left (hbound r hr sigma hsigma)
        (norm_nonneg _)

/-- For a fixed interior center and polynomial, the integrand domination
constant can be chosen uniformly over every frontier chord endpoint. -/
theorem exists_uniform_norm_inward_regularized_integrand_sub_le
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c : ℂ}
    (hc : c ∈ Omega.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ xi ∈ frontier Omega.carrier,
        ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
          ‖deriv Omega.boundaryParam t •
            (((star (Polynomial.eval (Omega.boundaryParam t) p) -
                  star (Polynomial.eval xi p)) *
                (Omega.boundaryParam t -
                  smoothJordanInwardPoint c xi r)⁻¹) -
              ((star (Polynomial.eval (Omega.boundaryParam t) p) -
                  star (Polynomial.eval xi p)) *
                (Omega.boundaryParam t - xi)⁻¹))‖ ≤
            C * (‖deriv Omega.boundaryParam t‖ *
              ‖Polynomial.eval (Omega.boundaryParam t)
                (p /ₘ (Polynomial.X - Polynomial.C xi))‖) := by
  obtain ⟨delta, R, hdelta, hR, hcross⟩ :=
    exists_uniform_inward_boundary_cross_bound Omega hc
  let C := R / delta
  refine ⟨C, div_nonneg hR hdelta.le, ?_⟩
  intro xi hxi r hr t _ht
  let q := p /ₘ (Polynomial.X - Polynomial.C xi)
  let sigma := Omega.boundaryParam t
  let z := smoothJordanInwardPoint c xi r
  have hsigma : sigma ∈ frontier Omega.carrier := by
    dsimp only [sigma]
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hz : z ∈ Omega.carrier :=
    smoothJordanInwardPoint_mem_carrier Omega hc hxi hr
  have hsigmaz : sigma - z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have hsigmaCarrier : sigma ∈ Omega.carrier := heq ▸ hz
    have hempty : sigma ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hsigmaCarrier, hsigma⟩
    exact hempty
  change
    ‖deriv Omega.boundaryParam t •
      (((star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
            (sigma - z)⁻¹) -
        ((star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
            (sigma - xi)⁻¹))‖ ≤
      C * (‖deriv Omega.boundaryParam t‖ * ‖Polynomial.eval sigma q‖)
  by_cases hsigmaXi : sigma = xi
  · rw [hsigmaXi]
    simp only [sub_self, inv_zero, mul_zero, zero_mul]
    rw [smul_zero, norm_zero]
    exact mul_nonneg (div_nonneg hR hdelta.le)
      (mul_nonneg (norm_nonneg (deriv Omega.boundaryParam t))
        (norm_nonneg (Polynomial.eval xi q)))
  have hsigmaXiSub : sigma - xi ≠ 0 := sub_ne_zero.mpr hsigmaXi
  have hpoly : Polynomial.C (Polynomial.eval xi p) +
      (Polynomial.X - Polynomial.C xi) * q = p := by
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p xi]
    exact Polynomial.modByMonic_add_div p
      (Polynomial.X - Polynomial.C xi)
  have heval : Polynomial.eval sigma p - Polynomial.eval xi p =
      (sigma - xi) * Polynomial.eval sigma q := by
    have h := congrArg (Polynomial.eval sigma) hpoly
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X] at h
    rw [← h]
    ring
  have hstar :
      star (Polynomial.eval sigma p) - star (Polynomial.eval xi p) =
        star (sigma - xi) * star (Polynomial.eval sigma q) := by
    rw [← star_sub, heval, star_mul]
    ring
  have hmiddle : (sigma - xi) - (sigma - z) = z - xi := by ring
  have hnorm :
      ‖((star (Polynomial.eval sigma p) -
            star (Polynomial.eval xi p)) * (sigma - z)⁻¹) -
          ((star (Polynomial.eval sigma p) -
            star (Polynomial.eval xi p)) * (sigma - xi)⁻¹)‖ =
        ‖Polynomial.eval sigma q‖ *
          (‖z - xi‖ / ‖sigma - z‖) := by
    rw [← mul_sub, inv_sub_inv' hsigmaz hsigmaXiSub, hstar,
      norm_mul, norm_mul, norm_mul, norm_mul, norm_star, norm_star,
      norm_inv, norm_inv, hmiddle]
    field_simp [norm_ne_zero_iff.mpr hsigmaz,
      norm_ne_zero_iff.mpr hsigmaXiSub]
  have hratio : ‖z - xi‖ / ‖sigma - z‖ ≤ R / delta := by
    apply (div_le_div_iff₀ (norm_pos_iff.mpr hsigmaz) hdelta).2
    simpa only [z, sigma, mul_comm] using
      hcross xi hxi r hr sigma hsigma
  simp only [smul_eq_mul, norm_mul]
  rw [hnorm]
  calc
    ‖deriv Omega.boundaryParam t‖ *
          (‖Polynomial.eval sigma q‖ * (‖z - xi‖ / ‖sigma - z‖)) =
        (‖z - xi‖ / ‖sigma - z‖) *
          (‖deriv Omega.boundaryParam t‖ *
            ‖Polynomial.eval sigma q‖) := by ring
    _ ≤ C * (‖deriv Omega.boundaryParam t‖ *
          ‖Polynomial.eval sigma q‖) :=
      mul_le_mul_of_nonneg_right hratio
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Joint continuity of the divided difference and the uniform chord
geometry give a single integrable majorant, depending only on the fixed
center and polynomial, for all frontier endpoints and inward radii. -/
theorem exists_uniform_norm_inward_regularized_integrand_sub_le_deriv
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c : ℂ}
    (hc : c ∈ Omega.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ xi ∈ frontier Omega.carrier,
        ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
          ‖deriv Omega.boundaryParam t •
            (((star (Polynomial.eval (Omega.boundaryParam t) p) -
                  star (Polynomial.eval xi p)) *
                (Omega.boundaryParam t -
                  smoothJordanInwardPoint c xi r)⁻¹) -
              ((star (Polynomial.eval (Omega.boundaryParam t) p) -
                  star (Polynomial.eval xi p)) *
                (Omega.boundaryParam t - xi)⁻¹))‖ ≤
            C * ‖deriv Omega.boundaryParam t‖ := by
  obtain ⟨C, hC, hdom⟩ :=
    exists_uniform_norm_inward_regularized_integrand_sub_le Omega p hc
  obtain ⟨Q, hQ, hq⟩ :=
    exists_uniform_norm_eval_divByMonic_X_sub_C_frontier_le Omega p
  refine ⟨C * Q, mul_nonneg hC hQ, ?_⟩
  intro xi hxi r hr t ht
  have hsigma : Omega.boundaryParam t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  calc
    ‖deriv Omega.boundaryParam t •
          (((star (Polynomial.eval (Omega.boundaryParam t) p) -
                star (Polynomial.eval xi p)) *
              (Omega.boundaryParam t -
                smoothJordanInwardPoint c xi r)⁻¹) -
            ((star (Polynomial.eval (Omega.boundaryParam t) p) -
                star (Polynomial.eval xi p)) *
              (Omega.boundaryParam t - xi)⁻¹))‖ ≤
        C * (‖deriv Omega.boundaryParam t‖ *
          ‖Polynomial.eval (Omega.boundaryParam t)
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖) :=
      hdom xi hxi r hr t ht
    _ ≤ C * (‖deriv Omega.boundaryParam t‖ * Q) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hq xi hxi _ hsigma) (norm_nonneg _)) hC
    _ = (C * Q) * ‖deriv Omega.boundaryParam t‖ := by ring

/-- Along inward chords, the parameterized regularized kernel minus its
self-kernel is uniformly dominated by a constant times the continuous
integrable function `‖boundaryParam'‖ * ‖q.eval boundaryParam‖`, where
`q = p /ₘ (X - C xi)`.  This is the exact domination input for a radial
Plemelj limit. -/
theorem exists_norm_inward_regularized_integrand_sub_le
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
        ‖deriv Omega.boundaryParam t •
          (((star (Polynomial.eval (Omega.boundaryParam t) p) -
                star (Polynomial.eval xi p)) *
              (Omega.boundaryParam t -
                smoothJordanInwardPoint c xi r)⁻¹) -
            ((star (Polynomial.eval (Omega.boundaryParam t) p) -
                star (Polynomial.eval xi p)) *
              (Omega.boundaryParam t - xi)⁻¹))‖ ≤
          C * (‖deriv Omega.boundaryParam t‖ *
            ‖Polynomial.eval (Omega.boundaryParam t)
              (p /ₘ (Polynomial.X - Polynomial.C xi))‖) := by
  obtain ⟨delta, hdelta, hcross⟩ :=
    exists_inward_boundary_cross_bound Omega hc hxi
  let q := p /ₘ (Polynomial.X - Polynomial.C xi)
  let C := ‖c - xi‖ / delta
  refine ⟨C, div_nonneg (norm_nonneg _) hdelta.le, ?_⟩
  intro r hr t _ht
  let sigma := Omega.boundaryParam t
  let z := smoothJordanInwardPoint c xi r
  have hsigma : sigma ∈ frontier Omega.carrier := by
    dsimp only [sigma]
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hz : z ∈ Omega.carrier :=
    smoothJordanInwardPoint_mem_carrier Omega hc hxi hr
  have hsigmaz : sigma - z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have hsigmaCarrier : sigma ∈ Omega.carrier := heq ▸ hz
    have hempty : sigma ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hsigmaCarrier, hsigma⟩
    exact hempty
  change
    ‖deriv Omega.boundaryParam t •
      (((star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
            (sigma - z)⁻¹) -
        ((star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
            (sigma - xi)⁻¹))‖ ≤
      C * (‖deriv Omega.boundaryParam t‖ * ‖Polynomial.eval sigma q‖)
  by_cases hsigmaXi : sigma = xi
  · rw [hsigmaXi]
    simp only [sub_self, inv_zero, mul_zero, zero_mul]
    dsimp only [C]
    rw [smul_zero, norm_zero]
    exact mul_nonneg (div_nonneg (norm_nonneg (c - xi)) hdelta.le)
      (mul_nonneg (norm_nonneg (deriv Omega.boundaryParam t))
        (norm_nonneg (Polynomial.eval xi q)))
  have hsigmaXiSub : sigma - xi ≠ 0 := sub_ne_zero.mpr hsigmaXi
  have hpoly : Polynomial.C (Polynomial.eval xi p) +
      (Polynomial.X - Polynomial.C xi) * q = p := by
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p xi]
    exact Polynomial.modByMonic_add_div p
      (Polynomial.X - Polynomial.C xi)
  have heval : Polynomial.eval sigma p - Polynomial.eval xi p =
      (sigma - xi) * Polynomial.eval sigma q := by
    have h := congrArg (Polynomial.eval sigma) hpoly
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X] at h
    rw [← h]
    ring
  have hstar :
      star (Polynomial.eval sigma p) - star (Polynomial.eval xi p) =
        star (sigma - xi) * star (Polynomial.eval sigma q) := by
    rw [← star_sub, heval, star_mul]
    ring
  have hmiddle : (sigma - xi) - (sigma - z) = z - xi := by ring
  have hnorm :
      ‖((star (Polynomial.eval sigma p) -
            star (Polynomial.eval xi p)) * (sigma - z)⁻¹) -
          ((star (Polynomial.eval sigma p) -
            star (Polynomial.eval xi p)) * (sigma - xi)⁻¹)‖ =
        ‖Polynomial.eval sigma q‖ *
          (‖z - xi‖ / ‖sigma - z‖) := by
    rw [← mul_sub, inv_sub_inv' hsigmaz hsigmaXiSub, hstar,
      norm_mul, norm_mul, norm_mul, norm_mul, norm_star, norm_star,
      norm_inv, norm_inv, hmiddle]
    field_simp [norm_ne_zero_iff.mpr hsigmaz,
      norm_ne_zero_iff.mpr hsigmaXiSub]
  have hratio : ‖z - xi‖ / ‖sigma - z‖ ≤ ‖c - xi‖ / delta := by
    apply (div_le_div_iff₀ (norm_pos_iff.mpr hsigmaz) hdelta).2
    simpa only [z, sigma, mul_comm] using hcross r hr sigma hsigma
  simp only [smul_eq_mul, norm_mul]
  rw [hnorm]
  calc
    ‖deriv Omega.boundaryParam t‖ *
          (‖Polynomial.eval sigma q‖ * (‖z - xi‖ / ‖sigma - z‖)) =
        (‖z - xi‖ / ‖sigma - z‖) *
          (‖deriv Omega.boundaryParam t‖ *
            ‖Polynomial.eval sigma q‖) := by ring
    _ ≤ C * (‖deriv Omega.boundaryParam t‖ *
          ‖Polynomial.eval sigma q‖) :=
      mul_le_mul_of_nonneg_right hratio
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The regularized scalar companion converges to its self-integral along
every inward chord from a frontier point to an interior center.  The proof is
an ordinary dominated-convergence argument using the preceding geometric
majorant; unlike full unrestricted Plemelj continuity, it requires no local
chart or curvature estimate. -/
theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_inward
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun r : ℝ ↦ crouzeixPolynomialScalarCompanionRegularized
        Omega p xi (smoothJordanInwardPoint c xi r))
      (nhdsWithin 0 (Ioc (0 : ℝ) 1))
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by
  let l : Filter ℝ := nhdsWithin 0 (Ioc (0 : ℝ) 1)
  let q := p /ₘ (Polynomial.X - Polynomial.C xi)
  let N : ℂ → ℂ := fun sigma ↦
    star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)
  let D : ℝ → ℝ → ℂ := fun r t ↦
    deriv Omega.boundaryParam t •
      ((N (Omega.boundaryParam t) *
          (Omega.boundaryParam t - smoothJordanInwardPoint c xi r)⁻¹) -
        (N (Omega.boundaryParam t) *
          (Omega.boundaryParam t - xi)⁻¹))
  obtain ⟨C, hC, hdom⟩ :=
    exists_norm_inward_regularized_integrand_sub_le Omega p hc hxi
  let bound : ℝ → ℝ := fun t ↦
    C * (‖deriv Omega.boundaryParam t‖ *
      ‖Polynomial.eval (Omega.boundaryParam t) q‖)
  have hboundCont : Continuous bound := by
    exact continuous_const.mul
      ((Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).norm.mul
        (q.continuous.comp
          Omega.boundaryParam_contDiff.continuous).norm)
  have hboundInt : IntervalIntegrable bound MeasureTheory.volume
      (0 : ℝ) (2 * Real.pi) := hboundCont.intervalIntegrable _ _
  have hselfInt :=
    contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
      Omega p xi
  have hDmeas : ∀ᶠ r in l,
      AEStronglyMeasurable (D r)
        (MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hz : smoothJordanInwardPoint c xi r ∈ Omega.carrier :=
      smoothJordanInwardPoint_mem_carrier Omega hc hxi hr
    have hne : ∀ t : ℝ,
        Omega.boundaryParam t - smoothJordanInwardPoint c xi r ≠ 0 := by
      intro t
      apply sub_ne_zero.mpr
      intro heq
      have hsigma : Omega.boundaryParam t ∈ frontier Omega.carrier := by
        rw [← Omega.boundaryParam_range]
        exact mem_range_self t
      have hsigmaCarrier : Omega.boundaryParam t ∈ Omega.carrier := heq ▸ hz
      have hempty : Omega.boundaryParam t ∈ (∅ : Set ℂ) := by
        rw [← Omega.isOpen_carrier.inter_frontier_eq]
        exact ⟨hsigmaCarrier, hsigma⟩
      exact hempty
    have hden : Continuous (fun t : ℝ ↦
        Omega.boundaryParam t - smoothJordanInwardPoint c xi r) :=
      Omega.boundaryParam_contDiff.continuous.sub continuous_const
    have hfirst : StronglyMeasurable (fun t : ℝ ↦
        deriv Omega.boundaryParam t •
          (N (Omega.boundaryParam t) *
            (Omega.boundaryParam t -
              smoothJordanInwardPoint c xi r)⁻¹)) := by
      apply Continuous.stronglyMeasurable
      exact
        (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).smul
          ((((p.continuous.comp
              Omega.boundaryParam_contDiff.continuous).star.sub
                continuous_const).mul (hden.inv₀ hne)))
    have hselfMeas : AEStronglyMeasurable
        (fun t : ℝ ↦ deriv Omega.boundaryParam t •
          (N (Omega.boundaryParam t) *
            (Omega.boundaryParam t - xi)⁻¹))
        (MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
      change IntervalIntegrable
          (fun t : ℝ ↦ deriv Omega.boundaryParam t •
            ((star (Polynomial.eval (Omega.boundaryParam t) p) -
                star (Polynomial.eval xi p)) *
              (Omega.boundaryParam t - xi)⁻¹))
          MeasureTheory.volume (0 : ℝ) (2 * Real.pi) at hselfInt
      exact hselfInt.def'.aestronglyMeasurable
    have heq : D r =
        (fun t : ℝ ↦ deriv Omega.boundaryParam t •
          (N (Omega.boundaryParam t) *
            (Omega.boundaryParam t -
              smoothJordanInwardPoint c xi r)⁻¹)) -
        fun t : ℝ ↦ deriv Omega.boundaryParam t •
          (N (Omega.boundaryParam t) *
            (Omega.boundaryParam t - xi)⁻¹) := by
      funext t
      simp only [D, Pi.sub_apply, smul_sub]
    rw [heq]
    exact hfirst.aestronglyMeasurable.sub hselfMeas
  have hDbound : ∀ᶠ r in l,
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
        ‖D r t‖ ≤ bound t := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards with t
    intro ht
    have ht' := uIoc_subset_uIcc ht
    rw [uIcc_of_le Real.two_pi_pos.le] at ht'
    exact hdom r hr t ht'
  have hDlim : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Ι (0 : ℝ) (2 * Real.pi) →
        Filter.Tendsto (fun r ↦ D r t) l (nhds 0) := by
    filter_upwards with t
    intro _ht
    let sigma := Omega.boundaryParam t
    by_cases hsigma : sigma = xi
    · have hzero : (fun r ↦ D r t) = fun _ ↦ 0 := by
        funext r
        dsimp only [D, N, sigma] at hsigma ⊢
        rw [hsigma]
        simp only [sub_self, inv_zero, mul_zero, zero_mul, sub_self, smul_zero]
      rw [hzero]
      exact tendsto_const_nhds
    · have hzcont : Continuous (smoothJordanInwardPoint c xi) := by
        unfold smoothJordanInwardPoint
        fun_prop
      have hden : ContinuousAt
          (fun r : ℝ ↦ sigma - smoothJordanInwardPoint c xi r) 0 :=
        continuousAt_const.sub hzcont.continuousAt
      have hden0 : sigma - smoothJordanInwardPoint c xi 0 ≠ 0 := by
        simpa only [smoothJordanInwardPoint, sub_zero, one_smul, zero_smul,
          add_zero] using sub_ne_zero.mpr hsigma
      have hinv := hden.inv₀ hden0
      have hmul : ContinuousAt
          (fun r : ℝ ↦ N sigma *
            (sigma - smoothJordanInwardPoint c xi r)⁻¹) 0 :=
        continuousAt_const.mul hinv
      have hsecond : ContinuousAt
          (fun _ : ℝ ↦ N sigma * (sigma - xi)⁻¹) 0 :=
        continuousAt_const
      have hcont : ContinuousAt (fun r ↦ D r t) 0 := by
        change ContinuousAt
          (fun r : ℝ ↦ deriv Omega.boundaryParam t •
            (N sigma * (sigma - smoothJordanInwardPoint c xi r)⁻¹ -
              N sigma * (sigma - xi)⁻¹)) 0
        have hderiv : ContinuousAt
            (fun _ : ℝ ↦ deriv Omega.boundaryParam t) 0 :=
          continuousAt_const
        exact hderiv.smul (hmul.sub hsecond)
      have hl : l ≤ nhds (0 : ℝ) := by
        dsimp only [l, nhdsWithin]
        exact inf_le_left
      have htend := hcont.tendsto.mono_left hl
      simpa only [l, D, smoothJordanInwardPoint, sub_zero, one_smul,
        zero_smul, add_zero, sub_self, smul_zero] using htend
  have hDIntegral : Filter.Tendsto
      (fun r ↦ ∫ t in (0 : ℝ)..(2 * Real.pi), D r t)
      l (nhds 0) := by
    have h :=
      intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        bound hDmeas hDbound hboundInt hDlim
    simpa only [intervalIntegral.integral_zero] using h
  rw [← tendsto_sub_nhds_zero_iff]
  have hscaled : Filter.Tendsto
      (fun r ↦ (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in (0 : ℝ)..(2 * Real.pi), D r t)
      l (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hDIntegral
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hz : smoothJordanInwardPoint c xi r ∈ Omega.carrier :=
    smoothJordanInwardPoint_mem_carrier Omega hc hxi hr
  have hzfrontier : smoothJordanInwardPoint c xi r ∉
      frontier Omega.carrier := by
    intro hzfrontier
    have hempty : smoothJordanInwardPoint c xi r ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hzfrontier⟩
    exact hempty
  have hfirst : ContourIntegrable
      (fun sigma ↦ N sigma *
        (sigma - smoothJordanInwardPoint c xi r)⁻¹)
      Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · have hden : ContinuousOn
          (fun sigma : ℂ ↦
            sigma - smoothJordanInwardPoint c xi r)
          (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) :=
        continuous_id.continuousOn.sub continuous_const.continuousOn
      have hne : ∀ sigma ∈
          Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi),
          sigma - smoothJordanInwardPoint c xi r ≠ 0 := by
        rintro sigma ⟨t, _ht, rfl⟩ hzero
        apply hzfrontier
        have heq := sub_eq_zero.mp hzero
        rw [← heq, ← Omega.boundaryParam_range]
        exact mem_range_self t
      exact ((p.continuous.star.continuousOn.sub
        continuous_const.continuousOn).mul (hden.inv₀ hne))
  have hself : ContourIntegrable
      (fun sigma ↦ N sigma * (sigma - xi)⁻¹)
      Omega.boundaryParam := by
    exact
      contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
        Omega p xi
  unfold crouzeixPolynomialScalarCompanionRegularized
  rw [← mul_sub, ← contourIntegral_sub hfirst hself]
  rfl

/-- When the scalar winding kernel is normalized to one in the carrier, the
full scalar companion converges along every inward chord to the explicit
Plemelj boundary value. -/
theorem tendsto_crouzeixPolynomialScalarCompanion_inward
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {c xi : ℂ} (hc : c ∈ Omega.carrier)
    (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun r : ℝ ↦ crouzeixPolynomialScalarCompanion Omega p
        (smoothJordanInwardPoint c xi r))
      (nhdsWithin 0 (Ioc (0 : ℝ) 1))
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by
  have hreg :=
    tendsto_crouzeixPolynomialScalarCompanionRegularized_inward
      Omega p hc hxi
  have hlim : Filter.Tendsto
      (fun r : ℝ ↦ star (Polynomial.eval xi p) +
        crouzeixPolynomialScalarCompanionRegularized Omega p xi
          (smoothJordanInwardPoint c xi r))
      (nhdsWithin 0 (Ioc (0 : ℝ) 1))
      (nhds (star (Polynomial.eval xi p) +
        crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) :=
    tendsto_const_nhds.add hreg
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hz : smoothJordanInwardPoint c xi r ∈ Omega.carrier :=
    smoothJordanInwardPoint_mem_carrier Omega hc hxi hr
  have hzfrontier : smoothJordanInwardPoint c xi r ∉
      frontier Omega.carrier := by
    intro hzfrontier
    have hempty : smoothJordanInwardPoint c xi r ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hzfrontier⟩
    exact hempty
  rw [crouzeixPolynomialScalarCompanion_eq_regularized_add Omega p xi
    hzfrontier, hkernel _ hz, mul_one]
  exact add_comm _ _

/-- The radial Plemelj error tends to zero jointly when the inward radius
tends to zero and the chord endpoint varies along the frontier.  The target
self-value moves with the endpoint; continuity of that self-value is a
separate remaining step. -/
theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_sub_self_joint
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun x : ℝ × ℂ =>
        crouzeixPolynomialScalarCompanionRegularized Omega p x.2
            (smoothJordanInwardPoint c x.2 x.1) -
          crouzeixPolynomialScalarCompanionRegularized Omega p x.2 x.2)
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))
      (nhds 0) := by
  let l : Filter (ℝ × ℂ) := nhdsWithin (0, xi)
    (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier)
  let N : ℂ → ℂ → ℂ := fun eta sigma =>
    star (Polynomial.eval sigma p) - star (Polynomial.eval eta p)
  let D : (ℝ × ℂ) → ℝ → ℂ := fun x t =>
    deriv Omega.boundaryParam t •
      ((N x.2 (Omega.boundaryParam t) *
          (Omega.boundaryParam t -
            smoothJordanInwardPoint c x.2 x.1)⁻¹) -
        (N x.2 (Omega.boundaryParam t) *
          (Omega.boundaryParam t - x.2)⁻¹))
  obtain ⟨C, hC, hdom⟩ :=
    exists_uniform_norm_inward_regularized_integrand_sub_le_deriv
      Omega p hc
  let bound : ℝ → ℝ := fun t => C * ‖deriv Omega.boundaryParam t‖
  have hboundCont : Continuous bound :=
    continuous_const.mul
      (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).norm
  have hboundInt : IntervalIntegrable bound MeasureTheory.volume
      (0 : ℝ) (2 * Real.pi) := hboundCont.intervalIntegrable _ _
  have hDmeas : ∀ᶠ x in l,
      AEStronglyMeasurable (D x)
        (MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hz : smoothJordanInwardPoint c x.2 x.1 ∈ Omega.carrier :=
      smoothJordanInwardPoint_mem_carrier Omega hc hx.2 hx.1
    have hne : ∀ t : ℝ,
        Omega.boundaryParam t -
          smoothJordanInwardPoint c x.2 x.1 ≠ 0 := by
      intro t
      apply sub_ne_zero.mpr
      intro heq
      have hsigma : Omega.boundaryParam t ∈ frontier Omega.carrier := by
        rw [← Omega.boundaryParam_range]
        exact mem_range_self t
      have hsigmaCarrier : Omega.boundaryParam t ∈ Omega.carrier := heq ▸ hz
      have hempty : Omega.boundaryParam t ∈ (∅ : Set ℂ) := by
        rw [← Omega.isOpen_carrier.inter_frontier_eq]
        exact ⟨hsigmaCarrier, hsigma⟩
      exact hempty
    have hden : Continuous (fun t : ℝ =>
        Omega.boundaryParam t - smoothJordanInwardPoint c x.2 x.1) :=
      Omega.boundaryParam_contDiff.continuous.sub continuous_const
    have hfirst : StronglyMeasurable (fun t : ℝ =>
        deriv Omega.boundaryParam t •
          (N x.2 (Omega.boundaryParam t) *
            (Omega.boundaryParam t -
              smoothJordanInwardPoint c x.2 x.1)⁻¹)) := by
      apply Continuous.stronglyMeasurable
      exact
        (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).smul
          ((((p.continuous.comp
              Omega.boundaryParam_contDiff.continuous).star.sub
                continuous_const).mul (hden.inv₀ hne)))
    have hselfInt :=
      contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
        Omega p x.2
    have hselfMeas : AEStronglyMeasurable
        (fun t : ℝ => deriv Omega.boundaryParam t •
          (N x.2 (Omega.boundaryParam t) *
            (Omega.boundaryParam t - x.2)⁻¹))
        (MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
      change IntervalIntegrable
          (fun t : ℝ => deriv Omega.boundaryParam t •
            ((star (Polynomial.eval (Omega.boundaryParam t) p) -
                star (Polynomial.eval x.2 p)) *
              (Omega.boundaryParam t - x.2)⁻¹))
          MeasureTheory.volume (0 : ℝ) (2 * Real.pi) at hselfInt
      exact hselfInt.def'.aestronglyMeasurable
    have heq : D x =
        (fun t : ℝ => deriv Omega.boundaryParam t •
          (N x.2 (Omega.boundaryParam t) *
            (Omega.boundaryParam t -
              smoothJordanInwardPoint c x.2 x.1)⁻¹)) -
        fun t : ℝ => deriv Omega.boundaryParam t •
          (N x.2 (Omega.boundaryParam t) *
            (Omega.boundaryParam t - x.2)⁻¹) := by
      funext t
      simp only [D, Pi.sub_apply, smul_sub]
    rw [heq]
    exact hfirst.aestronglyMeasurable.sub hselfMeas
  have hDbound : ∀ᶠ x in l,
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
        ‖D x t‖ ≤ bound t := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    filter_upwards with t
    intro ht
    have ht' := uIoc_subset_uIcc ht
    rw [uIcc_of_le Real.two_pi_pos.le] at ht'
    exact hdom x.2 hx.2 x.1 hx.1 t ht'
  have hDlim : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Ι (0 : ℝ) (2 * Real.pi) →
        Filter.Tendsto (fun x => D x t) l (nhds 0) := by
    filter_upwards [ae_boundaryParam_ne_of_mem_frontier Omega hxi] with t htne
    intro ht
    let sigma := Omega.boundaryParam t
    have hsigma : sigma ≠ xi := htne ht
    have hzcont : Continuous (fun x : ℝ × ℂ =>
        smoothJordanInwardPoint c x.2 x.1) := by
      unfold smoothJordanInwardPoint
      fun_prop
    have hN : ContinuousAt (fun x : ℝ × ℂ => N x.2 sigma) (0, xi) := by
      dsimp only [N]
      fun_prop
    have hdenFirst : ContinuousAt (fun x : ℝ × ℂ =>
        sigma - smoothJordanInwardPoint c x.2 x.1) (0, xi) :=
      continuousAt_const.sub hzcont.continuousAt
    have hdenFirst0 :
        sigma - smoothJordanInwardPoint c xi 0 ≠ 0 := by
      simpa only [smoothJordanInwardPoint, sub_zero, one_smul, zero_smul,
        add_zero] using sub_ne_zero.mpr hsigma
    have hfirst := hN.mul (hdenFirst.inv₀ hdenFirst0)
    have hdenSelf : ContinuousAt (fun x : ℝ × ℂ => sigma - x.2) (0, xi) := by
      fun_prop
    have hdenSelf0 : sigma - xi ≠ 0 := sub_ne_zero.mpr hsigma
    have hself := hN.mul (hdenSelf.inv₀ hdenSelf0)
    have hcont : ContinuousAt (fun x => D x t) (0, xi) := by
      change ContinuousAt (fun x : ℝ × ℂ =>
        deriv Omega.boundaryParam t •
          (N x.2 sigma *
              (sigma - smoothJordanInwardPoint c x.2 x.1)⁻¹ -
            N x.2 sigma * (sigma - x.2)⁻¹)) (0, xi)
      have hderiv : ContinuousAt
          (fun _ : ℝ × ℂ => deriv Omega.boundaryParam t) (0, xi) :=
        continuousAt_const
      exact hderiv.smul (hfirst.sub hself)
    have hl : l ≤ nhds (0, xi) := by
      dsimp only [l, nhdsWithin]
      exact inf_le_left
    have htend := hcont.tendsto.mono_left hl
    simpa only [l, D, smoothJordanInwardPoint, sub_zero, one_smul,
      zero_smul, add_zero, sub_self, smul_zero] using htend
  have hDIntegral : Filter.Tendsto
      (fun x => ∫ t in (0 : ℝ)..(2 * Real.pi), D x t)
      l (nhds 0) := by
    have h :=
      intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        bound hDmeas hDbound hboundInt hDlim
    simpa only [intervalIntegral.integral_zero] using h
  have hscaled : Filter.Tendsto
      (fun x => (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in (0 : ℝ)..(2 * Real.pi), D x t)
      l (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hDIntegral
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hz : smoothJordanInwardPoint c x.2 x.1 ∈ Omega.carrier :=
    smoothJordanInwardPoint_mem_carrier Omega hc hx.2 hx.1
  have hzfrontier : smoothJordanInwardPoint c x.2 x.1 ∉
      frontier Omega.carrier := by
    intro hzfrontier
    have hempty : smoothJordanInwardPoint c x.2 x.1 ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hzfrontier⟩
    exact hempty
  have hfirst : ContourIntegrable
      (fun sigma => N x.2 sigma *
        (sigma - smoothJordanInwardPoint c x.2 x.1)⁻¹)
      Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · have hden : ContinuousOn
          (fun sigma : ℂ =>
            sigma - smoothJordanInwardPoint c x.2 x.1)
          (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) :=
        continuous_id.continuousOn.sub continuous_const.continuousOn
      have hne : ∀ sigma ∈
          Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi),
          sigma - smoothJordanInwardPoint c x.2 x.1 ≠ 0 := by
        rintro sigma ⟨t, _ht, rfl⟩ hzero
        apply hzfrontier
        have heq := sub_eq_zero.mp hzero
        rw [← heq, ← Omega.boundaryParam_range]
        exact mem_range_self t
      exact ((p.continuous.star.continuousOn.sub
        continuous_const.continuousOn).mul (hden.inv₀ hne))
  have hself : ContourIntegrable
      (fun sigma => N x.2 sigma * (sigma - x.2)⁻¹)
      Omega.boundaryParam :=
    contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
      Omega p x.2
  unfold crouzeixPolynomialScalarCompanionRegularized
  rw [← mul_sub, ← contourIntegral_sub hfirst hself]
  rfl

/-- The regularized self-value varies continuously along the frontier.  The
moving removable singularity is handled by dominated convergence, using
joint continuity and the compact-uniform bound for divided differences. -/
theorem continuousOn_crouzeixPolynomialScalarCompanionRegularized_self
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ContinuousOn
      (fun xi =>
        crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)
      (frontier Omega.carrier) := by
  intro xi hxi
  let l : Filter ℂ := nhdsWithin xi (frontier Omega.carrier)
  let q : ℂ → Polynomial ℂ := fun eta =>
    p /ₘ (Polynomial.X - Polynomial.C eta)
  let H : ℂ → ℝ → ℂ := fun eta t =>
    deriv Omega.boundaryParam t •
      (star (Omega.boundaryParam t - eta) *
        star (Polynomial.eval (Omega.boundaryParam t) (q eta)) *
          (Omega.boundaryParam t - eta)⁻¹)
  obtain ⟨Q, hQ, hq⟩ :=
    exists_uniform_norm_eval_divByMonic_X_sub_C_frontier_le Omega p
  let bound : ℝ → ℝ := fun t => Q * ‖deriv Omega.boundaryParam t‖
  have hboundCont : Continuous bound :=
    continuous_const.mul
      (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).norm
  have hboundInt : IntervalIntegrable bound MeasureTheory.volume
      (0 : ℝ) (2 * Real.pi) := hboundCont.intervalIntegrable _ _
  have hHmeas : ∀ᶠ eta in l,
      AEStronglyMeasurable (H eta)
        (MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [self_mem_nhdsWithin] with eta heta
    have hint :=
      contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
        Omega eta (q eta)
    change IntervalIntegrable
        (fun t : ℝ => deriv Omega.boundaryParam t •
          (star (Omega.boundaryParam t - eta) *
            star (Polynomial.eval (Omega.boundaryParam t) (q eta)) *
              (Omega.boundaryParam t - eta)⁻¹))
        MeasureTheory.volume (0 : ℝ) (2 * Real.pi) at hint
    exact hint.def'.aestronglyMeasurable
  have hHbound : ∀ᶠ eta in l,
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
        ‖H eta t‖ ≤ bound t := by
    filter_upwards [self_mem_nhdsWithin] with eta heta
    filter_upwards with t
    intro _ht
    have hsigma : Omega.boundaryParam t ∈ frontier Omega.carrier := by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self t
    let d := Omega.boundaryParam t - eta
    by_cases hd : d = 0
    · simp only [H, d] at hd ⊢
      rw [hd]
      simp only [star_zero, zero_mul, inv_zero, mul_zero, smul_zero,
        norm_zero]
      exact mul_nonneg hQ (norm_nonneg _)
    · have hdNorm : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
      have hqbound := hq eta heta (Omega.boundaryParam t) hsigma
      simp only [H, smul_eq_mul, norm_mul, norm_star, norm_inv]
      change ‖deriv Omega.boundaryParam t‖ *
          (‖d‖ * ‖Polynomial.eval (Omega.boundaryParam t) (q eta)‖ * ‖d‖⁻¹) ≤
        Q * ‖deriv Omega.boundaryParam t‖
      have hcancel :
          ‖d‖ * ‖Polynomial.eval (Omega.boundaryParam t) (q eta)‖ * ‖d‖⁻¹ =
            ‖Polynomial.eval (Omega.boundaryParam t) (q eta)‖ := by
        field_simp
      rw [hcancel]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hqbound
          (norm_nonneg (deriv Omega.boundaryParam t))
  have hHlim : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Ι (0 : ℝ) (2 * Real.pi) →
        Filter.Tendsto (fun eta => H eta t) l (nhds (H xi t)) := by
    filter_upwards [ae_boundaryParam_ne_of_mem_frontier Omega hxi] with t htne
    intro ht
    let sigma := Omega.boundaryParam t
    have hsigma : sigma ≠ xi := htne ht
    have hqcont : Continuous (fun eta : ℂ =>
        Polynomial.eval sigma (q eta)) := by
      exact (continuous_eval_divByMonic_X_sub_C p).comp
        (continuous_id.prodMk continuous_const)
    have hden : ContinuousAt (fun eta : ℂ => sigma - eta) xi := by
      fun_prop
    have hden0 : sigma - xi ≠ 0 := sub_ne_zero.mpr hsigma
    have hcont : ContinuousAt (fun eta => H eta t) xi := by
      change ContinuousAt (fun eta : ℂ =>
        deriv Omega.boundaryParam t •
          (star (sigma - eta) * star (Polynomial.eval sigma (q eta)) *
            (sigma - eta)⁻¹)) xi
      have hderiv : ContinuousAt
          (fun _ : ℂ => deriv Omega.boundaryParam t) xi := continuousAt_const
      exact hderiv.smul
        ((hden.star.mul hqcont.continuousAt.star).mul (hden.inv₀ hden0))
    have hl : l ≤ nhds xi := by
      dsimp only [l, nhdsWithin]
      exact inf_le_left
    exact hcont.tendsto.mono_left hl
  have hIntegral : Filter.Tendsto
      (fun eta => ∫ t in (0 : ℝ)..(2 * Real.pi), H eta t)
      l (nhds (∫ t in (0 : ℝ)..(2 * Real.pi), H xi t)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      bound hHmeas hHbound hboundInt hHlim
  have hscaled : Filter.Tendsto
      (fun eta => (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in (0 : ℝ)..(2 * Real.pi), H eta t)
      l (nhds ((2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in (0 : ℝ)..(2 * Real.pi), H xi t)) :=
    tendsto_const_nhds.mul hIntegral
  change Filter.Tendsto
    (fun eta =>
      crouzeixPolynomialScalarCompanionRegularized Omega p eta eta)
    l (nhds
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi))
  simpa only [l, q, H,
    crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic,
    contourIntegral] using hscaled

/-- The explicit Plemelj boundary value is continuous on the frontier. -/
theorem continuousOn_crouzeixPolynomialScalarCompanionBoundaryValue
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionBoundaryValue Omega p)
      (frontier Omega.carrier) := by
  intro xi hxi
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  exact (p.continuous.comp continuous_id).star.continuousWithinAt.add
    (continuousOn_crouzeixPolynomialScalarCompanionRegularized_self
      Omega p xi hxi)

/-- Combining joint decay of the radial error with continuity of the moving
self-value gives the full joint radial Plemelj limit. -/
theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_joint
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun x : ℝ × ℂ =>
        crouzeixPolynomialScalarCompanionRegularized Omega p x.2
          (smoothJordanInwardPoint c x.2 x.1))
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by
  let l : Filter (ℝ × ℂ) := nhdsWithin (0, xi)
    (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier)
  have herror :=
    tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_sub_self_joint
      Omega p hc hxi
  have hl : l ≤ nhds (0, xi) := by
    dsimp only [l, nhdsWithin]
    exact inf_le_left
  have hproj : Filter.Tendsto (fun x : ℝ × ℂ => x.2) l
      (nhdsWithin xi (frontier Omega.carrier)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only using continuous_snd.continuousAt.tendsto.mono_left hl
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact hx.2
  have hself : Filter.Tendsto
      (fun x : ℝ × ℂ =>
        crouzeixPolynomialScalarCompanionRegularized Omega p x.2 x.2)
      l
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) :=
    (continuousOn_crouzeixPolynomialScalarCompanionRegularized_self
      Omega p xi hxi).tendsto.comp hproj
  have hadd := herror.add hself
  simpa only [l, zero_add] using hadd.congr'
    (Filter.Eventually.of_forall fun x => by ring)

/-- With normalized winding kernel, the full companion has the corresponding
joint radial limit while its frontier endpoint moves. -/
theorem tendsto_crouzeixPolynomialScalarCompanion_inward_joint
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {c xi : ℂ} (hc : c ∈ Omega.carrier)
    (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun x : ℝ × ℂ =>
        crouzeixPolynomialScalarCompanion Omega p
          (smoothJordanInwardPoint c x.2 x.1))
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by
  let l : Filter (ℝ × ℂ) := nhdsWithin (0, xi)
    (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier)
  have hl : l ≤ nhds (0, xi) := by
    dsimp only [l, nhdsWithin]
    exact inf_le_left
  have heval : Filter.Tendsto
      (fun x : ℝ × ℂ => star (Polynomial.eval x.2 p)) l
      (nhds (star (Polynomial.eval xi p))) := by
    have hcont : Continuous (fun x : ℝ × ℂ =>
        star (Polynomial.eval x.2 p)) := by fun_prop
    exact hcont.continuousAt.tendsto.mono_left hl
  have hreg :=
    tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_joint
      Omega p hc hxi
  have hadd := heval.add hreg
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  apply hadd.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hz : smoothJordanInwardPoint c x.2 x.1 ∈ Omega.carrier :=
    smoothJordanInwardPoint_mem_carrier Omega hc hx.2 hx.1
  have hzfrontier : smoothJordanInwardPoint c x.2 x.1 ∉
      frontier Omega.carrier := by
    intro hzfrontier
    have hempty : smoothJordanInwardPoint c x.2 x.1 ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hzfrontier⟩
    exact hempty
  rw [crouzeixPolynomialScalarCompanion_eq_regularized_add Omega p x.2
    hzfrontier, hkernel _ hz, mul_one]
  exact add_comm _ _

/-- Any inward-coordinate chart whose radius and endpoint tend jointly to
`(0, xi)` transfers the joint radial theorem to the unrestricted interior
filter.  This isolates the remaining geometry needed for a full Plemelj
theorem from the completed analytic argument. -/
theorem tendsto_crouzeixPolynomialScalarCompanion_of_inward_coordinates
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {c xi : ℂ} (hc : c ∈ Omega.carrier)
    (hxi : xi ∈ frontier Omega.carrier)
    (radius : ℂ → ℝ) (endpoint : ℂ → ℂ)
    (hcoord : ∀ᶠ z in nhdsWithin xi Omega.carrier,
      smoothJordanInwardPoint c (endpoint z) (radius z) = z)
    (hparam : Filter.Tendsto (fun z => (radius z, endpoint z))
      (nhdsWithin xi Omega.carrier)
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))) :
    Filter.Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by
  have h :=
    (tendsto_crouzeixPolynomialScalarCompanion_inward_joint
      Omega p hkernel hc hxi).comp hparam
  apply h.congr'
  filter_upwards [hcoord] with z hz
  dsimp only [Function.comp_apply]
  rw [hz]

/-- The same inward-coordinate hypothesis supplies exactly the regularized
frontier convergence consumed by the canonical Plemelj extension API. -/
theorem
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_inward_coordinates
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {c xi : ℂ} (hc : c ∈ Omega.carrier)
    (hxi : xi ∈ frontier Omega.carrier)
    (radius : ℂ → ℝ) (endpoint : ℂ → ℂ)
    (hcoord : ∀ᶠ z in nhdsWithin xi Omega.carrier,
      smoothJordanInwardPoint c (endpoint z) (radius z) = z)
    (hparam : Filter.Tendsto (fun z => (radius z, endpoint z))
      (nhdsWithin xi Omega.carrier)
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))) :
    Filter.Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by
  have hfull :=
    tendsto_crouzeixPolynomialScalarCompanion_of_inward_coordinates
      Omega p hkernel hc hxi radius endpoint hcoord hparam
  have hsub := hfull.sub
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℂ => star (Polynomial.eval xi p))
      (nhdsWithin xi Omega.carrier)
      (nhds (star (Polynomial.eval xi p))))
  have htarget :
      crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi -
          star (Polynomial.eval xi p) =
        crouzeixPolynomialScalarCompanionRegularized Omega p xi xi := by
    unfold crouzeixPolynomialScalarCompanionBoundaryValue
    ring
  rw [htarget] at hsub
  apply hsub.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzfrontier : z ∉ frontier Omega.carrier := by
    intro hzfrontier
    have hempty : z ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hzfrontier⟩
    exact hempty
  rw [crouzeixPolynomialScalarCompanion_eq_regularized_add Omega p xi
    hzfrontier, hkernel z hz, mul_one]
  ring
/-- Inward coordinates may be chosen simultaneously for all carrier points.
For every frontier point, the chosen radius and endpoint tend to zero and
that frontier point respectively. -/
theorem exists_inward_coordinate_functions
    (Omega : SmoothJordanDomain)
    (hbounded : Bornology.IsBounded Omega.carrier)
    {c : ℂ} (hc : c ∈ Omega.carrier) :
    ∃ radius : ℂ → ℝ, ∃ endpoint : ℂ → ℂ,
      (∀ z ∈ Omega.carrier,
        radius z ∈ Ioc (0 : ℝ) 1 ∧
        endpoint z ∈ frontier Omega.carrier ∧
        smoothJordanInwardPoint c (endpoint z) (radius z) = z) ∧
      ∀ xi ∈ frontier Omega.carrier,
        Filter.Tendsto (fun z => (radius z, endpoint z))
          (nhdsWithin xi Omega.carrier)
          (nhdsWithin (0, xi)
            (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier)) := by
  have hex : ∀ z : ℂ, ∃ r : ℝ, ∃ eta : ℂ,
      z ∈ Omega.carrier →
        r ∈ Ioc (0 : ℝ) 1 ∧ eta ∈ frontier Omega.carrier ∧
          smoothJordanInwardPoint c eta r = z := by
    intro z
    by_cases hz : z ∈ Omega.carrier
    · obtain ⟨r, hr, eta, heta, heq⟩ :=
        exists_inward_coordinates Omega hbounded hc hz
      exact ⟨r, eta, fun _ => ⟨hr, heta, heq⟩⟩
    · exact ⟨1, Omega.boundaryParam 0, fun hz' => (hz hz').elim⟩
  choose radius endpoint hcoord using hex
  refine ⟨radius, endpoint, ?_, ?_⟩
  · intro z hz
    exact hcoord z hz
  · intro xi hxi
    let l : Filter ℂ := nhdsWithin xi Omega.carrier
    obtain ⟨delta, R, hdelta, _hR, hcross⟩ :=
      exists_uniform_inward_boundary_cross_bound Omega hc
    obtain ⟨delta', hdelta', hden⟩ :=
      exists_uniform_inward_boundary_denominator_bound Omega hc
    have hl : l ≤ nhds xi := by
      dsimp only [l, nhdsWithin]
      exact inf_le_left
    have hdist : Filter.Tendsto (fun z : ℂ => ‖xi - z‖ / delta') l
        (nhds 0) := by
      have hcont : ContinuousAt (fun z : ℂ => ‖xi - z‖ / delta') xi := by
        fun_prop
      simpa only [sub_self, norm_zero, zero_div] using
        hcont.tendsto.mono_left hl
    have hradius : Filter.Tendsto radius l (nhds 0) := by
      apply squeeze_zero'
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact (hcoord z hz).1.1.le
      · filter_upwards [self_mem_nhdsWithin] with z hz
        obtain ⟨hr, heta, heq⟩ := hcoord z hz
        apply (le_div_iff₀ hdelta').2
        simpa only [heq] using hden (endpoint z) heta (radius z) hr xi hxi
      · exact hdist
    have hendpointMajorant : Filter.Tendsto
        (fun z : ℂ => (R / delta + 1) * ‖xi - z‖) l (nhds 0) := by
      have hcont : Filter.Tendsto (fun z : ℂ => ‖xi - z‖) l (nhds 0) := by
        have hc' : ContinuousAt (fun z : ℂ => ‖xi - z‖) xi := by fun_prop
        simpa only [sub_self, norm_zero] using hc'.tendsto.mono_left hl
      simpa only [mul_zero] using tendsto_const_nhds.mul hcont
    have hendpointDist : Filter.Tendsto
        (fun z : ℂ => dist (endpoint z) xi) l (nhds 0) := by
      apply squeeze_zero'
        (g := fun z : ℂ => (R / delta + 1) * ‖xi - z‖)
      · exact Filter.Eventually.of_forall fun _ => dist_nonneg
      · filter_upwards [self_mem_nhdsWithin] with z hz
        obtain ⟨hr, heta, heq⟩ := hcoord z hz
        have hfirst : ‖endpoint z - z‖ ≤
            (R / delta) * ‖xi - z‖ := by
          calc
            ‖endpoint z - z‖ ≤ (R * ‖xi - z‖) / delta := by
              apply (le_div_iff₀ hdelta).2
              simpa only [heq, mul_comm, norm_sub_rev] using
                hcross (endpoint z) heta (radius z) hr xi hxi
            _ = (R / delta) * ‖xi - z‖ := by ring
        rw [dist_eq_norm]
        calc
          ‖endpoint z - xi‖ ≤ ‖endpoint z - z‖ + ‖z - xi‖ := by
            simpa only [dist_eq_norm] using dist_triangle (endpoint z) z xi
          _ ≤ (R / delta) * ‖xi - z‖ + ‖xi - z‖ := by
            gcongr
            exact (norm_sub_rev z xi).le
          _ = (R / delta + 1) * ‖xi - z‖ := by ring
      · exact hendpointMajorant
    have hendpoint : Filter.Tendsto endpoint l (nhds xi) :=
      tendsto_iff_dist_tendsto_zero.2 hendpointDist
    apply tendsto_nhdsWithin_iff.mpr
    have hpair : Filter.Tendsto (fun z => (radius z, endpoint z)) l
        (nhds (0, xi)) := by
      rw [nhds_prod_eq]
      exact hradius.prodMk hendpoint
    refine ⟨hpair, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact ⟨(hcoord z hz).1, (hcoord z hz).2.1⟩

/-- Winding normalization alone supplies a global inward-coordinate choice
with the correct limiting parameters at every frontier point. -/
theorem exists_inward_coordinate_functions_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain)
    (hkernel : ∀ w ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega w = 1)
    {c : ℂ} (hc : c ∈ Omega.carrier) :
    ∃ radius : ℂ → ℝ, ∃ endpoint : ℂ → ℂ,
      (∀ z ∈ Omega.carrier,
        radius z ∈ Ioc (0 : ℝ) 1 ∧
        endpoint z ∈ frontier Omega.carrier ∧
        smoothJordanInwardPoint c (endpoint z) (radius z) = z) ∧
      ∀ xi ∈ frontier Omega.carrier,
        Filter.Tendsto (fun z => (radius z, endpoint z))
          (nhdsWithin xi Omega.carrier)
          (nhdsWithin (0, xi)
            (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier)) := by
  exact exists_inward_coordinate_functions Omega
    (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel) hc

/-- On every bounded smooth Jordan carrier, the regularized scalar companion
has the full unrestricted interior Plemelj limit at each frontier point. -/
theorem
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by
  have hfrontier : Omega.boundaryParam 0 ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self 0
  have hcarrier : Omega.carrier.Nonempty :=
    Set.Nonempty.of_closure
      ⟨Omega.boundaryParam 0, frontier_subset_closure hfrontier⟩
  obtain ⟨c, hc⟩ := hcarrier
  obtain ⟨radius, endpoint, hcoord, hparam⟩ :=
    exists_inward_coordinate_functions Omega hbounded hc
  apply
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_inward_coordinates
      Omega p hkernel hc hxi radius endpoint
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hcoord z hz).2.2
  · exact hparam xi hxi

/-- Under winding normalization, the actual scalar companion converges from
the whole carrier to its explicit Plemelj boundary value. -/
theorem tendsto_crouzeixPolynomialScalarCompanion_of_isBounded
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by
  apply tendsto_crouzeixPolynomialScalarCompanion_of_regularized
    Omega p hkernel xi
  exact
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
      Omega p hbounded hkernel hxi

/-- Winding normalization alone forces boundedness and hence supplies the
unrestricted regularized Plemelj limit. -/
theorem
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by
  exact
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
      Omega p
        (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hxi

/-- Winding normalization alone gives the unrestricted full Plemelj limit
from the carrier. -/
theorem tendsto_crouzeixPolynomialScalarCompanion_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by
  exact
    tendsto_crouzeixPolynomialScalarCompanion_of_isBounded
      Omega p
        (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hxi

/-- Winding normalization alone makes the canonical scalar-companion
extension continuous on the closure. -/
theorem
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      (closure Omega.carrier) := by
  apply
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
      Omega p hkernel
  intro xi hxi
  exact
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_cauchyKernel_eq_one
      Omega p hkernel hxi

/-- Under winding normalization alone, the canonical closed extension takes
the explicit Plemelj value on the frontier. -/
theorem
    crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p xi =
      crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by
  apply
    crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
      Omega p hkernel
  · intro eta heta
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_cauchyKernel_eq_one
        Omega p hkernel heta
  · exact hxi

/-- On a bounded smooth Jordan carrier, winding normalization makes the
canonical scalar-companion extension continuous on the closure. -/
theorem
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      (closure Omega.carrier) := by
  apply
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
      Omega p hkernel
  intro xi hxi
  exact
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
      Omega p hbounded hkernel hxi

/-- On a bounded smooth Jordan carrier, the canonical closed extension takes
the explicit Plemelj boundary value at every frontier point. -/
theorem
    crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_isBounded
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p xi =
      crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by
  apply
    crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
      Omega p hkernel
  · intro eta heta
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega p hbounded hkernel heta
  · exact hxi

/-- On a bounded normalized smooth Jordan carrier, the canonical closed
scalar companion preserves polynomial addition throughout the closure. -/
theorem
    crouzeixPolynomialScalarCompanionClosedExtension_add_of_isBounded
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (p + q) z =
      crouzeixPolynomialScalarCompanionClosedExtension Omega p z +
        crouzeixPolynomialScalarCompanionClosedExtension Omega q z := by
  apply
    crouzeixPolynomialScalarCompanionClosedExtension_add_of_regularized
      Omega p q hkernel
  · intro xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega p hbounded hkernel hxi
  · intro xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega q hbounded hkernel hxi
  · exact hz

/-- On a bounded normalized smooth Jordan carrier, the canonical closed
scalar companion is conjugate-homogeneous throughout the closure. -/
theorem
    crouzeixPolynomialScalarCompanionClosedExtension_smul_of_isBounded
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanionClosedExtension Omega p z := by
  apply
    crouzeixPolynomialScalarCompanionClosedExtension_smul_of_regularized
      Omega a p hkernel
  · intro xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega p hbounded hkernel hxi
  · exact hz

/-- A uniform bound for the explicit Plemelj boundary values controls the
scalar companion throughout every bounded normalized carrier. -/
theorem
    norm_crouzeixPolynomialScalarCompanion_le_of_isBounded_boundary
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {C : ℝ}
    (hC : ∀ xi ∈ frontier Omega.carrier,
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by
  apply norm_crouzeixPolynomialScalarCompanion_le_of_regularized_boundary
    Omega p hbounded hkernel
  · intro xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega p hbounded hkernel hxi
  · exact hC
  · exact hz

/-- Winding normalization alone makes the canonical closed companion
additive on the closure. -/
theorem
    crouzeixPolynomialScalarCompanionClosedExtension_add_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (p + q) z =
      crouzeixPolynomialScalarCompanionClosedExtension Omega p z +
        crouzeixPolynomialScalarCompanionClosedExtension Omega q z := by
  exact
    crouzeixPolynomialScalarCompanionClosedExtension_add_of_isBounded
      Omega p q (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hz

/-- Winding normalization alone makes the canonical closed companion
conjugate-homogeneous on the closure. -/
theorem
    crouzeixPolynomialScalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanionClosedExtension Omega p z := by
  exact
    crouzeixPolynomialScalarCompanionClosedExtension_smul_of_isBounded
      Omega a p (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hz

/-- Under winding normalization alone, a uniform Plemelj boundary bound
controls the scalar companion throughout the carrier. -/
theorem
    norm_crouzeixPolynomialScalarCompanion_le_of_boundary_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {C : ℝ}
    (hC : ∀ xi ∈ frontier Omega.carrier,
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by
  exact
    norm_crouzeixPolynomialScalarCompanion_le_of_isBounded_boundary
      Omega p (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hC hz

/-- On a bounded normalized carrier, the sharp boundary-phase inequality
immediately controls the scalar companion in the interior. -/
theorem
    norm_crouzeixPolynomialScalarCompanion_le_of_boundaryPhaseTransform_radial
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  have hbounded :=
    Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel
  apply norm_crouzeixPolynomialScalarCompanion_le_of_boundaryPhaseTransform
    Omega p hbounded hkernel
  · intro xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega p hbounded hkernel hxi
  · exact hphase
  · exact hz

/-- The same sharp boundary-phase inequality controls the canonical closed
extension on the entire closure of a bounded normalized carrier. -/
theorem
    norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform_radial
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  have hbounded :=
    Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel
  apply
    norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform
      Omega p hbounded hkernel
  · intro xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega p hbounded hkernel hxi
  · exact hphase
  · exact hz

/-- Constant polynomials give the conjugate constant throughout the
canonical closed extension of a bounded normalized carrier. -/
theorem
    crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded
    (Omega : SmoothJordanDomain) (a : ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension
        Omega (Polynomial.C a) z = star a := by
  rw [closure_eq_self_union_frontier] at hz
  rcases hz with hz | hz
  · rw [crouzeixPolynomialScalarCompanionClosedExtension_eq Omega _ hz]
    have hzfrontier : z ∉ frontier Omega.carrier := by
      intro hfrontier
      have hempty : z ∈ (∅ : Set ℂ) := by
        rw [← Omega.isOpen_carrier.inter_frontier_eq]
        exact ⟨hz, hfrontier⟩
      exact hempty
    have hshift := crouzeixPolynomialScalarCompanion_add_C
      Omega 0 a hzfrontier
    simpa only [zero_add, crouzeixPolynomialScalarCompanion_zero,
      hkernel z hz, mul_one, add_zero] using hshift
  · rw [
      crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_isBounded
        Omega (Polynomial.C a) hbounded hkernel hz]
    have hshift :=
      crouzeixPolynomialScalarCompanionBoundaryValue_add_C Omega 0 a z
    simpa only [zero_add,
      crouzeixPolynomialScalarCompanionBoundaryValue_zero, add_zero] using
      hshift

/-- Adding a constant polynomial shifts the canonical closed companion by
the conjugate constant throughout a bounded normalized closure. -/
theorem
    crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension
        Omega (p + Polynomial.C a) z =
      crouzeixPolynomialScalarCompanionClosedExtension Omega p z + star a := by
  rw [
    crouzeixPolynomialScalarCompanionClosedExtension_add_of_isBounded
      Omega p (Polynomial.C a) hbounded hkernel hz,
    crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded
      Omega a hbounded hkernel hz]

/-- The canonical closed companion obeys the full conjugate-affine law under
winding normalization. -/
theorem
    crouzeixPolynomialScalarCompanionClosedExtension_affine_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (a b : ℂ) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension
        Omega (a • p + Polynomial.C b) z =
      star a * crouzeixPolynomialScalarCompanionClosedExtension Omega p z +
        star b := by
  rw [
    crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded
      Omega (a • p) b
        (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel) hkernel hz,
    crouzeixPolynomialScalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
      Omega a p hkernel hz]

/-- Shifting an approximating polynomial by the conjugate constant preserves
the approximation error for the correspondingly shifted closed companion. -/
theorem
    norm_eval_add_C_star_sub_scalarCompanionClosedExtension_add_C
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (a : ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖Polynomial.eval z (q + Polynomial.C (star a)) -
        crouzeixPolynomialScalarCompanionClosedExtension
          Omega (p + Polynomial.C a) z‖ =
      ‖Polynomial.eval z q -
        crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ := by
  rw [Polynomial.eval_add, Polynomial.eval_C,
    crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded
      Omega p a hbounded hkernel hz]
  congr 1
  ring

/-- Any uniform polynomial approximation of a canonical companion transfers,
with exactly the same error, after adding a constant to the source
polynomial. -/
theorem
    exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (S : Set ℂ) (hS : S ⊆ closure Omega.carrier) (epsilon : ℕ → ℝ)
    (happrox : ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ S →
        ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
          epsilon j) :
    ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ S →
        ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              Omega (p + Polynomial.C a) z‖ ≤
          epsilon j := by
  obtain ⟨r, hr⟩ := happrox
  refine ⟨fun j => r j + Polynomial.C (star a), ?_⟩
  intro j z hz
  rw [norm_eval_add_C_star_sub_scalarCompanionClosedExtension_add_C
    Omega p (r j) a
      (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
      hkernel (hS hz)]
  exact hr j z hz

/-- Conjugate-scaling an approximating polynomial scales the closed-companion
approximation error by exactly the norm of the source scalar. -/
theorem
    norm_eval_star_smul_sub_scalarCompanionClosedExtension_smul
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖Polynomial.eval z ((star a) • q) -
        crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z‖ =
      ‖a‖ *
        ‖Polynomial.eval z q -
          crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ := by
  rw [Polynomial.eval_smul, smul_eq_mul,
    crouzeixPolynomialScalarCompanionClosedExtension_smul_of_isBounded
      Omega a p (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hz,
    ← mul_sub, norm_mul, norm_star]

/-- Consequently, a uniform approximation transfers under polynomial scaling
with the expected multiplicative error. -/
theorem
    exists_polynomial_approximation_scalarCompanionClosedExtension_smul
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (S : Set ℂ) (hS : S ⊆ closure Omega.carrier) (epsilon : ℕ → ℝ)
    (happrox : ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ S →
        ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
          epsilon j) :
    ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ S →
        ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              Omega (a • p) z‖ ≤
          ‖a‖ * epsilon j := by
  obtain ⟨r, hr⟩ := happrox
  refine ⟨fun j => (star a) • r j, ?_⟩
  intro j z hz
  rw [norm_eval_star_smul_sub_scalarCompanionClosedExtension_smul
    Omega p (r j) a hkernel (hS hz)]
  exact mul_le_mul_of_nonneg_left (hr j z hz) (norm_nonneg a)

/-- Uniform approximation is therefore stable under the full conjugate-affine
action on canonical companions. -/
theorem
    exists_polynomial_approximation_scalarCompanionClosedExtension_affine
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a b : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (S : Set ℂ) (hS : S ⊆ closure Omega.carrier) (epsilon : ℕ → ℝ)
    (happrox : ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ S →
        ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
          epsilon j) :
    ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ S →
        ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              Omega (a • p + Polynomial.C b) z‖ ≤
          ‖a‖ * epsilon j := by
  have hscaled :=
    exists_polynomial_approximation_scalarCompanionClosedExtension_smul
      Omega p a hkernel S hS epsilon happrox
  exact
    exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
      Omega (a • p) b hkernel S hS (fun j => ‖a‖ * epsilon j) hscaled

/-- The preceding affine transfer has an exact pointwise error identity. -/
theorem
    norm_eval_star_smul_add_C_star_sub_scalarCompanionClosedExtension_affine
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (a b : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖Polynomial.eval z ((star a) • q + Polynomial.C (star b)) -
        crouzeixPolynomialScalarCompanionClosedExtension
          Omega (a • p + Polynomial.C b) z‖ =
      ‖a‖ *
        ‖Polynomial.eval z q -
          crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ := by
  rw [norm_eval_add_C_star_sub_scalarCompanionClosedExtension_add_C
      Omega (a • p) ((star a) • q) b
        (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel) hkernel hz,
    norm_eval_star_smul_sub_scalarCompanionClosedExtension_smul
      Omega p q a hkernel hz]

/-- For a constant polynomial, the canonical closed companion has exactly
the conjugate-polynomial auxiliary contour; no extra Plemelj identity is
needed. -/
theorem
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_isBounded
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (a : ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (Polynomial.C a)) =
      crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a) := by
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have hfrontier : Omega.boundaryParam t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  change deriv Omega.boundaryParam t •
      (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (Polynomial.C a) (Omega.boundaryParam t) •
        resolvent A (Omega.boundaryParam t)) =
    deriv Omega.boundaryParam t •
      (star (Polynomial.eval (Omega.boundaryParam t) (Polynomial.C a)) •
        resolvent A (Omega.boundaryParam t))
  rw [
    crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded
      Omega a hbounded hkernel (frontier_subset_closure hfrontier)]
  simp only [Polynomial.eval_C]

/-- Winding normalization alone makes the canonical closed companion of a
constant polynomial equal to the conjugate constant. -/
theorem
    crouzeixPolynomialScalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension
        Omega (Polynomial.C a) z = star a := by
  exact
    crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded
      Omega a (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hz

/-- Consequently, the auxiliary contour of a constant canonical companion is
automatic under winding normalization alone. -/
theorem
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (Polynomial.C a)) =
      crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a) := by
  exact
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_isBounded
      A Omega a (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
