/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Affine homotopy invariance of the resolvent contour mass

The contour integral of the operator resolvent is constant along a commuting
affine operator path as long as the contour stays in the resolvent set.  For
the path from a scalar operator `c • 1` to `A`, convexity of the carrier and
the spectral inclusion `spectrum A ⊆ closure (numericalRange A)` provide that
resolvent-set condition.  Oriented scalar winding then computes the common
mass as `2 * pi * I • 1`.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCauchyKernelWinding
import LeanPool.OperatorTheory.Operator.SpectralSet.SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem hasDerivAt_resolvent_affineOperator
    (B D : E →L[ℂ] E) (s z : ℂ)
    (hres : z ∈ resolventSet ℂ (B + s • D)) :
    HasDerivAt (fun w : ℂ => resolvent (B + w • D) z)
      (resolvent (B + s • D) z * D * resolvent (B + s • D) z) s := by
  have hpath : HasDerivAt (fun w : ℂ => B + w • D) D s := by
    convert!
      (hasDerivAt_const s B).add ((hasDerivAt_id s).smul_const D) using 1
    simp only [zero_add, one_smul]
  simpa only [Function.comp_apply, ContinuousLinearMap.mulLeftRight_apply] using!
    (spectrum.hasFDerivAt_resolvent hres).comp_hasDerivAt s hpath

theorem hasDerivAt_contourIntegral_resolvent_affineOperator
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain) (s : ℂ)
    {epsilon C : ℝ} (hepsilon : 0 < epsilon) (hC : 0 ≤ C)
    (hres : ∀ w ∈ ball s epsilon, ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + w • D))
    (hbound : ∀ w ∈ ball s epsilon, ∀ t : ℝ,
      ‖resolvent (B + w • D) (Omega.boundaryParam t)‖ ≤ C) :
    HasDerivAt
      (fun w : ℂ =>
        contourIntegral (resolvent (B + w • D)) Omega.boundaryParam)
      (contourIntegral
        (fun z : ℂ =>
          resolvent (B + s • D) z * D * resolvent (B + s • D) z)
        Omega.boundaryParam) s := by
  let F : ℂ → ℝ → (E →L[ℂ] E) := fun w t =>
    deriv Omega.boundaryParam t •
      resolvent (B + w • D) (Omega.boundaryParam t)
  let F' : ℂ → ℝ → (E →L[ℂ] E) := fun w t =>
    deriv Omega.boundaryParam t •
      (resolvent (B + w • D) (Omega.boundaryParam t) * D *
        resolvent (B + w • D) (Omega.boundaryParam t))
  let bound : ℝ → ℝ := fun t =>
    ‖deriv Omega.boundaryParam t‖ * (C * ‖D‖ * C)
  have hFcont : ∀ w ∈ ball s epsilon, Continuous (F w) := by
    intro w hw
    have hRcont : Continuous
        (fun t => resolvent (B + w • D) (Omega.boundaryParam t)) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (spectrum.hasDerivAt_resolvent_const_left
        (hres w hw t)).continuousAt.comp_of_eq
          (Omega.boundaryParam_contDiff.continuous.continuousAt) rfl
    exact (Omega.boundaryParam_contDiff.continuous_deriv
      (by norm_num)).smul hRcont
  have hF'cont : ∀ w ∈ ball s epsilon, Continuous (F' w) := by
    intro w hw
    have hRcont : Continuous
        (fun t => resolvent (B + w • D) (Omega.boundaryParam t)) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (spectrum.hasDerivAt_resolvent_const_left
        (hres w hw t)).continuousAt.comp_of_eq
          (Omega.boundaryParam_contDiff.continuous.continuousAt) rfl
    exact (Omega.boundaryParam_contDiff.continuous_deriv
      (by norm_num)).smul ((hRcont.mul continuous_const).mul hRcont)
  have hboundInt : IntervalIntegrable bound volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact (Omega.boundaryParam_contDiff.continuous_deriv
      (by norm_num)).norm.mul continuous_const
  have hFmeas : ∀ᶠ w in nhds s,
      AEStronglyMeasurable (F w) (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [ball_mem_nhds s hepsilon] with w hw
    exact (hFcont w hw).aestronglyMeasurable.restrict
  have hFint : IntervalIntegrable (F s) volume 0 (2 * Real.pi) :=
    (hFcont s (mem_ball_self hepsilon)).intervalIntegrable 0 (2 * Real.pi)
  have hF'meas : AEStronglyMeasurable (F' s)
      (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) :=
    (hF'cont s (mem_ball_self hepsilon)).aestronglyMeasurable.restrict
  have hderiv : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ ball s epsilon, HasDerivAt (fun x => F x t) (F' w t) w := by
    filter_upwards [] with t _ w hw
    exact (hasDerivAt_resolvent_affineOperator B D w
      (Omega.boundaryParam t) (hres w hw t)).const_smul
        (deriv Omega.boundaryParam t)
  have hnorm : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ ball s epsilon, ‖F' w t‖ ≤ bound t := by
    filter_upwards [] with t _ w hw
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      ‖resolvent (B + w • D) (Omega.boundaryParam t) * D *
          resolvent (B + w • D) (Omega.boundaryParam t)‖ ≤
          ‖resolvent (B + w • D) (Omega.boundaryParam t)‖ * ‖D‖ *
            ‖resolvent (B + w • D) (Omega.boundaryParam t)‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ C * ‖D‖ * C := by
        gcongr
        · exact hbound w hw t
        · exact hbound w hw t
  obtain ⟨_, hdiff⟩ :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := ball s epsilon) (bound := bound) (ball_mem_nhds s hepsilon)
      hFmeas hFint hF'meas hnorm hboundInt hderiv
  simpa only [contourIntegral, F, F'] using hdiff

theorem exists_resolvent_affineOperator_neighborhood_bound
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain) (s : ℂ)
    (hres : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + s • D)) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ 0 ≤ C ∧
      ∀ w ∈ ball s epsilon, ∀ t : ℝ,
        Omega.boundaryParam t ∈ resolventSet ℂ (B + w • D) ∧
          ‖resolvent (B + w • D) (Omega.boundaryParam t)‖ ≤ C := by
  let base : ℂ × ℝ → (E →L[ℂ] E) := fun p =>
    Omega.boundaryParam p.2 • (1 : E →L[ℂ] E) - (B + p.1 • D)
  let N : Set (ℂ × ℝ) := {p | IsUnit (base p)}
  have hbasecont : Continuous base := by
    dsimp only [base]
    exact
      ((Omega.boundaryParam_contDiff.continuous.comp continuous_snd).smul
        continuous_const).sub
        (continuous_const.add (continuous_fst.smul continuous_const))
  have hNopen : IsOpen N := by
    exact Units.isOpen.preimage hbasecont
  have hprodSubset : ({s} : Set ℂ) ×ˢ Icc (0 : ℝ) (2 * Real.pi) ⊆ N := by
    rintro ⟨w, t⟩ ⟨hw, _⟩
    simp only [mem_singleton_iff] at hw
    subst w
    exact (mem_resolventSet_iff.mp (hres t))
  obtain ⟨U, V, hUopen, _hVopen, hsU, hIV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hNopen hprodSubset
  obtain ⟨delta, hdelta, hballU⟩ :=
    (Metric.isOpen_iff.mp hUopen) s (hsU (mem_singleton s))
  let epsilon : ℝ := delta / 2
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  let K : Set (ℂ × ℝ) :=
    closedBall s epsilon ×ˢ Icc (0 : ℝ) (2 * Real.pi)
  have hKcompact : IsCompact K :=
    IsCompact.prod (isCompact_closedBall s epsilon) isCompact_Icc
  have hKsubset : K ⊆ N := by
    rintro ⟨w, t⟩ ⟨hw, ht⟩
    apply hUV
    constructor
    · apply hballU
      change w ∈ closedBall s epsilon at hw
      change w ∈ ball s delta
      rw [mem_closedBall] at hw
      rw [mem_ball]
      dsimp only [epsilon] at hw
      linarith
    · exact hIV ht
  let Rfun : ℂ × ℝ → (E →L[ℂ] E) := fun p =>
    resolvent (B + p.1 • D) (Omega.boundaryParam p.2)
  have hRcont : ContinuousOn Rfun K := by
    intro p hp
    have hpN : p ∈ N := hKsubset hp
    have hunit : IsUnit (base p) := hpN
    have hinv := (NormedRing.inverse_continuousAt hunit.unit).comp_of_eq
      hbasecont.continuousAt rfl
    exact hinv.continuousWithinAt
  have himage : IsCompact (Rfun '' K) :=
    hKcompact.image_of_continuousOn hRcont
  obtain ⟨C, hCbound⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : E →L[ℂ] E)).mp
      himage.isBounded
  have hzeroIcc : (0 : ℝ) ∈ Icc (0 : ℝ) (2 * Real.pi) :=
    ⟨le_rfl, Real.two_pi_pos.le⟩
  have hsK : (s, (0 : ℝ)) ∈ K := by
    exact ⟨mem_closedBall_self hepsilon.le, hzeroIcc⟩
  have hCnonneg : 0 ≤ C := by
    have hmem := hCbound ⟨(s, 0), hsK, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hmem
    exact (norm_nonneg _).trans hmem
  refine ⟨epsilon, C, hepsilon, hCnonneg, ?_⟩
  intro w hw t
  obtain ⟨u, hu, htu⟩ :=
    Omega.boundaryParam_periodic.exists_mem_Ico₀ Real.two_pi_pos t
  have huIcc : u ∈ Icc (0 : ℝ) (2 * Real.pi) := ⟨hu.1, hu.2.le⟩
  have hwclosed : w ∈ closedBall s epsilon :=
    ball_subset_closedBall hw
  have hwuK : (w, u) ∈ K := ⟨hwclosed, huIcc⟩
  have hwuN : (w, u) ∈ N := hKsubset hwuK
  constructor
  · rw [htu]
    exact mem_resolventSet_iff.mpr hwuN
  · have hmem := hCbound ⟨(w, u), hwuK, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hmem
    rw [htu]
    exact hmem

theorem hasDerivAt_contourIntegral_resolvent_affineOperator_of_boundary_subset_resolventSet
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain) (s : ℂ)
    (hres : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + s • D)) :
    HasDerivAt
      (fun w : ℂ =>
        contourIntegral (resolvent (B + w • D)) Omega.boundaryParam)
      (contourIntegral
        (fun z : ℂ =>
          resolvent (B + s • D) z * D * resolvent (B + s • D) z)
        Omega.boundaryParam) s := by
  obtain ⟨epsilon, C, hepsilon, hC, hlocal⟩ :=
    exists_resolvent_affineOperator_neighborhood_bound
      B D Omega s hres
  apply hasDerivAt_contourIntegral_resolvent_affineOperator
    B D Omega s hepsilon hC
  · exact fun w hw t => (hlocal w hw t).1
  · exact fun w hw t => (hlocal w hw t).2

omit [CompleteSpace E] in
theorem commute_resolvent_of_commute
    (B D : E →L[ℂ] E) (z : ℂ) (hDB : Commute D B)
    (hres : z ∈ resolventSet ℂ B) :
    Commute D (resolvent B z) := by
  rw [spectrum.resolvent_eq hres]
  apply Commute.units_inv_right
  rw [hres.unit_spec]
  exact (Algebra.commute_algebraMap_right z D).sub_right hDB

theorem contourIntegral_const_mul_resolvent_sq_eq_zero
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hres : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ B) :
    contourIntegral (fun z : ℂ => D * resolvent B z ^ 2)
      Omega.boundaryParam = 0 := by
  have hint : ContourIntegrable
      (fun z : ℂ => D * resolvent B z ^ 2) Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · intro z hz
      obtain ⟨t, _, rfl⟩ := hz
      exact (continuousAt_const.mul
        ((spectrum.hasDerivAt_resolvent_const_left
          (hres t)).continuousAt.pow 2)).continuousWithinAt
  apply contourIntegral_eq_zero_of_hasDerivAt_of_closed
    (Fp := fun z : ℂ => -(D * resolvent B z))
  · intro _ _
    exact
      (Omega.boundaryParam_contDiff.differentiable (by norm_num)).differentiableAt
  · intro t _
    have hder :=
      ((spectrum.hasDerivAt_resolvent_const_left (hres t)).const_mul D).neg
    convert hder using 1
    · rfl
    · simp only [mul_neg, neg_neg]
  · exact hint
  · simpa only [zero_add] using Omega.boundaryParam_periodic 0

theorem contourIntegral_const_mul_resolvent_sq_eq_zero_of_numericalRange
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange B) ⊆ Omega.carrier) :
    contourIntegral (fun z : ℂ => D * resolvent B z ^ 2)
      Omega.boundaryParam = 0 := by
  apply contourIntegral_const_mul_resolvent_sq_eq_zero
  intro t
  rw [mem_resolventSet_iff, ← spectrum.notMem_iff]
  intro hspectrum
  have hcarrier : Omega.boundaryParam t ∈ Omega.carrier :=
    hOmega (spectrum_subset_closure_numericalRange B hspectrum)
  have hfrontier : Omega.boundaryParam t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hempty : Omega.boundaryParam t ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hcarrier, hfrontier⟩
  exact hempty

theorem hasDerivAt_contourIntegral_resolvent_affineOperator_eq_zero
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain) (s : ℂ)
    (hBD : Commute B D)
    (hres : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + s • D)) :
    HasDerivAt
      (fun w : ℂ =>
        contourIntegral (resolvent (B + w • D)) Omega.boundaryParam)
      0 s := by
  have hraw :=
    hasDerivAt_contourIntegral_resolvent_affineOperator_of_boundary_subset_resolventSet
      B D Omega s hres
  convert hraw using 1
  have hzero := contourIntegral_const_mul_resolvent_sq_eq_zero
    (B + s • D) D Omega hres
  rw [← hzero]
  simp only [contourIntegral]
  apply intervalIntegral.integral_congr
  intro t _ht
  apply congrArg (fun R : E →L[ℂ] E => deriv Omega.boundaryParam t • R)
  let R := resolvent (B + s • D) (Omega.boundaryParam t)
  have hDBs : Commute D (B + s • D) :=
    hBD.symm.add_right ((Commute.refl D).smul_right s)
  have hcomm : Commute D R :=
    commute_resolvent_of_commute (B + s • D) D
      (Omega.boundaryParam t) hDBs (hres t)
  simpa only [R, pow_two, mul_assoc] using
    congrArg (fun X : E →L[ℂ] E => X * R) hcomm.eq

theorem contourIntegral_resolvent_affineOperator_eq_of_boundary_subset_resolventSet
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hBD : Commute B D)
    (hres : ∀ r ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      Omega.boundaryParam t ∈
        resolventSet ℂ (B + (r : ℂ) • D)) :
    contourIntegral (resolvent (B + D)) Omega.boundaryParam =
      contourIntegral (resolvent B) Omega.boundaryParam := by
  let M : ℝ → (E →L[ℂ] E) := fun r =>
    contourIntegral (resolvent (B + (r : ℂ) • D)) Omega.boundaryParam
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt M 0 r := by
    intro r hr
    rw [uIcc_of_le zero_le_one] at hr
    simpa only [M, Function.comp_apply, Complex.ofRealCLM_apply, smul_zero] using!
      (hasDerivAt_contourIntegral_resolvent_affineOperator_eq_zero
        B D Omega (r : ℂ) hBD (hres r hr)).scomp r
          Complex.ofRealCLM.hasDerivAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := M) (f' := fun _ : ℝ => (0 : E →L[ℂ] E)) hderiv
    (continuous_const.intervalIntegrable (0 : ℝ) 1)
  have hM : M 1 = M 0 := by
    rw [intervalIntegral.integral_zero] at hftc
    exact sub_eq_zero.mp hftc.symm
  simpa only [M, Complex.ofReal_one, one_smul, Complex.ofReal_zero,
    zero_smul, add_zero] using hM

theorem spectrum_affine_smul_one_subset_convex_carrier
    [Nontrivial E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    spectrum ℂ (c • (1 : E →L[ℂ] E) +
      (r : ℂ) • (A - c • (1 : E →L[ℂ] E))) ⊆ Omega.carrier := by
  have hop : c • (1 : E →L[ℂ] E) +
      (r : ℂ) • (A - c • (1 : E →L[ℂ] E)) =
      (((1 - r : ℝ) : ℂ) * c) • (1 : E →L[ℂ] E) + (r : ℂ) • A := by
    ext x
    simp only [add_apply, smul_apply, sub_apply, one_apply_eq_self]
    module
  have hspec : spectrum ℂ (c • (1 : E →L[ℂ] E) +
      (r : ℂ) • (A - c • (1 : E →L[ℂ] E))) =
      {(((1 - r : ℝ) : ℂ) * c)} + (r : ℂ) • spectrum ℂ A := by
    rw [hop, ← Algebra.algebraMap_eq_smul_one,
      ← spectrum.singleton_add_eq,
      spectrum.smul_eq_smul (r : ℂ) A (spectrum.nonempty A)]
  rw [hspec]
  rintro z ⟨a, ha, b, hb, rfl⟩
  rw [mem_singleton_iff] at ha
  subst a
  obtain ⟨lambda, hlambda, rfl⟩ := hb
  have hlambdaCarrier : lambda ∈ Omega.carrier :=
    hOmega (spectrum_subset_closure_numericalRange A hlambda)
  convert Omega.strictConvex_carrier.convex hc hlambdaCarrier
    (sub_nonneg.mpr hr.2) hr.1 (by ring) using 1
  apply Complex.ext <;>
    simp only [ofReal_sub, ofReal_one, smul_eq_mul, add_re, add_im, mul_re,
      mul_im, sub_re, one_re, ofReal_re, sub_im, one_im, ofReal_im,
      sub_self, zero_mul, sub_zero, add_zero, real_smul]

theorem contourIntegral_resolvent_eq_scalar_of_convex_carrier
    [Nontrivial E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    contourIntegral (resolvent A) Omega.boundaryParam =
      contourIntegral (resolvent (c • (1 : E →L[ℂ] E)))
        Omega.boundaryParam := by
  let B : E →L[ℂ] E := c • 1
  let D : E →L[ℂ] E := A - c • 1
  have hBD : Commute B D := by
    dsimp only [B, D]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      Algebra.commute_algebraMap_left c (A - c • (1 : E →L[ℂ] E))
  have hres : ∀ r ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + (r : ℂ) • D) := by
    intro r hr t
    rw [mem_resolventSet_iff, ← spectrum.notMem_iff]
    intro hspectrum
    have hcarrier : Omega.boundaryParam t ∈ Omega.carrier :=
      spectrum_affine_smul_one_subset_convex_carrier
        A Omega c hc hOmega r hr hspectrum
    have hfrontier : Omega.boundaryParam t ∈ frontier Omega.carrier := by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self t
    have hempty : Omega.boundaryParam t ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hcarrier, hfrontier⟩
    exact hempty
  have hhom :=
    contourIntegral_resolvent_affineOperator_eq_of_boundary_subset_resolventSet
      B D Omega hBD hres
  have hsum : B + D = A := by
    dsimp only [B, D]
    abel
  simpa only [hsum, B] using hhom

omit [CompleteSpace E] in
theorem resolvent_smul_one_eq_inv_smul_one
    [Nontrivial E] (c z : ℂ) (hz : z ≠ c) :
    resolvent (c • (1 : E →L[ℂ] E)) z =
      (z - c)⁻¹ • (1 : E →L[ℂ] E) := by
  have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz
  have hunit : IsUnit ((z - c) • (1 : E →L[ℂ] E)) :=
    IsUnit.smul (Units.mk0 (z - c) hzc) isUnit_one
  unfold resolvent
  rw [Algebra.algebraMap_eq_smul_one, ← sub_smul]
  rw [← mul_one (Ring.inverse ((z - c) • (1 : E →L[ℂ] E)))]
  apply (Ring.inverse_mul_eq_iff_eq_mul
    ((z - c) • (1 : E →L[ℂ] E)) 1
    ((z - c)⁻¹ • (1 : E →L[ℂ] E)) hunit).2
  rw [smul_mul_smul_comm, mul_inv_cancel₀ hzc, one_smul, one_mul]

theorem contourIntegral_resolvent_smul_one_eq_scalar
    [Nontrivial E] (Omega : SmoothJordanDomain) (c : ℂ)
    (hc : c ∈ Omega.carrier) :
    contourIntegral (resolvent (c • (1 : E →L[ℂ] E)))
        Omega.boundaryParam =
      contourIntegral (fun z : ℂ => (z - c)⁻¹) Omega.boundaryParam •
        (1 : E →L[ℂ] E) := by
  have hne : ∀ t : ℝ, Omega.boundaryParam t ≠ c := by
    intro t heq
    have hfrontier : c ∈ frontier Omega.carrier := by
      rw [← heq, ← Omega.boundaryParam_range]
      exact mem_range_self t
    have hempty : c ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hc, hfrontier⟩
    exact hempty
  unfold contourIntegral
  have hfun :
      (fun t : ℝ => deriv Omega.boundaryParam t •
        resolvent (c • (1 : E →L[ℂ] E)) (Omega.boundaryParam t)) =
      fun t : ℝ =>
        (deriv Omega.boundaryParam t *
          (Omega.boundaryParam t - c)⁻¹) • (1 : E →L[ℂ] E) := by
    funext t
    rw [resolvent_smul_one_eq_inv_smul_one c
      (Omega.boundaryParam t) (hne t), smul_smul]
  rw [hfun, intervalIntegral.integral_smul_const]
  rfl

theorem contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier_of_nontrivial
    [Nontrivial E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  rw [contourIntegral_resolvent_eq_scalar_of_convex_carrier
    A Omega c hc hOmega,
    contourIntegral_resolvent_smul_one_eq_scalar Omega c hc]
  have hkernel :=
    crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier_point
      Omega c hc hcside
  unfold crouzeixScalarCauchyKernel at hkernel
  let q : ℂ := 2 * (Real.pi : ℂ) * I
  have hq : q ≠ 0 := by
    dsimp only [q]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hkernel' : q⁻¹ * contourIntegral (fun z : ℂ => (z - c)⁻¹)
      Omega.boundaryParam = 1 := by
    simpa only [q] using hkernel
  have hscaled := congrArg (fun z : ℂ => q * z) hkernel'
  have hscalar : contourIntegral (fun z : ℂ => (z - c)⁻¹)
      Omega.boundaryParam = q := by
    calc
      contourIntegral (fun z : ℂ => (z - c)⁻¹) Omega.boundaryParam =
          (q * q⁻¹) * contourIntegral (fun z : ℂ => (z - c)⁻¹)
            Omega.boundaryParam := by rw [mul_inv_cancel₀ hq, one_mul]
      _ = q * (q⁻¹ * contourIntegral (fun z : ℂ => (z - c)⁻¹)
            Omega.boundaryParam) := by rw [mul_assoc]
      _ = q * 1 := hscaled
      _ = q := mul_one q
  rw [hscalar]

/-- Oriented convex geometry computes the operator resolvent contour mass.
The subsingleton case is automatic, while in the nontrivial case the affine
homotopy joins `A` to the scalar operator at the oriented carrier point. -/
theorem contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    exact Subsingleton.elim _ _
  · let _ := hE
    exact
      contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier_of_nontrivial
        A Omega c hc hcside hOmega

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
