/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCauchyKernelConstancy
public import LeanPool.OperatorTheory.Operator.Crouzeix.CircleCauchy

/-!
# The exterior resolvent Cauchy kernel

The scalar Cauchy kernel vanishes outside a closed convex carrier.  Combining
that fact with the two-parameter resolvent identity evaluates the nested
operator kernel

`(2 * pi * I)⁻¹ ∮ (sigma - z)⁻¹ R_A(z) dz = R_A(sigma)`.

This is the inner-contour calculation needed to identify the scalar companion
functional calculus with the original conjugate-polynomial auxiliary contour.
-/

@[expose] public section

open Complex Set spectrum
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- The two-parameter resolvent identity in the form adapted to the nested
Cauchy kernel. -/
theorem inv_sub_smul_resolvent_eq_resolvent_mul_resolvent_add
    (A : E →L[ℂ] E) {z sigma : ℂ}
    (hz : z ∈ resolventSet ℂ A) (hsigma : sigma ∈ resolventSet ℂ A)
    (hne : z ≠ sigma) :
    (sigma - z)⁻¹ • resolvent A z =
      resolvent A z * resolvent A sigma +
        (sigma - z)⁻¹ • resolvent A sigma := by
  let B : E →L[ℂ] E := A - (sigma - z) • (1 : E →L[ℂ] E)
  have hB : z ∈ resolventSet ℂ B := by
    rw [mem_resolventSet_iff] at hsigma ⊢
    have heq : algebraMap ℂ (E →L[ℂ] E) z - B =
        algebraMap ℂ (E →L[ℂ] E) sigma - A := by
      dsimp only [B]
      simp only [Algebra.algebraMap_eq_smul_one]
      module
    rwa [heq]
  have hresB : resolvent B z = resolvent A sigma := by
    dsimp only [B]
    rw [resolvent_sub_smul_one_shift]
    congr 1
    ring
  have hsecond := spectrum.resolvent_sub_resolvent hz hB
  rw [hresB] at hsecond
  have hdiff : resolvent A z - resolvent A sigma =
      (sigma - z) • (resolvent A z * resolvent A sigma) := by
    calc
      resolvent A z - resolvent A sigma =
          resolvent A z * (A - B) * resolvent A sigma := hsecond
      _ = (sigma - z) • (resolvent A z * resolvent A sigma) := by
        dsimp only [B]
        simp only [sub_sub_cancel, mul_smul_comm, mul_one, smul_mul_assoc]
  have hscaled := congrArg (fun T : E →L[ℂ] E => (sigma - z)⁻¹ • T) hdiff
  simp only [smul_sub, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm), one_smul] at hscaled
  exact sub_eq_iff_eq_add.mp hscaled

/-- A fixed vector can be moved through a scalar-weighted contour integral. -/
theorem contourIntegral_smul_const
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : ℂ → ℂ) (b : F) (gamma : ℝ → ℂ) :
    contourIntegral (fun z => f z • b) gamma =
      contourIntegral f gamma • b := by
  unfold contourIntegral
  simp only [smul_smul]
  exact intervalIntegral.integral_smul_const
    (fun t => deriv gamma t * f (gamma t)) b

/-- Integrating the nested exterior Cauchy kernel against a resolvent contour
returns the resolvent at the exterior point, with the unnormalized contour
mass factor. -/
theorem contourIntegral_inv_sub_smul_resolvent_eq_two_pi_I_smul_resolvent
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (sigma : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsigma : sigma ∉ closure Omega.carrier) :
    contourIntegral (fun z => (sigma - z)⁻¹ • resolvent A z)
        Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • resolvent A sigma := by
  have hsigmaR : sigma ∈ resolventSet ℂ A := by
    by_contra hrho
    have hspectrum : sigma ∈ spectrum ℂ A := hrho
    exact hsigma (subset_closure
      (hOmega (spectrum_subset_closure_numericalRange A hspectrum)))
  have hboundaryR : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ A :=
    fun t => Omega.boundaryParam_mem_resolventSet A hOmega t
  have hboundaryNe : ∀ t : ℝ, Omega.boundaryParam t ≠ sigma := by
    intro t heq
    apply hsigma
    rw [← heq]
    apply frontier_subset_closure
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hres : ContourIntegrable (resolvent A) Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · rintro z ⟨t, _ht, rfl⟩
      exact (spectrum.hasDerivAt_resolvent_const_left
        (hboundaryR t)).continuousAt.continuousWithinAt
  have hresMul : ContourIntegrable
      (fun z => resolvent A z * resolvent A sigma)
      Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · apply ContinuousOn.mul
      · rintro z ⟨t, _ht, rfl⟩
        exact (spectrum.hasDerivAt_resolvent_const_left
          (hboundaryR t)).continuousAt.continuousWithinAt
      · exact continuousOn_const
  have hinvMul : ContourIntegrable
      (fun z => (sigma - z)⁻¹ • resolvent A sigma)
      Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · have hinv : ContinuousOn (fun z : ℂ => (sigma - z)⁻¹)
          (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) := by
        apply ContinuousOn.inv₀
        · exact (continuous_const.sub continuous_id).continuousOn
        · rintro _ ⟨t, _ht, rfl⟩
          exact sub_ne_zero.mpr (hboundaryNe t).symm
      let L : ℂ →L[ℂ] (E →L[ℂ] E) :=
        (1 : ℂ →L[ℂ] ℂ).smulRight (resolvent A sigma)
      have hL : Continuous (fun a : ℂ => a • resolvent A sigma) := by
        change Continuous (L : ℂ → E →L[ℂ] E)
        exact L.continuous
      exact hL.comp_continuousOn hinv
  have hinvzero :
      contourIntegral (fun z => (sigma - z)⁻¹) Omega.boundaryParam = 0 := by
    calc
      contourIntegral (fun z => (sigma - z)⁻¹) Omega.boundaryParam =
          contourIntegral (fun z => -(z - sigma)⁻¹) Omega.boundaryParam := by
        congr 1
        funext z
        rw [show sigma - z = -(z - sigma) by ring, inv_neg]
      _ = -contourIntegral (fun z => (z - sigma)⁻¹)
          Omega.boundaryParam := contourIntegral_neg _ _
      _ = 0 := by
        rw [contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier
          Omega hsigma, neg_zero]
  calc
    contourIntegral (fun z => (sigma - z)⁻¹ • resolvent A z)
        Omega.boundaryParam =
        contourIntegral (fun z =>
          resolvent A z * resolvent A sigma +
            (sigma - z)⁻¹ • resolvent A sigma)
          Omega.boundaryParam := by
      unfold contourIntegral
      apply intervalIntegral.integral_congr
      intro t _ht
      change deriv Omega.boundaryParam t •
          ((sigma - Omega.boundaryParam t)⁻¹ •
            resolvent A (Omega.boundaryParam t)) =
        deriv Omega.boundaryParam t •
          (resolvent A (Omega.boundaryParam t) * resolvent A sigma +
            (sigma - Omega.boundaryParam t)⁻¹ • resolvent A sigma)
      rw [inv_sub_smul_resolvent_eq_resolvent_mul_resolvent_add A (hboundaryR t)
        hsigmaR (hboundaryNe t)]
    _ = contourIntegral (fun z => resolvent A z * resolvent A sigma)
          Omega.boundaryParam +
        contourIntegral (fun z => (sigma - z)⁻¹ • resolvent A sigma)
          Omega.boundaryParam := contourIntegral_add hresMul hinvMul
    _ = contourIntegral (resolvent A) Omega.boundaryParam *
          resolvent A sigma +
        contourIntegral (fun z => (sigma - z)⁻¹) Omega.boundaryParam •
          resolvent A sigma := by
      rw [contourIntegral_mul_const (resolvent A sigma) hres,
        contourIntegral_smul_const]
    _ = (2 * (Real.pi : ℂ) * I) • resolvent A sigma := by
      rw [hmass, hinvzero,
        zero_smul, add_zero, smul_mul_assoc, one_mul]

/-- Normalized operator-valued Cauchy reproduction for an exterior resolvent
point of a smooth convex carrier. -/
theorem normalized_contourIntegral_inv_sub_smul_resolvent_eq_resolvent
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (sigma : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsigma : sigma ∉ closure Omega.carrier) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => (sigma - z)⁻¹ • resolvent A z)
          Omega.boundaryParam =
      resolvent A sigma := by
  rw [contourIntegral_inv_sub_smul_resolvent_eq_two_pi_I_smul_resolvent
    A Omega sigma hOmega hmass hsigma, smul_smul,
    inv_mul_cancel₀]
  · exact one_smul ℂ (resolvent A sigma)
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr
      Real.pi_ne_zero)) Complex.I_ne_zero

/-- Fubini's theorem for two contour integrals, with the exact product
integrability hypothesis on the derivative-weighted kernel. -/
theorem contourIntegral_contourIntegral_swap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → ℂ → F) (gamma delta : ℝ → ℂ)
    (hint : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ =>
      deriv gamma x.1 •
        (deriv delta x.2 • f (gamma x.1) (delta x.2)))
      (uIoc (0 : ℝ) (2 * Real.pi) ×ˢ
        uIoc (0 : ℝ) (2 * Real.pi))) :
    contourIntegral (fun z => contourIntegral (f z) delta) gamma =
      contourIntegral (fun w => contourIntegral (fun z => f z w) gamma)
        delta := by
  unfold contourIntegral
  calc
    (∫ s in (0 : ℝ)..(2 * Real.pi), deriv gamma s •
        ∫ t in (0 : ℝ)..(2 * Real.pi),
          deriv delta t • f (gamma s) (delta t)) =
        ∫ s in (0 : ℝ)..(2 * Real.pi),
          ∫ t in (0 : ℝ)..(2 * Real.pi),
            deriv gamma s •
              (deriv delta t • f (gamma s) (delta t)) := by
      apply intervalIntegral.integral_congr
      intro s _hs
      change deriv gamma s •
          (∫ t in (0 : ℝ)..(2 * Real.pi),
            deriv delta t • f (gamma s) (delta t)) =
        ∫ t in (0 : ℝ)..(2 * Real.pi), deriv gamma s •
          (deriv delta t • f (gamma s) (delta t))
      rw [intervalIntegral.integral_smul]
    _ = ∫ t in (0 : ℝ)..(2 * Real.pi),
          ∫ s in (0 : ℝ)..(2 * Real.pi),
            deriv gamma s •
              (deriv delta t • f (gamma s) (delta t)) := by
      exact MeasureTheory.intervalIntegral_intervalIntegral_swap hint
    _ = ∫ t in (0 : ℝ)..(2 * Real.pi),
          ∫ s in (0 : ℝ)..(2 * Real.pi),
            deriv delta t •
              (deriv gamma s • f (gamma s) (delta t)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      apply intervalIntegral.integral_congr
      intro s _hs
      exact smul_comm _ _ _
    _ = ∫ t in (0 : ℝ)..(2 * Real.pi), deriv delta t •
          ∫ s in (0 : ℝ)..(2 * Real.pi),
            deriv gamma s • f (gamma s) (delta t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change (∫ s in (0 : ℝ)..(2 * Real.pi), deriv delta t •
          (deriv gamma s • f (gamma s) (delta t))) =
        deriv delta t •
          (∫ s in (0 : ℝ)..(2 * Real.pi),
            deriv gamma s • f (gamma s) (delta t))
      rw [intervalIntegral.integral_smul]

/-- For two nested smooth Jordan domains, the derivative-weighted
scalar-companion/resolvent kernel is integrable on the parameter square. -/
theorem integrableOn_nested_scalarCompanion_resolvent_kernel
    (A : E →L[ℂ] E) (Omega Psi : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hnest : closure Omega.carrier ⊆ Psi.carrier) :
    MeasureTheory.IntegrableOn (fun x : ℝ × ℝ =>
      deriv Omega.boundaryParam x.1 •
        (deriv Psi.boundaryParam x.2 •
          (star (Polynomial.eval (Psi.boundaryParam x.2) p) •
            ((2 * (Real.pi : ℂ) * I)⁻¹ •
              ((Psi.boundaryParam x.2 - Omega.boundaryParam x.1)⁻¹ •
                resolvent A (Omega.boundaryParam x.1))))))
      (uIoc (0 : ℝ) (2 * Real.pi) ×ˢ
        uIoc (0 : ℝ) (2 * Real.pi)) := by
  let K : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) (2 * Real.pi)
  have hOmegaParam : Continuous (fun x : ℝ × ℝ =>
      Omega.boundaryParam x.1) :=
    Omega.boundaryParam_contDiff.continuous.comp continuous_fst
  have hPsiParam : Continuous (fun x : ℝ × ℝ =>
      Psi.boundaryParam x.2) :=
    Psi.boundaryParam_contDiff.continuous.comp continuous_snd
  have hOmegaDeriv : Continuous (fun x : ℝ × ℝ =>
      deriv Omega.boundaryParam x.1) :=
    (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).comp
      continuous_fst
  have hPsiDeriv : Continuous (fun x : ℝ × ℝ =>
      deriv Psi.boundaryParam x.2) :=
    (Psi.boundaryParam_contDiff.continuous_deriv (by norm_num)).comp
      continuous_snd
  have hres : ContinuousOn (fun x : ℝ × ℝ =>
      resolvent A (Omega.boundaryParam x.1)) K := by
    have hresBase : ContinuousOn (resolvent A)
        (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) := by
      rintro z ⟨t, _ht, rfl⟩
      exact (spectrum.hasDerivAt_resolvent_const_left
        (Omega.boundaryParam_mem_resolventSet A hOmega t)).continuousAt.continuousWithinAt
    apply hresBase.comp' hOmegaParam.continuousOn
    intro x hx
    exact ⟨x.1, hx.1, rfl⟩
  have hinv : ContinuousOn (fun x : ℝ × ℝ =>
      (Psi.boundaryParam x.2 - Omega.boundaryParam x.1)⁻¹) K := by
    apply ContinuousOn.inv₀
    · exact hPsiParam.continuousOn.sub hOmegaParam.continuousOn
    · intro x _hx
      apply sub_ne_zero.mpr
      intro heq
      have hInnerFrontier :
          Omega.boundaryParam x.1 ∈ frontier Omega.carrier := by
        rw [← Omega.boundaryParam_range]
        exact mem_range_self x.1
      have hOuterFrontier :
          Psi.boundaryParam x.2 ∈ frontier Psi.carrier := by
        rw [← Psi.boundaryParam_range]
        exact mem_range_self x.2
      have hempty : Psi.boundaryParam x.2 ∈ (∅ : Set ℂ) := by
        rw [← Psi.isOpen_carrier.inter_frontier_eq]
        refine ⟨?_, hOuterFrontier⟩
        rw [heq]
        exact hnest (frontier_subset_closure hInnerFrontier)
      exact hempty.elim
  have hpoly : Continuous (fun x : ℝ × ℝ =>
      star (Polynomial.eval (Psi.boundaryParam x.2) p)) :=
    p.continuous.star.comp hPsiParam
  have hc : ContinuousOn (fun _x : ℝ × ℝ =>
      (2 * (Real.pi : ℂ) * I)⁻¹) K := continuousOn_const
  have hcont : ContinuousOn (fun x : ℝ × ℝ =>
      deriv Omega.boundaryParam x.1 •
        (deriv Psi.boundaryParam x.2 •
          (star (Polynomial.eval (Psi.boundaryParam x.2) p) •
            ((2 * (Real.pi : ℂ) * I)⁻¹ •
              ((Psi.boundaryParam x.2 - Omega.boundaryParam x.1)⁻¹ •
                resolvent A (Omega.boundaryParam x.1)))))) K :=
    hOmegaDeriv.continuousOn.smul
      (hPsiDeriv.continuousOn.smul
        (hpoly.continuousOn.smul
          (hc.smul (hinv.smul hres))))
  apply (hcont.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
  rw [uIoc_of_le Real.two_pi_pos.le]
  exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self

private theorem crouzeixAuxiliaryOperator_scalarCompanion_of_separated_integrable
    (A : E →L[ℂ] E) (Omega Psi : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsep : ∀ t : ℝ,
      Psi.boundaryParam t ∉ closure Omega.carrier)
    (hint : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ =>
      deriv Omega.boundaryParam x.1 •
        (deriv Psi.boundaryParam x.2 •
          (star (Polynomial.eval (Psi.boundaryParam x.2) p) •
            ((2 * (Real.pi : ℂ) * I)⁻¹ •
              ((Psi.boundaryParam x.2 - Omega.boundaryParam x.1)⁻¹ •
                resolvent A (Omega.boundaryParam x.1))))))
      (uIoc (0 : ℝ) (2 * Real.pi) ×ˢ
        uIoc (0 : ℝ) (2 * Real.pi))) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanion Psi p) =
      crouzeixPolynomialAuxiliaryOperator A Psi p := by
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  let f : ℂ → ℂ → (E →L[ℂ] E) := fun z sigma =>
    star (Polynomial.eval sigma p) •
      (c • ((sigma - z)⁻¹ • resolvent A z))
  have hleft : ∀ z : ℂ,
      contourIntegral (f z) Psi.boundaryParam =
        crouzeixPolynomialScalarCompanion Psi p z • resolvent A z := by
    intro z
    have hfun : f z = fun sigma =>
        (c * (star (Polynomial.eval sigma p) * (sigma - z)⁻¹)) •
          resolvent A z := by
      funext sigma
      dsimp only [f]
      simp only [smul_smul]
      congr 1
      ring
    rw [hfun, contourIntegral_smul_const]
    have hscale := contourIntegral_smul c
      (fun sigma => star (Polynomial.eval sigma p) * (sigma - z)⁻¹)
      Psi.boundaryParam
    simp only [smul_eq_mul] at hscale
    rw [hscale]
    rfl
  have hright : ∀ (sigma : ℂ), sigma ∉ closure Omega.carrier →
      contourIntegral (fun z => f z sigma) Omega.boundaryParam =
        star (Polynomial.eval sigma p) • resolvent A sigma := by
    intro sigma hsigma
    dsimp only [f, c]
    rw [contourIntegral_smul, contourIntegral_smul,
      normalized_contourIntegral_inv_sub_smul_resolvent_eq_resolvent
        A Omega sigma hOmega hmass hsigma]
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  congr 1
  calc
    contourIntegral
        (fun z => crouzeixPolynomialScalarCompanion Psi p z • resolvent A z)
        Omega.boundaryParam =
      contourIntegral (fun z => contourIntegral (f z) Psi.boundaryParam)
        Omega.boundaryParam := by
      congr 1
      funext z
      exact (hleft z).symm
    _ = contourIntegral
        (fun sigma => contourIntegral (fun z => f z sigma) Omega.boundaryParam)
        Psi.boundaryParam := by
      apply contourIntegral_contourIntegral_swap
      simpa only [f, c] using hint
    _ = contourIntegral
        (fun sigma => star (Polynomial.eval sigma p) • resolvent A sigma)
        Psi.boundaryParam := by
      unfold contourIntegral
      apply intervalIntegral.integral_congr
      intro t _ht
      change deriv Psi.boundaryParam t •
          contourIntegral (fun z => f z (Psi.boundaryParam t))
            Omega.boundaryParam =
        deriv Psi.boundaryParam t •
          (star (Polynomial.eval (Psi.boundaryParam t) p) •
            resolvent A (Psi.boundaryParam t))
      rw [hright (Psi.boundaryParam t) (hsep t)]

/-- If one smooth Jordan domain compactly contains another, applying the
inner auxiliary calculus to the outer scalar companion reproduces the outer
conjugate-polynomial auxiliary contour. -/
theorem crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_nested
    (A : E →L[ℂ] E) (Omega Psi : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hnest : closure Omega.carrier ⊆ Psi.carrier) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension Psi p) =
      crouzeixPolynomialAuxiliaryOperator A Psi p := by
  have hsep : ∀ t : ℝ,
      Psi.boundaryParam t ∉ closure Omega.carrier := by
    intro t ht
    have hfrontier : Psi.boundaryParam t ∈ frontier Psi.carrier := by
      rw [← Psi.boundaryParam_range]
      exact mem_range_self t
    have hempty : Psi.boundaryParam t ∈ (∅ : Set ℂ) := by
      rw [← Psi.isOpen_carrier.inter_frontier_eq]
      exact ⟨hnest ht, hfrontier⟩
    exact hempty
  calc
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension Psi p) =
      crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanion Psi p) := by
      unfold crouzeixAuxiliaryOperator
      congr 1
      unfold contourIntegral
      apply intervalIntegral.integral_congr
      intro t _ht
      have hfrontier : Omega.boundaryParam t ∈ frontier Omega.carrier := by
        rw [← Omega.boundaryParam_range]
        exact mem_range_self t
      change deriv Omega.boundaryParam t •
          (crouzeixPolynomialScalarCompanionClosedExtension Psi p
              (Omega.boundaryParam t) •
            resolvent A (Omega.boundaryParam t)) =
        deriv Omega.boundaryParam t •
          (crouzeixPolynomialScalarCompanion Psi p
              (Omega.boundaryParam t) •
            resolvent A (Omega.boundaryParam t))
      rw [crouzeixPolynomialScalarCompanionClosedExtension_eq Psi p
        (hnest (frontier_subset_closure hfrontier))]
    _ = crouzeixPolynomialAuxiliaryOperator A Psi p :=
      crouzeixAuxiliaryOperator_scalarCompanion_of_separated_integrable
        A Omega Psi p hOmega hmass hsep
          (integrableOn_nested_scalarCompanion_resolvent_kernel
            A Omega Psi p hOmega hnest)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
