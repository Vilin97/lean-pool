/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Measure.Minlos
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Minlos Analyticity — Symmetry and Moments for Gaussian Measures

This file provides infrastructure for Gaussian measures constructed via Minlos' theorem:
- `CovarianceForm`: Real symmetric bilinear form for covariance
- `negMap`, `integral_neg_invariance`: Symmetry under sign flip (uses Minlos uniqueness)
- `moment_zero_from_realCF`: Zero mean from characteristic functional symmetry
-/

open TopologicalSpace MeasureTheory Complex Filter

/-! ## Contents

This file provides infrastructure for Gaussian measures via Minlos.
No axioms declared here.
-/

noncomputable section

namespace MinlosAnalytic

/-- A real symmetric, positive semidefinite covariance form on real test functions,
    together with a proof that the associated Gaussian characteristic functional
    exp(-½Q(f,f)) is positive definite (in the bochner sense).
-/
structure CovarianceForm where
  /-- The real covariance bilinear form. -/
  Q : TestFunction → TestFunction → ℝ
  symm : ∀ f g, Q f g = Q g f
  psd  : ∀ f, 0 ≤ Q f f
  cont_diag : Continuous fun f => Q f f
  add_left : ∀ f₁ f₂ g, Q (f₁ + f₂) g = Q f₁ g + Q f₂ g
  smul_left : ∀ (c : ℝ) f g, Q (c • f) g = c * Q f g
  gaussian_cf_pd : IsPositiveDefinite
    (fun f : TestFunction => Complex.exp (-(1/2 : ℂ) * (Q f f : ℂ)))

/-- The negation map on field configurations: T(ω) = -ω -/
def negMap : FieldConfiguration → FieldConfiguration := fun ω => -ω

/-- The negation map is measurable w.r.t. the cylinder σ-algebra. -/
lemma negMap_measurable : Measurable negMap := by
  rw [measurable_iff_comap_le]
  -- Unfold the cylinder σ-algebra instance and distribute comap over iSup
  change (⨆ f,
    (borel ℝ).comap (fun l : FieldConfiguration => (l : TestFunction →L[ℝ] ℝ) f)).comap negMap ≤
    ⨆ f, (borel ℝ).comap (fun l : FieldConfiguration => (l : TestFunction →L[ℝ] ℝ) f)
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le; intro g
  rw [MeasurableSpace.comap_comp]
  conv_lhs => rw [show (fun l : FieldConfiguration => (l : TestFunction →L[ℝ] ℝ) g) ∘ negMap =
      Neg.neg ∘ (fun l : FieldConfiguration => (l : TestFunction →L[ℝ] ℝ) g) from by
    ext ω; change (-ω) g = -(ω g); exact ContinuousLinearMap.neg_apply ω g]
  rw [← MeasurableSpace.comap_comp]
  have h_neg_meas : (borel ℝ).comap (Neg.neg : ℝ → ℝ) ≤ borel ℝ :=
    measurable_iff_comap_le.mp measurable_neg
  calc ((borel ℝ).comap Neg.neg).comap (fun l : FieldConfiguration => (l : TestFunction →L[ℝ] ℝ) g)
      ≤ (borel ℝ).comap (fun l : FieldConfiguration => (l : TestFunction →L[ℝ] ℝ) g) :=
        MeasurableSpace.comap_mono h_neg_meas
    _ ≤ _ := le_iSup (fun f => (borel ℝ).comap (fun l : FieldConfiguration => (l : TestFunction
      →L[ℝ] ℝ) f)) g

/-- Symmetry under global sign flip induced by the real Gaussian CF.
    Uses Minlos uniqueness from the bochner library.
-/
lemma integral_neg_invariance
  [IsHilbertNuclear TestFunction] [SeparableSpace TestFunction] [Nonempty TestFunction]
  [IsTopologicalAddGroup TestFunction] [ContinuousSMul ℝ TestFunction]
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f))) :
  ∀ (f : FieldConfiguration → ℂ), Integrable f μ.toMeasure →
    ∫ ω, f ω ∂μ.toMeasure = ∫ ω, f (-ω) ∂μ.toMeasure := by
  intro f hInt
  classical
  -- Step 1: Define the pushforward measure
  let μneg := μ.toMeasure.map negMap
  have hμneg_prob : IsProbabilityMeasure μneg := by
    exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable negMap_measurable)
  -- Step 2: Show characteristic functionals are equal
  have hCF_equal : ∀ g : TestFunction,
      ∫ ω, Complex.exp (Complex.I * (distributionPairing ω g)) ∂μneg
        = ∫ ω, Complex.exp (Complex.I * (distributionPairing ω g)) ∂μ.toMeasure := by
    intro g
    -- Use eval_measurable for the integrand
    have h_inner_meas : Measurable (fun ω : FieldConfiguration => distributionPairing ω g) :=
      WeakDual.eval_measurable g
    have h_cont_mulI : Continuous (fun x : ℝ => (Complex.I : ℂ) * (x : ℂ)) :=
      continuous_const.mul continuous_ofReal
    have h_cont_exp : Continuous (fun z : ℂ => Complex.exp z) := Complex.continuous_exp
    have h_outer_meas : Measurable (fun x : ℝ => Complex.exp ((Complex.I : ℂ) * (x : ℂ))) :=
      (h_cont_exp.comp h_cont_mulI).measurable
    have h_aestrongly_measurable : AEStronglyMeasurable (fun ω => Complex.exp (Complex.I *
      (distributionPairing ω g))) μneg :=
      (h_outer_meas.comp h_inner_meas).aestronglyMeasurable
    rw [integral_map (Measurable.aemeasurable negMap_measurable) h_aestrongly_measurable]
    have h_neg_pairing : (fun ω => Complex.exp (Complex.I * (distributionPairing (negMap ω) g))) =
                         (fun ω => Complex.exp (Complex.I * (distributionPairing (-ω) g))) := by
      simp [negMap]
    rw [h_neg_pairing]
    have h_neg_eq : ∀ ω : FieldConfiguration, distributionPairing (-ω) g = -distributionPairing ω g
      := by
      intro ω
      change (-ω) g = -(ω g)
      exact ContinuousLinearMap.neg_apply ω g
    have h_lhs_eq : (fun ω => Complex.exp (Complex.I * (distributionPairing (-ω) g : ℂ))) =
                    (fun ω => Complex.exp (-(Complex.I * (distributionPairing ω g : ℂ)))) := by
      funext ω
      rw [h_neg_eq]
      simp only [ofReal_neg, mul_neg]
    conv_lhs => rw [h_lhs_eq]
    have h_exp_neg_conj : ∀ x : ℝ, Complex.exp (-(Complex.I * (x : ℂ))) = starRingEnd ℂ
      (Complex.exp (Complex.I * (x : ℂ))) := by
      intro x
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have h_integrand_conj : (fun ω => Complex.exp (-(Complex.I * (distributionPairing ω g : ℂ)))) =
                            (fun ω => starRingEnd ℂ (Complex.exp (Complex.I * (distributionPairing
                               ω g : ℂ)))) := by
      funext ω
      exact h_exp_neg_conj (distributionPairing ω g)
    conv_lhs => rw [h_integrand_conj]
    have h_pull_conj : ∫ ω : FieldConfiguration, (starRingEnd ℂ)
        (Complex.exp (Complex.I * (distributionPairing ω g : ℂ))) ∂μ.toMeasure
        = (starRingEnd ℂ) (∫ ω,
          Complex.exp (Complex.I * (distributionPairing ω g : ℂ)) ∂μ.toMeasure) :=
      integral_conj
    rw [h_pull_conj]
    simp only [distributionPairing] at *
    rw [h_realCF g]
    have h_CF_is_real : (Complex.exp (-(1/2 : ℂ) * (C.Q g g : ℂ))).im = 0 := by
      have h_eq : (-(1/2 : ℂ) * (C.Q g g : ℂ)) = ((-(1/2 : ℝ) * C.Q g g : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h_eq]
      exact Complex.exp_ofReal_im (-(1/2) * C.Q g g)
    rw [Complex.conj_eq_iff_im.mpr h_CF_is_real]
  -- Step 3: Apply uniqueness of measures (Minlos theorem)
  let μneg_prob : ProbabilityMeasure FieldConfiguration := ⟨μneg, hμneg_prob⟩
  have h_cf_cont : Continuous
      (fun f : TestFunction => Complex.exp (-(1/2 : ℂ) * (C.Q f f : ℂ))) :=
    continuous_exp.comp (continuous_const.mul (continuous_ofReal.comp C.cont_diag))
  have h_cf_norm : (fun f : TestFunction =>
      Complex.exp (-(1/2 : ℂ) * (C.Q f f : ℂ))) 0 = 1 := by
    simp [show C.Q 0 0 = 0 from by simpa using C.smul_left 0 0 0]
  have hμeq_prob : μneg_prob = μ := by
    simp only [distributionPairing] at hCF_equal h_realCF
    exact minlos_gaussian_uniqueness h_cf_cont C.gaussian_cf_pd h_cf_norm
      (fun g => (hCF_equal g).trans (h_realCF g)) h_realCF
  have hμeq : μneg = μ.toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure hμeq_prob
    exact h
  -- Step 4: Use the equality of measures to get the integral identity
  have hf_aestrongly_measurable : AEStronglyMeasurable f μneg := by
    rw [hμeq]
    exact hInt.aestronglyMeasurable
  have h_cov : ∫ ω, f ω ∂μneg = ∫ ω, f (negMap ω) ∂μ.toMeasure := by
    exact integral_map (Measurable.aemeasurable negMap_measurable) hf_aestrongly_measurable
  rw [hμeq] at h_cov
  rw [h_cov]
  simp [negMap]

/-- Zero mean from the real Gaussian characteristic functional, via symmetry and L¹. -/
lemma moment_zero_from_realCF
  [IsHilbertNuclear TestFunction] [SeparableSpace TestFunction] [Nonempty TestFunction]
  [IsTopologicalAddGroup TestFunction] [ContinuousSMul ℝ TestFunction]
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a : TestFunction)
  (hInt1 : Integrable (fun ω => (ω a : ℂ)) μ.toMeasure) :
  ∫ ω, (ω a : ℂ) ∂μ.toMeasure = 0 := by
  classical
  -- Symmetry: ∫ f(ω) = ∫ f(-ω)
  have hInv := integral_neg_invariance C μ h_realCF (fun ω => (ω a : ℂ)) hInt1
  -- Flip integrand: ((-ω) a : ℂ) = - (ω a : ℂ)
  have hflip : (fun ω : FieldConfiguration => ((-ω) a : ℂ)) = (fun ω => - (ω a : ℂ)) := by
    funext ω
    have : (-ω) a = -(ω a) := ContinuousLinearMap.neg_apply ω a
    simp [this]
  -- Hence ∫ X = ∫ -X = -∫ X
  have : ∫ ω, (ω a : ℂ) ∂μ.toMeasure = - ∫ ω, (ω a : ℂ) ∂μ.toMeasure := by
    simpa [hflip, integral_neg, hInt1] using hInv
  -- 2 · ∫ X = 0 ⇒ ∫ X = 0
  exact self_eq_neg.mp this

end MinlosAnalytic
