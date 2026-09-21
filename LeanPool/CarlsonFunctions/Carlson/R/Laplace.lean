/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.R.Basic
public import LeanPool.CarlsonFunctions.Carlson.S
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Prod

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.PathConnected

/-!
# The Laplace representation of Carlson's R-function

This file develops the inverse confluence formula of [Carl77, Theorem 5.10-2], which expresses
`R` as a one-dimensional Laplace--Mellin transform of `S`.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.10,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
@[expose] public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The regularized Laplace--Mellin expression in Carlson's inverse confluence formula. -/
def regCarlsonRLaplaceIntegral (a : ℂ) (b z : ι → ℂ) : ℂ :=
  1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
    (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)

/-- The unregularized Laplace--Mellin expression in Carlson's inverse confluence formula. -/
def carlsonRLaplaceIntegral (a : ℂ) (b z : ι → ℂ) : ℂ :=
  1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
    (y : ℂ) ^ (a - 1) * carlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)

/-- Regularization in the Dirichlet parameters commutes with Carlson's one-dimensional
Laplace--Mellin construction. -/
theorem carlsonRLaplaceIntegral_eq_Gamma_mul_reg (a : ℂ) (b z : ι → ℂ) :
    carlsonRLaplaceIntegral a b z =
      Gamma (∑ i, b i) * regCarlsonRLaplaceIntegral a b z := by
  simp only [carlsonRLaplaceIntegral, regCarlsonRLaplaceIntegral, carlsonSIntegral]
  calc
    1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
        (y : ℂ) ^ (a - 1) *
          (Gamma (∑ i, b i) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) =
      1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
        Gamma (∑ i, b i) *
          ((y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) := by
        congr 2
        funext y
        ring
    _ = 1 / Gamma a * (Gamma (∑ i, b i) * ∫ y : ℝ in Set.Ioi 0,
        (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) := by
          rw [integral_const_mul]
    _ = Gamma (∑ i, b i) * (1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
        (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) := by
          ring

/-- The scalar Gamma integral underlying Carlson's inverse confluence formula, for a positive
real decay rate. -/
theorem integral_carlsonLaplaceKernel_ofReal {a : ℂ} {r : ℝ}
    (ha : 0 < a.re) (hr : 0 < r) :
    ∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (a - 1) * exp (-(r * y)) =
      (1 / r : ℂ) ^ a * Gamma a :=
  integral_cpow_mul_exp_neg_mul_Ioi ha hr

/-- Pointwise norm of the complex-rate Gamma kernel. -/
theorem norm_carlsonLaplaceKernel {a w : ℂ} {y : ℝ} (hy : 0 < y) :
    ‖(y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w)‖ =
      Real.exp (-w.re * y) * y ^ (a.re - 1) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, sub_re, one_re,
    Complex.norm_exp]
  have hre : (-(y : ℂ) * w).re = -w.re * y := by
    simp [mul_re, mul_comm]
  rw [hre]
  ring

/-- The integrand of `integral_carlsonLaplaceKernel_ofReal` is integrable. -/
theorem integrableOn_carlsonLaplaceKernel_ofReal {a : ℂ} {r : ℝ}
    (ha : 0 < a.re) (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (a - 1) * exp (-(r * y))) (Set.Ioi 0) := by
  have hval := integral_carlsonLaplaceKernel_ofReal (a := a) (r := r) ha hr
  by_contra h
  have hz : (∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (a - 1) * exp (-(r * y))) = 0 :=
    integral_undef h
  have hne : (1 / r : ℂ) ^ a * Gamma a ≠ 0 := by
    refine mul_ne_zero ?_ (Gamma_ne_zero_of_re_pos ha)
    exact cpow_ne_zero_iff.mpr (Or.inl (one_div_ne_zero (ofReal_ne_zero.mpr hr.ne')))
  exact hne (hval ▸ hz)

/-- Continuity of the complex-rate Gamma kernel on `(0, ∞)`. -/
theorem continuousOn_carlsonLaplaceKernel (a w : ℂ) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w))
      (Set.Ioi (0 : ℝ)) := by
  intro y hy
  refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
  · exact (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hy)).comp
      continuous_ofReal.continuousAt
  · exact continuous_exp.continuousAt.comp
      (((continuous_neg.comp continuous_ofReal).mul continuous_const).continuousAt)

/-- Integrability of the complex-rate Gamma kernel on `(0, ∞)`. -/
theorem integrableOn_carlsonLaplaceKernel {a w : ℂ}
    (ha : 0 < a.re) (hw : 0 < w.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w))
      (Set.Ioi (0 : ℝ)) := by
  have hreal := integrableOn_carlsonLaplaceKernel_ofReal (a := a) (r := w.re) ha hw
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (continuousOn_carlsonLaplaceKernel a w).aestronglyMeasurable measurableSet_Ioi
  refine Integrable.mono' (μ := volume.restrict (Set.Ioi (0 : ℝ))) hreal.norm hmeas ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
  have hypos : 0 < y := hy
  have hrealnorm :
      ‖(y : ℂ) ^ (a - 1) * exp (-(w.re * y))‖ =
        Real.exp (-w.re * y) * y ^ (a.re - 1) := by
    simpa [mul_comm (y : ℂ)] using
      (norm_carlsonLaplaceKernel (a := a) (w := (w.re : ℂ)) hypos)
  rw [norm_carlsonLaplaceKernel hypos, hrealnorm]

/-- The Laplace kernel is holomorphic in the decay rate throughout the right half-plane. -/
theorem hasDerivAt_integral_carlsonLaplaceKernel {a w : ℂ}
    (ha : 0 < a.re) (hw : 0 < w.re) :
    HasDerivAt
      (fun w' => ∫ y : ℝ in Set.Ioi (0 : ℝ),
        (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w'))
      (∫ y : ℝ in Set.Ioi (0 : ℝ),
        -((y : ℂ) * ((y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w)))) w := by
  let r : ℝ := w.re / 2
  let s : Set ℂ := {w' | r < w'.re}
  have hδ : 0 < r := half_pos hw
  have hs : s ∈ 𝓝 w :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (half_lt_self hw)
  let F : ℂ → ℝ → ℂ := fun w' y =>
    (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w')
  let F' : ℂ → ℝ → ℂ := fun w' y =>
    -((y : ℂ) * ((y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w')))
  let bound : ℝ → ℝ := fun y =>
    ‖(y : ℂ) ^ (((a.re : ℂ) + 1) - 1) * exp (-(r * y))‖
  have hF_meas : ∀ᶠ w' in 𝓝 w, AEStronglyMeasurable (F w')
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    filter_upwards [isOpen_carlsonRightHalfPlane.eventually_mem hw] with w' hw'
    exact (integrableOn_carlsonLaplaceKernel ha hw').1
  have hinter := integrableOn_carlsonLaplaceKernel_ofReal
      (a := (a.re : ℂ) + 1) (r := r) (add_pos ha zero_lt_one) hδ
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hinter.norm
  have hF'_meas : AEStronglyMeasurable (F' w)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro y hy
    have hypos : 0 < y := hy
    refine ContinuousAt.continuousWithinAt (ContinuousAt.neg (ContinuousAt.mul ?_ ?_))
    · exact continuous_ofReal.continuousAt
    · exact (continuousOn_carlsonLaplaceKernel a w y hy).continuousAt
        (isOpen_Ioi.mem_nhds hypos)
  have hbound : ∀ᵐ y : ℝ ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ w' ∈ s,
      ‖F' w' y‖ ≤ bound y := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy w' hw'
    have hypos : 0 < y := hy
    have hle : r ≤ w'.re := le_of_lt hw'
    have hy1 : y * y ^ (a.re - 1) = y ^ a.re := by
      simpa [Real.rpow_one] using (Real.rpow_add hypos 1 (a.re - 1)).symm
    have hre : (((a.re : ℂ) + 1) - 1).re = a.re := by simp
    have hLHS :
        ‖F' w' y‖ = Real.exp (-w'.re * y) * y ^ a.re := by
      unfold F'
      rw [norm_neg, norm_mul, norm_carlsonLaplaceKernel (a := a) (w := w') hypos]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hypos.le]
      calc
        y * (Real.exp (-w'.re * y) * y ^ (a.re - 1)) =
            Real.exp (-w'.re * y) * (y * y ^ (a.re - 1)) := by ring
        _ = Real.exp (-w'.re * y) * y ^ a.re := by rw [hy1]
    have hRHS :
        bound y = Real.exp (-r * y) * y ^ a.re := by
      simp only [bound, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hypos, hre, Complex.norm_exp]
      simp [mul_comm]
    rw [hLHS, hRHS]
    gcongr
  have hdiff : ∀ᵐ y : ℝ ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ w' ∈ s,
      HasDerivAt (F · y) (F' w' y) w' := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy w' hw'
    have harg : HasDerivAt (fun w'' : ℂ => -(y : ℂ) * w'') (-(y : ℂ)) w' :=
      hasDerivAt_const_mul (-(y : ℂ))
    have hexp : HasDerivAt (fun w'' : ℂ => exp (-(y : ℂ) * w''))
        (exp (-(y : ℂ) * w') * (-(y : ℂ))) w' :=
      (Complex.hasDerivAt_exp _).comp w' harg
    refine (hexp.const_mul ((y : ℂ) ^ (a - 1))).congr_deriv ?_
    simp [F', mul_comm, mul_assoc, mul_neg, neg_mul]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (F := F) (F' := F') (bound := bound)
      hs hF_meas (integrableOn_carlsonLaplaceKernel ha hw)
      hF'_meas hbound hbound_int hdiff).2

/-- The complex-rate Gamma integral needed in Carlson's inverse confluence theorem. -/
theorem integral_carlsonLaplaceKernel {a w : ℂ}
    (ha : 0 < a.re) (hw : 0 < w.re) :
    ∫ y : ℝ in Set.Ioi (0 : ℝ), (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w) =
      w ^ (-a) * Gamma a := by
  let Ω : Set ℂ := carlsonRightHalfPlane
  have hΩopen : IsOpen Ω := isOpen_carlsonRightHalfPlane
  have hΩpre : IsPreconnected Ω := convex_carlsonRightHalfPlane.isPreconnected
  let F : ℂ → ℂ := fun w' =>
    ∫ y : ℝ in Set.Ioi (0 : ℝ), (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w')
  let G : ℂ → ℂ := fun w' => w' ^ (-a) * Gamma a
  have hF : AnalyticOnNhd ℂ F Ω := by
    refine DifferentiableOn.analyticOnNhd ?_ hΩopen
    intro w' hw'
    exact (hasDerivAt_integral_carlsonLaplaceKernel ha hw').differentiableAt.differentiableWithinAt
  have hG : AnalyticOnNhd ℂ G Ω := by
    intro w' hw'
    have hwslit : w' ∈ slitPlane :=
      carlsonRightHalfPlane_subset_slitPlane hw'
    exact (AnalyticAt.cpow analyticAt_id analyticAt_const hwslit).mul analyticAt_const
  have hpos : (1 : ℂ) ∈ Ω := by simp [Ω, carlsonRightHalfPlane]
  have hagree : ∃ᶠ z in 𝓝[≠] (1 : ℂ), F z = G z := by
    have hseq : Tendsto (fun n : ℕ => ((1 + (n + 1 : ℝ)⁻¹ : ℝ) : ℂ))
        atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hr : Tendsto (fun n : ℕ => (1 + (n + 1 : ℝ)⁻¹ : ℝ)) atTop (𝓝 1) := by
          simpa using tendsto_const_nhds.add
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        exact Complex.continuous_ofReal.continuousAt.tendsto.comp hr
      · filter_upwards with n hn
        have : (1 + (n + 1 : ℝ)⁻¹ : ℝ) = 1 := Complex.ofReal_injective hn
        have : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by positivity
        linarith
    refine hseq.frequently (Frequently.of_forall fun n => ?_)
    let r : ℝ := 1 + (n + 1 : ℝ)⁻¹
    have hr : 0 < r := by positivity
    have hreal := integral_carlsonLaplaceKernel_ofReal (a := a) (r := r) ha hr
    have hcongr :
        (∫ y : ℝ in Set.Ioi (0 : ℝ),
            (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * (r : ℂ))) =
          ∫ y : ℝ in Set.Ioi (0 : ℝ),
            (y : ℂ) ^ (a - 1) * exp (-(r * y)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      have : -(y : ℂ) * (r : ℂ) = -(r * y : ℂ) := by
        simp [mul_comm]
      simp [this]
    have hpow : (1 / r : ℂ) ^ a = (r : ℂ) ^ (-a) := by
      rw [one_div, inv_cpow_ofReal_nonneg hr.le a, ← cpow_neg]
    calc
      F (r : ℂ) = ∫ y : ℝ in Set.Ioi (0 : ℝ),
          (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * (r : ℂ)) := rfl
      _ = ∫ y : ℝ in Set.Ioi (0 : ℝ),
          (y : ℂ) ^ (a - 1) * exp (-(r * y)) := hcongr
      _ = (1 / r : ℂ) ^ a * Gamma a := hreal
      _ = (r : ℂ) ^ (-a) * Gamma a := by rw [hpow]
      _ = G (r : ℂ) := rfl
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hΩpre hpos hagree hw

/-- Carlson's inverse confluence formula, Theorem 5.10-2, in regularized form. -/
theorem regCarlsonRIntegral_eq_regCarlsonRLaplaceIntegral
    {a : ℂ} (ha : 0 < a.re) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral (-a) b z = regCarlsonRLaplaceIntegral a b z := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [regCarlsonRIntegral, regCarlsonDirichletAverage, regDirichletIntegral,
        regCarlsonRLaplaceIntegral, regCarlsonSIntegral,
        MeasureTheory.Measure.stdSimplexMeasure_empty]
  | inr hι =>
    let _ := hι
    let μu := MeasureTheory.Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet
      ℝ ι)
    let μy := volume.restrict (Set.Ioi (0 : ℝ))
    let s : Finset ℝ := Finset.univ.image (fun i => (z i).re)
    have hs : s.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    let r : ℝ := s.min' hs
    have hr : 0 < r := by
      have hrmem : r ∈ s := Finset.min'_mem s hs
      rcases Finset.mem_image.mp hrmem with ⟨i, -, hi⟩
      rw [← hi]
      exact hz i
    have hr_le (i : ι) : r ≤ (z i).re := by
      exact Finset.min'_le s _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hWlower {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
        r ≤ (carlsonAffineForm z u).re := by
      have hre : (carlsonAffineForm z u).re = ∑ i, u i * (z i).re := by
        simp [carlsonAffineForm, mul_re]
      rw [hre]
      calc
        r = ∑ i, u i * r := by rw [← Finset.sum_mul, hu.2, one_mul]
        _ ≤ ∑ i, u i * (z i).re := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hr_le i) (hu.1 i)
    let F : ℝ × (ι → ℝ) → ℂ := fun p =>
      (p.1 : ℂ) ^ (a - 1) *
        (regDirichletDensity b p.2 * exp (-(p.1 : ℂ) * carlsonAffineForm z p.2))
    let G : ℝ × (ι → ℝ) → ℂ := fun p =>
      ((p.1 : ℂ) ^ (a - 1) * exp (-(r * p.1))) * regDirichletDensity b p.2
    have hG : Integrable G (μy.prod μu) := by
      have hy := integrableOn_carlsonLaplaceKernel_ofReal (a := a) (r := r) ha hr
      have hu : Integrable (regDirichletDensity b) μu := by
        change IntegrableOn (regDirichletDensity b) (Convexity.StdSimplex.coordinateSet ℝ ι)
          MeasureTheory.Measure.stdSimplexMeasure
        simpa only [mul_one] using integrableOn_regDirichletDensity_mul b hb
          (continuousOn_const : ContinuousOn (fun _ : ι → ℝ => (1 : ℂ))
            (Convexity.StdSimplex.coordinateSet ℝ ι))
      simpa [G, μy] using hy.mul_prod hu
    have hFmeas : AEStronglyMeasurable F (μy.prod μu) := by
      have hk : ContinuousOn (fun p : ℝ × (ι → ℝ) =>
          (p.1 : ℂ) ^ (a - 1) * exp (-(p.1 : ℂ) * carlsonAffineForm z p.2))
          (Set.Ioi (0 : ℝ) ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι) := by
        intro p hp
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.mul
        · have hy : ContinuousAt (fun q : ℝ × (ι → ℝ) => (q.1 : ℂ)) p := by
            simpa only [Function.comp_def] using
              (continuous_ofReal.comp continuous_fst).continuousAt
          exact (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hp.1)).comp_of_eq hy rfl
        · have hy : ContinuousAt (fun q : ℝ × (ι → ℝ) => (q.1 : ℂ)) p := by
            simpa only [Function.comp_def] using
              (continuous_ofReal.comp continuous_fst).continuousAt
          have hW : ContinuousAt (fun q : ℝ × (ι → ℝ) =>
              carlsonAffineForm z q.2) p := by
            simpa only [Function.comp_def] using
              ((continuous_carlsonAffineForm z).comp continuous_snd).continuousAt
          exact continuous_exp.continuousAt.comp (hy.neg.mul hW)
      unfold F μy μu
      rw [Measure.prod_restrict]
      have hk' : AEStronglyMeasurable
          (fun p : ℝ × (ι → ℝ) => (p.1 : ℂ) ^ (a - 1) *
            exp (-(p.1 : ℂ) * carlsonAffineForm z p.2))
          ((volume.prod MeasureTheory.Measure.stdSimplexMeasure).restrict
            (Set.Ioi (0 : ℝ) ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι)) :=
        hk.aestronglyMeasurable
          (measurableSet_Ioi.prod (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet)
      have hd : AEStronglyMeasurable (fun p : ℝ × (ι → ℝ) =>
          regDirichletDensity b p.2)
          ((volume.prod MeasureTheory.Measure.stdSimplexMeasure).restrict
            (Set.Ioi (0 : ℝ) ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι)) :=
        ((measurable_regDirichletDensity b).comp measurable_snd).aestronglyMeasurable
      have hm := hk'.mul hd
      convert hm using 1
      ext p
      change (p.1 : ℂ) ^ (a - 1) *
          (regDirichletDensity b p.2 * exp (-(p.1 : ℂ) * carlsonAffineForm z p.2)) =
        ((p.1 : ℂ) ^ (a - 1) * exp (-(p.1 : ℂ) * carlsonAffineForm z p.2)) *
          regDirichletDensity b p.2
      ring
    have hFle : ∀ᵐ p ∂μy.prod μu, ‖F p‖ ≤ ‖G p‖ := by
      have hp_mem : ∀ᵐ p ∂μy.prod μu,
          p.1 ∈ Set.Ioi (0 : ℝ) ∧ p.2 ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
        unfold μy μu
        rw [Measure.prod_restrict]
        exact ae_restrict_mem
          (measurableSet_Ioi.prod (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet)
      filter_upwards [hp_mem] with p hp
      rw [show ‖F p‖ = ‖regDirichletDensity b p.2‖ *
          (Real.exp (-(carlsonAffineForm z p.2).re * p.1) *
            p.1 ^ (a.re - 1)) by
        rw [show F p = regDirichletDensity b p.2 *
            ((p.1 : ℂ) ^ (a - 1) *
              exp (-(p.1 : ℂ) * carlsonAffineForm z p.2)) by unfold F; ring,
          norm_mul, norm_carlsonLaplaceKernel hp.1]]
      rw [show ‖G p‖ = ‖regDirichletDensity b p.2‖ *
          (Real.exp (-r * p.1) * p.1 ^ (a.re - 1)) by
        rw [show G p = regDirichletDensity b p.2 *
            ((p.1 : ℂ) ^ (a - 1) * exp (-(p.1 : ℂ) * (r : ℂ))) by
              have he : (-(r * p.1) : ℂ) = -(p.1 : ℂ) * (r : ℂ) := by
                simp [mul_comm]
              unfold G
              rw [he]
              ring,
          norm_mul, norm_carlsonLaplaceKernel hp.1]
        simp [mul_comm]]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg _ _)
      have hyp : 0 < p.1 := hp.1
      exact Real.exp_le_exp.mpr (by nlinarith [hWlower hp.2])
      all_goals exact hp.1.le
    have hF : Integrable F (μy.prod μu) := Integrable.mono' hG.norm hFmeas hFle
    have houter_eq_F :
        (∫ y : ℝ in Set.Ioi 0,
          (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) =
          ∫ y, ∫ u, F (y, u) ∂μu ∂μy := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      have hS : regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i) =
          ∫ u, regDirichletDensity b u *
            exp (-(y : ℂ) * carlsonAffineForm z u) ∂μu := by
        unfold regCarlsonSIntegral regCarlsonDirichletAverage regDirichletIntegral μu
        apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
        intro u hu
        have haff : carlsonAffineForm (fun i ↦ -(y : ℂ) * z i) u =
            -(y : ℂ) * carlsonAffineForm z u := by
          simpa using carlsonAffineForm_affine hu (-(y : ℂ)) 0 z
        change regDirichletDensity b u *
          exp (carlsonAffineForm (fun i ↦ -(y : ℂ) * z i) u) =
            regDirichletDensity b u * exp (-(y : ℂ) * carlsonAffineForm z u)
        rw [haff]
      change (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i) =
        ∫ u, F (y, u) ∂μu
      rw [hS]
      rw [← integral_const_mul]
    have hswap :
        (∫ y, ∫ u, F (y, u) ∂μu ∂μy) =
          ∫ u, ∫ y, F (y, u) ∂μy ∂μu :=
      integral_integral_swap hF
    have hinner : ∀ᵐ u ∂μu,
        (∫ y, F (y, u) ∂μy) =
          regDirichletDensity b u *
            (carlsonAffineForm z u ^ (-a) * Gamma a) := by
      have hu_mem : ∀ᵐ u ∂μu, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
        unfold μu
        exact ae_restrict_mem (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
      filter_upwards [hu_mem] with u hu
      calc
        (∫ y, F (y, u) ∂μy) = regDirichletDensity b u *
            ∫ y : ℝ in Set.Ioi 0,
              (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * carlsonAffineForm z u) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with y
          unfold F
          ring
        _ = regDirichletDensity b u *
            (carlsonAffineForm z u ^ (-a) * Gamma a) := by
          rw [integral_carlsonLaplaceKernel ha
            (carlsonAffineForm_mem_rightHalfPlane hz hu)]
    have hF_eq_R :
        (∫ u, ∫ y, F (y, u) ∂μy ∂μu) =
          Gamma a * regCarlsonRIntegral (-a) b z := by
      rw [integral_congr_ae hinner]
      unfold regCarlsonRIntegral regCarlsonDirichletAverage regDirichletIntegral μu
      rw [← integral_const_mul]
      apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
      intro u hu
      ring
    have hout :
        (∫ y : ℝ in Set.Ioi 0,
          (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) =
          Gamma a * regCarlsonRIntegral (-a) b z :=
      houter_eq_F.trans (hswap.trans hF_eq_R)
    rw [regCarlsonRLaplaceIntegral, hout]
    field_simp [Gamma_ne_zero_of_re_pos ha]

/-- Carlson's inverse confluence formula in the native unregularized normalization. -/
theorem carlsonRIntegral_eq_carlsonRLaplaceIntegral
    {a : ℂ} (ha : 0 < a.re) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    carlsonRIntegral (-a) b z = carlsonRLaplaceIntegral a b z := by
  rw [carlsonRIntegral_eq_Gamma_mul_reg,
    carlsonRLaplaceIntegral_eq_Gamma_mul_reg,
    regCarlsonRIntegral_eq_regCarlsonRLaplaceIntegral ha hb hz]

end DirichletTransform
end CarlsonR
