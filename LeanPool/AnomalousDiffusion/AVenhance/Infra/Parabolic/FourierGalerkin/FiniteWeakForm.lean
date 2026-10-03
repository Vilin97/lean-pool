/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.GalerkinSequence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.EquationModulus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.LimitPassage
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Time-tested finite Galerkin equation

The measurable-coefficient ODE yields the weak equation against a fixed finite Fourier test with
an arbitrary smooth time factor vanishing at the terminal time. This is the finite test identity
used before passing to the space-time weak limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open scoped Topology RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- The coefficient ODE, integrated against a smooth time test and a fixed real Fourier vector,
has the expected initial trace. -/
theorem FrozenDriftProblem.finite_time_test_identity
    (P : FrozenDriftProblem) (N : ℕ)
    (d : Coefficients (RealFourierDimension N))
    (η : ℝ → ℝ) (hη : ContDiff ℝ 1 η) (hη₁ : η 1 = 0) :
    ∫ t in (0 : ℝ)..1,
      -(inner ℝ
          (AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N) t) d) *
            deriv η t -
        η t * inner ℝ
          ((P.galerkinData N).coefficient t
            (AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N) t)) d =
      η 0 * inner ℝ (P.galerkinData N).initial d := by
  let D := P.galerkinData N
  let y : ℝ → Coefficients (RealFourierDimension N) :=
    AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N)
  let F : ℝ → ℝ := fun t => inner ℝ (y t) d
  have hACy : AbsolutelyContinuousOnInterval y 0 1 :=
    (P.coefficientPath_isSolution N).absolutelyContinuousOnInterval D.ode
  let L : Coefficients (RealFourierDimension N) →L[ℝ] ℝ := innerSL ℝ d
  have hF : AbsolutelyContinuousOnInterval F 0 1 := by
    have hcomp := (ContinuousLinearMap.lipschitzWith L).comp_absolutelyContinuousOnInterval hACy
    apply hcomp.congr
    intro t
    simp [F, L, real_inner_comm]
  have hηAC : AbsolutelyContinuousOnInterval η 0 1 :=
    hη.contDiffOn.absolutelyContinuousOnInterval
  have hderiv := (P.coefficientPath_isSolution N).ae_hasDerivAt D.ode
  have hFderiv : ∀ᵐ t ∂volume, t ∈ Set.Icc (0 : ℝ) 1 →
      deriv F t = inner ℝ (D.coefficient t (y t)) d := by
    filter_upwards [hderiv] with t ht hmem
    have hAt := HasDerivAt.inner ℝ (ht hmem) (hasDerivAt_const t d)
    have hAt' : HasDerivAt F (inner ℝ (D.coefficient t (y t)) d) t := by
      simpa [F, y, WeakFormGalerkinData.ode,
        AVenhance.Infra.ODE.LinearODEData.A,
        AVenhance.Infra.ODE.LinearODEData.f, real_inner_comm] using hAt
    exact hAt'.deriv
  have hFη' : IntervalIntegrable (fun t => F t * deriv η t) volume 0 1 := by
    have hmul := hηAC.intervalIntegrable_deriv.mul_continuousOn hF.continuousOn
    simpa [mul_comm] using hmul
  have hF'η : IntervalIntegrable (fun t => deriv F t * η t) volume 0 1 := by
    exact hF.intervalIntegrable_deriv.mul_continuousOn hηAC.continuousOn
  have hiparts := hF.integral_mul_deriv_eq_deriv_mul hηAC
  have hcombine :
      ∫ t in (0 : ℝ)..1, -(F t * deriv η t) - deriv F t * η t =
        -(∫ t in (0 : ℝ)..1, F t * deriv η t) -
          ∫ t in (0 : ℝ)..1, deriv F t * η t := by
    calc
      ∫ t in (0 : ℝ)..1, -(F t * deriv η t) - deriv F t * η t =
          (∫ t in (0 : ℝ)..1, -(F t * deriv η t)) -
            ∫ t in (0 : ℝ)..1, deriv F t * η t :=
        intervalIntegral.integral_sub hFη'.neg hF'η
      _ = -(∫ t in (0 : ℝ)..1, F t * deriv η t) -
          ∫ t in (0 : ℝ)..1, deriv F t * η t := by
        rw [intervalIntegral.integral_neg]
  have hbase :
      ∫ t in (0 : ℝ)..1, -(F t * deriv η t) - deriv F t * η t =
        η 0 * F 0 := by
    rw [hcombine, hiparts]
    rw [hη₁]
    ring
  have hinit : y 0 = D.initial := by
    have hext : y 0 = P.coefficientPath N ⟨0, by norm_num, by norm_num⟩ := by
      change AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N) 0 = _
      exact AVenhance.Infra.ODE.extendCurve_eq_of_mem
        (by norm_num) (P.coefficientPath N)
        (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    rw [hext, P.coefficientPath_initial N]
  calc
    _ = ∫ t in (0 : ℝ)..1, -(F t * deriv η t) - deriv F t * η t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hFderiv] with t ht
      intro htIoc
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
          uIoc_subset_uIcc htIoc
      rw [ht htIcc]
      simp only [F, y, D]
      ring
    _ = η 0 * F 0 := hbase
    _ = η 0 * inner ℝ D.initial d := by rw [← hinit]

/-- The concrete weak form holds after time integration against every fixed real Fourier
test and smooth scalar time factor vanishing at `t = 1`. -/
theorem FrozenDriftProblem.finite_fourier_test_weak_identity
    (P : FrozenDriftProblem) (N : ℕ)
    (d : Coefficients (RealFourierDimension N))
    (η : ℝ → ℝ) (hη : ContDiff ℝ 1 η) (hη₁ : η 1 = 0) :
    let y : ℝ → Coefficients (RealFourierDimension N) :=
      AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N)
    ∫ t in (0 : ℝ)..1,
      -(inner ℝ (realFourierScalarMap N (y t))
        (realFourierScalarMap N d)) * deriv η t +
        η t * (realFourierDriftBilinearForm N
          (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) t (y t) d +
          P.κ * inner ℝ (realFourierGradientMap N (y t))
            (realFourierGradientMap N d)) =
      η 0 * inner ℝ (P.galerkinData N).initial d := by
  dsimp only
  let D := P.galerkinData N
  let y : ℝ → Coefficients (RealFourierDimension N) :=
    AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N)
  have hentries := frozenDrift_realModeEntry_integrable_ae N P.b
    P.drift_measurable P.drift_bounded
  have hA : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      inner ℝ (D.coefficient t (y t)) d =
        -realFourierDriftBilinearForm N
          (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) t (y t) d -
        P.κ * inner ℝ (realFourierGradientMap N (y t))
          (realFourierGradientMap N d) := by
    filter_upwards [hentries, D.matrix_spec] with t herr hspec
    have hcoef : D.coefficient t (y t) = matrixCoefficientCLM
        (fun i j => weakFormMatrixEntry
          (fun s x => AVenhance.Infra.Torus.periodicToTorus (P.b s) x) P.κ
          (realFourierModeFin N) (realFourierModeGradFin N) t i j) (y t) := by
      ext i
      rw [matrixCoefficientCLM_apply]
      exact hspec (y t) i
    have hbil := positiveCutoffWeakForm_bilinear_identity N P.b P.κ t (y t) d herr
    rw [real_inner_comm, hcoef]
    exact hbil
  have hfinite := P.finite_time_test_identity N d η hη hη₁
  have hpathpair (t : ℝ) : inner ℝ (realFourierScalarMap N (y t))
      (realFourierScalarMap N d) = inner ℝ (y t) d :=
    realFourierScalarMap_inner N (y t) d
  have hAvol := (ae_restrict_iff' measurableSet_Icc).mp hA
  calc
    _ = ∫ t in (0 : ℝ)..1,
        -(inner ℝ (y t) d) * deriv η t - η t * inner ℝ (D.coefficient t (y t)) d := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hAvol] with t ht htIoc
      have htIcc : t ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
          uIoc_subset_uIcc htIoc
      rw [hpathpair, ht htIcc]
      ring
    _ = η 0 * inner ℝ D.initial d := hfinite
    _ = η 0 * inner ℝ (P.galerkinData N).initial d := by rfl

end AVenhance.Infra.Parabolic.FourierGalerkin

end
