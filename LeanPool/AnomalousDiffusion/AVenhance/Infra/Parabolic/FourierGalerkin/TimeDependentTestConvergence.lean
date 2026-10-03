/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentWeakEquation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Spacetime convergence of the smooth-test Fourier cutoffs

The spatial Fourier tails from `Section5.TestDensity` are integrated in time by dominated
convergence. These estimates are the strong `L²` convergence needed to pass the product weak
equation from finite cutoffs to a general smooth spacetime test.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance timeTestConvergenceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance timeTestConvergenceMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance timeTestConvergenceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance timeTestConvergenceProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

theorem TimeDependentTestConvergence.timeTestConvergence_unitCube_measurable :
    MeasurableSet AVenhance.unitCube := by
  unfold AVenhance.unitCube
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

theorem TimeDependentTestConvergence.timeTestConvergence_l2Error_le_four {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (N : ℕ) :
    AVenhance.l2NormSq
        (fun x => f x - AVenhance.Infra.Section5.testFourierCutoff f N x) ≤
      4 * AVenhance.l2NormSq f := by
  let fN := AVenhance.Infra.Section5.testFourierCutoff f N
  have hfInt : Integrable (fun x : Vec 2 => f x ^ 2)
      (volume.restrict AVenhance.unitCube) :=
    bridge_continuous_integrable_cube (hf.continuous.pow 2)
  have hcutSmooth : ContDiff ℝ 1 fN :=
    (AVenhance.Infra.Section5.testFourierCutoff_analytic f N).of_le (by norm_num)
  have hcutInt : Integrable (fun x : Vec 2 => fN x ^ 2)
      (volume.restrict AVenhance.unitCube) :=
    bridge_continuous_integrable_cube (hcutSmooth.continuous.pow 2)
  have herrInt : Integrable (fun x : Vec 2 => (f x - fN x) ^ 2)
      (volume.restrict AVenhance.unitCube) :=
    bridge_continuous_integrable_cube ((hf.continuous.sub hcutSmooth.continuous).pow 2)
  have hpoint : ∀ x, (f x - fN x) ^ 2 ≤ 2 * f x ^ 2 + 2 * fN x ^ 2 := by
    intro x
    nlinarith [sq_nonneg (f x + fN x)]
  have hmono :
      ∫ x in AVenhance.unitCube, (f x - fN x) ^ 2 ≤
        ∫ x in AVenhance.unitCube, 2 * f x ^ 2 + 2 * fN x ^ 2 := by
    apply setIntegral_mono_on herrInt
      ((hfInt.const_mul 2).add (hcutInt.const_mul 2))
      TimeDependentTestConvergence.timeTestConvergence_unitCube_measurable
    intro x hx
    exact hpoint x
  have hsum :
      (∫ x in AVenhance.unitCube, 2 * f x ^ 2 + 2 * fN x ^ 2) =
        2 * AVenhance.l2NormSq f + 2 * AVenhance.l2NormSq fN := by
    rw [integral_add (hfInt.const_mul 2) (hcutInt.const_mul 2)]
    rw [integral_const_mul, integral_const_mul]
    rfl
  calc
    AVenhance.l2NormSq (fun x => f x - fN x) ≤
        ∫ x in AVenhance.unitCube, 2 * f x ^ 2 + 2 * fN x ^ 2 := by
          simpa [AVenhance.l2NormSq, fN] using hmono
    _ = 2 * AVenhance.l2NormSq f + 2 * AVenhance.l2NormSq fN := hsum
    _ ≤ 4 * AVenhance.l2NormSq f := by
      nlinarith [testFourierCutoff_l2_le hf N]

theorem TimeDependentTestConvergence.timeTestConvergence_l2Energy_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    Continuous (fun t => AVenhance.l2NormSq (φ t)) := by
  have hF : Continuous (fun p : ℝ × Vec 2 => φ p.1 p.2 ^ 2) := hφ.continuous.pow 2
  simpa [AVenhance.l2NormSq] using continuous_cell_integral_of_joint hF

theorem TimeDependentTestConvergence.spacetimeTestValueCutoff_continuous
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) (N : ℕ) :
    Continuous (fun p : ℝ × Vec 2 =>
      AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) := by
  let sumFun : ℝ × Vec 2 → ℝ := fun p =>
    ∑ j : Fin (RealFourierDimension N),
      spacetimeRealFourierCoefficient φ N j p.1 *
        realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) p.2
  have hsum : Continuous sumFun := by
    unfold sumFun
    apply continuous_finsetSum
    intro j hj
    exact (spacetimeRealFourierCoefficient_contDiff_one hφ N j).continuous.comp
        continuous_fst |>.mul
      ((realFourierModeAmbient_contDiff N
        ((realFourierIndexEquivFin N).symm j)).continuous.comp continuous_snd)
  have heq (p : ℝ × Vec 2) :
      AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2 = sumFun p := by
    simpa [sumFun] using spacetimeTestFourierCutoff_expansion hφ hperiodic N p.1 p.2
  exact hsum.congr fun p => (heq p).symm

theorem TimeDependentTestConvergence.spacetimeTestValueCutoff_error_energy_continuous
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) (N : ℕ) :
    Continuous (fun t => AVenhance.l2NormSq (fun x =>
      φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x)) := by
  have hcut := TimeDependentTestConvergence.spacetimeTestValueCutoff_continuous hφ hperiodic N
  have hF : Continuous (fun p : ℝ × Vec 2 =>
      (φ p.1 p.2 - AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) ^ 2) := by
    exact (hφ.continuous.sub hcut).pow 2
  simpa [AVenhance.l2NormSq] using continuous_cell_integral_of_joint hF

theorem TimeDependentTestConvergence.timeTestConvergence_gradientCoord_continuous {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    Continuous (fun x => AVenhance.spaceGrad f x i) := by
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem TimeDependentTestConvergence.timeTestConvergence_gradient_continuous {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) : Continuous (AVenhance.spaceGrad f) :=
  continuous_pi (fun i =>
      TimeDependentTestConvergence.timeTestConvergence_gradientCoord_continuous hf i)

theorem TimeDependentTestConvergence.timeTestConvergence_gradientError_le_four {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hperiodic : AVenhance.IsZ2Periodic f) (N : ℕ) :
    AVenhance.gradNormSq (AVenhance.spaceGrad (fun x =>
      f x - AVenhance.Infra.Section5.testFourierCutoff f N x)) ≤
      4 * AVenhance.gradNormSq (AVenhance.spaceGrad f) := by
  let fN := AVenhance.Infra.Section5.testFourierCutoff f N
  have hfN : ContDiff ℝ 1 fN :=
    (AVenhance.Infra.Section5.testFourierCutoff_analytic f N).of_le (by norm_num)
  have hgradDiff (x : Vec 2) :
      AVenhance.spaceGrad (fun y => f y - fN y) x =
        AVenhance.spaceGrad f x - AVenhance.spaceGrad fN x := by
    funext i
    simp only [AVenhance.spaceGrad]
    rw [fderiv_fun_sub
      ((hf.differentiable (by norm_num)).differentiableAt)
      ((hfN.differentiable (by norm_num)).differentiableAt)]
    simp [AVenhance.spaceGrad]
  have hpoint : ∀ x, Homogenization.vecNormSq
      (AVenhance.spaceGrad (fun y => f y - fN y) x) ≤
      2 * Homogenization.vecNormSq (AVenhance.spaceGrad f x) +
        2 * Homogenization.vecNormSq (AVenhance.spaceGrad fN x) := by
    intro x
    rw [hgradDiff]
    simp [Homogenization.vecNormSq, Homogenization.vecDot, Fin.sum_univ_succ]
    nlinarith [sq_nonneg
      (AVenhance.spaceGrad f x 0 + AVenhance.spaceGrad fN x 0),
      sq_nonneg (AVenhance.spaceGrad f x 1 + AVenhance.spaceGrad fN x 1)]
  have herrInt : Integrable
      (fun x : Vec 2 => Homogenization.vecNormSq
        (AVenhance.spaceGrad (fun y => f y - fN y) x))
      (volume.restrict AVenhance.unitCube) := by
    have hc : Continuous (fun x => Homogenization.vecNormSq
        (AVenhance.spaceGrad (fun y => f y - fN y) x)) := by
      have hcoord (i : Fin 2) : Continuous
          (fun x => AVenhance.spaceGrad (fun y => f y - fN y) x i) :=
        TimeDependentTestConvergence.timeTestConvergence_gradientCoord_continuous (hf.sub hfN) i
      unfold Homogenization.vecNormSq Homogenization.vecDot
      exact continuous_finsetSum Finset.univ (fun i hi =>
        (hcoord i).mul (hcoord i))
    exact bridge_continuous_integrable_cube hc
  have hfInt : Integrable
      (fun x : Vec 2 => Homogenization.vecNormSq (AVenhance.spaceGrad f x))
      (volume.restrict AVenhance.unitCube) := by
    have hgrad := TimeDependentTestConvergence.timeTestConvergence_gradient_continuous hf
    have hcoord (i : Fin 2) : Continuous (fun x => AVenhance.spaceGrad f x i) :=
      TimeDependentTestConvergence.timeTestConvergence_gradientCoord_continuous hf i
    have hc : Continuous (fun x => Homogenization.vecNormSq (AVenhance.spaceGrad f x)) := by
      unfold Homogenization.vecNormSq Homogenization.vecDot
      exact continuous_finsetSum Finset.univ (fun i hi =>
        (hcoord i).mul (hcoord i))
    exact bridge_continuous_integrable_cube hc
  have hcutInt : Integrable
      (fun x : Vec 2 => Homogenization.vecNormSq (AVenhance.spaceGrad fN x))
      (volume.restrict AVenhance.unitCube) := by
    have hcoord (i : Fin 2) : Continuous (fun x => AVenhance.spaceGrad fN x i) :=
      TimeDependentTestConvergence.timeTestConvergence_gradientCoord_continuous hfN i
    have hc : Continuous (fun x => Homogenization.vecNormSq (AVenhance.spaceGrad fN x)) := by
      unfold Homogenization.vecNormSq Homogenization.vecDot
      exact continuous_finsetSum Finset.univ (fun i hi =>
        (hcoord i).mul (hcoord i))
    exact bridge_continuous_integrable_cube hc
  have hmono :
      ∫ x in AVenhance.unitCube,
        Homogenization.vecNormSq (AVenhance.spaceGrad (fun y => f y - fN y) x) ≤
      ∫ x in AVenhance.unitCube,
        2 * Homogenization.vecNormSq (AVenhance.spaceGrad f x) +
          2 * Homogenization.vecNormSq (AVenhance.spaceGrad fN x) := by
    apply setIntegral_mono_on herrInt
      ((hfInt.const_mul 2).add (hcutInt.const_mul 2))
      TimeDependentTestConvergence.timeTestConvergence_unitCube_measurable
    intro x hx
    exact hpoint x
  have hsum :
      (∫ x in AVenhance.unitCube,
        2 * Homogenization.vecNormSq (AVenhance.spaceGrad f x) +
          2 * Homogenization.vecNormSq (AVenhance.spaceGrad fN x)) =
        2 * AVenhance.gradNormSq (AVenhance.spaceGrad f) +
          2 * AVenhance.gradNormSq (AVenhance.spaceGrad fN) := by
    rw [integral_add (hfInt.const_mul 2) (hcutInt.const_mul 2)]
    rw [integral_const_mul, integral_const_mul]
    rfl
  calc
    AVenhance.gradNormSq (AVenhance.spaceGrad (fun x => f x - fN x)) ≤
        ∫ x in AVenhance.unitCube,
          2 * Homogenization.vecNormSq (AVenhance.spaceGrad f x) +
            2 * Homogenization.vecNormSq (AVenhance.spaceGrad fN x) := by
          simpa [AVenhance.gradNormSq] using hmono
    _ = 2 * AVenhance.gradNormSq (AVenhance.spaceGrad f) +
          2 * AVenhance.gradNormSq (AVenhance.spaceGrad fN) := hsum
    _ ≤ 4 * AVenhance.gradNormSq (AVenhance.spaceGrad f) := by
      nlinarith [AVenhance.Infra.Section5.testFourierCutoff_gradient_le hf hperiodic N]

theorem TimeDependentTestConvergence.spacetimeTestSpatialGradient_continuous
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    Continuous (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (φ p.1) p.2) := by
  apply continuous_pi
  intro i
  have hFderiv : Continuous
      (fderiv ℝ (fun p : ℝ × Vec 2 => φ p.1 p.2)) :=
    hφ.continuous_fderiv (by norm_num)
  have h : Continuous (fun p : ℝ × Vec 2 =>
      (fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p) (0, Homogenization.basisVec i)) :=
    hFderiv.clm_apply continuous_const
  have heq (p : ℝ × Vec 2) :
      AVenhance.spaceGrad (φ p.1) p.2 i =
        (fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p) (0, Homogenization.basisVec i) := by
    let F : ℝ × Vec 2 → ℝ := fun q => φ q.1 q.2
    have houter : HasFDerivAt F (fderiv ℝ F (p.1, p.2)) (p.1, p.2) :=
      (hφ.differentiable (by norm_num) (p.1, p.2)).hasFDerivAt
    have hlineDeriv : HasFDerivAt (fun x : Vec 2 => (p.1, x))
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hcomp := HasFDerivAt.comp p.2 houter hlineDeriv
    have hcomp' := hcomp.fderiv
    have hlineEval : (ContinuousLinearMap.inr ℝ ℝ (Vec 2))
        (Homogenization.basisVec i) = (0, Homogenization.basisVec i) := by
      simp [ContinuousLinearMap.inr]
    change fderiv ℝ (F ∘ fun x : Vec 2 => (p.1, x)) p.2
        (Homogenization.basisVec i) =
      (fderiv ℝ F (p.1, p.2)) (0, Homogenization.basisVec i)
    rw [hcomp']
    simp [ContinuousLinearMap.comp_apply, hlineEval]
  exact h.congr fun p => (heq p).symm

theorem TimeDependentTestConvergence.spacetimeTestFourierCutoff_contDiff_one
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) (N : ℕ) :
    ContDiff ℝ 1 (fun p : ℝ × Vec 2 =>
      AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) := by
  let sumFun : ℝ × Vec 2 → ℝ := fun p =>
    ∑ j : Fin (RealFourierDimension N),
      spacetimeRealFourierCoefficient φ N j p.1 *
        realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) p.2
  have hterm (j : Fin (RealFourierDimension N)) : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 =>
        spacetimeRealFourierCoefficient φ N j p.1 *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) p.2) := by
    exact ((spacetimeRealFourierCoefficient_contDiff_one hφ N j).comp contDiff_fst).mul
      (((realFourierModeAmbient_contDiff N
        ((realFourierIndexEquivFin N).symm j)).of_le (by norm_num)).comp contDiff_snd)
  have hsum : ContDiff ℝ 1 sumFun := by
    unfold sumFun
    exact ContDiff.sum (fun j _ => hterm j)
  have heq (p : ℝ × Vec 2) :
      AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2 = sumFun p := by
    simpa [sumFun] using spacetimeTestFourierCutoff_expansion hφ hperiodic N p.1 p.2
  have hfun : (fun p : ℝ × Vec 2 =>
      AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) = sumFun := by
    funext p
    exact heq p
  rw [hfun]
  exact hsum

theorem TimeDependentTestConvergence.timeTestConvergence_gradientEnergy_continuous {φ : ℝ → Vec 2
    → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    Continuous (fun t => AVenhance.gradNormSq (AVenhance.spaceGrad (φ t))) := by
  have hφone : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => φ p.1 p.2) :=
    hφ.of_le (by norm_num)
  have hgrad := TimeDependentTestConvergence.spacetimeTestSpatialGradient_continuous hφone
  have hF : Continuous (fun p : ℝ × Vec 2 =>
      Homogenization.vecNormSq (AVenhance.spaceGrad (φ p.1) p.2)) := by
    have hcoord (i : Fin 2) : Continuous (fun p : ℝ × Vec 2 =>
        AVenhance.spaceGrad (φ p.1) p.2 i) :=
      (continuous_apply i).comp hgrad
    unfold Homogenization.vecNormSq Homogenization.vecDot
    exact continuous_finsetSum Finset.univ (fun i hi =>
      (hcoord i).mul (hcoord i))
  simpa [AVenhance.gradNormSq] using continuous_cell_integral_of_joint hF

theorem TimeDependentTestConvergence.spacetimeTestGradientCutoff_error_energy_continuous
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) (N : ℕ) :
    Continuous (fun t => AVenhance.gradNormSq (AVenhance.spaceGrad
      (fun x => φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x))) := by
  have hφone : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => φ p.1 p.2) :=
    hφ.of_le (by norm_num)
  have htest := TimeDependentTestConvergence.spacetimeTestSpatialGradient_continuous hφone
  let φN : ℝ → Vec 2 → ℝ := fun t =>
    AVenhance.Infra.Section5.testFourierCutoff (φ t) N
  have hcutone : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => φN p.1 p.2) := by
    simpa [φN] using TimeDependentTestConvergence.spacetimeTestFourierCutoff_contDiff_one hφ
        hperiodic N
  have hcutGrad := TimeDependentTestConvergence.spacetimeTestSpatialGradient_continuous (φ := φN)
      hcutone
  have hgradDifference : Continuous (fun p : ℝ × Vec 2 =>
      AVenhance.spaceGrad (φ p.1) p.2 -
        AVenhance.spaceGrad
          (AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N) p.2) :=
    htest.sub hcutGrad
  have hEq (p : ℝ × Vec 2) :
      AVenhance.spaceGrad (fun x => φ p.1 x -
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 =
      AVenhance.spaceGrad (φ p.1) p.2 -
        AVenhance.spaceGrad
          (AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N) p.2 := by
    have hφslice : ContDiff ℝ 1 (φ p.1) :=
      hφone.comp (contDiff_prodMk_right p.1)
    have hcutslice : ContDiff ℝ 1
        (AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N) := by
      simpa [Function.comp_def, φN] using
        hcutone.comp (contDiff_prodMk_right p.1)
    ext i
    simp only [AVenhance.spaceGrad]
    rw [fderiv_fun_sub
      ((hφslice.differentiable (by norm_num)).differentiableAt)
      ((hcutslice.differentiable (by norm_num)).differentiableAt)]
    simp [AVenhance.spaceGrad]
  have herrGrad : Continuous (fun p : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => φ p.1 x -
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2) :=
    hgradDifference.congr fun p => (hEq p).symm
  have hsq : Continuous (fun p : ℝ × Vec 2 =>
      Homogenization.vecNormSq
        (AVenhance.spaceGrad (fun x => φ p.1 x -
          AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2)) := by
    unfold Homogenization.vecNormSq Homogenization.vecDot
    have hcoord (i : Fin 2) : Continuous (fun p : ℝ × Vec 2 =>
        AVenhance.spaceGrad (fun x => φ p.1 x -
          AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) :=
      (continuous_apply i).comp herrGrad
    exact continuous_finsetSum Finset.univ (fun i hi =>
      (hcoord i).mul (hcoord i))
  simpa [AVenhance.gradNormSq] using continuous_cell_integral_of_joint hsq

/-- The square-integral of the value error of the time-dependent Fourier cutoff tends to zero.
-/
theorem spacetimeTestValueCutoff_error_integral_tendsto
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) :
    Tendsto
      (fun N => ∫ t, AVenhance.l2NormSq (fun x =>
        φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x)
        ∂GalerkinTimeMeasure) atTop (𝓝 0) := by
  let E : ℕ → ℝ → ℝ := fun N t => AVenhance.l2NormSq (fun x =>
    φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x)
  have hEmeas : ∀ N, AEStronglyMeasurable (E N) GalerkinTimeMeasure := by
    intro N
    exact (TimeDependentTestConvergence.spacetimeTestValueCutoff_error_energy_continuous hφ
        hperiodic N).aestronglyMeasurable
  have henergyCont := TimeDependentTestConvergence.timeTestConvergence_l2Energy_continuous hφ
  obtain ⟨C, hCpos, hCball⟩ := (isCompact_Icc.image henergyCont).isBounded.subset_ball_lt 0 0
  have hEnergyBound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AVenhance.l2NormSq (φ t) ≤ C := by
    intro t ht
    have hb := hCball ⟨t, ht, rfl⟩
    have habs : |AVenhance.l2NormSq (φ t)| < C := by
      simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hb
    have hnonneg : 0 ≤ AVenhance.l2NormSq (φ t) := by
      unfold AVenhance.l2NormSq
      exact setIntegral_nonneg TimeDependentTestConvergence.timeTestConvergence_unitCube_measurable
        (fun x _ => sq_nonneg _)
    simpa [abs_of_nonneg hnonneg] using habs.le
  have hbound : ∀ N, ∀ᵐ t ∂GalerkinTimeMeasure, ‖E N t‖ ≤ 4 * C := by
    intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    have herror := TimeDependentTestConvergence.timeTestConvergence_l2Error_le_four
      ((hφ.comp (contDiff_prodMk_right t)).of_le (by norm_num)) N
    have hnonneg : 0 ≤ E N t := by
      unfold E AVenhance.l2NormSq
      exact setIntegral_nonneg TimeDependentTestConvergence.timeTestConvergence_unitCube_measurable
        (fun x _ => sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      E N t ≤ 4 * AVenhance.l2NormSq (φ t) := by
        simpa [E, Function.comp_def, Function.comp_apply] using herror
      _ ≤ 4 * C := by nlinarith [hEnergyBound t htcc]
  have hpoint : ∀ᵐ t ∂GalerkinTimeMeasure,
      Tendsto (fun N => E N t) atTop (𝓝 0) := by
    filter_upwards with t
    have hslice : ContDiff ℝ 1 (φ t) :=
      (hφ.comp (contDiff_prodMk_right t)).of_le (by norm_num)
    simpa [E] using AVenhance.Infra.Section5.testFourierCutoff_L2_error_tendsto hslice
  have hconstInt : Integrable (fun _ : ℝ => 4 * C) GalerkinTimeMeasure := integrable_const _
  have hdominated := tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => 4 * C) hEmeas hconstInt hbound hpoint
  simpa [E] using hdominated

/-- The spacetime square-integral of the spatial-gradient error of the time-dependent Fourier
cutoff tends to zero. -/
theorem spacetimeTestGradientCutoff_error_integral_tendsto
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) :
    Tendsto
      (fun N => ∫ t, AVenhance.gradNormSq (AVenhance.spaceGrad (fun x =>
        φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x))
        ∂GalerkinTimeMeasure) atTop (𝓝 0) := by
  let E : ℕ → ℝ → ℝ := fun N t => AVenhance.gradNormSq (AVenhance.spaceGrad (fun x =>
    φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x))
  have hEmeas : ∀ N, AEStronglyMeasurable (E N) GalerkinTimeMeasure := by
    intro N
    exact (TimeDependentTestConvergence.spacetimeTestGradientCutoff_error_energy_continuous hφ
        hperiodic N).aestronglyMeasurable
  have henergyCont := TimeDependentTestConvergence.timeTestConvergence_gradientEnergy_continuous hφ
  obtain ⟨C, hCpos, hCball⟩ := (isCompact_Icc.image henergyCont).isBounded.subset_ball_lt 0 0
  have hEnergyBound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AVenhance.gradNormSq (AVenhance.spaceGrad (φ t)) ≤ C := by
    intro t ht
    have hb := hCball ⟨t, ht, rfl⟩
    have habs : |AVenhance.gradNormSq (AVenhance.spaceGrad (φ t))| < C := by
      simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hb
    have hnonneg : 0 ≤ AVenhance.gradNormSq (AVenhance.spaceGrad (φ t)) := by
      unfold AVenhance.gradNormSq
      exact setIntegral_nonneg TimeDependentTestConvergence.timeTestConvergence_unitCube_measurable
        (fun x _ => Homogenization.vecNormSq_nonneg _)
    simpa [abs_of_nonneg hnonneg] using habs.le
  have hbound : ∀ N, ∀ᵐ t ∂GalerkinTimeMeasure, ‖E N t‖ ≤ 4 * C := by
    intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    have hslice : ContDiff ℝ 1 (φ t) :=
      (hφ.comp (contDiff_prodMk_right t)).of_le (by norm_num)
    have herror := TimeDependentTestConvergence.timeTestConvergence_gradientError_le_four
      hslice (hperiodic t) N
    have hnonneg : 0 ≤ E N t := by
      unfold E AVenhance.gradNormSq
      exact setIntegral_nonneg TimeDependentTestConvergence.timeTestConvergence_unitCube_measurable
        (fun x _ => Homogenization.vecNormSq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      E N t ≤ 4 * AVenhance.gradNormSq (AVenhance.spaceGrad (φ t)) := by
        simpa [E] using herror
      _ ≤ 4 * C := by nlinarith [hEnergyBound t htcc]
  have hpoint : ∀ᵐ t ∂GalerkinTimeMeasure,
      Tendsto (fun N => E N t) atTop (𝓝 0) := by
    filter_upwards with t
    have hslice : ContDiff ℝ 1 (φ t) :=
      (hφ.comp (contDiff_prodMk_right t)).of_le (by norm_num)
    simpa [E] using
      AVenhance.Infra.Section5.testFourierCutoff_gradient_error_tendsto
        hslice (hperiodic t)
  have hconstInt : Integrable (fun _ : ℝ => 4 * C) GalerkinTimeMeasure := integrable_const _
  have hdominated := tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => 4 * C) hEmeas hconstInt hbound hpoint
  simpa [E] using hdominated

/-- The time derivative has the same spacetime `L²` Fourier-tail convergence as a smooth
periodic test. -/
theorem spacetimeTestTimeDerivativeCutoff_error_integral_tendsto
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) :
    Tendsto
      (fun N => ∫ t, AVenhance.l2NormSq (fun x =>
        spacetimeTestTimeDerivative φ t x -
          AVenhance.Infra.Section5.testFourierCutoff
            (spacetimeTestTimeDerivative φ t) N x)
        ∂GalerkinTimeMeasure) atTop (𝓝 0) := by
  exact spacetimeTestValueCutoff_error_integral_tendsto
    (spacetimeTestTimeDerivative_contDiff hφ)
    (spacetimeTestTimeDerivative_periodic hperiodic)

end AVenhance.Infra.Parabolic.FourierGalerkin

end
