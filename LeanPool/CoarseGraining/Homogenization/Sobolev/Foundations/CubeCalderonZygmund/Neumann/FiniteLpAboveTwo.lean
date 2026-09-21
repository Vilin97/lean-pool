/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLp
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.Neumann.EnergyDuality
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.Neumann.ReflectedOneLevelTail

/-!
# Centered-cube Neumann Calderón--Zygmund estimates above two

This file closes the reflected Neumann good-`lambda` estimate by layer-cake
integration.  Its public endpoint exposes only the supplied mean-zero weak
solution and the normalized finite-exponent datum.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory Set

private theorem centeredCube_normalizedVolume_eq_smul_openCubeVolume_finitePNeumann
    {d : ℕ} (m : ℤ) :
    (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
  change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

private theorem sqWeightedMeasure_restrict_apply_eq_inter_finitePNeumann
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {B T : Set α} {f : α → E}
    (hB : MeasurableSet B) :
    sqWeightedMeasure f (μ.restrict B) T = sqWeightedMeasure f μ (T ∩ B) := by
  change ((μ.restrict B).withDensity fun x ↦ ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) T =
    (μ.withDensity fun x ↦ ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) (T ∩ B)
  rw [← MeasureTheory.restrict_withDensity hB]
  exact Measure.restrict_apply' hB

private theorem sqWeightedMeasure_smul_measure_finitePNeumann
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {c : ℝ≥0∞} {T : Set α} {f : α → E} :
    sqWeightedMeasure f (c • μ) T = c * sqWeightedMeasure f μ T := by
  unfold sqWeightedMeasure
  rw [MeasureTheory.withDensity_smul_measure]
  rfl

private noncomputable def finiteLpExponentSuccNeumann (p : FiniteLpExponent) :
    FiniteLpExponent where
  exponent := p.exponent + 1
  one_lt := lt_of_lt_of_le p.one_lt (le_add_of_nonneg_right bot_le)
  lt_top := ENNReal.add_lt_top.mpr ⟨p.lt_top, by norm_num⟩

private theorem finiteLpExponentSuccNeumann_toReal (p : FiniteLpExponent) :
    (finiteLpExponentSuccNeumann p).exponent.toReal = p.exponent.toReal + 1 := by
  simp only [finiteLpExponentSuccNeumann]
  rw [ENNReal.toReal_add p.lt_top.ne ENNReal.one_ne_top]
  norm_num

private theorem finiteLpExponent_lt_succNeumann (p : FiniteLpExponent) :
    p.exponent.toReal < (finiteLpExponentSuccNeumann p).exponent.toReal := by
  rw [finiteLpExponentSuccNeumann_toReal]
  linarith

private theorem sqWeightedMeasure_univ_ne_top_of_memLp_two_finitePNeumann
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    sqWeightedMeasure f μ Set.univ ≠ ∞ := by
  rw [sqWeightedMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  simpa only [Measure.restrict_univ, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two,
    ENNReal.toReal_ofNat, Real.rpow_two] using
    (MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      hf.eLpNorm_lt_top).ne

private theorem sqWeightedMeasure_univ_eq_eLpNorm_two_sq_finitePNeumann
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (f : α → E) :
    sqWeightedMeasure f μ Set.univ = (eLpNorm f 2 μ) ^ (2 : ℕ) := by
  rw [sqWeightedMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  change (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) ∂μ) = _
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [← ENNReal.rpow_natCast,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    ← ENNReal.rpow_mul]
  norm_num

private theorem lintegral_ofReal_norm_rpow_div_ne_top_of_memLp_finitePNeumann
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : FiniteLpExponent} {a : ℝ} {f : α → E}
    (ha : 0 < a) (hf : MemLp f p.exponent μ) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal /
      a ^ (p.exponent.toReal - 2)) ∂μ) ≠ ∞ := by
  let b : ℝ := a ^ (p.exponent.toReal - 2)
  have hb : 0 < b := Real.rpow_pos_of_pos ha _
  have hpoint (x : α) :
      ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal / b) =
        (ENNReal.ofReal b)⁻¹ * ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) := by
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul
      (inv_nonneg.mpr hb.le), ENNReal.ofReal_inv_of_pos hb]
  have hmeas : AEMeasurable
      (fun x ↦ ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal)) μ :=
    (hf.aestronglyMeasurable.norm.aemeasurable.pow aemeasurable_const).ennreal_ofReal
  simp_rw [show a ^ (p.exponent.toReal - 2) = b by rfl, hpoint]
  rw [MeasureTheory.lintegral_const_mul'' _ hmeas]
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_ne_zero_iff.mpr hb))
    (by
      simpa only [← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg] using
        (MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
          (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne
          hf.eLpNorm_lt_top).ne)

private theorem sqWeightedMeasure_neumannReflected_oneLevel_tail_finiteP
    {d : ℕ} [NeZero d] {q r : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d r depth)
    (hr : 2 < r.exponent.toReal) {m : ℤ} {sigma0 eps M level : ℝ}
    (hsigma0 : 0 < sigma0) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hM : 1 ≤ M)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x))
    (hlevel : neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField < level) :
    sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad) volume
        ({x | M * level < ‖hilbertifyVecField u.toH1Function.grad x‖} ∩
          openCubeSet (originCube d m)) ≤
      ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        (sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad) volume
            ({x | level / 2 < ‖hilbertifyVecField u.toH1Function.grad x‖} ∩
              openCubeSet (originCube d m)) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure (sigma0⁻¹ • hilbertifyVecField h.toField) volume
              ({x | eps * level / 2 <
                ‖(sigma0⁻¹ • hilbertifyVecField h.toField) x‖} ∩
                openCubeSet (originCube d m))) := by
  exact sqWeightedMeasure_neumannReflected_oneLevel_tail_originCube G hr hsigma0
    heps heps_one hM u h.toField
    (by
      have hnormalized : MemLp (fun x ↦ HilbertVec.ofVec (h.toField x)) 2
          (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume := by
        simpa only [centeredCubeDomain,
          cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
          using h.euclideanMemL2
      have hrestricted : MemLp (fun x ↦ HilbertVec.ofVec (h.toField x)) 2
          (cubeBoundedMeasurableDomain (originCube d m)).restrictedVolume :=
        ((cubeBoundedMeasurableDomain (originCube d m)).memLp_normalizedVolume_iff
          2 _).mp hnormalized
      have hopen : MemLp (fun x ↦ HilbertVec.ofVec (h.toField x)) 2
          (volume.restrict (openCubeSet (originCube d m))) := by
        simpa only [cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet]
          using hrestricted
      let T : HilbertVec d →L[ℝ] Vec d :=
        (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap
      simpa only [MemVectorL2, volumeMeasureOn, Function.comp_def,
        HilbertVec.toVec_ofVec, T] using! T.comp_memLp' hopen)
    hsolution hlevel

private theorem finiteLp_oneLevel_tail_restrict_neumann
    {d : ℕ} [NeZero d] {q r : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d r depth)
    (hr : 2 < r.exponent.toReal) {m : ℤ} {sigma0 eps M lambda : ℝ}
    (hsigma0 : 0 < sigma0) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hM : 1 ≤ M)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x))
    (hlambda : neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField < lambda) :
    ∀ level, lambda ≤ level →
      sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
          (volume.restrict (openCubeSet (originCube d m)))
          {x | M * level < ‖hilbertifyVecField u.toH1Function.grad x‖} ≤
        (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
            (volume.restrict (openCubeSet (originCube d m)))
            {x | level / 2 < ‖hilbertifyVecField u.toH1Function.grad x‖} +
        ((((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))) *
          sqWeightedMeasure (sigma0⁻¹ • hilbertifyVecField h.toField)
            (volume.restrict (openCubeSet (originCube d m)))
            {x | eps * level / 2 <
              ‖(sigma0⁻¹ • hilbertifyVecField h.toField) x‖} := by
  intro level hlevel
  have htail := sqWeightedMeasure_neumannReflected_oneLevel_tail_finiteP
    G hr hsigma0 heps heps_one hM u h hsolution (hlambda.trans_le hlevel)
  rw [sqWeightedMeasure_restrict_apply_eq_inter_finitePNeumann
      (measurableSet_openCubeSet (originCube d m)),
    sqWeightedMeasure_restrict_apply_eq_inter_finitePNeumann
      (measurableSet_openCubeSet (originCube d m)),
    sqWeightedMeasure_restrict_apply_eq_inter_finitePNeumann
      (measurableSet_openCubeSet (originCube d m))]
  simpa only [mul_add, mul_assoc] using htail

private theorem finiteLp_oneLevel_tail_normalized_neumann
    {d : ℕ} [NeZero d] {q r : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d r depth)
    (hr : 2 < r.exponent.toReal) {m : ℤ} {sigma0 eps M lambda : ℝ}
    (hsigma0 : 0 < sigma0) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hM : 1 ≤ M)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x))
    (hlambda : neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField < lambda) :
    ∀ level, lambda ≤ level →
      sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
          (centeredCubeDomain d m).normalizedVolume
          {x | M * level < ‖hilbertifyVecField u.toH1Function.grad x‖} ≤
        (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
            (centeredCubeDomain d m).normalizedVolume
            {x | level / 2 < ‖hilbertifyVecField u.toH1Function.grad x‖} +
        ((((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))) *
          sqWeightedMeasure (sigma0⁻¹ • hilbertifyVecField h.toField)
            (centeredCubeDomain d m).normalizedVolume
            {x | eps * level / 2 <
              ‖(sigma0⁻¹ • hilbertifyVecField h.toField) x‖} := by
  intro level hlevel
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)
  have hraw := finiteLp_oneLevel_tail_restrict_neumann G hr hsigma0 heps
    heps_one hM u h hsolution hlambda level hlevel
  rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume_finitePNeumann,
    sqWeightedMeasure_smul_measure_finitePNeumann,
    sqWeightedMeasure_smul_measure_finitePNeumann,
    sqWeightedMeasure_smul_measure_finitePNeumann]
  calc
    c * sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
        (volume.restrict (openCubeSet (originCube d m)))
        {x | M * level < ‖hilbertifyVecField u.toH1Function.grad x‖} ≤
      c *
        ((((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
            (volume.restrict (openCubeSet (originCube d m)))
            {x | level / 2 < ‖hilbertifyVecField u.toH1Function.grad x‖} +
          ((((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
            (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
              ENNReal.ofReal (eps ^ (2 : ℕ)))) *
            ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))) *
            sqWeightedMeasure (sigma0⁻¹ • hilbertifyVecField h.toField)
              (volume.restrict (openCubeSet (originCube d m)))
              {x | eps * level / 2 <
                ‖(sigma0⁻¹ • hilbertifyVecField h.toField) x‖}) := by
        simpa only [mul_comm] using mul_le_mul_right hraw c
    _ = _ := by ring

private theorem finiteLp_integrated_tail_of_parameters_neumann
    {d : ℕ} [NeZero d] {q r : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d r depth)
    (hr : 2 < r.exponent.toReal) (hq : 2 < q.exponent.toReal)
    {m : ℤ} {sigma0 M eps lambda0 : ℝ}
    (hsigma0 : 0 < sigma0) (hM : 1 < M) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hlambda0 : 0 < lambda0)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x))
    (hcutoff : neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField <
      lambda0)
    (hsmall :
      (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ)))) *
        ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2)) < 1) :
    ∫⁻ x, ENNReal.ofReal
        (‖hilbertifyVecField u.toH1Function.grad x‖ ^ q.exponent.toReal /
          M ^ (q.exponent.toReal - 2))
        ∂(centeredCubeDomain d m).normalizedVolume ≤
      (sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
          (centeredCubeDomain d m).normalizedVolume Set.univ *
          ENNReal.ofReal (lambda0 ^ (q.exponent.toReal - 2)) +
        ((((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))) *
          ∫⁻ x, ENNReal.ofReal
            (‖(sigma0⁻¹ • hilbertifyVecField h.toField) x‖ ^ q.exponent.toReal /
              (eps / 2) ^ (q.exponent.toReal - 2))
            ∂(centeredCubeDomain d m).normalizedVolume) /
        (1 -
          (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
            (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
              ENNReal.ofReal (eps ^ (2 : ℕ)))) *
            ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2))) := by
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let f : Vec d → HilbertVec d := hilbertifyVecField u.toH1Function.grad
  let g : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField h.toField
  let C : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G
  let theta : ℝ≥0∞ := C *
    (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
      ENNReal.ofReal (eps ^ (2 : ℕ)))
  let B : ℝ≥0∞ := theta * ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))
  have hfraw : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [f, hilbertifyVecField] using
      memHilbertVectorL2_hilbertifyVecField u.toH1Function.grad_memVectorL2
  have hf : MemLp f 2 μ := by
    rw [show μ = ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
      simpa only [μ] using
        centeredCube_normalizedVolume_eq_smul_openCubeVolume_finitePNeumann m]
    exact hfraw.smul_measure ENNReal.ofReal_ne_top
  have hg_base : MemLp (hilbertifyVecField h.toField) q.exponent μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemLp
  have hg : MemLp g q.exponent μ := by
    simpa only [g] using hg_base.const_smul sigma0⁻¹
  have hC : C ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
    (oneStoppingBallCoefficient_ne_top G)
  have htheta : theta ≠ ∞ := ENNReal.mul_ne_top hC (ENNReal.add_ne_top.mpr
    ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
  have hB : B ≠ ∞ := ENNReal.mul_ne_top htheta ENNReal.ofReal_ne_top
  have heps_half : 0 < eps / 2 := by linarith
  have htail : ∀ level, lambda0 ≤ level →
      sqWeightedMeasure f μ {x | M * level < ‖f x‖} ≤
        theta * sqWeightedMeasure f μ {x | level / 2 < ‖f x‖} +
          B * sqWeightedMeasure g μ {x | eps * level / 2 < ‖g x‖} := by
    simpa only [μ, f, g, theta, B, C, mul_assoc] using
      finiteLp_oneLevel_tail_normalized_neumann G hr hsigma0 heps heps_one hM.le
        u h hsolution hcutoff
  simpa only [μ, f, g, theta, B, C] using
    (lp_le_of_oneLevel_weighted_tail hf.aestronglyMeasurable
      hg.aestronglyMeasurable hq (by linarith) (by linarith) heps hlambda0
      (sqWeightedMeasure_univ_ne_top_of_memLp_two_finitePNeumann hf) hB
      (lintegral_ofReal_norm_rpow_div_ne_top_of_memLp_finitePNeumann
        heps_half hg) hsmall htail)

private theorem exists_finiteLp_goodLambda_data_neumann
    {d : ℕ} [NeZero d] (q : FiniteLpExponent)
    (hq : 2 < q.exponent.toReal) :
    ∃ (depth : ℕ) (G : INTERNAL.HarmonicEuclideanGradientGain d
        (finiteLpExponentSuccNeumann q) depth) (M eps : ℝ),
      1 < M ∧ 0 < eps ∧ eps ≤ 1 ∧
        (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^
            (2 - (finiteLpExponentSuccNeumann q).exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2)) < 1 := by
  obtain ⟨⟨depth, G⟩⟩ :=
    INTERNAL.nonempty_harmonicEuclideanGradientGain_finiteTarget_of_pos d
      (Nat.pos_of_ne_zero (NeZero.ne d)) (finiteLpExponentSuccNeumann q)
  let C : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G
  have hC : C ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (by norm_num)) (oneStoppingBallCoefficient_ne_top G)
  obtain ⟨M, eps, hM, heps, heps_one, hsmall⟩ :=
    INTERNAL.exists_strict_goodLambda_parameters hC hq
      (finiteLpExponent_lt_succNeumann q)
  exact ⟨depth, G, M, eps, hM, heps, heps_one, hsmall⟩

private theorem eLpNorm_rpow_eq_lintegral_finitePNeumann
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (p : FiniteLpExponent) (f : α → E) :
    (eLpNorm f p.exponent μ) ^ p.exponent.toReal =
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) ∂μ := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne,
    ← ENNReal.rpow_mul]
  have hp : p.exponent.toReal ≠ 0 :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne |>.ne'
  rw [one_div, inv_mul_cancel₀ hp, ENNReal.rpow_one]
  apply MeasureTheory.lintegral_congr
  intro x
  rw [← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg]

private theorem lintegral_eq_ofReal_mul_div_finitePNeumann
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : FiniteLpExponent} {a : ℝ} {f : α → E}
    (ha : 0 < a) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) ∂μ) =
      ENNReal.ofReal (a ^ (p.exponent.toReal - 2)) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal /
          a ^ (p.exponent.toReal - 2)) ∂μ := by
  let b : ℝ := a ^ (p.exponent.toReal - 2)
  have hb : 0 < b := Real.rpow_pos_of_pos ha _
  have hpoint (x : α) :
      ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) =
        ENNReal.ofReal b * ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal / b) := by
    calc
      ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) =
          ENNReal.ofReal ((‖f x‖ ^ p.exponent.toReal / b) * b) := by
        congr 1
        exact (div_mul_cancel₀ _ hb.ne').symm
      _ = ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal / b) * ENNReal.ofReal b :=
        ENNReal.ofReal_mul (div_nonneg
          (Real.rpow_nonneg (norm_nonneg _) _) hb.le)
      _ = _ := mul_comm _ _
  simp_rw [show a ^ (p.exponent.toReal - 2) = b by rfl, hpoint]
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem divided_moment_eq_finitePNeumann
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : FiniteLpExponent} {a : ℝ} {f : α → E}
    (ha : 0 < a) (hf : MemLp f p.exponent μ) :
    ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal /
      a ^ (p.exponent.toReal - 2)) ∂μ =
      (ENNReal.ofReal (a ^ (p.exponent.toReal - 2)))⁻¹ *
        (eLpNorm f p.exponent μ) ^ p.exponent.toReal := by
  let b : ℝ := a ^ (p.exponent.toReal - 2)
  have hb : 0 < b := Real.rpow_pos_of_pos ha _
  have hpoint (x : α) :
      ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal / b) =
        (ENNReal.ofReal b)⁻¹ * ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) := by
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul
      (inv_nonneg.mpr hb.le), ENNReal.ofReal_inv_of_pos hb]
  have hmeas : AEMeasurable
      (fun x ↦ ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal)) μ :=
    (hf.aestronglyMeasurable.norm.aemeasurable.pow aemeasurable_const).ennreal_ofReal
  simp_rw [show a ^ (p.exponent.toReal - 2) = b by rfl, hpoint]
  rw [MeasureTheory.lintegral_const_mul'' _ hmeas,
    ← eLpNorm_rpow_eq_lintegral_finitePNeumann p f]

private theorem tail_powered_package_finitePNeumann
    {cM D L B cdata X Y : ℝ≥0∞} (hcM : cM ≠ 0) (hcMtop : cM ≠ ∞)
    (htail : cM⁻¹ * X ≤ (L * Y + B * (cdata⁻¹ * Y)) / D) :
    X ≤ (cM * D⁻¹ * (L + B * cdata⁻¹)) * Y := by
  calc
    X = cM * (cM⁻¹ * X) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hcM hcMtop, one_mul]
    _ = (cM⁻¹ * X) * cM := mul_comm _ _
    _ ≤ ((L * Y + B * (cdata⁻¹ * Y)) / D) * cM := mul_le_mul_left htail _
    _ = cM * ((L * Y + B * (cdata⁻¹ * Y)) / D) := mul_comm _ _
    _ = (cM * D⁻¹ * (L + B * cdata⁻¹)) * Y := by
      rw [ENNReal.div_eq_inv_mul]
      ring

private theorem tail_norm_package_finitePNeumann
    {p : ℝ} {cM D L B cdata X Y : ℝ≥0∞} (hp : 0 < p) (hcM : cM ≠ 0)
    (hcMtop : cM ≠ ∞)
    (htail : cM⁻¹ * X ^ p ≤ (L * Y ^ p + B * (cdata⁻¹ * Y ^ p)) / D) :
    X ≤ (cM * D⁻¹ * (L + B * cdata⁻¹)) ^ p⁻¹ * Y := by
  have hpow : X ^ p ≤ (cM * D⁻¹ * (L + B * cdata⁻¹)) * Y ^ p :=
    tail_powered_package_finitePNeumann hcM hcMtop htail
  have hp0 : p ≠ 0 := hp.ne'
  have hpnonneg : 0 ≤ p := hp.le
  calc
    X = X ^ (p * p⁻¹) := by rw [mul_inv_cancel₀ hp0, ENNReal.rpow_one]
    _ = (X ^ p) ^ p⁻¹ := ENNReal.rpow_mul _ _ _
    _ ≤ ((cM * D⁻¹ * (L + B * cdata⁻¹)) * Y ^ p) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow hpow (inv_nonneg.mpr hpnonneg)
    _ = (cM * D⁻¹ * (L + B * cdata⁻¹)) ^ p⁻¹ * Y := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hpnonneg),
        ← ENNReal.rpow_mul, mul_inv_cancel₀ hp0, ENNReal.rpow_one]

private theorem finiteLp_norm_bound_of_moment_tail_neumann
    {p : ℝ} {cM D L B cdata X Y Jf Jg low : ℝ≥0∞}
    (hp : 0 < p) (hcM : cM ≠ 0) (hcMtop : cM ≠ ∞)
    (hJf : X ^ p = cM * Jf) (hJg : Jg = cdata⁻¹ * Y ^ p)
    (htail : Jf ≤ (low + B * Jg) / D) (hlow : low ≤ L * Y ^ p) :
    X ≤ (cM * D⁻¹ * (L + B * cdata⁻¹)) ^ p⁻¹ * Y := by
  apply tail_norm_package_finitePNeumann hp hcM hcMtop
  rw [hJf, ← mul_assoc, ENNReal.inv_mul_cancel hcM hcMtop, one_mul]
  calc
    Jf ≤ (low + B * Jg) / D := htail
    _ ≤ (L * Y ^ p + B * (cdata⁻¹ * Y ^ p)) / D := by
      apply ENNReal.div_le_div_right
      calc
        low + B * Jg ≤ L * Y ^ p + B * Jg := by
          simpa [add_comm] using add_le_add_right hlow (B * Jg)
        _ = _ := by rw [hJg]

private theorem finiteLp_low_term_package_finitePNeumann
    {p : ℝ} {S lam c N₂ Nq : ℝ≥0∞}
    (hp : 2 < p) (hS : S ≤ N₂ ^ (2 : ℕ))
    (hlam : lam ≤ c * N₂) (hN : N₂ ≤ Nq) :
    S * lam ^ (p - 2) ≤ c ^ (p - 2) * Nq ^ p := by
  have he : 0 ≤ p - 2 := by linarith
  calc
    S * lam ^ (p - 2) ≤ N₂ ^ (2 : ℕ) * (c * N₂) ^ (p - 2) :=
      mul_le_mul hS (ENNReal.rpow_le_rpow hlam he) bot_le bot_le
    _ = c ^ (p - 2) * N₂ ^ p := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ he, ← ENNReal.rpow_natCast]
      calc
        N₂ ^ (2 : ℝ) * (c ^ (p - 2) * N₂ ^ (p - 2)) =
            c ^ (p - 2) * (N₂ ^ (2 : ℝ) * N₂ ^ (p - 2)) := by ac_rfl
        _ = c ^ (p - 2) * N₂ ^ (2 + (p - 2)) := by
          rw [ENNReal.rpow_add_of_nonneg _ _ (by norm_num) he]
        _ = c ^ (p - 2) * N₂ ^ p := by
          congr 2
          ring
    _ ≤ c ^ (p - 2) * Nq ^ p := by gcongr

private theorem finiteLp_low_term_of_l2_control_neumann
    {d : ℕ} {m : ℤ} {q : FiniteLpExponent}
    {f g : Vec d → HilbertVec d} {lambda c : ℝ}
    (hgq : MemLp g q.exponent (centeredCubeDomain d m).normalizedVolume)
    (hq : 2 < q.exponent.toReal)
    (henergy : eLpNorm f 2 (centeredCubeDomain d m).normalizedVolume ≤
      eLpNorm g 2 (centeredCubeDomain d m).normalizedVolume)
    (hc : 0 ≤ c) (hlambda : 0 ≤ lambda)
    (hlambda_bound : lambda ≤ c *
      (eLpNorm g q.exponent (centeredCubeDomain d m).normalizedVolume).toReal) :
    sqWeightedMeasure f (centeredCubeDomain d m).normalizedVolume Set.univ *
        ENNReal.ofReal (lambda ^ (q.exponent.toReal - 2)) ≤
      (ENNReal.ofReal c) ^ (q.exponent.toReal - 2) *
        (eLpNorm g q.exponent (centeredCubeDomain d m).normalizedVolume) ^
          q.exponent.toReal := by
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let : IsProbabilityMeasure μ := ⟨by
    dsimp only [μ]
    exact (centeredCubeDomain d m).normalizedVolume_apply_univ⟩
  have htwoq : (2 : ℝ≥0∞) ≤ q.exponent := by
    apply le_of_lt
    apply (ENNReal.toReal_lt_toReal (a := (2 : ℝ≥0∞)) (b := q.exponent)
      (by norm_num) q.lt_top.ne).mp
    simpa using hq
  have htwoqnorm : eLpNorm g 2 μ ≤ eLpNorm g q.exponent μ :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le htwoq hgq.aestronglyMeasurable
  have hS : sqWeightedMeasure f μ Set.univ ≤ (eLpNorm g 2 μ) ^ (2 : ℕ) := by
    rw [sqWeightedMeasure_univ_eq_eLpNorm_two_sq_finitePNeumann]
    exact pow_le_pow_left₀ bot_le henergy 2
  have hSq : sqWeightedMeasure f μ Set.univ ≤
      (eLpNorm g q.exponent μ) ^ (2 : ℕ) :=
    hS.trans (pow_le_pow_left₀ bot_le htwoqnorm 2)
  have hlamENN : ENNReal.ofReal lambda ≤
      ENNReal.ofReal c * eLpNorm g q.exponent μ := by
    calc
      ENNReal.ofReal lambda ≤ ENNReal.ofReal
          (c * (eLpNorm g q.exponent μ).toReal) :=
        ENNReal.ofReal_le_ofReal hlambda_bound
      _ = ENNReal.ofReal c * eLpNorm g q.exponent μ := by
        rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hgq.eLpNorm_lt_top.ne]
  rw [show ENNReal.ofReal (lambda ^ (q.exponent.toReal - 2)) =
      (ENNReal.ofReal lambda) ^ (q.exponent.toReal - 2) by
    exact (ENNReal.ofReal_rpow_of_nonneg (p := q.exponent.toReal - 2)
      hlambda (by linarith)).symm]
  exact finiteLp_low_term_package_finitePNeumann hq hSq hlamENN le_rfl

private theorem toReal_eLpNorm_two_sq_eq_integral_finitePNeumann
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    (ENNReal.toReal (eLpNorm f 2 μ)) ^ (2 : ℕ) =
      ∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ := by
  have hpow : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  have hnorm := hf.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have hsq : (ENNReal.toReal (eLpNorm f 2 μ)) ^ (2 : ℕ) =
      ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
    rw [hnorm, hpow]
    have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ :=
      MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
    rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hnonneg
  calc
    (ENNReal.toReal (eLpNorm f 2 μ)) ^ (2 : ℕ) =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := hsq
    _ = _ := by
      congr 1 with x
      rw [Real.rpow_two]

private theorem neumannReflectedGoodLambdaCutoff_sq_eq_normalized_energy
    {d : ℕ} {m : ℤ} (depth : ℕ) (eps sigma0 : ℝ)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m))) (H : Vec d → Vec d) :
    neumannReflectedGoodLambdaCutoff m depth eps sigma0 u H ^ (2 : ℕ) =
      (3 : ℝ) ^ d * (10 * (3 : ℝ) ^ depth) ^ d *
        ((∫ x, ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ)
            ∂(centeredCubeDomain d m).normalizedVolume) +
          (eps⁻¹) ^ (2 : ℕ) *
            ∫ x, ‖sigma0⁻¹ • hilbertifyVecField H x‖ ^ (2 : ℕ)
              ∂(centeredCubeDomain d m).normalizedVolume) := by
  let s : ℝ := cubeScaleFactor (originCube d m)
  let L : ℝ := 10 * (3 : ℝ) ^ depth
  let V : ℝ := cubeVolume (originCube d m)
  have hs : 0 < s := by
    dsimp only [s]
    simpa [cubeScaleFactor] using! zpow_pos (by norm_num : (0 : ℝ) < 3) m
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hV : V = s ^ d := by simp only [V, s, cubeVolume_eq_scaleFactor_pow]
  have hnormal : (ENNReal.ofReal (V⁻¹)).toReal = V⁻¹ := by
    rw [ENNReal.toReal_ofReal]
    exact inv_nonneg.mpr (by rw [hV]; positivity)
  have hmeasure : (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal (V⁻¹) • volume.restrict (openCubeSet (originCube d m)) := by
    simpa only [V] using
      centeredCube_normalizedVolume_eq_smul_openCubeVolume_finitePNeumann m
  have hIu :
      (∫ x, ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ)
          ∂(centeredCubeDomain d m).normalizedVolume) =
        V⁻¹ * ∫ x in openCubeSet (originCube d m),
          ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume := by
    rw [hmeasure, MeasureTheory.integral_smul_measure, hnormal]
    exact smul_eq_mul _ _
  have hIH :
      (∫ x, ‖sigma0⁻¹ • hilbertifyVecField H x‖ ^ (2 : ℕ)
          ∂(centeredCubeDomain d m).normalizedVolume) =
        V⁻¹ * ∫ x in openCubeSet (originCube d m),
          ‖sigma0⁻¹ • hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume := by
    rw [hmeasure, MeasureTheory.integral_smul_measure, hnormal]
    exact smul_eq_mul _ _
  have hscaled :
      (∫ x in openCubeSet (originCube d m),
          ‖sigma0⁻¹ • hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume) =
        (sigma0⁻¹) ^ (2 : ℕ) *
          ∫ x in openCubeSet (originCube d m),
            ‖hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext x
    rw [norm_smul, Real.norm_eq_abs]
    calc
      (|sigma0⁻¹| * ‖hilbertifyVecField H x‖) ^ (2 : ℕ) =
          |sigma0⁻¹| ^ (2 : ℕ) * ‖hilbertifyVecField H x‖ ^ (2 : ℕ) := by ring
      _ = _ := by rw [sq_abs]
  have hcoef : ((2 * ((s / 2) / L)) ^ d)⁻¹ * (3 : ℝ) ^ d =
      (3 : ℝ) ^ d * L ^ d * V⁻¹ := by
    rw [hV, ← inv_pow]
    field_simp [hs.ne', hL.ne']
    rw [div_pow]
    exact div_mul_cancel₀ _ (pow_pos hs _).ne'
  rw [neumannReflectedGoodLambdaCutoff, neumannReflectedSourceSquaredEnergy,
    Real.sq_sqrt]
  · dsimp only [reflectedStoppingRadius]
    rw [show cubeRadius (originCube d m) = s / 2 by
      dsimp only [s, cubeRadius]
      ring]
    rw [show 10 * (3 : ℝ) ^ depth = L by rfl, hIu, hIH, hscaled]
    calc
      ((2 * (s / 2 / L)) ^ d)⁻¹ *
          ((3 : ℝ) ^ d *
            ((∫ x in openCubeSet (originCube d m),
              ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) +
              (eps⁻¹) ^ (2 : ℕ) * (sigma0⁻¹) ^ (2 : ℕ) *
                ∫ x in openCubeSet (originCube d m),
                  ‖hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume)) =
          (((2 * (s / 2 / L)) ^ d)⁻¹ * (3 : ℝ) ^ d) *
            ((∫ x in openCubeSet (originCube d m),
              ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) +
              (eps⁻¹) ^ (2 : ℕ) * (sigma0⁻¹) ^ (2 : ℕ) *
                ∫ x in openCubeSet (originCube d m),
                  ‖hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume) := by ring
      _ = _ := by rw [hcoef]; ring
  · apply mul_nonneg
    · exact inv_nonneg.mpr (pow_nonneg
        (mul_nonneg (by norm_num) (reflectedStoppingRadius_pos m depth).le) _)
    · apply mul_nonneg (pow_nonneg (by norm_num) _)
      apply add_nonneg
      · exact MeasureTheory.integral_nonneg fun _ ↦ sq_nonneg _
      · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (MeasureTheory.integral_nonneg fun _ ↦ sq_nonneg _)

private theorem neumannReflectedGoodLambdaCutoff_le_normalized_datum_energy
    {d : ℕ} [NeZero d] {m : ℤ} {q : FiniteLpExponent}
    (depth : ℕ) {eps sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x)) :
    neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField ≤
      Real.sqrt (((3 : ℝ) ^ d * (10 * (3 : ℝ) ^ depth) ^ d) *
        (1 + (eps⁻¹) ^ (2 : ℕ))) *
        Real.sqrt (∫ x, ‖sigma0⁻¹ • hilbertifyVecField h.toField x‖ ^ (2 : ℕ)
          ∂(centeredCubeDomain d m).normalizedVolume) := by
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let f : Vec d → HilbertVec d := hilbertifyVecField u.toH1Function.grad
  let g : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField h.toField
  let K : ℝ := (3 : ℝ) ^ d * (10 * (3 : ℝ) ^ depth) ^ d
  let E : ℝ := ∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ
  let A : ℝ := ∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ
  let C : ℝ := Real.sqrt (K * (1 + (eps⁻¹) ^ (2 : ℕ)))
  have hfraw : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [f, hilbertifyVecField] using
      memHilbertVectorL2_hilbertifyVecField u.toH1Function.grad_memVectorL2
  have hf : MemLp f 2 μ := by
    rw [show μ = ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
      simpa only [μ] using
        centeredCube_normalizedVolume_eq_smul_openCubeVolume_finitePNeumann m]
    exact hfraw.smul_measure ENNReal.ofReal_ne_top
  have hgbase : MemLp (hilbertifyVecField h.toField) 2 μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemL2
  have hg : MemLp g 2 μ := by simpa only [g] using hgbase.const_smul sigma0⁻¹
  have hnormSource := centeredCubeH1MeanZeroScalarDivergence_cz_two
    m sigma0 h.toLpTwo u hsigma0 hsolution
  have hnorm : eLpNorm f 2 μ ≤ eLpNorm g 2 μ := by
    rw [eLpNorm_const_smul]
    rw [← ofReal_norm, Real.norm_of_nonneg (inv_nonneg.mpr hsigma0.le),
      ENNReal.ofReal_inv_of_pos hsigma0]
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm, FiniteLpExponent.two_exponent,
      euclideanNorm_eq_norm_ofVec, eLpNorm_norm, μ, f, g, hilbertifyVecField]
      using! hnormSource
  have hnormR := (ENNReal.toReal_le_toReal hf.eLpNorm_lt_top.ne
      hg.eLpNorm_lt_top.ne).mpr hnorm
  have hsq := (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hnormR
  rw [toReal_eLpNorm_two_sq_eq_integral_finitePNeumann hf,
    toReal_eLpNorm_two_sq_eq_integral_finitePNeumann hg] at hsq
  have hAE : A ≤ E := by simpa only [A, E, f, g] using hsq
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hE0 : 0 ≤ E := MeasureTheory.integral_nonneg fun _ ↦ sq_nonneg _
  have hsum : A + (eps⁻¹) ^ (2 : ℕ) * E ≤
      (1 + (eps⁻¹) ^ (2 : ℕ)) * E := by
    have he : 0 ≤ (eps⁻¹) ^ (2 : ℕ) := sq_nonneg _
    nlinarith [hAE]
  calc
    neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField =
        Real.sqrt
          (neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField ^
            (2 : ℕ)) := by
      symm
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
        (neumannReflectedGoodLambdaCutoff_nonneg m depth eps sigma0 u h.toField)]
    _ = Real.sqrt (K * (A + (eps⁻¹) ^ (2 : ℕ) * E)) := by
      rw [neumannReflectedGoodLambdaCutoff_sq_eq_normalized_energy]
      rfl
    _ ≤ Real.sqrt (K * ((1 + (eps⁻¹) ^ (2 : ℕ)) * E)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsum hK.le)
    _ = C * Real.sqrt E := by
      dsimp only [C]
      rw [← mul_assoc, Real.sqrt_mul]
      positivity
    _ = _ := rfl

private theorem neumannReflectedGoodLambdaCutoff_le_q_datum_norm
    {d : ℕ} [NeZero d] {m : ℤ} {q : FiniteLpExponent} (depth : ℕ)
    {eps sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x))
    (hq : 2 < q.exponent.toReal) :
    neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField ≤
      Real.sqrt (((3 : ℝ) ^ d * (10 * (3 : ℝ) ^ depth) ^ d) *
        (1 + (eps⁻¹) ^ (2 : ℕ))) *
      (eLpNorm (sigma0⁻¹ • hilbertifyVecField h.toField) q.exponent
        (centeredCubeDomain d m).normalizedVolume).toReal := by
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let g : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField h.toField
  let C : ℝ := Real.sqrt (((3 : ℝ) ^ d * (10 * (3 : ℝ) ^ depth) ^ d) *
    (1 + (eps⁻¹) ^ (2 : ℕ)))
  have hgbase : MemLp (hilbertifyVecField h.toField) 2 μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemL2
  have hg2 : MemLp g 2 μ := by simpa only [g] using hgbase.const_smul sigma0⁻¹
  have hgqbase : MemLp (hilbertifyVecField h.toField) q.exponent μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemLp
  have hgq : MemLp g q.exponent μ := by
    simpa only [g] using hgqbase.const_smul sigma0⁻¹
  let : IsProbabilityMeasure μ := ⟨by
    dsimp only [μ]
    exact (centeredCubeDomain d m).normalizedVolume_apply_univ⟩
  have htwoq : (2 : ℝ≥0∞) ≤ q.exponent := by
    apply le_of_lt
    apply (ENNReal.toReal_lt_toReal (a := (2 : ℝ≥0∞)) (b := q.exponent)
      (by norm_num) q.lt_top.ne).mp
    simpa using hq
  have hnorm : eLpNorm g 2 μ ≤ eLpNorm g q.exponent μ :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le htwoq hgq.aestronglyMeasurable
  have hnormR : (eLpNorm g 2 μ).toReal ≤ (eLpNorm g q.exponent μ).toReal :=
    (ENNReal.toReal_le_toReal hg2.eLpNorm_lt_top.ne hgq.eLpNorm_lt_top.ne).mpr hnorm
  have hmoment : (eLpNorm g 2 μ).toReal ^ (2 : ℕ) =
      ∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ :=
    toReal_eLpNorm_two_sq_eq_integral_finitePNeumann hg2
  have hsqrt : Real.sqrt (∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ) =
      (eLpNorm g 2 μ).toReal := by
    rw [← hmoment, Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hcut := neumannReflectedGoodLambdaCutoff_le_normalized_datum_energy
    (eps := eps) depth hsigma0 u h hsolution
  calc
    neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField ≤
        C * Real.sqrt (∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ) := by
      simpa only [μ, g, C] using! hcut
    _ = C * (eLpNorm g 2 μ).toReal := by rw [hsqrt]
    _ ≤ C * (eLpNorm g q.exponent μ).toReal := by
      apply mul_le_mul_of_nonneg_left hnormR
      dsimp only [C]
      positivity

private theorem finiteLp_norm_bound_of_parameters_neumann
    {d : ℕ} [NeZero d] {q r : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d r depth)
    (hr : 2 < r.exponent.toReal) (hq : 2 < q.exponent.toReal)
    {m : ℤ} {sigma0 M eps lambda0 : ℝ}
    (hsigma0 : 0 < sigma0) (hM : 1 < M) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hlambda0 : 0 < lambda0)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x))
    (hcutoff : neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField < lambda0)
    (hsmall :
      (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ)))) *
        ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2)) < 1)
    {L : ℝ≥0∞}
    (hlow :
      sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
          (centeredCubeDomain d m).normalizedVolume Set.univ *
          ENNReal.ofReal (lambda0 ^ (q.exponent.toReal - 2)) ≤
        L * (eLpNorm (sigma0⁻¹ • hilbertifyVecField h.toField) q.exponent
          (centeredCubeDomain d m).normalizedVolume) ^ q.exponent.toReal) :
    eLpNorm (hilbertifyVecField u.toH1Function.grad) q.exponent
        (centeredCubeDomain d m).normalizedVolume ≤
      (ENNReal.ofReal (M ^ (q.exponent.toReal - 2)) *
        (1 -
          (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
            (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
              ENNReal.ofReal (eps ^ (2 : ℕ)))) *
            ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2)))⁻¹ *
        (L +
          ((((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
            (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
              ENNReal.ofReal (eps ^ (2 : ℕ)))) *
            ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))) *
            (ENNReal.ofReal ((eps / 2) ^ (q.exponent.toReal - 2)))⁻¹)) ^
          (q.exponent.toReal)⁻¹ *
        eLpNorm (sigma0⁻¹ • hilbertifyVecField h.toField) q.exponent
          (centeredCubeDomain d m).normalizedVolume := by
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let f : Vec d → HilbertVec d := hilbertifyVecField u.toH1Function.grad
  let g : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField h.toField
  let theta : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
    (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
      ENNReal.ofReal (eps ^ (2 : ℕ)))
  let B : ℝ≥0∞ := theta * ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))
  let cM : ℝ≥0∞ := ENNReal.ofReal (M ^ (q.exponent.toReal - 2))
  let cdata : ℝ≥0∞ := ENNReal.ofReal ((eps / 2) ^ (q.exponent.toReal - 2))
  let D : ℝ≥0∞ := 1 - theta * ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2))
  have hepshalf : 0 < eps / 2 := by linarith
  have hcM : cM ≠ 0 := by
    dsimp only [cM]
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hcMtop : cM ≠ ∞ := ENNReal.ofReal_ne_top
  have htail := finiteLp_integrated_tail_of_parameters_neumann G hr hq hsigma0 hM
    heps heps_one hlambda0 u h hsolution hcutoff hsmall
  have hJf : (eLpNorm f q.exponent μ) ^ q.exponent.toReal =
      cM * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal /
        M ^ (q.exponent.toReal - 2)) ∂μ := by
    rw [eLpNorm_rpow_eq_lintegral_finitePNeumann,
      lintegral_eq_ofReal_mul_div_finitePNeumann (p := q) (a := M)
        (f := f) (by linarith)]
  have hgbase : MemLp (hilbertifyVecField h.toField) q.exponent μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemLp
  have hg : MemLp g q.exponent μ := by
    simpa only [g] using hgbase.const_smul sigma0⁻¹
  have hJg : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ q.exponent.toReal /
      (eps / 2) ^ (q.exponent.toReal - 2)) ∂μ) =
      cdata⁻¹ * (eLpNorm g q.exponent μ) ^ q.exponent.toReal := by
    simpa only [cdata] using divided_moment_eq_finitePNeumann hepshalf hg
  have htail' :
      (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal /
        M ^ (q.exponent.toReal - 2)) ∂μ) ≤
        (sqWeightedMeasure f μ Set.univ *
            ENNReal.ofReal (lambda0 ^ (q.exponent.toReal - 2)) +
          B * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ q.exponent.toReal /
            (eps / 2) ^ (q.exponent.toReal - 2)) ∂μ) / D := by
    simpa only [μ, f, g, theta, B, D] using htail
  have hlow' : sqWeightedMeasure f μ Set.univ *
      ENNReal.ofReal (lambda0 ^ (q.exponent.toReal - 2)) ≤
        L * (eLpNorm g q.exponent μ) ^ q.exponent.toReal := by
    simpa only [μ, f, g] using hlow
  have hp : 0 < q.exponent.toReal := by linarith
  simpa only [μ, f, g, theta, B, cM, cdata, D] using
    (finiteLp_norm_bound_of_moment_tail_neumann
      (p := q.exponent.toReal) (L := L) (B := B) hp
      hcM hcMtop hJf hJg htail' hlow')

private theorem finiteLp_final_coefficient_ne_top_neumann
    {p : ℝ} {cM rho L B cdata : ℝ≥0∞}
    (hp : 0 < p) (hcMtop : cM ≠ ∞) (hrho : rho < 1)
    (hLtop : L ≠ ∞) (hBtop : B ≠ ∞) (hcdata : cdata ≠ 0) :
    (cM * (1 - rho)⁻¹ * (L + B * cdata⁻¹)) ^ p⁻¹ ≠ ∞ := by
  apply ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp.le)
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top hcMtop
    exact ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hrho))
  · apply ENNReal.add_ne_top.mpr
    exact ⟨hLtop, ENNReal.mul_ne_top hBtop (ENNReal.inv_ne_top.mpr hcdata)⟩

/-- Centered-cube Neumann Calderón--Zygmund estimate above the energy exponent. -/
theorem centeredCubeH1MeanZeroNeumannDivergence_cz_of_two_lt
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (hq : 2 < q.exponent.toReal) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h : CubeEuclideanL2LpField (originCube d m) q)
      (u : H1MeanZeroFunction (openCubeSet (originCube d m))), 0 < sigma0 →
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
        (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x) →
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        u.toH1Function.grad ≤ C * (ENNReal.ofReal sigma0)⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
            h.toField := by
  obtain ⟨depth, G, M, eps, hM, heps, heps_one, hsmall⟩ :=
    exists_finiteLp_goodLambda_data_neumann (d := d) q hq
  let theta : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
    (ENNReal.ofReal ((M / 2) ^
      (2 - (finiteLpExponentSuccNeumann q).exponent.toReal)) +
      ENNReal.ofReal (eps ^ (2 : ℕ)))
  let B : ℝ≥0∞ := theta * ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))
  let cM : ℝ≥0∞ := ENNReal.ofReal (M ^ (q.exponent.toReal - 2))
  let cdata : ℝ≥0∞ := ENNReal.ofReal ((eps / 2) ^ (q.exponent.toReal - 2))
  let rho : ℝ≥0∞ := theta * ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2))
  let Ccut : ℝ := Real.sqrt (((3 : ℝ) ^ d * (10 * (3 : ℝ) ^ depth) ^ d) *
    (1 + (eps⁻¹) ^ (2 : ℕ)))
  let L : ℝ≥0∞ := (ENNReal.ofReal (2 * Ccut)) ^ (q.exponent.toReal - 2)
  let C : ℝ≥0∞ :=
    (cM * (1 - rho)⁻¹ * (L + B * cdata⁻¹)) ^ (q.exponent.toReal)⁻¹
  have hp : 0 < q.exponent.toReal := by linarith
  have hCtop : C ≠ ∞ := by
    apply finiteLp_final_coefficient_ne_top_neumann hp ENNReal.ofReal_ne_top
    · simpa only [rho, theta] using hsmall
    · dsimp only [L]
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
    · dsimp only [B, theta]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
            (oneStoppingBallCoefficient_ne_top G))
          (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩))
        ENNReal.ofReal_ne_top
    · dsimp only [cdata]
      exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  refine ⟨C, lt_top_iff_ne_top.mpr hCtop, ?_⟩
  intro m sigma0 h u hsigma0 hsolution
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let f : Vec d → HilbertVec d := hilbertifyVecField u.toH1Function.grad
  let g : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField h.toField
  have henergy : eLpNorm f 2 μ ≤ eLpNorm g 2 μ := by
    rw [eLpNorm_const_smul]
    rw [← ofReal_norm,
      Real.norm_of_nonneg (inv_nonneg.mpr hsigma0.le),
      ENNReal.ofReal_inv_of_pos hsigma0]
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm, FiniteLpExponent.two_exponent,
      euclideanNorm_eq_norm_ofVec, eLpNorm_norm, μ, f, g, hilbertifyVecField] using!
      (centeredCubeH1MeanZeroScalarDivergence_cz_two m sigma0 h.toLpTwo u hsigma0
        hsolution)
  have hgbase : MemLp (hilbertifyVecField h.toField) q.exponent μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemLp
  have hg : MemLp g q.exponent μ := by simpa only [g] using hgbase.const_smul sigma0⁻¹
  by_cases hYzero : eLpNorm g q.exponent μ = 0
  · let : IsProbabilityMeasure μ := ⟨by
      dsimp only [μ]
      exact (centeredCubeDomain d m).normalizedVolume_apply_univ⟩
    have htwoq : (2 : ℝ≥0∞) ≤ q.exponent := by
      apply le_of_lt
      apply (ENNReal.toReal_lt_toReal (a := (2 : ℝ≥0∞)) (b := q.exponent)
        (by norm_num) q.lt_top.ne).mp
      simpa using hq
    have hg2zero : eLpNorm g 2 μ = 0 :=
      le_zero_iff.mp ((MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
        htwoq hg.aestronglyMeasurable).trans_eq hYzero)
    have hf2zero : eLpNorm f 2 μ = 0 := le_zero_iff.mp (henergy.trans_eq hg2zero)
    have hfraw : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))) := by
      simpa only [f, hilbertifyVecField] using
        memHilbertVectorL2_hilbertifyVecField u.toH1Function.grad_memVectorL2
    have hf2 : MemLp f 2 μ := by
      rw [show μ = ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
          volume.restrict (openCubeSet (originCube d m)) by
        simpa only [μ] using
          centeredCube_normalizedVolume_eq_smul_openCubeVolume_finitePNeumann m]
      exact hfraw.smul_measure ENNReal.ofReal_ne_top
    have hfae : f =ᵐ[μ] 0 :=
      (MeasureTheory.eLpNorm_eq_zero_iff hf2.aestronglyMeasurable (by norm_num)).mp hf2zero
    have hfqzero : eLpNorm f q.exponent μ = 0 :=
      MeasureTheory.eLpNorm_eq_zero_of_ae_zero hfae
    have htargetzero : (centeredCubeDomain d m).normalizedEuclideanLpENorm
        q.exponent u.toH1Function.grad = 0 := by
      simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
        BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
        MeasureTheory.eLpNorm_norm, f, μ, hilbertifyVecField] using! hfqzero
    rw [htargetzero]
    exact bot_le
  · let lambda0 : ℝ := neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField +
      Ccut * (eLpNorm g q.exponent μ).toReal
    have hYpos : 0 < (eLpNorm g q.exponent μ).toReal :=
      ENNReal.toReal_pos hYzero hg.eLpNorm_lt_top.ne
    have hCcut : 0 < Ccut := by
      dsimp only [Ccut]
      positivity
    have hcut := neumannReflectedGoodLambdaCutoff_le_q_datum_norm (eps := eps)
      depth hsigma0 u h hsolution hq
    have hcut' : neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField ≤
        Ccut * (eLpNorm g q.exponent μ).toReal := by
      simpa only [μ, g, Ccut] using hcut
    have hlambda0 : 0 < lambda0 := by
      dsimp only [lambda0]
      exact add_pos_of_nonneg_of_pos
        (neumannReflectedGoodLambdaCutoff_nonneg m depth eps sigma0 u h.toField)
        (mul_pos hCcut hYpos)
    have hcutoff : neumannReflectedGoodLambdaCutoff m depth eps sigma0 u h.toField <
        lambda0 := by
      dsimp only [lambda0]
      nlinarith [hcut']
    have hlambdaBound : lambda0 ≤ 2 * Ccut * (eLpNorm g q.exponent μ).toReal := by
      dsimp only [lambda0]
      nlinarith [hcut']
    have hlow := finiteLp_low_term_of_l2_control_neumann (q := q) (f := f) (g := g)
      hg hq henergy (by nlinarith [hCcut]) hlambda0.le hlambdaBound
    have hbound := finiteLp_norm_bound_of_parameters_neumann G
      (hq.trans (finiteLpExponent_lt_succNeumann q)) hq hsigma0 hM heps heps_one
      hlambda0 u h hsolution hcutoff (by
        simpa only [finiteLpExponentSuccNeumann_toReal] using hsmall) (L := L) (by
          simpa only [μ, f, g, lambda0, L, Ccut] using hlow)
    have hleft : (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        u.toH1Function.grad = eLpNorm f q.exponent μ := by
      simp only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
        BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
        MeasureTheory.eLpNorm_norm, f, μ]
      rfl
    rw [hleft]
    rw [MeasureTheory.eLpNorm_const_smul] at hbound
    rw [← ofReal_norm,
      Real.norm_of_nonneg (inv_nonneg.mpr hsigma0.le),
      ENNReal.ofReal_inv_of_pos hsigma0] at hbound
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
      MeasureTheory.eLpNorm_norm, μ, f, g, C, theta, B, cM, cdata, rho, L,
      mul_assoc] using! hbound

end CubeCalderonZygmund

end

end Homogenization
