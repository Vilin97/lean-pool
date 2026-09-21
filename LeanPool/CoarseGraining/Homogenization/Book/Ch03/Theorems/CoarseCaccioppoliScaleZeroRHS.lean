/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliScaleZeroCore
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliScalarEnvelopes

/-! # Coarse Caccioppoli Scale Zero RHS -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Scale-zero Caccioppoli RHS bridge helpers

This file contains the parent-energy conversions, deterministic note-RHS
translations, and scalar monotonicity helpers used by the scale-zero
Caccioppoli endpoint assembly.

## Audit tag

Claim: convert deterministic note RHS quantities at scale zero into the public
Chapter 3 RHS forms, including parent-energy and scalar monotonicity bridges.

Downstream target: `CoarseCaccioppoliScaleZeroBridge.lean`.  Keep this file to
RHS translations and avoid new public `*Theory` surfaces.
-/

noncomputable section

open scoped ENNReal

theorem boundary_localPatch_deterministic_note_from_public_standardExplicitBudgetSplit
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : BoundaryCaccioppoliDatum Q a x) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    let Csol : ℝ := fullVectorPoincareCubeConstant Q
    let Calpha : ℝ := coarseCaccioppoliLocalPatchBufferedAlphaBudget Q s Csol
    let Ccross : ℝ := coarseCaccioppoliLocalPatchBufferedCrossBudget Q s Csol
    let Cnote : ℝ :=
      coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
        Q (pointwiseCoeffFor Q a) s t
        ((Fintype.card (Fin d) : ℝ) * Calpha)
        ((Fintype.card (Fin d) : ℝ) * Ccross)
    0 ≤ Cnote ∧
      coarseCaccioppoliLocalEnergyRadiusProfile Q x
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic y) (1 / 3 : ℝ) ≤
        coarseCaccioppoliBoundaryNoteRhs Q (pointwiseCoeffFor Q a) s t Cnote
          (coarseCaccioppoliHarmonicL2Sq Q (pointwiseCoeffFor Q a)
            u.toPointwiseAHarmonic) := by
  have hzero :
      LocalizedZeroTraceFunctionOn (openCubeSet Q)
        (coarseCaccioppoliLocalOpenCube Q x 1) u.toH1.toFun := by
    simpa [Ch02.cubeDomain, coarseCaccioppoliLocalOpenCube_one_eq_openCubeAtScale Q x]
      using u.zeroTraceOnBoundaryPatch
  exact
    coarseCaccioppoli_boundary_qone_standard_note_of_closedCubeEllipticity_of_localPatchBuffered_constantFamily_of_localizedZeroTraceOnLocalOpenCube_explicitBudgetSplit
      (Q := Q) (center := x) (a := pointwiseCoeffFor Q a) (s := s) (t := t)
      (u := u.toPointwiseAHarmonic) hzero hs ht hst
      (pointwiseCoeffFor_isEllipticFieldOn_cubeSet Q a)

theorem boundaryCaccioppoliParentL2Sq_eq_harmonicL2Sq_pointwise
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : BoundaryCaccioppoliDatum Q a x) :
    boundaryCaccioppoliParentL2Sq u =
      coarseCaccioppoliHarmonicL2Sq Q (pointwiseCoeffFor Q a)
        u.toPointwiseAHarmonic := by
  let A : CoeffField d := pointwiseCoeffFor Q a
  let w : AHarmonicFunction A (openCubeSet Q) := u.toPointwiseAHarmonic
  let f : Vec d → ℝ := fun y => w.toH1 y
  have hf :
      MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [f] using memLp_harmonicFunction_normalizedCubeMeasure Q A w
  have hsq_integral :
      ∫ y in openCubeSet Q, f y ^ (2 : ℕ) ∂MeasureTheory.volume =
        cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℕ) := by
    have hmul :=
      setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow
        Q f hf
    calc
      ∫ y in openCubeSet Q, f y ^ (2 : ℕ) ∂MeasureTheory.volume =
          ∫ y in openCubeSet Q, f y * f y ∂MeasureTheory.volume := by
        apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
        intro y hy
        ring
      _ =
          cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℝ) := hmul
      _ =
          cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℕ) := by
        rw [Real.rpow_two]
  have hvol_ne : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  unfold boundaryCaccioppoliParentL2Sq normalizedL2SqOnSet normalizedSetAverage
    coarseCaccioppoliHarmonicL2Sq
  calc
    (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
        ∫ y in openCubeSet Q, u.toH1.toFun y ^ (2 : ℕ) ∂MeasureTheory.volume =
        (cubeVolume Q)⁻¹ *
          ∫ y in openCubeSet Q, f y ^ (2 : ℕ) ∂MeasureTheory.volume := by
      simp [f, w, A, BoundaryCaccioppoliDatum.toPointwiseAHarmonic]
    _ =
        (cubeVolume Q)⁻¹ *
          (cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℕ)) := by
      rw [hsq_integral]
    _ = (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℕ) := by
      rw [← mul_assoc, inv_mul_cancel₀ hvol_ne, one_mul]

theorem interiorCaccioppoliParentOscillationL2Sq_eq_harmonicL2Sq_pointwise_normalizeMeanZero
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q))]
    (u : CubeSolution Q a) :
    interiorCaccioppoliParentOscillationL2Sq Q a u =
      coarseCaccioppoliHarmonicL2Sq Q (pointwiseCoeffFor Q a)
        u.toPointwiseAHarmonic.normalizeMeanZero := by
  let A : CoeffField d := pointwiseCoeffFor Q a
  let w : AHarmonicFunction A (openCubeSet Q) :=
    u.toPointwiseAHarmonic.normalizeMeanZero
  let f : Vec d → ℝ := fun y => w.toH1 y
  have hf :
      MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [f] using memLp_harmonicFunction_normalizedCubeMeasure Q A w
  have havg :
      integralAverage (openCubeSet Q) (fun y => u.toH1.toFun y) =
        Ch01.Legacy.normalizedAverage Q u.toH1.toFun := by
    simpa [Ch01.Legacy.normalizedAverage] using
      (cubeAverage_eq_integralAverage_openCubeSet Q
        (fun y => u.toH1.toFun y)).symm
  have hf_pointwise :
      ∀ y : Vec d, f y =
        u.toH1.toFun y - Ch01.Legacy.normalizedAverage Q u.toH1.toFun := by
    intro y
    simp [f, w, A, CubeSolution.toPointwiseAHarmonic, havg]
  have hsq_integral :
      ∫ y in openCubeSet Q, f y ^ (2 : ℕ) ∂MeasureTheory.volume =
        cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℕ) := by
    have hmul :=
      setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow
        Q f hf
    calc
      ∫ y in openCubeSet Q, f y ^ (2 : ℕ) ∂MeasureTheory.volume =
          ∫ y in openCubeSet Q, f y * f y ∂MeasureTheory.volume := by
        apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
        intro y hy
        ring
      _ =
          cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℝ) := hmul
      _ =
          cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℕ) := by
        rw [Real.rpow_two]
  have hvol_ne : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  unfold interiorCaccioppoliParentOscillationL2Sq normalizedL2SqOnSet
    normalizedSetAverage coarseCaccioppoliHarmonicL2Sq volumeAverage
  calc
    (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
        ∫ y in openCubeSet Q,
          (u.toH1.toFun y - Ch01.Legacy.normalizedAverage Q u.toH1.toFun) ^ (2 : ℕ)
          ∂MeasureTheory.volume =
        (cubeVolume Q)⁻¹ *
          ∫ y in openCubeSet Q, f y ^ (2 : ℕ) ∂MeasureTheory.volume := by
      simp [hf_pointwise, volume_openCubeSet_toReal]
    _ =
        (cubeVolume Q)⁻¹ *
          (cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℕ)) := by
      rw [hsq_integral]
    _ = (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℕ) := by
      rw [← mul_assoc, inv_mul_cancel₀ hvol_ne, one_mul]
    _ =
        (cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => u.toPointwiseAHarmonic.normalizeMeanZero.toH1 x)) ^ (2 : ℕ) := by
      rfl

private theorem coarseCaccioppoliLocalizedEnergyRadiusProfile_normalizeMeanZero_eq
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q))]
    (u : CubeSolution Q a) (rho : ℝ) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q
        (fun y =>
          scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
            u.toPointwiseAHarmonic.normalizeMeanZero y) rho =
      coarseCaccioppoliLocalizedEnergyRadiusProfile Q
        (fun y =>
          scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
            u.toPointwiseAHarmonic y) rho := by
  unfold coarseCaccioppoliLocalizedEnergyRadiusProfile
    coarseCaccioppoliLocalizedEnergyProfile cubeAverage
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp [scalarVariationEnergyIntegrand]

theorem coarseCaccioppoliLocalEnergyRadiusProfile_cubeCenter_one_third_le_localizedEnergyRadiusProfile
    {d : ℕ} (Q : TriadicCube d) {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ y ∈ cubeSet Q, 0 ≤ energy y)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    coarseCaccioppoliLocalEnergyRadiusProfile Q (cubeCenter Q) energy (1 / 3 : ℝ) ≤
      coarseCaccioppoliLocalizedEnergyRadiusProfile Q energy (1 / 3 : ℝ) := by
  have hsub :
      coarseCaccioppoliLocalClosedCube Q (cubeCenter Q) (1 / 3 : ℝ) ⊆
        scaledClosedCubeSet Q (1 / 3 : ℝ) := by
    intro y hy i
    have hrad :
        coarseCaccioppoliLocalPatchRadius Q (1 / 3 : ℝ) ≤
          (1 / 3 : ℝ) * cubeRadius Q := by
      have hcr_nonneg : 0 ≤ cubeRadius Q := le_of_lt (cubeRadius_pos Q)
      unfold coarseCaccioppoliLocalPatchRadius
      nlinarith
    exact le_trans (hy i) hrad
  unfold coarseCaccioppoliLocalEnergyRadiusProfile
    coarseCaccioppoliLocalEnergyProfile
    coarseCaccioppoliLocalizedEnergyRadiusProfile
    coarseCaccioppoliLocalizedEnergyProfile
  apply cubeAverage_le_cubeAverage_of_le_on Q
    (integrableOn_indicator_coarseCaccioppoliLocalClosedCube_of_integrableOn_cubeSet
      Q (cubeCenter Q) (1 / 3 : ℝ) henergy_int)
    (integrableOn_indicator_scaledClosedCubeSet_of_integrableOn_cubeSet
      Q (1 / 3 : ℝ) henergy_int)
  intro y hyQ
  by_cases hylocal :
      y ∈ coarseCaccioppoliLocalClosedCube Q (cubeCenter Q) (1 / 3 : ℝ)
  · have hyscaled : y ∈ scaledClosedCubeSet Q (1 / 3 : ℝ) := hsub hylocal
    rw [Set.indicator_of_mem hylocal, Set.indicator_of_mem hyscaled]
  · rw [Set.indicator_of_notMem hylocal]
    by_cases hyscaled : y ∈ scaledClosedCubeSet Q (1 / 3 : ℝ)
    · rw [Set.indicator_of_mem hyscaled]
      exact henergy_nonneg y hyQ
    · rw [Set.indicator_of_notMem hyscaled]

theorem
    interior_centered_deterministic_note_from_public_oscillation_standardExplicitBudgetSplit
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    (u : CubeSolution Q a) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    let Csol : ℝ := fullVectorPoincareCubeConstant Q
    let Calpha : ℝ := coarseCaccioppoliBufferedAlphaBudget Q s Csol
    let Ccross : ℝ := coarseCaccioppoliBufferedCrossBudget Q s Csol
    let Cnote : ℝ :=
      coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
        Q (pointwiseCoeffFor Q a) s t
        ((Fintype.card (Fin d) : ℝ) * Calpha)
        ((Fintype.card (Fin d) : ℝ) * Ccross)
    0 ≤ Cnote ∧
      coarseCaccioppoliLocalizedEnergyRadiusProfile Q
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic y) (1 / 3 : ℝ) ≤
        coarseCaccioppoliInteriorNoteRhs Q (pointwiseCoeffFor Q a) s t Cnote
          (interiorCaccioppoliParentOscillationL2Sq Q a u) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  rcases
      coarseCaccioppoli_interior_qone_standard_note_of_closedCubeEllipticity_of_buffered_constantFamily_explicitBudgetSplit
        (Q := Q) (a := pointwiseCoeffFor Q a) (s := s) (t := t)
        (u := u.toPointwiseAHarmonic.normalizeMeanZero) hs ht hst
        (pointwiseCoeffFor_isEllipticFieldOn_cubeSet Q a) with
    ⟨hCnote, hdet⟩
  refine ⟨hCnote, ?_⟩
  have hprofile :=
    coarseCaccioppoliLocalizedEnergyRadiusProfile_normalizeMeanZero_eq
      (Q := Q) (a := a) u (1 / 3 : ℝ)
  have hprofile_inv :
      coarseCaccioppoliLocalizedEnergyRadiusProfile Q
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic.normalizeMeanZero y) ((3 : ℝ)⁻¹) =
        coarseCaccioppoliLocalizedEnergyRadiusProfile Q
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic y) ((3 : ℝ)⁻¹) := by
    simpa [one_div] using hprofile
  simpa [one_div, hprofile_inv,
    interiorCaccioppoliParentOscillationL2Sq_eq_harmonicL2Sq_pointwise_normalizeMeanZero
      (Q := Q) (a := a) u] using hdet

theorem cubeCenter_mem_openCubeSet {d : ℕ} (Q : TriadicCube d) :
    cubeCenter Q ∈ openCubeSet Q := by
  rw [← ball_cubeCenter_eq_openCubeSet]
  exact Metric.mem_ball_self (cubeRadius_pos Q)

private theorem public_LambdaS_le_deterministic_LambdaSq_one_pointwiseCoeffFor
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d) (s : ℝ) :
    0 < s →
    Ch02.LambdaS Q s a ≤
      Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
        (pointwiseCoeffFor Q a) := by
  intro hs
  have hhalf :=
    Ch02.LambdaSq_one_rpow_half_le_old_pointwiseCoeffField Q a hs
  have hpublic_nonneg :
      0 ≤ Ch02.LambdaS Q s a := by
    unfold Ch02.LambdaS
    exact Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 1)
  have hold_nonneg :
      0 ≤
        Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (pointwiseCoeffFor Q a) := by
    exact Homogenization.multiscale_ellipticity_LambdaSq_one_nonneg
      Q s (pointwiseCoeffFor Q a) hs.le
  have hsq := pow_le_pow_left₀
    (Real.rpow_nonneg hpublic_nonneg (1 / 2 : ℝ)) hhalf 2
  calc
    Ch02.LambdaS Q s a =
        (Real.rpow (Ch02.LambdaS Q s a) (1 / 2 : ℝ)) ^ 2 := by
          symm
          exact Homogenization.sq_rpow_half_eq_self_of_nonneg hpublic_nonneg
    _ ≤
        (Real.rpow
          (Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
            (pointwiseCoeffFor Q a)) (1 / 2 : ℝ)) ^ 2 := by
          simpa [Ch02.LambdaS, pointwiseCoeffFor] using hsq
    _ =
        Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (pointwiseCoeffFor Q a) := by
          exact Homogenization.sq_rpow_half_eq_self_of_nonneg hold_nonneg

private theorem public_lambdaS_inv_le_deterministic_lambdaSq_one_inv_pointwiseCoeffFor
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d) (s : ℝ) :
    0 < s →
    (Ch02.lambdaS Q s a)⁻¹ ≤
      (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
        (pointwiseCoeffFor Q a))⁻¹ := by
  intro hs
  have hhalf :=
    Ch02.lambdaSq_one_rpow_neg_half_le_old_pointwiseCoeffField Q a hs
  have hpublic_nonneg :
      0 ≤ Ch02.lambdaS Q s a := by
    unfold Ch02.lambdaS
    exact Ch02.lambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 1)
  have hold_nonneg :
      0 ≤
        Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (pointwiseCoeffFor Q a) := by
    exact Homogenization.multiscale_ellipticity_lambdaSq_one_nonneg
      Q s (pointwiseCoeffFor Q a) hs.le
  have hsq := pow_le_pow_left₀
    (Real.rpow_nonneg hpublic_nonneg (-1 / 2 : ℝ)) hhalf 2
  calc
    (Ch02.lambdaS Q s a)⁻¹ =
        (Real.rpow (Ch02.lambdaS Q s a) (-1 / 2 : ℝ)) ^ 2 := by
          symm
          exact Homogenization.sq_rpow_neg_half_eq_inv_of_nonneg hpublic_nonneg
    _ ≤
        (Real.rpow
          (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
            (pointwiseCoeffFor Q a)) (-1 / 2 : ℝ)) ^ 2 := by
          simpa [Ch02.lambdaS, pointwiseCoeffFor] using hsq
    _ =
        (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (pointwiseCoeffFor Q a))⁻¹ := by
          exact Homogenization.sq_rpow_neg_half_eq_inv_of_nonneg hold_nonneg

private theorem public_ThetaRatio_le_deterministic_ThetaRatio_pointwiseCoeffFor
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Ch02.ThetaRatio Q s t a ≤
      Homogenization.ThetaRatio Q s t (pointwiseCoeffFor Q a) := by
  have hLambda :=
    public_LambdaS_le_deterministic_LambdaSq_one_pointwiseCoeffFor Q a s hs
  have hlambda_inv :=
    public_lambdaS_inv_le_deterministic_lambdaSq_one_inv_pointwiseCoeffFor Q a t ht
  have hpublic_inv_nonneg :
      0 ≤ (Ch02.lambdaS Q t a)⁻¹ := by
    exact inv_nonneg.mpr
      (Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num : (1 : ℝ) ≤ 1))
  have holdLambda_nonneg :
      0 ≤
        Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (pointwiseCoeffFor Q a) :=
    Homogenization.multiscale_ellipticity_LambdaSq_one_nonneg
      Q s (pointwiseCoeffFor Q a) hs.le
  calc
    Ch02.ThetaRatio Q s t a =
        Ch02.LambdaS Q s a * (Ch02.lambdaS Q t a)⁻¹ := by
          rw [Ch02.ThetaRatio, div_eq_mul_inv]
    _ ≤
        Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
            (pointwiseCoeffFor Q a) *
          (Homogenization.lambdaSq Q t (Homogenization.MultiscaleExponent.finite 1)
            (pointwiseCoeffFor Q a))⁻¹ := by
          exact mul_le_mul hLambda hlambda_inv hpublic_inv_nonneg holdLambda_nonneg
    _ =
        Homogenization.ThetaRatio Q s t (pointwiseCoeffFor Q a) := by
          rw [Homogenization.ThetaRatio, div_eq_mul_inv]

private theorem deterministic_LambdaSq_one_pointwiseCoeffFor_le_dim_sq_mul_public_LambdaS
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d) (s : ℝ) :
    0 < s →
    Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
        (pointwiseCoeffFor Q a) ≤
      ((d : ℝ) ^ (2 : ℕ)) * Ch02.LambdaS Q s a := by
  intro hs
  have hhalf :=
    Ch02.old_LambdaSq_one_rpow_half_le_dim_mul_pointwiseCoeffField Q a hs
  have hold_nonneg :
      0 ≤
        Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (pointwiseCoeffFor Q a) := by
    exact Homogenization.multiscale_ellipticity_LambdaSq_one_nonneg
      Q s (pointwiseCoeffFor Q a) hs.le
  have hpublic_nonneg :
      0 ≤ Ch02.LambdaS Q s a := by
    unfold Ch02.LambdaS
    exact Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 1)
  have hsq := pow_le_pow_left₀
    (Real.rpow_nonneg hold_nonneg (1 / 2 : ℝ)) hhalf 2
  calc
    Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
        (pointwiseCoeffFor Q a) =
        (Real.rpow
          (Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
            (pointwiseCoeffFor Q a)) (1 / 2 : ℝ)) ^ 2 := by
          symm
          exact Homogenization.sq_rpow_half_eq_self_of_nonneg hold_nonneg
    _ ≤
        ((d : ℝ) * Real.rpow (Ch02.LambdaS Q s a) (1 / 2 : ℝ)) ^ 2 := by
          simpa [Ch02.LambdaS, pointwiseCoeffFor] using hsq
    _ =
        ((d : ℝ) ^ (2 : ℕ)) *
          (Real.rpow (Ch02.LambdaS Q s a) (1 / 2 : ℝ)) ^ 2 := by
          ring
    _ =
        ((d : ℝ) ^ (2 : ℕ)) * Ch02.LambdaS Q s a := by
          rw [Homogenization.sq_rpow_half_eq_self_of_nonneg hpublic_nonneg]

private theorem deterministic_lambdaSq_one_inv_pointwiseCoeffFor_le_dim_sq_mul_public_lambdaS_inv
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d) (s : ℝ) :
    0 < s →
    (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
        (pointwiseCoeffFor Q a))⁻¹ ≤
      ((d : ℝ) ^ (2 : ℕ)) * (Ch02.lambdaS Q s a)⁻¹ := by
  intro hs
  have hhalf :=
    Ch02.old_lambdaSq_one_rpow_neg_half_le_dim_mul_pointwiseCoeffField Q a hs
  have hold_nonneg :
      0 ≤
        Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (pointwiseCoeffFor Q a) := by
    exact Homogenization.multiscale_ellipticity_lambdaSq_one_nonneg
      Q s (pointwiseCoeffFor Q a) hs.le
  have hpublic_nonneg :
      0 ≤ Ch02.lambdaS Q s a := by
    unfold Ch02.lambdaS
    exact Ch02.lambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 1)
  have hsq := pow_le_pow_left₀
    (Real.rpow_nonneg hold_nonneg (-1 / 2 : ℝ)) hhalf 2
  calc
    (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
        (pointwiseCoeffFor Q a))⁻¹ =
        (Real.rpow
          (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
            (pointwiseCoeffFor Q a)) (-1 / 2 : ℝ)) ^ 2 := by
          symm
          exact Homogenization.sq_rpow_neg_half_eq_inv_of_nonneg hold_nonneg
    _ ≤
        ((d : ℝ) * Real.rpow (Ch02.lambdaS Q s a) (-1 / 2 : ℝ)) ^ 2 := by
          simpa [Ch02.lambdaS, pointwiseCoeffFor] using hsq
    _ =
        ((d : ℝ) ^ (2 : ℕ)) *
          (Real.rpow (Ch02.lambdaS Q s a) (-1 / 2 : ℝ)) ^ 2 := by
          ring
    _ =
        ((d : ℝ) ^ (2 : ℕ)) * (Ch02.lambdaS Q s a)⁻¹ := by
          rw [Homogenization.sq_rpow_neg_half_eq_inv_of_nonneg hpublic_nonneg]

private theorem deterministic_ThetaRatio_pointwiseCoeffFor_le_dim_four_mul_public
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Homogenization.ThetaRatio Q s t (pointwiseCoeffFor Q a) ≤
      (((d : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ)) * Ch02.ThetaRatio Q s t a := by
  let D : ℝ := (d : ℝ) ^ (2 : ℕ)
  have hLambda :=
    deterministic_LambdaSq_one_pointwiseCoeffFor_le_dim_sq_mul_public_LambdaS
      Q a s hs
  have hlambda_inv :=
    deterministic_lambdaSq_one_inv_pointwiseCoeffFor_le_dim_sq_mul_public_lambdaS_inv
      Q a t ht
  have hold_inv_nonneg :
      0 ≤
        (Homogenization.lambdaSq Q t (Homogenization.MultiscaleExponent.finite 1)
          (pointwiseCoeffFor Q a))⁻¹ := by
    exact inv_nonneg.mpr
      (Homogenization.multiscale_ellipticity_lambdaSq_one_nonneg
        Q t (pointwiseCoeffFor Q a) ht.le)
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hpublic_Lambda_nonneg :
      0 ≤ Ch02.LambdaS Q s a := by
    unfold Ch02.LambdaS
    exact Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 1)
  have hD_public_Lambda_nonneg : 0 ≤ D * Ch02.LambdaS Q s a :=
    mul_nonneg hD_nonneg hpublic_Lambda_nonneg
  calc
    Homogenization.ThetaRatio Q s t (pointwiseCoeffFor Q a) =
        Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
            (pointwiseCoeffFor Q a) *
          (Homogenization.lambdaSq Q t (Homogenization.MultiscaleExponent.finite 1)
            (pointwiseCoeffFor Q a))⁻¹ := by
          rw [Homogenization.ThetaRatio, div_eq_mul_inv]
    _ ≤
        (D * Ch02.LambdaS Q s a) *
          (D * (Ch02.lambdaS Q t a)⁻¹) := by
          exact mul_le_mul hLambda (by simpa [D] using hlambda_inv)
            hold_inv_nonneg hD_public_Lambda_nonneg
    _ =
        (D ^ (2 : ℕ)) * Ch02.ThetaRatio Q s t a := by
          rw [Ch02.ThetaRatio, div_eq_mul_inv]
          ring
    _ =
        (((d : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ)) * Ch02.ThetaRatio Q s t a := by
          rfl

private theorem deterministic_one_le_ThetaRatio_pointwiseCoeffFor
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    1 ≤ Homogenization.ThetaRatio Q s t (pointwiseCoeffFor Q a) := by
  exact (Ch02.one_le_ThetaRatio_of_pos Q a hs ht).trans
    (public_ThetaRatio_le_deterministic_ThetaRatio_pointwiseCoeffFor Q a hs ht)

private theorem boundary_localPatch_standardExplicitNoteConstantSplit_le_explicitBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    let Csol : ℝ := fullVectorPoincareCubeConstant Q
    let Calpha : ℝ := coarseCaccioppoliLocalPatchBufferedAlphaBudget Q s Csol
    let Ccross : ℝ := coarseCaccioppoliLocalPatchBufferedCrossBudget Q s Csol
    let CalphaInternal : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
    let CcrossInternal : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
        Q (pointwiseCoeffFor Q a) s t CalphaInternal CcrossInternal ≤
      caccioppoliStandardExplicitNoteBoundSplit s t
        CalphaInternal CcrossInternal := by
  let Csol : ℝ := fullVectorPoincareCubeConstant Q
  let Calpha : ℝ := coarseCaccioppoliLocalPatchBufferedAlphaBudget Q s Csol
  let Ccross : ℝ := coarseCaccioppoliLocalPatchBufferedCrossBudget Q s Csol
  rcases coarseCaccioppoliLocalPatchBufferedBudgetSplit_spec
      (Q := Q) (s := s) (t := t) (Csol := Csol) hs ht hst with
    ⟨_, _, hCalpha, hCcross, _, _, _⟩
  have hcard_nat_pos : 0 < Fintype.card (Fin d) := by
    simp [Fintype.card_fin, Nat.pos_iff_ne_zero, NeZero.ne d]
  have hcard_pos : 0 < (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast hcard_nat_pos
  have hCalphaInternal :
      0 < (Fintype.card (Fin d) : ℝ) * Calpha :=
    mul_pos hcard_pos hCalpha
  have hCcrossInternal :
      0 ≤ (Fintype.card (Fin d) : ℝ) * Ccross :=
    mul_nonneg hcard_pos.le hCcross
  simpa [Csol, Calpha, Ccross, caccioppoliStandardExplicitNoteBoundSplit] using
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit_le_explicitBound
      Q (pointwiseCoeffFor Q a) s t
      ((Fintype.card (Fin d) : ℝ) * Calpha)
      ((Fintype.card (Fin d) : ℝ) * Ccross)
      hCalphaInternal hCcrossInternal hs ht hst
      (deterministic_one_le_ThetaRatio_pointwiseCoeffFor Q a hs ht)

theorem boundary_localPatch_standardExplicitNoteConstantSplit_le_unitExplicitBound_of_scale_zero
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hQ : Q.scale = 0) :
    let CalphaInternal : ℝ :=
      (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s
    let CcrossInternal : ℝ :=
      (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
        Q (pointwiseCoeffFor Q a) s t CalphaInternal CcrossInternal ≤
      caccioppoliStandardExplicitNoteBoundSplit s t
        CalphaInternal CcrossInternal := by
  simpa [caccioppoliStandardExplicitNoteBoundSplit,
    coarseCaccioppoliLocalPatchBufferedAlphaBudget_eq_unit_of_scale_eq_zero
      (Q := Q) s hQ,
    coarseCaccioppoliLocalPatchBufferedCrossBudget_eq_unit_of_scale_eq_zero
      (Q := Q) s hQ] using
    boundary_localPatch_standardExplicitNoteConstantSplit_le_explicitBound
      Q a hs ht hst

private theorem interior_centered_standardExplicitNoteConstantSplit_le_explicitBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    let Csol : ℝ := fullVectorPoincareCubeConstant Q
    let Calpha : ℝ := coarseCaccioppoliBufferedAlphaBudget Q s Csol
    let Ccross : ℝ := coarseCaccioppoliBufferedCrossBudget Q s Csol
    let CalphaInternal : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
    let CcrossInternal : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
        Q (pointwiseCoeffFor Q a) s t CalphaInternal CcrossInternal ≤
      caccioppoliStandardExplicitNoteBoundSplit s t
        CalphaInternal CcrossInternal := by
  let Csol : ℝ := fullVectorPoincareCubeConstant Q
  let Calpha : ℝ := coarseCaccioppoliBufferedAlphaBudget Q s Csol
  let Ccross : ℝ := coarseCaccioppoliBufferedCrossBudget Q s Csol
  rcases coarseCaccioppoliBufferedBudgetSplit_spec
      (Q := Q) (s := s) (t := t) (Csol := Csol) hs ht hst with
    ⟨_, _, hCalpha, hCcross, _, _, _⟩
  have hcard_nat_pos : 0 < Fintype.card (Fin d) := by
    simp [Fintype.card_fin, Nat.pos_iff_ne_zero, NeZero.ne d]
  have hcard_pos : 0 < (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast hcard_nat_pos
  have hCalphaInternal :
      0 < (Fintype.card (Fin d) : ℝ) * Calpha :=
    mul_pos hcard_pos hCalpha
  have hCcrossInternal :
      0 ≤ (Fintype.card (Fin d) : ℝ) * Ccross :=
    mul_nonneg hcard_pos.le hCcross
  simpa [Csol, Calpha, Ccross, caccioppoliStandardExplicitNoteBoundSplit] using
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit_le_explicitBound
      Q (pointwiseCoeffFor Q a) s t
      ((Fintype.card (Fin d) : ℝ) * Calpha)
      ((Fintype.card (Fin d) : ℝ) * Ccross)
      hCalphaInternal hCcrossInternal hs ht hst
      (deterministic_one_le_ThetaRatio_pointwiseCoeffFor Q a hs ht)

theorem interior_centered_standardExplicitNoteConstantSplit_le_unitExplicitBound_of_scale_zero
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hQ : Q.scale = 0) :
    let CalphaInternal : ℝ :=
      (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedAlphaBudgetUnit d s
    let CcrossInternal : ℝ :=
      (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedCrossBudgetUnit d s
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
        Q (pointwiseCoeffFor Q a) s t CalphaInternal CcrossInternal ≤
      caccioppoliStandardExplicitNoteBoundSplit s t
        CalphaInternal CcrossInternal := by
  simpa [caccioppoliStandardExplicitNoteBoundSplit,
    coarseCaccioppoliBufferedAlphaBudget_eq_unit_of_scale_eq_zero
      (Q := Q) s hQ,
    coarseCaccioppoliBufferedCrossBudget_eq_unit_of_scale_eq_zero
      (Q := Q) s hQ] using
    interior_centered_standardExplicitNoteConstantSplit_le_explicitBound
      Q a hs ht hst

private theorem dim_sq_theta_loss_mul_rpow_le_scaled_rpow
    {D C σ e p : ℝ} (hD : 1 ≤ D) (hC : 0 ≤ C) (hσ : 0 < σ)
    (he : 0 ≤ e) (hp : p = 2 + 4 * e) :
    D * Real.rpow (D ^ (2 : ℕ)) e * Real.rpow (C / σ) p ≤
      Real.rpow (D * C / σ) p := by
  have hD_nonneg : 0 ≤ D := le_trans zero_le_one hD
  have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hbase_nonneg : 0 ≤ C / σ := div_nonneg hC hσ.le
  have hDsq_rpow :
      Real.rpow (D ^ (2 : ℕ)) e = Real.rpow D (2 * e) := by
    have hDsq_eq : D ^ (2 : ℕ) = Real.rpow D (2 : ℝ) := by
      exact (Real.rpow_two D).symm
    rw [hDsq_eq]
    exact (Real.rpow_mul hD_nonneg (2 : ℝ) e).symm
  have hfactor_eq :
      D * Real.rpow (D ^ (2 : ℕ)) e = Real.rpow D (1 + 2 * e) := by
    calc
      D * Real.rpow (D ^ (2 : ℕ)) e =
          D * Real.rpow D (2 * e) := by
            rw [hDsq_rpow]
      _ = Real.rpow D 1 * Real.rpow D (2 * e) := by
            simp
      _ = Real.rpow D (1 + 2 * e) := by
            exact (Real.rpow_add hD_pos 1 (2 * e)).symm
  have hexp_le : 1 + 2 * e ≤ p := by
    rw [hp]
    nlinarith [he]
  have hfactor_le :
      D * Real.rpow (D ^ (2 : ℕ)) e ≤ Real.rpow D p := by
    rw [hfactor_eq]
    exact Real.rpow_le_rpow_of_exponent_le hD hexp_le
  have hscaled_eq :
      Real.rpow (D * C / σ) p =
        Real.rpow D p * Real.rpow (C / σ) p := by
    have hbase : D * C / σ = D * (C / σ) := by ring
    rw [hbase]
    exact Real.mul_rpow hD_nonneg hbase_nonneg
  calc
    D * Real.rpow (D ^ (2 : ℕ)) e * Real.rpow (C / σ) p ≤
        Real.rpow D p * Real.rpow (C / σ) p := by
          exact mul_le_mul_of_nonneg_right hfactor_le
            (Real.rpow_nonneg hbase_nonneg _)
    _ = Real.rpow (D * C / σ) p := hscaled_eq.symm

private theorem deterministic_boundaryNoteCoeff_pointwiseCoeffFor_le_publicPrefactor_dim_sq_mul
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {s t C : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hC : 0 ≤ C) (hQscale : Q.scale = 0) :
    coarseCaccioppoliBoundaryNoteCoeff Q (pointwiseCoeffFor Q a) s t C ≤
      caccioppoliPrefactor (((d : ℝ) ^ (2 : ℕ)) * C) Q a s t := by
  let σ : ℝ := 1 - s - t
  let e : ℝ := s / σ
  let p : ℝ := 2 + 4 * s / σ
  let D : ℝ := (d : ℝ) ^ (2 : ℕ)
  let front : ℝ := Real.rpow (C / σ) p * Real.rpow s (-2 * s / σ)
  let F : ℝ :=
    Real.rpow s (-2 * s / σ) *
      Real.rpow (Ch02.ThetaRatio Q s t a) e *
      Ch02.LambdaS Q s a
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    linarith
  have he_nonneg : 0 ≤ e := by
    dsimp [e]
    positivity
  have hd_nat : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne d))
  have hd_one : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_nat
  have hd_nonneg : 0 ≤ (d : ℝ) := le_trans zero_le_one hd_one
  have hD_one : (1 : ℝ) ≤ D := by
    dsimp [D]
    simpa [pow_two] using
      mul_le_mul hd_one hd_one (by norm_num : (0 : ℝ) ≤ 1) hd_nonneg
  have hD_nonneg : 0 ≤ D := le_trans zero_le_one hD_one
  have hDsq_nonneg : 0 ≤ D ^ (2 : ℕ) := pow_nonneg hD_nonneg 2
  have hbase_nonneg : 0 ≤ C / σ := div_nonneg hC hσ_pos.le
  have hCpow_nonneg : 0 ≤ Real.rpow (C / σ) p :=
    Real.rpow_nonneg hbase_nonneg _
  have hsPow_nonneg : 0 ≤ Real.rpow s (-2 * s / σ) :=
    Real.rpow_nonneg hs.le _
  have hfront_nonneg : 0 ≤ front := by
    dsimp [front]
    exact mul_nonneg hCpow_nonneg hsPow_nonneg
  have hOldTheta_nonneg :
      0 ≤ Homogenization.ThetaRatio Q s t (pointwiseCoeffFor Q a) :=
    thetaRatio_nonneg Q s t (pointwiseCoeffFor Q a) hs.le ht.le
  have hPubTheta_nonneg : 0 ≤ Ch02.ThetaRatio Q s t a :=
    Ch02.ThetaRatio_nonneg Q a hs ht
  have hOldLambda_nonneg :
      0 ≤
        Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (pointwiseCoeffFor Q a) :=
    Homogenization.multiscale_ellipticity_LambdaSq_one_nonneg
      Q s (pointwiseCoeffFor Q a) hs.le
  have hPubLambda_nonneg : 0 ≤ Ch02.LambdaS Q s a := by
    unfold Ch02.LambdaS
    exact Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 1)
  have hD_pubLambda_nonneg : 0 ≤ D * Ch02.LambdaS Q s a :=
    mul_nonneg hD_nonneg hPubLambda_nonneg
  have hF_nonneg : 0 ≤ F := by
    dsimp [F]
    exact mul_nonneg
      (mul_nonneg hsPow_nonneg
        (Real.rpow_nonneg hPubTheta_nonneg _))
      hPubLambda_nonneg
  have hLambda :
      Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (pointwiseCoeffFor Q a) ≤
        D * Ch02.LambdaS Q s a := by
    simpa [D] using
      deterministic_LambdaSq_one_pointwiseCoeffFor_le_dim_sq_mul_public_LambdaS
        Q a s hs
  have hTheta :
      Homogenization.ThetaRatio Q s t (pointwiseCoeffFor Q a) ≤
        D ^ (2 : ℕ) * Ch02.ThetaRatio Q s t a := by
    simpa [D] using
      deterministic_ThetaRatio_pointwiseCoeffFor_le_dim_four_mul_public
        Q a hs ht
  have hThetaPow :
      Real.rpow (Homogenization.ThetaRatio Q s t (pointwiseCoeffFor Q a)) e ≤
        Real.rpow (D ^ (2 : ℕ) * Ch02.ThetaRatio Q s t a) e := by
    exact Real.rpow_le_rpow hOldTheta_nonneg hTheta he_nonneg
  have hThetaPow_mul :
      Real.rpow (D ^ (2 : ℕ) * Ch02.ThetaRatio Q s t a) e =
        Real.rpow (D ^ (2 : ℕ)) e *
          Real.rpow (Ch02.ThetaRatio Q s t a) e := by
    exact Real.mul_rpow hDsq_nonneg hPubTheta_nonneg
  have hThetaLambda :
      Real.rpow (Homogenization.ThetaRatio Q s t (pointwiseCoeffFor Q a)) e *
          Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
            (pointwiseCoeffFor Q a) ≤
        Real.rpow (D ^ (2 : ℕ) * Ch02.ThetaRatio Q s t a) e *
          (D * Ch02.LambdaS Q s a) := by
    exact mul_le_mul hThetaPow hLambda hOldLambda_nonneg
      (Real.rpow_nonneg (mul_nonneg hDsq_nonneg hPubTheta_nonneg) _)
  have hconstant_absorb :
      D * Real.rpow (D ^ (2 : ℕ)) e * Real.rpow (C / σ) p ≤
        Real.rpow (D * C / σ) p :=
    dim_sq_theta_loss_mul_rpow_le_scaled_rpow hD_one hC hσ_pos he_nonneg
      (by dsimp [p, e]; ring)
  have hsPow_public :
      Real.rpow s (-2 * s / σ) = Real.rpow s (-(2 * s / σ)) := by
    congr 1
    ring
  have hsPow_public_expanded :
      Real.rpow s (-2 * s / (1 - s - t)) =
        Real.rpow s (-(2 * s / (1 - s - t))) := by
    simpa [σ] using hsPow_public
  have hscale_one :
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) = 1 := by
    simp [hQscale]
  calc
    coarseCaccioppoliBoundaryNoteCoeff Q (pointwiseCoeffFor Q a) s t C =
        front *
          (Real.rpow (Homogenization.ThetaRatio Q s t (pointwiseCoeffFor Q a)) e *
            Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
              (pointwiseCoeffFor Q a)) := by
          dsimp [front, p, e, σ]
          unfold coarseCaccioppoliBoundaryNoteCoeff coarseCaccioppoliSigma
          simp [Homogenization.LambdaSq]
          ring
    _ ≤
        front *
          (Real.rpow (D ^ (2 : ℕ) * Ch02.ThetaRatio Q s t a) e *
            (D * Ch02.LambdaS Q s a)) :=
          mul_le_mul_of_nonneg_left hThetaLambda hfront_nonneg
    _ =
        (D * Real.rpow (D ^ (2 : ℕ)) e * Real.rpow (C / σ) p) * F := by
          rw [hThetaPow_mul]
          dsimp [front, F]
          ring
    _ ≤ Real.rpow (D * C / σ) p * F :=
          mul_le_mul_of_nonneg_right hconstant_absorb hF_nonneg
    _ =
        Real.rpow (D * C / σ) p *
          (Real.rpow s (-(2 * s / σ)) *
            Real.rpow (Ch02.ThetaRatio Q s t a) e *
            Ch02.LambdaS Q s a) := by
          simpa [F, mul_assoc] using
            congrArg
              (fun z : ℝ =>
                Real.rpow (D * C / σ) p *
                  (z * Real.rpow (Ch02.ThetaRatio Q s t a) e *
                    Ch02.LambdaS Q s a))
              hsPow_public
    _ = caccioppoliPrefactor (D * C) Q a s t := by
          dsimp [p, e, σ, D]
          unfold caccioppoliPrefactor
          simp [hQscale, mul_assoc, mul_left_comm, mul_comm]

theorem deterministic_boundaryNoteRhs_pointwiseCoeffFor_le_publicPrefactor_dim_sq_mul
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {s t C uL2Sq : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hC : 0 ≤ C) (hQscale : Q.scale = 0) (hu : 0 ≤ uL2Sq) :
    coarseCaccioppoliBoundaryNoteRhs Q (pointwiseCoeffFor Q a) s t C uL2Sq ≤
      caccioppoliPrefactor (((d : ℝ) ^ (2 : ℕ)) * C) Q a s t * uL2Sq := by
  rw [coarseCaccioppoliBoundaryNoteRhs_eq_coeff_mul_uL2Sq]
  exact mul_le_mul_of_nonneg_right
    (deterministic_boundaryNoteCoeff_pointwiseCoeffFor_le_publicPrefactor_dim_sq_mul
      (Q := Q) (a := a) hs ht hst hC hQscale)
    hu

theorem deterministic_boundaryNoteRhs_pointwiseCoeffFor_le_publicRHS_dim_sq_mul_of_scale_zero
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : BoundaryCaccioppoliDatum Q a x) {s t C : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hC : 0 ≤ C) (hQscale : Q.scale = 0) :
    coarseCaccioppoliBoundaryNoteRhs Q (pointwiseCoeffFor Q a) s t C
        (boundaryCaccioppoliParentL2Sq u) ≤
      boundaryCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * C) s t u := by
  have hu :
      0 ≤ boundaryCaccioppoliParentL2Sq u := by
    rw [boundaryCaccioppoliParentL2Sq_eq_harmonicL2Sq_pointwise u]
    exact
      coarseCaccioppoliHarmonicL2Sq_nonneg Q (pointwiseCoeffFor Q a)
        u.toPointwiseAHarmonic
  simpa [boundaryCaccioppoliRHS] using
    deterministic_boundaryNoteRhs_pointwiseCoeffFor_le_publicPrefactor_dim_sq_mul
      (Q := Q) (a := a) (s := s) (t := t) (C := C)
      (uL2Sq := boundaryCaccioppoliParentL2Sq u)
      hs ht hst hC hQscale hu

theorem deterministic_interiorNoteRhs_pointwiseCoeffFor_le_publicRHS_dim_sq_mul_of_scale_zero
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    (u : CubeSolution Q a) {s t C : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hC : 0 ≤ C) (hQscale : Q.scale = 0) :
    coarseCaccioppoliInteriorNoteRhs Q (pointwiseCoeffFor Q a) s t C
        (interiorCaccioppoliParentOscillationL2Sq Q a u) ≤
      interiorCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * C) Q a s t u := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hu :
      0 ≤ interiorCaccioppoliParentOscillationL2Sq Q a u := by
    rw [interiorCaccioppoliParentOscillationL2Sq_eq_harmonicL2Sq_pointwise_normalizeMeanZero
      (Q := Q) (a := a) u]
    exact
      coarseCaccioppoliHarmonicL2Sq_nonneg Q (pointwiseCoeffFor Q a)
        u.toPointwiseAHarmonic.normalizeMeanZero
  simpa [interiorCaccioppoliRHS, coarseCaccioppoliInteriorNoteRhs] using
    deterministic_boundaryNoteRhs_pointwiseCoeffFor_le_publicPrefactor_dim_sq_mul
      (Q := Q) (a := a) (s := s) (t := t) (C := C)
      (uL2Sq := interiorCaccioppoliParentOscillationL2Sq Q a u)
      hs ht hst hC hQscale hu

end

end Ch03
end Book
end Homogenization
