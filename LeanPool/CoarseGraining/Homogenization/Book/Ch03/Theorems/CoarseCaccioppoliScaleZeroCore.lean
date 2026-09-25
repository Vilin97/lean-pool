/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.Endpoints

/-! # Coarse Caccioppoli Scale Zero Core -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Scale-zero Caccioppoli core estimates

This file contains the pointwise coefficient bridge, core-window geometry,
and normalized core-energy estimates used by the scale-zero Caccioppoli
proof.  The theorem assembly remains in `CoarseCaccioppoliScaleZero.lean`.

## Audit tag

Claim: provide the pointwise-coefficient transport and unit-scale core-energy
geometry used by the scale-zero Caccioppoli bridge.

Downstream target: `CoarseCaccioppoliScaleZeroBridge.lean`.  This file should
remain core estimate infrastructure, not a public theorem-package surface.
-/

noncomputable section

open scoped ENNReal

abbrev pointwiseCoeffFor {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) : CoeffField d :=
  Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (a.coeffOn Q)

theorem pointwiseCoeffFor_isEllipticFieldOn_cubeSet {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) :
    IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam (cubeSet Q)
      (pointwiseCoeffFor Q a) := by
  simpa [pointwiseCoeffFor] using
    Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn_cubeSet
      Q (a.coeffOn Q)

noncomputable def CubeSolution.toPointwiseAHarmonic {d : ℕ}
    {Q : TriadicCube d} {a : CoeffFamily d} (u : CubeSolution Q a) :
    AHarmonicFunction (pointwiseCoeffFor Q a) (openCubeSet Q) where
  toH1 := u.toH1
  isHarmonic := by
    let U : Ch02.Domain d := Ch02.cubeDomain Q
    let A : CoeffField d := pointwiseCoeffFor Q a
    have hA :
        (a.coeffOn Q).toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)] A := by
      simpa [A, pointwiseCoeffFor, U, Ch02.cubeDomain] using
        (Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq U (a.coeffOn Q)).symm
    exact IsAHarmonicGradient.of_ae_eq_coeff hA u.isHarmonic

noncomputable def BoundaryCaccioppoliDatum.toPointwiseAHarmonic
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d}
    (u : BoundaryCaccioppoliDatum Q a x) :
    AHarmonicFunction (pointwiseCoeffFor Q a) (openCubeSet Q) where
  toH1 := u.toH1
  isHarmonic := by
    let U : Ch02.Domain d := Ch02.cubeDomain Q
    let A : CoeffField d := pointwiseCoeffFor Q a
    have hA :
        (a.coeffOn Q).toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)] A := by
      simpa [A, pointwiseCoeffFor, U, Ch02.cubeDomain] using
        (Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq U (a.coeffOn Q)).symm
    exact IsAHarmonicGradient.of_ae_eq_coeff hA u.isHarmonic

theorem coarseCaccioppoliLocalOpenCube_one_eq_openCubeAtScale
    {d : ℕ} (Q : TriadicCube d) (x : Vec d) :
    coarseCaccioppoliLocalOpenCube Q x 1 =
      openCubeAtScale x (Q.scale - 1) := by
  ext y
  constructor
  · intro hy i
    have hrad :
        coarseCaccioppoliLocalPatchRadius Q 1 =
          Real.rpow (3 : ℝ) (((Q.scale - 1 : ℤ) : ℝ)) / 2 := by
      calc
        coarseCaccioppoliLocalPatchRadius Q 1 =
            (3 : ℝ) ^ (Q.scale - 1) / 2 := by
          unfold coarseCaccioppoliLocalPatchRadius cubeRadius cubeScaleFactor
          rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
          norm_num
          ring
        _ = Real.rpow (3 : ℝ) (((Q.scale - 1 : ℤ) : ℝ)) / 2 :=
          congrArg (fun r : ℝ => r / 2)
            (Real.rpow_intCast (3 : ℝ) (Q.scale - 1)).symm
    simpa [openCubeAtScale, coarseCaccioppoliLocalOpenCube, hrad] using hy i
  · intro hy i
    have hrad :
        coarseCaccioppoliLocalPatchRadius Q 1 =
          Real.rpow (3 : ℝ) (((Q.scale - 1 : ℤ) : ℝ)) / 2 := by
      calc
        coarseCaccioppoliLocalPatchRadius Q 1 =
            (3 : ℝ) ^ (Q.scale - 1) / 2 := by
          unfold coarseCaccioppoliLocalPatchRadius cubeRadius cubeScaleFactor
          rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
          norm_num
          ring
        _ = Real.rpow (3 : ℝ) (((Q.scale - 1 : ℤ) : ℝ)) / 2 :=
          congrArg (fun r : ℝ => r / 2)
            (Real.rpow_intCast (3 : ℝ) (Q.scale - 1)).symm
    simpa [openCubeAtScale, coarseCaccioppoliLocalOpenCube, hrad] using hy i

private theorem coarseCaccioppoliLocalPatchRadius_one_third_eq
    {d : ℕ} (Q : TriadicCube d) :
    coarseCaccioppoliLocalPatchRadius Q ((3 : ℝ)⁻¹) =
      Real.rpow (3 : ℝ) (((Q.scale - 2 : ℤ) : ℝ)) / 2 := by
  calc
    coarseCaccioppoliLocalPatchRadius Q ((3 : ℝ)⁻¹) =
        (3 : ℝ) ^ (Q.scale - 2) / 2 := by
      unfold coarseCaccioppoliLocalPatchRadius cubeRadius cubeScaleFactor
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
      ring
    _ = Real.rpow (3 : ℝ) (((Q.scale - 2 : ℤ) : ℝ)) / 2 :=
      congrArg (fun r : ℝ => r / 2)
        (Real.rpow_intCast (3 : ℝ) (Q.scale - 2)).symm

private theorem coarseCaccioppoliLocalOpenCube_one_third_eq_openCubeAtScale
    {d : ℕ} (Q : TriadicCube d) (x : Vec d) :
    coarseCaccioppoliLocalOpenCube Q x ((3 : ℝ)⁻¹) =
      openCubeAtScale x (Q.scale - 2) := by
  ext y
  constructor
  · intro hy i
    have hrad := coarseCaccioppoliLocalPatchRadius_one_third_eq Q
    simpa [openCubeAtScale, coarseCaccioppoliLocalOpenCube, hrad] using hy i
  · intro hy i
    have hrad := coarseCaccioppoliLocalPatchRadius_one_third_eq Q
    simpa [openCubeAtScale, coarseCaccioppoliLocalOpenCube, hrad] using hy i

theorem caccioppoliCoreSet_subset_cubeSet
    {d : ℕ} (Q : TriadicCube d) (x : Vec d) :
    caccioppoliCoreSet Q x ⊆ cubeSet Q := by
  intro y hy i
  exact ⟨le_of_lt (hy.1 i).1, (hy.1 i).2⟩

private theorem caccioppoliCoreSet_subset_localClosedCube_one_third
    {d : ℕ} (Q : TriadicCube d) (x : Vec d) :
    caccioppoliCoreSet Q x ⊆
      coarseCaccioppoliLocalClosedCube Q x ((3 : ℝ)⁻¹) := by
  intro y hy
  have hlocalOpen :
      y ∈ coarseCaccioppoliLocalOpenCube Q x ((3 : ℝ)⁻¹) := by
    have hset := coarseCaccioppoliLocalOpenCube_one_third_eq_openCubeAtScale Q x
    rw [hset]
    exact hy.2
  exact coarseCaccioppoliLocalOpenCube_subset_closedCube Q x ((3 : ℝ)⁻¹) hlocalOpen

theorem coreOpenCubeRadius_eq_scaleFactor_div_eighteen
    {d : ℕ} (Q : TriadicCube d) :
    Real.rpow (3 : ℝ) (((Q.scale - 2 : ℤ) : ℝ)) / 2 =
      cubeScaleFactor Q / 18 := by
  calc
    Real.rpow (3 : ℝ) (((Q.scale - 2 : ℤ) : ℝ)) / 2 =
        (3 : ℝ) ^ (Q.scale - 2) / 2 := by
      exact congrArg (fun r : ℝ => r / 2)
        (Real.rpow_intCast (3 : ℝ) (Q.scale - 2))
    _ = cubeScaleFactor Q / 18 := by
      unfold cubeScaleFactor
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
      ring

theorem volume_caccioppoliCoreSet_toReal_ge_scaleFactor_div_eighteen_pow
    {d : ℕ} (Q : TriadicCube d) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    (cubeScaleFactor Q / 18) ^ d ≤
      (MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal := by
  classical
  let r : ℝ := Real.rpow (3 : ℝ) (((Q.scale - 2 : ℤ) : ℝ)) / 2
  let lo : Fin d → ℝ := fun i =>
    ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) ⊔ (x i - r))
  let hi : Fin d → ℝ := fun i =>
    ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) ⊓ (x i + r))
  have hscale_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hr_eq : r = cubeScaleFactor Q / 18 := by
    simpa [r] using coreOpenCubeRadius_eq_scaleFactor_div_eighteen Q
  have hr_pos : 0 < r := by
    rw [hr_eq]
    positivity
  have hcore_eq :
      caccioppoliCoreSet Q x =
        Set.pi Set.univ (fun i : Fin d => Set.Ioo (lo i) (hi i)) := by
    rw [caccioppoliCoreSet, openCubeSet_eq_pi_Ioo,
      openCubeAtScale_eq_pi_Ioo, ← Set.pi_inter_distrib]
    apply Set.pi_congr rfl
    intro i _
    simp [lo, hi, r, Set.Ioo_inter_Ioo]
  have hside : ∀ i : Fin d, cubeScaleFactor Q / 18 ≤ hi i - lo i := by
    intro i
    let A : ℝ := (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)
    let B : ℝ := (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)
    have hx_i : A < x i ∧ x i < B := by
      simpa [A, B, openCubeSet] using hx i
    have hBA : B - A = cubeScaleFactor Q := by
      dsimp [A, B]
      ring
    have hA_le_B_sub_r : A ≤ B - r := by
      rw [hr_eq]
      nlinarith [hBA, hscale_pos]
    have hx_sub_r_le_B_sub_r : x i - r ≤ B - r := by
      linarith [le_of_lt hx_i.2]
    have hsup_le_B_sub_r : A ⊔ (x i - r) ≤ B - r :=
      sup_le hA_le_B_sub_r hx_sub_r_le_B_sub_r
    have hsup_le_x : A ⊔ (x i - r) ≤ x i := by
      apply sup_le
      · exact le_of_lt hx_i.1
      · linarith [le_of_lt hr_pos]
    have hsup_add_le_inf : A ⊔ (x i - r) + r ≤ B ⊓ (x i + r) := by
      apply le_inf
      · linarith [hsup_le_B_sub_r]
      · linarith [hsup_le_x]
    have hcoord :
        hi i - lo i = (B ⊓ (x i + r)) - (A ⊔ (x i - r)) := by
      simp [hi, lo, A, B]
    rw [hcoord, ← hr_eq]
    linarith
  have hab : lo ≤ hi := by
    intro i
    have h := hside i
    nlinarith [hscale_pos]
  rw [hcore_eq]
  have hvol :
      (MeasureTheory.volume
        (Set.pi Set.univ (fun i : Fin d => Set.Ioo (lo i) (hi i)))).toReal =
        ∏ i : Fin d, (hi i - lo i) :=
    Real.volume_pi_Ioo_toReal (ι := Fin d) hab
  calc
    (cubeScaleFactor Q / 18) ^ d =
        ∏ _i : Fin d, cubeScaleFactor Q / 18 := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i : Fin d, (hi i - lo i) := by
      apply Finset.prod_le_prod
      · intro i _
        exact le_of_lt (div_pos hscale_pos (by norm_num))
      · intro i _
        exact hside i
    _ =
        (MeasureTheory.volume
          (Set.pi Set.univ (fun i : Fin d => Set.Ioo (lo i) (hi i)))).toReal := by
      rw [hvol]

theorem caccioppoliCoreSet_volumeRatio_le_eighteen_pow
    {d : ℕ} (Q : TriadicCube d) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    ((MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal)⁻¹ *
        cubeVolume Q ≤
      (18 : ℝ) ^ d := by
  have hscale_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hbase_pos : 0 < cubeScaleFactor Q / 18 := by
    positivity
  have hlower :
      (cubeScaleFactor Q / 18) ^ d ≤
        (MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal :=
    volume_caccioppoliCoreSet_toReal_ge_scaleFactor_div_eighteen_pow Q hx
  have hlower_pos : 0 < (cubeScaleFactor Q / 18) ^ d :=
    pow_pos hbase_pos d
  have hcore_volume_pos :
      0 < (MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal :=
    lt_of_lt_of_le hlower_pos hlower
  have hinv :
      ((MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal)⁻¹ ≤
        ((cubeScaleFactor Q / 18) ^ d)⁻¹ :=
    (inv_le_inv₀ hcore_volume_pos hlower_pos).2 hlower
  calc
    ((MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal)⁻¹ *
        cubeVolume Q ≤
        ((cubeScaleFactor Q / 18) ^ d)⁻¹ * cubeVolume Q := by
      exact mul_le_mul_of_nonneg_right hinv (cubeVolume_nonneg Q)
    _ = (18 : ℝ) ^ d := by
      rw [cubeVolume_eq_scaleFactor_pow, div_pow]
      field_simp [pow_ne_zero d hscale_pos.ne']

private theorem setIntegral_caccioppoliCoreSet_le_cubeVolume_mul_localEnergyRadiusProfile
    {d : ℕ} (Q : TriadicCube d) (x : Vec d) {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ y ∈ cubeSet Q, 0 ≤ energy y)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    ∫ y in caccioppoliCoreSet Q x, energy y ∂MeasureTheory.volume ≤
      cubeVolume Q *
        coarseCaccioppoliLocalEnergyRadiusProfile Q x energy ((3 : ℝ)⁻¹) := by
  let localCube : Set (Vec d) :=
    coarseCaccioppoliLocalClosedCube Q x ((3 : ℝ)⁻¹)
  have hlocal_int :
      MeasureTheory.IntegrableOn (localCube.indicator energy)
        (cubeSet Q) MeasureTheory.volume := by
    simpa [localCube] using
      integrableOn_indicator_coarseCaccioppoliLocalClosedCube_of_integrableOn_cubeSet
        Q x ((3 : ℝ)⁻¹) henergy_int
  have hlocal_nonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
        localCube.indicator energy := by
    change ∀ᵐ y ∂MeasureTheory.volume.restrict (cubeSet Q),
      0 ≤ localCube.indicator energy y
    rw [MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)]
    exact Filter.Eventually.of_forall fun y hyQ => by
      by_cases hylocal : y ∈ localCube
      · simpa [Set.indicator_of_mem hylocal] using henergy_nonneg y hyQ
      · simp [Set.indicator_of_notMem hylocal]
  have hcore_sub_cube_ae :
      caccioppoliCoreSet Q x ≤ᵐ[MeasureTheory.volume] cubeSet Q :=
    Filter.Eventually.of_forall fun y hy =>
      caccioppoliCoreSet_subset_cubeSet Q x hy
  have hmono :
      ∫ y in caccioppoliCoreSet Q x, localCube.indicator energy y ∂MeasureTheory.volume ≤
        ∫ y in cubeSet Q, localCube.indicator energy y ∂MeasureTheory.volume :=
    MeasureTheory.setIntegral_mono_set hlocal_int hlocal_nonneg hcore_sub_cube_ae
  have hcore_eq :
      ∫ y in caccioppoliCoreSet Q x, energy y ∂MeasureTheory.volume =
        ∫ y in caccioppoliCoreSet Q x, localCube.indicator energy y ∂MeasureTheory.volume := by
    apply MeasureTheory.setIntegral_congr_fun (measurableSet_caccioppoliCoreSet Q x)
    intro y hy
    simp [localCube, Set.indicator_of_mem
      (caccioppoliCoreSet_subset_localClosedCube_one_third Q x hy)]
  have hprofile_eq :
      ∫ y in cubeSet Q, localCube.indicator energy y ∂MeasureTheory.volume =
        cubeVolume Q *
          coarseCaccioppoliLocalEnergyRadiusProfile Q x energy ((3 : ℝ)⁻¹) := by
    have hvol_ne : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
    unfold coarseCaccioppoliLocalEnergyRadiusProfile
      coarseCaccioppoliLocalEnergyProfile cubeAverage
    simp only [localCube]
    calc
      ∫ y in cubeSet Q,
          (coarseCaccioppoliLocalClosedCube Q x (3 : ℝ)⁻¹).indicator energy y
          ∂MeasureTheory.volume =
          1 *
            ∫ y in cubeSet Q,
              (coarseCaccioppoliLocalClosedCube Q x (3 : ℝ)⁻¹).indicator energy y
              ∂MeasureTheory.volume := by
        ring
      _ =
          (cubeVolume Q * (cubeVolume Q)⁻¹) *
            ∫ y in cubeSet Q,
              (coarseCaccioppoliLocalClosedCube Q x (3 : ℝ)⁻¹).indicator energy y
              ∂MeasureTheory.volume := by
        rw [mul_inv_cancel₀ hvol_ne]
      _ =
          cubeVolume Q *
            ((cubeVolume Q)⁻¹ *
              ∫ y in cubeSet Q,
                (coarseCaccioppoliLocalClosedCube Q x (3 : ℝ)⁻¹).indicator energy y
                ∂MeasureTheory.volume) := by
        ring
  calc
    ∫ y in caccioppoliCoreSet Q x, energy y ∂MeasureTheory.volume =
        ∫ y in caccioppoliCoreSet Q x, localCube.indicator energy y
          ∂MeasureTheory.volume := hcore_eq
    _ ≤ ∫ y in cubeSet Q, localCube.indicator energy y ∂MeasureTheory.volume := hmono
    _ =
        cubeVolume Q *
          coarseCaccioppoliLocalEnergyRadiusProfile Q x energy ((3 : ℝ)⁻¹) :=
      hprofile_eq

private theorem normalizedSetAverage_caccioppoliCoreSet_le_eighteen_pow_mul_localEnergyRadiusProfile
    {d : ℕ} (Q : TriadicCube d) {x : Vec d} {energy : Vec d → ℝ}
    (hx : x ∈ openCubeSet Q)
    (henergy_nonneg : ∀ y ∈ cubeSet Q, 0 ≤ energy y)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    normalizedSetAverage (caccioppoliCoreSet Q x) energy ≤
      (18 : ℝ) ^ d *
        coarseCaccioppoliLocalEnergyRadiusProfile Q x energy ((3 : ℝ)⁻¹) := by
  have hraw :=
    setIntegral_caccioppoliCoreSet_le_cubeVolume_mul_localEnergyRadiusProfile
      Q x henergy_nonneg henergy_int
  have hratio := caccioppoliCoreSet_volumeRatio_le_eighteen_pow Q hx
  have hprofile_nonneg :
      0 ≤ coarseCaccioppoliLocalEnergyRadiusProfile Q x energy ((3 : ℝ)⁻¹) := by
    simpa [coarseCaccioppoliLocalEnergyRadiusProfile] using
      coarseCaccioppoliLocalEnergyProfile_nonneg Q x ((3 : ℝ)⁻¹) henergy_nonneg
  unfold normalizedSetAverage
  calc
    (MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal⁻¹ *
        ∫ y in caccioppoliCoreSet Q x, energy y ∂MeasureTheory.volume ≤
        (MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal⁻¹ *
          (cubeVolume Q *
            coarseCaccioppoliLocalEnergyRadiusProfile Q x energy ((3 : ℝ)⁻¹)) := by
      exact mul_le_mul_of_nonneg_left hraw
        (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ =
        ((MeasureTheory.volume (caccioppoliCoreSet Q x)).toReal⁻¹ *
          cubeVolume Q) *
            coarseCaccioppoliLocalEnergyRadiusProfile Q x energy ((3 : ℝ)⁻¹) := by
      ring
    _ ≤
        (18 : ℝ) ^ d *
          coarseCaccioppoliLocalEnergyRadiusProfile Q x energy ((3 : ℝ)⁻¹) := by
      exact mul_le_mul_of_nonneg_right hratio hprofile_nonneg

private theorem boundary_scalarEnergy_normalizedCore_le_eighteen_pow_mul_localEnergyRadiusProfile
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : BoundaryCaccioppoliDatum Q a x)
    (hx : x ∈ openCubeSet Q) :
    normalizedSetAverage (caccioppoliCoreSet Q x)
        (fun y =>
          scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
            u.toPointwiseAHarmonic y) ≤
      (18 : ℝ) ^ d *
        coarseCaccioppoliLocalEnergyRadiusProfile Q x
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic y) ((3 : ℝ)⁻¹) := by
  let A : CoeffField d := pointwiseCoeffFor Q a
  let uPw : AHarmonicFunction A (openCubeSet Q) := u.toPointwiseAHarmonic
  let energy : Vec d → ℝ := fun y => scalarVariationEnergyIntegrand A uPw y
  have hctrl :
      CoarseCaccioppoliFluxEnergyControls Q A (1 : ℝ)
        (fun y => matVecMul (A y) (uPw.toCubeSet.toH1.grad y))
        (fun y => scalarVariationEnergyIntegrand A uPw.toCubeSet y) :=
    CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
      (Q := Q) (a := A) (s := (1 : ℝ)) (by norm_num)
      (pointwiseCoeffFor_isEllipticFieldOn_cubeSet Q a) uPw.toCubeSet
  have henergy_nonneg : ∀ y ∈ cubeSet Q, 0 ≤ energy y := by
    intro y hy
    simpa [energy, A, uPw, scalarVariationEnergyIntegrand] using hctrl.1 y hy
  have henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume := by
    simpa [energy, A, uPw, scalarVariationEnergyIntegrand] using hctrl.2.1
  simpa [energy, A, uPw] using
    normalizedSetAverage_caccioppoliCoreSet_le_eighteen_pow_mul_localEnergyRadiusProfile
      Q hx henergy_nonneg henergy_int

private theorem interior_scalarEnergy_normalizedCore_le_eighteen_pow_mul_localEnergyRadiusProfile
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : CubeSolution Q a) (hx : x ∈ openCubeSet Q) :
    normalizedSetAverage (caccioppoliCoreSet Q x)
        (fun y =>
          scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
            u.toPointwiseAHarmonic y) ≤
      (18 : ℝ) ^ d *
        coarseCaccioppoliLocalEnergyRadiusProfile Q x
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic y) ((3 : ℝ)⁻¹) := by
  let A : CoeffField d := pointwiseCoeffFor Q a
  let uPw : AHarmonicFunction A (openCubeSet Q) := u.toPointwiseAHarmonic
  let energy : Vec d → ℝ := fun y => scalarVariationEnergyIntegrand A uPw y
  have hctrl :
      CoarseCaccioppoliFluxEnergyControls Q A (1 : ℝ)
        (fun y => matVecMul (A y) (uPw.toCubeSet.toH1.grad y))
        (fun y => scalarVariationEnergyIntegrand A uPw.toCubeSet y) :=
    CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
      (Q := Q) (a := A) (s := (1 : ℝ)) (by norm_num)
      (pointwiseCoeffFor_isEllipticFieldOn_cubeSet Q a) uPw.toCubeSet
  have henergy_nonneg : ∀ y ∈ cubeSet Q, 0 ≤ energy y := by
    intro y hy
    simpa [energy, A, uPw, scalarVariationEnergyIntegrand] using hctrl.1 y hy
  have henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume := by
    simpa [energy, A, uPw, scalarVariationEnergyIntegrand] using hctrl.2.1
  simpa [energy, A, uPw] using
    normalizedSetAverage_caccioppoliCoreSet_le_eighteen_pow_mul_localEnergyRadiusProfile
      Q hx henergy_nonneg henergy_int

private theorem boundaryCaccioppoliCoreEnergy_eq_normalizedSetAverage_scalarEnergy_pointwise
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : BoundaryCaccioppoliDatum Q a x) :
    boundaryCaccioppoliCoreEnergy u =
      normalizedSetAverage (caccioppoliCoreSet Q x)
        (fun y =>
          scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
            u.toPointwiseAHarmonic y) := by
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  have hAopen :
      (a.coeffOn Q).toCoeffField
        =ᵐ[MeasureTheory.volume.restrict (openCubeSet Q)] pointwiseCoeffFor Q a := by
    simpa [pointwiseCoeffFor, U, Ch02.cubeDomain] using
      (Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq U (a.coeffOn Q)).symm
  have hAcore :
      (a.coeffOn Q).toCoeffField
        =ᵐ[MeasureTheory.volume.restrict (caccioppoliCoreSet Q x)]
          pointwiseCoeffFor Q a :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (fun y hy => hy.1) hAopen
  unfold boundaryCaccioppoliCoreEnergy localizedCoeffEnergyValue normalizedSetAverage
    volumeAverage
  congr 1
  exact MeasureTheory.integral_congr_ae <|
    hAcore.mono fun y hy => by
      simp [scalarVariationEnergyIntegrand, hy,
        BoundaryCaccioppoliDatum.toPointwiseAHarmonic]

private theorem interiorCaccioppoliCoreEnergy_eq_normalizedSetAverage_scalarEnergy_pointwise
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : CubeSolution Q a) :
    interiorCaccioppoliCoreEnergy Q a x u =
      normalizedSetAverage (caccioppoliCoreSet Q x)
        (fun y =>
          scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
            u.toPointwiseAHarmonic y) := by
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  have hAopen :
      (a.coeffOn Q).toCoeffField
        =ᵐ[MeasureTheory.volume.restrict (openCubeSet Q)] pointwiseCoeffFor Q a := by
    simpa [pointwiseCoeffFor, U, Ch02.cubeDomain] using
      (Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq U (a.coeffOn Q)).symm
  have hAcore :
      (a.coeffOn Q).toCoeffField
        =ᵐ[MeasureTheory.volume.restrict (caccioppoliCoreSet Q x)]
          pointwiseCoeffFor Q a :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (fun y hy => hy.1) hAopen
  unfold interiorCaccioppoliCoreEnergy localizedCoeffEnergyValue normalizedSetAverage
    volumeAverage
  congr 1
  exact MeasureTheory.integral_congr_ae <|
    hAcore.mono fun y hy => by
      simp [scalarVariationEnergyIntegrand, hy, CubeSolution.toPointwiseAHarmonic]

theorem boundaryCaccioppoliCoreEnergy_le_eighteen_pow_mul_localEnergyRadiusProfile
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : BoundaryCaccioppoliDatum Q a x)
    (hx : x ∈ openCubeSet Q) :
    boundaryCaccioppoliCoreEnergy u ≤
      (18 : ℝ) ^ d *
        coarseCaccioppoliLocalEnergyRadiusProfile Q x
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic y) ((3 : ℝ)⁻¹) := by
  calc
    boundaryCaccioppoliCoreEnergy u =
        normalizedSetAverage (caccioppoliCoreSet Q x)
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic y) :=
      boundaryCaccioppoliCoreEnergy_eq_normalizedSetAverage_scalarEnergy_pointwise u
    _ ≤
        (18 : ℝ) ^ d *
          coarseCaccioppoliLocalEnergyRadiusProfile Q x
            (fun y =>
              scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
                u.toPointwiseAHarmonic y) ((3 : ℝ)⁻¹) :=
      boundary_scalarEnergy_normalizedCore_le_eighteen_pow_mul_localEnergyRadiusProfile
        u hx

theorem interiorCaccioppoliCoreEnergy_le_eighteen_pow_mul_localEnergyRadiusProfile
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : CubeSolution Q a) (hx : x ∈ openCubeSet Q) :
    interiorCaccioppoliCoreEnergy Q a x u ≤
      (18 : ℝ) ^ d *
        coarseCaccioppoliLocalEnergyRadiusProfile Q x
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic y) ((3 : ℝ)⁻¹) := by
  calc
    interiorCaccioppoliCoreEnergy Q a x u =
        normalizedSetAverage (caccioppoliCoreSet Q x)
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic y) :=
      interiorCaccioppoliCoreEnergy_eq_normalizedSetAverage_scalarEnergy_pointwise u
    _ ≤
        (18 : ℝ) ^ d *
          coarseCaccioppoliLocalEnergyRadiusProfile Q x
            (fun y =>
              scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
                u.toPointwiseAHarmonic y) ((3 : ℝ)⁻¹) :=
      interior_scalarEnergy_normalizedCore_le_eighteen_pow_mul_localEnergyRadiusProfile
        u hx


end

end Ch03
end Book
end Homogenization
