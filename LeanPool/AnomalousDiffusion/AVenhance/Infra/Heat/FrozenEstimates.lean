/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.WeakFourier

/-! Heat-flow energy estimates for the periodic weak H1 carriers. -/

@[expose] public section

noncomputable section

open MeasureTheory
open AVenhance.Infra.Torus
open Homogenization

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance frozenHeatMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance frozenHeatIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance frozenHeatProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Heat

theorem FrozenEstimates.summable_sq_mFourierCoeff (f : TorusL2 2) :
    Summable fun k : Frequency => ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
  have hpow : (2 : ENNReal).toReal = 2 := by norm_num
  simpa only [hpow, Real.rpow_two, UnitAddTorus.mFourierBasis_repr] using
    ((UnitAddTorus.mFourierBasis.repr f).2).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)

theorem FrozenEstimates.normSq_heatWeakGradientMultiplier (m : ℤ) (z : ℂ) :
    ‖(2 * Real.pi * Complex.I * (m : ℂ)) * z‖ ^ 2 =
      (4 * Real.pi ^ 2) * (m : ℝ) ^ 2 * ‖z‖ ^ 2 := by
  simp only [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Real.abs_pi,
    Complex.norm_I, mul_one, Complex.norm_intCast]
  calc
    (2 * Real.pi * |(m : ℝ)| * ‖z‖) ^ 2 =
        (2 * Real.pi) ^ 2 * |(m : ℝ)| ^ 2 * ‖z‖ ^ 2 := by ring
    _ = (4 * Real.pi ^ 2) * (m : ℝ) ^ 2 * ‖z‖ ^ 2 := by
      rw [sq_abs]
      ring

theorem FrozenEstimates.frozenH1_energyTerm_eq_gradientCoeffSum
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) (k : Frequency) :
    fourierEnergyTerm (frozenPeriodicH1ValueL2 h) k =
      ∑ i : Fin 2,
        ‖UnitAddTorus.mFourierCoeff
          (frozenPeriodicH1GradientL2 h i) k‖ ^ 2 := by
  have hfreq : frequencySq k = (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 := by
    unfold frequencySq
    simp
  have h0 := mFourierCoeff_frozenPeriodicH1GradientL2 h (0 : Fin 2) k
  have h1 := mFourierCoeff_frozenPeriodicH1GradientL2 h (1 : Fin 2) k
  have hnorm0 :
      ‖UnitAddTorus.mFourierCoeff
          (frozenPeriodicH1GradientL2 h (0 : Fin 2)) k‖ ^ 2 =
        (4 * Real.pi ^ 2) * (k 0 : ℝ) ^ 2 *
          ‖UnitAddTorus.mFourierCoeff (frozenPeriodicH1ValueL2 h) k‖ ^ 2 := by
    rw [h0]
    exact FrozenEstimates.normSq_heatWeakGradientMultiplier (k 0)
      (UnitAddTorus.mFourierCoeff (frozenPeriodicH1ValueL2 h) k)
  have hnorm1 :
      ‖UnitAddTorus.mFourierCoeff
          (frozenPeriodicH1GradientL2 h (1 : Fin 2)) k‖ ^ 2 =
        (4 * Real.pi ^ 2) * (k 1 : ℝ) ^ 2 *
          ‖UnitAddTorus.mFourierCoeff (frozenPeriodicH1ValueL2 h) k‖ ^ 2 := by
    rw [h1]
    exact FrozenEstimates.normSq_heatWeakGradientMultiplier (k 1)
      (UnitAddTorus.mFourierCoeff (frozenPeriodicH1ValueL2 h) k)
  calc
    fourierEnergyTerm (frozenPeriodicH1ValueL2 h) k =
        (4 * Real.pi ^ 2) *
            ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2) *
              ‖UnitAddTorus.mFourierCoeff
                (frozenPeriodicH1ValueL2 h) k‖ ^ 2 := by
          simp [fourierEnergyTerm, hfreq]
    _ = ((4 * Real.pi ^ 2) * (k 0 : ℝ) ^ 2 *
          ‖UnitAddTorus.mFourierCoeff
            (frozenPeriodicH1ValueL2 h) k‖ ^ 2) +
        (4 * Real.pi ^ 2) * (k 1 : ℝ) ^ 2 *
          ‖UnitAddTorus.mFourierCoeff
            (frozenPeriodicH1ValueL2 h) k‖ ^ 2 := by ring
    _ = ‖UnitAddTorus.mFourierCoeff
          (frozenPeriodicH1GradientL2 h (0 : Fin 2)) k‖ ^ 2 +
        ‖UnitAddTorus.mFourierCoeff
          (frozenPeriodicH1GradientL2 h (1 : Fin 2)) k‖ ^ 2 := by
          rw [← hnorm0, ← hnorm1]
    _ = ∑ i : Fin 2,
          ‖UnitAddTorus.mFourierCoeff
            (frozenPeriodicH1GradientL2 h i) k‖ ^ 2 := by simp

theorem FrozenEstimates.integrableOn_sq_of_memL2On {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) :
    IntegrableOn (fun x => f x ^ 2) AVenhance.unitCube := by
  have hbase := hf.integrable_norm_rpow (by norm_num) (by norm_num)
  change Integrable (fun x => f x ^ 2)
    (volume.restrict AVenhance.unitCube)
  convert hbase using 1
  norm_num [Real.norm_eq_abs, sq_abs, Real.rpow_natCast]

theorem FrozenEstimates.gradNormSq_eq_sum_componentL2 {Du : Vec 2 → Vec 2}
    (hDu : GradMemL2On AVenhance.unitCube Du) :
    AVenhance.gradNormSq Du =
      ∑ i : Fin 2, AVenhance.l2NormSq (fun x => Du x i) := by
  have hInt : ∀ i : Fin 2,
      IntegrableOn (fun x : Vec 2 => Du x i ^ 2) AVenhance.unitCube := by
    intro i
    exact FrozenEstimates.integrableOn_sq_of_memL2On (hDu i)
  have hsum := integral_finsetSum (Finset.univ : Finset (Fin 2))
    (μ := (volume : Measure (Vec 2)).restrict AVenhance.unitCube)
    (f := fun i : Fin 2 => fun x => Du x i ^ 2)
    (fun i hi => hInt i)
  calc
    AVenhance.gradNormSq Du =
        ∫ x in AVenhance.unitCube, ∑ i : Fin 2, Du x i ^ 2 := by
          unfold AVenhance.gradNormSq
          apply integral_congr_ae
          filter_upwards with x
          simp [Homogenization.vecNormSq, Homogenization.vecDot, pow_two]
    _ = ∑ i : Fin 2, ∫ x in AVenhance.unitCube, Du x i ^ 2 := by
          simpa using hsum
    _ = ∑ i : Fin 2, AVenhance.l2NormSq (fun x => Du x i) := by
          simp [AVenhance.l2NormSq]

/-- The Fourier Dirichlet energy of any periodic weak H1 value is finite. -/
theorem hasFiniteFourierEnergy_frozenPeriodicH1
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) :
    HasFiniteFourierEnergy (frozenPeriodicH1ValueL2 h) := by
  have h0 := FrozenEstimates.summable_sq_mFourierCoeff (frozenPeriodicH1GradientL2 h 0)
  have h1 := FrozenEstimates.summable_sq_mFourierCoeff (frozenPeriodicH1GradientL2 h 1)
  have hsum : Summable fun k : Frequency =>
      ∑ i : Fin 2,
        ‖UnitAddTorus.mFourierCoeff
          (frozenPeriodicH1GradientL2 h i) k‖ ^ 2 := by
    simpa using h0.add h1
  refine hsum.congr ?_
  intro k
  exact (FrozenEstimates.frozenH1_energyTerm_eq_gradientCoeffSum h k).symm

/-- Parseval identifies the spectral Dirichlet energy with the squared
weak-gradient norm for arbitrary IsPeriodicH1With data. -/
theorem fourierEnergy_frozenPeriodicH1_eq_gradNormSq
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) :
    fourierEnergy (frozenPeriodicH1ValueL2 h) = AVenhance.gradNormSq Du := by
  have h0 := FrozenEstimates.summable_sq_mFourierCoeff (frozenPeriodicH1GradientL2 h 0)
  have h1 := FrozenEstimates.summable_sq_mFourierCoeff (frozenPeriodicH1GradientL2 h 1)
  have hpoint := fun k => FrozenEstimates.frozenH1_energyTerm_eq_gradientCoeffSum h k
  have hgradNorm0 := norm_sq_eq_tsum_fourierCoeff
    (frozenPeriodicH1GradientL2 h 0)
  have hgradNorm1 := norm_sq_eq_tsum_fourierCoeff
    (frozenPeriodicH1GradientL2 h 1)
  calc
    fourierEnergy (frozenPeriodicH1ValueL2 h) =
        ∑' k : Frequency, fourierEnergyTerm
          (frozenPeriodicH1ValueL2 h) k := rfl
    _ = ∑' k : Frequency,
        (‖UnitAddTorus.mFourierCoeff
            (frozenPeriodicH1GradientL2 h 0) k‖ ^ 2 +
          ‖UnitAddTorus.mFourierCoeff
            (frozenPeriodicH1GradientL2 h 1) k‖ ^ 2) := by
          apply tsum_congr
          intro k
          simpa using hpoint k
    _ = (∑' k : Frequency,
          ‖UnitAddTorus.mFourierCoeff
            (frozenPeriodicH1GradientL2 h 0) k‖ ^ 2) +
        (∑' k : Frequency,
          ‖UnitAddTorus.mFourierCoeff
            (frozenPeriodicH1GradientL2 h 1) k‖ ^ 2) := by
          rw [← h0.tsum_add h1]
    _ = ‖frozenPeriodicH1GradientL2 h 0‖ ^ 2 +
        ‖frozenPeriodicH1GradientL2 h 1‖ ^ 2 := by
          rw [← hgradNorm0, ← hgradNorm1]
    _ = AVenhance.gradNormSq Du := by
          have hgrad0 :
              ‖frozenPeriodicH1GradientL2 h 0‖ ^ 2 =
                AVenhance.l2NormSq (fun x => Du x 0) := by
            change ‖frozenCellToTorusL2 (h.2.2.2.1 0)‖ ^ 2 = _
            exact normSq_frozenCellToTorusL2_eq (h.2.2.2.1 0)
          have hgrad1 :
              ‖frozenPeriodicH1GradientL2 h 1‖ ^ 2 =
                AVenhance.l2NormSq (fun x => Du x 1) := by
            change ‖frozenCellToTorusL2 (h.2.2.2.1 1)‖ ^ 2 = _
            exact normSq_frozenCellToTorusL2_eq (h.2.2.2.1 1)
          rw [hgrad0, hgrad1]
          simpa using (FrozenEstimates.gradNormSq_eq_sum_componentL2 h.2.2.2.1).symm

theorem FrozenEstimates.frozenPeriodicH1Value_norm
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) :
    ‖frozenPeriodicH1ValueL2 h‖ = Real.sqrt (AVenhance.l2NormSq u) := by
  have hsq := normSq_frozenCellToTorusL2_eq h.2.2.1
  calc
    ‖frozenPeriodicH1ValueL2 h‖ =
        Real.sqrt (‖frozenPeriodicH1ValueL2 h‖ ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ = Real.sqrt (AVenhance.l2NormSq u) := congrArg Real.sqrt hsq

theorem FrozenEstimates.frozenPeriodicH1Value_normSq
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) :
    ‖frozenPeriodicH1ValueL2 h‖ ^ 2 = AVenhance.l2NormSq u := by
  change ‖frozenCellToTorusL2 h.2.2.1‖ ^ 2 = _
  exact normSq_frozenCellToTorusL2_eq h.2.2.1

theorem FrozenEstimates.l2NormSq_nonneg (u : Vec 2 → ℝ) :
    0 ≤ AVenhance.l2NormSq u := by
  unfold AVenhance.l2NormSq
  exact integral_nonneg fun x => sq_nonneg (u x)

theorem FrozenEstimates.heatGradNormSq_nonneg (Du : Vec 2 → Vec 2) :
    0 ≤ AVenhance.gradNormSq Du := by
  unfold AVenhance.gradNormSq
  exact integral_nonneg fun x => Homogenization.vecNormSq_nonneg (Du x)

/-- The heat approximation error is at most s times the squared weak
gradient norm for arbitrary periodic H1 data. -/
theorem normSq_sub_heatTorusL2_le_frozenPeriodicH1
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) {s : ℝ} (hs : 0 ≤ s) :
    ‖frozenPeriodicH1ValueL2 h -
        heatTorusL2 s hs (frozenPeriodicH1ValueL2 h)‖ ^ 2 ≤
      s * AVenhance.gradNormSq Du := by
  have hE := hasFiniteFourierEnergy_frozenPeriodicH1 h
  have happrox := normSq_sub_heatTorusL2_le hs
    (frozenPeriodicH1ValueL2 h) hE
  rw [fourierEnergy_frozenPeriodicH1_eq_gradNormSq h] at happrox
  exact happrox

theorem FrozenEstimates.torusCharacter_zero (x : Vec 2) :
    torusCharacter (0 : Frequency) x = 1 := by
  simp [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk]

theorem FrozenEstimates.frozenPeriodicH1_zeroCoeff
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du)
    (hmean : Homogenization.MeanZeroOn AVenhance.unitCube u) :
    UnitAddTorus.mFourierCoeff (frozenPeriodicH1ValueL2 h) 0 = 0 := by
  change UnitAddTorus.mFourierCoeff
    (frozenCellToTorusL2 h.2.2.1) 0 = 0
  rw [mFourierCoeff_frozenCellToTorusL2 h.2.2.1]
  have hcell : ∫ x in unitCell 2, u x = 0 := by
    rw [integral_unitCell_eq_unitCube]
    exact hmean
  have hcellC : ∫ x in unitCell 2, (u x : ℂ) = 0 := by
    calc
      ∫ x in unitCell 2, (u x : ℂ) =
          ((∫ x in unitCell 2, u x : ℝ) : ℂ) := by
            exact integral_ofReal
      _ = 0 := by rw [hcell]; simp
  calc
    ∫ x in unitCell 2, torusCharacter 0 x * (u x : ℂ) =
        ∫ x in unitCell 2, (u x : ℂ) := by
          apply setIntegral_congr_fun (measurableSet_unitCell 2)
          intro x hx
          change torusCharacter 0 x * (u x : ℂ) = (u x : ℂ)
          rw [FrozenEstimates.torusCharacter_zero]
          simp
    _ = 0 := hcellC

theorem FrozenEstimates.frozenPeriodicH1_torusMeanZero
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du)
    (hmean : Homogenization.MeanZeroOn AVenhance.unitCube u) :
    ∫ x : UnitAddTorus (Fin 2), frozenPeriodicH1ValueL2 h x = 0 := by
  have hzero := FrozenEstimates.frozenPeriodicH1_zeroCoeff h hmean
  simpa [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier_zero] using hzero

/-- Mean-zero periodic H1 data satisfy the mean-zero torus Poincare bound,
written in the carriers. -/
theorem meanZero_frozenPeriodicH1_fourierPoincare
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du)
    (hmean : Homogenization.MeanZeroOn AVenhance.unitCube u) :
    AVenhance.l2NormSq u ≤ (4 * Real.pi ^ 2)⁻¹ * AVenhance.gradNormSq Du := by
  have hE := hasFiniteFourierEnergy_frozenPeriodicH1 h
  have hmeanTorus := FrozenEstimates.frozenPeriodicH1_torusMeanZero h hmean
  have hP := meanZero_fourierPoincare hmeanTorus hE
  rw [FrozenEstimates.frozenPeriodicH1Value_normSq h,
    fourierEnergy_frozenPeriodicH1_eq_gradNormSq h] at hP
  exact hP

end AVenhance.Infra.Heat
