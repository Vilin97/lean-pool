/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.Semigroup

/-! Spectral energy identity and the quantitative heat-flow deficit estimate. -/

@[expose] public section

noncomputable section

open MeasureTheory
open AVenhance.Infra.Torus
open Homogenization

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraHeatEnergyMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraHeatEnergyMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraHeatEnergyIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure
    UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Heat

/-- The Fourier expression for the squared torus `L²` norm. -/
theorem norm_sq_eq_tsum_fourierCoeff (f : TorusL2 2) :
    ‖f‖ ^ 2 = ∑' k : Frequency, ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
  rw [← UnitAddTorus.mFourierBasis.repr.norm_map f]
  have h := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ENNReal).toReal) (UnitAddTorus.mFourierBasis.repr f)
  have hpow : (2 : ENNReal).toReal = 2 := by norm_num
  simpa [hpow, UnitAddTorus.mFourierBasis_repr, Real.rpow_two] using h

/-- The spectral Dirichlet energy on the torus. -/
def fourierEnergyTerm (f : TorusL2 2) (k : Frequency) : ℝ :=
  4 * Real.pi ^ 2 * frequencySq k * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2

/-- Finite Fourier Dirichlet energy, stated as summability of its nonnegative terms. -/
def HasFiniteFourierEnergy (f : TorusL2 2) : Prop :=
  Summable (fourierEnergyTerm f)

/-- The spectral Dirichlet energy associated with the Fourier coefficients. -/
noncomputable def fourierEnergy (f : TorusL2 2) : ℝ :=
  ∑' k : Frequency, fourierEnergyTerm f k

theorem Energy.fourierEnergyTerm_nonneg (f : TorusL2 2) (k : Frequency) :
    0 ≤ fourierEnergyTerm f k := by
  unfold fourierEnergyTerm
  have hq : 0 ≤ frequencySq k := by
    unfold frequencySq
    exact Finset.sum_nonneg fun i hi => sq_nonneg (k i : ℝ)
  positivity

theorem Energy.heatMultiplier_sq {s : ℝ} (k : Frequency) :
    heatMultiplier s k ^ 2 =
      Real.exp (-(8 * Real.pi ^ 2 * s * frequencySq k)) := by
  rw [heatMultiplier]
  calc
    Real.exp (-(4 * Real.pi ^ 2 * s * frequencySq k)) ^ 2 =
        Real.exp (-(4 * Real.pi ^ 2 * s * frequencySq k) +
          -(4 * Real.pi ^ 2 * s * frequencySq k)) := by
      rw [pow_two, ← Real.exp_add]
    _ = Real.exp (-(8 * Real.pi ^ 2 * s * frequencySq k)) := by
      congr 1
      ring

theorem Energy.mFourierCoeff_sub_heat {s : ℝ} (hs : 0 ≤ s)
    (f : TorusL2 2) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (f - heatTorusL2 s hs f) k =
      (1 - heatMultiplier s k : ℂ) * UnitAddTorus.mFourierCoeff f k := by
  have hrepr :
      UnitAddTorus.mFourierBasis.repr (f - heatTorusL2 s hs f) =
        UnitAddTorus.mFourierBasis.repr f -
          UnitAddTorus.mFourierBasis.repr (heatTorusL2 s hs f) :=
    UnitAddTorus.mFourierBasis.repr.map_sub f (heatTorusL2 s hs f)
  calc
    UnitAddTorus.mFourierCoeff (f - heatTorusL2 s hs f) k =
        UnitAddTorus.mFourierBasis.repr (f - heatTorusL2 s hs f) k :=
      (UnitAddTorus.mFourierBasis_repr (f - heatTorusL2 s hs f) k).symm
    _ = (UnitAddTorus.mFourierBasis.repr f -
          UnitAddTorus.mFourierBasis.repr (heatTorusL2 s hs f)) k :=
      congrArg (fun a : lp (fun _ : Frequency => ℂ) 2 => a k) hrepr
    _ = UnitAddTorus.mFourierBasis.repr f k -
        UnitAddTorus.mFourierBasis.repr (heatTorusL2 s hs f) k := by
      rfl
    _ = UnitAddTorus.mFourierCoeff f k -
        UnitAddTorus.mFourierCoeff (heatTorusL2 s hs f) k := by
      rw [UnitAddTorus.mFourierBasis_repr f k,
        UnitAddTorus.mFourierBasis_repr (heatTorusL2 s hs f) k]
    _ = (1 - heatMultiplier s k : ℂ) * UnitAddTorus.mFourierCoeff f k := by
      rw [mFourierCoeff_heatTorusL2 hs]
      ring

/-- The `L²` error between a function and its heat regularization is bounded
by `s` times the spectral Dirichlet energy. -/
theorem normSq_sub_heatTorusL2_le {s : ℝ} (hs : 0 ≤ s)
    (f : TorusL2 2) (hE : HasFiniteFourierEnergy f) :
    ‖f - heatTorusL2 s hs f‖ ^ 2 ≤ s * fourierEnergy f := by
  have hdiffSummable : Summable fun k : Frequency =>
      ‖UnitAddTorus.mFourierCoeff (f - heatTorusL2 s hs f) k‖ ^ 2 := by
    have hpow : (2 : ENNReal).toReal = 2 := by norm_num
    simpa only [hpow, Real.rpow_two, UnitAddTorus.mFourierBasis_repr] using
      ((UnitAddTorus.mFourierBasis.repr (f - heatTorusL2 s hs f)).2).summable
        (by norm_num : 0 < (2 : ENNReal).toReal)
  have hscaledEnergy : Summable fun k : Frequency => s * fourierEnergyTerm f k :=
    hE.mul_left s
  rw [norm_sq_eq_tsum_fourierCoeff (f - heatTorusL2 s hs f), fourierEnergy,
    ← hE.tsum_mul_left s]
  refine Summable.tsum_le_tsum ?_ hdiffSummable hscaledEnergy
  intro k
  rw [Energy.mFourierCoeff_sub_heat hs]
  let x : ℝ := 4 * Real.pi ^ 2 * s * frequencySq k
  let t : ℝ := 1 - Real.exp (-x)
  have hx : 0 ≤ x := by
    dsimp [x]
    have hq : 0 ≤ frequencySq k := by
      unfold frequencySq
      exact Finset.sum_nonneg fun i hi => sq_nonneg (k i : ℝ)
    positivity
  have ht0 : 0 ≤ t := by
    have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    dsimp [t]
    linarith
  have ht1 : t ≤ 1 := by
    dsimp [t]
    linarith [Real.exp_pos (-x)]
  have htx : t ≤ x := by
    dsimp [t]
    have h := Real.one_sub_le_exp_neg x
    linarith
  have htsq : t ^ 2 ≤ x := by
    have hsq : t ^ 2 ≤ t := by nlinarith [mul_le_mul_of_nonneg_left ht1 ht0]
    exact hsq.trans htx
  have hweight : heatMultiplier s k = Real.exp (-x) := by
    rfl
  have hweightNorm : ‖1 - (heatMultiplier s k : ℂ)‖ = t := by
    rw [hweight]
    have hcast : (1 : ℂ) - (Real.exp (-x) : ℂ) = ((1 - Real.exp (-x) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hcoefSq :
      ‖(1 - (heatMultiplier s k : ℂ)) * UnitAddTorus.mFourierCoeff f k‖ ^ 2 =
        t ^ 2 * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
    rw [norm_mul, hweightNorm]
    ring
  rw [hcoefSq]
  calc
    t ^ 2 * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 ≤
        x * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right htsq (sq_nonneg _)
    _ = s * fourierEnergyTerm f k := by
      dsimp [x, fourierEnergyTerm]
      ring

theorem Energy.frequencySq_ge_one_of_ne_zero (k : Frequency) (hk : k ≠ 0) :
    1 ≤ frequencySq k := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  have habs : (1 : ℤ) ≤ |k i| := by
    have hp : 0 < |k i| := abs_pos.mpr hi
    omega
  have habsR : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast habs
  have hsq : 1 ≤ (k i : ℝ) ^ 2 := by nlinarith [sq_abs (k i : ℝ)]
  have hsum : (k i : ℝ) ^ 2 ≤ frequencySq k := by
    unfold frequencySq
    exact Finset.single_le_sum
      (fun j hj => sq_nonneg (k j : ℝ)) (Finset.mem_univ i)
  exact hsq.trans hsum

/-- Mean-zero Poincaré inequality for arbitrary torus `L²` functions with
finite spectral Dirichlet energy. -/
theorem meanZero_fourierPoincare {f : TorusL2 2}
    (hmean : ∫ x : UnitAddTorus (Fin 2), f x = 0)
    (hE : HasFiniteFourierEnergy f) :
    ‖f‖ ^ 2 ≤ (4 * Real.pi ^ 2)⁻¹ * fourierEnergy f := by
  have hzero : UnitAddTorus.mFourierCoeff f (0 : Frequency) = 0 := by
    simpa [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier_zero] using hmean
  have hcoeffSummable : Summable fun k : Frequency =>
      ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
    have hpow : (2 : ENNReal).toReal = 2 := by norm_num
    simpa only [hpow, Real.rpow_two, UnitAddTorus.mFourierBasis_repr] using
      ((UnitAddTorus.mFourierBasis.repr f).2).summable
        (by norm_num : 0 < (2 : ENNReal).toReal)
  have hscaledEnergy : Summable fun k : Frequency =>
      (4 * Real.pi ^ 2)⁻¹ * fourierEnergyTerm f k :=
    hE.mul_left ((4 * Real.pi ^ 2)⁻¹)
  rw [norm_sq_eq_tsum_fourierCoeff f, fourierEnergy,
    ← hE.tsum_mul_left ((4 * Real.pi ^ 2)⁻¹)]
  refine Summable.tsum_le_tsum ?_ hcoeffSummable hscaledEnergy
  intro k
  by_cases hk : k = 0
  · subst k
    simp [hzero, fourierEnergyTerm, frequencySq]
  · have hfreq := Energy.frequencySq_ge_one_of_ne_zero k hk
    have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
    have hbase : 4 * Real.pi ^ 2 ≤ 4 * Real.pi ^ 2 * frequencySq k := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfreq hpi.le
    have hcoeff : 0 ≤ ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 := sq_nonneg _
    calc
      ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 =
          (4 * Real.pi ^ 2)⁻¹ *
            ((4 * Real.pi ^ 2) * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2) := by
        field_simp [ne_of_gt hpi]
      _ ≤ (4 * Real.pi ^ 2)⁻¹ *
          ((4 * Real.pi ^ 2) * frequencySq k *
            ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpi.le)
        exact mul_le_mul_of_nonneg_right hbase hcoeff
      _ = (4 * Real.pi ^ 2)⁻¹ * fourierEnergyTerm f k := by
        rfl

theorem Energy.normSq_fourierGradientMultiplier (m : ℤ) (z : ℂ) :
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

theorem Energy.smoothGradientFourierCoeff_eq_frequency {g : Vec 2 → ℂ}
    (hg : ContDiff ℝ 1 g) (hpg : IsZdPeriodic g) (k : Frequency) :
    (∑ i : Fin 2, ‖smoothFourierCoeff (coordDeriv i g) k‖ ^ 2) =
      (4 * Real.pi ^ 2) * frequencySq k * ‖smoothFourierCoeff g k‖ ^ 2 := by
  calc
    ∑ i : Fin 2, ‖smoothFourierCoeff (coordDeriv i g) k‖ ^ 2 =
        ∑ i : Fin 2,
          (4 * Real.pi ^ 2) * (k i : ℝ) ^ 2 * ‖smoothFourierCoeff g k‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [smoothFourierCoeff_coordDeriv i hg hpg k]
      exact Energy.normSq_fourierGradientMultiplier (k i) (smoothFourierCoeff g k)
    _ = (4 * Real.pi ^ 2) * frequencySq k * ‖smoothFourierCoeff g k‖ ^ 2 := by
      simp only [frequencySq]
      calc
        _ = ∑ i : Fin 2,
            (4 * Real.pi ^ 2) * ((k i : ℝ) ^ 2 * ‖smoothFourierCoeff g k‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (4 * Real.pi ^ 2) *
            ∑ i : Fin 2, (k i : ℝ) ^ 2 * ‖smoothFourierCoeff g k‖ ^ 2 := by
          rw [Finset.mul_sum]
        _ = (4 * Real.pi ^ 2) *
            ((∑ i : Fin 2, (k i : ℝ) ^ 2) * ‖smoothFourierCoeff g k‖ ^ 2) := by
          rw [Finset.sum_mul]
        _ = (4 * Real.pi ^ 2) * frequencySq k * ‖smoothFourierCoeff g k‖ ^ 2 := by
          simp [frequencySq]
          ring

theorem Energy.periodicToTorusL2_fourierCoeff_eq_heat {g : Vec 2 → ℂ}
    (hg : Continuous g) (k : Frequency) :
    periodicL2FourierCoeff (periodicToTorusL2 g hg) k = smoothFourierCoeff g k := by
  let hmem := memLp_periodicToTorus hg
  calc
    periodicL2FourierCoeff (periodicToTorusL2 g hg) k =
        ∫ y : UnitAddTorus (Fin 2),
          UnitAddTorus.mFourier (-k) y * periodicToTorus g y := by
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp] with y hy
      exact congrArg (fun z : ℂ => UnitAddTorus.mFourier (-k) y * z) hy
    _ = ∫ x in unitCell 2, torusCharacter k x * g x := by
      rw [← integral_periodicToTorus_eq_unitCell
        (fun x : Vec 2 => torusCharacter k x * g x)]
      apply integral_congr_ae
      filter_upwards with y
      change UnitAddTorus.mFourier (-k) y * g (unitTorusRepresentative 2 y) =
        UnitAddTorus.mFourier (-k)
          (toUnitTorus 2 (unitTorusRepresentative 2 y)) *
            g (unitTorusRepresentative 2 y)
      rw [toUnitTorus_unitTorusRepresentative]

/-- For a smooth periodic function, the spectral Dirichlet energy is exactly
the cell integral of the squared gradient. -/
theorem hasFiniteFourierEnergy_periodicToTorusL2 {g : Vec 2 → ℂ}
    (hg : ContDiff ℝ 1 g) (hpg : IsZdPeriodic g) :
    HasFiniteFourierEnergy (periodicToTorusL2 g hg.continuous) ∧
      fourierEnergy (periodicToTorusL2 g hg.continuous) =
        ∫ x in unitCell 2, ∑ i : Fin 2, ‖coordDeriv i g x‖ ^ 2 := by
  let u := periodicToTorusL2 g hg.continuous
  have hgradient := hasSum_sq_smoothGradientFourierCoeff hg
  rw [integral_unitCell_gradSq_eq_sum_coord hg] at hgradient
  have hsum : HasSum (fourierEnergyTerm u)
      (∫ x in unitCell 2, ∑ i : Fin 2, ‖coordDeriv i g x‖ ^ 2) := by
    refine hgradient.congr_fun ?_
    intro k
    rw [fourierEnergyTerm]
    have hcoeff := Energy.periodicToTorusL2_fourierCoeff_eq_heat hg.continuous k
    change
      (4 * Real.pi ^ 2) * frequencySq k *
          ‖periodicL2FourierCoeff u k‖ ^ 2 =
        ∑ i : Fin 2, ‖smoothFourierCoeff (coordDeriv i g) k‖ ^ 2
    rw [hcoeff]
    exact (Energy.smoothGradientFourierCoeff_eq_frequency hg hpg k).symm
  refine ⟨hsum.summable, ?_⟩
  exact hsum.tsum_eq

/-- Real smooth periodic functions enter the gradient-energy carrier. -/
theorem hasFiniteFourierEnergy_realSmooth {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hpf : AVenhance.IsZ2Periodic f) :
    HasFiniteFourierEnergy
        (periodicToTorusL2 (realToComplex f)
          (Complex.ofRealCLM.contDiff.comp hf).continuous) ∧
      fourierEnergy
          (periodicToTorusL2 (realToComplex f)
            (Complex.ofRealCLM.contDiff.comp hf).continuous) =
        AVenhance.gradNormSq (AVenhance.spaceGrad f) := by
  have hpc : IsZdPeriodic (realToComplex f) := by
    intro k x
    have h := (isZdPeriodic_iff_frozen f).2 hpf k x
    exact congrArg (fun y : ℝ => (y : ℂ)) h
  have hcomplex : ContDiff ℝ 1 (realToComplex f) :=
    Complex.ofRealCLM.contDiff.comp hf
  obtain ⟨hfinite, henergy⟩ :=
    hasFiniteFourierEnergy_periodicToTorusL2 hcomplex hpc
  have hcell :
      (∫ x in unitCell 2,
        ∑ i : Fin 2, ‖coordDeriv i (realToComplex f) x‖ ^ 2) =
        AVenhance.gradNormSq (AVenhance.spaceGrad f) := by
    calc
      _ = ∫ x in unitCell 2, Homogenization.vecNormSq (AVenhance.spaceGrad f x) := by
        apply setIntegral_congr_fun (measurableSet_unitCell 2)
        intro x hx
        simp [Homogenization.vecNormSq, Homogenization.vecDot,
          coordDeriv_realToComplex hf]
        ring
      _ = ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq (AVenhance.spaceGrad f x) :=
        integral_unitCell_eq_unitCube _
      _ = AVenhance.gradNormSq (AVenhance.spaceGrad f) := rfl
  exact ⟨hfinite, henergy.trans hcell⟩

end AVenhance.Infra.Heat
