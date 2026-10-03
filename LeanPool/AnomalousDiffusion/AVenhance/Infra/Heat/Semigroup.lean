/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Fourier
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Calculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-! Fourier definition of the periodic heat semigroup on the two dimensional torus. -/

@[expose] public section

noncomputable section

open MeasureTheory
open AVenhance.Infra.Torus

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraHeatSemigroupMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraHeatSemigroupMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraHeatSemigroupIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure
    UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Heat

/-- Two-dimensional integer frequencies for the periodic heat equation. -/
abbrev Frequency := Fin 2 → ℤ

/-- The squared Euclidean length of an integer torus frequency. -/
def frequencySq (k : Frequency) : ℝ :=
  ∑ i : Fin 2, (k i : ℝ) ^ 2

/-- The Fourier multiplier of the heat flow at time `s`. -/
def heatMultiplier (s : ℝ) (k : Frequency) : ℝ :=
  Real.exp (-(4 * Real.pi ^ 2 * s * frequencySq k))

theorem Semigroup.frequencySq_nonneg (k : Frequency) : 0 ≤ frequencySq k := by
  unfold frequencySq
  exact Finset.sum_nonneg fun i hi => sq_nonneg (k i : ℝ)

theorem Semigroup.heatMultiplier_nonneg (s : ℝ) (k : Frequency) :
    0 ≤ heatMultiplier s k := (Real.exp_pos _).le

theorem Semigroup.heatMultiplier_le_one {s : ℝ} (hs : 0 ≤ s) (k : Frequency) :
    heatMultiplier s k ≤ 1 := by
  rw [heatMultiplier, Real.exp_le_one_iff]
  have hpi : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  exact neg_nonpos.mpr (mul_nonneg (mul_nonneg hpi hs) (Semigroup.frequencySq_nonneg k))

theorem Semigroup.heatMultiplier_add (s t : ℝ) (k : Frequency) :
    heatMultiplier (s + t) k = heatMultiplier s k * heatMultiplier t k := by
  simp only [heatMultiplier]
  rw [show -(4 * Real.pi ^ 2 * (s + t) * frequencySq k) =
      -(4 * Real.pi ^ 2 * s * frequencySq k) +
        -(4 * Real.pi ^ 2 * t * frequencySq k) by ring,
    Real.exp_add]

/-- Apply the heat multiplier to each Fourier coefficient. -/
def Semigroup.heatSequence (s : ℝ) (a : Frequency → ℂ) : Frequency → ℂ :=
  fun k => (heatMultiplier s k : ℂ) * a k

theorem Semigroup.memℓp_heatSequence {s : ℝ} (hs : 0 ≤ s)
    (a : Frequency → ℂ) (ha : Memℓp a 2) : Memℓp (Semigroup.heatSequence s a) 2 := by
  refine Memℓp.mono' ha ?_
  intro k
  change ‖(heatMultiplier s k : ℂ) * a k‖ ≤ ‖a k‖
  rw [norm_mul, Complex.norm_real]
  have hnorm : ‖heatMultiplier s k‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Semigroup.heatMultiplier_nonneg s k)]
    exact Semigroup.heatMultiplier_le_one hs k
  exact mul_le_of_le_one_left (norm_nonneg _) hnorm

/-- Fourier coefficients after heat evolution, regarded as an `ℓ²` sequence. -/
noncomputable def heatFourierSequence (s : ℝ) (hs : 0 ≤ s) (f : TorusL2 2) :
    lp (fun _ : Frequency => ℂ) 2 := by
  let a : Frequency → ℂ := fun k => UnitAddTorus.mFourierBasis.repr f k
  have ha : Memℓp a 2 := by
    change Memℓp (fun k => UnitAddTorus.mFourierBasis.repr f k) 2
    exact (UnitAddTorus.mFourierBasis.repr f).2
  exact ⟨Semigroup.heatSequence s a, Semigroup.memℓp_heatSequence hs a ha⟩

/-- The torus heat semigroup, defined by the multiplier `exp(-4π²s|k|²)`. -/
noncomputable def heatTorusL2 (s : ℝ) (hs : 0 ≤ s) (f : TorusL2 2) : TorusL2 2 :=
  UnitAddTorus.mFourierBasis.repr.symm (heatFourierSequence s hs f)

/-- The multiplier formula for every Fourier coefficient of the heat flow. -/
theorem mFourierCoeff_heatTorusL2 {s : ℝ} (hs : 0 ≤ s) (f : TorusL2 2)
    (k : Frequency) :
    UnitAddTorus.mFourierCoeff (heatTorusL2 s hs f) k =
      (heatMultiplier s k : ℂ) * UnitAddTorus.mFourierCoeff f k := by
  rw [← UnitAddTorus.mFourierBasis_repr (heatTorusL2 s hs f) k]
  simp only [heatTorusL2, LinearIsometryEquiv.apply_symm_apply,
    heatFourierSequence, Semigroup.heatSequence]
  rw [← UnitAddTorus.mFourierBasis_repr f k]

/-- Heat flow preserves the integral, since its zero Fourier mode is unchanged. -/
theorem integral_heatTorusL2 {s : ℝ} (hs : 0 ≤ s) (f : TorusL2 2) :
    ∫ x : UnitAddTorus (Fin 2), heatTorusL2 s hs f x =
      ∫ x : UnitAddTorus (Fin 2), f x := by
  have hzero := mFourierCoeff_heatTorusL2 hs f (0 : Frequency)
  simpa [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier_zero,
    heatMultiplier, frequencySq] using hzero

end AVenhance.Infra.Heat
