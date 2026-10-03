/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.Analytic
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-! # Smooth

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open MeasureTheory
open AVenhance.Infra.Heat
open scoped ENNReal

namespace AVenhance.Infra.Heat

lemma summable_gauss_int {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-c * (n : ℝ)^2)) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 (T := c / Real.pi)
    (div_pos hc Real.pi_pos) 0
  have h' : Summable (fun n : ℤ => Real.exp (-Real.pi * ((c / Real.pi) * (n : ℝ)^2))) := by
    simpa using h
  refine h'.congr ?_
  intro n
  congr 1
  field_simp

lemma summable_gauss_frequency {c : ℝ} (hc : 0 < c) :
    Summable (fun k : Frequency => Real.exp (-c * frequencySq k)) := by
  rw [← (finTwoArrowEquiv ℤ).symm.summable_iff]
  have h1 := summable_gauss_int hc
  have hprod : Summable (fun p : ℤ × ℤ =>
      Real.exp (-c * (p.1 : ℝ)^2) * Real.exp (-c * (p.2 : ℝ)^2)) := by
    apply (summable_prod_of_nonneg (fun p : ℤ × ℤ => mul_nonneg (Real.exp_nonneg _)
        (Real.exp_nonneg _))).2
    constructor
    · intro a
      exact h1.mul_left (Real.exp (-c * (a : ℝ)^2))
    · have hA := h1.mul_left (∑' b : ℤ, Real.exp (-c * (b : ℝ)^2))
      refine hA.congr ?_
      intro a
      change (∑' b : ℤ, Real.exp (-c * (b : ℝ)^2)) * Real.exp (-c * (a : ℝ)^2) =
        ∑' b : ℤ, Real.exp (-c * (a : ℝ)^2) * Real.exp (-c * (b : ℝ)^2)
      rw [tsum_mul_left]
      ring
  refine hprod.congr ?_
  intro p
  change Real.exp (-c * (p.1 : ℝ)^2) * Real.exp (-c * (p.2 : ℝ)^2) =
    Real.exp (-c * frequencySq ((finTwoArrowEquiv ℤ).symm p))
  rw [← Real.exp_add]
  congr 1
  simp [frequencySq, Fin.sum_univ_succ]
  ring

lemma gaussianWeight_memLp (c : ℝ) (hc : 0 < c) :
    Memℓp (fun k : Frequency => (Real.exp (-c * frequencySq k) : ℂ)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
  have h := summable_gauss_frequency (mul_pos (by norm_num : (0:ℝ) < 2) hc)
  refine h.congr ?_
  intro k
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  norm_num
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end AVenhance.Infra.Heat

noncomputable section

open MeasureTheory
open AVenhance.Infra.Torus
open scoped ComplexConjugate ENNReal

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraHeatSmoothMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraHeatSmoothMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraHeatSmoothIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure
    UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Heat

theorem heatFourierCoeff_summable {s : ℝ} (hs : 0 < s) (f : TorusL2 2) :
    Summable (fun k : Frequency =>
      ‖UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k‖) := by
  let c : ℝ := 4 * Real.pi ^ 2 * s
  have hc : 0 < c := by dsimp [c]; positivity
  let a : lp (fun _ : Frequency => ℂ) 2 := UnitAddTorus.mFourierBasis.repr f
  let b : lp (fun _ : Frequency => ℂ) 2 := ⟨
    (fun k : Frequency => (Real.exp (-c * frequencySq k) : ℂ)), gaussianWeight_memLp c hc⟩
  have hprod : Summable (fun k : Frequency => ‖a k‖ * ‖b k‖) := by
    have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal :=
      ENNReal.HolderConjugate.toReal (by norm_num)
    exact lp.summable_mul hpq a b
  refine hprod.congr ?_
  intro k
  rw [mFourierCoeff_heatTorusL2 hs.le]
  rw [norm_mul]
  simp only [a, b, UnitAddTorus.mFourierBasis_repr]
  rw [Complex.norm_real, Complex.norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hmulabs : |heatMultiplier s k| = Real.exp (-c * frequencySq k) := by
    rw [heatMultiplier, abs_of_pos (Real.exp_pos _)]
    congr 1
    dsimp [c]
    ring
  rw [hmulabs]
  rw [abs_of_pos (Real.exp_pos _)]
  ring

end AVenhance.Infra.Heat

namespace AVenhance.Infra.Heat

/-- Continuous torus representative of the positive-time heat evolution. -/
noncomputable def heatTorusContinuous {s : ℝ} (hs : 0 < s) (f : TorusL2 2) :
    C(UnitAddTorus (Fin 2), ℂ) :=
  ∑' k : Frequency,
    UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k • UnitAddTorus.mFourier k

theorem heatTorusContinuous_toLp {s : ℝ} (hs : 0 < s) (f : TorusL2 2) :
    ContinuousMap.toLp 2 volume ℂ (heatTorusContinuous hs f) = heatTorusL2 s hs.le f := by
  let g : Frequency → C(UnitAddTorus (Fin 2), ℂ) := fun k =>
    UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k • UnitAddTorus.mFourier k
  have hcoeff : Summable (fun k : Frequency =>
      ‖UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k‖) :=
    heatFourierCoeff_summable hs f
  have hg : Summable g := by
    apply Summable.of_norm_bounded hcoeff
    intro k
    simp [g, norm_smul, UnitAddTorus.mFourier_norm]
  have hL2 : HasSum (fun k : Frequency => ContinuousMap.toLp 2 volume ℂ (g k))
      (heatTorusL2 s hs.le f) := by
    have hbasis := UnitAddTorus.hasSum_mFourier_series_L2 (heatTorusL2 s hs.le f)
    simpa [g, UnitAddTorus.mFourierLp] using hbasis
  change ContinuousMap.toLp 2 volume ℂ (∑' k, g k) = heatTorusL2 s hs.le f
  rw [ContinuousLinearMap.map_tsum (ContinuousMap.toLp 2 volume ℂ) hg]
  exact hL2.tsum_eq

end AVenhance.Infra.Heat
