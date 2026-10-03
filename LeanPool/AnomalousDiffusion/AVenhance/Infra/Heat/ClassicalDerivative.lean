/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.SmoothClassical
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.Analytic
public import Mathlib.Analysis.Fourier.AddCircle

/-! # Classical Derivative

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraHeatClassicalDerivativeMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraHeatClassicalDerivativeMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraHeatClassicalDerivativeIsProbabilityMeasure3 : IsProbabilityMeasure (volume
    : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
open AVenhance.Infra.Torus Homogenization
noncomputable section
namespace AVenhance.Infra.Heat

theorem degree_eq_zero_one (α : Fin 2 → ℕ) :
    multiIndexDegree α = α 0 + α 1 := by
  simp [multiIndexDegree, Fin.sum_univ_succ]

/-- The Fourier coefficients of a heat-evolved multi-index derivative are
absolutely summable. The Gaussian absorbs the polynomial frequency factor. -/
theorem heatDerivativeFourierCoeff_summable {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (α : Fin 2 → ℕ) :
    Summable (fun k : Frequency =>
      ‖UnitAddTorus.mFourierCoeff (heatDerivativeTorusL2 hs f α) k‖) := by
  let half : ℝ := s / 2
  have hhalf : 0 < half := by dsimp [half]; positivity
  let a : lp (fun _ : Frequency => ℂ) 2 := UnitAddTorus.mFourierBasis.repr f
  let b : lp (fun _ : Frequency => ℂ) 2 := ⟨
    (fun k : Frequency => (Real.exp (-(2 * Real.pi^2 * s) * frequencySq k) : ℂ)),
    gaussianWeight_memLp (2 * Real.pi^2 * s) (by positivity)⟩
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal :=
    ENNReal.HolderConjugate.toReal (by norm_num)
  have hprod : Summable (fun k : Frequency => ‖a k‖ * ‖b k‖) :=
    lp.summable_mul hpq a b
  let M : ℝ := (Nat.factorial (multiIndexDegree α) : ℝ) *
    (1 / Real.sqrt half) ^ multiIndexDegree α
  have hM : 0 ≤ M := by positivity
  have hbound : ∀ k : Frequency,
      ‖UnitAddTorus.mFourierCoeff (heatDerivativeTorusL2 hs f α) k‖ ≤
        M * (‖a k‖ * ‖b k‖) := by
    intro k
    rw [mFourierCoeff_heatDerivativeTorusL2, norm_mul]
    have hsplit : heatMultiplier s k = heatMultiplier half k * heatMultiplier half k := by
      rw [heatMultiplier, heatMultiplier, ← Real.exp_add]
      congr 1
      dsimp [half]
      ring
    have hsplitC : (heatMultiplier s k : ℂ) =
        (heatMultiplier half k : ℂ) * (heatMultiplier half k : ℂ) := by
      exact_mod_cast hsplit
    have hmh : 0 ≤ heatMultiplier half k := (Real.exp_pos _).le
    have hderivhalf := heatDerivativeMultiplier_norm_le hhalf α k
    have hcoeff : ‖UnitAddTorus.mFourierCoeff f k‖ = ‖a k‖ := by
      simp [a, UnitAddTorus.mFourierBasis_repr]
    have hmult : ‖heatDerivativeMultiplier s α k‖ =
        heatMultiplier half k * ‖heatDerivativeMultiplier half α k‖ := by
      calc
        ‖heatDerivativeMultiplier s α k‖ =
            ‖(heatMultiplier half k : ℂ) * heatDerivativeMultiplier half α k‖ := by
          simp only [heatDerivativeMultiplier, hsplitC]
          congr 1
          ring
        _ = ‖(heatMultiplier half k : ℂ)‖ *
              ‖heatDerivativeMultiplier half α k‖ := norm_mul _ _
        _ = heatMultiplier half k * ‖heatDerivativeMultiplier half α k‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmh]
    rw [hmult, hcoeff]
    have hb : ‖b k‖ = heatMultiplier half k := by
      dsimp [b]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_nonneg _)]
      rw [heatMultiplier]
      congr 1
      dsimp [half]
      ring
    calc
      heatMultiplier half k * ‖heatDerivativeMultiplier half α k‖ * ‖a k‖ ≤
          heatMultiplier half k * M * ‖a k‖ := by
        calc
          _ = heatMultiplier half k *
              (‖heatDerivativeMultiplier half α k‖ * ‖a k‖) := by ring
          _ ≤ heatMultiplier half k * (M * ‖a k‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (by simpa [M] using hderivhalf)
                (norm_nonneg _)) hmh
          _ = heatMultiplier half k * M * ‖a k‖ := by ring
      _ = M * (‖a k‖ * ‖b k‖) := by rw [hb]; ring
  have hsummable : Summable (fun k : Frequency =>
      UnitAddTorus.mFourierCoeff (heatDerivativeTorusL2 hs f α) k) := by
    apply Summable.of_norm_bounded (hprod.mul_left M)
    intro k
    exact hbound k
  exact hsummable.norm

/-- Continuous Fourier series representative of a classical heat derivative. -/
noncomputable def heatDerivativeTorusContinuous {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (α : Fin 2 → ℕ) : C(UnitAddTorus (Fin 2), ℂ) :=
  ∑' k : Frequency,
    UnitAddTorus.mFourierCoeff (heatDerivativeTorusL2 hs f α) k • UnitAddTorus.mFourier k

theorem heatDerivativeTorusContinuous_toLp {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (α : Fin 2 → ℕ) :
    ContinuousMap.toLp 2 volume ℂ (heatDerivativeTorusContinuous hs f α) =
      heatDerivativeTorusL2 hs f α := by
  let g : Frequency → C(UnitAddTorus (Fin 2), ℂ) := fun k =>
    UnitAddTorus.mFourierCoeff (heatDerivativeTorusL2 hs f α) k • UnitAddTorus.mFourier k
  have hcoeff := heatDerivativeFourierCoeff_summable hs f α
  have hg : Summable g := by
    apply Summable.of_norm_bounded hcoeff
    intro k
    simp [g, norm_smul, UnitAddTorus.mFourier_norm]
  have hL2 : HasSum (fun k : Frequency => ContinuousMap.toLp 2 volume ℂ (g k))
      (heatDerivativeTorusL2 hs f α) := by
    have hbasis := UnitAddTorus.hasSum_mFourier_series_L2 (heatDerivativeTorusL2 hs f α)
    simpa [g, UnitAddTorus.mFourierLp] using hbasis
  change ContinuousMap.toLp 2 volume ℂ (∑' k, g k) = heatDerivativeTorusL2 hs f α
  rw [ContinuousLinearMap.map_tsum (ContinuousMap.toLp 2 volume ℂ) hg]
  exact hL2.tsum_eq

theorem heatDerivativeTorusContinuous_apply_toUnitTorus {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (α : Fin 2 → ℕ) (x : Vec 2) :
    heatDerivativeTorusContinuous hs f α (toUnitTorus 2 x) =
      ∑' k : Frequency,
        UnitAddTorus.mFourierCoeff f k * heatDerivativeMultiplier s α k *
          torusCharacter (-k) x := by
  let g : Frequency → C(UnitAddTorus (Fin 2), ℂ) := fun k =>
    UnitAddTorus.mFourierCoeff (heatDerivativeTorusL2 hs f α) k • UnitAddTorus.mFourier k
  have hg : Summable g := by
    apply Summable.of_norm_bounded (heatDerivativeFourierCoeff_summable hs f α)
    intro k
    simp [g, norm_smul, UnitAddTorus.mFourier_norm]
  change (∑' k : Frequency, g k) (toUnitTorus 2 x) = _
  rw [← ContinuousMap.tsum_apply hg]
  apply tsum_congr
  intro k
  simp only [g, ContinuousMap.smul_apply, smul_eq_mul]
  rw [mFourierCoeff_heatDerivativeTorusL2]
  have hchar : UnitAddTorus.mFourier k (toUnitTorus 2 x) = torusCharacter (-k) x := by
    change UnitAddTorus.mFourier k (toUnitTorus 2 x) =
      UnitAddTorus.mFourier (-(-k)) (toUnitTorus 2 x)
    simp
  rw [hchar]
  ring

/-- The classical periodic derivative obeys the explicit analytic multiplier
bound in torus `L²`, with universal constant one. -/
theorem norm_heatTorusSmoothLift_multiIndexDerivative_le {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (α : Fin 2 → ℕ) :
    ‖ContinuousMap.toLp 2 volume ℂ (heatDerivativeTorusContinuous hs f α)‖ ≤
      (Nat.factorial (multiIndexDegree α) : ℝ) *
        (1 / Real.sqrt s) ^ multiIndexDegree α * ‖f‖ := by
  rw [heatDerivativeTorusContinuous_toLp]
  exact norm_heatDerivativeTorusL2_le hs f α

end AVenhance.Infra.Heat
