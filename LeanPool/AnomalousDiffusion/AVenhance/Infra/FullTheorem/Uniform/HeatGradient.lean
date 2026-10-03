/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.H1Reduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.Energy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.SmoothClassical
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge

/-!
# The heat approximant does not increase the `H¹` seminorm

For `g = realHeatApprox hf hs` (real part of the heat Fourier series of the datum), the gradient
energy is bounded by that of the datum: pointwise `|∇ Re H| ≤ |∇ H|`, Parseval for the smooth
periodic `H`, the Fourier multiplier `e^{-4π² s |k|²} ≤ 1`, and Parseval for the datum's weak
gradient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open AVenhance.Infra.Torus AVenhance.Infra.Heat

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance heatGradMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance heatGradIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance heatGradProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.FullTheorem.Uniform

open AVenhance AVenhance.Infra.Section5

theorem HeatGradient.heatMult_nonneg (s : ℝ) (k : Frequency) : 0 ≤ heatMultiplier s k :=
  Real.exp_nonneg _

theorem HeatGradient.heatMult_le_one {s : ℝ} (hs : 0 ≤ s) (k : Frequency) : heatMultiplier s k ≤ 1
    := by
  unfold heatMultiplier
  rw [Real.exp_le_one_iff]
  have : 0 ≤ frequencySq k := by
    unfold frequencySq
    exact Finset.sum_nonneg fun i _ => sq_nonneg (k i : ℝ)
  have : 0 ≤ 4 * Real.pi ^ 2 * s * frequencySq k := by positivity
  linarith

/-- The heat flow does not increase the Fourier Dirichlet energy. -/
theorem fourierEnergy_heatTorusL2_le {s : ℝ} (hs : 0 ≤ s) (u : TorusL2 2)
    (hu : HasFiniteFourierEnergy u) :
    HasFiniteFourierEnergy (heatTorusL2 s hs u) ∧
      fourierEnergy (heatTorusL2 s hs u) ≤ fourierEnergy u := by
  have hterm : ∀ k, fourierEnergyTerm (heatTorusL2 s hs u) k ≤ fourierEnergyTerm u k := by
    intro k
    unfold fourierEnergyTerm
    rw [mFourierCoeff_heatTorusL2 hs u k, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (HeatGradient.heatMult_nonneg s k)]
    have h1 := HeatGradient.heatMult_le_one hs k
    have h0 := HeatGradient.heatMult_nonneg s k
    have hq : 0 ≤ 4 * Real.pi ^ 2 * frequencySq k := by
      have : 0 ≤ frequencySq k := by
        unfold frequencySq
        exact Finset.sum_nonneg fun i _ => sq_nonneg (k i : ℝ)
      positivity
    have hsq : (heatMultiplier s k) ^ 2 ≤ 1 := by nlinarith
    calc 4 * Real.pi ^ 2 * frequencySq k * (heatMultiplier s k * ‖UnitAddTorus.mFourierCoeff u k‖)
        ^ 2
        = (4 * Real.pi ^ 2 * frequencySq k * ‖UnitAddTorus.mFourierCoeff u k‖ ^ 2) *
            (heatMultiplier s k) ^ 2 := by ring
      _ ≤ (4 * Real.pi ^ 2 * frequencySq k * ‖UnitAddTorus.mFourierCoeff u k‖ ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := mul_one _
  have hnn : ∀ k, 0 ≤ fourierEnergyTerm (heatTorusL2 s hs u) k := by
    intro k
    unfold fourierEnergyTerm
    have : 0 ≤ frequencySq k := by
      unfold frequencySq
      exact Finset.sum_nonneg fun i _ => sq_nonneg (k i : ℝ)
    positivity
  have hsum : Summable (fourierEnergyTerm (heatTorusL2 s hs u)) :=
    Summable.of_nonneg_of_le hnn hterm hu
  exact ⟨hsum, hsum.tsum_le_tsum hterm hu⟩

/-- The classical complex heat series is the periodic lift of the continuous heat evolution. -/
theorem HeatGradient.heatLift_periodicToTorusL2 {s : ℝ} (hs : 0 < s) (u : TorusL2 2)
    (hc : Continuous (heatTorusSmoothLift hs u)) :
    periodicToTorusL2 (heatTorusSmoothLift hs u) hc = heatTorusL2 s hs.le u := by
  rw [← heatTorusContinuous_toLp hs u]
  apply Lp.ext
  have h1 := (memLp_periodicToTorus hc).coeFn_toLp
  have h2 := (heatTorusContinuous hs u).coeFn_toLp (p := 2)
    (μ := (volume : Measure (UnitAddTorus (Fin 2)))) (𝕜 := ℂ)
  filter_upwards [h1, h2] with y hy1 hy2
  have h1' : (periodicToTorusL2 (heatTorusSmoothLift hs u) hc : UnitAddTorus (Fin 2) → ℂ) y =
      periodicToTorus (heatTorusSmoothLift hs u) y := hy1
  rw [h1', hy2]
  unfold periodicToTorus
  rw [heatTorusSmoothLift_eq_heatTorusContinuous, toUnitTorus_unitTorusRepresentative]

theorem HeatGradient.heatLift_periodic {s : ℝ} (hs : 0 < s) (u : TorusL2 2) :
    IsZdPeriodic (heatTorusSmoothLift hs u) := by
  have : heatTorusSmoothLift hs u = fromUnitTorus (heatTorusContinuous hs u) := by
    funext x
    exact heatTorusSmoothLift_eq_heatTorusContinuous hs u x
  rw [this]
  exact isZdPeriodic_fromUnitTorus _

/-- The real part of a `C¹` function has coordinate derivatives bounded by the complex ones. -/
theorem HeatGradient.spaceGrad_re_apply {H : Vec 2 → ℂ} (hH : ContDiff ℝ 1 H) (i : Fin 2) (x : Vec
    2) :
    spaceGrad (fun y => (H y).re) x i = (coordDeriv i H x).re := by
  have hd : DifferentiableAt ℝ H x := hH.differentiable (by simp) x
  have := (Complex.reCLM.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  unfold spaceGrad coordDeriv
  have h2 : fderiv ℝ (fun y => (H y).re) x = Complex.reCLM.comp (fderiv ℝ H x) := this
  rw [h2]
  rfl

/-- The heat approximant has gradient energy at most that of the datum. -/
theorem realHeatApprox_gradNormSq_le {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) {s : ℝ} (hs : 0 < s) :
    gradNormSq (spaceGrad (realHeatApprox hf hs)) ≤ gradNormSq Df := by
  set u := frozenPeriodicH1ValueL2 hf with hu
  set H := heatTorusSmoothLift hs u with hHdef
  have hHs : ContDiff ℝ (⊤ : ℕ∞) H := heatTorusSmoothLift_contDiff hs u
  have hH1 : ContDiff ℝ 1 H := hHs.of_le (by exact_mod_cast le_top)
  have hper : IsZdPeriodic H := HeatGradient.heatLift_periodic hs u
  obtain ⟨-, hP⟩ := hasFiniteFourierEnergy_periodicToTorusL2 hH1 hper
  rw [HeatGradient.heatLift_periodicToTorusL2 hs u hH1.continuous] at hP
  obtain ⟨-, hheat⟩ := fourierEnergy_heatTorusL2_le hs.le u
    (hasFiniteFourierEnergy_frozenPeriodicH1 hf)
  have hD := fourierEnergy_frozenPeriodicH1_eq_gradNormSq hf
  have hreal : realHeatApprox hf hs = fun y => (H y).re := rfl
  rw [hreal]
  have hcont : Continuous (fun x => ∑ i : Fin 2, ‖coordDeriv i H x‖ ^ 2) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_coordDeriv i hH1).norm.pow 2
  have hint : IntegrableOn (fun x => ∑ i : Fin 2, ‖coordDeriv i H x‖ ^ 2) unitCube := by
    refine (hcont.integrableOn_Icc (a := (0 : Vec 2)) (b := 1)).mono_set ?_
    intro x hx
    exact ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2.le⟩
  have hle : gradNormSq (spaceGrad fun y => (H y).re) ≤
      ∫ x in unitCube, ∑ i : Fin 2, ‖coordDeriv i H x‖ ^ 2 := by
    unfold gradNormSq
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _) hint ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [vecNormSq, vecDot, Fin.sum_univ_two, HeatGradient.spaceGrad_re_apply hH1]
    have h0 : (coordDeriv 0 H x).re ^ 2 ≤ ‖coordDeriv 0 H x‖ ^ 2 :=
      sq_le_sq' (by linarith [abs_le.mp (Complex.abs_re_le_norm (coordDeriv 0 H x))])
        (Complex.re_le_norm _)
    have h1 : (coordDeriv 1 H x).re ^ 2 ≤ ‖coordDeriv 1 H x‖ ^ 2 :=
      sq_le_sq' (by linarith [abs_le.mp (Complex.abs_re_le_norm (coordDeriv 1 H x))])
        (Complex.re_le_norm _)
    nlinarith [h0, h1]
  rw [← integral_unitCell_eq_unitCube] at hle
  linarith

end AVenhance.Infra.FullTheorem.Uniform
